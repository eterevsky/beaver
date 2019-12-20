mod brainfuck;

use crate::brainfuck::{Instruction, Program, State, Status, run};
#[cfg(test)]
use crate::brainfuck::gen_valid_programs;
use std::collections::VecDeque;
use std::env;
use std::fmt;


#[derive(PartialEq, Debug, Clone)]
enum Predicate {
    // Always true in any state.
    True,

    // Always false.
    False,
    
    // The tape starting from current position + offset is all zeros.
    ZerosFrom(isize),

    // A value at a given offset equals to a constant.
    Equals(isize, u8),

    // A value at a given offset is greater than a constant.
    GreaterThan(isize, u8),

    // Conjunction of a list of predicates.
    All(Vec<Predicate>),

    // Disjunction of a list of predicates.
    Any(Vec<Predicate>),
}

fn flatten_all(children: &mut Vec<Predicate>) {
    let mut new_children = Vec::new();
    for child in children.iter() {
        if let Predicate::All(grandchildren) = child {
            new_children.extend(grandchildren.iter().cloned());
        }
    }

    children.retain(|v| !v.is_all());
    children.extend_from_slice(&new_children);
}

fn optimize_all(children: Vec<Predicate>) -> Vec<Predicate> {
    let mut children = children.clone();
    flatten_all(&mut children);
    for i in 0..children.len() {
        for j in 0..children.len() {
            if i == j { continue; }
            if children[i].implies(&children[j]) { 
                children[j] = Predicate::True;
            } else if children[i].incompatible(&children[j]) {
                return vec![Predicate::False]
            }
        }
    }
    children.retain(|v| *v != Predicate::True);
    children
}

fn flatten_any(children: &mut Vec<Predicate>) {
    // TODO: Expand Any inside of All?
    let mut new_children = Vec::new();
    for child in children.iter() {
        if let Predicate::Any(grandchildren) = child {
            new_children.extend(grandchildren.iter().cloned());
        }
    }

    children.retain(|v| !v.is_any());
    children.extend_from_slice(&new_children);
}

fn optimize_any(mut children: Vec<Predicate>) -> Vec<Predicate> {
    flatten_any(&mut children);
    for i in 0..children.len() {
        for j in 0..children.len() {
            if i != j && children[j].implies(&children[i]) { 
                children[j] = Predicate::False;
            }
        }
    }
    children.retain(|v| *v != Predicate::False);
    children
}

/// Expand the expression  (any1 | any2 | ... ) & (all1 & all2 & ...) into
/// (any1 & all1 & all2 & ...) | (any2 & all1 & all2 & ...) | ...
fn expand_any_clause(any_children: &[Predicate], all_children: Vec<Predicate>) -> Predicate {
    let mut new_any = Vec::new();
    for any_child in any_children.iter() {
        let mut clause = all_children.clone();
        clause.push(any_child.clone());
        new_any.push(Predicate::All(clause));
    }
    Predicate::Any(new_any)
}

impl Predicate {
    fn is_any(&self) -> bool {
        match self {
            Predicate::Any(_) => true,
            _ => false
        }
    }

    fn is_all(&self) -> bool {
        match self {
            Predicate::All(_) => true,
            _ => false
        }
    }

    #[cfg(test)]
    fn check(&self, state: &State) -> bool {
        match self {
            Predicate::True => true,
            Predicate::False => false,
            Predicate::ZerosFrom(offset) => {
                let start = state.pos as isize + offset;
                if start < 0 {
                    false
                } else {
                    ((start as usize)..state.tape.len()).all(|i| state.tape[i] == 0)
                }
            },
            Predicate::Equals(offset, x) => state.val_at_offset(*offset) == Some(*x),
            Predicate::GreaterThan(offset, x) => match state.val_at_offset(*offset) {
                None => false,
                Some(v) => v > *x,
            },
            Predicate::All(children) => children.iter().all(|c| c.check(state)),
            Predicate::Any(children) => children.iter().any(|c| c.check(state)),
        }
    }

    fn optimize(self) -> Self {
        match self {
            Predicate::All(children) => {
                let children: Vec<Predicate> = children.iter().map(|c| c.clone().optimize()).collect();
                let temp_self = Predicate::All(children.clone());

                for child in children.iter() {
                    match child {
                        Predicate::False => return Predicate::False,

                        Predicate::Equals(o, v) => if *v != 0 && temp_self.implies(&Predicate::Equals(*o, 0)) {
                            return Predicate::False
                        },

                        Predicate::GreaterThan(o, _) => if temp_self.implies(&Predicate::Equals(*o, 0)) {
                            return Predicate::False
                        },

                        _ => (),
                    }
                }

                for i in 0..children.len() {
                    if let Predicate::Any(any_children) = &children[i] {
                        let mut all_children = children.clone();
                        all_children[i] = Predicate::True;

                        return expand_any_clause(any_children, all_children).optimize();
                    }
                }

                let new_children = optimize_all(children);
                match new_children.len() {
                    0 => Predicate::True,
                    1 => new_children[0].clone(),
                    _ => Predicate::All(new_children),
                }
            },

            Predicate::Any(children) => {
                let children: Vec<Predicate> = children.iter().map(|c| c.clone().optimize()).collect();
                let new_children = optimize_any(children);
                match new_children.len() {
                    0 => Predicate::False,
                    1 => new_children[0].clone(),
                    _ => Predicate::Any(new_children)
                }    
            },

            _ => self
        }
    }

    // We assume that self is opimized, i.e. All is higer than Offset and Offset is
    // collapsed.
    fn implies(&self, other: &Predicate) -> bool {
        match (self, other) {
            (_, Predicate::True) => true,

            (Predicate::False, _) => true,

            (s, Predicate::All(children)) => children.iter().all(|c| s.implies(c)),

            (Predicate::Any(children), o) => children.iter().all(|c| c.implies(o)),

            // These two rules are a simplifications.
            (s, Predicate::Any(children)) => children.iter().any(|c| s.implies(c)),

            (Predicate::All(children), o) => children.iter().any(|c| c.implies(o)),

            (Predicate::ZerosFrom(offset_x), Predicate::ZerosFrom(offset_y)) =>
                *offset_x <= *offset_y,

            (Predicate::Equals(offset_x, x), Predicate::Equals(offset_y, y)) =>
                *offset_x == *offset_y && *x == *y,

            (Predicate::ZerosFrom(offset_x), Predicate::Equals(offset_y, y)) =>
                *offset_x <= *offset_y && *y == 0,

            (Predicate::Equals(offset_x, x), Predicate::GreaterThan(offset_y, y)) =>
                *offset_x == *offset_y && x > y,

            (Predicate::GreaterThan(offset_x, x), Predicate::GreaterThan(offset_y, y)) =>
                *offset_x == *offset_y && x >= y,

            _ => false,
        }
    }

    // Checks whether this predicate implies negation of another predicate.
    fn incompatible(&self, other: &Predicate) -> bool {
        match (self, other) {
            (Predicate::False, _) => true,

            (_, Predicate::False) => true,

            (s, Predicate::Any(children)) => children.iter().all(|c| s.incompatible(c)),

            (Predicate::Any(children), o) => children.iter().all(|c| c.incompatible(o)),

            (s, Predicate::All(children)) => children.iter().any(|c| s.incompatible(c)),

            (Predicate::All(children), o) => children.iter().any(|c| c.incompatible(o)),

            (Predicate::ZerosFrom(zeros_from), Predicate::Equals(offset, v)) =>
                zeros_from <= offset && *v != 0,

            (Predicate::Equals(offset, v), Predicate::ZerosFrom(zeros_from)) =>
                zeros_from <= offset && *v != 0,

            (Predicate::ZerosFrom(zeros_from), Predicate::GreaterThan(offset, _)) =>
                zeros_from <= offset,

            (Predicate::GreaterThan(offset, _), Predicate::ZerosFrom(zeros_from)) =>
                zeros_from <= offset,

            (Predicate::Equals(offset_e, v), Predicate::GreaterThan(offset_g, l)) =>
                offset_e == offset_g && v <= l,

            (Predicate::GreaterThan(offset_g, l), Predicate::Equals(offset_e, v)) =>
                offset_e == offset_g && v <= l,

            (Predicate::Equals(o1, v1), Predicate::Equals(o2, v2)) =>
                o1 == o2 && v1 != v2,

            _ => false,
        }
    }

    // Recursively apply the instruction.  
    fn apply_impl(&self, instruction: Instruction) -> Self {
        match (instruction, self.clone()) {
            (i, Predicate::All(children)) => 
                Predicate::All(children.iter().map(|c| c.apply_impl(i)).collect()).optimize(),

            (i, Predicate::Any(children)) => 
                Predicate::Any(children.iter().map(|c| c.apply_impl(i)).collect()).optimize(),

            (_, Predicate::True) => Predicate::True,

            (_, Predicate::False) => Predicate::False,

            (Instruction::Inc, Predicate::ZerosFrom(offset)) if offset > 0 => Predicate::ZerosFrom(offset),

            (Instruction::Inc, Predicate::ZerosFrom(offset)) if offset <= 0 => {
                let mut children = vec![Predicate::ZerosFrom(1), Predicate::Equals(0, 1)];
                for i in offset..0 {
                    children.push(Predicate::Equals(i, 0));
                }
                Predicate::All(children)
            },

            (Instruction::Inc, Predicate::Equals(0, x)) => Predicate::Equals(0, x + 1),
           
            (Instruction::Inc, Predicate::Equals(offset, x)) => Predicate::Equals(offset, x),

            (Instruction::Inc, Predicate::GreaterThan(0, x)) => Predicate::GreaterThan(0, x + 1),
           
            (Instruction::Inc, Predicate::GreaterThan(offset, x)) => Predicate::GreaterThan(offset, x),


            (Instruction::Dec, Predicate::ZerosFrom(offset)) if offset <= 0 => Predicate::False,

            (Instruction::Dec, Predicate::ZerosFrom(offset)) => Predicate::ZerosFrom(offset),

            (Instruction::Dec, Predicate::Equals(0, 0)) => Predicate::False,
           
            (Instruction::Dec, Predicate::Equals(0, x)) => Predicate::Equals(0, x - 1),
           
            (Instruction::Dec, Predicate::Equals(offset, x)) => Predicate::Equals(offset, x),

            (Instruction::Dec, Predicate::GreaterThan(0, 0)) => Predicate::True,
           
            (Instruction::Dec, Predicate::GreaterThan(0, x)) => Predicate::GreaterThan(0, x - 1),
           
            (Instruction::Dec, Predicate::GreaterThan(offset, x)) => Predicate::GreaterThan(offset, x),


            (Instruction::Right, Predicate::ZerosFrom(offset)) => Predicate::ZerosFrom(offset - 1),

            (Instruction::Right, Predicate::Equals(offset, x)) => Predicate::Equals(offset - 1, x),

            (Instruction::Right, Predicate::GreaterThan(offset, x)) => Predicate::GreaterThan(offset - 1, x),


            (Instruction::Left, Predicate::ZerosFrom(offset)) => Predicate::ZerosFrom(offset + 1),

            (Instruction::Left, Predicate::Equals(offset, x)) => Predicate::Equals(offset + 1, x),

            (Instruction::Left, Predicate::GreaterThan(offset, x)) => Predicate::GreaterThan(offset + 1, x),

            _ => unreachable!()
        }
    }

    // Construct a weaker version of the predicate by modifying all the predicates with offset
    // farther than +/-2.
    fn weaken(self) -> Self {
        match self {
            Predicate::Equals(offset, _) if offset < -2 || offset > 2 => Predicate::True,
            Predicate::GreaterThan(offset, _) if offset < -2 || offset > 2 => Predicate::True,
            Predicate::All(mut children) =>
                Predicate::All(children.drain(..).map(|c| c.weaken()).collect()).optimize(),
            Predicate::Any(mut children) =>
                Predicate::Any(children.drain(..).map(|c| c.weaken()).collect()).optimize(),
            _ => self,
        }
    }

    // Modify the predicate after executing the instruction.
    fn apply(&self, instruction: Instruction) -> Self {
        let predicate = self.apply_impl(instruction);

        if instruction == Instruction::Inc && !predicate.implies(&Predicate::GreaterThan(0, 0)) {
            Predicate::All(vec![Predicate::GreaterThan(0, 0), predicate]).optimize()
        } else {
            predicate
        } 
    }

    fn step(&self, program: &Program, ip: usize) -> ((Self, usize), Option<(Self, usize)>) {
        assert!(ip < program.len());
        match program[ip] {
            Instruction::Forward(target) => {
                if self.implies(&Predicate::GreaterThan(0, 0)) {
                    ((self.clone(), ip + 1), None)   
                } else if self.implies(&Predicate::Equals(0, 0)) {
                    ((self.clone(), target), None)
                } else {
                    ((Predicate::All(vec![self.clone(), Predicate::GreaterThan(0, 0)]).optimize(), ip + 1),
                     Some((Predicate::All(vec![self.clone(), Predicate::Equals(0, 0)]).optimize(), target)))
                }
            },
            Instruction::Backward(target) => {
                if self.implies(&Predicate::GreaterThan(0, 0)) {
                    ((self.clone(), target), None)   
                } else if self.implies(&Predicate::Equals(0, 0)) {
                    ((self.clone(), ip + 1), None)
                } else {
                    ((Predicate::All(vec![self.clone(), Predicate::GreaterThan(0, 0)]).optimize(), target),
                     Some((Predicate::All(vec![self.clone(), Predicate::Equals(0, 0)]).optimize(), ip + 1)))
                }
            },
            instruction => ((self.apply(instruction), ip + 1), None)
        }
    }

    // Find a predicate that follows from both self and other.
    fn intersect(&self, other: &Predicate) -> Self {
        if self.implies(other) {
            other.clone()
        } else if other.implies(self) {
            self.clone()
        } else {
            Predicate::Any(vec![self.clone(), other.clone()]).weaken()
        }
    }
}

#[test]
fn test_optimize() {
    let predicate = Predicate::All(vec![
        Predicate::All(vec![Predicate::Equals(1, 2), Predicate::Equals(1, 2)]),
        Predicate::Equals(1, 2),
        Predicate::True,
        ]);
    let optimized = predicate.optimize();
    assert_eq!(optimized, Predicate::Equals(1, 2));
}

#[test]
fn test_check_zeros_from() {
    let mut state = State::new("+".parse().unwrap());
    assert!(Predicate::ZerosFrom(0).check(&state));
    assert!(!Predicate::ZerosFrom(-1).check(&state));
    assert!(Predicate::ZerosFrom(1).check(&state));

    state.step();
    assert!(!Predicate::ZerosFrom(0).check(&state));
    assert!(!Predicate::ZerosFrom(-1).check(&state));
    assert!(Predicate::ZerosFrom(1).check(&state));
}

#[test]
fn test_imply_zeros_from() {
    assert!(Predicate::ZerosFrom(-1).implies(&Predicate::Equals(0, 0)));
    assert!(Predicate::ZerosFrom(0).implies(&Predicate::Equals(0, 0)));
    assert!(!Predicate::ZerosFrom(1).implies(&Predicate::Equals(0, 0)));

    assert!(Predicate::ZerosFrom(0).implies(&Predicate::Equals(1, 0)));
    assert!(Predicate::ZerosFrom(1).implies(&Predicate::Equals(1, 0)));
    assert!(!Predicate::ZerosFrom(2).implies(&Predicate::Equals(1, 0)));
}

#[test]
fn test_weaken1() {
    let predicate = Predicate::Equals(-2, 1);
    let weaker = predicate.clone().weaken();
    assert!(predicate.implies(&weaker));
}

#[test]
fn test_weaken_and() {
    let predicate = Predicate::All(vec![Predicate::Equals(-2, 1), Predicate::ZerosFrom(1)]);
    let weaker = predicate.clone().weaken();
    assert!(predicate.implies(&weaker));
}

#[test]
fn test_weaken_or() {
    let predicate = Predicate::Any(vec![Predicate::Equals(-2, 1), Predicate::ZerosFrom(1)]);
    let weaker = predicate.clone().weaken();
    assert!(predicate.implies(&weaker));
}

#[test]
fn test_composite_pred_apply() {
    let predicate = Predicate::All(vec![Predicate::ZerosFrom(1), Predicate::Equals(0, 1)]);
    let expected = Predicate::All(vec![Predicate::ZerosFrom(1), Predicate::Equals(0, 2)]);;
    let next = predicate.apply(Instruction::Inc);
    assert!(next.implies(&expected));
    assert!(expected.implies(&next));
}

#[test]
fn test_zeros_apply_inc() {
    let predicate = Predicate::ZerosFrom(0);
    let expected = Predicate::All(vec![Predicate::ZerosFrom(1), Predicate::Equals(0, 1)]);
    let next = predicate.apply(Instruction::Inc);
    dbg!(&next);
    assert!(next.implies(&expected));
    assert!(expected.implies(&next));
}

#[derive(Debug)]
struct Proof {
    program: Program,
    invariants: Vec<Predicate>,
}

impl fmt::Display for Proof {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "    {:?}", &self.invariants[0])?;
        for i in 1..self.invariants.len() {
            writeln!(f, "{}   {:?}", self.program[i-1], self.invariants[i])?;
        }
        writeln!(f, "{}", self.program[self.program.len() - 1])
    }
}

fn prove_from_ip(program: &Program, start_ip: usize, verbose: bool) -> Option<Proof> {
    assert!(start_ip < program.len());
    if verbose { println!("{}", program) }
    let mut invariants = vec![Predicate::False; program.len()];
    for i in 0..start_ip {
        invariants[i] = Predicate::True;
    }

    let invariant = if start_ip == 0 {
        Predicate::ZerosFrom(0)
    } else if program[start_ip - 1].is_backward() {
        Predicate::Equals(0, 0)
    } else {
        Predicate::True
    };

    let mut queue = VecDeque::new();
    queue.push_back((start_ip, invariant));
    let mut counter = 0;

    while let Some((ip, invariant)) = queue.pop_front() {
        counter += 1;
        if counter > 64 { return None; }
        if ip >= program.len() {
            // We reached the end of the program.
            return None;
        }
        let old_invariant = &invariants[ip];
        if invariant.implies(old_invariant) {
            // We proved the current invariant.
            continue;
        }
        if verbose {
            println!("old: {:?}, incoming: {:?}", old_invariant, invariant);
        }
        invariants[ip] = invariant.intersect(old_invariant);
        let current_invariant = &invariants[ip];
        if verbose {
            println!("invariant[{}] = {:?}", ip, invariants[ip]);
        }

        let ((new_invariant, new_ip), maybe_other) = current_invariant.step(program, ip);
        queue.push_back((new_ip, new_invariant));
        if let Some((new_inv2, new_ip2)) = maybe_other {
            queue.push_back((new_ip2, new_inv2))
        }
    }

    Some(Proof { program: program.clone(), invariants })
}

fn prove_runs_forever(program: &Program) -> Option<Proof> {
    let mut nesting = 0;
    for ip in (0..program.len()).rev() {
        nesting += match program[ip] {
            Instruction::Backward(_) => 1,
            Instruction::Forward(_) => -1,
            _ => 0,
        };
        if ip == 0 || (nesting == 0 && program[ip - 1].is_backward()) {
            let maybe_proof = prove_from_ip(program, ip, false);
            if maybe_proof.is_some() {
                return maybe_proof;
            }
        }
    }
    None
}

/// Verify a proof by running the program and checking the predicate on every step.
#[cfg(test)]
fn verify_proof(proof: Option<Proof>) -> bool {
    if !proof.is_some() { return false; }
    let proof = proof.unwrap();
    let mut state = State::new(proof.program.clone());
    for _ in 0..1000 {
        match state.status {
            Status::TapeOverflow | Status::ValueOverflow => return true,
            Status::Finished => {
                println!("{}", &state);
                println!("Program finished");
                return false;
            },
            _ => ()
        }
        if !proof.invariants[state.ip].check(&state) {
            println!("IP = {}", state.ip);
            println!("Invariant failed: {:?}", &proof.invariants[state.ip]);
            println!("{}", &state);
            println!("{}", &proof);
            return false;
        }
        state.step();
    }
    true
}

#[cfg(test)]
fn test_program(prog_str: &str) {
    let program: Program = prog_str.parse().unwrap();
    let proof = prove_runs_forever(&program);
    dbg!(&proof);
    assert!(verify_proof(proof));
}

#[test]
fn test_simple_loop() {
    test_program("+[]");
}

#[test]
fn test_right_left() {
    test_program("+[><]");
}

#[test]
fn test_right_right_left() {
    test_program("+[>><+]");
}

#[test]
fn test_loop_with_init() {
    test_program("+[[]+]");
}

#[test]
fn test_nested_loop() {
    test_program("+[[>]<]");
}

fn solve_program(program: &Program) -> (State, Option<Proof>) {
    let mut state = run(program, 5000);

    if state.status == Status::Running {
        let maybe_proof = prove_runs_forever(program);
        if maybe_proof.is_some() {
            state.status = Status::RunsForever;
        }
        (state, maybe_proof)
    } else {
        (state, None)
    }
}

#[cfg(test)]
fn test_len(l: usize, finishing: usize) {
    let mut finished = 0;
    for p in gen_valid_programs(l) {
        let (state, proof) = solve_program(&p);
        match state.status {
            Status::Finished => finished += 1,
            
            Status::RunsForever => {
                println!("{}", p);
                assert!(verify_proof(proof))
            },

            Status::Running => panic!(),

            _ => (),
        }
    }
    assert_eq!(finished, finishing);
}

#[test]
fn test1() {
    test_len(1, 2);
}

#[test]
fn test2() {
    test_len(2, 7);
}

#[test]
fn test3() {
    test_len(3, 24);
}

#[test]
fn test4() {
    test_len(4, 98);
}

#[test]
fn test5() {
    test_len(5, 413);
}

#[test]
fn test6() {
    test_len(6, 1871);
}

#[test]
fn test7() {
    test_len(7, 8740);
}

#[derive(Debug)]
struct Stats {
    total: u64,
    finished: u64,
    run_forever: u64,
    overflow: u64,
    unknown: u64,
    longest_run: usize,
    longest_running_program: Option<Program>,
    longest_tape: usize,
    longest_tape_program: Option<Program>,
}

impl Stats {
    fn merge(&mut self, other: Stats) {
        self.total += other.total;
        self.finished += other.finished;
        self.run_forever += other.run_forever;
        self.overflow += other.overflow;
        self.unknown += other.unknown;
        if self.longest_run < other.longest_run {
            self.longest_run = other.longest_run;
            self.longest_running_program = other.longest_running_program
        }
        if self.longest_tape < other.longest_tape {
            self.longest_tape = other.longest_tape;
            self.longest_tape_program = other.longest_tape_program
        }
    }
}

fn program_stats(program: &Program) -> Stats {
    let (state, _) = solve_program(program);
    
    let mut finished = 0;
    let mut run_forever = 0;
    let mut overflow = 0;
    let mut unknown = 0;
    let mut longest_run = 0;
    let mut longest_running_program = None;
    let mut longest_tape = 0;
    let mut longest_tape_program = None;

    match state.status {
        Status::Finished => {
            finished = 1;
            longest_run = state.step;
            longest_running_program = Some(program.clone());
            longest_tape = state.tape.len();
            longest_tape_program = Some(program.clone());
        },
        Status::TapeOverflow | Status::ValueOverflow =>
            overflow = 1,
        Status::RunsForever => run_forever = 1,
        Status::Running => {
            unknown = 1;
            println!("    {}", program);
        }
    };

    Stats { total: 1, finished, run_forever, overflow, unknown, longest_run, longest_running_program, longest_tape, longest_tape_program }
}

// Generated by possible_programs.rs
const NPROGRAMS: &[u64] = &[
    1, 4, 17, 76, 354, 1704, 8421, 42508, 218318, 1137400, 5996938, 31940792,
    171605956, 928931280, 5061593709, 27739833228];

fn gen_and_solve(len: usize, prefix: &Program, opened_loops: usize) -> Stats {
    if prefix.len() + opened_loops == len {
        let mut program = prefix.clone();
        // Just one possible program
        for _ in 0..opened_loops {
            program.push(Instruction::Backward(0));
        }
        return program_stats(&program);
    }

    if opened_loops == 0 && prefix.len() != 0 {
        let (state, _) = solve_program(prefix);
        if state.status != Status::Finished {
            let nprograms = NPROGRAMS[len - prefix.len()];
            let (run_forever, overflow, unknown) = match state.status {
                Status::TapeOverflow | Status::ValueOverflow => (0, nprograms, 0),
                Status::RunsForever => (nprograms, 0, 0),
                Status::Running => {
                    // Hmm. Maybe we shouldn't skip these, because we might be able to prove that
                    // the program runs forever based on the rest of the program.
                    println!("    {}", prefix);
                    (0, 0, nprograms)
                },
                Status::Finished => unreachable!(),
            };

            return Stats { total: nprograms, finished: 0,
                           run_forever, overflow, unknown,
                           longest_run: 0, longest_running_program: None,
                           longest_tape: 0, longest_tape_program: None }
        }
    }

    let mut program = prefix.clone();
    program.push(Instruction::Inc);
    let mut stats = gen_and_solve(len, &program, opened_loops);
    program.pop();

    program.push(Instruction::Dec);
    stats.merge(gen_and_solve(len, &program, opened_loops));
    program.pop();

    program.push(Instruction::Left);
    stats.merge(gen_and_solve(len, &program, opened_loops));
    program.pop();

    program.push(Instruction::Right);
    stats.merge(gen_and_solve(len, &program, opened_loops));
    program.pop();

    if len - prefix.len() >= opened_loops + 2 {
        program.push(Instruction::Forward(0));
        stats.merge(gen_and_solve(len, &program, opened_loops + 1));
        program.pop();
    }

    if opened_loops > 0 {
        program.push(Instruction::Backward(0));
        stats.merge(gen_and_solve(len, &program, opened_loops - 1));
        program.pop();
    }

    stats
}

#[test]
fn test7_gen() {
    let stats = gen_and_solve(7, &"".parse().unwrap(), 0);
    assert_eq!(stats.total, 42508);
    assert_eq!(stats.finished, 8740);
    assert_eq!(stats.run_forever + stats.overflow, 1208 + 32560);
    assert_eq!(stats.unknown, 0);
    assert_eq!(stats.longest_run, 13);
    assert_eq!(stats.longest_tape, 8);
}

fn solve_len(len: usize) {
    println!("Length {}", len);
    println!("Total programs: {}\n", NPROGRAMS[len]);

    let stats = gen_and_solve(len, &"".parse().unwrap(), 0);
    println!("\nTotal: {}", stats.total);
    println!("Finished: {}", stats.finished);
    println!("Run forever: {}", stats.run_forever);
    println!("Overflow: {}", stats.overflow);
    println!("Unknown: {}", stats.unknown);
    println!("Longest run: {} {}", stats.longest_running_program.unwrap(), stats.longest_run);
    println!("Longest tape: {} {}", stats.longest_tape_program.unwrap(), stats.longest_tape);
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let arg: &str = &args[1];
    let len: usize = arg.parse().unwrap_or(0);
    if len == 0 {
        let program = arg.parse().unwrap();
        dbg!(&program);
        let (state, proof) = solve_program(&program);
        println!("{}", state);
        if let Some(p) = proof {
            println!("{}", p);
        }
    } else {
        solve_len(len)
    }
}
