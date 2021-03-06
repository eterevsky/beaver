use crate::brainfuck::{Instruction, Program, State, Status};
use crate::statement::{Term, Proof, Proposition};
use std::collections::VecDeque;
use std::fmt;

#[derive(PartialEq, Debug, Clone)]
pub enum LocalStatement {
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

    // Conjunction of a list of sub-statements.
    All(Vec<LocalStatement>),

    // Disjunction of a list of sub-statements.
    Any(Vec<LocalStatement>),
}

fn flatten_all(children: &mut Vec<LocalStatement>) {
    let mut new_children = Vec::new();
    for child in children.iter() {
        if let LocalStatement::All(grandchildren) = child {
            new_children.extend(grandchildren.iter().cloned());
        }
    }

    children.retain(|v| !v.is_all());
    children.extend_from_slice(&new_children);
}

fn optimize_all(children: Vec<LocalStatement>) -> Vec<LocalStatement> {
    let mut children = children.clone();
    flatten_all(&mut children);
    for i in 0..children.len() {
        for j in 0..children.len() {
            if i == j {
                continue;
            }
            if children[i].implies(&children[j]) {
                children[j] = LocalStatement::True;
            } else if children[i].incompatible(&children[j]) {
                return vec![LocalStatement::False];
            }
        }
    }
    children.retain(|v| *v != LocalStatement::True);
    children
}

fn flatten_any(children: &mut Vec<LocalStatement>) {
    // TODO: Expand Any inside of All?
    let mut new_children = Vec::new();
    for child in children.iter() {
        if let LocalStatement::Any(grandchildren) = child {
            new_children.extend(grandchildren.iter().cloned());
        }
    }

    children.retain(|v| !v.is_any());
    children.extend_from_slice(&new_children);
}

fn optimize_any(mut children: Vec<LocalStatement>) -> Vec<LocalStatement> {
    flatten_any(&mut children);
    for i in 0..children.len() {
        for j in 0..children.len() {
            if i != j && children[j].implies(&children[i]) {
                children[j] = LocalStatement::False;
            }
        }
    }
    children.retain(|v| *v != LocalStatement::False);
    children
}

/// Expand the expression  (any1 | any2 | ... ) & (all1 & all2 & ...) into
/// (any1 & all1 & all2 & ...) | (any2 & all1 & all2 & ...) | ...
fn expand_any_clause(
    any_children: &[LocalStatement],
    all_children: Vec<LocalStatement>,
) -> LocalStatement {
    let mut new_any = Vec::new();
    for any_child in any_children.iter() {
        let mut clause = all_children.clone();
        clause.push(any_child.clone());
        new_any.push(LocalStatement::All(clause));
    }
    LocalStatement::Any(new_any)
}

impl LocalStatement {
    fn is_any(&self) -> bool {
        match self {
            LocalStatement::Any(_) => true,
            _ => false,
        }
    }

    fn is_all(&self) -> bool {
        match self {
            LocalStatement::All(_) => true,
            _ => false,
        }
    }

    pub fn check(&self, state: &State) -> bool {
        match self {
            LocalStatement::True => true,
            LocalStatement::False => false,
            LocalStatement::ZerosFrom(offset) => {
                let start = state.pos as isize + offset;
                if start < 0 {
                    false
                } else {
                    ((start as usize)..state.tape.len()).all(|i| state.tape[i] == 0)
                }
            }
            LocalStatement::Equals(offset, x) => state.val_at_offset(*offset) == Some(*x),
            LocalStatement::GreaterThan(offset, x) => match state.val_at_offset(*offset) {
                None => false,
                Some(v) => v > *x,
            },
            LocalStatement::All(children) => children.iter().all(|c| c.check(state)),
            LocalStatement::Any(children) => children.iter().any(|c| c.check(state)),
        }
    }

    fn optimize(self) -> Self {
        match self {
            LocalStatement::All(children) => {
                let children: Vec<LocalStatement> =
                    children.iter().map(|c| c.clone().optimize()).collect();
                let temp_self = LocalStatement::All(children.clone());

                for child in children.iter() {
                    match child {
                        LocalStatement::False => return LocalStatement::False,

                        LocalStatement::Equals(o, v) => {
                            if *v != 0 && temp_self.implies(&LocalStatement::Equals(*o, 0)) {
                                return LocalStatement::False;
                            }
                        }

                        LocalStatement::GreaterThan(o, _) => {
                            if temp_self.implies(&LocalStatement::Equals(*o, 0)) {
                                return LocalStatement::False;
                            }
                        }

                        _ => (),
                    }
                }

                for i in 0..children.len() {
                    if let LocalStatement::Any(any_children) = &children[i] {
                        let mut all_children = children.clone();
                        all_children[i] = LocalStatement::True;

                        return expand_any_clause(any_children, all_children).optimize();
                    }
                }

                let new_children = optimize_all(children);
                match new_children.len() {
                    0 => LocalStatement::True,
                    1 => new_children[0].clone(),
                    _ => LocalStatement::All(new_children),
                }
            }

            LocalStatement::Any(children) => {
                let children: Vec<LocalStatement> =
                    children.iter().map(|c| c.clone().optimize()).collect();
                let new_children = optimize_any(children);
                match new_children.len() {
                    0 => LocalStatement::False,
                    1 => new_children[0].clone(),
                    _ => LocalStatement::Any(new_children),
                }
            }

            _ => self,
        }
    }

    // We assume that self is opimized, i.e. All is higer than Offset and Offset is
    // collapsed.
    pub fn implies(&self, other: &LocalStatement) -> bool {
        match (self, other) {
            (_, LocalStatement::True) => true,

            (LocalStatement::False, _) => true,

            (s, LocalStatement::All(children)) => children.iter().all(|c| s.implies(c)),

            (LocalStatement::Any(children), o) => children.iter().all(|c| c.implies(o)),

            // These two rules are a simplifications.
            (s, LocalStatement::Any(children)) => children.iter().any(|c| s.implies(c)),

            (LocalStatement::All(children), o) => children.iter().any(|c| c.implies(o)),

            (LocalStatement::ZerosFrom(offset_x), LocalStatement::ZerosFrom(offset_y)) => {
                *offset_x <= *offset_y
            }

            (LocalStatement::Equals(offset_x, x), LocalStatement::Equals(offset_y, y)) => {
                *offset_x == *offset_y && *x == *y
            }

            (LocalStatement::ZerosFrom(offset_x), LocalStatement::Equals(offset_y, y)) => {
                *offset_x <= *offset_y && *y == 0
            }

            (LocalStatement::Equals(offset_x, x), LocalStatement::GreaterThan(offset_y, y)) => {
                *offset_x == *offset_y && x > y
            }

            (
                LocalStatement::GreaterThan(offset_x, x),
                LocalStatement::GreaterThan(offset_y, y),
            ) => *offset_x == *offset_y && x >= y,

            _ => false,
        }
    }

    // Checks whether this predicate implies negation of another predicate.
    fn incompatible(&self, other: &LocalStatement) -> bool {
        match (self, other) {
            (LocalStatement::False, _) => true,

            (_, LocalStatement::False) => true,

            (s, LocalStatement::Any(children)) => children.iter().all(|c| s.incompatible(c)),

            (LocalStatement::Any(children), o) => children.iter().all(|c| c.incompatible(o)),

            (s, LocalStatement::All(children)) => children.iter().any(|c| s.incompatible(c)),

            (LocalStatement::All(children), o) => children.iter().any(|c| c.incompatible(o)),

            (LocalStatement::ZerosFrom(zeros_from), LocalStatement::Equals(offset, v)) => {
                zeros_from <= offset && *v != 0
            }

            (LocalStatement::Equals(offset, v), LocalStatement::ZerosFrom(zeros_from)) => {
                zeros_from <= offset && *v != 0
            }

            (LocalStatement::ZerosFrom(zeros_from), LocalStatement::GreaterThan(offset, _)) => {
                zeros_from <= offset
            }

            (LocalStatement::GreaterThan(offset, _), LocalStatement::ZerosFrom(zeros_from)) => {
                zeros_from <= offset
            }

            (LocalStatement::Equals(offset_e, v), LocalStatement::GreaterThan(offset_g, l)) => {
                offset_e == offset_g && v <= l
            }

            (LocalStatement::GreaterThan(offset_g, l), LocalStatement::Equals(offset_e, v)) => {
                offset_e == offset_g && v <= l
            }

            (LocalStatement::Equals(o1, v1), LocalStatement::Equals(o2, v2)) => {
                o1 == o2 && v1 != v2
            }

            _ => false,
        }
    }

    // Recursively apply the instruction.
    fn apply_impl(&self, instruction: Instruction) -> Self {
        match (instruction, self.clone()) {
            (i, LocalStatement::All(children)) => {
                LocalStatement::All(children.iter().map(|c| c.apply_impl(i)).collect()).optimize()
            }

            (i, LocalStatement::Any(children)) => {
                LocalStatement::Any(children.iter().map(|c| c.apply_impl(i)).collect()).optimize()
            }

            (_, LocalStatement::True) => LocalStatement::True,

            (_, LocalStatement::False) => LocalStatement::False,

            (Instruction::Inc, LocalStatement::ZerosFrom(offset)) if offset > 0 => {
                LocalStatement::ZerosFrom(offset)
            }

            (Instruction::Inc, LocalStatement::ZerosFrom(offset)) if offset <= 0 => {
                let mut children = vec![LocalStatement::ZerosFrom(1), LocalStatement::Equals(0, 1)];
                for i in offset..0 {
                    children.push(LocalStatement::Equals(i, 0));
                }
                LocalStatement::All(children)
            }

            (Instruction::Inc, LocalStatement::Equals(0, x)) => LocalStatement::Equals(0, x + 1),

            (Instruction::Inc, LocalStatement::Equals(offset, x)) => {
                LocalStatement::Equals(offset, x)
            }

            (Instruction::Inc, LocalStatement::GreaterThan(0, x)) => {
                LocalStatement::GreaterThan(0, x + 1)
            }

            (Instruction::Inc, LocalStatement::GreaterThan(offset, x)) => {
                LocalStatement::GreaterThan(offset, x)
            }

            (Instruction::Dec, LocalStatement::ZerosFrom(offset)) if offset <= 0 => {
                LocalStatement::False
            }

            (Instruction::Dec, LocalStatement::ZerosFrom(offset)) => {
                LocalStatement::ZerosFrom(offset)
            }

            (Instruction::Dec, LocalStatement::Equals(0, 0)) => LocalStatement::False,

            (Instruction::Dec, LocalStatement::Equals(0, x)) => LocalStatement::Equals(0, x - 1),

            (Instruction::Dec, LocalStatement::Equals(offset, x)) => {
                LocalStatement::Equals(offset, x)
            }

            (Instruction::Dec, LocalStatement::GreaterThan(0, 0)) => LocalStatement::True,

            (Instruction::Dec, LocalStatement::GreaterThan(0, x)) => {
                LocalStatement::GreaterThan(0, x - 1)
            }

            (Instruction::Dec, LocalStatement::GreaterThan(offset, x)) => {
                LocalStatement::GreaterThan(offset, x)
            }

            (Instruction::Right, LocalStatement::ZerosFrom(offset)) => {
                LocalStatement::ZerosFrom(offset - 1)
            }

            (Instruction::Right, LocalStatement::Equals(offset, x)) => {
                LocalStatement::Equals(offset - 1, x)
            }

            (Instruction::Right, LocalStatement::GreaterThan(offset, x)) => {
                LocalStatement::GreaterThan(offset - 1, x)
            }

            (Instruction::Left, LocalStatement::ZerosFrom(offset)) => {
                LocalStatement::ZerosFrom(offset + 1)
            }

            (Instruction::Left, LocalStatement::Equals(offset, x)) => {
                LocalStatement::Equals(offset + 1, x)
            }

            (Instruction::Left, LocalStatement::GreaterThan(offset, x)) => {
                LocalStatement::GreaterThan(offset + 1, x)
            }

            _ => unreachable!(),
        }
    }

    // Construct a weaker version of the predicate by modifying all the predicates with offset
    // farther than `max_offset`.
    fn weaken(self, max_offset: isize) -> Self {
        match self {
            LocalStatement::Equals(offset, _) if offset.abs() > max_offset => LocalStatement::True,
            LocalStatement::GreaterThan(offset, _) if offset.abs() > max_offset => {
                LocalStatement::True
            }
            LocalStatement::All(mut children) => {
                LocalStatement::All(children.drain(..).map(|c| c.weaken(max_offset)).collect())
                    .optimize()
            }
            LocalStatement::Any(mut children) => {
                LocalStatement::Any(children.drain(..).map(|c| c.weaken(max_offset)).collect())
                    .optimize()
            }
            _ => self,
        }
    }

    // Modify the predicate after executing the instruction.
    fn apply(&self, instruction: Instruction) -> Self {
        let predicate = self.apply_impl(instruction);

        if instruction == Instruction::Inc && !predicate.implies(&LocalStatement::GreaterThan(0, 0))
        {
            LocalStatement::All(vec![LocalStatement::GreaterThan(0, 0), predicate]).optimize()
        } else {
            predicate
        }
    }

    pub fn step(&self, program: &Program, ip: usize) -> ((Self, usize), Option<(Self, usize)>) {
        assert!(ip < program.len());
        match program[ip] {
            Instruction::Forward(target) => {
                if self.implies(&LocalStatement::GreaterThan(0, 0)) {
                    ((self.clone(), ip + 1), None)
                } else if self.implies(&LocalStatement::Equals(0, 0)) {
                    ((self.clone(), target), None)
                } else {
                    (
                        (
                            LocalStatement::All(vec![
                                self.clone(),
                                LocalStatement::GreaterThan(0, 0),
                            ])
                            .optimize(),
                            ip + 1,
                        ),
                        Some((
                            LocalStatement::All(vec![self.clone(), LocalStatement::Equals(0, 0)])
                                .optimize(),
                            target,
                        )),
                    )
                }
            }
            Instruction::Backward(target) => {
                if self.implies(&LocalStatement::GreaterThan(0, 0)) {
                    ((self.clone(), target), None)
                } else if self.implies(&LocalStatement::Equals(0, 0)) {
                    ((self.clone(), ip + 1), None)
                } else {
                    (
                        (
                            LocalStatement::All(vec![
                                self.clone(),
                                LocalStatement::GreaterThan(0, 0),
                            ])
                            .optimize(),
                            target,
                        ),
                        Some((
                            LocalStatement::All(vec![self.clone(), LocalStatement::Equals(0, 0)])
                                .optimize(),
                            ip + 1,
                        )),
                    )
                }
            }
            instruction => ((self.apply(instruction), ip + 1), None),
        }
    }

    // Find a predicate that follows from both self and other.
    pub fn intersect(&self, other: &LocalStatement, max_offset: isize) -> Self {
        if self.implies(other) {
            other.clone()
        } else if other.implies(self) {
            self.clone()
        } else {
            LocalStatement::Any(vec![self.clone(), other.clone()]).weaken(max_offset)
        }
    }

    fn as_proposition(self) -> Proposition {
        match self {
            LocalStatement::True => Proposition::True,
            LocalStatement::False => Proposition::False,

            LocalStatement::ZerosFrom(0) => Proposition::or2(
                Proposition::Equals(Term::tape(Term::Var(0)), Term::Const(0)),
                Proposition::Greater(Term::Pos, Term::Var(0)),
            ),
            LocalStatement::ZerosFrom(x) => Proposition::or2(
                Proposition::Equals(Term::tape(Term::Var(0)), Term::Const(0)),
                Proposition::Greater(Term::sum2(Term::Pos, Term::Const(x)), Term::Var(0)),
            ),

            LocalStatement::Equals(0, y) => Proposition::Equals(Term::tape(Term::Pos), Term::Const(y as isize)),
            LocalStatement::Equals(x, y) => Proposition::Equals(
                Term::tape(Term::sum2(Term::Pos, Term::Const(x))),
                Term::Const(y as isize)),

            LocalStatement::GreaterThan(0, y) => Proposition::Greater(Term::tape(Term::Pos), Term::Const(y as isize)),
            LocalStatement::GreaterThan(x, y) => Proposition::Greater(
                Term::tape(Term::sum2(Term::Pos, Term::Const(x))),
                Term::Const(y as isize)),

            LocalStatement::All(mut clauses) => 
                Proposition::and_ind(clauses.drain(..).map(|x| x.as_proposition()).collect()),

            LocalStatement::Any(mut clauses) => 
                Proposition::or_ind(clauses.drain(..).map(|x| x.as_proposition()).collect()),
        }
    }
}

#[test]
fn test_optimize() {
    let predicate = LocalStatement::All(vec![
        LocalStatement::All(vec![
            LocalStatement::Equals(1, 2),
            LocalStatement::Equals(1, 2),
        ]),
        LocalStatement::Equals(1, 2),
        LocalStatement::True,
    ]);
    let optimized = predicate.optimize();
    assert_eq!(optimized, LocalStatement::Equals(1, 2));
}

#[test]
fn test_check_zeros_from() {
    let mut state = State::new("+".parse().unwrap());
    assert!(LocalStatement::ZerosFrom(0).check(&state));
    assert!(!LocalStatement::ZerosFrom(-1).check(&state));
    assert!(LocalStatement::ZerosFrom(1).check(&state));

    state.step();
    assert!(!LocalStatement::ZerosFrom(0).check(&state));
    assert!(!LocalStatement::ZerosFrom(-1).check(&state));
    assert!(LocalStatement::ZerosFrom(1).check(&state));
}

#[test]
fn test_imply_zeros_from() {
    assert!(LocalStatement::ZerosFrom(-1).implies(&LocalStatement::Equals(0, 0)));
    assert!(LocalStatement::ZerosFrom(0).implies(&LocalStatement::Equals(0, 0)));
    assert!(!LocalStatement::ZerosFrom(1).implies(&LocalStatement::Equals(0, 0)));

    assert!(LocalStatement::ZerosFrom(0).implies(&LocalStatement::Equals(1, 0)));
    assert!(LocalStatement::ZerosFrom(1).implies(&LocalStatement::Equals(1, 0)));
    assert!(!LocalStatement::ZerosFrom(2).implies(&LocalStatement::Equals(1, 0)));
}

#[test]
fn test_weaken1() {
    let predicate = LocalStatement::Equals(-2, 1);
    let weaker = predicate.clone().weaken(2);
    assert!(predicate.implies(&weaker));
}

#[test]
fn test_weaken_and() {
    let predicate = LocalStatement::All(vec![
        LocalStatement::Equals(-2, 1),
        LocalStatement::ZerosFrom(1),
    ]);
    let weaker = predicate.clone().weaken(2);
    assert!(predicate.implies(&weaker));
}

#[test]
fn test_weaken_or() {
    let predicate = LocalStatement::Any(vec![
        LocalStatement::Equals(-2, 1),
        LocalStatement::ZerosFrom(1),
    ]);
    let weaker = predicate.clone().weaken(2);
    assert!(predicate.implies(&weaker));
}

#[test]
fn test_composite_pred_apply() {
    let predicate = LocalStatement::All(vec![
        LocalStatement::ZerosFrom(1),
        LocalStatement::Equals(0, 1),
    ]);
    let expected = LocalStatement::All(vec![
        LocalStatement::ZerosFrom(1),
        LocalStatement::Equals(0, 2),
    ]);
    let next = predicate.apply(Instruction::Inc);
    assert!(next.implies(&expected));
    assert!(expected.implies(&next));
}

#[test]
fn test_zeros_apply_inc() {
    let predicate = LocalStatement::ZerosFrom(0);
    let expected = LocalStatement::All(vec![
        LocalStatement::ZerosFrom(1),
        LocalStatement::Equals(0, 1),
    ]);
    let next = predicate.apply(Instruction::Inc);
    dbg!(&next);
    assert!(next.implies(&expected));
    assert!(expected.implies(&next));
}

#[derive(Debug)]
pub struct LocalProof {
    program: Program,
    invariants: Vec<LocalStatement>,
}

impl LocalProof {
    pub fn as_proof(mut self) -> Proof {
        Proof {
            program: self.program,
            invariants: self.invariants.drain(..).map(|i| i.as_proposition()).collect(),
        }
    }
}

impl fmt::Display for LocalProof {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "    {:?}", &self.invariants[0])?;
        for i in 1..self.invariants.len() {
            writeln!(f, "{}   {:?}", self.program[i - 1], self.invariants[i])?;
        }
        writeln!(f, "{}", self.program[self.program.len() - 1])
    }
}

pub struct LocalProver {
    // During weaken() we will drop any predicates about cells that are further from
    // the current cell than this.
    max_offset: isize,
    // Number of steps in proof search.
    max_steps: usize,
}

impl LocalProver {
    pub fn new(max_offset: isize, max_steps: usize) -> Self {
        LocalProver {
            max_offset,
            max_steps,
        }
    }

    fn prove_from_ip(
        &self,
        program: &Program,
        start_ip: usize,
        partial_proof: &Vec<LocalStatement>,
        verbose: bool,
    ) -> Option<Vec<LocalStatement>> {
        assert!(start_ip < program.len());
        let mut invariants = partial_proof.clone();

        let invariant = if start_ip == 0 {
            LocalStatement::ZerosFrom(0)
        } else if program[start_ip - 1].is_backward() {
            LocalStatement::Equals(0, 0)
        } else if program[start_ip - 1].is_forward() {
            LocalStatement::GreaterThan(0, 0)
        } else {
            LocalStatement::True
        };

        let mut queue = VecDeque::new();
        queue.push_back((start_ip, invariant));
        let mut counter = 0;

        while let Some((ip, invariant)) = queue.pop_front() {
            if counter >= self.max_steps {
                return None;
            }
            counter += 1;
            if ip >= program.len() {
                // We reached the end of the program.
                return None;
            }
            let old_invariant = &invariants[ip];
            if invariant.implies(old_invariant) {
                // We proved the old invariant.
                continue;
            }
            if verbose {
                println!("old: {:?}, incoming: {:?}", old_invariant, invariant);
            }
            invariants[ip] = invariant.intersect(old_invariant, self.max_offset);
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

        Some(invariants)
    }

    pub fn prove_runs_forever(&self, program: &Program) -> Option<LocalProof> {
        assert!(program.len() >= 2);
        let mut ip = program.len() - 2;
        let mut invariants = vec![LocalStatement::False; program.len()];
        loop {
            if ip == 0
                || (2 <= ip
                    && ip < program.len() - 1
                    && match (program[ip - 1], program[ip], program[ip + 1]) {
                        (_, Instruction::Inc, Instruction::Backward(_)) => true,
                        (Instruction::Forward(_), _, _) => true,
                        (Instruction::Backward(_), _, _) => true,
                        _ => false,
                    })
            {
                let mut temp_proof = LocalProof {
                    program: program.clone(),
                    invariants: invariants.clone(),
                };
                // println!("ip = {}", ip);
                // println!("current proof:\n{}", temp_proof.to_string());
                let maybe_proof = self.prove_from_ip(program, ip, &invariants, false);
                if let Some(new_invariants) = maybe_proof {
                    temp_proof.invariants = new_invariants.clone();
                    // println!("new proof:\n{}", temp_proof.to_string());
                    invariants = new_invariants;
                    if program.nesting_at(ip) == 0 {
                        for i in 0..invariants.len() {
                            if invariants[i] == LocalStatement::False {
                                invariants[i] = LocalStatement::True;
                            } else {
                                break;
                            }
                        }
                        return Some(LocalProof {
                            invariants,
                            program: program.clone(),
                        });
                    } else {
                        assert!(invariants[0] == LocalStatement::False);
                        ip = 1;
                        while invariants[ip] == LocalStatement::False {
                            ip += 1;
                        }
                        ip -= 1;
                    }
                } else {
                    if ip == 0 {
                        break;
                    }
                    ip -= 1
                }
            } else {
                if ip == 0 {
                    break;
                }
                ip -= 1;
            }
        }
        None
    }
}

/// Verify a proof by running the program and checking the predicate on every step.
pub fn verify_proof(proof: &LocalProof) -> bool {
    let mut state = State::new(proof.program.clone());
    for _ in 0..1000 {
        match state.status {
            Status::TapeOverflow | Status::ValueOverflow => return true,
            Status::Finished => {
                println!("{}", &state);
                println!("Program finished");
                return false;
            }
            _ => (),
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
    let proof = LocalProver::new(2, 64).prove_runs_forever(&program);
    assert!(proof.is_some());
    assert!(verify_proof(&proof.unwrap()));
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

