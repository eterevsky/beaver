use std::collections::VecDeque;
use std::env;

const INC: u8 = '+' as u8;
const DEC: u8 = '-' as u8;
const LEFT: u8 = '<' as u8;
const RIGHT: u8 = '>' as u8;
const LABEL: u8 = '[' as u8;
const LOOP: u8 = ']' as u8;

static INSTRUCTIONS: &'static [u8] = &[INC, DEC, LEFT, RIGHT, LABEL, LOOP];

fn gen_valid_programs(len: usize) -> Vec<Vec<u8>> {
    let mut programs = Vec::new();
    for mut pcode in 0..6usize.pow(len as u32) {
        let mut p = Vec::with_capacity(len);
        let mut nesting: isize = 0;
        let mut well_formed = true;
        for _ in 0..len {
            let instruction: u8 = INSTRUCTIONS[pcode % 6];
            pcode /= 6;
            p.push(instruction);
            nesting += match instruction {
                LABEL => 1,
                LOOP => -1,
                _ => 0,
            };
            if nesting < 0 {
                well_formed = false;
                break;
            }
        }
        if well_formed && nesting == 0 {
            programs.push(p);
        }
    }
    return programs;
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum Status {
    Running,
    TapeOverflow,
    ValueOverflow,
    Finished,
    Infinite,
}

#[derive(Clone, Debug)]
struct State {
    tape: Vec<u8>,
    ip: usize,
    pos: usize,
    step: usize,
    status: Status,
}

impl State {
    fn new() -> Self { State { tape: vec![0], ip: 0, pos: 0, step: 0, status: Status::Running } }

    fn val_at_offset(&self, offset: isize) -> u8 {
        self.tape[(self.pos as isize + offset) as usize]
    }
}

fn find_matching_label(program: &[u8], mut ip: usize) -> usize {
    debug_assert!(program[ip] == LOOP);
    let mut nesting = 1;
    while nesting > 0 {
        ip -= 1;
        nesting += match program[ip] {
            LOOP => 1,
            LABEL => -1,
            _ => 0,
        };
    };
    ip
}

fn simulate_step(program: &[u8], mut state: State) -> State {
    state.step += 1;
    match program[state.ip] {
        INC => {
            if state.tape[state.pos] == 255 {
                state.status = Status::ValueOverflow;
                return state;
            }
            state.tape[state.pos] += 1;
        },
        DEC => {
            if state.tape[state.pos] == 0 {
                state.status = Status::ValueOverflow;
                return state;
            }
            state.tape[state.pos] -= 1;
        },
        RIGHT => {
            state.pos += 1;
            if state.pos >= state.tape.len() {
                state.tape.push(0);
            }
        },
        LEFT => {
            if state.pos == 0 {
                state.status = Status::TapeOverflow;
                return state;
            } else {
                state.pos -= 1;
            }
            
        },
        _ => {}
    };
    if program[state.ip] == LOOP && state.tape[state.pos] != 0 {
        state.ip = find_matching_label(program, state.ip);
    } else {
        state.ip += 1;
        if state.ip >= program.len() {
            state.status = Status::Finished;
        }
    }
    state
}

fn simulate(program: &[u8], steps: usize) -> State {
    let mut state = State::new();
    for _ in 0..steps {
        state = simulate_step(program, state);
        if state.status != Status::Running { break; }
    }
    state
}

#[derive(PartialEq, Debug, Clone)]
enum Predicate {
    // Always true in any state.
    True,
    
    // The tape starting from current position + offset is all zeros.
    ZerosFrom(isize),

    // A value at a given offset equals to a constant.
    Equals(isize, u8),

    // A value at a given offset is greater than a constant.
    GreaterThan(isize, u8),

    // Conjunction of a list of predicates.
    All(Vec<Predicate>),
}

fn remove_true_from_all(children: &mut Vec<Predicate>) {
    let mut i = 0;
    while i < children.len() {
        if children[i] == Predicate::True {
            children.swap_remove(i);
        } else {
            i += 1;
        }
    }
}

fn flatten_all(children: &mut Vec<Predicate>) {
    let mut i = 0;
    while i < children.len() {
        let child = children[i].clone();
        if let Predicate::All(grandchildren) = child {
            children.extend(grandchildren.iter().cloned());
            children[i] = Predicate::True;
        } else {
            i += 1;
        }
    }
    remove_true_from_all(children);
}

fn optimize_all(children: Vec<Predicate>) -> Vec<Predicate> {
    let mut children = children.clone();
    flatten_all(&mut children);
    for i in 0..children.len() {
        for j in 0..children.len() {
            if i != j && children[i].implies(&children[j]) { 
                children[j] = Predicate::True;
            }
        }
    }
    remove_true_from_all(&mut children);
    children
}

impl Predicate {
    fn check(&self, state: &State) -> bool {
        match self {
            Predicate::True => true,
            Predicate::ZerosFrom(offset) => {
                let start = state.pos as isize + offset;
                if start < 0 {
                    false
                } else {
                    ((start as usize)..state.tape.len()).all(|i| state.tape[i] == 0)
                }
            },
            Predicate::Equals(offset, x) => state.val_at_offset(*offset) == *x,
            Predicate::GreaterThan(offset, x) => state.val_at_offset(*offset) > *x,
            Predicate::All(children) => children.iter().all(|c| c.check(state))
        }
    }

    fn optimize(self) -> Self {
        if let Predicate::All(children) = self {
            let new_children = optimize_all(children);
            match new_children.len() {
                0 => Predicate::True,
                1 => new_children[0].clone(),
                _ => Predicate::All(new_children)
            }
        } else {
            self
        }
    }

    // We assume that self is opimized, i.e. All is higer than Offset and Offset is
    // collapsed.
    fn implies(&self, other: &Predicate) -> bool {
        match (self, other) {
            (s, Predicate::All(children)) => children.iter().all(|c| s.implies(c)),

            (Predicate::All(children), o) => children.iter().any(|c| c.implies(o)),

            (_, Predicate::True) => true,

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

    // Recursively apply the instruction.  
    fn apply_impl(&self, instruction: u8) -> Self {
        match (instruction, self.clone()) {
            (LOOP, p) => p,

            (LABEL, p) => p,

            (i, Predicate::All(children)) => 
                Predicate::All(children.iter().map(|c| c.apply_impl(i)).collect()).optimize(),

            (_, Predicate::True) => Predicate::True,

            (INC, Predicate::ZerosFrom(offset)) if offset > 0 => Predicate::ZerosFrom(offset),

            (INC, Predicate::ZerosFrom(offset)) if offset <= 0 =>
                Predicate::All(vec![Predicate::ZerosFrom(1), Predicate::Equals(0, 1)]),

            (INC, Predicate::Equals(0, x)) => Predicate::Equals(0, x + 1),
           
            (INC, Predicate::Equals(offset, x)) => Predicate::Equals(offset, x),

            (INC, Predicate::GreaterThan(0, x)) => Predicate::GreaterThan(0, x + 1),
           
            (INC, Predicate::GreaterThan(offset, x)) => Predicate::GreaterThan(offset, x),


            (DEC, Predicate::ZerosFrom(offset)) => Predicate::ZerosFrom(offset),

            (DEC, Predicate::Equals(0, x)) => Predicate::Equals(0, x - 1),
           
            (DEC, Predicate::Equals(offset, x)) => Predicate::Equals(offset, x),

            (DEC, Predicate::GreaterThan(0, 0)) => Predicate::True,
           
            (DEC, Predicate::GreaterThan(0, x)) => Predicate::GreaterThan(0, x - 1),
           
            (DEC, Predicate::GreaterThan(offset, x)) => Predicate::GreaterThan(offset, x),


            (RIGHT, Predicate::ZerosFrom(offset)) => Predicate::ZerosFrom(offset - 1),

            (RIGHT, Predicate::Equals(offset, x)) => Predicate::Equals(offset - 1, x),

            (RIGHT, Predicate::GreaterThan(offset, x)) => Predicate::GreaterThan(offset - 1, x),


            (LEFT, Predicate::ZerosFrom(offset)) => Predicate::ZerosFrom(offset + 1),

            (LEFT, Predicate::Equals(offset, x)) => Predicate::Equals(offset + 1, x),

            (LEFT, Predicate::GreaterThan(offset, x)) => Predicate::GreaterThan(offset + 1, x),

            _ => unreachable!()
        }
    }

    // Recursively apply the instruction.  
    fn apply(&self, instruction: u8) -> Self {
        let predicate = self.apply_impl(instruction);

        if instruction == INC && !predicate.implies(&Predicate::GreaterThan(0, 0)) {
            Predicate::All(vec![Predicate::GreaterThan(0, 0), predicate]).optimize()
        } else {
            predicate
        } 
    }

    // Find a predicate that follows from both self and other.
    fn intersect(&self, other: &Predicate) -> Self {
        if let Predicate::All(children) = self {
            let mut new_children = Vec::new();
            for child in children.iter() {
                let new_child = child.intersect(other);
                if !Predicate::True.implies(&new_child) {
                    new_children.push(new_child)
                }
            }
            match new_children.len() {
                0 => Predicate::True,
                1 => new_children[0].clone(),
                _ => Predicate::All(new_children)
            }
        } else if self.implies(other) {
            other.clone()
        } else if other.implies(self) {
            self.clone()
        } else {
            Predicate::True
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
    let state = State::new();
    assert!(Predicate::ZerosFrom(0).check(&state));
    assert!(!Predicate::ZerosFrom(-1).check(&state));
    assert!(Predicate::ZerosFrom(1).check(&state));

    let state = simulate_step(b"+", state);
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

#[derive(Debug)]
struct Proof {
    start_ip: usize,
    invariants: Vec<Predicate>
}

fn prove_starting_with_invariant(program: &[u8], state: &State, invariant: Predicate) -> Option<Proof> {
    if !invariant.check(state) {
        return None;
    }

    let mut invariants = vec![Predicate::True; program.len()];
    let mut visited = vec![false; program.len()];
    let start_ip = state.ip;

    let mut queue = VecDeque::new();
    queue.push_back((start_ip, invariant));
    let mut counter = 0;

    while let Some((ip, invariant)) = queue.pop_front() {
        counter += 1;
        if counter > 32 { return None; }
        println!("{} {:?}", ip, &invariant);
        // dbg!(ip, &invariant);
        if ip >= program.len() {
            // We reached the end of the program.
            return None;
        }
        if visited[ip] {
            let current_invariant = &invariants[ip];
            if invariant.implies(current_invariant) {
                // We proved the current invariant.
                continue;
            }
            // dbg!(&current_invariant);
            invariants[ip] = invariant.intersect(current_invariant);
            println!("invariant[{}] = {:?}", ip, invariants[ip]);
            // dbg!(&invariants[ip]);
        } else {
            visited[ip] = true;
            invariants[ip] = invariant;
        }

        let current_invariant = &invariants[ip];
        if program[ip] == LOOP {
            if current_invariant.implies(&Predicate::GreaterThan(0, 0)) {
                queue.push_back((find_matching_label(program, ip), current_invariant.clone()));
            } else if current_invariant.implies(&Predicate::Equals(0, 0)) {
                queue.push_back((ip + 1, current_invariant.clone()));
            } else {
                // Both cases can take place.
                let jump_back_inv = Predicate::All(
                    vec![Predicate::GreaterThan(0, 0), current_invariant.clone()]).optimize();
                let go_through_inv = Predicate::All(
                    vec![Predicate::Equals(0, 0), current_invariant.clone()]).optimize();
                queue.push_back((find_matching_label(program, ip), jump_back_inv));
                queue.push_back((ip + 1, go_through_inv));
            };
        } else {
            let instruction = program[ip];
            queue.push_back((ip + 1, current_invariant.apply(instruction)))
        }
    }

    Some(Proof {
        start_ip,
        invariants,
    })
}

//// Old solver, in which I try proving starting from different points in the program's execution.
// fn prove_infinite(program: &[u8], state: &State) -> Option<Proof> {
//     let mut starting_points = vec![false; program.len()];
//     let mut state: State = (*state).clone();

//     while !starting_points[state.ip] {
//         starting_points[state.ip] = true;

//         let try_invariants = vec![
//             Predicate::GreaterThan(0, 0),
//             Predicate::ZerosFrom(1),
//             Predicate::Equals(0, state.tape[state.pos]),
//             Predicate::All(vec![Predicate::ZerosFrom(1),
//                                 Predicate::Equals(0, state.tape[state.pos])]),
//         ];

//         for invariant in try_invariants {
//             let maybe_proof = prove_starting_with_invariant(program, &state, invariant);
//             if maybe_proof.is_some() {
//                 return maybe_proof;
//             }
//         }

//         state = simulate_step(program, state);
//     }

//     return None
// }

fn prove_from_start(program: &[u8]) -> Option<Proof> {
    let state = State::new();
    prove_starting_with_invariant(program, &state, Predicate::ZerosFrom(0))
}

#[test]
fn test_simple_loop() {
    let proof = prove_infinite(
        &[INC, LABEL, LOOP],
        &State {tape: vec![1], ip: 1, step: 1, pos: 0, status: Status::Running } );
    assert!(proof.is_some());
}

#[test]
fn test_right_left() {
    let p = &[INC, LABEL, RIGHT, LEFT, LOOP];
    let state = simulate(p, 2000);
    let proof = prove_infinite(p, &state);
    assert!(proof.is_some());
}

#[test]
fn test_right_right_left() {
    let p = &[LABEL, RIGHT, RIGHT, LEFT, INC, LOOP];
    let state = simulate(p, 2000);
    let proof = prove_infinite(p, &state);
    assert!(proof.is_some());
    dbg!(proof);
}

#[test]
fn test_loop_with_init() {
    let p = b"[[]+]";
    let proof = prove_from_start(p);
    assert!(proof.is_some());
    dbg!(String::from_utf8(p.to_vec()).unwrap());
    dbg!(proof.unwrap());
}

#[test]
fn test_nested_loop() {
    let p = b"+[[>]<]";
    let state = simulate(p, 2000);
    let proof = prove_infinite(p, &state);
    assert!(proof.is_some());
    dbg!(proof);
}

#[test]
fn test_composite_pred_apply() {
    let predicate = Predicate::All(vec![Predicate::ZerosFrom(1), Predicate::Equals(0, 1)]);
    let expected = Predicate::All(vec![Predicate::ZerosFrom(1), Predicate::Equals(0, 2)]);;
    let next = predicate.apply(INC);
    assert!(next.implies(&expected));
    assert!(expected.implies(&next));
}

#[test]
fn test_zeros_apply_inc() {
    let predicate = Predicate::ZerosFrom(0);
    let expected = Predicate::All(vec![Predicate::ZerosFrom(1), Predicate::Equals(0, 1)]);
    let next = predicate.apply(INC);
    dbg!(&next);
    assert!(next.implies(&expected));
    assert!(expected.implies(&next));
}

fn solve_for_program(program: &[u8], verbose: bool) -> State {
    let mut state = simulate(program, 1000);

    if state.status == Status::Running {
        // let maybe_proof = prove_infinite(&p, &state);
        if verbose {
            println!("{}", String::from_utf8(program.to_vec()).unwrap());
        }
        let maybe_proof = prove_from_start(program);
        if let Some(proof) = maybe_proof  {
            state.status = Status::Infinite;
            if verbose {
                println!("{:?}", &proof.invariants[0]);
                for i in 1..proof.invariants.len() {
                    println!("{} {:?}", program[i-1] as char, proof.invariants[i])
                }
                println!("{}", program[program.len() - 1] as char);
            }                }
    }

    state
}

fn solve_for_len(l: usize) {
    println!("\nLength {}", l);

    let mut total_programs = 0;
    let mut tape_overflow = 0;
    let mut value_overflow = 0;
    let mut finished = 0;
    let mut infinite = 0;
    let mut running = 0;
    let mut longest_run = 0;
    let mut longest_running_program = String::new();
    let mut longest_tape = 0;
    let mut longest_tape_program = String::new();

    for p in gen_valid_programs(l) {
        let state = solve_for_program(&p, false);

        total_programs += 1;
        match state.status {
            Status::Finished => {
                finished += 1;
                if state.step > longest_run {
                    longest_run = state.step;
                    longest_running_program = String::from_utf8(p.clone()).unwrap();
                }
                if state.tape.len() > longest_tape {
                    longest_tape = state.tape.len();
                    longest_tape_program = String::from_utf8(p.clone()).unwrap();
                }
            },
            Status::TapeOverflow => tape_overflow += 1,
            Status::ValueOverflow => value_overflow += 1,
            Status::Infinite => {
                infinite += 1;
            },
            Status::Running => {
                running += 1;
                println!("Running: {}", String::from_utf8(p.clone()).unwrap());
            }
        };
    }
    println!();
    println!("Total programs: {}", total_programs);
    println!("Finished: {}", finished);
    println!("Tape overflow: {}", tape_overflow);
    println!("Value overflow: {}", value_overflow);
    println!("Proven infinite: {}", infinite);
    println!("Running: {}", running);
    println!("Longest run: {} {}", longest_run, longest_running_program);
    println!("Longest tape: {} {}", longest_tape, longest_tape_program);
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        solve_for_program(b"[[]>+]-", true);
        return;
    }
    let arg: &str = &args[1];
    let len: usize = arg.parse().unwrap_or(0);
    if len == 0 {
        solve_for_program(arg.as_bytes(), true);
    } else {
        solve_for_len(len)
    }
}
