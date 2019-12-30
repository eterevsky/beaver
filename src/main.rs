mod brainfuck;
mod local_statement;
mod statement;

#[cfg(test)]
use crate::brainfuck::gen_valid_programs;
use crate::brainfuck::{run, Instruction, Program, State, Status};
use crate::local_statement::{LocalProof, LocalProver, verify_proof};
use crate::statement::Proof;
use std::env;
use std::sync::mpsc::{channel, Receiver, Sender};
use std::sync::{Arc, Mutex};
use std::thread::spawn;

fn solve_program(program: &Program) -> (State, Option<Proof>) {
    let mut state = run(program, 200);
    if state.status != Status::Running {
        return (state, None);
    }

    let maybe_proof = LocalProver::new(1, 32).prove_runs_forever(program).map(|p| p.as_proof());
    if maybe_proof.is_some() {
        state.status = Status::RunsForever;
        return (state, maybe_proof);
    }

    state.run(2000);
    if state.status != Status::Running {
        return (state, None);
    }

    let maybe_proof = LocalProver::new(2, 64).prove_runs_forever(program).map(|p| p.as_proof());
    if maybe_proof.is_some() {
        state.status = Status::RunsForever;
        return (state, maybe_proof);
    }

    state.run(20000);
    if state.status != Status::Running {
        return (state, None);
    }

    let maybe_proof = LocalProver::new(3, 128).prove_runs_forever(program).map(|p| p.as_proof());
    if maybe_proof.is_some() {
        state.status = Status::RunsForever;
        return (state, maybe_proof);
    }

    state.run(200000);
    if state.status != Status::Running {
        return (state, None);
    }

    let maybe_proof = LocalProver::new(4, 256).prove_runs_forever(program).map(|p| p.as_proof());
    if maybe_proof.is_some() {
        state.status = Status::RunsForever;
        return (state, maybe_proof);
    }

    state.run(2000000);
    if state.status != Status::Running {
        return (state, None);
    }

    let maybe_proof = LocalProver::new(5, 512).prove_runs_forever(program).map(|p| p.as_proof());
    if maybe_proof.is_some() {
        state.status = Status::RunsForever;
        return (state, maybe_proof);
    }

    (state, maybe_proof)
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
                assert!(proof.is_some());
                // assert!(verify_proof(&proof.unwrap()))
            }

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

#[derive(Clone, Debug)]
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
    fn new() -> Self {
        Stats {
            total: 0,
            finished: 0,
            run_forever: 0,
            overflow: 0,
            unknown: 0,
            longest_run: 0,
            longest_running_program: None,
            longest_tape: 0,
            longest_tape_program: None,
        }
    }

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
        }
        Status::TapeOverflow | Status::ValueOverflow => overflow = 1,
        Status::RunsForever => run_forever = 1,
        Status::Running => {
            unknown = 1;
            println!("    {}", program);
        }
    };

    Stats {
        total: 1,
        finished,
        run_forever,
        overflow,
        unknown,
        longest_run,
        longest_running_program,
        longest_tape,
        longest_tape_program,
    }
}

// Generated by possible_programs.rs
const NPROGRAMS: &[u64] = &[
    1,
    4,
    17,
    76,
    354,
    1704,
    8421,
    42508,
    218318,
    1137400,
    5996938,
    31940792,
    171605956,
    928931280,
    5061593709,
    27739833228,
    152809506582,
    845646470616,
    4699126915422,
    26209721959656,
];

fn solve_prefix(len: usize, prefix: &Program) -> Option<Stats> {
    let opened_loops = prefix.nesting_at(prefix.len());

    if prefix.len() + opened_loops == len {
        let mut program = prefix.clone();
        // Just one possible program
        for _ in 0..opened_loops {
            program.push(Instruction::Backward(0));
        }
        return Some(program_stats(&program));
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
                }
                Status::Finished => unreachable!(),
            };

            Some(Stats {
                total: nprograms,
                finished: 0,
                run_forever,
                overflow,
                unknown,
                longest_run: 0,
                longest_running_program: None,
                longest_tape: 0,
                longest_tape_program: None,
            })
        } else {
            None
        }
    } else {
        None
    }
}

const INSTRUCTIONS_NONE: &[Instruction] = &[
    Instruction::Inc,
    Instruction::Dec,
    Instruction::Left,
    Instruction::Right,
];
const INSTRUCTIONS_FWD: &[Instruction] = &[
    Instruction::Inc,
    Instruction::Dec,
    Instruction::Left,
    Instruction::Right,
    Instruction::Forward(0),
];
const INSTRUCTIONS_BACK: &[Instruction] = &[
    Instruction::Inc,
    Instruction::Dec,
    Instruction::Left,
    Instruction::Right,
    Instruction::Backward(0),
];
const INSTRUCTIONS_BOTH: &[Instruction] = &[
    Instruction::Inc,
    Instruction::Dec,
    Instruction::Left,
    Instruction::Right,
    Instruction::Forward(0),
    Instruction::Backward(0),
];

fn possible_instructions(len: usize, prefix: &Program) -> &'static [Instruction] {
    let opened_loops = prefix.nesting_at(prefix.len());
    if len - prefix.len() >= opened_loops + 2 && prefix.len() > 0 {
        if opened_loops > 0 {
            INSTRUCTIONS_BOTH
        } else {
            INSTRUCTIONS_FWD
        }
    } else {
        if opened_loops > 0 {
            INSTRUCTIONS_BACK
        } else {
            INSTRUCTIONS_NONE
        }
    }
}

fn gen_and_solve(len: usize, prefix: &Program) -> Stats {
    if let Some(stats) = solve_prefix(len, prefix) {
        return stats;
    }

    let mut stats = Stats::new();
    let mut program = prefix.clone();

    for instruction in possible_instructions(len, prefix).iter() {
        program.push(*instruction);
        stats.merge(gen_and_solve(len, &program));
        program.pop();
    }

    stats
}

// TODO: Adapt this test to gen_and_solve skipping programs startin with [.
// #[test]
// fn test7_gen() {
//     let stats = gen_and_solve(7, &"".parse().unwrap());
//     assert_eq!(stats.total, 42508);
//     assert_eq!(stats.finished, 8740);
//     assert_eq!(stats.run_forever + stats.overflow, 1208 + 32560);
//     assert_eq!(stats.unknown, 0);
//     assert_eq!(stats.longest_run, 13);
//     assert_eq!(stats.longest_tape, 8);
// }

#[derive(Clone)]
enum Job {
    Stop,
    Solve((usize, Program)),
}

#[derive(Clone)]
struct JobResult {
    prefix: Program,
    stats: Stats,
}

const JOB_LEN: usize = 11;
const NTHREADS: usize = 72;

fn gen_and_queue(
    len: usize,
    prefix: &Program,
    jobs_sender: &Sender<Job>,
    results_sender: &Sender<JobResult>,
) -> usize {
    if let Some(stats) = solve_prefix(len, prefix) {
        results_sender
            .send(JobResult {
                prefix: prefix.clone(),
                stats,
            })
            .unwrap();
        return 1;
    }

    if len - prefix.len() == JOB_LEN {
        jobs_sender.send(Job::Solve((len, prefix.clone()))).unwrap();
        return 1;
    }

    let mut program = prefix.clone();
    let mut nresults = 0;

    for instruction in possible_instructions(len, prefix).iter() {
        program.push(*instruction);
        nresults += gen_and_queue(len, &program, jobs_sender, results_sender);
        program.pop();
    }

    nresults
}

fn worker(jobs_receiver: Arc<Mutex<Receiver<Job>>>, results_sender: Sender<JobResult>) {
    loop {
        let job = jobs_receiver.lock().unwrap().recv().unwrap();
        match job {
            Job::Stop => break,
            Job::Solve((len, prefix)) => {
                let stats = gen_and_solve(len, &prefix);
                results_sender.send(JobResult { prefix, stats }).unwrap();
            }
        }
    }
}

fn solve_parallel(len: usize) -> Stats {
    let mut threads = Vec::new();
    let (jobs_sender, jobs_receiver) = channel();
    let jobs_receiver = Arc::new(Mutex::new(jobs_receiver));
    let (results_sender, results_receiver) = channel();
    for _ in 0..NTHREADS {
        let jobs_receiver_clone = jobs_receiver.clone();
        let results_sender_clone = results_sender.clone();
        threads.push(spawn(move || {
            worker(jobs_receiver_clone, results_sender_clone);
        }))
    }

    let nresults = gen_and_queue(len, &"".parse().unwrap(), &jobs_sender, &results_sender);
    for _ in 0..NTHREADS {
        jobs_sender.send(Job::Stop).unwrap();
    }

    let mut stats = Stats::new();
    for _ in 0..nresults {
        let res = results_receiver.recv().unwrap();
        println!(
            "{}  {} / {} / {}",
            res.prefix,
            res.stats.finished,
            res.stats.run_forever + res.stats.overflow,
            res.stats.unknown
        );
        stats.merge(res.stats)
    }

    stats
}

fn solve_len_with_memo(len: usize, previous: &Vec<Stats>) -> Stats {
    // Programs that don't start with [
    let mut stats = if len <= JOB_LEN {
        gen_and_solve(len, &"".parse().unwrap())
    } else {
        println!("\nLength {}\n", len);
        solve_parallel(len)
    };

    // Programs that start with [
    for sublen in 0..len - 1 {
        let nprefixes = NPROGRAMS[sublen];
        let mut suffix_stats = previous[len - sublen - 2].clone();
        suffix_stats.finished *= nprefixes;
        suffix_stats.overflow *= nprefixes;
        suffix_stats.run_forever *= nprefixes;
        suffix_stats.total *= nprefixes;
        suffix_stats.unknown *= nprefixes;
        stats.merge(suffix_stats);
    }

    stats
}

fn solve_len(len: usize) {
    println!("Total programs: {}\n", NPROGRAMS[len]);

    let mut zero_stats = Stats::new();
    zero_stats.total = 1;
    zero_stats.finished = 1;
    let mut stats_per_len = vec![zero_stats];

    for shorter_len in 1..(len - 1) {
        let shorter_stats = solve_len_with_memo(shorter_len, &stats_per_len);
        stats_per_len.push(shorter_stats);
    }

    let stats = solve_len_with_memo(len, &stats_per_len);

    println!("\nTotal: {}", stats.total);
    println!("Finished: {}", stats.finished);
    println!("Run forever: {}", stats.run_forever);
    println!("Overflow: {}", stats.overflow);
    println!("Unknown: {}", stats.unknown);
    println!(
        "Longest run: {} {}",
        stats.longest_running_program.unwrap(),
        stats.longest_run
    );
    println!(
        "Longest tape: {} {}",
        stats.longest_tape_program.unwrap(),
        stats.longest_tape
    );
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let arg: &str = &args[1];
    let len: usize = arg.parse().unwrap_or(0);
    if len == 0 {
        let program = arg.parse().unwrap();
        let (state, proof) = solve_program(&program);
        println!("{}", state);
        if let Some(p) = proof {
            // assert!(verify_proof(&p));
            println!("{}", p);
        }
    } else {
        solve_len(len)
    }
}
