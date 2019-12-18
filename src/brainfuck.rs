use std::fmt;
use std::ops::Index;
use std::str::FromStr;

/// Represents a Brainfuck instruction.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Instruction {
    Inc,
    Dec,
    Left,
    Right,
    Label,
    /// The value is the address of the label to which we jump.
    Loop(u16),
}

impl Instruction {
    pub fn is_loop(self) -> bool {
        match self {
            Instruction::Loop(_) => true,
            _ => false,
        }
    }
}

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let c = match *self {
            Instruction::Inc => '+',
            Instruction::Dec => '-',
            Instruction::Left => '<',
            Instruction::Right => '>',
            Instruction::Label => '[',
            Instruction::Loop(_) => ']',
        };
        write!(f, "{}", c)
    }
}

#[derive(Clone, Debug)]
pub struct Program {
    instructions: Vec<Instruction>,
}

impl Program {
    pub fn len(&self) -> usize { self.instructions.len() }

    pub fn push(&mut self, instruction: Instruction) {
        self.instructions.push(instruction)
    }

    pub fn pop(&mut self) {
        self.instructions.pop();
    }
}

impl Index<usize> for Program {
    type Output = Instruction;

    fn index(&self, i: usize) -> &Self::Output {
        &self.instructions[i]
    }
}

impl FromStr for Program {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut program = Program { instructions: Vec::new() };
        for c in s.chars() {
            let instruction = match c {
                '+' => Instruction::Inc,
                '-' => Instruction::Dec,
                '>' => Instruction::Right,
                '<' => Instruction::Left,
                '[' => Instruction::Label,
                ']' => {
                    let mut ip = program.len();
                    let mut nesting = 1;
                    while nesting > 0 {
                        if ip == 0 { return Err(()); }
                        ip -= 1;
                        nesting += match program[ip] {
                            Instruction::Loop(_) => 1,
                            Instruction::Label => -1,
                            _ => 0,
                        };
                    }
                    Instruction::Loop(ip as u16)
                },
                _ => return Err(())
            };
            program.instructions.push(instruction);
        }
        Ok(program)
    }
}

impl fmt::Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for instruction in self.instructions.iter() {
            write!(f, "{}", instruction)?
        }
        Ok(())
    }
}

#[cfg(test)]
static INSTRUCTIONS: &'static [u8] = &[b'+', b'-', b'<', b'>', b'[', b']'];

#[cfg(test)]
pub fn gen_valid_programs(len: usize) -> Vec<Program> {
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
                b'[' => 1,
                b']' => -1,
                _ => 0,
            };
            if nesting < 0 {
                well_formed = false;
                break;
            }
        }
        if well_formed && nesting == 0 {
            programs.push(String::from_utf8(p).unwrap().parse().unwrap());
        }
    }
    
    programs
}

#[test]
fn test_gen_programs_len1() {
    let programs = gen_valid_programs(1);
    assert_eq!(programs.len(), 4);
}

#[test]
fn test_gen_programs_len2() {
    let programs = gen_valid_programs(2);
    assert_eq!(programs.len(), 17);
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Status {
    Running,
    TapeOverflow,
    ValueOverflow,
    Finished,
    RunsForever,
}

#[derive(Clone, Debug)]
pub struct State {
    pub program: Program,
    pub tape: Vec<u8>,
    pub ip: usize,
    pub pos: usize,
    pub step: usize,
    pub status: Status,
}

impl State {
    pub fn new(program: Program) -> Self {
        State { program, tape: vec![0], ip: 0, pos: 0, step: 0, status: Status::Running }
    }

    #[cfg(test)]
    pub fn val_at_offset(&self, offset: isize) -> Option<u8> {
        let address = self.pos as isize + offset;
        if address < 0 {
            return None;
        }
        let address = address as usize;
        if address >= self.tape.len() {
            Some(0)
        } else {
            Some(self.tape[address])
        }
    }

    pub fn step(&mut self) {
        if self.status != Status::Running {
            return;
        }
        self.step += 1;
        match self.program[self.ip] {
            Instruction::Inc => {
                if self.tape[self.pos] == 255 {
                    self.status = Status::ValueOverflow;
                } else {
                    self.tape[self.pos] += 1;
                    self.ip += 1;
                }
            },
            Instruction::Dec => {
                if self.tape[self.pos] == 0 {
                    self.status = Status::ValueOverflow;
                } else {
                    self.tape[self.pos] -= 1;
                    self.ip += 1;
                }
            },
            Instruction::Right => {
                self.pos += 1;
                if self.pos >= self.tape.len() {
                    self.tape.push(0);
                }
                self.ip += 1;
            },
            Instruction::Left => {
                if self.pos == 0 {
                    self.status = Status::TapeOverflow;
                } else {
                    self.pos -= 1;
                    self.ip += 1;
                }
            },
            Instruction::Label => {
                self.ip += 1;
            },
            Instruction::Loop(new_ip) => {
                if self.tape[self.pos] == 0 {
                    self.ip += 1;
                } else {
                    self.ip = new_ip as usize + 1;
                }
            }
        };
        if self.ip >= self.program.len() {
            self.status = Status::Finished;
        }
    }
    
    fn run(&mut self, steps: usize) {
        for _ in 0..steps {
            self.step();
            if self.status != Status::Running { break; }
        }
    }    
}

impl fmt::Display for State {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{}", self.program)?;
        for _ in 0..self.ip {
            write!(f, " ")?;
        }
        writeln!(f, "^")?;
        for i in 0..self.tape.len() {
            if i == self.pos {
                write!(f, "[{}] ", self.tape[i])?;
            } else {
                write!(f, "{} ", self.tape[i])?;
            }
        }
        writeln!(f, "...")?;
        writeln!(f, "{:?} IP = {} pos = {} step = {}", self.status, self.ip, self.pos, self.step)
    }
}

pub fn run(program: &Program, steps: usize) -> State {
    let mut state = State::new(program.clone());
    state.run(steps);
    state
}
