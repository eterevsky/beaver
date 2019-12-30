use crate::brainfuck::Program;
use std::fmt;

#[derive(Clone, Debug, PartialEq)]
pub enum Term {
    Const(isize),
    // The index of a varible. Within a proposition variables are treated as if in a ∀ quantifier.
    Var(usize),
    Pos,
    Sum(Vec<Term>),
    Tape(Box<Term>),
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Const(x) => write!(f, "{}", x),
            Term::Var(0) => write!(f, "x"),
            Term::Var(1) => write!(f, "y"),
            Term::Var(2) => write!(f, "z"),
            Term::Var(x) => write!(f, "t{}", x-3),
            Term::Pos => write!(f, "p"),
            Term::Sum(clauses) => {
                write!(f, "{}", clauses[0])?;
                for c in clauses.iter().skip(1) {
                    if let Term::Const(x) = c {
                        if *x >= 0 {
                            write!(f, " + {}", x)?;
                        } else {
                            write!(f, " - {}", -x)?;
                        }
                    } else {
                        write!(f, " + {}", c)?;
                    }
                }
                write!(f, "")
            },
            Term::Tape(x) => write!(f, "tape[{}]", x)
        }
    }
}
impl Term {
    pub fn tape(index: Term) -> Self {
        Term::Tape(Box::new(index))
    }

    pub fn sum2(a: Term, b: Term) -> Self {
        Term::Sum(vec![a, b])
    }

    fn renumber_vars(self, used_vars: &mut Vec<usize>, new_indices: &mut Vec<(usize, usize)>) -> Self {
        match self {
            Term::Var(x) => {
                let mut new_idx = None;
                for (i, j) in new_indices.iter() {
                    if *i == x {
                        new_idx = Some(*j)
                    }
                }
                if let Some(i) = new_idx {
                    Term::Var(i)
                } else {
                    let mut new_idx = 0;
                    while used_vars.contains(&new_idx) {
                        new_idx += 1;
                    }
                    used_vars.push(new_idx);
                    new_indices.push((x, new_idx));
                    Term::Var(new_idx)
                }
            },
            Term::Sum(mut args) => {
                Term::Sum(args.drain(..).map(|arg| arg.renumber_vars(used_vars, new_indices)).collect())
            },
            Term::Tape(arg) => {
                Term::Tape(Box::new(arg.renumber_vars(used_vars, new_indices)))
            },
            _ => self,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Proposition {
    True,
    False,
    Equals(Term, Term),
    Greater(Term, Term),
    And(Vec<Proposition>),
    Or(Vec<Proposition>),
}

impl Proposition {
    pub fn or2(left: Self, right: Self) -> Self {
        Proposition::Or(vec![left, right])
    }

    fn renumber_vars(self, used_vars: &mut Vec<usize>, new_indices: &mut Vec<(usize, usize)>) -> Self {
        match self {
            Proposition::Equals(x, y) => 
                Proposition::Equals(x.renumber_vars(used_vars, new_indices),
                                    y.renumber_vars(used_vars, new_indices)),
            Proposition::Greater(x, y) => 
                Proposition::Greater(x.renumber_vars(used_vars, new_indices),
                                    y.renumber_vars(used_vars, new_indices)),
            Proposition::And(mut clauses) =>
                Proposition::And(clauses.drain(..).map(|c| c.renumber_vars(used_vars, new_indices)).collect()),
            Proposition::Or(mut clauses) =>
                Proposition::Or(clauses.drain(..).map(|c| c.renumber_vars(used_vars, new_indices)).collect()),
            _ => self,
        }
    }

    fn renumber_ind_vars(mut clauses: Vec<Self>) -> Vec<Self> {
        let mut used_vars = Vec::new();
        clauses.drain(..).map(|c| c.renumber_vars(&mut used_vars, &mut Vec::new())).collect()
    }

    pub fn or_ind(clauses: Vec<Self>) -> Self {
        Proposition::Or(Self::renumber_ind_vars(clauses))
    }

    pub fn and_ind(clauses: Vec<Self>) -> Self {
        Proposition::And(Self::renumber_ind_vars(clauses))
    }
}

impl fmt::Display for Proposition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Proposition::True => write!(f, "true"),
            Proposition::False => write!(f, "true"),
            Proposition::Equals(x, y) => {
                if let Term::Const(_) = x {
                    write!(f, "{} = {}", y, x)
                } else {
                    write!(f, "{} = {}", x, y)
                }
            },
            Proposition::Greater(x, y) => {
                if let Term::Const(_) = x {
                    write!(f, "{} < {}", y, x)
                } else {
                    write!(f, "{} > {}", x, y)
                }

            },
            Proposition::And(clauses) => {
                write!(f, "{}", clauses[0])?;
                for c in clauses.iter().skip(1) {
                    write!(f, " & {}", c)?;
                }
                write!(f, "")
            },
            Proposition::Or(clauses) => {
                write!(f, "({}", clauses[0])?;
                for c in clauses.iter().skip(1){
                    write!(f, " | {}", c)?;
                }
                write!(f, ")")
            },
        }
    }
}

#[derive(Clone, Debug)]
pub struct Proof {
    pub program: Program,
    pub invariants: Vec<Proposition>,
}

impl fmt::Display for Proof {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "    {}", &self.invariants[0])?;
        for i in 1..self.invariants.len() {
            writeln!(f, "{}   {}", self.program[i - 1], self.invariants[i])?;
        }
        writeln!(f, "{}", self.program[self.program.len() - 1])
    }
}

#[test]
fn test_or_ind() {
    let a = Proposition::Equals(Term::Var(0), Term::Const(0));
    let b = Proposition::Equals(Term::Var(0), Term::Const(1));
    let or = Proposition::or_ind(vec![a, b]);
    assert_eq!(or,
        Proposition::Or(vec![
            Proposition::Equals(Term::Var(0), Term::Const(0)),
            Proposition::Equals(Term::Var(1), Term::Const(1)),
        ]))
}
