use crate::brainfuck::{Instruction, Program, State};

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
