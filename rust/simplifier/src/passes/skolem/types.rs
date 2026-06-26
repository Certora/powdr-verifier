#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SortKind {
    Int,
    Bool,
    Array,
    Other,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SkolemPin {
    pub equation: smt2::Term,
    pub kind: String,
}
