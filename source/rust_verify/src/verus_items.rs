use rustc_middle::ty::TyCtxt;
use rustc_span::{def_id::DefId};
use std::collections::HashMap;

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum SpecItem {
    Admit,
    Assume,
    NoMethodBody,
    Requires,
    Recommends,
    Ensures,
    Invariant,
    InvariantEnsures,
    Decreases,
    DecreasesWhen,
    DecreasesBy,
    RecommendsBy,
    OpensInvariantsNone,
    OpensInvariantsAny,
    OpensInvariants,
    OpensInvariantsExcept,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum QuantItem {
    Forall,
    ForallArith,
    Exists,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum DirectiveItem {
    ExtraDependency,
    Hide,
    Reveal,
    RevealFuel,
    RevealStrlit,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum ExprItem {
    Choose,
    ChooseTuple,
    Old,
    StrSliceLen,
    StrSliceGetChar,
    StrSliceIsAscii,
    ArchWordBits,
    ClosureToFnSpec,
    SignedMin,
    SignedMax,
    UnsignedMax,
    Height,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum CompilableOprItem {
    Implies,
    // SmartPtrNew,
    NewStrLit,
    GhostExec,
    GhostNew,
    TrackedNew,
    TrackedExec,
    TrackedExecBorrow,
    TrackedGet,
    TrackedBorrow,
    TrackedBorrowMut,
    // GhostSplitTuple,
    // TrackedSplitTuple,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum ArithItem {
    BuiltinAdd,
    BuiltinSub,
    BuiltinMul,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum EqualityItem {
    Equal,
    SpecEq,
    ExtEqual,
    ExtEqualDeep,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum SpecOrdItem {
    Le,
    Ge,
    Lt,
    Gt,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum SpecArithItem {
    Add,
    Sub,
    Mul,
    EuclideanDiv,
    EuclideanMod,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum SpecBitwiseItem {
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum BinaryOpItem {
    Arith(ArithItem),
    Equality(EqualityItem),
    SpecOrd(SpecOrdItem),
    SpecArith(SpecArithItem),
    SpecBitwise(SpecBitwiseItem),
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum ChainedItem {
    Value,
    Le,
    Lt,
    Ge,
    Gt,
    Cmp,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum AssertItem {
    Assert,
    AssertBy,
    AssertByCompute,
    AssertByComputeOnly,
    AssertNonlinearBy,
    AssertBitvectorBy,
    AssertForallBy,
    AssertBitVector,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum SpecLiteralItem {
    Integer,
    Int,
    Nat
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum SpecGhostTrackedItem {
    GhostView,
    GhostBorrow,
    GhostBorrowMut,
    TrackedView,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum UnaryOpItem {
    SpecLiteral(SpecLiteralItem),
    SpecNeg,
    SpecCastInteger,
    SpecGhostTracked(SpecGhostTrackedItem),
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum OpenInvariantBlockItem {
    OpenLocalInvariantBegin,
    OpenAtomicInvariantBegin,
    OpenInvariantEnd,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum PervasiveItem {
    StrSlice,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum MarkerItem {
    Structural,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum VerusItem {
    Spec(SpecItem),
    Quant(QuantItem),
    Directive(DirectiveItem),
    Expr(ExprItem),
    CompilableOpr(CompilableOprItem),
    BinaryOp(BinaryOpItem),
    UnaryOp(UnaryOpItem),
    Chained(ChainedItem),
    Assert(AssertItem),
    WithTriggers,
    OpenInvariantBlock(OpenInvariantBlockItem),
    Pervasive(PervasiveItem),
    Marker(MarkerItem),
}

#[rustfmt::skip]
const VERUS_ITEMS_MAP: &[(&str, VerusItem)] = &[
    ("verus::builtin::admit",                   VerusItem::Spec(SpecItem::Admit)),
    ("verus::builtin::assume_",                 VerusItem::Spec(SpecItem::Assume)),
    ("verus::builtin::no_method_body",          VerusItem::Spec(SpecItem::NoMethodBody)),
    ("verus::builtin::requires",                VerusItem::Spec(SpecItem::Requires)),
    ("verus::builtin::recommends",              VerusItem::Spec(SpecItem::Recommends)),
    ("verus::builtin::ensures",                 VerusItem::Spec(SpecItem::Ensures)),
    ("verus::builtin::invariant",               VerusItem::Spec(SpecItem::Invariant)),
    ("verus::builtin::invariant_ensures",       VerusItem::Spec(SpecItem::InvariantEnsures)),
    ("verus::builtin::decreases",               VerusItem::Spec(SpecItem::Decreases)),
    ("verus::builtin::decreases_when",          VerusItem::Spec(SpecItem::DecreasesWhen)),
    ("verus::builtin::decreases_by",            VerusItem::Spec(SpecItem::DecreasesBy)),
    ("verus::builtin::recommends_by",           VerusItem::Spec(SpecItem::RecommendsBy)),
    ("verus::builtin::opens_invariants_none",   VerusItem::Spec(SpecItem::OpensInvariantsNone)),
    ("verus::builtin::opens_invariants_any",    VerusItem::Spec(SpecItem::OpensInvariantsAny)),
    ("verus::builtin::opens_invariants",        VerusItem::Spec(SpecItem::OpensInvariants)),
    ("verus::builtin::opens_invariants_except", VerusItem::Spec(SpecItem::OpensInvariantsExcept)),

    ("verus::builtin::forall",                  VerusItem::Quant(QuantItem::Forall)),
    ("verus::builtin::exists",                  VerusItem::Quant(QuantItem::Exists)),
    ("verus::builtin::forall_arith",            VerusItem::Quant(QuantItem::ForallArith)),

    ("verus::builtin::extra_dependency",        VerusItem::Directive(DirectiveItem::ExtraDependency)),
    ("verus::builtin::hide",                    VerusItem::Directive(DirectiveItem::Hide)),
    ("verus::builtin::reveal",                  VerusItem::Directive(DirectiveItem::Reveal)),
    ("verus::builtin::reveal_with_fuel",        VerusItem::Directive(DirectiveItem::RevealFuel)),
    ("verus::builtin::reveal_strlit",           VerusItem::Directive(DirectiveItem::RevealStrlit)),

    ("verus::builtin::choose",                  VerusItem::Expr(ExprItem::Choose)),
    ("verus::builtin::choose_tuple",            VerusItem::Expr(ExprItem::ChooseTuple)),
    ("verus::builtin::old",                     VerusItem::Expr(ExprItem::Old)),
    ("verus::builtin::strslice_len",            VerusItem::Expr(ExprItem::StrSliceLen)),
    ("verus::builtin::strslice_get_char",       VerusItem::Expr(ExprItem::StrSliceGetChar)),
    ("verus::builtin::strslice_is_ascii",       VerusItem::Expr(ExprItem::StrSliceIsAscii)),
    ("verus::builtin::arch_word_bits",          VerusItem::Expr(ExprItem::ArchWordBits)),
    ("verus::builtin::closure_to_fn_spec",      VerusItem::Expr(ExprItem::ClosureToFnSpec)),
    ("verus::builtin::signed_min",              VerusItem::Expr(ExprItem::SignedMin)),
    ("verus::builtin::signed_max",              VerusItem::Expr(ExprItem::SignedMax)),
    ("verus::builtin::unsigned_max",            VerusItem::Expr(ExprItem::UnsignedMax)),
    ("verus::builtin::height",                  VerusItem::Expr(ExprItem::Height)),

    ("verus::builtin::imply",                   VerusItem::CompilableOpr(CompilableOprItem::Implies)),
    // TODO ("verus::builtin::smartptr_new",    VerusItem::CompilableOpr(CompilableOprItem::SmartPtrNew)),
    // TODO: replace with builtin:
    ("verus::pervasive::string::new_strlit",    VerusItem::CompilableOpr(CompilableOprItem::NewStrLit)),
    ("verus::builtin::ghost_exec",              VerusItem::CompilableOpr(CompilableOprItem::GhostExec)),
    ("verus::builtin::Ghost::new",              VerusItem::CompilableOpr(CompilableOprItem::GhostNew)),
    ("verus::builtin::Tracked::new",            VerusItem::CompilableOpr(CompilableOprItem::TrackedNew)),
    ("verus::builtin::tracked_exec",            VerusItem::CompilableOpr(CompilableOprItem::TrackedExec)),
    ("verus::builtin::tracked_exec_borrow",     VerusItem::CompilableOpr(CompilableOprItem::TrackedExecBorrow)),
    ("verus::builtin::Tracked::get",            VerusItem::CompilableOpr(CompilableOprItem::TrackedGet)),
    ("verus::builtin::Tracked::borrow",         VerusItem::CompilableOpr(CompilableOprItem::TrackedBorrow)),
    ("verus::builtin::Tracked::borrow_mut",     VerusItem::CompilableOpr(CompilableOprItem::TrackedBorrowMut)),

    ("verus::builtin::add",                     VerusItem::BinaryOp(BinaryOpItem::Arith(ArithItem::BuiltinAdd))),
    ("verus::builtin::sub",                     VerusItem::BinaryOp(BinaryOpItem::Arith(ArithItem::BuiltinSub))),
    ("verus::builtin::mul",                     VerusItem::BinaryOp(BinaryOpItem::Arith(ArithItem::BuiltinMul))),

    ("verus::builtin::equal",                   VerusItem::BinaryOp(BinaryOpItem::Equality(EqualityItem::Equal))),
    ("verus::builtin::spec_eq",                 VerusItem::BinaryOp(BinaryOpItem::Equality(EqualityItem::SpecEq))),
    ("verus::builtin::ext_equal",               VerusItem::BinaryOp(BinaryOpItem::Equality(EqualityItem::ExtEqual))),
    ("verus::builtin::ext_equal_deep",          VerusItem::BinaryOp(BinaryOpItem::Equality(EqualityItem::ExtEqualDeep))),

    ("verus::builtin::SpecOrd::spec_le",        VerusItem::BinaryOp(BinaryOpItem::SpecOrd(SpecOrdItem::Le))),
    ("verus::builtin::SpecOrd::spec_ge",        VerusItem::BinaryOp(BinaryOpItem::SpecOrd(SpecOrdItem::Ge))),
    ("verus::builtin::SpecOrd::spec_lt",        VerusItem::BinaryOp(BinaryOpItem::SpecOrd(SpecOrdItem::Lt))),
    ("verus::builtin::SpecOrd::spec_gt",        VerusItem::BinaryOp(BinaryOpItem::SpecOrd(SpecOrdItem::Gt))),
    
    ("verus::builtin::SpecAdd::spec_add",        VerusItem::BinaryOp(BinaryOpItem::SpecArith(SpecArithItem::Add))),
    ("verus::builtin::SpecSub::spec_sub",        VerusItem::BinaryOp(BinaryOpItem::SpecArith(SpecArithItem::Sub))),
    ("verus::builtin::SpecMul::spec_mul",        VerusItem::BinaryOp(BinaryOpItem::SpecArith(SpecArithItem::Mul))),
    ("verus::builtin::SpecEuclideanDiv::spec_euclidean_div", VerusItem::BinaryOp(BinaryOpItem::SpecArith(SpecArithItem::EuclideanDiv))),
    ("verus::builtin::SpecEuclideanMod::spec_euclidean_mod", VerusItem::BinaryOp(BinaryOpItem::SpecArith(SpecArithItem::EuclideanMod))),

    ("verus::builtin::SpecBitAnd::spec_bitand",  VerusItem::BinaryOp(BinaryOpItem::SpecBitwise(SpecBitwiseItem::BitAnd))),
    ("verus::builtin::SpecBitOr::spec_bitor",    VerusItem::BinaryOp(BinaryOpItem::SpecBitwise(SpecBitwiseItem::BitOr))),
    ("verus::builtin::SpecBitXor::spec_bitxor",  VerusItem::BinaryOp(BinaryOpItem::SpecBitwise(SpecBitwiseItem::BitXor))),
    ("verus::builtin::SpecShl::spec_shl",        VerusItem::BinaryOp(BinaryOpItem::SpecBitwise(SpecBitwiseItem::Shl))),
    ("verus::builtin::SpecShr::spec_shr",        VerusItem::BinaryOp(BinaryOpItem::SpecBitwise(SpecBitwiseItem::Shr))),

    ("verus::builtin::spec_chained_value",       VerusItem::Chained(ChainedItem::Value)),
    ("verus::builtin::spec_chained_le",          VerusItem::Chained(ChainedItem::Le)),
    ("verus::builtin::spec_chained_lt",          VerusItem::Chained(ChainedItem::Lt)),
    ("verus::builtin::spec_chained_ge",          VerusItem::Chained(ChainedItem::Ge)),
    ("verus::builtin::spec_chained_gt",          VerusItem::Chained(ChainedItem::Gt)),
    ("verus::builtin::spec_chained_cmp",         VerusItem::Chained(ChainedItem::Cmp)),

    ("verus::builtin::assert_",                  VerusItem::Assert(AssertItem::Assert)),
    ("verus::builtin::assert_by",                VerusItem::Assert(AssertItem::AssertBy)),
    ("verus::builtin::assert_by_compute",        VerusItem::Assert(AssertItem::AssertByCompute)),
    ("verus::builtin::assert_by_compute_only",   VerusItem::Assert(AssertItem::AssertByComputeOnly)),
    ("verus::builtin::assert_nonlinear_by",      VerusItem::Assert(AssertItem::AssertNonlinearBy)),
    ("verus::builtin::assert_bitvector_by",      VerusItem::Assert(AssertItem::AssertBitvectorBy)),
    ("verus::builtin::assert_forall_by",         VerusItem::Assert(AssertItem::AssertForallBy)),
    ("verus::builtin::assert_bit_vector",        VerusItem::Assert(AssertItem::AssertBitVector)),

    ("verus::builtin::with_triggers",            VerusItem::WithTriggers),
    
    ("verus::builtin::spec_literal_integer",     VerusItem::UnaryOp(UnaryOpItem::SpecLiteral(SpecLiteralItem::Integer))),
    ("verus::builtin::spec_literal_int",         VerusItem::UnaryOp(UnaryOpItem::SpecLiteral(SpecLiteralItem::Int))),
    ("verus::builtin::spec_literal_nat",         VerusItem::UnaryOp(UnaryOpItem::SpecLiteral(SpecLiteralItem::Nat))),
    ("verus::builtin::SpecNeg::spec_neg",        VerusItem::UnaryOp(UnaryOpItem::SpecNeg)),
    ("verus::builtin::spec_cast_integer",        VerusItem::UnaryOp(UnaryOpItem::SpecCastInteger)),
    ("verus::builtin::Ghost::view",              VerusItem::UnaryOp(UnaryOpItem::SpecGhostTracked(SpecGhostTrackedItem::GhostView))),
    ("verus::builtin::Ghost::borrow",            VerusItem::UnaryOp(UnaryOpItem::SpecGhostTracked(SpecGhostTrackedItem::GhostBorrow))),
    ("verus::builtin::Ghost::borrow_mut",        VerusItem::UnaryOp(UnaryOpItem::SpecGhostTracked(SpecGhostTrackedItem::GhostBorrowMut))),
    ("verus::builtin::Tracked::view",            VerusItem::UnaryOp(UnaryOpItem::SpecGhostTracked(SpecGhostTrackedItem::TrackedView))),

    ("verus::pervasive::invariant::open_atomic_invariant_begin", VerusItem::OpenInvariantBlock(OpenInvariantBlockItem::OpenAtomicInvariantBegin)),
    ("verus::pervasive::invariant::open_local_invariant_begin",  VerusItem::OpenInvariantBlock(OpenInvariantBlockItem::OpenLocalInvariantBegin)),
    ("verus::pervasive::invariant::open_invariant_end",          VerusItem::OpenInvariantBlock(OpenInvariantBlockItem::OpenInvariantEnd)),

    ("verus::pervasive::string::StrSlice",       VerusItem::Pervasive(PervasiveItem::StrSlice)),

    ("verus::builtin::Structural",               VerusItem::Marker(MarkerItem::Structural)),
];

pub(crate) struct VerusItems {
    pub(crate) id_to_name: HashMap<DefId, VerusItem>,
    pub(crate) name_to_id: HashMap<VerusItem, DefId>,
}

pub(crate) fn from_diagnostic_items(diagnostic_items: &rustc_hir::diagnostic_items::DiagnosticItems) -> VerusItems {
    let verus_item_map: HashMap<&str, VerusItem> = VERUS_ITEMS_MAP.iter().map(|(k, v)| (*k, v.clone())).collect();
    let diagnostic_name_to_id = &diagnostic_items.name_to_id;
    let mut id_to_name: HashMap<DefId, VerusItem> = HashMap::new();
    let mut name_to_id: HashMap<VerusItem, DefId> = HashMap::new();
    for (name, id) in diagnostic_name_to_id {
        let name = name.as_str();
        if name.starts_with("verus::builtin") || name.starts_with("verus::pervasive") {
            if let Some(item) = verus_item_map.get(name) {
                id_to_name.insert(id.clone(), item.clone());
                name_to_id.insert(item.clone(), id.clone());
            } else {
                // TODO panic when all the cases are covered
                // dbg!(name);
            }
        }
    }
    VerusItems { id_to_name, name_to_id }
}


#[derive(PartialEq, Eq, Debug, Clone, Copy)]
pub(crate) enum RustItem {
    Panic,
}

pub(crate) fn get_rust_item<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Option<RustItem> {
    // if tcx.parent(def_id) == partial_eq {
    if tcx.lang_items().panic_fn() == Some(def_id) {
        Some(RustItem::Panic)
    } else {
        None
    }
}
