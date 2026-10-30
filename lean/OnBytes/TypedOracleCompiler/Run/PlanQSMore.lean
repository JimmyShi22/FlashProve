-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/PlanQSMore.lean: WHAT THE PARSER ASKS OF THE GENERIC PROTOCOL WITH A LIST OF TREES A
ROUND (the typing), and a symbol's spelling. After the library's Run/PlanQS.lean:320-383 (leafSL,
plainsSL, placeSL, symSL, TYS, embPS): what the entry's clause holds of that file and
Run/PlanQS.lean | PlanQSpell.lean of the sibling do not say.
  AS TEXT            plainsSL, TYS
  TURNED BY MATTER   leafSL, placeSL, symSL (each goes to the position's own tree: leafT, noT, symT:
                     NEW)
  TURNED BY A PARAMETER MORE (Bd)   embPS
  NOT SAID           Lo3, Lb: the library's serve (Run/PlanQSpell.lean: LbS sets a body beside the
                     library's Lb)

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.PlanQSpell
import OnBytes.TypedOracleCompiler.Run.ParseThin

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open _root_.Run.Twin (RS PS)

/-- TWO: a leaf's spelling, in its own tree: what stands above the leaves' number in the label's
first word; the index; the column's bytes with the fill -/
def leafT (salt : Nat) : (ts : List _root_.Fmt.Shape) → (p : PosT ts) → SymT ts p →
    Nat × Nat × ByteArray
  | s :: _, .inl x, col =>
    (_root_.Fmt.leafPlace s.tree s.W (salt / 8),
      2 ^ s.a + x.val,
      _root_.Fmt.colBytes (List.ofFn col) ++ _root_.Fmt.zeroBytes (_root_.Fmt.fillLen s.W salt))
  | _ :: ts, .inr p, col => leafT salt ts p col

def leafSL (C : CK) (salt : Nat) : (ds : List RD) → SymAny (uL C ds) → Nat × Nat × ByteArray
  | [], ⟨p, _⟩ => p.elim
  | d :: _, ⟨.inl x, col⟩ => leafT salt d.trees x col
  | _ :: ds, ⟨.inr q, col⟩ => leafSL C salt ds ⟨q, col⟩

def plainsSL (C : CK) : (ds : List RD) → List _root_.Fmt.RoundOut → Option (Plains (uL C ds))
  | [], [] => some ()
  | d :: ds, o :: os =>
    match PlainOf.ofGots d.items o.vals, plainsSL C ds os with
    | some p, some r => some (GPlain.mk d.entry.work p o.nonce, r)
    | _, _ => none
  | _, _ => none

/-- TWO: the format's number of a position's tree, and the leaf's number -/
def noT : (ts : List _root_.Fmt.Shape) → PosT ts → Nat × Nat
  | s :: _, .inl x => (s.tree, x.val)
  | _ :: ts, .inr p => noT ts p

def placeSL (C : CK) : (ds : List RD) → OPos (uL C ds) → Nat × Nat
  | [], p => p.elim
  | d :: _, .inl x => noT d.trees x
  | _ :: ds, .inr q => placeSL C ds q

/-- TWO: a list of words as a column of a position's tree -/
def symT : (ts : List _root_.Fmt.Shape) → (p : PosT ts) → List UInt64 → Option (SymT ts p)
  | s :: _, .inl _, l =>
    if h : l.length = s.W then some (fun i => l[i.val]'(by rw [h]; exact i.isLt)) else none
  | _ :: ts, .inr p, l => symT ts p l

def symSL (C : CK) : (ds : List RD) → (p : OPos (uL C ds)) → List UInt64 → Option (OSym (uL C ds) p)
  | [], p, _ => p.elim
  | d :: _, .inl x, l => symT d.trees x l
  | _ :: ds, .inr q, l => symSL C ds q l

/-- What the parser asks of a protocol. -/
def TYS (S : _root_.Fmt.Spec) (C : CK) (dec : View → Bool) : TypingP (PSof C (rds S) dec) where
  saltBytes := S.plan.salt
  plains := fun os => (plainsSL C (rds S) os.toList).map fun r => ((), r)
  place := fun p => match p with
    | .inl e => e.elim
    | .inr q => placeSL C (rds S) q
  sym := fun p l => match p with
    | .inl e => e.elim
    | .inr q => symSL C (rds S) q l

/-- a plain part of the whole shape, carried over -/
def embPS (Bd : Type) (C : CK) (ds : List RD) (dec : View → Bool) :
    PlainPart (Twin.up (SOf C ds)) (Twin.allLo (SOf C ds)) →
    PlainPart (Compile.Batch.shapeOf (LbS Bd C ds dec) .onl) (Compile.Batch.annOf (LbS Bd C ds dec) .onl)
  | .inl x => .inl x
  | .inr q => .inr (embPL C ds q)

end TypedOracleCompiler.Run.PQ
