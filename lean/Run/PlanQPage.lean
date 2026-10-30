-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanQPage.lean: makes, from a description of a proof's rounds, the interface, the spelling of
typed queries as hash calls, and what the parser needs of a protocol.

Run/PlanQTypes.lean has rounds, shape, view and the protocol `QT C ds dec` from a description.
Run/ToyQ.lean (the interface `Lt`, the spelling `PD`) and Run/ParseToy1.lean (the typing `T`) write
out directly, for one example, three more things. Here each is a function of the description, of the
choice of challenge types C and of the decision dec.
A description is a value of `Fmt.Spec` (Fmt/Rules8.lean). The interface (`BatchProtocol`, Iop/Batch.lean) is
the library's record of three protocols, called Test, Link and Batch, with an encoding and a
decoding of an index. The spelling (`PageD`, Run/CodingFn.lean) has what the format hashes and a
typed query does not hold, or holds in typed form. What the parser needs is the record `Typing`
(Run/ParseChain.lean): `TY`.

Sources. That a leaf's label holds its shape is the format page's rule (docs/format/FORMAT.md, which
comes with the programs, the C++ implementation that comes with this Lean code); this file has not
been held against the page as it ships, and may differ from it.


1. What the file contains. Definitions that can be evaluated.
   `QU C ds dec`: The protocol `QT` with no statement (type `Unit`), over an encoded index of length
     0: the form of an interface's Test.
   `Lt C ds dec`: The interface. Its Test is the protocol itself; Link and Batch are trivial.
   `msgL`, `nonceL`, `leafL`: By recursion on the rounds. `leafL`, of a symbol with its position:
     `Fmt.leafPlace` of the tree's number, the number of the column's words and the number of the
     salt's words; 2^depth + position; the column's bytes with their fill (Fmt/Rules7.lean:
     `fillLen`, at the plan's length of a leaf's salt).
   `PD S C dec`: The data for Run/CodingFn.lean. Label, kinds, work and the vertices' starting value
     are the description's. (Typed round i is the description's round i - 1. The trivial round 0,
     and a number beyond the last round, have the kind "nothing" and no work.) `stm`: the
     description's statement bytes, a constant; the typed first query holds no statement.

2. What is checked when the file compiles. Only the types.

3. Theorems. None.

4. What is not claimed. No law. That the decision speaks of the statement whose bytes the
description holds is the caller's duty. The verifier itself needs the wiring, which is in another
file (Run/PlanQWire.lean).

Terms: lean/GLOSSARY.md.
-/
import Run.PlanQTypes
import Run.CodingFn
import Run.ParseChain

set_option autoImplicit false

namespace Run.PQ
open Iop Rom Compile Compile.Batch

/-- the strategy that sends every round's fixed substitute -/
def dfltS {β : Type} (b : β) : (s : Shape) → Strat s β
  | [] => b
  | r :: s => ((r.dOrc, r.dPlain), fun _ => dfltS b s)

/-- The protocol as the ambient interface's Test needs it: no statement (what a statement there is
stands in the description's bytes and in the decision), no external oracle. -/
@[reducible] def QU (C : CK) (ds : List RD) (dec : View → Bool) : InteractiveOracleProof Unit (oneExternalString 0 Unit) :=
  QT C ds fun _ => dec

@[reducible] def pL : InteractiveOracleProof Unit (twoExternalStrings 0 Unit) :=
  { shape := [], blinded := fun _ => false, extReads := fun _ _ => ∅,
    reads := fun _ _ _ => ∅, accept := fun _ _ _ => true }
@[reducible] def pB : InteractiveOracleProof Unit (oneExternalString 0 Unit) :=
  { shape := [], blinded := fun _ => false, extReads := fun _ _ => ∅,
    reads := fun _ _ _ => ∅, accept := fun _ _ _ => true }

/-- The ambient interface. -/
@[reducible] def Lt (C : CK) (ds : List RD) (dec : View → Bool) : BatchProtocol Unit Unit where
  wordLength := 0
  Symbol := Unit
  EncodingRandomness := Unit
  encodeIndex := fun _ _ _ => ()
  decodeIndex := fun _ => some ()
  offline := QU C ds dec
  link := pL
  maxBatchSize := 1
  onlineBatch := BatchInteractiveOracleProof.ofProto pB
  honestOfflineProver := { Coin := Unit, ext := fun _ _ => (), strat := fun _ _ _ => dfltS () _,
                           Bad := ∅, Hid := fun _ _ => ∅ }
  honestLinkProver := { Coin := Unit, ext := fun _ => (fun _ => (), fun _ => ()), strat := fun _ _ _ => (),
                        Bad := ∅, Hid := fun _ _ => ∅ }
  honestOnlineBatchProver := { Coin0 := Unit, Coin := Unit, ext := fun _ _ => (), strat0 := fun _ _ => (),
                               strat := fun _ _ _ _ => (), Bad := ∅, Hid := fun _ _ => ∅, stop0 := fun _ => false }
  early := id
  late := none

/-- the shape, with proof of work, of the rounds after the trivial round -/
abbrev sG (C : CK) (ds : List RD) : Shape := (shapeL C ds).grind ℕ (gL C ds)

/-- the message's bytes of a typed plain part -/
def msgL (C : CK) (rt : ByteArray) : (ds : List RD) → PlainPart (sG C ds) (RoundSplits.allLocal _) → ByteArray
  | [], p => p.elim
  | d :: _, .inl (.inr p) => PlainOf.bytes rt d.items (GPlain.old (b := d.entry.work) p)
  | _ :: _, .inl (.inl _) => ByteArray.empty
  | _ :: ds, .inr q => msgL C rt ds q

/-- the nonce of a typed plain part -/
def nonceL (C : CK) : (ds : List RD) → PlainPart (sG C ds) (RoundSplits.allLocal _) → Nat
  | [], p => p.elim
  | d :: _, .inl (.inr p) => GPlain.nonce (b := d.entry.work) p
  | _ :: _, .inl (.inl _) => 0
  | _ :: ds, .inr q => nonceL C ds q

def trNo : Option _root_.Fmt.Shape → Nat
  | none => 0
  | some s => s.tree

/-- of a symbol with its position: `Fmt.leafPlace` of the tree's number, the number of the column's
words and the number of the salt's words, 2 ^ depth + position, the column's bytes with their fill
-/
def leafL (C : CK) (salt : Nat) : (ds : List RD) → SymAny (sG C ds) → Nat × Nat × ByteArray
  | [], ⟨p, _⟩ => p.elim
  | d :: _, ⟨.inl x, col⟩ =>
    (_root_.Fmt.leafPlace (trNo d.tree) (colW d.tree) (salt / 8),
      posN d.tree + x.val,
      _root_.Fmt.colBytes (List.ofFn col) ++
        _root_.Fmt.zeroBytes (_root_.Fmt.fillLen (colW d.tree) salt))
  | _ :: ds, ⟨.inr q, col⟩ => leafL C salt ds ⟨q, col⟩

/-- The spellings. -/
def PD (S : _root_.Fmt.Spec) (C : CK) (dec : View → Bool) : PageD (Lt C (rds S) dec) where
  label := S.label
  kind := fun i => if i = 0 then 7 else ((S.rounds[i - 1]?).map (·.kind.num)).getD 7
  work := fun i => if i = 0 then 0 else ((S.rounds[i - 1]?).map (·.entry.work)).getD 0
  stm := fun _ => S.statement
  msg := fun _ rt pl => match pl with
    | .inl _ => ByteArray.empty
    | .inr q => msgL C (rt.getD ByteArray.empty) (rds S) q
  nonce := fun _ pl => match pl with
    | .inl _ => 0
    | .inr q => nonceL C (rds S) q
  leaf := fun s => match s with
    | ⟨.inl p, _⟩ => p.elim
    | ⟨.inr q, col⟩ => leafL C S.plan.salt (rds S) ⟨q, col⟩
  cfg := S.cfg

/-- the typed plain parts from what the reader has read -/
def plainsL (C : CK) : (ds : List RD) → List _root_.Fmt.RoundOut → Option (Plains (sG C ds))
  | [], [] => some ()
  | d :: ds, o :: os =>
    match PlainOf.ofGots d.items o.vals, plainsL C ds os with
    | some p, some r => some (GPlain.mk d.entry.work p o.nonce, r)
    | _, _ => none
  | _, _ => none

/-- a position's tree and column -/
def placeL (C : CK) : (ds : List RD) → OPos (sG C ds) → Nat × Nat
  | [], p => p.elim
  | d :: _, .inl x => (trNo d.tree, x.val)
  | _ :: ds, .inr q => placeL C ds q

/-- a column of words as the symbol at a position -/
def symL (C : CK) : (ds : List RD) → (p : OPos (sG C ds)) → List UInt64 → Option (OSym (sG C ds) p)
  | [], p, _ => p.elim
  | d :: _, .inl _, l =>
    if h : l.length = colW d.tree then some (fun i => l[i.val]'(by rw [h]; exact i.isLt)) else none
  | _ :: ds, .inr q, l => symL C ds q l

/-- What the parser asks of a protocol. -/
def TY (S : _root_.Fmt.Spec) (C : CK) (dec : View → Bool) :
    Typing (BatchInteractiveOracleProof.ofProto (QU C (rds S) dec)) where
  saltBytes := S.plan.salt
  plains := fun os => (plainsL C (rds S) os.toList).map fun r => ((), r)
  place := fun p => match p with
    | .inl e => e.elim
    | .inr q => placeL C (rds S) q
  sym := fun p l => match p with
    | .inl e => e.elim
    | .inr q => symL C (rds S) q l

end Run.PQ
