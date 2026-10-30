-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PageQMsg.lean: a prover's message of a round, as the programs' format spells it, as a partial
code of (root or none, typed plain part): by recursion on the round's items.

A chain query of the compiled verifier (`FbIn`, Compile/Batch/Oracles.lean) holds the prover's
message of a round, as a root or none and a plain part. This file writes that message as a bit
string, with a parser. Definitions that compute, with their laws. After the format page, in an
edition that is not the one that ships: R8.2 (the items of a message and their bytes), R5.2 (the
nonce's word ends a round's call).
A partial code (`PCode A`, Run/CodingPart.lean) writes some points of A as bit strings (`put`) and
reads them back (`parse`); its two laws: `parse s = some a` exactly if `put a = some s`.
Run/PlanQTypes.lean makes the typed plain part of a round from the description's list of items
(`PlainOf`: the items but the roots). The compiled verifier's chain query holds the root apart
(root or none). The format spells the message as its items in order, the root at its place.

Main names:
  `RootOf l`: the roots of a message, one digest for each item "root".
  `toRoots`, `ofRoots`: "root or none" as `RootOf l`, and back: for a message with no root, or with
    one; a message with two roots has no typed form (both maps refuse); both laws
    (`ofRoots_toRoots`, `toRoots_ofRoots`).
  `msgBits l`: the number of bits of a message.
  `pMsg l`: a `PCode (RootOf l × PlainOf l)` with the proof that every string has `msgBits l` bits
    (`pMsg_len`): root: its 256 bits; an element of F, a word: a word; an element of E, an answer:
    three words.
  `pRound w l : PCode (Option (Dig 256) × GPlain ℕ w (PlainOf l))`: the message and then the 64
    bits of the nonce's word: the word 0 in a round without work (w = 0), the plain part's last
    component else; `pRound_len`.

Limits: not tested here: that a word is below the field's prime (as in Run/CodingAtoms.lean).
This file does not say that the strings are the bits of `PlainOf.bytes`: another file's tie.

Terms: lean/GLOSSARY.md.
-/
import Run.CodingAtoms
import Run.PlanQTypes

set_option autoImplicit false

namespace Run.PCode
variable {A B : Type}

theorem congr_len (p : PCode A) (e : A ≃ B) (n : ℕ) (hp : p.Len n) : (p.congr e).Len n :=
  fun b s h => hp (e.symm b) s h

end Run.PCode

namespace Run.PQ
open Rom Iop
open _root_.Fmt (Item)

/-- the roots of a message -/
def RootOf : List Item → Type
  | [] => Unit
  | .root :: l => Dig 256 × RootOf l
  | .f :: l => RootOf l
  | .word :: l => RootOf l
  | .e :: l => RootOf l
  | .answer :: l => RootOf l

def toRoots : (l : List Item) → Option (Dig 256) → Option (RootOf l)
  | [], none => some ()
  | [], some _ => none
  | .root :: l, some r => (toRoots l none).map fun y => ((r, y) : Dig 256 × RootOf l)
  | .root :: _, none => none
  | .f :: l, rt => toRoots l rt
  | .word :: l, rt => toRoots l rt
  | .e :: l, rt => toRoots l rt
  | .answer :: l, rt => toRoots l rt

def ofRoots : (l : List Item) → RootOf l → Option (Option (Dig 256))
  | [], _ => some none
  | .root :: l, (y : Dig 256 × RootOf l) =>
      match ofRoots l y.2 with
      | some none => some (some y.1)
      | _ => none
  | .f :: l, y => ofRoots l y
  | .word :: l, y => ofRoots l y
  | .e :: l, y => ofRoots l y
  | .answer :: l, y => ofRoots l y

theorem ofRoots_toRoots :
    ∀ (l : List Item) (rt : Option (Dig 256)) (y : RootOf l),
      toRoots l rt = some y → ofRoots l y = some rt
  | [], none, _, _ => rfl
  | [], some _, _, h => by cases h
  | .root :: l, some r, y, h => by
      have h0 : (toRoots l none).map (fun y => ((r, y) : Dig 256 × RootOf l)) = some y := h
      cases hy : toRoots l none with
      | none => rw [hy] at h0; cases h0
      | some y' =>
          rw [hy] at h0
          rw [← Option.some.inj h0]
          show (match ofRoots l y' with
            | some none => some (some r)
            | _ => none) = some (some r)
          rw [ofRoots_toRoots l none y' hy]
  | .root :: _, none, _, h => by cases h
  | .f :: l, rt, y, h => ofRoots_toRoots l rt y h
  | .word :: l, rt, y, h => ofRoots_toRoots l rt y h
  | .e :: l, rt, y, h => ofRoots_toRoots l rt y h
  | .answer :: l, rt, y, h => ofRoots_toRoots l rt y h

theorem toRoots_ofRoots :
    ∀ (l : List Item) (y : RootOf l) (rt : Option (Dig 256)),
      ofRoots l y = some rt → toRoots l rt = some y
  | [], _, rt, h => by
      rw [← Option.some.inj h]
      rfl
  | .root :: l, (y : Dig 256 × RootOf l), rt, h => by
      have h0 : (match ofRoots l y.2 with
        | some none => some (some y.1)
        | _ => none) = some rt := h
      cases hy : ofRoots l y.2 with
      | none => rw [hy] at h0; cases h0
      | some o =>
          cases o with
          | some _ => rw [hy] at h0; cases h0
          | none =>
              rw [hy] at h0
              rw [← Option.some.inj h0]
              show (toRoots l none).map (fun z => ((y.1, z) : Dig 256 × RootOf l)) = some y
              rw [toRoots_ofRoots l y.2 none hy]
              rfl
  | .f :: l, y, rt, h => toRoots_ofRoots l y rt h
  | .word :: l, y, rt, h => toRoots_ofRoots l y rt h
  | .e :: l, y, rt, h => toRoots_ofRoots l y rt h
  | .answer :: l, y, rt, h => toRoots_ofRoots l y rt h

/-- the number of bits of a message -/
def msgBits : List Item → ℕ
  | [] => 0
  | .root :: l => 256 + msgBits l
  | .f :: l => 64 + msgBits l
  | .word :: l => 64 + msgBits l
  | .e :: l => 192 + msgBits l
  | .answer :: l => 192 + msgBits l

/-- a field in front that belongs to the roots -/
def eqR (A R P : Type) : A × (R × P) ≃ (A × R) × P := (Equiv.prodAssoc A R P).symm

/-- a field in front that belongs to the plain part -/
def eqP (A R P : Type) : A × (R × P) ≃ R × (A × P) :=
  ⟨fun x => (x.2.1, (x.1, x.2.2)), fun y => (y.2.1, (y.1, y.2.2)), fun _ => rfl, fun _ => rfl⟩

/-- The message, with the length of its strings. -/
def pMsg : (l : List Item) → { p : PCode (RootOf l × PlainOf l) // p.Len (msgBits l) }
  | [] =>
    ⟨(pUnit []).congr ⟨fun _ => ((), ()), fun _ => (), fun _ => rfl, fun _ => rfl⟩,
      fun _ s h => by rw [← Option.some.inj h]; rfl⟩
  | .root :: l =>
    ⟨(pDig.cons 256 pDig_len fun _ => (pMsg l).1).congr (eqR (Dig 256) (RootOf l) (PlainOf l)),
      PCode.congr_len _ _ _ (PCode.cons_len _ _ _ _ (msgBits l) fun _ => (pMsg l).2)⟩
  | .f :: l =>
    ⟨(pU64.cons 64 pU64_len fun _ => (pMsg l).1).congr (eqP UInt64 (RootOf l) (PlainOf l)),
      PCode.congr_len _ _ _ (PCode.cons_len _ _ _ _ (msgBits l) fun _ => (pMsg l).2)⟩
  | .word :: l =>
    ⟨(pU64.cons 64 pU64_len fun _ => (pMsg l).1).congr (eqP UInt64 (RootOf l) (PlainOf l)),
      PCode.congr_len _ _ _ (PCode.cons_len _ _ _ _ (msgBits l) fun _ => (pMsg l).2)⟩
  | .e :: l =>
    ⟨(pE3.cons 192 pE3_len fun _ => (pMsg l).1).congr (eqP _root_.Fmt.Ext (RootOf l) (PlainOf l)),
      PCode.congr_len _ _ _ (PCode.cons_len _ _ _ _ (msgBits l) fun _ => (pMsg l).2)⟩
  | .answer :: l =>
    ⟨(pE3.cons 192 pE3_len fun _ => (pMsg l).1).congr (eqP _root_.Fmt.Ext (RootOf l) (PlainOf l)),
      PCode.congr_len _ _ _ (PCode.cons_len _ _ _ _ (msgBits l) fun _ => (pMsg l).2)⟩

theorem pMsg_len (l : List Item) : (pMsg l).1.Len (msgBits l) := (pMsg l).2

def rtTo (l : List Item) (x : Option (Dig 256) × PlainOf l) : Option (RootOf l × PlainOf l) :=
  (toRoots l x.1).map fun y => (y, x.2)

def rtOf (l : List Item) (y : RootOf l × PlainOf l) : Option (Option (Dig 256) × PlainOf l) :=
  (ofRoots l y.1).map fun rt => (rt, y.2)

theorem rtOf_rtTo (l : List Item) (x : Option (Dig 256) × PlainOf l)
    (y : RootOf l × PlainOf l) (h : rtTo l x = some y) : rtOf l y = some x := by
  unfold rtTo at h
  unfold rtOf
  cases hr : toRoots l x.1 with
  | none => rw [hr] at h; cases h
  | some r =>
      rw [hr] at h
      rw [← Option.some.inj h]
      show (ofRoots l r).map (fun rt => (rt, x.2)) = some x
      rw [ofRoots_toRoots l x.1 r hr]
      rfl

theorem rtTo_rtOf (l : List Item) (y : RootOf l × PlainOf l)
    (x : Option (Dig 256) × PlainOf l) (h : rtOf l y = some x) : rtTo l x = some y := by
  unfold rtOf at h
  unfold rtTo
  cases hr : ofRoots l y.1 with
  | none => rw [hr] at h; cases h
  | some rt =>
      rw [hr] at h
      rw [← Option.some.inj h]
      show (toRoots l rt).map (fun z => (z, y.2)) = some y
      rw [toRoots_ofRoots l y.1 rt hr]
      rfl

/-- the message, on "root or none" -/
def pMsgO (l : List Item) : PCode (Option (Dig 256) × PlainOf l) :=
  (pMsg l).1.pull (rtTo l) (rtOf l) (rtOf_rtTo l) (rtTo_rtOf l)

theorem pMsgO_len (l : List Item) : (pMsgO l).Len (msgBits l) :=
  PCode.pull_len _ _ _ _ _ _ (pMsg_len l)

def word0 : List Bool := bytesToBits (_root_.Fmt.u64n 0)

/-- The message and then the nonce's word. -/
def pRound : (w : ℕ) → (l : List Item) → PCode (Option (Dig 256) × GPlain ℕ w (PlainOf l))
  | 0, l =>
    ((pMsgO l).cons (msgBits l) (pMsgO_len l) fun _ => pUnit word0).congr
      ⟨fun x => x.1, fun y => (y, ()), fun _ => rfl, fun _ => rfl⟩
  | _ + 1, l =>
    ((pMsgO l).cons (msgBits l) (pMsgO_len l) fun _ => pWord).congr ⟨fun x =>
        (x.1.1, ((x.1.2, x.2) : PlainOf l × ℕ)),
      fun y => ((y.1, (show PlainOf l × ℕ from y.2).1), (show PlainOf l × ℕ from y.2).2),
      fun _ => rfl, fun _ => rfl⟩

theorem pRound_len : ∀ (w : ℕ) (l : List Item), (pRound w l).Len (msgBits l + 64)
  | 0, _ => PCode.congr_len _ _ _ (PCode.cons_len _ _ _ _ 64 fun _ => pUnit_len word0)
  | _ + 1, _ => PCode.congr_len _ _ _ (PCode.cons_len _ _ _ _ 64 fun _ => pWord_len)

end Run.PQ
