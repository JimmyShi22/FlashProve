-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Decl/KeyAsks169.lean: which strings of calls with the number 169 the asking reading of a
key file asks: no string but those of the calls that hash the parameter bytes of the key's three
chains; and the derivation of a table's seeds asks none.

OnBytes/Tie/Decl/ProofAsks169.lean proves the like of a proof file's asking reading, and carries the
frame "every call of the hash under a number other than 169, and the call under 169 on the
description's parameter bytes" through the tail that a key file and a proof file share
(`okR_readTailAt`). Here the frame is carried through the reader of a key file, whose first chain is
the one-time chain. What it is for: a reading of a key file that takes the public digests in the
place of its own questions needs to lay in three answers and no more. Statements and proofs.

Main names:
  `okR_readKeyAt`: the frame, at letters.
  `KeyOnly169 asm k table file j`: every string of a call with the number 169 that `typedKR asm k
    table file j` (OnBytes/Tie/KeyAsked.lean) asks is the string of the call on the parameter bytes
    of k's one-time, shared or second chain.
  `keyOnly169`: THE LAW: it holds of every plain map, parameters, table, file and place. No premise.
  `keeps0`, `ok0_HM`, `seedsBy_off169`: the derivation of a table's seeds at the asking hash
    (`seedsBy`, OnBytes/Tie/EntryAskM.lean) asks no string of a call with the number 169 at all. No
    premise.
Limits: on every path, whatever the oracle answers. Nothing on how often these strings are asked, on
the other strings, or on values. No probability. Nothing on soundness.

-/
import OnBytes.Tie.Decl.ProofAsks169
import OnBytes.Tie.KeyAsked

set_option autoImplicit false

namespace OnBytes.Tie

section Frame

open OnBytes.Proof hiding climb readPlace Reading need Reading.fromStart readerName readNamed
    requestItem readTail readProof check
open OnBytes.TwoPort.M OnBytes.TwoPort.M.Proof
open OnBytes.Params

variable {m : Type → Type} [Monad m] [LawfulMonad m] (k : Keeps m) (h : HashM m)
  (hh : ∀ n t i s b, n % 65536 ≠ 169 → k.ok (h n t i s b))
include hh

theorem okR_readKeyAt (c : KeyChains) (table : TableName) (file : ByteArray) (j : Nat)
    (h1 : k.ok (h 169 0 1 Fmt.zero32 c.oneTime.given.bytes))
    (h2 : k.ok (h 169 0 1 Fmt.zero32 c.shared.given.bytes))
    (h3 : k.ok (h 169 0 1 Fmt.zero32 c.second.given.bytes)) :
    OkR k (OnBytes.TwoPort.M.Key.readKey h c table file j) := by
  unfold OnBytes.TwoPort.M.Key.readKey
  dsimp only
  refine okR_bind k (RoadKeeps.ok_need k _ _) fun x => ?_
  obtain ⟨rounds, dry⟩ := x
  refine okR_need_bind k _ fun spec e => ?_
  have p1 : spec.base.params = c.oneTime.given.bytes := RoadKeepsAt.params_of_describe e
  refine okR_bind k (RoadKeepsAt.ok_readNamed k h hh _ spec _ _ (p1 ▸ h1)) fun first => ?_
  refine okR_bind k (okR_readTailAt k h hh (OnBytes.Key.tailPublic c table) _ _ _ h2 h3)
    fun r => ?_
  dsimp only
  split
  · exact okR_bind k (okR_throw k _) fun _ => okR_pure k _
  · exact okR_bind k (okR_pure k _) fun _ => okR_pure k _

end Frame

open OnBytes.TwoPort
open OnBytes.Slice (IsCall169)
open OnBytes.Params (TableName KeyChains)
open OnBytes.Proof (TailRead)

/-- Of the strings of calls with the number 169 the reading asks the three alone. -/
def KeyOnly169 {Out : Type} (asm : TailRead → Option Out) (c : KeyChains) (table : TableName)
    (file : ByteArray) (j : Nat) : Prop :=
  (typedKR asm c table file j).AsksIn fun _ (s : List Bool) =>
    IsCall169 s → s = strPar c.oneTime.given.bytes ∨ s = strPar c.shared.given.bytes ∨
      s = strPar c.second.given.bytes

/-- **THE LAW.** -/
theorem keyOnly169 {Out : Type} (asm : TailRead → Option Out) (c : KeyChains) (table : TableName)
    (file : ByteArray) (j : Nat) : KeyOnly169 asm c table file j := by
  unfold KeyOnly169 typedKR
  have e := okR_readKeyAt (keeps3 c.oneTime.given.bytes c.shared.given.bytes c.second.given.bytes)
    (Fmt.HM Run.askB) (ok3_HM _ _ _) c table file j (ok3_digest _ _ _ _ (Or.inl rfl))
    (ok3_digest _ _ _ _ (Or.inr (Or.inl rfl))) (ok3_digest _ _ _ _ (Or.inr (Or.inr rfl)))
    Session.start
  refine Rom.OComp.AsksIn.bind ?_ e
  intro _
  trivial

/-! ## The derivation of a table's seeds -/

/-- "No string of a call with the number 169 is asked": pure has the property, and bind keeps it. -/
def keeps0 : M.Keeps (ZKCP.OComp 256) where
  ok := fun x => (Rom.toRom x).AsksIn fun _ s => ¬ IsCall169 s
  ok_pure := fun _ => trivial
  ok_bind := fun x g hx hg => by
    show (Rom.toRom (x.bind g)).AsksIn _
    rw [Rom.toRom_bind]
    exact Rom.OComp.AsksIn.bind hg hx

/-- A call of the asking hash under a number other than 169 has the property. -/
theorem ok0_HM (n t i : ℕ) (st bs : ByteArray) (hn : n % 65536 ≠ 169) :
    keeps0.ok (Fmt.HM Run.askB n t i st bs) := by
  unfold Fmt.HM
  split
  · exact keeps0.ok_bind _ _ ⟨not169 _ _ _ _ _ _ hn, fun _ => trivial⟩ fun _ =>
      keeps0.ok_bind _ _ ⟨not169 _ _ _ _ _ _ hn, fun _ => trivial⟩ fun _ => keeps0.ok_pure _
  · exact ⟨not169 _ _ _ _ _ _ hn, fun _ => trivial⟩

/-- **The derivation of a table's seeds asks no string of a call with the number 169.** -/
theorem seedsBy_off169 (f : Fmt.Fld) (name : ByteArray) (bits count : Nat) :
    (Rom.toRom (seedsBy Run.askB f name bits count)).AsksIn
      fun _ (s : List Bool) => ¬ IsCall169 s := by
  have e : keeps0.ok (seedsBy Run.askB f name bits count) := by
    unfold seedsBy Slice.recordSeedsW Fmt.recordFirstW Fmt.firstValueW
    refine keeps0.ok_bind _ _ (ok0_HM 160 _ _ _ _ (by decide)) fun ρ0 => ?_
    exact keeps0.ok_bind _ _ (M.EngineKeepsAt.ok_queryW keeps0 _ ok0_HM _ _ _ _ _ _) fun _ =>
      keeps0.ok_pure _
  exact e

end OnBytes.Tie

#print axioms OnBytes.Tie.keyOnly169
#print axioms OnBytes.Tie.seedsBy_off169
