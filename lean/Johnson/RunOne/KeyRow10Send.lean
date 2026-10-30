-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyRow10Send.lean: THE TRACER ON ROW 1.0, LEVEL 3: THE KEY FILE's OWN FIRST BLOCK IS A SENDING IN THE SENSE OF THE SENDING KIND's FILES' LAW (IsSend: Johnson/Desc/K1/Law/GoodSend3.lean): one premise of send_goodIn, PAID, by unfolding the seat (Johnson/Desc/Key/One.lean: sendingSeat · sendIndexMasks) down to the kind's own decideSend.
OBJECT: IsSend at sendingSeat | sendIndexMasks | what Chain.blocksInOrder and «held» make of it · USER: owed10_of's premise hS · LETTERS: one N groups.
  isSend_seat      PROVED: sendingSeat name P is a sending at P, at the reader «the state's statement»
  isSend_idx       PROVED: so sendIndexMasks one N groups is a sending at sendingPar one N.idx … (by isSend_andThen, Johnson/Desc/K1/Law/GoodSend4.lean)
  isSend_of_decide PROVED: IsSend reads a block's decide alone · isSend_held: PROVED: and passes to the held block, at the reader off the second component
KIN: isSend_idxAt | isSend_msgAt | isSend_wAt (in Johnson/RunOne/KeySendIs.lean) say IsSend at the three joined blocks: isSend_seat | isSend_idx HERE ARE TWINS OF THE FIRST OF THEM, TYPED APART: at 1.1 | 1.17 that file's are called; both stand in this library. isSend_of_decide | isSend_held are not in that file.
Nothing on soundness.
-/
import Johnson.Desc.Key.One
import Johnson.Desc.K1.Law.GoodSend4
import Johnson.Desc.Plain.PaidKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows1
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Plain VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K1 (Par IsSend SameMsgs LeavesMsgs isSend_andThen decideSend)

variable {β Cl : Type}

/-- **The seat of a sending is a sending.** -/
theorem isSend_seat (name : String) (P : Par) : IsSend P (fun s : ChainState β => s.d.st) (sendingSeat name P : Block (ChainState β) Cl) := by
  intro s s' r₁ r₂ gs h
  have h' : ((decideSend P s.debt (withLoc s.d (#[] : Array Nat)) [r₁, r₂]).map fun x =>
      ({ owed := none, held := { x.2 with loc := x.1 } } : K1.Owing (_root_.Desc.Plain.DState (Array Nat)))).map (fun y =>
        { s with d := withLoc y.held (), owed := y.owed, sent := y.held.loc }) = .ok s' := h
  cases hd : decideSend P s.debt (withLoc s.d (#[] : Array Nat)) [r₁, r₂] with
  | error e => rw [hd] at h'; cases h'
  | ok x =>
    rw [hd] at h'
    have e : s' = { s with d := withLoc ({ x.2 with loc := x.1 } : _root_.Desc.Plain.DState (Array Nat)) (), owed := none, sent := x.1 } := (Except.ok.inj h').symm
    subst e
    exact ⟨_, _, x.2, _, x.1, hd, ⟨rfl, fun _ => rfl⟩, rfl⟩

/-- IsSend reads a block's decide alone. -/
theorem isSend_of_decide {T : Type} (P : Par) (stOf : T → Statement) (b b' : Block T Cl) (h : b'.decide = b.decide) (hb : IsSend P stOf b) : IsSend P stOf b' := by
  intro s s' r₁ r₂ gs hy
  rw [h] at hy
  exact hb s s' r₁ r₂ gs hy

/-- **It passes to the held block.** -/
theorem isSend_held {Q T : Type} (P : Par) (stOf : T → Statement) (b : Block T Cl) (hb : IsSend P stOf b) :
    IsSend P (fun a : Q × T => stOf a.2) (held b : Block (Q × T) Cl) := by
  intro a a' r₁ r₂ gs hy
  exact hb a.2 a'.2 r₁ r₂ gs (held_decide b a _ gs a' hy).2

/-- **The first sending of the key file's first chain is a sending.** -/
theorem isSend_idx (one : OneTime) (N : Pieces) (groups : List (List Nat)) :
    IsSend (sendingPar one N.idx "the index masks" #[one.indexMasks] groups) (fun s : ChainState β => s.d.st) (sendIndexMasks one N groups : Block (ChainState β) Cl) := by
  unfold sendIndexMasks
  refine isSend_andThen _ _ _ _ _ (isSend_seat _ _) rfl ?_
  intro s s' rs gs h
  have h' : (do
      let i ← named "the sending has left no number" s.sent[0]?
      pure { s with idx := i } : Except String (ChainState β)) = .ok s' := h
  cases hi : s.sent[0]? with
  | none => rw [hi] at h'; cases h'
  | some i =>
    rw [hi] at h'
    have e : s' = { s with idx := i } := (Except.ok.inj h').symm
    subst e
    exact ⟨rfl, fun _ => rfl⟩

end Johnson.RunOne.KeyRows1

#print axioms Johnson.RunOne.KeyRows1.isSend_seat
#print axioms Johnson.RunOne.KeyRows1.isSend_idx
#print axioms Johnson.RunOne.KeyRows1.isSend_held
