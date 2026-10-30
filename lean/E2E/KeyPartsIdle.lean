-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
WHAT IS LACKING STANDS IN NAMED PREMISES, NOT PROVED.
E2E/KeyPartsIdle.lean: `KeyParts` has a term at any types that have a value, and it meets the premises
that `stand_three` (E2E/KeyStandMember.lean) puts on `K'`.

Why. A statement over `K'` says nothing if there is no `K'`. This file answers that, and only that.

Main names.
  `fixedKeyParts`: a term. ITS FIRST CHAIN'S HALVES SEND NOTHING, ITS FOUR PROXIMITY TESTS' HALVES HAVE NO PART, AND
    NO TERM HERE IS A PROVER FOR THOSE PLACES. Its stored table, index, coins, `lin`, `send` are overwritten
    by `keyOf`.
  `idle_quiet`: the four halves are quiet.

Not here. A proximity test's real half: no such half is written on this ground; the halves
with no part stand for it here; by the text of `chainSteps` they would be refused at the next member: a
thread past border 9 needs real ones.

No coin is named here.

Nothing on soundness, completeness, hiding or binding.

-/
import E2E.KeyStandMember

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace AtPublicFiles.KeyPartsIdle
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (zeroE)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeyBook (foldedTestPlace omegaTestPlace ownTestPlace rngPlace)
open AtPublicFiles.AtFiles.Full (QK)

variable {W₀ Rc X₀ X Wk : Type}

/-- The points of a lookup that reads nothing. -/
def idlePts : K3.Pts :=
  ⟨zeroE, zeroE, #[], fun _ _ => #[], fun _ => #[], #[], []⟩

/-- A sending that sends nothing of its own. -/
def idleSend {W Y : Type} : K1.SendJob W Y :=
  ⟨_root_.Desc.K14.parK1 QK 2 "nothing" #[], 0, fun _ => none, fun _ _ _ _ _ => none⟩

/-- A batching's numbers that are idle. -/
def idleWhere : VerifiableInference.Desc.K13.Where :=
  { chain := 1, piece := 0, pieceRows := 0, rows := 0, lin := QK.S, sent := 0 }

/-- **A term of `KeyParts`.** -/
def fixedKeyParts (fc : VerifiableInference.Desc.K3.Face) (wh : VerifiableInference.Desc.K13.Where)
    (d : W₀) (x₀ : X₀) (x : X) (wk : Wk) : KeyParts W₀ Rc X₀ X Wk where
  stored := fun _ _ _ _ => none
  inRange := fun _ => true
  dummy := d
  own₀ := x
  ownShared₀ := x₀
  meet := fun a _ => a
  weights := fun _ => ⟨fun _ _ => 0⟩
  rand := fun _ => ⟨fun _ _ => 0, fun _ _ => 0⟩
  idx := idleSend
  msg := idleSend
  w := idleSend
  reads := ⟨fun _ _ _ => idlePts, fun _ _ _ => []⟩
  jobs0 := ⟨fun _ => ⟨fun _ _ _ => [], fun _ _ _ _ => [], fun _ _ _ => []⟩⟩
  jobs1 := ⟨fun _ => ⟨fun _ _ _ => [], fun _ _ _ _ => [], fun _ _ _ => []⟩⟩
  wit := fun _ => wk
  look0 := ⟨⟨1, some 0, 2, .K3⟩, fc, 0⟩
  look1 := ⟨⟨1, some 1, 2, .K3⟩, fc, 0⟩
  rng := ⟨rngPlace, []⟩
  pile := fun _ _ => []
  batt := wh
  lin := ⟨QK.S, 0, 6⟩
  send := ⟨QK, 0⟩
  onU := ⟨foldedTestPlace, []⟩
  onOmega := ⟨omegaTestPlace, []⟩
  own := ⟨ownTestPlace, []⟩

/-- Its four halves have no part, so none stops. -/
theorem idle_quiet (fc : VerifiableInference.Desc.K3.Face) (wh : VerifiableInference.Desc.K13.Where)
    (d : W₀) (x₀ : X₀) (x : X) (wk : Wk) :
    AtPublicFiles.Stops.QuietHalf (fixedKeyParts (Rc := Rc) fc wh d x₀ x wk).rng ∧
      AtPublicFiles.Stops.QuietHalf (fixedKeyParts (Rc := Rc) fc wh d x₀ x wk).onU ∧
      AtPublicFiles.Stops.QuietHalf (fixedKeyParts (Rc := Rc) fc wh d x₀ x wk).onOmega ∧
      AtPublicFiles.Stops.QuietHalf (fixedKeyParts (Rc := Rc) fc wh d x₀ x wk).own :=
  ⟨fun _ hp => absurd hp List.not_mem_nil, fun _ hp => absurd hp List.not_mem_nil,
    fun _ hp => absurd hp List.not_mem_nil, fun _ hp => absurd hp List.not_mem_nil⟩

/-- **So there is one, at any types with a value.** -/
theorem parts_exist (K₀ : AtPublicFiles.KeyBook.KeyPub) (hK₀ : AtPublicFiles.KeyBook.fullPub = some K₀) (d : W₀) (x₀ : X₀)
    (x : X) (wk : Wk) : Nonempty (KeyParts W₀ Rc X₀ X Wk) := by
  obtain ⟨f₀, f₁, -⟩ := List.length_eq_two.1 (by simpa using AtPublicFiles.KeyBook.of_atFull AtPublicFiles.KeyBook.full_two hK₀)
  exact ⟨fixedKeyParts f₀ idleWhere d x₀ x wk⟩

end AtPublicFiles.KeyPartsIdle

#print axioms AtPublicFiles.KeyPartsIdle.idle_quiet
#print axioms AtPublicFiles.KeyPartsIdle.parts_exist
