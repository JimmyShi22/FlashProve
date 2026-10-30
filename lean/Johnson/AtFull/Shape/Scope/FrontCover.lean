-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/FrontCover.lean: THE COVER ON THE TERM's LIST OF FALLS AT THE 25 BATCHINGS: where the first thread's list
of falls says nothing at a batching, the smallness test's fall at it says nothing. The batching stands at the place of
k8FrontFall (a written fact), and that fall is in the list (fallsHead_front).

  written_batchings   the written list's places at the 25 batchings
  front_cover         at 14 l + 8 + 1, l < 24
  front_cover_head    at 337 + 10

Limits. Under the head. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread
import Johnson.Desc.ProofFile.Honest.Thread.HeadFacts
import Johnson.Desc.ProofFile.Honest.K8.FrontFallList
import Johnson.AtFull.Shape.Numbers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open P5J (TS)
open ProofFile.Honest (OnlineProverWithDescription fallsBy Fall oAt fallsHead_front)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K8 (k8Front batchPlace k8Front_of_silent)

set_option maxRecDepth 1000000 in
theorem written_batchings :
    ((List.range 24).all fun l => P5J.At.ps[14 * l + 8 + 1]? == some (batchPlace l 0)) = true ∧
      P5J.At.ps[337 + 10]? = some (batchPlace 24 1) := by decide +kernel

variable {files : VerifierAndGoals.PublicFiles} {W₀ Rc Tr X₀ X : Type} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

theorem cover_at (h : HeadAtReturn files A) (n : FallNumbers) {j l : Nat} (hl : l < 25)
    (hj : j < 358) (hp : P5J.At.ps[j]? = some (batchPlace l (oAt l))) (s : TS)
    (ds : List Fmt.Drawn)
    (hs : fallsBy (firstFalls A n) h.description.first.blocksInOrder j s ds = none) : k8Front s ds = none := by
  have hlen := flat_len h.head
  obtain ⟨blk, hb⟩ : ∃ blk, h.firstChain.blocksInOrder[j]? = some blk :=
    ⟨h.firstChain.blocksInOrder[j], List.getElem?_eq_getElem (by rw [hlen]; exact hj)⟩
  have ep : blk.place = batchPlace l (oAt l) :=
    Option.some.inj ((ProofFile.Honest.FirstFill.place_of_member h.head hb).symm.trans hp)
  have hs' : ProofFile.Honest.fallOf (firstFalls A n) blk.place s ds = none := by
    have e : fallsBy (firstFalls A n) h.firstChain.blocksInOrder j = ProofFile.Honest.fallOf (firstFalls A n) blk.place := by
      unfold fallsBy
      rw [hb]
    rw [← e]
    exact hs
  rw [ep] at hs'
  exact k8Front_of_silent (fallsHead_front hl) hs'

/-- **THE COVER AT THE 24 BATCHINGS IN FRONT OF THE HEAD.** -/
theorem front_cover (h : HeadAtReturn files A) (n : FallNumbers) (l : Nat) (hl : l < 24) (s : TS)
    (ds : List Fmt.Drawn)
    (hs : fallsBy (firstFalls A n) h.description.first.blocksInOrder (14 * l + 8 + 1) s ds = none) :
    k8Front s ds = none := by
  have e := List.all_eq_true.1 written_batchings.1 l (List.mem_range.2 hl)
  have e' : P5J.At.ps[14 * l + 8 + 1]? = some (batchPlace l 0) := beq_iff_eq.1 e
  have o : oAt l = 0 := if_neg (by omega)
  exact cover_at h n (l := l) (by omega) (by omega) (by rw [o]; exact e') s ds hs

/-- **THE COVER AT THE HEAD's BATCHING.** -/
theorem front_cover_head (h : HeadAtReturn files A) (n : FallNumbers) (s : TS) (ds : List Fmt.Drawn)
    (hs : fallsBy (firstFalls A n) h.description.first.blocksInOrder (337 + 10) s ds = none) :
    k8Front s ds = none :=
  cover_at h n (l := 24) (by omega) (by omega) written_batchings.2 s ds hs

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.written_batchings
#print axioms Johnson.AtFull.Shape.front_cover
#print axioms Johnson.AtFull.Shape.front_cover_head
