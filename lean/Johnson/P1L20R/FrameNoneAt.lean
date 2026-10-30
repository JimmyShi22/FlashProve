-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1L20R/FrameNoneAt.lean:
PAID, IN THE GOALS' SCOPE: FrameOwes' THREE FIELDS NoneBetween
(FrameSits.lean), at the numbers that are filled off what the proof file's own first chain's
sub-protocols tell.

  told_at           the front, every "laid" and every "cleared" tell no oracle message: from
                    front_oracles and frame_oracles (Johnson/IMR/FrameQuiet.lean)
  none_between_at   so NoneBetween at N.withTold (the written list) (c.blocksInOrder.map fun b => g
                    b.oracles), at the 51 numbers: no premise is left but the scope. g: however a
                    sub-protocol's declared oracle messages, round by round, are gathered into one
                    list: any g with g [] = []
  linksW_eq, placesW_eq, none_between_atW   the written lists IM.linksW and IM.placesW are linksFull
                    and flatPlacesOf linksFull true (by Lean's kernel): so the same at placesW and
                    nAt: the premise of shareW_laid and shareW_cleared (FrameShares.lean, not in this library)

Limits. At numbers of that form alone. That the written list is the flat list's own places is not
said here. No soundness statement.

-/
import Johnson.P1L20R.FrameSits
import Johnson.IMR.FrameQuiet
import Johnson.IMR.WrittenList

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1L20

open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S Numbers flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull)
open Johnson.Desc.First.Walk.Tied
open ProofFile (Cl)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

theorem told_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (g : List (List VerifiableInference.Desc.Oracle) → List VerifiableInference.Desc.Oracle)
    (hg : g [] = []) :
    (c.blocksInOrder.map fun b => g b.oracles)[0]? = some [] ∧
      (∀ l, l < 25 → (c.blocksInOrder.map fun b => g b.oracles)[14 * l + 1]? = some []) ∧
      ∀ l, l < 25 → (c.blocksInOrder.map fun b => g b.oracles)[clearIx l]? = some [] := by
  refine ⟨?_, fun l hl => ?_, fun l hl => ?_⟩
  · obtain ⟨b0, e0, _⟩ := IM.front_of O
    rw [List.getElem?_map, e0]
    show some (g b0.oracles) = some []
    rw [IM.front_oracles O e0, hg]
  · obtain ⟨_, bL, _, _, _, _, iL, oL, _⟩ := IM.frame_oracles hS hR O l hl
    rw [List.getElem?_map, iL]
    show some (g bL.oracles) = some []
    rw [oL, hg]
  · obtain ⟨_, _, _, bC, _, hn, _, _, _, _, iC, oC⟩ := IM.frame_oracles hS hR O l hl
    rw [hn] at iC
    rw [List.getElem?_map, iC]
    show some (g bC.oracles) = some []
    rw [oC, hg]

/-- **nFront · nLaid · nClear: PAID, in scope.** -/
theorem none_between_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (N : Numbers)
    (g : List (List VerifiableInference.Desc.Oracle) → List VerifiableInference.Desc.Oracle)
    (hg : g [] = []) :
    NoneBetween (N.withTold (flatPlacesOf linksFull true) (c.blocksInOrder.map fun b => g b.oracles))
        (flatPlacesOf linksFull true) 0 ∧
      (∀ l, l < 25 →
        NoneBetween (N.withTold (flatPlacesOf linksFull true) (c.blocksInOrder.map fun b => g b.oracles))
          (flatPlacesOf linksFull true) (14 * l + 1)) ∧
      ∀ l, l < 25 →
        NoneBetween (N.withTold (flatPlacesOf linksFull true) (c.blocksInOrder.map fun b => g b.oracles))
          (flatPlacesOf linksFull true) (clearIx l) := by
  obtain ⟨h0, hL, hC⟩ := told_at hS hR O g hg
  exact none_between_paid N h0 hL hC

set_option maxRecDepth 1000000 in
theorem linksW_eq : IM.linksW = linksFull := by decide +kernel

theorem placesW_eq : IM.placesW = flatPlacesOf linksFull true := by
  unfold IM.placesW
  rw [linksW_eq]

/-- The same at the written list IM.placesW and the numbers IM.nAt. -/
theorem none_between_atW (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (N : Numbers)
    (g : List (List VerifiableInference.Desc.Oracle) → List VerifiableInference.Desc.Oracle)
    (hg : g [] = []) :
    (∀ l, l < 25 → NoneBetween (N.withTold IM.placesW (c.blocksInOrder.map fun b => g b.oracles))
        IM.placesW (14 * l + 1)) ∧
      ∀ l, l < 25 → NoneBetween (N.withTold IM.placesW (c.blocksInOrder.map fun b => g b.oracles))
        IM.placesW (14 * l + IM.nAt l + 7) := by
  rw [placesW_eq]
  exact (none_between_at hS hR O N g hg).2

end

end P1L20

#print axioms P1L20.linksW_eq
#print axioms P1L20.none_between_atW
#print axioms P1L20.told_at
#print axioms P1L20.none_between_at
