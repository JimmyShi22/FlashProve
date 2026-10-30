-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Riders/BuiltFvs.lean: THE FLAGS "DOES THIS SEGMENT's SUB-PROOF LEAVE A ROW ON THE
COMMITTED TABLE", READ OFF THE BUILT SEGMENTS (fvsAt Z, Johnson/Top/H0/Fill/D1At.lean), ARE ONE
CLOSED LIST IN THE GOALS' SCOPE: true at the even numbers below 25: the twelve feed-forward segments
and the output head; and in front of segment 2 g just g segments leave a row.

  `fvsFull`: the closed list.
  `fvs_plain`: where the plain road returns the public part Z, at Z.p.X.p4 = true and
    Z.p.X.NGr = 12: fvsAt Z = fvsFull.
  **`fvs_at_scope`**: in the goals' scope (hS, hR), at an opening O of the IOP as written in Lean:
    fvsAt Z = fvsFull.
  `rowsBefore_full`: rowsBefore fvsFull (2 * g) = g for g ≤ 12: closed; by cases.
  **`rowsBefore_at`**: in scope, at an opening, g < 12: rowsBefore (fvsAt Z) (2 * g) = g.
No new argument: listLinksH_with (OnBytes/Tie/Pv/Keeps/LinksOrder.lean: which link stands at which
place, each with its flag by its make) and built_at (Johnson/Goal/Meaning/PlanShapes.lean: the built
links are the listed ones with one other field filled). The road to Z.p.built is that of
Johnson/Road/K4/Riders/BuiltNs.lean.
Limits. That there is an opening is shown by no theorem. K04_law, the law of K4's sub-protocol
itself, IS NOT PROVED. Nothing on soundness.


-/
import Johnson.Road.K4.Riders.PlanOfScope
import Johnson.Top.H0.Fill.D1At
import Johnson.Top.H0.Walk.FrameEntriesDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Riders

open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.FillP1 (fvsAt)
open Johnson.Desc.First.Walk.Seat (fvsOf)
open Johnson.Desc.First.Walk.Tied (rowsBefore)

/-- The closed list of the flags: true at the even numbers below 25. -/
def fvsFull : List Bool := (List.range 25).map fun i => i % 2 == 0

/-- Where the plain road returns the public part Z, with attention and twelve groups: the flags
off the built segments are the closed list. -/
theorem fvs_plain {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) (h4 : Z.p.X.p4 = true) (hN : Z.p.X.NGr = 12) :
    fvsAt Z = fvsFull := by
  have hB : ProofFile.Plain.builtOf Z.p.X Z.p.chains = .ok Z.p.built :=
    IM.planned_built (ProofFile.Law.madeOf_planned (ProofFile.Law.pubBy_made
            (show ProofFile.pubBy (ProofFile.PlainG.madeOf o) ProofFile.plainStarts pol lay KL = .ok Z from hZ)))
  obtain ⟨l₀, h₀, hB⟩ := IM.plain_built hB
  unfold ProofFile.Plain.linksPlain at h₀
  rw [h4] at h₀
  obtain ⟨hG, hA, hsz, p0, pH⟩ := OnBytes.L5.LinksOrder.listLinksH_with _ _ _ _ _ h₀
  obtain ⟨bs, bat⟩ := Meaning.built_at hB
  rw [hN] at hG hA hsz pH
  unfold fvsAt fvsOf fvsFull
  refine List.ext_getElem? fun i => ?_
  rw [List.getElem?_map, List.getElem?_map, Array.getElem?_toList]
  by_cases hi : i < 25
  · rw [List.getElem?_range hi]
    obtain ⟨g, hg⟩ : ∃ g, i = 2 * g ∨ i = 2 * g + 1 := ⟨i / 2, by omega⟩
    rcases hg with rfl | rfl
    · have e2 : (2 * g % 2 == 0) = true := by
        rw [Nat.mul_mod_right]
        rfl
      by_cases h12 : g = 12
      · subst h12
        obtain ⟨ar, e⟩ := bat (2 * 12) _ pH
        rw [e]
        rfl
      · obtain ⟨q0, _⟩ := p0 g _ _
          (Array.getElem?_eq_getElem (by rw [hG]; omega))
          (Array.getElem?_eq_getElem (by rw [hA]; omega))
        obtain ⟨ar, e⟩ := bat (2 * g) _ q0
        rw [e]
        show some true = some (2 * g % 2 == 0)
        rw [e2]
    · have e2 : ((2 * g + 1) % 2 == 0) = false := by
        rw [show (2 * g + 1) % 2 = 1 by omega]
        rfl
      obtain ⟨_, q1⟩ := p0 g _ _
        (Array.getElem?_eq_getElem (by rw [hG]; omega))
        (Array.getElem?_eq_getElem (by rw [hA]; omega))
      obtain ⟨ar, e⟩ := bat (2 * g + 1) _ q1
      rw [e]
      show some false = some ((2 * g + 1) % 2 == 0)
      rw [e2]
  · rw [Array.getElem?_eq_none (by rw [bs, hsz]; omega),
      List.getElem?_eq_none (by rw [List.length_range]; omega)]
    rfl

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {c : VerifiableInference.Desc.Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **In the goals' scope, at an opening: the flags are the closed list.** -/
theorem fvs_at_scope (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) : fvsAt Z = fvsFull := by
  obtain ⟨k4, kN, _⟩ := Meaning.scope_plans hS hR O.public
  rw [O.W] at k4 kN
  exact fvs_plain O.pub k4 kN

/-- In front of segment 2 g of the closed list just g segments leave a row. -/
theorem rowsBefore_full {g : ℕ} (hg : g ≤ 12) : rowsBefore fvsFull (2 * g) = g := by
  have h : ∀ g ∈ List.range 13, rowsBefore fvsFull (2 * g) = g := by decide +kernel
  exact h g (List.mem_range.2 (by omega))

/-- **In the goals' scope, at an opening, g < 12: in front of segment 2 g just g segments leave a
row.** -/
theorem rowsBefore_at (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12) :
    rowsBefore (fvsAt Z) (2 * g) = g := by
  rw [fvs_at_scope hS hR O]
  exact rowsBefore_full (by omega)

end OnBytes.Road.K4.Riders

#print axioms OnBytes.Road.K4.Riders.fvs_plain
#print axioms OnBytes.Road.K4.Riders.fvs_at_scope
#print axioms OnBytes.Road.K4.Riders.rowsBefore_full
#print axioms OnBytes.Road.K4.Riders.rowsBefore_at
