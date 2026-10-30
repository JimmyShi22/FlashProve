-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/SecondIff.lean: THE SMALLNESS TEST: THE KIND's SECOND SHARE OF THE FALL (`k8Second`,
Johnson/Desc/ProofFile/Honest/K8/Share.lean) IS SILENT JUST WHERE `SecondEqs` AND `SecondRest` HOLD
(Johnson/Desc/K8/Honest/SecondParts.lean): NONE OF THE TWO TESTS' CONJUNCTS IS LEFT OUT AND NONE
ADDED; AND WHERE IT SPEAKS. A definition and lemmas; NONE OF THE LIBRARY's GOALS. Nothing on
completeness, soundness or hiding.

  `K8Never nU tl F`   `K8Rest nU tl F` (Johnson/Desc/ProofFile/Honest/K8/TestsSplit.lean) and
      `SecondEqs tl F`: all of the verifier's three tests behind the adding that must never fail
  `two_none`   two tests in a row, each with its word, are silent just where both say yes
  **`second_iff`**   where the data have heard their lookup, hold the joining object and the wanted
      pieces: `k8Second tl F = none` just if both halves hold; `second_silent`: where one of the
      three lacks it is silent
  `secondEqs_slot`   `SecondEqs` does not read the kept slots
  **`k8Second_speaks`**   `second_speaks` (Johnson/Desc/K8/Honest/SecondNz.lean) at `k8Second tl F ≠
      none`
By: `piece_split`, `tie_split` · coefficientsP's text
(Johnson/Desc/First/TailClaims/Coefficients.lean).
Limits. This file proves `K8Never` and `SecondEqs` of no state. `K8Rest` reads the kept slots, which
are laid behind the batching's step: so `K8Never` is a sentence for the state behind that laying.
-/
import Johnson.Desc.ProofFile.Honest.K8.TestsSplit
import Johnson.Desc.K8.Honest.SecondNz

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open Fo (HasRow)
open OnBytes.Tie.Pv.Tail.Port (Powered)
open VerifiableInference.Desc.First.TailClaims (coefBody coefficientsP)
open VerifiableInference.Desc.First.K8.Honest
open ProofFile.Honest.K8 (k8Second K8Rest)

/-- **All of the verifier's three tests behind the adding that must never fail.** -/
def K8Never (nU : Array Nat) (tl : HTailF2) (F : Fork) : Prop := K8Rest nU tl F ∧ SecondEqs tl F

/-- Two tests in a row, each with its word: silent just where both say yes. -/
theorem two_none (a b : Bool) (x y : String) :
    (if !a then some x else if !b then some y else none) = none ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp

/-- **The kind's second share is silent just where both halves hold**: none left out, none added. -/
theorem second_iff {tl : HTailF2} {F : Fork} {g : Forest.Heard} {jo nbW : Nat} {W : List Want}
    (hg : tl.heard = some g) (hj : tl.joinObj9 = some jo) (hw : tl.wants = some (nbW, W)) :
    k8Second tl F = none ↔ SecondEqs tl F ∧ SecondRest tl F := by
  have hc : coefficientsP tl F = .ok (coefBody tl g F) := by
    unfold coefficientsP
    rw [hg]
  unfold k8Second
  rw [hc, hg, hj, hw]
  dsimp only
  rw [two_none, List.all_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨a1, a2⟩
    refine ⟨fun g' jo' nbW' W' e1 e2 e3 => ?_, fun g' jo' nbW' W' e1 e2 e3 => ?_⟩ <;>
      (obtain rfl : g = g' := Option.some.inj (hg.symm.trans e1)
       obtain rfl : jo = jo' := Option.some.inj (hj.symm.trans e2)
       obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hw.symm.trans e3)))
    · exact ⟨fun w hw' => ((piece_split _ _ _ _ _).1 (a1 w hw')).1,
        fun mu hmu => ((tie_split _ _ _ _).1 (a2 mu (List.mem_range.2 hmu))).1⟩
    · exact ⟨fun w hw' => ((piece_split _ _ _ _ _).1 (a1 w hw')).2,
        fun mu hmu => ((tie_split _ _ _ _).1 (a2 mu (List.mem_range.2 hmu))).2⟩
  · rintro ⟨hE, hR⟩
    obtain ⟨p1, t1⟩ := hE g jo nbW W hg hj hw
    obtain ⟨p2, t2⟩ := hR g jo nbW W hg hj hw
    exact ⟨fun w hw' => (piece_split _ _ _ _ _).2 ⟨p1 w hw', p2 w hw'⟩,
      fun mu hmu =>
        (tie_split _ _ _ _).2 ⟨t1 mu (List.mem_range.1 hmu), t2 mu (List.mem_range.1 hmu)⟩⟩

/-- Where one of the three values lacks, it is silent. -/
theorem second_silent {tl : HTailF2} {F : Fork}
    (h : tl.heard = none ∨ tl.joinObj9 = none ∨ tl.wants = none) : k8Second tl F = none := by
  unfold k8Second
  rcases h with h | h | h <;> rw [h] <;> split <;> first | rfl | simp_all

/-- `SecondEqs` does not read the kept slots. -/
theorem secondEqs_slot (tl : HTailF2) (F : Fork) (x : Array E) :
    SecondEqs { tl with lsTail := x } F ↔ SecondEqs tl F := Iff.rfl

/-- **Where the kind's second share speaks: the batching element is 0, or two of its powers
meet.** -/
theorem k8Second_speaks (tl : HTailF2) (F : Fork) {g : Forest.Heard} {jo nbW : Nat}
    {W : List Want} (hg : tl.heard = some g) (hj : tl.joinObj9 = some jo)
    (hw : tl.wants = some (nbW, W)) (hE : SecondEqs tl F) (hL : PieceLive tl g W)
    (hP : Powered tl F.theta) (hsz : tl.NM ≤ tl.shp.size)
    (hr : ∀ mu < tl.NM, HasRow F (tl.gtTree.getD mu 0) 0)
    (hinj : ∀ a, a < tl.NM → ∀ b, b < tl.NM → tl.gtTree.getD a 0 = tl.gtTree.getD b 0 → a = b)
    (hno : k8Second tl F ≠ none) :
    Reading.gl.val F.theta = 0 ∨ ∃ mu, mu < tl.NM ∧ ∃ i j, i < j ∧
      j < (tl.shp.getD mu {}).mS ∧
      (Reading.gl.val F.theta ^ tl.stepF) ^ i = (Reading.gl.val F.theta ^ tl.stepF) ^ j :=
  second_speaks tl F hg hj hw hE hL hP hsz hr hinj fun hR =>
    hno ((second_iff hg hj hw).2 ⟨hE, hR⟩)

end P1K8

#print axioms P1K8.two_none
#print axioms P1K8.second_iff
#print axioms P1K8.second_silent
#print axioms P1K8.secondEqs_slot
#print axioms P1K8.k8Second_speaks
#print axioms P1K8.K8Never
