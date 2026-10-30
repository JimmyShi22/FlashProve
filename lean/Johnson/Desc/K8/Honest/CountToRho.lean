-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/CountToRho.lean: FROM A COUNT OVER ONE ROUND's CHALLENGES TO THE LIBRARY's
MEASURE ON THE VERIFIER's MESSAGES OF THAT ONE ROUND (Iop.prRho, Iop/InteractiveOracleProof.lean, over Iop.Rho (uLT C
[d]), OnBytes/Maker/Trees.lean). Statements and proofs, on the library's definitions alone: no
block, no state of the chain, no prover. Lemmas; none of the library's goals.

C: a kit of verifier's messages (Run.PQ.CK: for each entry and kind a finite type of challenges, and
the map dr to what a view shows). d: one round's data. That round's message is a challenge of the
kit WITH THE BITS OF THE TEST OF WORK (Iop.GChal, Iop/Grind.lean); drawnT shows the challenge
without them.
  `gchal_fib`, `gchal_card`   over each challenge stand at most 2 ^ b messages; there are (the
      number of challenges) * 2 ^ b messages
  **`prRho_one_le`**   if at most n challenges c of the kit are such that Q holds of what c shows,
      the measure of "the round shows one drawn value, and Q holds of it" is at most n / (the number
      of challenges): the bits of the test of work cancel
  **`prRho_test_le`**   the same for a test with code T on the list that the round shows: the
      measure of "T says yes"
  **`prRho_elem_le`**   the same from a count of field elements: each challenge shows one field
      element el c in reduced words, at most w challenges to one element; Q of what is shown gives
      Q' of the element; at most n elements meet Q': at most n * w / (the number of challenges)
By: prRho_head_le (Iop/ViewKit.lean) · GChal.equiv, GChal.mk_old_test (Iop/GrindProofs.lean) ·
Prob.cnt_comp_le (Prob/Bias.lean).
Limits. One round. The uniform law on that round's messages: that the messages of any run have it is
not said.
Terms: lean/GLOSSARY.md.
-/
import Iop.ViewKit
import Iop.GrindProofs
import OnBytes.Maker.Trees
import Prob.Bias
import Johnson.Desc.K8.Honest.ChiTyped

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes
open OnBytes.Maker (RDT uLT drawnT)
open _root_.Run.PQ (CK)
open Iop
open scoped ENNReal

/-- Over each challenge stand at most 2 ^ b messages. -/
theorem gchal_fib {C' : Type} [Fintype C'] (b : ℕ) (c₀ : C') :
    Prob.cnt (fun c : GChal b C' => GChal.old c = c₀) ≤ 2 ^ b := by
  have h := Nat.card_le_card_of_injective
    (fun x : {c : GChal b C' // GChal.old c = c₀} => GChal.test x.1) (fun x y hxy => by
      refine Subtype.ext ?_
      rw [← GChal.mk_old_test x.1, ← GChal.mk_old_test y.1, x.2, y.2]
      exact congrArg (GChal.mk b c₀) hxy)
  refine h.trans (le_of_eq ?_)
  rw [Nat.card_eq_fintype_card]
  simp

theorem gchal_card {C' : Type} [Fintype C'] (b : ℕ) :
    Nat.card (GChal b C') = Nat.card C' * 2 ^ b := by
  rw [Nat.card_congr (GChal.equiv b C'), Nat.card_prod]
  congr 1
  rw [Nat.card_eq_fintype_card]
  simp

/-- **From a count of challenges.** -/
theorem prRho_one_le (C : CK) (d : RDT) (Q : Fmt.Drawn → Prop) (n : ℕ)
    (h : Prob.cnt (fun c : C.Ch d.entry d.kind => Q (C.dr d.entry d.kind c)) ≤ n) :
    Iop.prRho {ρ : Iop.Rho (uLT C [d]) | ∃ dr, drawnT C [d] ρ = [dr] ∧ Q dr} ≤
      (n : ℝ≥0∞) / (Nat.card (C.Ch d.entry d.kind) : ℝ≥0∞) := by
  have hc : Prob.cnt (fun c : GChal d.entry.work (C.Ch d.entry d.kind) =>
      Q (C.dr d.entry d.kind (GChal.old c))) ≤ n * 2 ^ d.entry.work :=
    (Prob.cnt_comp_le (GChal.old (b := d.entry.work)) (gchal_fib d.entry.work)
      (fun c => Q (C.dr d.entry d.kind c))).trans (Nat.mul_le_mul_right _ h)
  have hh := Iop.prRho_head_le (TypedOracleCompiler.Run.PQ.roundS C d.toRD).up []
    (fun c => Q (C.dr d.entry d.kind (GChal.old (b := d.entry.work) c))) _ hc
  have hsub : Iop.prRho {ρ : Iop.Rho (uLT C [d]) | ∃ dr, drawnT C [d] ρ = [dr] ∧ Q dr} ≤
      Iop.prRho (s := (TypedOracleCompiler.Run.PQ.roundS C d.toRD).up :: [])
        {ρ | Q (C.dr d.entry d.kind (GChal.old (b := d.entry.work)
          (show (TypedOracleCompiler.Run.PQ.roundS C d.toRD).up.Chal × Iop.Rho [] from ρ).1))} := by
    refine Prob.pr_mono _ fun ρ hρ => ?_
    obtain ⟨dr, h1, h2⟩ := hρ
    obtain ⟨c, u⟩ := ρ
    have e : C.dr d.entry d.kind (GChal.old (b := d.entry.work) c) = dr :=
      List.head_eq_of_cons_eq h1
    show Q (C.dr d.entry d.kind (GChal.old (b := d.entry.work) c))
    rw [e]
    exact h2
  refine hsub.trans (hh.trans (le_of_eq ?_))
  have hcard : (Fintype.card (TypedOracleCompiler.Run.PQ.roundS C d.toRD).up.Chal : ℝ≥0∞) =
      (Nat.card (C.Ch d.entry d.kind) : ℝ≥0∞) * ((2 ^ d.entry.work : ℕ) : ℝ≥0∞) := by
    rw [← Nat.cast_mul, ← gchal_card, Nat.card_eq_fintype_card]
  rw [hcard, Nat.cast_mul]
  have h2 : ((2 ^ d.entry.work : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_ne_zero (by positivity)).ne'
  have h3 : ((2 ^ d.entry.work : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  exact ENNReal.mul_div_mul_right _ _ h2 h3

/-- **The same for a test with code on the list that the round shows**: the left side is the local
bound of a test at one round. -/
theorem prRho_test_le (C : CK) (d : RDT) (T : List Fmt.Drawn → Bool) (n : ℕ)
    (h : Prob.cnt (fun c : C.Ch d.entry d.kind => T [C.dr d.entry d.kind c] = true) ≤ n) :
    Iop.prRho {ρ : Iop.Rho (uLT C [d]) | T (drawnT C [d] ρ) = true} ≤
      (n : ℝ≥0∞) / (Nat.card (C.Ch d.entry d.kind) : ℝ≥0∞) := by
  refine (Prob.pr_mono _ fun ρ hρ => ?_).trans (prRho_one_le C d (fun dr => T [dr] = true) n h)
  obtain ⟨c, u⟩ := ρ
  exact ⟨C.dr d.entry d.kind (GChal.old (b := d.entry.work) c), rfl, hρ⟩

/-- **From a count of field elements.** -/
theorem prRho_elem_le (C : CK) (d : RDT) (el : C.Ch d.entry d.kind → Cb.Gl.E) (w : ℕ)
    (hw : ∀ y, Prob.cnt (fun c => el c = y) ≤ w)
    (hel : ∀ c, (C.dr d.entry d.kind c).elems = [Slice.ofE (el c)])
    (Q : Fmt.Drawn → Prop) (Q' : Cb.Gl.E → Prop)
    (hQ : ∀ dr x, Q dr → dr.elems = [Slice.ofE x] → Q' x) (n : ℕ) (hn : Prob.cnt Q' ≤ n) :
    Iop.prRho {ρ : Iop.Rho (uLT C [d]) | ∃ dr, drawnT C [d] ρ = [dr] ∧ Q dr} ≤
      ((n * w : ℕ) : ℝ≥0∞) / (Nat.card (C.Ch d.entry d.kind) : ℝ≥0∞) := by
  refine prRho_one_le C d Q (n * w) ?_
  exact (Prob.cnt_mono fun c hc => hQ _ (el c) hc (hel c)).trans
    ((Prob.cnt_comp_le el hw Q').trans (Nat.mul_le_mul_right _ hn))

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.gchal_fib
#print axioms VerifiableInference.Desc.First.K8.Honest.gchal_card
#print axioms VerifiableInference.Desc.First.K8.Honest.prRho_one_le
#print axioms VerifiableInference.Desc.First.K8.Honest.prRho_test_le
#print axioms VerifiableInference.Desc.First.K8.Honest.prRho_elem_le
