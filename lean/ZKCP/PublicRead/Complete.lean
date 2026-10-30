-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/PublicRead/Complete.lean: A SCHEME WHOSE LETTERS ARE READ OFF THE HASH FUNCTION: the measure's
side, and COMPLETENESS: the proofs of Spec.reading_law, Spec.measure_pub, Spec.complete_pub and
Spec.complete_pub_on (ZKCP/PublicRead/Spec.lean). Theorems with their proofs.

General theorems, over one hash function. This file states no goal of the release.

THE MEASURE's SIDE (measure_c). F d g is a quantity that hangs on a value d and on the hash function
g, but not on g's values at public strings. If its average over g is at most c d at each fixed d,
then at the d that a public reading gets from g itself its average is at most the average of c over
the reading's values. One public string at a time: the average over g is the average over the value
r at the string of the average over g with r laid in there (Rom.lintegral_U_resample,
Rom/Measure.lean); what follows in the reading never asks the string again, and F does not see it.
It follows the pattern of pub_lift (Johnson/TypedOracleCompiler/RecCompile/PublicLift.lean). It is no general form
of that lemma: there the makers may ask public strings, so the quantity does hang on g at these.

COMPLETENESS. Under a fixed g the committer and the verifier of the glued scheme read one value
(commit_at, verify_at), so the glued experiment under g is the experiment at that value
(completenessExp_at). The experiment at d asks no public string (asks_completenessExp), so it does
not see g there. Then the measure's side.

Main names (namespace ZKCP.PublicRead).
  det_set, measurable_det   a reading that never asks a string does not see the value there; a
                quantity at the reading's value is measurable.
  measure_c     the measure's side, with a bound that may hang on d.
  law_c, reading_law   the average of a quantity that hangs on the reading's value alone; THE LAW OF
                THE READING: the draw with fresh answers has the law of the real reading's value.
  measure_pub   THE MEASURE's SIDE.
  verifyAll_at, completenessExp_at, asks_completenessExp   the glued experiment.
  complete_pub_on, complete_pub   THE THEOREMS ON COMPLETENESS.

Limits. Those of the head of ZKCP/PublicRead/Spec.lean: the public strings are fixed before the hash
function is drawn; the premises are asked at every d of the type, or of Dok; no member is shown.
Terms: lean/GLOSSARY.md.

-/
import ZKCP.PublicRead.Spec

set_option autoImplicit false

noncomputable section

open scoped ENNReal
open MeasureTheory

namespace ZKCP.PublicRead
open Rom Prob
open TypedOracleCompiler.Compile.Batch.Cms (NoRepeat runEager_set)

variable {lam : ℕ} {I X W PP IVK ISK Pf D : Type}

/-! ## The measure's side -/

/-- A reading that never asks a string does not see the value there. -/
theorem det_set {α : Type} (s : List Bool) (r : Fin lam → Bool) (g : Fam (rom lam)) :
    ∀ c : Rom.OComp (rom lam) α, (c.AsksIn fun _ s' => s' ≠ s) →
      c.det (g.set () s r) = c.det g := by
  intro c
  induction c with
  | pure a => intro _; rfl
  | sample n k ih => intro h; exact ih 0 (h 0)
  | query o q k ih =>
    intro h
    cases o
    show (k ((g.set () s r) () q)).det (g.set () s r) = (k (g () q)).det g
    rw [Fam.set_of_ne_point g () h.1 r]
    exact ih _ (h.2 _)

/-- A quantity at the reading's value is measurable. -/
theorem measurable_det (F : D → Fam (rom lam) → ℝ≥0∞) (hF : ∀ d, Measurable (F d)) :
    ∀ Pub : Rom.OComp (rom lam) D, Measurable fun g => F (Pub.det g) g := by
  intro Pub
  induction Pub with
  | pure d => exact hF d
  | sample n k ih => exact ih 0
  | query o q k ih => exact Rom.measurable_eval_dep o q (F := fun r g => F ((k r).det g) g) ih

/-- **The measure's side**, with a bound that may hang on d. -/
theorem measure_c (Pt : List Bool → Prop) (F : D → Fam (rom lam) → ℝ≥0∞) (c : D → ℝ≥0∞)
    (hF : ∀ d, Measurable (F d)) (hinv : ∀ d g s r, Pt s → F d (g.set () s r) = F d g)
    (hB : ∀ d, ∫⁻ g, F d g ∂(Rom.U (rom lam)) ≤ c d) :
    ∀ (Pub : Rom.OComp (rom lam) D) (l : Path lam), Pub.NoCoin →
      (Pub.AsksIn fun _ s => Pt s) → NoRepeat Pub →
      ∫⁻ g, F (Pub.det g) g ∂(Rom.U (rom lam)) ≤ Prob.expect (runPub Pub l) fun p => c p.1 := by
  intro Pub
  induction Pub with
  | pure d =>
    intro l _ _ _
    show _ ≤ Prob.expect (PMF.pure (d, l)) fun p => c p.1
    rw [Prob.expect_pure]
    exact hB d
  | sample n k _ => exact fun _ hc => hc.elim
  | query o s k ih =>
    intro l hc hp hr
    cases o
    rw [Rom.lintegral_U_resample () s (measurable_det F hF (.query () s k))]
    show _ ≤ Prob.expect ((unif (Fin lam → Bool)).bind fun r =>
      runPub (k r) (l ++ [((show List Bool from s), r)]))
      fun p => c p.1
    rw [Prob.expect_bind]
    refine Prob.expect_mono _ fun r => ?_
    refine le_trans (le_of_eq (lintegral_congr fun g => ?_))
      (ih r (l ++ [((show List Bool from s), (show Fin lam → Bool from r))]) (hc r) (hp.2 r)
        (hr r).2)
    show F ((k ((g.set () s r) () s)).det (g.set () s r)) (g.set () s r) = F ((k r).det g) g
    rw [Fam.set_self, det_set s r g (k r) (hr r).1, hinv _ g s r hp.1]

/-- The average of a quantity that hangs on the reading's value alone. -/
theorem law_c (c : D → ℝ≥0∞) : ∀ (Pub : Rom.OComp (rom lam) D) (l : Path lam), Pub.NoCoin →
    NoRepeat Pub →
    ∫⁻ g, c (Pub.det g) ∂(Rom.U (rom lam)) = Prob.expect (runPub Pub l) fun p => c p.1 := by
  intro Pub
  induction Pub with
  | pure d =>
    intro l _ _
    show ∫⁻ _, c d ∂(Rom.U (rom lam)) = Prob.expect (PMF.pure (d, l)) fun p => c p.1
    rw [Prob.expect_pure]
    simp
  | sample n k _ => exact fun _ hc => hc.elim
  | query o s k ih =>
    intro l hc hr
    cases o
    rw [Rom.lintegral_U_resample () s
      (measurable_det (fun d _ => c d) (fun _ => measurable_const) (.query () s k))]
    show _ = Prob.expect ((unif (Fin lam → Bool)).bind fun r =>
      runPub (k r) (l ++ [((show List Bool from s), r)])) fun p => c p.1
    rw [Prob.expect_bind]
    refine congrArg _ (funext fun r => ?_)
    refine Eq.trans (lintegral_congr fun g => ?_)
      (ih r (l ++ [((show List Bool from s), (show Fin lam → Bool from r))]) (hc r) (hr r).2)
    show c ((k ((g.set () s r) () s)).det (g.set () s r)) = c ((k r).det g)
    rw [Fam.set_self, det_set s r g (k r) (hr r).1]

/-- **The simulator's own draw of d has the law of the real d.** -/
theorem reading_law : Spec.reading_law := by
  intro lam D Pub hc hr E
  have h := law_c (fun d => pr (PMF.pure d) E) Pub [] hc hr
  have e1 : Rom.Pr Pub (fun _ => E) = ∫⁻ g, pr (PMF.pure (Pub.det g)) E ∂(Rom.U (rom lam)) := by
    unfold Rom.Pr Rom.PrCoins
    exact lintegral_congr fun g => by rw [hc.runEager g]
  have e2 : pr (runPub Pub []) {p | p.1 ∈ E} =
      Prob.expect (runPub Pub []) fun p => pr (PMF.pure p.1) E := by
    have : pr ((runPub Pub []).map Prod.fst) E = pr (runPub Pub []) {p | p.1 ∈ E} := pr_map _ _ _
    rw [← this]
    exact pr_bind _ _ _
  rw [e1, e2]
  exact h

/-- **The measure's side.** -/
theorem measure_pub : Spec.measure_pub := by
  intro lam D Pt F B hF hinv hB Pub hc hp hr
  refine le_trans (measure_c Pt F (fun _ => B) hF hinv hB Pub [] hc hp hr) ?_
  rw [Prob.expect_const]

/-! ## The glued experiment -/

/-- Under a fixed hash function the verifier's checks of a batch are those at the one value. -/
theorem verifyAll_at {Pub : Rom.OComp (rom lam) D} (hc : Pub.NoCoin)
    (A : D → Gen.Arg (rom lam) I X W IVK ISK Pf) (ivk : IVK) (g : Fam (rom lam)) :
    ∀ l : List (X × Pf), (Gen.verifyAll (glueArg Pub A) ivk l).runEager g =
      (Gen.verifyAll (A (Pub.det g)) ivk l).runEager g
  | [] => rfl
  | (x, π) :: rest => by
    show (((glueArg Pub A).V ivk x π).bind fun c =>
        (Gen.verifyAll (glueArg Pub A) ivk rest).bind fun cs =>
          Rom.OComp.pure (c && cs)).runEager g =
      (((A (Pub.det g)).V ivk x π).bind fun c =>
        (Gen.verifyAll (A (Pub.det g)) ivk rest).bind fun cs => Rom.OComp.pure (c && cs)).runEager g
    simp only [Rom.OComp.runEager_bind, verify_at hc A ivk x π g, verifyAll_at hc A ivk g rest]

/-- **Under a fixed hash function the glued experiment is the experiment at the one value.** -/
theorem completenessExp_at {Pub : Rom.OComp (rom lam) D} (hc : Pub.NoCoin)
    (A : D → Gen.Arg (rom lam) I X W IVK ISK Pf) (i : I) (b : List (X × W)) (g : Fam (rom lam)) :
    (Gen.completenessExp (glueArg Pub A) i b).runEager g =
      (Gen.completenessExp (A (Pub.det g)) i b).runEager g := by
  show (((glueArg Pub A).C i).bind fun key => ((glueArg Pub A).P key.2 b).bind fun πs =>
      Gen.verifyAll (glueArg Pub A) key.1 ((b.map Prod.fst).zip πs.val)).runEager g =
    (((A (Pub.det g)).C i).bind fun key => ((A (Pub.det g)).P key.2 b).bind fun πs =>
      Gen.verifyAll (A (Pub.det g)) key.1 ((b.map Prod.fst).zip πs.val)).runEager g
  rw [Rom.OComp.runEager_bind, Rom.OComp.runEager_bind, commit_at hc A i g, PMF.bind_map]
  refine congrArg _ (funext fun key => ?_)
  show (((A (Pub.det g)).P key.2 b).bind fun πs =>
      Gen.verifyAll (glueArg Pub A) key.1 ((b.map Prod.fst).zip πs.val)).runEager g = _
  rw [Rom.OComp.runEager_bind, Rom.OComp.runEager_bind]
  exact congrArg _ (funext fun πs => verifyAll_at hc A key.1 g _)

/-- The experiment of a scheme whose three algorithms ask strings with P alone asks such alone. -/
theorem asks_completenessExp (P : (o : (rom lam).ι) → (rom lam).Dom o → Prop)
    (A : Gen.Arg (rom lam) I X W IVK ISK Pf) (hC : ∀ i, (A.C i).AsksIn P)
    (hP : ∀ isk b, (A.P isk b).AsksIn P) (hV : ∀ k x π, (A.V k x π).AsksIn P) (i : I)
    (b : List (X × W)) : (Gen.completenessExp A i b).AsksIn P := by
  have hall : ∀ (ivk : IVK) (l : List (X × Pf)), (Gen.verifyAll A ivk l).AsksIn P := by
    intro ivk l
    induction l with
    | nil => trivial
    | cons a rest ih =>
      obtain ⟨x, π⟩ := a
      show ((A.V ivk x π).bind fun c => (Gen.verifyAll A ivk rest).bind fun cs =>
        Rom.OComp.pure (c && cs)).AsksIn P
      exact Rom.OComp.AsksIn.bind (fun c => Rom.OComp.AsksIn.bind
        (g := fun cs => Rom.OComp.pure (c && cs)) (fun _ => trivial) ih) (hV ivk x π)
  show ((A.C i).bind fun key => (A.P key.2 b).bind fun πs =>
    Gen.verifyAll A key.1 ((b.map Prod.fst).zip πs.val)).AsksIn P
  exact Rom.OComp.AsksIn.bind (fun key => Rom.OComp.AsksIn.bind (fun πs => hall _ _) (hP _ _))
    (hC i)

/-! ## Completeness -/

open Classical in
/-- **Completeness, where it is known at the d of Dok alone.** -/
theorem complete_pub_on : Spec.complete_pub_on := by
  intro lam I X W PP IVK ISK Pf D R A B α β Pt Dok Pub hc hp hr hC hP hV hA hβ' i b hb
  have hβ : pr (runPub Pub []) {p | ¬ Dok p.1} ≤ β :=
    le_of_eq_of_le (reading_law lam D Pub hc hr {d | ¬ Dok d}).symm hβ'
  -- the quantity: the experiment's error at d; 1 at a d that is set aside
  let F : D → Fam (rom lam) → ℝ≥0∞ := fun d g =>
    if Dok d then Rom.PrCoins g (Gen.completenessExp (A d) i b) {c | c = false} else 1
  have hF : ∀ d, Measurable (F d) := fun d => by
    by_cases hd : Dok d
    · simp only [F, if_pos hd]
      exact Rom.measurable_PrCoins _ _
    · simp only [F, if_neg hd]
      exact measurable_const
  have hinv : ∀ d g s r, Pt s → F d (g.set () s r) = F d g := fun d g s r hs => by
    by_cases hd : Dok d
    · simp only [F, if_pos hd]
      unfold Rom.PrCoins
      rw [runEager_set s r g _ (Rom.OComp.AsksIn.mono (fun _ s' h e => h (by rw [e]; exact hs))
        (asks_completenessExp (fun _ s' => ¬ Pt s') (A d) (hC d hd) (hP d hd) (hV d hd) i b))]
    · simp only [F, if_neg hd]
  have hB : ∀ d, ∫⁻ g, F d g ∂(Rom.U (rom lam)) ≤ if Dok d then α else 1 := fun d => by
    by_cases hd : Dok d
    · simp only [F, if_pos hd]
      exact hA d hd i b hb
    · simp only [F, if_neg hd]
      simp
  have h1 := measure_c Pt F (fun d => if Dok d then α else 1) hF hinv hB Pub [] hc hp hr
  refine le_trans (lintegral_mono fun g => ?_) (le_trans h1 ?_)
  · show Rom.PrCoins g (Gen.completenessExp (glueArg Pub A) i b) {c | c = false} ≤ F (Pub.det g) g
    unfold Rom.PrCoins
    rw [completenessExp_at hc A i b g]
    by_cases hd : Dok (Pub.det g)
    · simp only [F, if_pos hd]
      exact le_refl _
    · simp only [F, if_neg hd]
      exact pr_le_one _ _
  · have h2 : Prob.expect (runPub Pub []) (fun p => if Dok p.1 then α else 1) ≤
        Prob.expect (runPub Pub []) fun p => α +
          @ite ℝ≥0∞ (p ∈ {p : D × Path lam | ¬ Dok p.1}) (Classical.propDecidable _) 1 0 := by
      refine Prob.expect_mono _ fun p => ?_
      by_cases hd : Dok p.1
      · rw [if_pos hd]
        exact le_self_add
      · rw [if_neg hd, if_pos (show p ∈ {p : D × Path lam | ¬ Dok p.1} from hd)]
        exact le_add_self
    refine le_trans h2 ?_
    rw [Prob.expect_add, Prob.expect_const, ← Prob.pr_eq_expect]
    exact add_le_add le_rfl hβ

/-- **Completeness passes to the glued scheme, at the same error.** -/
theorem complete_pub : Spec.complete_pub := by
  intro lam I X W PP IVK ISK Pf D R A B α Pt Pub hc hp hr hC hP hV hA
  have h := complete_pub_on lam I X W PP IVK ISK Pf D R A B α 0 Pt (fun _ => True) Pub hc hp hr
    (fun d _ => hC d) (fun d _ => hP d) (fun d _ => hV d) (fun d _ => hA d)
    (le_of_eq (by
      rw [reading_law lam D Pub hc hr]
      exact pr_eq_zero_of_forall_not_mem _ fun _ _ h => h trivial))
  rwa [add_zero] at h

end ZKCP.PublicRead

#print axioms ZKCP.PublicRead.reading_law
#print axioms ZKCP.PublicRead.measure_pub
#print axioms ZKCP.PublicRead.complete_pub_on
#print axioms ZKCP.PublicRead.complete_pub
