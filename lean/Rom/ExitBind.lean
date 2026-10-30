-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/ExitBind.lean: the step to one hash function, part 2: completeness and, under a condition on the
extractor, index binding (ZKCP/Gen.lean) carry over from the family of oracles to the hash function.

The step implements all oracles of a family by one hash function on bit strings, by domain
separation (Rom/Family.lean). Completeness carries over with the same error
(`completeness_overOne`). Index binding carries over with the same bound for an extractor E that
reads only entries at oracles whose answer is one hash block (`LocalTo`, Rom/Family.lean); the
extractor becomes `extractorOverOneHashFunction m E` (`binding_overOne`).

Notation: `Gen.`: the namespace `ZKCP.Gen` (ZKCP/Gen.lean); `B : ℕ` (the docstring of `Gen.Arg`,
ZKCP/Gen.lean): the bound B on the length of a batch; `α : ℝ≥0∞`, `ε : ℕ → ℕ → ℝ≥0∞`: the last
arguments of `Gen.HasCompletenessError` and `Gen.HasIndexBindingWith` (there); ε is taken at
`tC tP`, with `Ct.QueryBound tC` and `(Pt st).QueryBound tP`; `Ei`, `Ew`: the two fields of
`Gen.Extractor` (there).
-/
import Rom.ExitDown
noncomputable section -- Lean tags what it cannot compile

open MeasureTheory
open scoped ENNReal

namespace Rom

open ZKCP

variable {S : OSpec} {lam : ℕ} {α β : Type}

theorem overOne_bind (m : OracleCoding S lam) (c : OComp S α) (g : α → OComp S β) :
    (c.bind g).overOne m = (c.overOne m).bind fun a => (g a).overOne m := by
  induction c with
  | pure a => rfl
  | sample n k ih => simp only [OComp.bind, OComp.overOne, ih]
  | query o q k ih => simp only [OComp.bind, OComp.overOne, ih, OComp.bind_assoc]

variable {I X W PP IVK ISK Pf : Type}

/-! ### Completeness -/

theorem verifyAll_overOne (m : OracleCoding S lam) (A : Gen.Arg S I X W IVK ISK Pf)
    (ivk : IVK) (l : List (X × Pf)) :
    Gen.verifyAll (schemeOverOneHashFunction m A) ivk l = (Gen.verifyAll A ivk l).overOne m := by
  induction l with
  | nil => rfl
  | cons s rest ih =>
    have e1 : Gen.verifyAll (schemeOverOneHashFunction m A) ivk (s :: rest) = ((A.V ivk s.1 s.2).overOne m).bind fun c =>
        (Gen.verifyAll (schemeOverOneHashFunction m A) ivk rest).bind fun cs => .pure (c && cs) := rfl
    have e2 : Gen.verifyAll A ivk (s :: rest) = (A.V ivk s.1 s.2).bind fun c =>
        (Gen.verifyAll A ivk rest).bind fun cs => .pure (c && cs) := rfl
    rw [e1, e2, ih]
    simp only [overOne_bind]
    rfl

theorem completenessExp_overOne
    (m : OracleCoding S lam) (A : Gen.Arg S I X W IVK ISK Pf) (i : I) (b : List (X × W)) :
    Gen.completenessExp (schemeOverOneHashFunction m A) i b = (Gen.completenessExp A i b).overOne m := by
  have e1 : Gen.completenessExp (schemeOverOneHashFunction m A) i b = ((A.C i).overOne m).bind fun key =>
      ((A.P key.2 b).overOne m).bind fun πs =>
        Gen.verifyAll (schemeOverOneHashFunction m A) key.1 ((b.map Prod.fst).zip πs.val) := rfl
  have e2 : Gen.completenessExp A i b = (A.C i).bind fun key =>
      (A.P key.2 b).bind fun πs => Gen.verifyAll A key.1 ((b.map Prod.fst).zip πs.val) := rfl
  rw [e1, e2]
  simp only [overOne_bind, verifyAll_overOne]

theorem completeness_overOne (m : OracleCoding S lam) (R : Gen.RelPair I X W PP)
    (A : Gen.Arg S I X W IVK ISK Pf) (B : ℕ) (α : ℝ≥0∞) (h : Gen.HasCompletenessError R A B α) :
    Gen.HasCompletenessError R (schemeOverOneHashFunction m A) B α := by
  intro i b hb
  rw [completenessExp_overOne, Pr_overOne]
  exact h i b hb

/-! ### Index binding -/

/-- The extractor over the hash function: it reads the entries at one-block oracles off the trace.
-/
def extractorOverOneHashFunction (m : OracleCoding S lam) (E : Gen.Extractor S I X W IVK Pf) :
    Gen.Extractor (rom lam) I X W IVK Pf where
  Ei ivk tr := E.Ei ivk (singleTr m tr)
  Ew ivk trC x π trP := E.Ew ivk (singleTr m trC) x π (singleTr m trP)

theorem bind_retr (g : Fam S) (c : OComp S α) (K : α × Trace S → PMF β) :
    (c.withTrace.runEager g).bind K =
      (c.withTrace.runEager g).bind fun out => K (out.1, retr g out.2) := by
  conv_lhs => rw [withTrace_retr g c]
  rw [PMF.bind_map]
  rfl

theorem bindingExp_glue (m : OracleCoding S lam) (A : Gen.Arg S I X W IVK ISK Pf)
    (E : Gen.Extractor S I X W IVK Pf) (hE : LocalTo E m) {St : Type}
    (Ct : OComp (rom lam) (IVK × St)) (Pt : St → OComp (rom lam) (X × Pf)) (F : Fam S) :
    (Gen.bindingExp (schemeOverOneHashFunction m A) (extractorOverOneHashFunction m E) Ct Pt).runEager (glue m F) =
      (Gen.bindingExp A E (down m Ct) fun st => down m (Pt st)).runEager F := by
  have e1 : Gen.bindingExp (schemeOverOneHashFunction m A) (extractorOverOneHashFunction m E) Ct Pt = Ct.withTrace.bind fun o1 =>
      (Pt o1.1.2).withTrace.bind fun o2 => ((A.V o1.1.1 o2.1.1 o2.1.2).overOne m).bind fun c =>
        .pure ⟨c, E.Ei o1.1.1 (singleTr m o1.2), o2.1.1,
          E.Ew o1.1.1 (singleTr m o1.2) o2.1.1 o2.1.2 (singleTr m o2.2)⟩ := rfl
  have e2 : Gen.bindingExp A E (down m Ct) (fun st => down m (Pt st)) = (down m Ct).withTrace.bind fun o1 =>
      (down m (Pt o1.1.2)).withTrace.bind fun o2 => (A.V o1.1.1 o2.1.1 o2.1.2).bind fun c =>
        .pure ⟨c, E.Ei o1.1.1 o1.2, o2.1.1, E.Ew o1.1.1 o1.2 o2.1.1 o2.1.2 o2.2⟩ := rfl
  rw [e1, e2]
  simp only [OComp.runEager_bind, withTrace_down, PMF.bind_map, runEager_overOne,
    readBlocks_glue, Function.comp_def]
  rw [bind_retr]
  congr 1
  funext o1
  rw [bind_retr]
  congr 1
  funext o2
  congr 1
  funext c
  simp only [OComp.runEager]
  rw [hE.1 o1.1.1 (upTr m F o1.2), hE.2 o1.1.1 (upTr m F o1.2) o2.1.1 o2.1.2 (upTr m F o2.2),
    single_upTr, single_upTr]

theorem binding_overOne (m : OracleCoding S lam) (R : Gen.RelPair I X W PP)
    (A : Gen.Arg S I X W IVK ISK Pf) (E : Gen.Extractor S I X W IVK Pf) (hE : LocalTo E m)
    (ε : ℕ → ℕ → ℝ≥0∞) (h : Gen.HasIndexBindingWith R A E ε) :
    Gen.HasIndexBindingWith R (schemeOverOneHashFunction m A) (extractorOverOneHashFunction m E) ε := by
  intro tC tP St Ct Pt hC hP
  refine le_trans (le_of_eq ?_)
    (h tC tP St (down m Ct) (fun st => down m (Pt st)) (queryBound_down m Ct tC hC)
      fun st => queryBound_down m (Pt st) tP (hP st))
  unfold Pr
  rw [lintegral_glue m
      (fun g => PrCoins g (Gen.bindingExp (schemeOverOneHashFunction m A) (extractorOverOneHashFunction m E) Ct Pt) (Gen.bindingBad R))]
  · simp only [PrCoins, bindingExp_glue m A E hE]
  · simp only [PrCoins, bindingExp_glue m A E hE]
    exact measurable_PrCoins _ _

end Rom
