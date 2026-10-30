-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/CutBind.lean: the splitting step. Completeness and index binding (ZKCP/Gen.lean) carry over from
a family of oracles to the split family, with the same bounds. The file has the same structure as
Rom/ExitBind.lean.

The splitting step (`OCut`, Rom/SpecCut.lean) replaces each oracle by two oracles on the same
queries, one for each of two parts of its answer (an oracle marked `OCut.whole` is not split; its
second oracle is trivial); these form the split family `cutSpec S C`, and `cutFam C F` is the split
form of a family F of functions.

  `verifyAll_cutFam`, `completenessExp_cutFam`
                              For every family F the honest experiment over `cutFam C F` returns
                              what the experiment before the step returns under F (by `runCut`, for
                              each of the three algorithms under its own rule). A rule (`NeedCut`,
                              Rom/SpecCut.lean) says, after the first part of an answer, whether the
                              second part is queried.
  `bindingExp_cutFam`, `binding_cut`
                              The same for the experiment of index binding, where the adversary over
                              the split family is translated to the family S (`downCut`); index
                              binding carries over. Both are for the extractor `extCut C E`, if E
                              reads only entries at oracles that are not split (`WholeOnly`).

All of them assume `NeedOKCut`: committer, prover and verifier each meet the condition `ReadsCut`
(Rom/SpecCut.lean) under their rule.

Notation:
  `nC`, `nP`, `nV`: `NeedCut C` (Rom/SpecCut.lean): a rule for each algorithm (doc comment of
    `cutArg`)
  `B`: `ℕ`: the bound on the length of a batch (doc comment of `Gen.Arg`, ZKCP/Gen.lean)
  `α`: `ℝ≥0∞`: the last argument of `Gen.HasCompletenessError R A B α` (ZKCP/Gen.lean)
  `ε`: `ℕ → ℕ → ℝ≥0∞`: in `Gen.HasIndexBindingWith R A E ε` (ZKCP/Gen.lean) it stands as `ε tC tP`,
    with `Ct.QueryBound tC` and `∀ st, (Pt st).QueryBound tP`; `Ct : OComp S (IVK × St)`,
    `Pt : St → OComp S (X × Pf)`
  `extCut C E`: `Gen.Extractor (cutSpec S C) I X W IVK Pf` (Rom/SpecCut.lean)
  `wholeTr C tr` (Rom/SpecCut.lean): the entries at oracles that are not split, as entries of the
    first family
  `upTrCut C F tr` (Rom/CutDown.lean): the trace over the family that belongs to a trace over the
    split family, when the family is F
  `retr g tr` (Rom/ExitDown.lean): the answers of a trace, replaced by the true answers of g
  `c.runEager F` (Rom/OComp.lean): the oracles fixed: the law of the output over the coins only;
    `F`: `Fam S` (Rom/OSpec.lean): a whole family of functions

Limits: what the head of Rom/SpecCut.lean lists as not said is not said here either. Of that head's
limits: nothing is said about any scheme, and nothing about one hash function; the bounds stay the
same, but the numbers of queries now count queries to the split family, and a query of an honest
algorithm whose second part is asked is now two queries.
-/
import Rom.CutDown
import Rom.ExitBind

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Rom
open ZKCP

variable {S : OSpec} (C : ∀ o, OCut (S.Rng o)) {α β : Type} {I X W PP IVK ISK Pf : Type}

/-! ### Completeness -/

theorem verifyAll_cutFam {A : Gen.Arg S I X W IVK ISK Pf} {nC nP nV : NeedCut C}
    (h : NeedOKCut C A nC nP nV) (F : Fam S) (ivk : IVK) (l : List (X × Pf)) :
    (Gen.verifyAll (cutArg C nC nP nV A) ivk l).runEager (cutFam C F) =
      (Gen.verifyAll A ivk l).runEager F := by
  induction l with
  | nil => rfl
  | cons s rest ih =>
    have e1 : Gen.verifyAll (cutArg C nC nP nV A) ivk (s :: rest) = ((A.V ivk s.1 s.2).cut C nV).bind fun c =>
        (Gen.verifyAll (cutArg C nC nP nV A) ivk rest).bind fun cs => .pure (c && cs) := rfl
    have e2 : Gen.verifyAll A ivk (s :: rest) =
        (A.V ivk s.1 s.2).bind fun c => (Gen.verifyAll A ivk rest).bind fun cs => .pure (c && cs) :=
      rfl
    rw [e1, e2]
    simp only [OComp.runEager_bind, runCut S C _ nV _ (h.ver ivk s.1 s.2) F, ih]
    rfl

theorem completenessExp_cutFam {A : Gen.Arg S I X W IVK ISK Pf} {nC nP nV : NeedCut C}
    (h : NeedOKCut C A nC nP nV) (F : Fam S) (i : I) (b : List (X × W)) :
    (Gen.completenessExp (cutArg C nC nP nV A) i b).runEager (cutFam C F) =
      (Gen.completenessExp A i b).runEager F := by
  have e1 : Gen.completenessExp (cutArg C nC nP nV A) i b = ((A.C i).cut C nC).bind fun key =>
      ((A.P key.2 b).cut C nP).bind fun πs =>
        Gen.verifyAll (cutArg C nC nP nV A) key.1 ((b.map Prod.fst).zip πs.val) := rfl
  have e2 : Gen.completenessExp A i b =
      (A.C i).bind fun key =>
        (A.P key.2 b).bind fun πs => Gen.verifyAll A key.1 ((b.map Prod.fst).zip πs.val) := rfl
  rw [e1, e2]
  simp only [OComp.runEager_bind, runCut S C _ nC _ (h.com i) F,
    runCut S C _ nP _ (h.prv _ b) F, verifyAll_cutFam C h F]

theorem completeness_cut (R : Gen.RelPair I X W PP) {A : Gen.Arg S I X W IVK ISK Pf}
    {nC nP nV : NeedCut C} (h : NeedOKCut C A nC nP nV) (B : ℕ) (α : ℝ≥0∞)
    (hA : Gen.HasCompletenessError R A B α) :
    Gen.HasCompletenessError R (cutArg C nC nP nV A) B α := by
  intro i b hb
  refine le_trans (le_of_eq ?_) (hA i b hb)
  unfold Pr
  rw [lintegral_cutFam C
      (fun g => PrCoins g (Gen.completenessExp (cutArg C nC nP nV A) i b) {c | c = false})]
  · simp only [PrCoins, completenessExp_cutFam C h]
  · simp only [PrCoins, completenessExp_cutFam C h]
    exact measurable_PrCoins _ _

/-! ### Index binding -/

theorem bindingExp_cutFam {A : Gen.Arg S I X W IVK ISK Pf} {nC nP nV : NeedCut C}
    (h : NeedOKCut C A nC nP nV) (E : Gen.Extractor S I X W IVK Pf) (hE : WholeOnly C E) {St : Type}
    (Ct : OComp (cutSpec S C) (IVK × St)) (Pt : St → OComp (cutSpec S C) (X × Pf)) (F : Fam S) :
    (Gen.bindingExp (cutArg C nC nP nV A) (extCut C E) Ct Pt).runEager (cutFam C F) =
      (Gen.bindingExp A E (downCut C Ct) fun st => downCut C (Pt st)).runEager F := by
  have e1 : Gen.bindingExp (cutArg C nC nP nV A) (extCut C E) Ct Pt = Ct.withTrace.bind fun o1 =>
      (Pt o1.1.2).withTrace.bind fun o2 => ((A.V o1.1.1 o2.1.1 o2.1.2).cut C nV).bind fun c =>
        .pure ⟨c, E.Ei o1.1.1 (wholeTr C o1.2), o2.1.1,
            E.Ew o1.1.1 (wholeTr C o1.2) o2.1.1 o2.1.2 (wholeTr C o2.2)⟩ := rfl
  have e2 : Gen.bindingExp A E (downCut C Ct) (fun st => downCut C (Pt st)) = (downCut C Ct).withTrace.bind fun o1 =>
      (downCut C (Pt o1.1.2)).withTrace.bind fun o2 => (A.V o1.1.1 o2.1.1 o2.1.2).bind fun c =>
        .pure ⟨c, E.Ei o1.1.1 o1.2, o2.1.1, E.Ew o1.1.1 o1.2 o2.1.1 o2.1.2 o2.2⟩ := rfl
  rw [e1, e2]
  simp only [OComp.runEager_bind, withTrace_downCut, PMF.bind_map,
    runCut S C _ nV _ (h.ver _ _ _) F, Function.comp_def]
  rw [bind_retr]
  congr 1
  funext o1
  rw [bind_retr]
  congr 1
  funext o2
  congr 1
  funext c
  simp only [OComp.runEager]
  rw [hE.1 o1.1.1 (upTrCut C F o1.2),
    hE.2 o1.1.1 (upTrCut C F o1.2) o2.1.1 o2.1.2 (upTrCut C F o2.2),
    wholeOf_upTrCut, wholeOf_upTrCut]

theorem binding_cut (R : Gen.RelPair I X W PP) {A : Gen.Arg S I X W IVK ISK Pf}
    {nC nP nV : NeedCut C} (h : NeedOKCut C A nC nP nV) (E : Gen.Extractor S I X W IVK Pf)
    (hE : WholeOnly C E) (ε : ℕ → ℕ → ℝ≥0∞) (hA : Gen.HasIndexBindingWith R A E ε) :
    Gen.HasIndexBindingWith R (cutArg C nC nP nV A) (extCut C E) ε := by
  intro tC tP St Ct Pt hC hP
  refine le_trans (le_of_eq ?_)
    (hA tC tP St (downCut C Ct) (fun st => downCut C (Pt st)) (queryBound_downCut C Ct tC hC)
      fun st => queryBound_downCut C (Pt st) tP (hP st))
  unfold Pr
  rw [lintegral_cutFam C (fun g =>
      PrCoins g (Gen.bindingExp (cutArg C nC nP nV A) (extCut C E) Ct Pt) (Gen.bindingBad R))]
  · simp only [PrCoins, bindingExp_cutFam C h E hE]
  · simp only [PrCoins, bindingExp_cutFam C h E hE]
    exact measurable_PrCoins _ _

end Rom
