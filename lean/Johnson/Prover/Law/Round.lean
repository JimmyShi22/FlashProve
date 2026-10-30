-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Law/Round.lean: A FIAT-SHAMIR QUERY OF THE COMPILED PROVER, WITH A TEST OR WITHOUT,
UNDER LAZILY SAMPLED ORACLES, WITH WHAT FOLLOWS IT: the probability of an event of what follows is
at most the mean, over a UNIFORM verifier message with its test bits set to 0, of a bound on what
follows, plus the probability that the search runs out, (1 - 2^-b)^(cap + 1).

Main names.
  chalA, lensOf, ok_false_iff, set_of_ok   a uniform answer gives a uniform verifier message; the
    test's record is a lens; a verifier message that passes is itself with its test bits set to 0.
  qFail_eq, ok_ind one uniform answer fails the test with probability 1 - 2^-b; the verifier message
    with its test bits set to 0 is independent of the test.
  mean_le   the mean over "sample until the test is passed" (Prob.retry).
  zeroOf, fs_le   THE STATEMENT.
  PrFrom_bind_le, PrFrom_bind_pure   two steps for the walk along a program.

Earlier lemmas: ok_share, ok_indep (Compile/Batch/LoopLaw.lean), over the first form's records. Here
the second form's record (OnBytes/TypedOracleCompiler/Iop/BatchWire.lean), through the same general lemmas on a lens
(Prob/LensLaw.lean) and on sampling again (Prob/Retry.lean).

Limits. One query. The bound on what follows may hang on the verifier message alone.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Law.Search
import Prob.LensLaw

set_option autoImplicit false

noncomputable section

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-! ## Two steps along a program -/

theorem PrFrom_bind_le {S : OSpec} {α β : Type} (T : Table S) (c : OComp S α) (g : α → OComp S β)
    (E : Set β) {ε : ℝ≥0∞} (h : ∀ out ∈ (c.runLazy T).support, PrFrom out.2 (g out.1) E ≤ ε) :
    PrFrom T (c.bind g) E ≤ ε := by
  rw [PrFrom_bind]
  exact expect_le_of_forall_le _ h

theorem PrFrom_bind_pure {S : OSpec} {α β : Type} (T : Table S) (c : OComp S α) (f : α → β)
    (E : Set β) : PrFrom T (c.bind fun a => .pure (f a)) E = PrFrom T c (f ⁻¹' E) := by
  classical
  rw [PrFrom_bind, PrFrom_eq_lazy, pr_map, pr_eq_expect]
  refine expect_congr _ fun out => ?_
  rw [PrFrom_eq_lazy]
  show pr ((PMF.pure (f out.1, out.2)).map Prod.fst) E = _
  rw [PMF.pure_map, pr_pure]
  rfl

/-! ## The test under a uniform answer -/

section Test
variable {C P : Type} [Fintype C] [Nonempty C] (g : GrW C P) (chal : (Fin K → Dig lam) → C)

theorem chalA (hc : (unif (Fin K → Dig lam)).map chal = unif C) :
    (unif (FsAns lam K)).map (fun x => chal x.1) = unif C := by
  have h1 : (unif (FsAns lam K)).map Prod.fst = unif (Fin K → Dig lam) := Prob.Lens.map_fst
  rw [show (fun x : FsAns lam K => chal x.1) = chal ∘ Prod.fst from rfl, ← PMF.map_comp, h1, hc]

omit [Fintype C] [Nonempty C] in
theorem lensOf (hg : g.OK) : Prob.Lens.OK g.tst g.set := ⟨hg.tst_set, hg.set_tst, hg.set_set⟩

omit [Fintype C] [Nonempty C] in
theorem ok_false_iff (c : C) :
    g.ok c = false ↔ g.tst c ∈ ({fun _ => false} : Set (Fin g.b → Bool))ᶜ := by
  unfold TypedOracleCompiler.Iop.GrW.ok
  rw [decide_eq_false_iff_not]
  rfl

omit [Fintype C] [Nonempty C] in
/-- a verifier message that passes is itself with its test bits set to 0 -/
theorem set_of_ok (hg : g.OK) {c : C} (h : g.ok c = true) : g.set (fun _ => false) c = c := by
  have h' : g.tst c = fun _ => false := of_decide_eq_true h
  rw [← h']
  exact hg.set_tst c

theorem qFail_push (hc : (unif (Fin K → Dig lam)).map chal = unif C) :
    qFail (fun x : FsAns lam K => g.ok (chal x.1)) =
      pr (unif C) {c | g.tst c ∈ ({fun _ => false} : Set (Fin g.b → Bool))ᶜ} := by
  unfold qFail
  rw [← chalA chal hc, pr_map]
  exact congrArg _ (Set.ext fun x => ok_false_iff g (chal x.1))

/-- One uniform answer fails the test with probability 1 - 2^-b. -/
theorem qFail_eq (hg : g.OK) (hc : (unif (Fin K → Dig lam)).map chal = unif C) :
    qFail (fun x : FsAns lam K => g.ok (chal x.1)) = 1 - ((2 : ℝ≥0∞) ^ g.b)⁻¹ := by
  rw [qFail_push g chal hc]
  have e : pr (unif C) {c | g.tst c ∈ ({fun _ => false} : Set (Fin g.b → Bool))ᶜ} =
      pr (unif (Fin g.b → Bool)) ({fun _ => false} : Set (Fin g.b → Bool))ᶜ := by
    rw [← Prob.Lens.map_tst (lensOf g hg), pr_map]
    rfl
  rw [e, pr_compl, pr_singleton, PMF.uniformOfFintype_apply]
  congr 2
  simp

/-- The verifier message with its test bits set to 0 is independent of the test. -/
theorem ok_ind (hg : g.OK) (hc : (unif (Fin K → Dig lam)).map chal = unif C) (b : C) :
    pr (unif (FsAns lam K))
        {x | g.set (fun _ => false) (chal x.1) = b ∧ g.ok (chal x.1) = false} =
      pr (unif (FsAns lam K)) {x | g.set (fun _ => false) (chal x.1) = b} *
        qFail (fun x : FsAns lam K => g.ok (chal x.1)) := by
  rw [qFail_push g chal hc]
  have h := Prob.Lens.pr_indep (lensOf g hg) (fun _ => false)
    ({fun _ => false} : Set (Fin g.b → Bool))ᶜ ({b} : Set C)
  have e1 : pr (unif (FsAns lam K))
        {x | g.set (fun _ => false) (chal x.1) = b ∧ g.ok (chal x.1) = false} =
      pr (unif C) {c | g.set (fun _ => false) c ∈ ({b} : Set C) ∧
        g.tst c ∈ ({fun _ => false} : Set (Fin g.b → Bool))ᶜ} := by
    rw [← chalA chal hc, pr_map]
    exact congrArg _ (Set.ext fun x => and_congr Iff.rfl (ok_false_iff g (chal x.1)))
  have e2 : pr (unif (FsAns lam K)) {x | g.set (fun _ => false) (chal x.1) = b} =
      pr (unif C) {c | g.set (fun _ => false) c ∈ ({b} : Set C)} := by
    rw [← chalA chal hc, pr_map]
    rfl
  rw [e1, e2]
  exact h

/-- **The mean over "sample until the test is passed".** -/
theorem mean_le (hg : g.OK) (hc : (unif (Fin K → Dig lam)).map chal = unif C) (ψ : C → ℝ≥0∞)
    (n : ℕ) :
    (expect (retry (fun a : FsAns lam K => g.ok (chal a.1)) n) fun a =>
        if g.ok (chal a.1) then ψ (chal a.1) else 1) ≤
      (expect (unif C) fun c => ψ (g.set (fun _ => false) c)) +
        (1 - ((2 : ℝ≥0∞) ^ g.b)⁻¹) ^ (n + 1) := by
  have h2 := map_retry (fun a : FsAns lam K => g.ok (chal a.1))
    (fun a : FsAns lam K => g.set (fun _ => false) (chal a.1)) (ok_ind g chal hg hc) n
  have hA : (expect (unif C) fun c => ψ (g.set (fun _ => false) c)) =
      expect (retry (fun a : FsAns lam K => g.ok (chal a.1)) n) fun a =>
        ψ (g.set (fun _ => false) (chal a.1)) := by
    rw [← expect_map (retry (fun a : FsAns lam K => g.ok (chal a.1)) n)
        (fun a : FsAns lam K => g.set (fun _ => false) (chal a.1)) ψ, h2,
      show (fun a : FsAns lam K => g.set (fun _ => false) (chal a.1)) =
        (g.set fun _ => false) ∘ fun a : FsAns lam K => chal a.1 from rfl,
      ← PMF.map_comp, chalA chal hc, expect_map]
  rw [hA, ← qFail_eq g chal hg hc, ← pr_retry_fail, pr_eq_expect, ← expect_add]
  refine expect_mono _ fun a => ?_
  by_cases ho : g.ok (chal a.1) = true
  · rw [if_pos ho, set_of_ok g hg ho]
    exact le_self_add
  · have ho' : g.ok (chal a.1) = false := by simpa using ho
    rw [if_neg ho, if_pos (show a ∈ {x : FsAns lam K | g.ok (chal x.1) = false} from ho')]
    exact le_add_self

end Test

/-! ## A Fiat-Shamir query, with what follows it -/

/-- the verifier message with its test bits set to 0; itself where there is no test -/
def zeroOf {C P : Type} : Option (GrW C P) → C → C
  | none, c => c
  | some g, c => g.set (fun _ => false) c

section Fs
variable {C P γ : Type} [Fintype C] [Nonempty C] (gr : Option (GrW C P)) (cap : ℕ)
  (chal : (Fin K → Dig lam) → C) (t : Tag) (qf : P → FbIn lam L t) (α : P)
  (k : Option (P × FsAns lam K) → TypedOracleComputation lam K L γ) (E : Set γ) (ψ : C → ℝ≥0∞)

/-- **A Fiat-Shamir query, with what follows it.** hnew: no query of this form has an entry in T.
hk: from every table that agrees with T, in the column fb t, off the queries of this form, what
follows a returned answer has the event with probability at most ψ of the verifier message. -/
theorem fs_le (hgr : ∀ g, gr = some g → g.OK)
    (hc : (unif (Fin K → Dig lam)).map chal = unif C) (T : Table (typedOracleFamily lam K L))
    (hnew : ∀ β, T (OracleName.fb t) (qf β) = none) (hinj : Function.Injective qf)
    (hap : ∀ g, gr = some g → GrApart g cap)
    (hk : ∀ β ans T', (∀ q, (∀ β', q ≠ qf β') → T' (OracleName.fb t) q = T (OracleName.fb t) q) →
      PrFrom T' (k (some (β, ans))) E ≤ ψ (chal ans.1)) :
    PrFrom T ((fsO gr cap chal (fun β => askTypedOracle (L := L) (K := K) (OracleName.fb t) (qf β)) α).bind k) E ≤
      (expect (unif C) fun c => ψ (zeroOf gr c)) + grFailAt cap gr := by
  cases gr with
  | none =>
    show PrFrom T (((askTypedOracle (L := L) (K := K) (OracleName.fb t) (qf α)).bind fun a =>
      OComp.pure (some (α, a))).bind k) E ≤ _
    rw [_root_.Compile.Batch.LoopLazy.obind_assoc]
    refine (PrFrom_ask t _ _ T (hnew α) E).trans_le ?_
    show _ ≤ (expect (unif C) fun c => ψ c) + 0
    rw [add_zero, ← chalA chal hc, expect_map]
    refine expect_mono _ fun ans => ?_
    refine hk α ans _ fun q hq => ?_
    exact set_fb_other T t (hq α) ans
  | some g =>
    refine (search_le g chal t qf α k E (fun a => ψ (chal a.1)) cap 0 T (fun m _ _ => hnew _)
      (fun m m' _ h1 _ h2 e => hap g rfl α m m' (by omega) (by omega) (hinj e))
      fun m ans T' _ hT' => hk _ ans T' fun q hq => hT' q fun m' => hq _).trans ?_
    exact mean_le g chal (hgr g rfl) hc ψ cap

end Fs

end OnBytes.Prover
