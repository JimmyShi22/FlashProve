-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/FallAtRunRows.lean: THE SMALLNESS TEST: THE CHANCE OF Johnson/P1K8R/FallAtRun.lean, AT
THE HONEST SIDE's OWN RUN OF THE PROOF FILE's DESCRIPTION, WITH THE NUMBER d TIED TO THE PLAN: d :=
(THE ROWS OF THE BATCHING's DECLARED ROUND) - 1, UNDER ONE TEST WITH CODE ON THE PUBLIC PART. A
LEMMA; NONE OF THE LIBRARY's GOALS. Nothing on completeness, soundness or hiding. An assembly: no
new argument.

  **`fall_at_run_rows`**   `fall_at_run` without the letter d and its premise (bound), under
      `RowsAsked Z` (Johnson/Desc/First/Link/Law/K9RowsAskLaw.lean): in the goals' scope, at every
      segment l < 25, at every book, prover, input and coins, with (hj) and (hshow) on how a list is
      shown: the chance, over the list, that the run returns, that its verifier comes to stand in
      front of the member behind the batching, and that `selfUnits` says no at the state there, is
      at most nU[2] * (p.rows - 1) * w / (the number of round j's challenges), p the batching's
      numbers (IM.k9At Z l)
By: `fall_at_run` at d := p.rows - 1; `frontAt_reach`
(Johnson/Desc/ProofFile/Honest/K8/FrontsAgree.lean) and `bound_at_batch`
(Johnson/P1K8R/BoundAtBatch.lean).
Limits. `RowsAsked Z` IS A PREMISE: that the test accepts at any public files is not shown here. For
the rest those of FallAtRun.lean but for (bound): by number, not by place; (hj) and (hshow) are
premises; the law is named, not derived; one segment, one of the tests; no number is evaluated; that
a run returns is not said.
-/
import Johnson.P1K8R.FallAtRun
import Johnson.P1K8R.BoundAtBatch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.K9Asks (RowsAsked)
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.Tie.Pv.Tail.Port (topOf)
open ProofFile.Honest (ProverCoinCounts Prover Coins Draws RunC runC frontsOf)
open ProofFile.Honest.K8 (frontAt rnds)
open scoped ENNReal

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}

/-- **The chance at the honest side's own run, with the plan's number.** -/
theorem fall_at_run_rows (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25)
    {W₀ Rc Ky Tr X₀ X' : Type} (Bk : ProverCoinCounts) (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X') (w₀ : W₀)
    (rc : Rc) (x : ProofFile.Inst) (k : Coins Bk)
    {ι : Type} [Fintype ι] [DecidableEq ι] {A : ι → Type} [∀ i, Fintype (A i)]
    [∀ i, Nonempty (A i)] (j : ι) (el : A j → Cb.Gl.E) (w : ℕ)
    (hw : ∀ y, Prob.cnt (fun a => el a = y) ≤ w) (shows : (∀ i, A i) → Draws)
    (hj : ∀ f a, (shows (Function.update f j a)).first.take
        (rnds (c.blocksInOrder.take (14 * l + (if l = 24 then 11 else 9)))) =
      (shows f).first.take (rnds (c.blocksInOrder.take (14 * l + (if l = 24 then 11 else 9)))))
    (hshow : ∀ f dr, (shows f).first[rnds (c.blocksInOrder.take (14 * l + (if l = 24 then 11 else 9)))]? =
      some dr → dr.elems = [Slice.ofE (el (f j))]) :
    ∃ (p : K9.Where) (X : LinkH), IM.k9At Z l = some p ∧ Bs.G₀.built.toList[l]? = some X ∧
      Prob.pr (Prob.unif (∀ i, A i)) {f | ∃ (r : RunC (descAt Z A₂ B₂ c))
          (e' : Place × S × List Fmt.Drawn),
          runC (descAt Z A₂ B₂ c) Bk H w₀ rc x k (shows f) = .ok r ∧
          (frontsOf 0 c.blocksInOrder (ProofFile.startS Z x.pub) (withEmptySealRound r.run.views.1).rounds
            (withEmptySealRound r.run.views.1).opened)[14 * l + (if l = 24 then 11 else 9) + 1]? =
              some e' ∧
          zeroUnitAt (ProofFile.k8NU Bs.G₀ X) e'.2.1 = true} ≤
        (((ProofFile.k8NU Bs.G₀ X).getD 2 0 * (p.rows - 1) * w : ℕ) : ℝ≥0∞) / Fintype.card (A j) := by
  obtain ⟨p', hp', hbound⟩ := bound_at_batch hE hS hR O hl
  obtain ⟨p, X, hp, hX, h⟩ := fall_at_run hS hR O hl Bk H w₀ rc x k j el w hw shows hj hshow
    (p'.rows - 1) (fun f zs hz tl F' funs h1 h2 h3 => by
      have h := hbound zs.1 zs.2 (ProofFile.Honest.K8.frontAt_reach hz) tl F' funs h1 h2 h3
      omega)
  obtain rfl : p = p' := Option.some.inj (hp.symm.trans hp')
  exact ⟨p, X, hp, hX, h⟩

end

end P1K8

#print axioms P1K8.fall_at_run_rows
