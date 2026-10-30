-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/RunIsInScope.lean: `RunIs` in the spender's shape, in the goals' scope, with no
public premise left; and the same at every function in the place of the second hash function.

What is shown.
  `nums_whole`: `Nums X` (Reads/RunIsAtBorder.lean) at what `publicOf` returns on public files in
    the goals' scope. By `InScope.nums_in_scope` (Johnson/Goal/Meaning/HeadNumsScope.lean).
  `runIs_in_scope`: **for public files in the goals' scope, the public part Z that the maker makes
    of them at the second hash function, and the ground G of a request of zeros: for every state
    with `ReachGives`, every e that `withTables` answers and every answer of `lettersAt` at e:
    `RunIs` at these letters.** hJ is paid by `InScope.cols_in_scope`
    (Johnson/Goal/Meaning/HeadColsScope.lean).
  `runIs_any`: **the same where the maker's public part is made at any function o in that hash's
    place**, under one premise more: `publicOf` returns a value on the same files. Two public parts
    made at two such functions differ at most in three digests (`publicOfO_two`,
    Johnson/Desc/Ok/PlanWritten/PublicAtTwo.lean); the premises that are paid here speak of the
    shape and the layout alone.

Premises. On a state: `ReachGives`. In `runIs_any`: that `publicOf` returns: which function o lets
the maker return a value is said by no law beneath this file.

Limits. That a state reached by the chain's fold behind the fourth place has `ReachGives` is not
shown.
(Where this and lean/THEOREM.md differ, the page holds.)
No states are shown at which the premises hold together. The full size alone. Nothing on
soundness.


-/
import Johnson.Desc.Reads.RunIsAtSecondHashFunction
import Johnson.Goal.Meaning.HeadNumsScope
import Johnson.Desc.Ok.PlanWritten.PublicAtTwo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads.AtSeat

open OnBytes.Model.Verify (publicOf)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K8 (ReadsQuiet.tables)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law

/-- The three closed facts in the goals' scope, with no premise left. -/
theorem nums_whole {A : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
    {X : OnBytes.Model.Verify.Public} (hA : VerifierAndGoals.InScope A = true)
    (hR : VerifierAndGoals.readFiles A = .ok pp) (h : publicOf A.pol A.KL lay = .ok X) : Nums X :=
  have n := InScope.nums_in_scope hA hR h
  ⟨n.1, n.2.1, n.2.2⟩

/-- **RunIs in the spender's shape, in the goals' scope: no public premise is left.** -/
theorem runIs_in_scope {A : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub}
    {mk : ProofFile.LinksBy} {G : ProofFile.Ground} (hA : VerifierAndGoals.InScope A = true)
    (hR : VerifierAndGoals.readFiles A = .ok pp)
    (hp : ProofFile.pureRoad.pub OnBytes.secondHashFunction A.pol lay A.KL = .ok Z) (hG : ProofFile.blankBy mk Z = some G)
    (same : S → S → Bool) (but : Place → Bool) (a4 : Place) (n4 : String) (place : Place)
    (b : OnBytes.Model.Head.Border) :
    ∀ s, ReachGives Z G same but a4 n4 s → ∀ (e : S) (v : Given × Behind × Places),
      withTables ⟨place, G.W.hS, G.W.HLy, G.W.H⟩ s = some e →
      lettersAt (parOf G.W.hS (Law.workOf G.W)) (seatAt G.W.hS (Law.readsOf G.W)) e = .ok v →
      ∃ a cov x t, e.here = .head a ∧ e.covered G.W.hS.T G.W.hS.V = .ok cov ∧ a.x = some x ∧
        a.t = some t ∧ ReadsQuiet.tables G.W.hS G.W.HLy G.W.H cov x = .ok t ∧
        (letI := v.1; letI := v.2.1
         RunIs ⟨G.W.hS, G.W.HLy, b, G.W.H, cov, x, t, Law.readsOf G.W⟩) := by
  have eW : G.W = Z.p.X := ProofFile.Law.blankBy_W hG
  have hX := public_older hp
  have hJ : ∀ q, q < 6 → (G.W.HLy.calls.getD q default).lJ =
      (letI := sizesOf G.W.hS; lJ (OnBytes.Model.Head.keyFloor G.W.hS) (callKeys q)) := by
    rw [eW]
    exact InScope.cols_in_scope hA hR hX
  have N : Nums G.W := by
    rw [eW]
    exact nums_whole hA hR hX
  exact runIs_at_reach Z G same but a4 n4 place b hJ N

/-- **The same at every function in the place of the second hash function.** -/
theorem runIs_any {o : ProofFile.SecondHashFunctionArgument} {A : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {Z : ProofFile.Pub} {mk : ProofFile.LinksBy} {G : ProofFile.Ground} {X₀ : OnBytes.Model.Verify.Public}
    (hA : VerifierAndGoals.InScope A = true) (hR : VerifierAndGoals.readFiles A = .ok pp)
    (hp : ProofFile.pureRoad.pub o A.pol lay A.KL = .ok Z) (hG : ProofFile.blankBy mk Z = some G)
    (hX₀ : publicOf A.pol A.KL (some lay) = .ok X₀)
    (same : S → S → Bool) (but : Place → Bool) (a4 : Place) (n4 : String) (place : Place)
    (b : OnBytes.Model.Head.Border) :
    ∀ s, ReachGives Z G same but a4 n4 s → ∀ (e : S) (v : Given × Behind × Places),
      withTables ⟨place, G.W.hS, G.W.HLy, G.W.H⟩ s = some e →
      lettersAt (parOf G.W.hS (Law.workOf G.W)) (seatAt G.W.hS (Law.readsOf G.W)) e = .ok v →
      ∃ a cov x t, e.here = .head a ∧ e.covered G.W.hS.T G.W.hS.V = .ok cov ∧ a.x = some x ∧
        a.t = some t ∧ ReadsQuiet.tables G.W.hS G.W.HLy G.W.H cov x = .ok t ∧
        (letI := v.1; letI := v.2.1
         RunIs ⟨G.W.hS, G.W.HLy, b, G.W.H, cov, x, t, Law.readsOf G.W⟩) := by
  have eW : G.W = Z.p.X := ProofFile.Law.blankBy_W hG
  have h0 : VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction A.pol A.KL (some lay) =
      .ok X₀ := by
    rw [VerifiableInference.PlanWritten.publicOfO_older]
    exact hX₀
  have e2 := VerifiableInference.PlanWritten.publicOfO_two h0 (ProofFile.Law.pub_public hp)
  have ehS : G.W.hS = X₀.hS := by
    rw [eW, e2]
  have eHL : G.W.HLy = X₀.HLy := by
    rw [eW, e2]
  have hJ : ∀ q, q < 6 → (G.W.HLy.calls.getD q default).lJ =
      (letI := sizesOf G.W.hS; lJ (OnBytes.Model.Head.keyFloor G.W.hS) (callKeys q)) := by
    rw [ehS, eHL]
    exact InScope.cols_in_scope hA hR hX₀
  have N0 := nums_whole hA hR hX₀
  have N : Nums G.W :=
    ⟨by rw [eHL]; exact N0.six, by rw [ehS]; exact N0.floor, by rw [ehS]; exact N0.hls⟩
  exact runIs_at_reach Z G same but a4 n4 place b hJ N

end VerifiableInference.Reads.AtSeat

#print axioms VerifiableInference.Reads.AtSeat.nums_whole
#print axioms VerifiableInference.Reads.AtSeat.runIs_in_scope
#print axioms VerifiableInference.Reads.AtSeat.runIs_any
