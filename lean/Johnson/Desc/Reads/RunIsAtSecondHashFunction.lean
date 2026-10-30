-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/RunIsAtSecondHashFunction.lean: `runIs_at_reach` (Reads/RunIsAtBorder.lean) at the ground that
the proof file's IOP as written in Lean makes of public files in the goals' scope.

This law is stated at the second hash function itself (`OnBytes.secondHashFunction`) in the place of the letter
for that hash: the laws on the goals' scope speak of the program's own `publicOf`, which the maker's
text is at that hash alone (`publicOfO_older`, Johnson/Desc/Ok/PlanWritten/PublicAtLaws.lean). In
this file that hash enters through the maker's public part alone (`Road.pub`), which is made of the
three public files: no challenge is drawn by it there. The hash by which challenges are drawn is not
named in this file.

What is shown.
  `public_older`: where the maker's public part is made at that hash, its public values are what
    `publicOf` returns. By `ProofFile.Law.pub_public` (Johnson/Desc/ProofFile/Law/MakerPublic.lean).
  `runIs_at_reach_older`: **for public files in the goals' scope, the public part Z that the maker
    makes of them, and the ground G of a request of zeros: for every state with `ReachGives`, every
    e that `withTables` answers and every answer of `lettersAt` at e: `RunIs` at these letters.**
    Two public premises are left: hJ, in the letters of the conclusion of `cols_in_scope`
    (Johnson/Goal/Meaning/HeadColsScope.lean, not imported); and "the layout has at most six calls".

Limits. As in Reads/RunIsAtBorder.lean: that a state reached by the chain's fold behind the fourth
place has `ReachGives` is not shown
(Where this and lean/THEOREM.md differ, the page holds.); no states are shown at which
the premises hold together. The
full size alone. Nothing on soundness.


-/
import Johnson.Desc.Reads.NumsOf
import Johnson.Desc.ProofFile.Law.MakerPublic
import Johnson.Desc.Ok.PlanWritten.PublicAtLaws

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

/-- The maker's public values, at the second hash function itself. -/
theorem public_older {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pureRoad.pub OnBytes.secondHashFunction pol lay KL = .ok Z) :
    publicOf pol KL (some lay) = .ok Z.p.X := by
  rw [← VerifiableInference.PlanWritten.publicOfO_older]
  exact ProofFile.Law.pub_public h

/-- **RunIs in the spender's shape, at the maker's ground, in the goals' scope.** -/
theorem runIs_at_reach_older {A : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {Z : ProofFile.Pub} {mk : ProofFile.LinksBy} {G : ProofFile.Ground} (hA : VerifierAndGoals.InScope A = true)
    (hR : VerifierAndGoals.readFiles A = .ok pp)
    (hp : ProofFile.pureRoad.pub OnBytes.secondHashFunction A.pol lay A.KL = .ok Z) (hG : ProofFile.blankBy mk Z = some G)
    (hJ : ∀ q, q < 6 → (G.W.HLy.calls.getD q default).lJ =
      (letI := sizesOf G.W.hS; lJ (OnBytes.Model.Head.keyFloor G.W.hS) (callKeys q)))
    (h6 : G.W.HLy.calls.size ≤ 6) (same : S → S → Bool) (but : Place → Bool) (a4 : Place)
    (n4 : String) (place : Place) (b : OnBytes.Model.Head.Border) :
    ∀ s, ReachGives Z G same but a4 n4 s → ∀ (e : S) (v : Given × Behind × Places),
      withTables ⟨place, G.W.hS, G.W.HLy, G.W.H⟩ s = some e →
      lettersAt (parOf G.W.hS (Law.workOf G.W)) (seatAt G.W.hS (Law.readsOf G.W)) e = .ok v →
      ∃ a cov x t, e.here = .head a ∧ e.covered G.W.hS.T G.W.hS.V = .ok cov ∧ a.x = some x ∧
        a.t = some t ∧ ReadsQuiet.tables G.W.hS G.W.HLy G.W.H cov x = .ok t ∧
        (letI := v.1; letI := v.2.1
         RunIs ⟨G.W.hS, G.W.HLy, b, G.W.H, cov, x, t, Law.readsOf G.W⟩) := by
  have eW : G.W = Z.p.X := ProofFile.Law.blankBy_W hG
  have N : Nums G.W := by
    rw [eW]
    exact nums_in_scope hA hR (public_older hp) (by rw [← eW]; exact h6)
  exact runIs_at_reach Z G same but a4 n4 place b hJ N

end VerifiableInference.Reads.AtSeat

#print axioms VerifiableInference.Reads.AtSeat.public_older
#print axioms VerifiableInference.Reads.AtSeat.runIs_at_reach_older
