--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/YesAt.lean: the public premises under which the functions of the eight
sub-protocols of the linear claim's shared rounds return (Johnson/Desc/K14/Honest/YesChain.lean:
PlanFacts) hold at the library's two TYPED shapes: the typed sizes over a proof file's own codes,
and the typed sizes of a key of full size.

PlanFacts follows from two structures that the library already has at these shapes, and one test
more:
  K14Cond (Johnson/Goal/Numbers/K14CondAt.lean): each of the eight sub-protocols' tests on the plan
      accepts. These tests ask: every code's message length is a power of two; the shape fits the
      codes; the two groups' codes are in order; the notices of the two sendings fit the codes and
      their trees can be laid; the mask message has a free entry.
  Ten (Johnson/Goal/Numbers/K14PlanTen.lean): there are two codes; what goes out with o_u has two
      notices; masks are sent ahead; how the trees of o_omega's sending are laid.
  ownTreeB: in that layout o_omega's notice gets a tree that is there and that o_sp's notice does
      not share. Evaluated in Lean's kernel (decide +kernel) at the two typed shapes.

Main names:
  ownTreeB, ownTree_of   the test, and what it gives where it is passed
  planFacts_of        **K14Cond, Ten and the test give PlanFacts**
  planFacts_real      PlanFacts at the typed sizes over a proof file's own codes
  planFacts_real_at_chains   so at the parameters that the shared chain's maker takes off the
                      planner's chains, wherever the planner's sizes of the proof have that setting,
                      these codes and that shape, and are no one-time test's
  planFacts_key       PlanFacts at the typed sizes of a key of full size
  planFacts_key_at_scope   so at the planner's sizes of the key, at every three public files in the
                      scope of the goals, from a planner that returns

What is not claimed. THAT THE PLANNER's SIZES OF A PROOF AT THE RELEASE's FILES ARE THE TYPED ONES:
no theorem says so; what the heads of K14CondAt.lean and K14PlanTen.lean do not claim is not claimed
here. This file states no goal. Nothing on a view's rounds or on the instance's key. Nothing on
soundness, on completeness or on hiding.

-/
import Johnson.Desc.K14.Honest.YesChain
import Johnson.Goal.Numbers.K14PlanTen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params OnBytes.Params.Prices OnBytes.Plan Johnson.G Desc.Plain
open VerifiableInference.Desc.K1 (realSized)
open Lk6.AtPlan (keyFull key_eq_at_scope)
open Desc.K14.Law (K14Cond Ten k14_real k14_key ten_real ten_key)

/-- In the layout of o_omega's sending, o_omega's notice gets a tree that is there and that o_sp's
notice does not share. -/
def ownTreeB (cs : Codes) (S : LinShape) : Bool :=
  (layTrees cs (withOmega S)).any fun l =>
    decide (l.tree.getD 0 0 < l.shapes.size) && decide (l.tree.getD 1 0 ≠ l.tree.getD 0 0)

/-- What the test gives where it is passed. -/
theorem ownTree_of {cs : Codes} {S : LinShape} {layO : TreeLay} (h : ownTreeB cs S = true)
    (hl : layTrees cs (withOmega S) = some layO) :
    layO.tree.getD 0 0 < layO.shapes.size ∧ layO.tree.getD 1 0 ≠ layO.tree.getD 0 0 := by
  unfold ownTreeB at h
  rw [hl, Option.any_some] at h
  simpa only [Bool.and_eq_true, decide_eq_true_eq] using h

/-- **K14Cond, Ten and the test give the public premises.** -/
theorem planFacts_of {f : Nat} {P : P14} {W : Rounds} {sentU : Array OracleNotice}
    {layU layO : TreeLay} (hC : K14Cond f P W) (hT : Ten P.codes P.S sentU layU layO)
    (hO : ownTreeB P.codes P.S = true) :
    PlanFacts P.par P.codes sentU layO := by
  obtain ⟨bs, hb, _, hplan, _⟩ := hC.blocks
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hb
  obtain ⟨sentU', hU', rfl⟩ := hb
  obtain rfl : sentU = sentU' := Option.some.inj (hT.hU.symm.trans hU')
  have p1 := hplan _ (List.mem_cons_self)
  have p2 := hplan _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have p5 := hplan _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ List.mem_cons_self))))
  have p8 := hplan _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)))))))
  have q1 : (VerifiableInference.OnPublicFiles.OkD.At.linPoint P.codes P.S &&
      !P.beforePoint.isEmpty) = true := p1
  have q8 : VerifiableInference.OnPublicFiles.OkD.At.splitB P.codes P.S = true := p8
  have q2 : VerifiableInference.OnPublicFiles.OkD.At.sending P.codes
      (VerifiableInference.OnPublicFiles.OkD.At.withU P.S) = true := by
    have : ((VerifiableInference.Desc.Block.inside _ _ _).planOk &&
      VerifiableInference.OnPublicFiles.OkD.At.sending P.codes
        (VerifiableInference.OnPublicFiles.OkD.At.withU P.S) && _) = true := p2
    simp only [Bool.and_eq_true] at this
    exact this.1.2
  have q5 : VerifiableInference.OnPublicFiles.OkD.At.sending P.codes (linMessageOmega P.S) = true := by
    have : ((VerifiableInference.Desc.Block.inside _ _ _).planOk &&
      VerifiableInference.OnPublicFiles.OkD.At.sending P.codes (linMessageOmega P.S) && _) = true := p5
    simp only [Bool.and_eq_true] at this
    exact this.1.2
  have eU : VerifiableInference.OnPublicFiles.OkD.At.withU P.S = sentU := by
    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.1 hT.hU
    unfold VerifiableInference.OnPublicFiles.OkD.At.withU
    rw [hw]
    rfl
  rw [eU] at q2
  simp only [VerifiableInference.OnPublicFiles.OkD.At.linPoint, Bool.and_eq_true, Bool.or_eq_true] at q1
  simp only [VerifiableInference.OnPublicFiles.OkD.At.splitB, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at q8
  simp only [VerifiableInference.OnPublicFiles.OkD.At.sending, Bool.and_eq_true] at q2 q5
  obtain ⟨⟨⟨⟨⟨_, a2⟩, a3⟩, a4⟩, a5⟩, _⟩ := q1
  refine ⟨a2, a3, a4, ?_, hT.hS, hT.hm, hT.hU, hT.hsU, q2.1, q5.1, ?_, hT.hlO, ownTree_of hO hT.hlO⟩
  · rcases a5 with e | e
    · rw [hT.hS] at e
      cases e
    · exact e
  · rcases q8.2 with e | e
    · rw [hT.hS] at e
      cases e
    · exact e

/-- The test is passed at the typed sizes over a proof file's own codes: an evaluation in Lean's
kernel. -/
theorem ownTree_real : (realSized.any fun p => ownTreeB p.2 p.1.shape) = true := by decide +kernel

/-- The test is passed at the typed sizes of a key of full size: an evaluation in Lean's kernel. -/
theorem ownTree_key : ownTreeB keyFull.codes keyFull.once.shape = true := by decide +kernel

/-- **The public premises at the typed sizes over a proof file's own codes.** -/
theorem planFacts_real : ∃ (x : LinSized) (sentU : Array OracleNotice) (layO : TreeLay),
    realSized = some (x, codesFull2) ∧ AtRecord x ∧
    ∀ (item : Nat) (bp : List (Nat × Nat)), bp ≠ [] →
      PlanFacts (P14.par ⟨recordSet, .shared, codesFull2, x.shape, item, bp⟩) codesFull2 sentU
        layO := by
  obtain ⟨x, a1, a2, a3⟩ := k14_real
  obtain ⟨x', b1, sentU, layU, layO, hT⟩ := ten_real
  obtain rfl : x = x' := congrArg Prod.fst (Option.some.inj (a1.symm.trans b1))
  have h := ownTree_real
  rw [a1, Option.any_some] at h
  exact ⟨x, sentU, layO, a1, a2, fun item bp hbp =>
    planFacts_of (P := ⟨recordSet, .shared, codesFull2, x.shape, item, bp⟩) (a3 item bp hbp) hT h⟩

/-- **At the parameters that the shared chain's maker takes off the planner's chains.** -/
theorem planFacts_real_at_chains : ∃ (x : LinSized) (sentU : Array OracleNotice) (layO : TreeLay),
    realSized = some (x, codesFull2) ∧ AtRecord x ∧
    ∀ (c : Model.Verify.Chains) (bp : List (Nat × Nat)), bp ≠ [] →
      c.made.sized.proof.set = recordSet → c.made.sized.proof.codes = codesFull2 →
      c.made.sized.proof.batch.shape = x.shape →
      c.made.sized.proof.batch.lines.oneTime = false →
        PlanFacts (p14Of c bp).par (p14Of c bp).codes sentU layO := by
  obtain ⟨x, sentU, layO, a1, a2, a3⟩ := planFacts_real
  refine ⟨x, sentU, layO, a1, a2, fun c bp hbp h1 h2 h3 h4 => ?_⟩
  have e : p14Of c bp = ⟨recordSet, .shared, codesFull2, x.shape, 0, bp⟩ := by
    unfold p14Of
    simp only [h1, h2, h3, h4, Bool.false_eq_true, if_false]
  rw [e]
  exact a3 0 bp hbp

/-- **The public premises at the typed sizes of a key of full size.** -/
theorem planFacts_key : ∃ (sentU : Array OracleNotice) (layO : TreeLay),
    ∀ (item : Nat) (bp : List (Nat × Nat)), bp ≠ [] →
      PlanFacts (P14.par ⟨recordSet, .once, keyFull.codes, keyFull.once.shape, item, bp⟩)
        keyFull.codes sentU layO := by
  obtain ⟨sentU, layU, layO, hT⟩ := ten_key
  exact ⟨sentU, layO, fun item bp hbp =>
    planFacts_of (P := ⟨recordSet, .once, keyFull.codes, keyFull.once.shape, item, bp⟩)
      (k14_key item bp hbp) hT ownTree_key⟩

/-- **At the planner's sizes of the key**, at every three public files in the scope of the goals,
from a planner that returns. -/
theorem planFacts_key_at_scope {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {p : Model.Verify.Planned} (hp : Model.Verify.planned Z.pol Z.KL (some Z.lay) = .ok p) :
    ∃ (sentU : Array OracleNotice) (layO : TreeLay),
    ∀ (item : Nat) (bp : List (Nat × Nat)), bp ≠ [] →
      PlanFacts (P14.par ⟨p.chains.made.sized.key.set, .once, p.chains.made.sized.key.codes,
        p.chains.made.sized.key.once.shape, item, bp⟩) p.chains.made.sized.key.codes sentU
        layO := by
  rw [key_eq_at_scope hZ hp]
  exact planFacts_key

end Desc.K14.Honest

#print axioms Desc.K14.Honest.ownTree_of
#print axioms Desc.K14.Honest.planFacts_of
#print axioms Desc.K14.Honest.ownTree_real
#print axioms Desc.K14.Honest.ownTree_key
#print axioms Desc.K14.Honest.planFacts_real
#print axioms Desc.K14.Honest.planFacts_real_at_chains
#print axioms Desc.K14.Honest.planFacts_key
#print axioms Desc.K14.Honest.planFacts_key_at_scope
