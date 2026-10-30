-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/PlanAtHead.lean: kind K14: THE KIND's PUBLIC PREMISES, Plan2
(Honest/K14/Debts2.lean), AT THE SHARED CHAIN's OWN PARAMETERS p14Of Zp.p.chains (beforePointOf Np):
all fifteen facts follow, in the goals' scope, from the library's LaidAt
(Johnson/P5J/LaidOpens.lean), and so from its head (P5J.AtMgA, Johnson/P5J/MgAtAll.lean). Statements
with their proofs: calls; no definition. This file imports modules of the folder Johnson/Goal/
directly (Johnson/Goal/Numbers/WrittenAtZ.lean, Johnson/Goal/Skeleton/PinsOfLaid.lean): for laws; it
defines nothing.

  plan2_of_written Plan2 at p14Of Z.p.chains bp, at some sentU and layO, from the library's
                  equations on the public part (Written Z x, WrittenAtZ.lean) at the size x that the
                  library's realSized (Johnson/Desc/K1/) returns, and bp ≠ []: PlanFacts by
                  planFacts_real_at_chains (Johnson/Desc/K14/Honest/YesAt.lean); the two sendings'
                  tests on the plan by planOwn_of (Johnson/Desc/K14/Honest/ChainWitness.lean) from
                  the library's k14_at_Z. (plan2_real, Honest/K14/Thread2Member.lean, has the same
                  at the written-out parameters: what is new here is: at p14Of of the planner's
                  chains)
  plan2_of_laid   **from VerifierAndGoals.InScope Z and LaidAt, at every earlier hash o**: the equations by
                  the library's Sh.written_of_made (Johnson/Desc/K14/Law/SharedConstCodesMade.lean),
                  pins_of_laid (PinsOfLaid.lean) and laidPOf_of; bp ≠ [] by their field before at
                  LaidAt's places. (The term "L.run ▸ laidPOf_of …" in the proof is the body of the
                  library's laidPOf_of_laidAt, Johnson/Road/K4/K4PlanOfLaid.lean: it is not imported
                  for that one term)
  plan2_at_head   **under the head**: its scope and its laid
  plan2_unique    Plan2 fixes its two arguments sentU and layO: at most one pair

AMONG THE CLOSED FACTS BENEATH are evaluations in Lean's kernel at the typed sizes: beneath the
library's k14_at_Z (it opens five closed facts, of which this file spends the first,
k14_real_seat's) and ten_real; this kind's ownTree_real; beneath written_of_made: full_real and what
written_in_scope calls. The cone of imports was not walked.

What is not claimed. No example of LaidAt or of the head is shown in this file; one, at
VerifierAndGoals.storedPublicFiles, is AtFullSide/Top/HeadMemberAtFull.lean's. The full size alone. Nothing of a run.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.Debts2
import Johnson.Desc.K14.Law.SharedConstCodesMade
import Johnson.Goal.Numbers.WrittenAtZ
import Johnson.Goal.Skeleton.PinsOfLaid
import Johnson.P5J.MgAtAll
import Johnson.Desc.K14.Honest.YesAt
import Johnson.Desc.K14.Honest.ChainWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (OracleNotice TreeLay)
open OnBytes.Params (LinSized)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.K1 (realSized)
open Johnson.G (codesFull2)
open Desc.K14 (P14 p14Of beforePointOf)
open Desc.K14.Law (Written sized_one k14_at_Z)
open Desc.K14.Honest (planFacts_real_at_chains planOwn_of)

/-- Plan2 at p14Of of the planner's chains, from the library's equations on the public part at the
size that realSized returns. -/
theorem plan2_of_written {Z : ProofFile.Pub} {x : LinSized} (hx : realSized = some (x, codesFull2))
    (W : Written Z x) (bp : List (Nat × Nat)) (hbp : bp ≠ []) :
    ∃ sentU layO, Plan2 (p14Of Z.p.chains bp) sentU layO := by
  obtain ⟨x₁, sentU, layO, a1, -, a3⟩ := planFacts_real_at_chains
  obtain rfl := sized_one hx a1
  have F := a3 Z.p.chains bp hbp W.set W.codes W.shape W.batch
  obtain ⟨u, v⟩ := planOwn_of (k14_at_Z hx W bp hbp).1 F.goes
  exact ⟨sentU, layO, F, u, v⟩

section laid
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- **Plan2 at the shared chain's own parameters, in the goals' scope, from LaidAt.** -/
theorem plan2_of_laid (hZ : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) :
    ∃ sentU layO, Plan2 (p14Of Zp.p.chains (beforePointOf Np)) sentU layO := by
  obtain ⟨x, hx, W⟩ := Desc.K14.Law.Sh.written_of_made hZ L.pub (P5J.pins_of_laid hZ L).1
    (L.run ▸ LPFD.Full.laidPOf_of L.value L.planOk L.data L.asks)
  exact plan2_of_written hx W _ (W.before Np L.places)

end laid

/-- **Plan2 at the shared chain's own parameters, under the library's head.** -/
theorem plan2_at_head {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place} {o : ProofFile.SecondHashFunctionArgument}
    (h : P5J.AtMgA o Z D r Zp Np cF x₀) :
    ∃ sentU layO, Plan2 (p14Of Zp.p.chains (beforePointOf Np)) sentU layO :=
  plan2_of_laid h.scope h.laid

/-- Plan2 fixes its two arguments sentU and layO. -/
theorem plan2_unique {Q : P14} {u u' : Array OracleNotice} {l l' : TreeLay} (h : Plan2 Q u l)
    (h' : Plan2 Q u' l') : u = u' ∧ l = l' := by
  obtain rfl : u = u' := Option.some.inj (h.facts.goes.symm.trans h'.facts.goes)
  exact ⟨rfl, Option.some.inj (h.facts.trees.symm.trans h'.facts.trees)⟩

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.plan2_of_written
#print axioms ProofFile.Honest.K14.plan2_of_laid
#print axioms ProofFile.Honest.K14.plan2_at_head
#print axioms ProofFile.Honest.K14.plan2_unique
