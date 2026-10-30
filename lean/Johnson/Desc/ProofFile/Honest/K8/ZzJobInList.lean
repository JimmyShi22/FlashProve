-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/ZzJobInList.lean: the honest side of the smallness test (K8):
places, numbers and the prover's text alone: under the library's head and an opening of the
description, the shared sending's second later job of segment l, at the lot's own data, stands with
the number behind the kind's in the list of jobs by their places' numbers (`byNo`,
Johnson/Desc/ProofFile/Honest/Thread/Join.lean) over the two lists of jobs, which together are
`k1Jobs` of Johnson/Desc/ProofFile/Honest/Thread/JoinAtHead.lean written out. This meets the
premises hx and hJ of `zz_at_join_head` (Johnson/Desc/ProofFile/Honest/K8/ZzAtJoin.lean). Three
statements with their proofs; no definition.

  `behind_closed`, `behind_bite`   the written numbers: that member stands one number behind the
                  kind's at all 25 segments; at the kind's own number at none
  **`zz_job_in_list`**   by `members_by_border`
                  (Johnson/Desc/ProofFile/Honest/K1/Law/MembersByBorder.lean), `mem_k1MembersW`,
                  `mem_k1Members` and the closed fact
No option is raised; one instance is taken away, as in the files beneath. No tactic that searches;
two lines are an evaluation each by Lean's kernel (`decide +kernel`).
Limits. The head and the opening are hypotheses. The full size alone. Nothing on what the job sends.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Join
import Johnson.Desc.ProofFile.Honest.K1.Law.MembersByBorder
import Johnson.Desc.ProofFile.Honest.K1.LotData

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open OnBytes.Maker (WholeD)
open ProofFile.Honest.FirstThread (byNo)
open OnBytes.SendSim.Seat (wJobs)
open _root_.Desc.K14.Law (seatZ secondAt)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {X : Type}

/-- The shared sending's second later member of each segment stands one number behind the kind's. A
closed fact, by the kernel. -/
theorem behind_closed : ((List.range 25).all fun l =>
    K1.noL l true == 14 * l + (if l = 24 then 5 else 4) + 2 + 1) = true := by decide +kernel

/-- A control: at no segment does it stand at the kind's own number. -/
theorem behind_bite : ((List.range 25).any fun l =>
    K1.noL l true == 14 * l + (if l = 24 then 5 else 4) + 2) = false := by decide +kernel

/-- **The job that sends the digits stands in the list, with the number behind the kind's.** Under
the head and an opening of the description; l is below 25. Places, numbers and the prover's text
alone. -/
theorem zz_job_in_list (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base₀ : List (Block S ProofFile.Cl)}
    (O₁ : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np))
    (no : Place → Nat) (S₀ : OnBytes.HonestTrace.Sz)
    (Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf ProofFile.Inst) {l : ℕ} (hl : l < 25) :
    (14 * l + (if l = 24 then 5 else 4) + 2 + 1,
      K1.laterJobAt (X := X) Bs.G₀.first (K1.gpOf Zp) l (IM.k1Ix l true + 1) 2
        (no ⟨1, some l, IM.k1Ix l true + 1, .K1⟩) (K1.lotData S₀ Zp Bs.G₀)) ∈
      byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData S₀) Zp Bs.G₀ ++
                 wJobs (X := X) no Dd Zp Bs.G₀) := by
  have e := beq_iff_eq.1 (List.all_eq_true.1 behind_closed l (List.mem_range.2 hl))
  unfold byNo
  rw [K1.members_by_border h O₁ no (K1.lotData S₀) Dd]
  exact K1.mem_k1MembersW.2 (Or.inl (K1.mem_k1Members.2 (Or.inr ⟨l, hl, true,
    Prod.ext e.symm rfl⟩)))

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.behind_closed
#print axioms ProofFile.Honest.K8.behind_bite
#print axioms ProofFile.Honest.K8.zz_job_in_list
