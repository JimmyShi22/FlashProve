-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/LotJobsAtHead.lean: THE SHARED "SENDING" (the kind K1): THE 51
JOBS OF K1's OWN LOT (lotJobs, Honest/K1/LotJobs.lean), UNDER THE LIBRARY's HEAD, ARE THE JOBS OF
THE LIST BY NUMBERS (k1Members, Honest/K1/Law/LotsAtHead.lean), IN ITS ORDER, AT TWO WRITTEN
LETTERS. PUBLIC TERMS: plans, places, numbers; the data D stand under a binder and are not opened.
Three theorems; no definition.

WHY. LotsAtHead.lean's laws take the jobs as letters J₂ and Jl, under two premises on their plans.
lotJobs is the term of which a filling's halves are made (lotHalves_jobs). Nothing said that the one
list is the other.

  - lotJobs_at_head    UNDER h (the library's head: A HYPOTHESIS) and O: lotJobs no D Zp Bs.G₀ =
                       (k1Members J₂ Jl).map (·.2), where J₂ is the opening's job and Jl l d the
                       later job at the piece IM.k1Ix l d + 1 and the moment 1 (reads) or 2 (digits)
  - later_plan_head    the plan of that Jl l d is K1.parL Zp Bs.G₀ l d: LotsAtHead.lean's hPl. No
                       premise
  - lotJobs_length_head   so the lot has 51 jobs

The road. The ground has 25 built segments (IM.ground_gets, Johnson/IMR/PureJoin.lean); at each the
lot's own numbers of the two pieces are the flat list's (pieces_inScope, PiecesAndPort.lean).

KIN, TOLD. lotJobs_plans (Honest/K1/RunAt.lean) gives the jobs' plans and rides as a list of the
same shape as lotJobs, at any ground, without numbers. Another house's jobs_52_in_scope
(Johnson/SendSim/Seat/LotCount.lean) counts its own twin of lotJobs with W's job: 52. Neither says
which job stands at which number of the chain.

Limits. UNDER h. AT THE DESCRIPTION's OWN GROUND Bs.G₀: that a prover's ground is this one is not
said here. W's sending (number 356) is not in lotJobs and not here. THAT ANY FILLING CALLS lotJobs
IS NOT SAID HERE. THE FULL SIZE; the format's second hash function. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.LotsAtHead
import Johnson.Desc.ProofFile.Honest.K1.LotJobs
import Johnson.Desc.ProofFile.Honest.K1.Law.PiecesAndPort
import Johnson.IMR.PureJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S)
open OnBytes.Maker (WholeD)
open _root_.Desc.K14.Law (seatZ secondAt)

variable {Xi X : Type}

/-- **The later job's plan is the fifty's own.** No premise. -/
theorem later_plan_head (Zp : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (d : Bool) (first : ℕ)
    (Dd : RowDataOf Xi) :
    (laterJobAt (X := X) G.first (K1.gpOf Zp) l (IM.k1Ix l d + 1) (if d then 2 else 1) first Dd).P =
      K1.parL Zp G l d :=
  (parL_later Zp G l d).symm

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x₀ : First.Look.Place} {Bs : ProofFile.PureBase}
  {base₀ : List (Block S ProofFile.Cl)}

/-- **K1's OWN LOT's JOBS ARE THE LIST BY NUMBERS' JOBS, IN ITS ORDER.** -/
theorem lotJobs_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np))
    (no : Place → Nat) (Dt : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) :
    lotJobs (X := X) no Dt Zp Bs.G₀ =
      (k1Members
        (placeJob (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) (no ⟨1, some 0, 1, .K1⟩)
          (firstFold Bs.G₀.first) (Dt Zp Bs.G₀))
        (fun l d => laterJobAt Bs.G₀.first (K1.gpOf Zp) l (IM.k1Ix l d + 1) (if d then 2 else 1)
          (no ⟨1, some l, IM.k1Ix l d + 1, .K1⟩) (Dt Zp Bs.G₀))).map (·.2) := by
  have h25 : Bs.G₀.built.size = 25 := (IM.ground_gets h.scope h.reads h.laid.pub O.blank).1
  unfold lotJobs k1Members
  rw [List.map_cons, List.map_flatMap]
  congr 1
  rw [List.flatMap_def, List.flatMap_def]
  congr 1
  refine List.ext_getElem (by simp [h25]) fun i h1 h2 => ?_
  have hi : i < 25 := by simpa using h2
  obtain ⟨Xl, reads, digits, hX, hn⟩ := pieces_inScope h.scope h.reads O hi
  have hx : Bs.G₀.built.toList[i]? = some Xl := by
    rw [Array.getElem?_toList]
    exact hX
  obtain ⟨hlt, hx'⟩ := List.getElem?_eq_some_iff.1 hx
  simp only [List.getElem_map, List.getElem_zipIdx, List.getElem_range, Nat.zero_add, hx', hn]
  rfl

/-- **So the lot has 51 jobs.** -/
theorem lotJobs_length_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np))
    (no : Place → Nat) (Dt : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) :
    (lotJobs (X := X) no Dt Zp Bs.G₀).length = 51 := by
  rw [lotJobs_at_head h O no Dt, List.length_map]
  unfold k1Members
  simp

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.later_plan_head
#print axioms ProofFile.Honest.K1.lotJobs_at_head
#print axioms ProofFile.Honest.K1.lotJobs_length_head
