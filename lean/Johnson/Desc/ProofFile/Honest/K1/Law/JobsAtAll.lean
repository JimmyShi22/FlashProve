-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/JobsAtAll.lean: THE SHARED "SENDING" (the kind K1): UNDER THE
LIBRARY's HEAD THE JOB AT W's SENDING IS A WRITTEN TERM; AND THE 52 JOBS OF THE TWO LOTS' LISTS,
lotJobs ++ wJobs, ARE THE JOBS OF k1MembersW (LotsAtAll.lean), IN ORDER, AT THREE WRITTEN LETTERS.
Six theorems; no definition.

WHY. LotJobsAtHead.lean says which job stands at which number for the 51. In k1MembersW the job at
356, Jw, was still a letter. Here it is laid.

  wJobs_at_head    UNDER h (the library's head: A HYPOTHESIS) AND O: the list wJobs
                   (Johnson/SendSim/Seat/LotW.lean) is one job: wJobAt
                   (Honest/K1/PlaceW.lean) at the WRITTEN message wMsgFull
  w_plan_head      that job's plan is K1.parW ... wMsgFull: LotsAtAll.lean's premise hPw at that
                   letter. No premise: by unfolding
  two_plan_head    the opening's job's plan is K1.firstPar ...: the premise hP₂. By unfolding
  jobs_at_head     UNDER h AND O: lotJobs no Dt Zp Bs.G₀ ++ wJobs no Dd Zp Bs.G₀ =
                   (k1MembersW J₂ Jl Jw).map (·.2) at the three written letters

  lotJobs_one      TWO DEFINITIONS IN THE LIBRARY BEAR THE NAME lotJobs: ours
                   (Honest/K1/LotJobs.lean) and another house's (OnBytes.SendSim.Seat.lotJobs,
                   Johnson/SendSim/Seat/Lot.lean): one body, sign for sign; the binders' types are
                   spelled with and without "ProofFile.". THEY ARE ONE TERM: an equation, by unfolding
  jobs_at_head_seat  so jobs_at_head holds at the other house's list too

THE OTHER HOUSE's LAWS RANGE OVER ITS OWN lotJobs ++ wJobs (there at one datum D for both:
stands_at_job, Johnson/SendSim/Seat/AtDescStands.lean; that it has 52 entries:
Johnson/SendSim/Seat/LotCount.lean: not restated here): jobs_at_head_seat IS STATED AT THAT LIST.

PUBLIC TERMS ALONE: plans, numbers, folds and the letters no, Dt, Dd. No coin, no run, no input.

KIN, TOLD. wJobs_some (Johnson/SendSim/Seat/AtDescStands.lean): where the description's maker
returns, wJobs is one job at SOME message msg that linMessageW gives. Here the head says WHICH:
msg_w_head (FitsAtW.lean). The same step, one storey up, at the halves: our wHalves_head
(HalfAtW.lean); the other house's wHalves_eq (Johnson/SendSim/Seat/LotW.lean) says that wHalves is
placeHalf over wJobs. BENEATH lotJobs_one: that house's lotHalves_eq (Johnson/SendSim/Seat/Lot.lean)
and our lotHalves_jobs (Honest/K1/LotJobs.lean) are one statement at the two names.
Both stand, and so do the two definitions lotJobs: lotJobs_one says that these are one term,
and jobs_at_head_seat stands on it.

Limits. WHICH DATA Dt AND Dd ARE IS NOT SAID: THEY ARE LETTERS: a filling's to lay. AT THE
DESCRIPTION's OWN GROUND Bs.G₀: that a prover's ground is this one is not said here. THAT ANY
FILLING CALLS lotJobs OR wJobs IS NOT SAID HERE. THE FULL SIZE ALONE; the format's second hash function
alone. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.LotJobsAtHead
import Johnson.Desc.ProofFile.Honest.K1.Law.LotsAtAll
import Johnson.Desc.ProofFile.Honest.K1.Law.FitsAtW
import Johnson.SendSim.Seat.LotW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Law (wMsgFull)
open OnBytes.Maker (WholeD)
open OnBytes.SendSim.Seat (wJobs)
open _root_.Desc.K14.Law (seatZ secondAt)

variable {Xi X : Type}

/-- The plan of the job at W's sending: LotsAtAll.lean's hPw at that letter. -/
theorem w_plan_head (Zp : ProofFile.Pub) (first : ℕ) (Dd : RowDataOf Xi) :
    (wJobAt (X := X) Zp.first (wGp Zp) 4 wMsgFull first Dd).P =
      K1.parW Zp.first (wGp Zp) 4 wMsgFull :=
  rfl

/-- The plan of the opening's job: LotsAtAll.lean's hP₂ at that letter. -/
theorem two_plan_head (Zp : ProofFile.Pub) (G : ProofFile.Ground) (first : ℕ) (Dd : RowDataOf Xi) :
    (placeJob (X := X) (K1.firstPar G.first (K1.gpOf Zp)) first (firstFold G.first) Dd).P =
      K1.firstPar G.first (K1.gpOf Zp) :=
  rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x₀ : First.Look.Place} {Bs : ProofFile.PureBase}
  {base₀ : List (Block S ProofFile.Cl)}

/-- **UNDER THE HEAD wJobs IS ONE JOB, AT THE WRITTEN MESSAGE.** -/
theorem wJobs_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np))
    (no : Place → Nat) (Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) (G : ProofFile.Ground) :
    wJobs (X := X) no Dd Zp G =
      [wJobAt Zp.first (wGp Zp) 4 wMsgFull (no ⟨1, none, 4, .K1⟩) (Dd Zp G)] := by
  unfold wJobs
  rw [msg_w_head h O]
  rfl

/-- **THE 52 JOBS OF THE TWO LISTS ARE k1MembersW's, IN ORDER, AT THREE WRITTEN LETTERS.** -/
theorem jobs_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np))
    (no : Place → Nat) (Dt Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) :
    lotJobs (X := X) no Dt Zp Bs.G₀ ++ wJobs (X := X) no Dd Zp Bs.G₀ =
      (k1MembersW
        (placeJob (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) (no ⟨1, some 0, 1, .K1⟩)
          (firstFold Bs.G₀.first) (Dt Zp Bs.G₀))
        (fun l d => laterJobAt Bs.G₀.first (K1.gpOf Zp) l (IM.k1Ix l d + 1) (if d then 2 else 1)
          (no ⟨1, some l, IM.k1Ix l d + 1, .K1⟩) (Dt Zp Bs.G₀))
        (wJobAt Zp.first (wGp Zp) 4 wMsgFull (no ⟨1, none, 4, .K1⟩) (Dd Zp Bs.G₀))).map (·.2) := by
  rw [lotJobs_at_head h O no Dt, wJobs_at_head h O no Dd Bs.G₀]
  unfold k1MembersW
  rw [List.map_append]
  rfl

/-- **THE TWO DEFINITIONS NAMED lotJobs ARE ONE TERM.** -/
theorem lotJobs_one (no : Place → Nat) (Dt : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) (Zp : ProofFile.Pub)
    (G : ProofFile.Ground) :
    OnBytes.SendSim.Seat.lotJobs (X := X) no Dt Zp G = lotJobs (X := X) no Dt Zp G :=
  rfl

/-- **jobs_at_head AT THE OTHER HOUSE's LIST.** -/
theorem jobs_at_head_seat (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np))
    (no : Place → Nat) (Dt Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) :
    OnBytes.SendSim.Seat.lotJobs (X := X) no Dt Zp Bs.G₀ ++ wJobs (X := X) no Dd Zp Bs.G₀ =
      (k1MembersW
        (placeJob (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) (no ⟨1, some 0, 1, .K1⟩)
          (firstFold Bs.G₀.first) (Dt Zp Bs.G₀))
        (fun l d => laterJobAt Bs.G₀.first (K1.gpOf Zp) l (IM.k1Ix l d + 1) (if d then 2 else 1)
          (no ⟨1, some l, IM.k1Ix l d + 1, .K1⟩) (Dt Zp Bs.G₀))
        (wJobAt Zp.first (wGp Zp) 4 wMsgFull (no ⟨1, none, 4, .K1⟩) (Dd Zp Bs.G₀))).map (·.2) := by
  rw [lotJobs_one]
  exact jobs_at_head h O no Dt Dd

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.w_plan_head
#print axioms ProofFile.Honest.K1.two_plan_head
#print axioms ProofFile.Honest.K1.wJobs_at_head
#print axioms ProofFile.Honest.K1.jobs_at_head
#print axioms ProofFile.Honest.K1.lotJobs_one
#print axioms ProofFile.Honest.K1.jobs_at_head_seat
