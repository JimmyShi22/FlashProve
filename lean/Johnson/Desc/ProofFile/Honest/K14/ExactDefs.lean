-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/ExactDefs.lean: kind K14: WHAT STANDS BESIDE THE PARTS OF THE TWO
SENDINGS OF THE BATCH's SHARED ROUNDS, "send o_u" and "send o_omega" (Honest/K14/Sendings.lean), in
a row of the frame for the honest side: a simulator, and a sentence at the part's entry. Definitions
alone; no theorem is stated. (The two rows themselves: Honest/K14/ExactRows.lean.)

  rideBySort      which of a sending's tables is a fold's fresh table, read off the job's own sorts
  sendingSim      THE SIMULATOR: the shared sending's own (sendSim, Johnson/SendSim/At/Sim.lean) at
                  the job's public numbers: the two moves of the shared sending's part (sendPart,
                  Honest/K1/Part.lean: ANOTHER TEXT of a sending than this kind's), played at NO
                  DATA, at coins of its own. No second text of a simulator is written here
  SameData        the job's vectors are the same in front of the part's first challenge and behind
                  it, at every input: a sentence on the job and the challenges heard
  pointApart      that sentence's form at the two sendings: the number of the round "LIN point" is
                  not the number of challenges heard
  sendingMember   the one member of a side whose row is a sending's part, written out

WHAT THE SIMULATOR READS. Its challenges, its positions, its own coins; of the place: the sending's
parameters and which tables ride: public data. By its type it is also handed the public part of the
input (in the shared rounds: the committed table's out-of-domain (OOD) seeds and answers) and what
the parts in front show: BY ITS TEXT IT READS NEITHER.

WHAT IT IS NOT. The rows beneath what it tells are laid at no data: at a real key and real stored
columns they meet none of the constraints that are laid on these messages behind the sendings
((rec_gamma), (loc_x), (fold_u), (fold_omega): Johnson/Desc/K14/Text.lean). Nothing of these rows is
handed on: what it tells reaches the simulators of the parts behind as what stands in front of them.
That each of them tells, from it, what its part shows is for each of them to show, and is not said
here.

WHY SameData. This kind's parts read their vector off the challenges heard anew in each of their two
rounds, by a number. Where just as many challenges have been heard in front of the part as that
number says, the second round reads the part's own seeds in the point's place, and the two rounds
lay two vectors. The shared sending's part reads, in both rounds, what stands in front of the part.
So in that one case the two texts of a sending lay different rows, and a law on the shared sending's
part cannot be carried over to this kind's. THE CLAUSE SERVES THAT PROOF: it is not known to be
needed for the sentences of Honest/K14/ExactStated.lean. At the two sendings SameData follows from
pointApart (sameData_u, sameData_omega, Honest/K14/ExactOfRows.lean), which reads a number and a
length alone. In the general form it is a sentence on the job and the list heard: it reads no input;
at a made-up job it can hang on a challenge's value.

Limits. Definitions. Nothing says here that the simulator tells what a part shows. The number that
the simulator is told for the first new message is 0: its answers do not hang on that number
(Honest/K14/SendingsViaAnswers.lean: answers_same). Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.SendingsPlay
import Johnson.SendSim.At.Sim

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open ProofFile.Honest.K1 (Ride)
open OnBytes.SendSim.At (sendSim)

variable {S Cl X Pb W : Type}

/-- Which tables ride, read off the job's own sorts. -/
def rideBySort (J : SendJob) (k : Nat) : Option Ride :=
  match J.sort k with
  | .fresh k' h => some { k := k', h := h }
  | .plain _ => none

/-- **THE SIMULATOR beside a sending's part**: the two moves of the shared sending's part at no
data, at the job's public numbers. By its text it reads its challenges, its positions and its coins
alone: not the public part of the input, not what the parts in front show. THE ROWS BENEATH WHAT IT
TELLS ARE LAID AT NO DATA: they meet none of the constraints that are laid on these messages behind
the sendings (Johnson/Desc/K14/Text.lean); nothing of these rows is handed on. That the simulators
of the parts behind tell, from what this one tells, what their parts show is for each of them to
show, and is not said here. -/
def sendingSim (J : SendJob) (a : Addr) : Sim Pb := sendSim J.Q 0 (rideBySort J) a

/-- The job's vectors are the same in front of the part's first challenge and behind it, AT EVERY
INPUT: a sentence on the job and the challenges heard; it reads no input. -/
def SameData (J : SendJob) (h : List Fmt.Drawn) : Prop :=
  ∀ (a : Ask) (x₀ : Fmt.Drawn) (k : Nat),
    J.data { input := a, heard := h ++ [x₀], own := () } k =
      J.data { input := a, heard := h, own := () } k

/-- The number of "LIN point" among the chain's rounds is not the number of challenges heard. -/
def pointApart (A : SendPub) (h : List Fmt.Drawn) : Prop := A.atPoint ≠ h.length

/-- The one member of a side whose row is a sending's part, written out. -/
def sendingMember (σ : Side S Cl Empty W X Pb) (J : SendJob) (wit : W → Ask) (sim : Sim Pb) :
    Member Empty W X Pb :=
  { number := 0, rounds := (σ.block.rounds.zip σ.block.oracles).take 2
    part := liftSend wit (sendingPart J), sim := sim }

end ProofFile.Honest.K14
