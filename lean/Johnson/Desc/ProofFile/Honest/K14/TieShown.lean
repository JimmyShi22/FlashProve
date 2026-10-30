-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/TieShown.lean: kind K14: THE TIE: WHAT THIS KIND's PART OF A
SENDING SHOWS (sendingPart, Honest/K14/Sendings.lean, played alone by the frame: Side.shows,
Honest/Side.lean) IS THE SHARED SENDING's TWO MOVES, WRITTEN OUT (shownR,
Johnson/SendSim/At/Sim.lean), at the job's own parameters, at the data made of the job's vectors at
the stand in front of the part, AT THE SAME COINS, NUMBER BY NUMBER: WHERE THE JOB'S SHAPES FIT, THE
SUB-PROTOCOL DECLARES THE PART'S TWO ROUNDS, AND THE JOB'S VECTORS ARE THE SAME IN BOTH ROUNDS
(SameData). One statement with its proof. AN EQUATION AT EACH VALUE OF THE COINS: no distribution
occurs; no property is claimed.

  shows_tie       **the tie**, general in the job

BY NUMBER. The two texts state their counts of coins by two sums. These are equal (due_tie,
Honest/K14/TieCounts.lean), each message's coins begin at one number in both (start_tie), and the
coins are read at the other count with every coin's number kept (recount, Honest/K14/TieCoins.lean:
recount_e, recount_cut, recount_cutAll). So whatever a book of coins cuts off the part's coins by
numbers is cut off the same coins in the shared text (a sentence on recount_cut and recount_cutAll,
which nothing calls so far: no theorem draws it).

How. What the part shows, written out: shows_send (Honest/K14/FreshShows.lean). The tables are the
same as values: sentTables_tie (Honest/K14/TieColumns.lean) at rows_tie (Honest/K14/TieRows.lean).
The second round's items: answers_tie (Honest/K14/TieAnswers.lean).
What is assumed. sendShapeFits J = true: the public test on the sending's shapes. SendDeclared: the
part's messages fit what the sub-protocol states: just two rounds, oracle messages in the first
alone, nothing opened and nothing stored. SameData at the challenges heard: this kind's part reads
its vector anew in each round; the shared sending's reads what stands in front of the part in both.
NOT ASKED: which rounds are declared beyond that; a bound on positions; that a seed's factor is not
0: the equation WITH shownR holds at every pair of challenges and every list of positions. BUT
shownR is the shared part's two moves WRITTEN OUT; that that part, played, shows it: play_send
(Johnson/SendSim/At/Shows.lean), where its test accepts (fits_tie, Honest/K14/TieCounts.lean) and
the first challenge holds just the seeds; at another challenge that part stops, and this kind's does
not.
Limits. Nothing on a distribution, on a simulator, on roots, salts or paths. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.K14.TieAnswers
import Johnson.Desc.ProofFile.Honest.K14.TieColumns
import Johnson.Desc.ProofFile.Honest.K14.FreshShows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes.SendSim.At (shownR asked)

variable {S Cl X Pb W : Type}

/-- **THE TIE.** What this kind's part of a sending shows is the shared sending's two moves, written
out (shownR), at the job's parameters, at the data made of the job's vectors at the stand in front
of the part, at the same coins, number by number: where the job's shapes fit, the sub-protocol
declares the part's two rounds, and the job's vectors are the same in both rounds (SameData). That
the shared part, played, shows shownR: play_send, only where the first challenge holds just the
seeds. An equation at each value of the coins. -/
theorem shows_tie (J : SendJob) (hfit : sendShapeFits J = true) (wit : W → Ask)
    (φ : Face Empty W Pb) (σ : Side S Cl Empty W X Pb) (sim : Sim Pb)
    (hd : SendDeclared σ.block J) (m : Mid W X) (hsame : SameData J m.st.heard)
    (x₀ x₁ : Fmt.Drawn) (asks : List (List (List Nat))) (c : Cs (sendingPart J).takes) :
    σ.shows φ (sendingMember σ J wit sim) (c, (), ()) m [x₀, x₁] asks =
      some (shownR J.Q 0 (rideBySort J)
        (vecData J { input := wit m.st.input, heard := m.st.heard, own := () }) [x₀, x₁] asks
        (recount (due_tie J hfit) c)) := by
  have h := shows_send J wit σ sim hd φ (c, (), ()) m x₀ x₁ asks
  refine h.trans (congrArg some ?_)
  unfold shownR
  rw [answers_tie J hfit c (wit m.st.input) m.st.heard hsame x₀ x₁]
  unfold sendTablesAt
  rw [sentTables_tie J.Q _ _ (rows_tie J hfit c
    { input := wit m.st.input, heard := m.st.heard, own := () })]
  simp only [List.zipIdx_map, List.map_map, asked, Function.comp_def]
  rfl

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.shows_tie
