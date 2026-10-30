-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/Lots/K2RoundsNamed.lean: THE CODE SWITCH's LOT's SECOND ROW (K2Rounds.lean) WITH
THE NAME AS A FUNCTION OF THE BLOCK's PLACE: each block b of the lot has no round, or its declared
rounds are `listAt (nameW b.place)` (`nameW`: the written name at a place,
Johnson/Desc/ProofFile/Law/Skel/Full/Names.lean). No place and no list of places stands in the
conclusion. NO BLOCK IMPORTS THIS FILE.
  k2NamedOk             the test: at every place that has its numbers, the kind's two rounds are the
                        table's list at the written name of that place
  k2_named_closed       THE CLOSED FACT, BY LEAN's KERNEL, at the written places, the written sizes
                        and the number 0: the test says yes. One fact for all 25 lists. That the
                        «all» runs over every written place of the kind, 25 of them, is
                        K2Rounds.lean's k2_made_names and k2_made_count
  k2_named_tree_one · k2_named_swapped    NEGATIVE FACTS, BY THE KERNEL: with the number 1 for 0 ·
                        with two switches' names exchanged in the table: the test says no
  k2_lists_named_prep   THE ROW, under K2Rounds.lean's hs, hP and hF: from the general law
                        k2_lot_rounds and the closed fact
  k2_lists_named        THE ROW, under hs, hz, t1 … t5 and hF
  k2_lists_named_made   with hF paid where the plain road makes the public part
  k2_lists_named_at_blank    and with t1, t2 read at the public part's own first chain (u1, u2),
                        where the blank records are made: every hypothesis is on the public part
                        alone, or is one of the two returns
  k2_lists_named_whole  under the first row's hH besides: «no round» is barred
`nameW` looks a place up in one written list of places (`spotsW`,
Johnson/Desc/ProofFile/Law/Skel/Full/Data.lean); hs speaks of another (`spotsWritten`,
Johnson/AtFull/Desc/SpotsWritten.lean). THAT THE TWO ARE ONE LIST IS NEITHER SPENT NOR SHOWN HERE:
the closed fact asks `nameW` at the 25 places themselves.
LIMITS. At a place that `spotsW` has not, `nameW` is the empty name, at which `listAt` bears the
empty list: there the second arm would say no more than the first. At the lot's 25 places it does
not bite: the closed fact lays two rounds against each list. Those of K2Rounds.lean, all: THE ROW
ALONE LETS EVERY BLOCK BE WITHOUT A ROUND; that any public part and ground meet the hypotheses
together is shown nowhere here: THE ROW MAY BE IDLE; THERE IS NO EXAMPLE.

Both lists of places were printed off the routine that they describe. The full size
alone. No soundness is claimed.
-/
import Johnson.AtFull.Desc.Lots.K2Rounds
import Johnson.Desc.ProofFile.Law.Skel.Full.Names
import Johnson.Desc.K1.Law.FirstMakeFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Lots.K2
open P1K2
open OnBytes OnBytes.Model OnBytes.Params OnBytes.Plan
open ProofFile (Pub Ground Spot spotsOf)
open ProofFile.Sk.Full (nameW)
open VerifiableInference.Desc.First.K2 (rounds headPlanOk)
open VerifiableInference.PlanWritten (proofSizedFull)
open Johnson.AtFull.Desc (spotsWritten)
open Johnson.AtFull.Rounds (listAt)

/-- The test: at every place that has its numbers, the kind's two rounds are T's list at the
written name of that place. -/
def k2NamedOk (sps : List Spot) (Pq : Option Prep) (ft : Nat)
    (T : String → List Fmt.DeclaredRound) : Bool :=
  (madeW sps Pq).all fun x => decide (rounds (p2Ft ft x.1 x.2) = T (nameW x.1.place))

set_option maxRecDepth 1000000 in
/-- **THE CLOSED FACT.** -/
theorem k2_named_closed : k2NamedOk spotsWritten (prepW proofSizedFull) 0 listAt = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The number of the chain's first tree turned: 1 for 0. -/
theorem k2_named_tree_one : k2NamedOk spotsWritten (prepW proofSizedFull) 1 listAt = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Two switches' names exchanged in the table. -/
theorem k2_named_swapped : k2NamedOk spotsWritten (prepW proofSizedFull) 0
    (fun n => listAt (if n == "A1:1" then "G2:1" else if n == "G2:1" then "A1:1" else n)) =
      false := by decide +kernel

/-- **THE ROW, at the written name of the block's place, under what the rounds read.** -/
theorem k2_lists_named_prep {Zq : Pub} {G : Ground} (hs : spotsOf Zq.cuts = some spotsWritten)
    (hP : prepOf Zq G = prepW proofSizedFull) (hF : Zq.P.firstTree = 0) :
    ∀ b ∈ (ProofFile.k2Pure Zq).blocks G, b.rounds = [] ∨ b.rounds = listAt (nameW b.place) := by
  intro b hb
  rcases k2_lot_rounds Zq G b hb with h0 | ⟨x, hx, hxp, hxr⟩
  · exact Or.inl h0
  · rw [hs, hP] at hx
    simp only [Option.map_some, Option.getD_some] at hx
    have c := k2_named_closed
    unfold k2NamedOk at c
    have k := List.all_eq_true.1 c x hx
    simp only [decide_eq_true_eq] at k
    refine Or.inr ?_
    rw [hxr, hF, hxp]
    exact k

/-- **THE ROW, under the first row's hypotheses by field.** -/
theorem k2_lists_named {Zq : Pub} {G : Ground} (hs : spotsOf Zq.cuts = some spotsWritten)
    (hz : Zq.p.chains.made.sized.proof = proofSizedFull)
    (t1 : proofSizedFull.request = G.first.shape) (t2 : proofSizedFull.codes = G.first.codes)
    (t3 : Zq.s₀.st.codes = proofSizedFull.codes)
    (t4 : Zq.s₀.check.frame.shape = proofSizedFull.request)
    (t5 : proofSizedFull.set.samples = Zq.P.samples) (hF : Zq.P.firstTree = 0) :
    ∀ b ∈ (ProofFile.k2Pure Zq).blocks G, b.rounds = [] ∨ b.rounds = listAt (nameW b.place) :=
  k2_lists_named_prep hs (prep_at hz t1 t2 t3 t4 t5) hF

/-- The same, where the plain road makes the public part. -/
theorem k2_lists_named_made {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Zq : Pub} {G : Ground}
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Zq) (hs : spotsOf Zq.cuts = some spotsWritten)
    (hz : Zq.p.chains.made.sized.proof = proofSizedFull)
    (t1 : proofSizedFull.request = G.first.shape) (t2 : proofSizedFull.codes = G.first.codes)
    (t3 : Zq.s₀.st.codes = proofSizedFull.codes)
    (t4 : Zq.s₀.check.frame.shape = proofSizedFull.request)
    (t5 : proofSizedFull.set.samples = Zq.P.samples) :
    ∀ b ∈ (ProofFile.k2Pure Zq).blocks G, b.rounds = [] ∨ b.rounds = listAt (nameW b.place) :=
  k2_lists_named hs hz t1 t2 t3 t4 t5 (first_tree_made hZ)

/-- The same, where the blank records are made too: t1 and t2 at the public part's first chain. -/
theorem k2_lists_named_at_blank {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Zq : Pub}
    {G : Ground} (hZ : ProofFile.pubPlain o pol lay KL = .ok Zq)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zq = some G) (hs : spotsOf Zq.cuts = some spotsWritten)
    (hz : Zq.p.chains.made.sized.proof = proofSizedFull)
    (u1 : proofSizedFull.request = Zq.first.shape) (u2 : proofSizedFull.codes = Zq.first.codes)
    (t3 : Zq.s₀.st.codes = proofSizedFull.codes)
    (t4 : Zq.s₀.check.frame.shape = proofSizedFull.request)
    (t5 : proofSizedFull.set.samples = Zq.P.samples) :
    ∀ b ∈ (ProofFile.k2Pure Zq).blocks G, b.rounds = [] ∨ b.rounds = listAt (nameW b.place) := by
  have e := ProofFile.Law.blankBy_first hG
  exact k2_lists_named_made hZ hs hz (by rw [e]; exact u1) (by rw [e]; exact u2) t3 t4 t5

/-- Beside the first row: no block of the lot is without a round. -/
theorem k2_lists_named_whole {Zq : Pub} {G : Ground} (hs : spotsOf Zq.cuts = some spotsWritten)
    (hz : Zq.p.chains.made.sized.proof = proofSizedFull)
    (t1 : proofSizedFull.request = G.first.shape) (t2 : proofSizedFull.codes = G.first.codes)
    (t3 : Zq.s₀.st.codes = proofSizedFull.codes)
    (t4 : Zq.s₀.check.frame.shape = proofSizedFull.request)
    (t5 : proofSizedFull.set.samples = Zq.P.samples) (hF : Zq.P.firstTree = 0)
    (hH : (pureLetters G 24).map headPlanOk = some true) :
    ∀ b ∈ (ProofFile.k2Pure Zq).blocks G, b.rounds = listAt (nameW b.place) := by
  intro b hb
  rcases k2_lists_named hs hz t1 t2 t3 t4 t5 hF b hb with h0 | h
  · exfalso
    have hk : ProofFile.Sk.skel b ∈ k2SkelW := by
      rw [← k2_row_spots hs hz t1 t2 t3 t4 t5 hH]
      exact List.mem_map_of_mem hb
    have h2 : ((ProofFile.Sk.skel b).nRounds == 2) = true := List.all_eq_true.1 k2_two_rounds _ hk
    have h3 : b.rounds.length = 2 := eq_of_beq h2
    rw [h0] at h3
    exact absurd h3 (by simp)
  · exact h

end Johnson.AtFull.Lots.K2

#print axioms Johnson.AtFull.Lots.K2.k2_named_closed
#print axioms Johnson.AtFull.Lots.K2.k2_named_tree_one
#print axioms Johnson.AtFull.Lots.K2.k2_named_swapped
#print axioms Johnson.AtFull.Lots.K2.k2_lists_named_prep
#print axioms Johnson.AtFull.Lots.K2.k2_lists_named
#print axioms Johnson.AtFull.Lots.K2.k2_lists_named_made
#print axioms Johnson.AtFull.Lots.K2.k2_lists_named_at_blank
#print axioms Johnson.AtFull.Lots.K2.k2_lists_named_whole
