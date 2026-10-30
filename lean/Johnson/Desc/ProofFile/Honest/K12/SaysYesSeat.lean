-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/SaysYesSeat.lean: the statement of `saysYes_k12` (SaysYesK12.lean
in this folder) is proved at every block that has a proximity test's place, rounds and oracle
messages and whose decision is the test's between two functions `enter` and `leave`: at every type
of claims and under every name. `saysYes_k12` itself is stated at one such block,
`Block.inside enter (proximityTestKind guardedProximityTestParts J.p) leave` with `Unit` as the type of claims. A file's chain has
the test as a block that the file builds itself: the key file's test on the ranges, `rangesTest`
(Johnson/Desc/Key/Ranges.lean), is such a `Block.inside` under another name, with one more test on
the plan (the field `planOk`), and is general in the type of claims. Of a block, `SaysYes` reads the
name, the place, the rounds, the oracle messages and the decision; `SeatOf` fixes the last four. A
structure and two theorems, with their proofs.

In the list: a block (`Block S Cl`, Johnson/Desc/Block.lean) is a sub-protocol at one place
(`Place`) of a description's chain; S is the type of its states, Cl the type of its claims. The job
J (`TestJob`, Test.lean in this folder) is what a caller supplies for its test; `J.p` (`P12`,
Johnson/Desc/K12/Frame.lean) has the test's parameters, among them its place and its stages
(`Fmt.M1.Stage`). The test's own block is `proximityTestKind guardedProximityTestParts J.p` (`proximityTestKind`: Johnson/Desc/K12/Frame.lean;
`guardedProximityTestParts`: Johnson/Desc/K12/JoinGuarded.lean), on states of type `T12` (Johnson/Desc/K12/Join.lean).
`Block.inside enter b leave` (Block.lean) has the name, place, rounds and oracle messages of b; its
decision calls `enter` on the state, then the decision of b, then `leave`. `SaysYes`
(Johnson/Desc/ProofFile/Honest/Law/ThreadC.lean) is a definition, meant as a hypothesis, and that
file describes it so: "outside the stops and outside its fall its own step accepts". Its parameters
and `K12At` are explained at the top of SaysYesK12.lean.

  `saysYes_seat`: under the five hypotheses below, `SaysYes φ Bk chain ft hs b fall A` holds
  `SeatOf b J enter leave`: a structure of four equations. `place`: the place of b is `J.p.place`.
    `rounds`, `oracles`: the rounds and the oracle messages of b are those of the test's own block.
    `decide`: the decision of b at a state s is `enter s`, then the decision of the test's own
    block, then `leave s`. The test's own block is taken at `Unit` as the type of claims
  `seatOf_inside`: `SeatOf` holds of `Block.inside enter (proximityTestKind guardedProximityTestParts J.p) leave`, at every type of
    claims, every job J and all `enter` and `leave`. No hypothesis

By what. `seatOf_inside`: `same_k12` (SameCl.lean in this folder: `proximityTestKind X p` has the same name,
place, rounds, oracle messages and decision at two types of claims) and `k12_place`
(SaysYesK12.lean). `saysYes_seat` goes as the proof of `saysYes_k12` does, and rewrites by the four
equations of `SeatOf`. `saysYes_of_play` (Johnson/Desc/ProofFile/Honest/Small/SaysYesOf.lean)
reduces `SaysYes` to the block's decision on the rounds as played and on `colGroups` at the tables
after the play. `played_term` (PlayedTerm.lean in this folder), which holds at every name: the
rounds as played are the rounds of `testAll` (Test.lean). `cols_term` (ColsTerm.lean): these groups
are the groups of `testAll`. The numbers of rounds: `first_moves` and `rest_moves` (HalfSteps.lean),
`zip_length` (SaysYesOf.lean), `drawsFit_length` (Johnson/Desc/ProofFile/Honest/Law/Along.lean).

Hypotheses of `saysYes_seat`. `hb`: `SeatOf b J enter leave`. The other four are those of
`saysYes_k12`, word for word. `hst`: the job has two stages or more. `hk`: at the first stage s,
`s.k = (sgOf s).h + (sgOf s).g`. `hf`: in the list hs of prover's sides (`Placed`,
Johnson/Desc/ProofFile/Honest/Frame.lean), the first at the place `J.p.place` is `proverSideOfProximityTest J`
(Parts.lean in this folder: two parts, of type `Part`, at that place). `HA`:
`K12At J enter leave st m E ds c` holds wherever A holds at k, st, m and E, the challenges ds fit
the declared rounds of the test's own block (`drawsFit`), `fall st ds` is `none`, and `lendRow`
(Frame.lean), at the book Bk (`ProverCoinCounts`, Frame.lean: public data that goes with a description), the
chain's rows and the coins k, returns c for the two parts. All other parameters are free.

Limits. The limits of SaysYesK12.lean hold here too. Among them: the proof hands `HA` four of the
ten fields of `YesGiven` (SaysYesOf.lean), so `HA` asks `K12At` at more runs than `SaysYes` speaks
of. The block's test on the plan (`planOk`) is not read. That the key file's `rangesTest` is such a
block is not shown here: `seatOf_ranges`, SeatRanges.lean (not in the library yet) in this folder.
`saysYes_k12` is `saysYes_seat` at `seatOf_inside`, with `Unit` as the type of claims; it is not
derived from it: SaysYesK12.lean has a proof of its own, so the argument is written twice. No
property of a protocol is stated: nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.SaysYesK12
import Johnson.Desc.ProofFile.Honest.K12.SameCl

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open ProofFile.Honest.Small (colGroups saysYes_of_play zip_length)

variable {S Cl V W X Pb : Type}

/-- The block b has the place `J.p.place` and the rounds and oracle messages of the test's own block
`proximityTestKind guardedProximityTestParts J.p`, and its decision is: `enter`, then that block's decision, then `leave`. The
test's own block is taken at `Unit` as the type of claims. -/
structure SeatOf (b : Block S Cl) (J : TestJob W X) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) : Prop where
  place : b.place = J.p.place
  rounds : b.rounds = (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds
  oracles : b.oracles = (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).oracles
  decide : ∀ s rs gs, b.decide s rs gs =
    (enter s).bind fun t => ((proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).decide t rs gs).bind (leave s)

theorem seatOf_inside (J : TestJob W X) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) :
    SeatOf (Block.inside enter (proximityTestKind guardedProximityTestParts J.p : Block T12 Cl) leave) J enter leave := by
  have h := same_k12 (Cl := Cl) (Cl' := Unit) guardedProximityTestParts J.p
  refine ⟨h.place.trans (k12_place J.p), h.rounds, h.oracles, fun s rs gs => ?_⟩
  show (enter s).bind (fun t => ((proximityTestKind guardedProximityTestParts J.p : Block T12 Cl).decide t rs gs).bind (leave s)) =
    _
  rw [h.decide]

/-- **`SaysYes` at every block b with `SeatOf b J enter leave`**, under the hypotheses of
`saysYes_k12` (SaysYesK12.lean). Among them is `K12At`; its field `accepts` says that the decision
of the test's own block accepts the rounds of `testAll`, under `noDigest`, with its groups, and that
`leave` returns. -/
theorem saysYes_seat (φ : Face V W Pb) (Bk : ProverCoinCounts) (chain ft : ℕ) (hs : List (Placed V W X))
    (b : Block S Cl) (J : TestJob W X) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (hb : SeatOf b J enter leave)
    (fall : S → List Fmt.Drawn → Option String) (A : Coins Bk → S → Mid W X → Env → Prop)
    (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: t :: rest)
    (hk : s.k = (sgOf s).h + (sgOf s).g)
    (hf : (hs.find? fun g => g.place == J.p.place) = some (proverSideOfProximityTest J))
    (HA : ∀ k st m E ds (c : RowCoins [(firstPart J : Part V W X), restPart J]), A k st m E →
      drawsFit (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds ds = true → fall st ds = none →
      lendRow Bk (Bk.rowsOf chain) (k.look chain) J.p.place [(firstPart J : Part V W X), restPart J]
        0 = .ok c → K12At J enter leave st m E ds c) :
    SaysYes φ Bk chain ft hs b fall A := by
  have hpl := hb.place
  refine saysYes_of_play (g := proverSideOfProximityTest J) (by rw [hpl]; exact hf) fun k st m E ds c y cols h => ?_
  have hlent := h.lent
  rw [hpl] at hlent
  have hdr := h.draws
  rw [hb.rounds] at hdr
  obtain ⟨ag, cnt, ⟨depths, src₀, hdep, hO, hE⟩, hen, ⟨t', hacc, s', hlv⟩⟩ :=
    HA k st m E ds c h.stand hdr h.noFall hlent
  have hs0 : J.s₀ = s := by
    unfold TestJob.s₀
    rw [hst]
    rfl
  rw [hs0] at ag
  have hzl := zip_length h.oracles h.rounds
  rw [hb.rounds, hb.oracles] at hzl
  have l1 : (firstPart J : Part V W X).moves.length = firstLen J.p.nums.stages := by
    rw [first_moves]
    exact (List.length_map _).trans List.length_range
  have l2 : (restPart J : Part V W X).moves.length = restLen J.p.nums.stages := by
    rw [rest_moves J s t rest hst]
    exact (List.length_map _).trans List.length_range
  have hrs : ((proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds.zip
      (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).oracles).length =
      firstLen J.p.nums.stages + restLen J.p.nums.stages := by
    refine hzl.trans ?_
    show (firstPart J : Part V W X).moves.length + ((restPart J : Part V W X).moves.length + 0) = _
    rw [l1, l2, Nat.add_zero]
  have hzr : ((proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds.zip
      (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).oracles).length =
      (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds.length := by
    have ho := h.oracles
    rw [hb.rounds, hb.oracles] at ho
    rw [List.length_zip, ho, Nat.min_self]
  have hplay : play (rowSteps b.name J.p.place (φ.sees m.st.input)
      [(firstPart J : Part V W X), restPart J] 0
      ((proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds.zip (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).oracles)
      c) ds [] m = .ok y := by
    have := h.played
    unfold Placed.steps at this
    rw [hpl, hb.rounds, hb.oracles] at this
    exact this
  obtain ⟨q1, q2, -, -, -⟩ := played_term J s t rest hst hk _ _ _ hrs c ds [] m y hplay ag
    (cnt.trans hzr.symm)
  rw [hzr] at q2
  have q3 := cols_term J m.st.input (frontOf m) (restCoins J c.2.1) ds s (t :: rest) hst
    (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds depths src₀ E y.1 hdep hO hE q2
    (drawsFit_length _ _ hdr)
  refine ⟨s', ?_⟩
  rw [hb.decide, hb.rounds, hen, q1, q3]
  show ((proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).decide _ _ _).bind (leave st) = .ok s'
  rw [hacc]
  exact hlv

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.seatOf_inside
#print axioms ProofFile.Honest.K12.saysYes_seat
#print axioms ProofFile.Honest.K12.SeatOf
