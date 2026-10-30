-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Own/SaysYesOwn.lean

`SaysYes` AT A SEATED PROXIMITY TEST WHERE THE FIRST FOLD SENDS ITS OWN FRESH TABLE, AND BEHIND THE
GUARD. The fellow of `saysYes_seat` (SaysYesSeat.lean in the folder above), whose `K12At` cannot be met
there: `OldAt` asks every tree of the job to have been sent before the test.

  `K12AtO`           `K12At` with `opens` through `OldAtO` and the fold's tree (ColsTermOwn.lean)
  `saysYes_seat_own` `SaysYes` at the plain half `proverSideOfProximityTest J`
  `saysYes_seat_guarded`   the same at the half behind the guard, under hopen (FieldGuardLift.lean)

By what. The proof of `saysYes_seat`, with `cols_term_own` in the place of `cols_term`.

HOW EACH PREMISE WOULD BE PAID AT jobKO (E2E/KeyHalves.lean), n := 2.
- hb: `omegaEntry_sits`, and the tie of the chain's member 10 to the job: OPEN, the like of `seat_nine`.
- hst, hk: closed lines at `piKOFull`: not typed. h1, hr1: the same.
- hf of `saysYes_seat_guarded`: proverSideOfTestOnOmega is `(proverSideOfProximityTest …).needsField` by its text; that it is the first
  at the place in the key's shared list: OPEN.
- hopen: NOT THE LETTER's DEBT AT THIS RUNG. At a field that is none the guarded play does not return
  (`play_guarded_none`, and every step of `proverSideOfProximityTest J` has a move), so `SaysYes`'s own premise on play
  fails there, and `SaysYes` is TRUE FOR NOTHING. Hence `SaysYes`, and `AcceptedS` after it, can be
  had for nothing at 10 at any letter that keeps the field at none: A YES THERE WOULD BE EMPTY. What
  the letter owes is `ho` inside `enters`: WHICH columns the field holds. That already gives hopen.
- HA, field by field: agree: `agree_of_tiesO`, `ties_O`, `rowsMu_many`. count:
  `planPlays_KO`, `length_test`. opens: ColsTermOwn.lean's head. enters: a twin of
  `enters_nine`, with `door_of_opened`, asks the letter: OPEN. accepts: `accepts_of_plan_own`, with its
  own open premises; `Seat.leave` returns by text.
OF THE JOB AND THE PLACE, no premise is known to be unmeetable. OF THE LETTER A: hopen, enters and
E.sent = 7 are premises on A, not on the job. At the letters that stand typed today hopen FAILS:
`PlayedTo` keeps the field at none, and `Thr` does not read it. So this holds only at some letter that
binds the field, and none is typed at the key. What speaks for one: the walk's start has the field
at some, and `fold_at_stand` gives the field with the fold's return, at the proof file's description,
joined to nothing at the key. E.sent = 7 is asked at every state where A holds: `opens_O_sent` says no
at 8, so A must bind its fourth argument.
WHAT IS MET. Outright: hF, by `fresh_tree_atOmega` and `treeAt_own`; the second half of `accepts`; hst, hk,
h1, hr1 by closed numbers, not typed here. A trial named above is a closed Bool at a place or a
copy, NOT fields of `K12AtO`: `opens_O` still wants `opensFit_of_B`, the job's flag and E.sent = 7;
`ties_O` wants the book, two members, hrows and the lending; `planPlays_KO` wants `length_test`.

Limits. The limits of SaysYesK12.lean and SaysYesSeat.lean hold here too: HA is handed four of
`YesGiven`'s ten fields, so it asks `K12AtO`, `accepts` and `OldAtO.cols` in it, also at runs where
`chainSteps`, `play` or `fillCols` do not return; `SaysYes` is vacuous where one of these errs; `planOk`
is not read. Of t' and s' nothing is said: member 11 asks `untestedL` at that state, by another
road. HA hands `drawsFit` at the block's rounds, while
`formAsks_of_draws` wants those of `laidOf`: the bridge is `k12_rounds`, under `planOk`. hF stands inside
the «there are» of `opens` though it reads neither. Conditionals. A is free: with a false A it says
nothing, and see hopen above. No thread here: `AcceptedS` wants one more rung. Nothing on completeness, on soundness or on
what is hidden.

NOT IN FRONT OF A LAW OVER COINS: `saysYes_seat_own`, `saysYes_seat_guarded` bear this label; the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean. Their ground: the letter A, as a free premise, `SaysYes` as an end. None: the bar is flat.
-/
import Johnson.Desc.ProofFile.Honest.K12.SaysYesSeat
import Johnson.Desc.ProofFile.Honest.K12.Own.ColsTermOwn
import Johnson.Desc.ProofFile.Honest.K12.FieldGuardLift

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Own
open OnBytes OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open ProofFile.Honest.Small (colGroups saysYes_of_play zip_length)

variable {S Cl V W X Pb : Type}

/-- `K12At` where the job's tree number n is the one that the test's round 1 sends. -/
structure K12AtO (J : TestJob W X) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (n : ℕ) (st : S) (m : Mid W X) (E : Env)
    (ds : List Fmt.Drawn) (c : RowCoins [(firstPart J : Part V W X), restPart J]) : Prop where
  agree : Agree J m.st.input (frontOf m) J.s₀ (firstRd J c.1) (restCoins J c.2.1)
  count : (testAll J m.st.input (frontOf m) (restCoins J c.2.1) (byNo ds)).rs.length =
    (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds.length
  opens : ∃ depths src₀,
    (J.trees₀ m.st.input (frontOf m) (restCoins J c.2.1).mem
      (J.first m.st.input (frontOf m) (restCoins J c.2.1))).map (·.1) = depths ∧
    OpensFit J (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds depths src₀ E.sent ∧
    OldAtO E (J.trees₀ m.st.input (frontOf m) (restCoins J c.2.1).mem
      (J.first m.st.input (frontOf m) (restCoins J c.2.1))) src₀ n ∧
    ∀ x, x < 2 ^ ((J.trees₀ m.st.input (frontOf m) (restCoins J c.2.1).mem
        (J.first m.st.input (frontOf m) (restCoins J c.2.1))).getD n (0, fun _ => [])).1 →
      ((J.trees₀ m.st.input (frontOf m) (restCoins J c.2.1).mem
        (J.first m.st.input (frontOf m) (restCoins J c.2.1))).getD n (0, fun _ => [])).2 x =
        treeAt J m.st.input (frontOf m) (restCoins J c.2.1) (byNo ds) 1 x
  enters : enter st = .ok (J.rec₀ m.st.input (frontOf m))
  accepts : ∃ t', (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).decide (J.rec₀ m.st.input (frontOf m))
    ((testAll J m.st.input (frontOf m) (restCoins J c.2.1) (byNo ds)).rs.map noDigest)
    (testAll J m.st.input (frontOf m) (restCoins J c.2.1) (byNo ds)).gs = .ok t' ∧
    ∃ s', leave st t' = .ok s'

/-- **`SaysYes` at every block b with `SeatOf b J enter leave`, where the job's tree number n is the
one that the test's round 1 sends.** h1, hr1: round 1 sends a tree.
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem saysYes_seat_own (φ : Face V W Pb) (Bk : ProverCoinCounts) (chain ft : ℕ) (hs : List (Placed V W X))
    (b : Block S Cl) (J : TestJob W X) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (hb : SeatOf b J enter leave)
    (fall : S → List Fmt.Drawn → Option String) (A : Coins Bk → S → Mid W X → Env → Prop)
    (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: t :: rest)
    (hk : s.k = (sgOf s).h + (sgOf s).g) (n a₁ : ℕ) (h1 : depthAt J 1 = some a₁)
    (hr1 : 1 < (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds.length)
    (hf : (hs.find? fun g => g.place == J.p.place) = some (proverSideOfProximityTest J))
    (HA : ∀ k st m E ds (c : RowCoins [(firstPart J : Part V W X), restPart J]), A k st m E →
      drawsFit (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds ds = true → fall st ds = none →
      lendRow Bk (Bk.rowsOf chain) (k.look chain) J.p.place [(firstPart J : Part V W X), restPart J]
        0 = .ok c → K12AtO J enter leave n st m E ds c) :
    SaysYes φ Bk chain ft hs b fall A := by
  have hpl := hb.place
  refine saysYes_of_play (g := proverSideOfProximityTest J) (by rw [hpl]; exact hf) fun k st m E ds c y cols h => ?_
  have hlent := h.lent
  rw [hpl] at hlent
  have hdr := h.draws
  rw [hb.rounds] at hdr
  obtain ⟨ag, cnt, ⟨depths, src₀, hdep, hO, hE, hF⟩, hen, ⟨t', hacc, s', hlv⟩⟩ :=
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
  have q3 := cols_term_own J m.st.input (frontOf m) (restCoins J c.2.1) ds s (t :: rest) hst
    (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds depths src₀ E y.1 n a₁ hdep hO hE h1 hr1 hF q2
    (drawsFit_length _ _ hdr)
  refine ⟨s', ?_⟩
  rw [hb.decide, hb.rounds, hen, q1, q3]
  show ((proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).decide _ _ _).bind (leave st) = .ok s'
  rw [hacc]
  exact hlv

/-- **The same at the half behind the guard**, wherever A holds the field being some (hopen).
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem saysYes_seat_guarded (φ : Face V W Pb) (Bk : ProverCoinCounts) (chain ft : ℕ)
    (hs : List (Placed V W X)) (b : Block S Cl) (J : TestJob W X) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (hb : SeatOf b J enter leave)
    (fall : S → List Fmt.Drawn → Option String) (A : Coins Bk → S → Mid W X → Env → Prop)
    (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: t :: rest)
    (hk : s.k = (sgOf s).h + (sgOf s).g) (n a₁ : ℕ) (h1 : depthAt J 1 = some a₁)
    (hr1 : 1 < (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds.length)
    (hf : (hs.find? fun g => g.place == b.place) = some (proverSideOfProximityTest J : Placed V W X).needsField)
    (hopen : ∀ k s m E, A k s m E → m.opened.isSome = true)
    (HA : ∀ k st m E ds (c : RowCoins [(firstPart J : Part V W X), restPart J]), A k st m E →
      drawsFit (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds ds = true → fall st ds = none →
      lendRow Bk (Bk.rowsOf chain) (k.look chain) J.p.place [(firstPart J : Part V W X), restPart J]
        0 = .ok c → K12AtO J enter leave n st m E ds c) :
    SaysYes φ Bk chain ft hs b fall A := by
  have hp : ((proverSideOfProximityTest J : Placed V W X).place == J.p.place) = true := by
    show (J.p.place == J.p.place) = true
    exact beq_self_eq_true _
  have f1 : ([proverSideOfProximityTest J].find? fun g => g.place == J.p.place) =
      some (proverSideOfProximityTest J : Placed V W X) := by
    simp [List.find?, hp]
  have f2 : ([proverSideOfProximityTest J].find? fun g => g.place == b.place) =
      some (proverSideOfProximityTest J : Placed V W X) := by
    rw [hb.place]
    exact f1
  exact saysYes_guarded (proverSideOfProximityTest J) hf f2 hopen
    (saysYes_seat_own φ Bk chain ft [proverSideOfProximityTest J] b J enter leave hb fall A s t rest hst hk n a₁ h1
      hr1 f1 HA)

end ProofFile.Honest.K12.Own

#print axioms ProofFile.Honest.K12.Own.K12AtO
#print axioms ProofFile.Honest.K12.Own.saysYes_seat_own
#print axioms ProofFile.Honest.K12.Own.saysYes_seat_guarded
