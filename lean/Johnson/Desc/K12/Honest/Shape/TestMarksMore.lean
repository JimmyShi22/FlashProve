-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/Shape/TestMarksMore.lean: two more marks go through a proximity test. A mark
is a Bool on a statement (`Statement`, OnBytes/Iop/Ground.lean) that is meant to be carried along a
chain of sub-protocols and not computed anew; Johnson/Desc/K12/Honest/Shape/TestMarks.lean treats
the first two, `stTidyB` and `stPlainB` (Johnson/Desc/Ground/Shape/Marks.lean). Here: where the
description's own block, `proximityTestKind guardedProximityTestParts p` (`proximityTestKind`: Johnson/Desc/K12/Frame.lean; `guardedProximityTestParts`:
Johnson/Desc/K12/JoinGuarded.lean), accepts, on whatever rounds and columns, and under two hypotheses on
the plan p: (1) the mark on sample rows (`stSamplesB`, Johnson/Desc/Ground/Shape/Samples.lean) is
kept: if it is true at the statement before the test, it is true at the statement after it
(`k12_samples_mark`); (2) the mark on the open rows (`claimsAtB`,
Johnson/Desc/Ground/Shape/Claims.lean) is kept in the same sense at every number of a group, where
the statement before the test is tidy (`k12_claims_mark`). The two theorems are meant for a later
test of the same chain; what is not stated of that is in the limits. General in p, in the structures
before and after the test, in the rounds and in the columns. One definition, `StayPad`; everything
else is a theorem. The verifier's structure alone: no prover, no coin, no frame for an honest side.

In the list: t and t' are structures inside a proximity test (`T12`, Johnson/Desc/K12/Join.lean), t
before the test or a part of it and t' after it; among their fields are the statement `st` and the
number `g` of the group under test. A statement has codes, oracle messages (`oracles`; below:
messages) and groups. A message (`Oracle`) has a shape, sample rows (`sampleRows`) and a list of pad
places (`pad`: pairs of a part and a number). A group (`Group`) has members (`members`: numbers of
messages) and open rows (`rows`). Both structures are in OnBytes/Iop/Ground.lean. "Older" is what t
has: a message or a group whose number is below the size in `t.st`. A row is plain where it passes
`rowPlainB` (Marks.lean): no tensor among its terms or in its whole coefficient vectors has a
written-out factor. `stSamplesB S` says that every sample row of every message of S is plain.
`claimsAtB S q` says: if S has a group number q, each of its open rows is no sample row and passes
`rowRestB` (Johnson/Desc/Ground/Shape/Ground.lean) at S and q; it is true where S has no group
number q. The plan p (`P12`, Johnson/Desc/K12/Frame.lean) holds the numbers of the place of the
test. A block or a part accepts where its `decide` returns `.ok` with the next structure; rs are the
rounds and gs the groups of columns that it is given. The parts of the test are the front
(`frontJ`), the batching (`batJ`), for each stage but the last a fold (`foldJ`), a switch
(`switchJ`) and the batching after it (`behindJ`), all in Join.lean, and the base case (`baseJ5`,
JoinGuarded.lean). he, ha, h, ht are the hypotheses named below. The frame for an honest side is
Johnson/Desc/ProofFile/Honest/Frame.lean.

  `k12_samples_mark`: under he, ha and h: if `stSamplesB t.st` is true, `stSamplesB t'.st` is true
  `k12_claims_mark`: under he, ha, h and ht, at every number q: if `claimsAtB t.st q` is true,
    `claimsAtB t'.st q` is true
  `k12_grown`: under he, ha, h and ht, at every number q other than `t.g`:
    `Grown (stSh t.st) (stSh t'.st) q` (`Grown`: Claims.lean; `stSh`, the shape of a statement:
    Johnson/Desc/Ground/Shape/Core.lean). That is: the codes stay; every message that was there is
    there, with its shape; if group number q was there it is there, with all members that it had,
    and at each of these members the list of pad places, read as empty where there is no such
    message, is as it was. Where t has no group number q the clause on the group is vacuous
  `StayPad S S'`: a definition: S' has no fewer messages than S, and each message of S has in S' the
    list of pad places that it has in S
  `k12_pads`: every older message's list of pad places stays. In Lean: under he, ha and h,
    `StayPad t.st t'.st`
  `StayPad.refl`, `StayPad.trans`: `StayPad` is reflexive and transitive
  `k12_keep`: for every property P of a statement and every p: if the batching, a fold, a switch
    with the batching after it (taken as one step, on at most two rounds) and the base case each
    keep P wherever they accept, from the statement before to the statement after, then so does the
    whole block
  `stages_keep`: the same for the stages from any stage on (`stagesFrom guardedProximityTestParts`,
    Johnson/Desc/K12/Frame.lean); the hypothesis on the batching is not needed
  `bat_samples`, `fold_samples`, `base_samples`: where the batching, a fold or the base case
    accepts, it keeps `stSamplesB`. No hypothesis on p
  `switch_samples`: the same for a switch and the batching after it, taken as one step, under he, ha
    and `rs.length ≤ 2`; `stages_keep` proves that bound: `stagesFrom` deals a switch two rounds at
    most
  `bat_pads`, `fold_pads`, `base_pads`, `switch_pads`: where the part accepts, `StayPad` holds from
    the statement before to the statement after; `switch_pads` under the hypotheses of
    `switch_samples`, the other three with no hypothesis on p
  `switch_did'`: under he, ha and `rs.length ≤ 2`, where a switch accepts at t1 and returns t2, and
    the batching after it accepts at t2 and returns t3: there are T, gp, others, z and a D of the
    library's structure `Taken` (Johnson/Desc/K12/Law/SwDid.lean) such that `t3.st` is
    `begun (D.stR T gp others t1.st) gp (D.grown t1.st)`, and `Send.form` (OnBytes/Iop/Send.lean) at
    the codes of `t1.st`, `T.shape`, the number `t1.st.oracles.size`, the seed `⟨z, D.beta⟩` and the
    answer number 0 returns `D.smp`
  `samples_idx`: `stSamplesB S` is true if and only if, at every number at which S has a message,
    each of that message's sample rows passes `rowPlainB`
  `modify_pad`: `Array.modify` by a function that keeps `pad` keeps the list of pad places at every
    number
  `shut_pad`, `begun_pad`: `closeLedgers S l` and `begun S g G` (both: OnBytes/Slice/BlkBegin.lean)
    have at every number the list of pad places that S has

By what. The block's accept is cut into its parts' accepts in `k12_keep` and `stages_keep`, by
`k12_ok`, `stagesFrom_ok`, `stagesFrom_last` (Johnson/Desc/K12/FrameLaws.lean), `like_P5`
(Johnson/Desc/K12/Law/OutK.lean: an accept of a part of `guardedProximityTestParts`, the base case apart, gives an
accept of the part of Join.lean) and, for the base case, `ranged_ok`
(Johnson/Desc/K12/Law/BaseGives.lean); the front returns the structure that it is given. What a part
leaves: `bat_form` (Johnson/Desc/K12/Honest/Shape/TestKeeps.lean); `foldJ_form`, `spendP_form`
(Johnson/Desc/K12/Law/OutK2.lean) and `recvP_ok` (Johnson/Desc/K12/Law/SwUnfold.lean); the text of
`baseJ5`, unfolded; `switch_did'`, which calls `switchE_two` (OutK.lean) and `switchUnfolds`
(SwUnfold.lean).
(1) goes as `k12_plain_mark` (TestMarks.lean) does, and reads the messages only: `orcs_shut`,
`orcs_modify`, `orcs_sent` (Samples.lean). In `switch_samples`, an older message has the sample rows
that it had, and a message that comes with the switch has none, but for the first of them:
`begun_rows`, `modify_other` (TestKeeps.lean), `withRows_oracles` (OnBytes/Slice/BlkCalls.lean),
`joined_sampleRows`, `ledgerShut_sampleRows`, `admitted_sampleRows` (OnBytes/Slice/BlkCsRun.lean),
`stSent_old`, `stSent_new` (OnBytes/Slice/BlkStLaws.lean). The one sample row that a switch admits
is plain by the library's `plainRow_form` (OnBytes/Slice/BlkPlain.lean).
(2) `k12_claims_mark` goes by cases on q, over the library's `k12_out2` (OutK2.lean). At `t.g` the
group has no open row after the test (field `begunG`). At another older group, the group is
unchanged (`others`), and `claims_keep` (Claims.lean) is called at `k12_grown`. At any other q, t'
has no such group, or a group that came with the test and has no open row (`groupsN`, `groupsNew`).
`k12_grown`: the codes and the shapes by the library's `k12_out` (OutK.lean); the group by `others`;
that a member is a message of t by `tidy_of` (Marks.lean) and the field `members` of `Tidy`
(Johnson/Desc/Means/Walk.lean); the pads by `k12_pads`. The pads: shown here, part by part. These
proofs take the sizes from `bat_stay`, `fold_stay`, `base_stay`, `switch_stay` (TestKeeps.lean) and
call `closeLedgers_get` (OnBytes/Slice/BlkProxEarlierMessagesAndGroups.lean), `withRows_oracles`, `stSent_old` and
`modify_other`.

Hypotheses. he: `p.early = true`. ha: `p.answers = 1`. h:
`(proximityTestKind guardedProximityTestParts p).decide t rs gs = .ok t'`: the block accepts at t and returns t'. ht, of
`k12_grown` and `k12_claims_mark`: `stTidyB t.st = true`: the first mark at the statement before the
test. hp, of `k12_samples_mark`, and hc, of `k12_claims_mark`: the mark in question is true at the
statement before the test.

Limits.
- Premises: the masks come early and a sample has one answer. In Lean: he and ha.
- (2) has the first mark at the statement before the test as a hypothesis (ht). Of it the proof uses
  only that every member of a group is a message that is there.
- At the group under test, and at the groups that the test itself brings, the mark is true after the
  test for want of an open row: there `k12_claims_mark` carries nothing over, and hc is not used. At
  a number q at which t' has no group the mark is true by its definition.
- `k12_grown` states nothing at `t.g`.
- `StayPad` and `k12_pads` speak of older messages only: nothing is stated of the pad places of a
  message that comes with the test.
- In `k12_keep` and `stages_keep`, P is a property of the statement only: not of the other fields of
  `T12`, so not of what passes inside a test from a part to the next.
- One direction only: from an accept to the marks. Where the block refuses, the theorems are
  vacuous. No accept is shown here, and neither mark is shown to be true at any structure.
- That a later test of the same chain finds the two marks is not stated here. Nothing here treats
  the steps of a chain between two tests. The theorems of
  Johnson/Desc/K12/Honest/Shape/TestDoor.lean on a test's door (`door_of_shape`,
  `door_of_shape_own`; the door: the front, the batching, the question of `proximityTestKind` whether the group is
  the first stage's, and the first fold) have neither mark as a hypothesis. They have `claimsB t`,
  which `claimsB_of_mark` (Johnson/Desc/K12/Honest/Shape/TestClaims.lean) derives from `claimsAtB`
  at the group under test where that group is there and no test of it has begun. And they have that
  every row that the test takes in is plain, which `stSamplesB` gives of the members' sample rows
  only.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.Shape.TestMarks
import Johnson.Desc.Ground.Shape.Samples
import Johnson.Desc.Ground.Shape.Claims

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Sh
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.Out (like_P5 foldJ_form spendP_form)
open H2K.FoldLaw (bind_ok)
open H2K.JointK H2K.Sw

/-! ## 1 The mark on sample rows -/

/-- The mark by numbers: `stSamplesB S` is true if and only if, at every number at which S has a
message, each of that message's sample rows passes `rowPlainB`. -/
theorem samples_idx {S : Statement} : stSamplesB S = true ↔
    ∀ (o : Nat) (rows : Array OnBytes.Row), (S.oracles[o]?).map (·.sampleRows) = some rows →
      ∀ r ∈ rows.toList, rowPlainB r = true := by
  unfold stSamplesB
  rw [orcs_iff]
  constructor
  · intro h o rows ho
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 ho
    obtain ⟨hq, rfl⟩ := Array.getElem?_eq_some_iff.1 hx
    exact h _ (Array.getElem_mem_toList hq)
  · intro h x hx
    obtain ⟨o, ho, rfl⟩ := List.getElem_of_mem hx
    have ho' : o < S.oracles.size := by simpa using ho
    exact h o _ (by rw [Array.getElem?_eq_getElem ho']; simp)

theorem bat_samples (p : P12) (cut : List Fmt.DeclaredRound) (t t1 : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (batJ p cut).decide t rs gs = .ok t1) (hp : stSamplesB t.st = true) :
    stSamplesB t1.st = true := by
  obtain ⟨G, row, L, m, _, rfl⟩ := bat_form p cut t t1 rs gs h
  exact orcs_shut _ t.st hp

theorem fold_samples (p : P12) (j : Nat) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound)
    (t t1 : T12) (rs : List Fmt.RoundView) (gs : Gs) (h : (foldJ p j cur cut).decide t rs gs = .ok t1)
    (hp : stSamplesB t.st = true) : stSamplesB t1.st = true := by
  obtain ⟨row, L, c, nn, id, d1, d', rows, _, _, hcase, hsp, rfl⟩ :=
    foldJ_form p j cur cut t t1 rs gs h
  have hd' := spendP_form hsp
  subst hd'
  rcases hcase with ⟨_, rfl⟩ | ⟨_, ids, hr, _⟩
  · exact orcs_modify (A := t.st.oracles) hp id _ fun _ x => x
  · obtain ⟨lay, _, _, _, rfl⟩ := recvP_ok hr
    exact orcs_modify (A := (stSent t.st _).oracles) (orcs_sent hp _) id _ fun _ x => x

theorem base_samples (p : P12) (j : Nat) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound)
    (t tE : T12) (rs : List Fmt.RoundView) (gs : Gs) (h : (baseJ5 p j cur cut).decide t rs gs = .ok tE)
    (hp : stSamplesB t.st = true) : stSamplesB tE.st = true := by
  unfold baseJ5 at h
  dsimp only at h
  split at h
  · obtain ⟨cl, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨cl', _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨m, _, h⟩ := bind_ok h
    obtain ⟨star, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨a, _, h⟩ := bind_ok h
    cases h
    exact orcs_modify (A := t.st.oracles) hp star _ fun _ x => x
  · cases h

/-- What a switch and the batching after it leave, in terms of the library's own structure `Taken`
(Johnson/Desc/K12/Law/SwDid.lean): the statement after the two; and `D.smp`, the left side of the
sample row that the switch admits, is what `Send.form` returns. -/
theorem switch_did' (p : P12) (he : p.early = true) (ha : p.answers = 1) (j : Nat)
    (cur nxt : Fmt.M1.Stage) (last : Bool) (cut : List Fmt.DeclaredRound) (t1 t2 t3 : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (hlen : rs.length ≤ 2)
    (h1 : (switchJ p j cur nxt last cut).decide t1 rs gs = .ok t2)
    (h2 : (behindJ p (j + 1) nxt cut).decide t2 [] [] = .ok t3) :
    ∃ (T : SwitchTarget) (gp : Nat) (others : Array OracleNotice) (D : Taken) (z : List E),
      t3.st = begun (D.stR T gp others t1.st) gp (D.grown t1.st) ∧
      Send.form t1.st.codes T.shape t1.st.oracles.size ⟨z, D.beta⟩ 0 = some D.smp := by
  have h1' := h1
  simp only [switchJ] at h1'
  split at h1'
  · rename_i rows gp nx e1 e2
    obtain ⟨⟨⟨out0, theta0⟩, s'⟩, hx, h1''⟩ := bind_ok h1'
    obtain ⟨r1, r2, rest, hr⟩ := H2K.Out.switchE_two hx
    have hr' : rs = r1 :: r2 :: rest := hr
    have hrest : rest = [] := by
      rw [hr'] at hlen
      simp only [List.length_cons] at hlen
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hrest
    subst hr'
    obtain ⟨out, row, L, th, D, _, _, hd, _, _⟩ :=
      switchUnfolds p j cur nxt last cut t1 t2 t3 r1 r2 gs rows gp nx he ha e1 e2 h1 h2
    exact ⟨_, gp, _, D, _, hd.st, hd.form⟩
  · cases h1'

theorem switch_samples (p : P12) (he : p.early = true) (ha : p.answers = 1) (j : Nat)
    (cur nxt : Fmt.M1.Stage) (last : Bool) (cut : List Fmt.DeclaredRound) (t1 t2 t3 : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (hlen : rs.length ≤ 2)
    (h1 : (switchJ p j cur nxt last cut).decide t1 rs gs = .ok t2)
    (h2 : (behindJ p (j + 1) nxt cut).decide t2 [] [] = .ok t3) (hp : stSamplesB t1.st = true) :
    stSamplesB t3.st = true := by
  obtain ⟨T, gp, others, D, z, hst, hform⟩ :=
    switch_did' p he ha j cur nxt last cut t1 t2 t3 rs gs hlen h1 h2
  have p2 := samples_idx.1 hp
  rw [hst]
  refine samples_idx.2 fun o rws ho => ?_
  rw [begun_rows] at ho
  unfold Taken.stR Taken.stJ Taken.stA at ho
  rw [(withRows_oracles gp D.rows _).1, joined_sampleRows, ledgerShut_sampleRows] at ho
  by_cases hid : o = t1.st.oracles.size
  · subst hid
    rw [admitted_sampleRows _ _ _ _ _ (by
      show _ < (t1.st.oracles ++ _).size
      rw [Array.size_append]
      simp [Slice.sentOf])] at ho
    obtain rfl := Option.some.inj ho
    intro r hr
    have er : r = D.sample := by simpa using hr
    rw [er]
    exact rowPlainB_iff.2 (plainRow_form _ _ _ _ _ D.smp hform)
  · have ho' : (((stSent t1.st _).oracles.modify t1.st.oracles.size _)[o]?).map
        (·.sampleRows) = some rws := ho
    rw [modify_other _ _ _ _ hid] at ho'
    rcases Nat.lt_or_ge o t1.st.oracles.size with hlt | hge
    · rw [stSent_old _ _ _ hlt] at ho'
      exact p2 o rws ho'
    · obtain ⟨i, rfl⟩ : ∃ i, o = t1.st.oracles.size + i := ⟨o - t1.st.oracles.size, by omega⟩
      rw [stSent_new] at ho'
      obtain ⟨x, hx', rfl⟩ := Option.map_eq_some_iff.1 ho'
      obtain ⟨nn, _, rfl⟩ := Option.map_eq_some_iff.1 hx'
      intro r hr
      cases hr

/-- A property of the statement that each part keeps goes through the stages. -/
theorem stages_keep (P : Statement → Prop) (p : P12)
    (hF : ∀ j cur cut t t1 rs gs, (foldJ p j cur cut).decide t rs gs = .ok t1 → P t.st → P t1.st)
    (hS : ∀ j cur nxt last cut t1 t2 t3 rs gs, rs.length ≤ 2 →
      (switchJ p j cur nxt last cut).decide t1 rs gs = .ok t2 →
      (behindJ p (j + 1) nxt cut).decide t2 [] [] = .ok t3 → P t1.st → P t3.st)
    (hB : ∀ j cur cut t tE rs gs, (baseJ5 p j cur cut).decide t rs gs = .ok tE → P t.st →
      P tE.st) :
    ∀ (rest : List Fmt.M1.Stage) (j : Nat) (cur : Fmt.M1.Stage) (la : Laid) (t tE : T12)
      (rs : List Fmt.RoundView) (gs : Gs),
      (stagesFrom guardedProximityTestParts p j cur rest la : Blk').decide t rs gs = .ok tE → P t.st → P tE.st
  | [], j, cur, la, t, tE, rs, gs, h, hp => by
    rw [stagesFrom_last] at h
    exact hB _ _ _ _ _ _ _ (ranged_ok _ _ _ _ _ _ h).1 hp
  | nxt :: rest, j, cur, la, t, tE, rs, gs, h, hp => by
    obtain ⟨t1, t2, t3, f1, f2, f3, _, f5⟩ :=
      (stagesFrom_ok guardedProximityTestParts p j cur nxt rest la t tE rs gs).1 h
    have k1 := hF j cur _ t t1 _ _ ((like_P5 p).fold _ _ _ _ _ _ _ f1) hp
    have hlen : ((rs.drop (foldAt guardedProximityTestParts p j cur la : Blk').rounds.length).take
        (switchAt guardedProximityTestParts p j cur nxt rest.isEmpty la : Blk').rounds.length).length ≤ 2 := by
      refine (List.length_take_le _ _).trans ?_
      show (((la.drop (1 + cur.k)).take 2).map (·.1)).length ≤ 2
      rw [List.length_map]
      exact List.length_take_le _ _
    have k2 := hS j cur nxt rest.isEmpty _ t1 t2 t3 _ _ hlen
      ((like_P5 p).switch _ _ _ _ _ _ _ _ _ f2) ((like_P5 p).behind _ _ _ _ _ f3) k1
    exact stages_keep P p hF hS hB rest (j + 1) nxt _ t3 tE _ _ f5 k2

/-- The same through the whole test. -/
theorem k12_keep (P : Statement → Prop) (p : P12)
    (hA : ∀ cut t t1 rs gs, (batJ p cut).decide t rs gs = .ok t1 → P t.st → P t1.st)
    (hF : ∀ j cur cut t t1 rs gs, (foldJ p j cur cut).decide t rs gs = .ok t1 → P t.st → P t1.st)
    (hS : ∀ j cur nxt last cut t1 t2 t3 rs gs, rs.length ≤ 2 →
      (switchJ p j cur nxt last cut).decide t1 rs gs = .ok t2 →
      (behindJ p (j + 1) nxt cut).decide t2 [] [] = .ok t3 → P t1.st → P t3.st)
    (hB : ∀ j cur cut t tE rs gs, (baseJ5 p j cur cut).decide t rs gs = .ok tE → P t.st →
      P tE.st)
    (t t' : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t rs gs = .ok t') (hp : P t.st) : P t'.st := by
  obtain ⟨first, rest, ds, tF, t1, hs, hr, hfr, hbat, _, hst⟩ := k12_ok guardedProximityTestParts p t t' rs gs h
  have hF' : tF = t := by
    have hfr' := (like_P5 p).front _ _ hfr
    unfold frontJ at hfr'
    dsimp only at hfr'
    split at hfr'
    · obtain ⟨_, _, hfr'⟩ := bind_ok hfr'
      cases hfr'
      rfl
    · cases hfr'
  subst hF'
  exact stages_keep P p hF hS hB rest 0 first _ _ t' _ _ hst
    (hA _ _ _ _ _ ((like_P5 p).bat _ _ _ _ _ hbat) hp)

/-- **The mark on sample rows goes through a test.** -/
theorem k12_samples_mark (p : P12) (he : p.early = true) (ha : p.answers = 1) (t t' : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t rs gs = .ok t')
    (hp : stSamplesB t.st = true) : stSamplesB t'.st = true :=
  k12_keep (fun S => stSamplesB S = true) p (bat_samples p) (fold_samples p)
    (switch_samples p he ha) (base_samples p) t t' rs gs h hp

/-! ## 2 The pads of older messages -/

/-- From a statement to a later one: no message is lost, and each message that was there has its
list of pad places as it was. -/
def StayPad (S S' : Statement) : Prop :=
  S.oracles.size ≤ S'.oracles.size ∧ ∀ o, o < S.oracles.size →
    (S'.oracles[o]?).map (·.pad) = (S.oracles[o]?).map (·.pad)

theorem StayPad.refl (S : Statement) : StayPad S S := ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem StayPad.trans {A B C : Statement} (h1 : StayPad A B) (h2 : StayPad B C) : StayPad A C :=
  ⟨Nat.le_trans h1.1 h2.1, fun o ho =>
    (h2.2 o (Nat.lt_of_lt_of_le ho h1.1)).trans (h1.2 o ho)⟩

theorem modify_pad (a : Array OnBytes.Oracle) (i o : Nat) (f : OnBytes.Oracle → OnBytes.Oracle)
    (hf : ∀ x, (f x).pad = x.pad) : ((a.modify i f)[o]?).map (·.pad) = (a[o]?).map (·.pad) := by
  rw [Array.getElem?_modify]
  split
  · cases a[o]? with
    | none => rfl
    | some x => exact congrArg some (hf x)
  · rfl

theorem shut_pad (l : List Nat) (S : Statement) (o : Nat) :
    ((closeLedgers S l).oracles[o]?).map (·.pad) = (S.oracles[o]?).map (·.pad) := by
  rw [ProxRun.closeLedgers_get]
  cases S.oracles[o]? with
  | none => rfl
  | some x =>
    show some (if o ∈ l then ProxRun.shut x else x).pad = some x.pad
    split <;> rfl

theorem begun_pad (S : Statement) (g o : Nat) (G : Group) :
    ((begun S g G).oracles[o]?).map (·.pad) = (S.oracles[o]?).map (·.pad) :=
  shut_pad G.members.toList S o

theorem bat_pads (p : P12) (cut : List Fmt.DeclaredRound) (t t1 : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (batJ p cut).decide t rs gs = .ok t1) : StayPad t.st t1.st := by
  refine ⟨(bat_stay p cut t t1 rs gs h).osize, fun o _ => ?_⟩
  obtain ⟨G, row, L, m, _, rfl⟩ := bat_form p cut t t1 rs gs h
  exact begun_pad t.st t.g o G

theorem fold_pads (p : P12) (j : Nat) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound)
    (t t1 : T12) (rs : List Fmt.RoundView) (gs : Gs) (h : (foldJ p j cur cut).decide t rs gs = .ok t1) :
    StayPad t.st t1.st := by
  refine ⟨(fold_stay p j cur cut t t1 rs gs h).osize, fun o ho => ?_⟩
  obtain ⟨row, L, c, nn, id, d1, d', rows, _, _, hcase, hsp, rfl⟩ :=
    foldJ_form p j cur cut t t1 rs gs h
  have hd' := spendP_form hsp
  subst hd'
  rcases hcase with ⟨_, rfl⟩ | ⟨_, ids, hr, _⟩
  · exact modify_pad _ _ _ _ fun _ => rfl
  · obtain ⟨lay, _, _, _, rfl⟩ := recvP_ok hr
    show (((stSent t.st _).oracles.modify _ _)[o]?).map _ = _
    refine Eq.trans (modify_pad _ _ _ _ ?_) ?_
    · exact fun _ => rfl
    · rw [stSent_old _ _ _ ho]

theorem base_pads (p : P12) (j : Nat) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound)
    (t tE : T12) (rs : List Fmt.RoundView) (gs : Gs) (h : (baseJ5 p j cur cut).decide t rs gs = .ok tE) :
    StayPad t.st tE.st := by
  refine ⟨(base_stay p j cur cut t tE rs gs h).osize, fun o _ => ?_⟩
  unfold baseJ5 at h
  dsimp only at h
  split at h
  · obtain ⟨cl, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨cl', _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨m, _, h⟩ := bind_ok h
    obtain ⟨star, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨a, _, h⟩ := bind_ok h
    cases h
    exact modify_pad _ _ _ _ fun _ => rfl
  · cases h

theorem switch_pads (p : P12) (he : p.early = true) (ha : p.answers = 1) (j : Nat)
    (cur nxt : Fmt.M1.Stage) (last : Bool) (cut : List Fmt.DeclaredRound) (t1 t2 t3 : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (hlen : rs.length ≤ 2)
    (h1 : (switchJ p j cur nxt last cut).decide t1 rs gs = .ok t2)
    (h2 : (behindJ p (j + 1) nxt cut).decide t2 [] [] = .ok t3) : StayPad t1.st t3.st := by
  refine ⟨(switch_stay p he ha j cur nxt last cut t1 t2 t3 rs gs hlen h1 h2).osize,
    fun o ho => ?_⟩
  obtain ⟨T, gp, others, D, z, hst, _⟩ :=
    switch_did' p he ha j cur nxt last cut t1 t2 t3 rs gs hlen h1 h2
  rw [hst, begun_pad]
  unfold Taken.stR Taken.stJ
  rw [(withRows_oracles gp D.rows _).1]
  show (((ledgerShut _ _ _).oracles.modify _ _)[o]?).map _ = _
  refine Eq.trans (modify_pad _ _ _ _ fun _ => rfl) ?_
  have e : ∀ (S : Statement) (i : Nat),
      ((ledgerShut S T i).oracles[o]?).map (·.pad) = (S.oracles[o]?).map (·.pad) := fun S i => by
    unfold ledgerShut
    split
    · exact shut_pad _ _ _
    · rfl
  rw [e]
  unfold Taken.stA
  show (((stSent t1.st _).oracles.modify t1.st.oracles.size _)[o]?).map _ = _
  rw [modify_other _ _ _ _ (by omega), stSent_old _ _ _ ho]

/-- **Every older message's list of pad places stays, through a test.** -/
theorem k12_pads (p : P12) (he : p.early = true) (ha : p.answers = 1) (t t' : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t rs gs = .ok t') :
    StayPad t.st t'.st :=
  k12_keep (fun S => StayPad t.st S) p
    (fun cut a b rs gs k hp => hp.trans (bat_pads p cut a b rs gs k))
    (fun j cur cut a b rs gs k hp => hp.trans (fold_pads p j cur cut a b rs gs k))
    (fun j cur nxt last cut a b c rs gs hl k1 k2 hp =>
      hp.trans (switch_pads p he ha j cur nxt last cut a b c rs gs hl k1 k2))
    (fun j cur cut a b rs gs k hp => hp.trans (base_pads p j cur cut a b rs gs k))
    t t' rs gs h (StayPad.refl _)

/-! ## 3 The mark on the open rows -/

/-- At every number q other than that of the group under test, the shape of the statement after a
test is the shape before it, grown (`Grown`, Johnson/Desc/Ground/Shape/Claims.lean). Where the
statement before the test has no group number q, the clause on the group is vacuous. -/
theorem k12_grown (p : P12) (he : p.early = true) (ha : p.answers = 1) (t t' : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t rs gs = .ok t')
    (ht : stTidyB t.st = true) (q : Nat) (hq : q ≠ t.g) :
    Grown (stSh t.st) (stSh t'.st) q := by
  have o1 := H2K.Out.k12_out p he ha t t' rs gs h
  obtain ⟨G0, o2⟩ := H2K.Out.k12_out2 p he ha t t' rs gs h
  have pd := k12_pads p he ha t t' rs gs h
  refine ⟨o1.codes, fun o x hx => ?_, fun Gs hGs => ?_⟩
  · rw [orc_get] at hx
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
    obtain ⟨y', hy', e⟩ := o1.shapes o y hy
    exact ⟨orcSh y', by rw [orc_get, hy']; rfl, e⟩
  · rw [grp_get] at hGs
    obtain ⟨G, hG, rfl⟩ := Option.map_eq_some_iff.1 hGs
    have hlt : q < t.st.groups.size := (Array.getElem?_eq_some_iff.1 hG).1
    refine ⟨grpSh G, by rw [grp_get, o2.others q hlt hq, hG]; rfl, fun _ c => c, fun o ho => ?_⟩
    obtain ⟨x, hx, _⟩ := (tidy_of ht).members q G hG o ho
    have hlo : o < t.st.oracles.size := (Array.getElem?_eq_some_iff.1 hx).1
    have e := pd.2 o hlo
    rw [orc_get, orc_get, Option.map_map, Option.map_map]
    exact congrArg (·.getD []) e

/-- **The mark on the open rows goes through a test, at every group**, where the statement before
the test is tidy (`stTidyB`). -/
theorem k12_claims_mark (p : P12) (he : p.early = true) (ha : p.answers = 1) (t t' : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t rs gs = .ok t')
    (ht : stTidyB t.st = true) (q : Nat) (hc : claimsAtB t.st q = true) :
    claimsAtB t'.st q = true := by
  obtain ⟨G0, o2⟩ := H2K.Out.k12_out2 p he ha t t' rs gs h
  by_cases hq : q = t.g
  · subst hq
    refine claimsAt_iff.2 fun G' hG' r hr => ?_
    rw [o2.begunG] at hG'
    obtain rfl := Option.some.inj hG'
    cases hr
  · rcases Nat.lt_or_ge q t.st.groups.size with hlt | hge
    · refine claims_keep (k12_grown p he ha t t' rs gs h ht q hq) (fun G' hG' r hr => ?_) hc
      rw [o2.others q hlt hq] at hG'
      exact Or.inl ⟨G', hG', hr⟩
    · refine claimsAt_iff.2 fun G' hG' r hr => ?_
      have hlt' : q < t'.st.groups.size := (Array.getElem?_eq_some_iff.1 hG').1
      rw [o2.groupsN] at hlt'
      obtain ⟨G'', hG'', _, hrows⟩ := o2.groupsNew q hge hlt'
      obtain rfl : G'' = G' := Option.some.inj (hG''.symm.trans hG')
      rw [hrows] at hr
      cases hr

end ProofFile.Honest.Sh

#print axioms ProofFile.Honest.Sh.samples_idx
#print axioms ProofFile.Honest.Sh.bat_samples
#print axioms ProofFile.Honest.Sh.fold_samples
#print axioms ProofFile.Honest.Sh.base_samples
#print axioms ProofFile.Honest.Sh.switch_did'
#print axioms ProofFile.Honest.Sh.switch_samples
#print axioms ProofFile.Honest.Sh.stages_keep
#print axioms ProofFile.Honest.Sh.k12_keep
#print axioms ProofFile.Honest.Sh.k12_samples_mark
#print axioms ProofFile.Honest.Sh.StayPad.refl
#print axioms ProofFile.Honest.Sh.StayPad.trans
#print axioms ProofFile.Honest.Sh.modify_pad
#print axioms ProofFile.Honest.Sh.shut_pad
#print axioms ProofFile.Honest.Sh.begun_pad
#print axioms ProofFile.Honest.Sh.bat_pads
#print axioms ProofFile.Honest.Sh.fold_pads
#print axioms ProofFile.Honest.Sh.base_pads
#print axioms ProofFile.Honest.Sh.switch_pads
#print axioms ProofFile.Honest.Sh.k12_pads
#print axioms ProofFile.Honest.Sh.k12_grown
#print axioms ProofFile.Honest.Sh.k12_claims_mark
#print axioms ProofFile.Honest.Sh.StayPad
