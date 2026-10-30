-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/Shape/TestMarks.lean: a proximity test that accepts keeps two marks on the
verifier's statement. The marks are the Bools `stTidyB` and `stPlainB`
(Johnson/Desc/Ground/Shape/Marks.lean). Proved: where the description's own block for the test,
`proximityTestKind guardedProximityTestParts p` (`proximityTestKind`: Johnson/Desc/K12/Frame.lean; `guardedProximityTestParts`: Johnson/Desc/K12/JoinGuarded.lean),
accepts, on whatever rounds and columns, and the statement before the test has a mark, the statement
after the test has it. The theorems are meant for a chain that has a second test after this one;
nothing here is stated of a chain. General in the plan p (for the second mark under two hypotheses
on it), the structures t and t', the rounds and the columns. Theorems only: nothing is defined. The
verifier's structure alone: no prover, no coin, no frame for an honest side.

Terms. The structure inside a test is `T12` (Johnson/Desc/K12/Join.lean); its field `st` is the
statement (`Statement`, OnBytes/Iop/Ground.lean: codes, oracle messages, groups). t is the structure
before a test or a part of it; t', t1, t3 or tE is the one after. A group (`Group`) has open rows
(`rows`); an oracle message (`Oracle`) has sample rows (`sampleRows`). The plan p (`P12`,
Frame.lean) holds the numbers of the place of the test. A block (`Block`, Johnson/Desc/Block.lean)
or a part of the test (`Part`, Frame.lean) accepts where its `decide` returns `.ok` with the next
structure. The first mark, `stTidyB S`, is true if and only if `Tidy S` holds
(Johnson/Desc/Means/Walk.lean; `tidy_of`, `tidy_mark`, Marks.lean). The second mark, `stPlainB S`,
is true if and only if every open row of every group and every sample row of every oracle message
passes `rowPlainB` (Marks.lean): no tensor of the row's terms or of its whole coefficient vectors
has a written-out variable (`denseVars` is empty). `rowPlainB r` is true if and only if `PlainRow r`
holds (OnBytes/Slice/BlkPlain.lean; `rowPlainB_iff`, Marks.lean); such a row is called plain. The
frame for an honest side is Johnson/Desc/ProofFile/Honest/Frame.lean.

  `k12_tidy_mark`: where `(proximityTestKind guardedProximityTestParts p).decide t rs gs` returns `.ok t'`,
    `t.st.codes.lengthsOk = true` and `stTidyB t.st = true`: `stTidyB t'.st = true`. No hypothesis
    on p
  `k12_plain_mark`: where `p.early = true`, `p.answers = 1`, `(proximityTestKind guardedProximityTestParts p).decide t rs gs`
    returns `.ok t'` and `stPlainB t.st = true`: `stPlainB t'.st = true`
  `stages_plain`: the same as `k12_plain_mark` for the stages from any stage on
    (`stagesFrom guardedProximityTestParts`, Frame.lean), under the same two hypotheses on p
  `bat_plain`, `fold_plain`, `base_plain`: the second mark is kept where the batching (`batJ`) or a
    fold (`foldJ`, both Join.lean) or the base case (`baseJ5`, JoinGuarded.lean) accepts, with no
    hypothesis on p
  `switch_plain`: the second mark is kept by a switch (`switchJ`) and the batching after it
    (`behindJ`, both Join.lean; on no round and no column), taken as one step from t1 through t2 to
    t3: if `t1.st` has the mark, `t3.st` has it. Under the two hypotheses on p and `rs.length ≤ 2`;
    `stages_plain` proves that bound
  `plain_idx`: the second mark by numbers of groups and messages: `stPlainB S = true` if and only
    if, at every number q at which S has a group, each open row of that group passes `rowPlainB`,
    and, at every number o at which S has an oracle message, each of its sample rows does
  `begun_plain`, `withGroup_plain`: the second mark is kept by `begun S g G`
    (OnBytes/Slice/BlkBegin.lean), the statement after the beginning of a test, and by
    `Ground.withGroup S a b` (Johnson/Desc/First/Base/Ground.lean), the statement with one more
    group, at all arguments

By what. `k12_tidy_mark`: the library's `k12_calls` (Johnson/Desc/K12/Law/Calls.lean) and
`calls_tidy` (Johnson/Desc/K12/Law/CallsWalkG.lean) are called, not proved anew. `k12_plain_mark` is
proved here, part by part. The block's accept is cut into its parts' accepts by `k12_ok`,
`stagesFrom_ok`, `stagesFrom_last` (Johnson/Desc/K12/FrameLaws.lean), `like_P5`
(Johnson/Desc/K12/Law/OutK.lean) and `ranged_ok` (Johnson/Desc/K12/Law/BaseGives.lean). What a part
leaves is taken from `bat_form` (Johnson/Desc/K12/Honest/Shape/TestKeeps.lean), `foldJ_form`,
`spendP_form` (Johnson/Desc/K12/Law/OutK2.lean), `recvP_ok` and `switchUnfolds`
(Johnson/Desc/K12/Law/SwUnfold.lean); `base_plain` unfolds `baseJ5`. That such a change keeps the
mark: `plain_iff`, `plain_group`, `plain_oracle`, `sent_plain`, `closeLedgers_plain` (Marks.lean);
in `switch_plain`, `plain_idx` with equations on a statement's groups and sample rows from
OnBytes/Slice/BlkCsRun.lean, BlkStLaws.lean, BlkCalls.lean and BlkProxEarlierMessagesAndGroups.lean, OutK2.lean and
TestKeeps.lean, and `switchE_two` (OutK.lean). A switch lays rows on its new group that need not be
plain; the batching behind it takes them off again, so they do not show behind the two; the one
sample row that a switch admits is plain by the library's `plainRow_form`
(OnBytes/Slice/BlkPlain.lean). In Lean: `t3.st` is `begun` of the statement with these rows, at
their group (the field `st` of `Did`, Johnson/Desc/K12/Law/SwDid.lean), and `begun` sets that
group's `rows` to `#[]`.

Hypotheses. Of `k12_tidy_mark`: h: the block's accept; hl: `t.st.codes.lengthsOk = true`; ht: the
first mark before the test. Of `k12_plain_mark`: he: `p.early = true`; ha: `p.answers = 1`; h: the
block's accept; hp: the second mark before the test.

Limits.
- `k12_tidy_mark` has the hypothesis `Codes.lengthsOk` (OnBytes/Iop/Ground.lean) at the codes of the
  statement before the test: every code's message length is a power of two. It is a test on the
  codes; the library's `calls_tidy` has the same hypothesis.
- `k12_plain_mark` asks that the masks come early and a sample has one answer.
- The second mark speaks of the statement's open rows and sample rows: not of what passes inside a
  test from a part to the next. In Lean that is the field `pass` of `T12`.
- The open rows of the group under test leave the statement at the test's beginning (`bat_form`: the
  batching leaves `begun t.st t.g G`, in which that group's `rows` is `#[]`): the second mark after
  the test does not speak of them.
- `switch_plain` states nothing of `t2.st`, the statement between the switch and the batching after
  it.
- Every theorem on a test or a part is a conditional on an accept. No accept is shown here, and no
  value is given that meets the hypotheses of a theorem together.
- The second mark rests on `rowPlainB`, that is, on `PlainRow`. Where the statement before the test
  has an open row or a sample row with a written-out variable, `stPlainB` is false there and the
  theorems that the second mark is kept are vacuous. Nothing is stated here of rows that may have
  written-out factors (`DenseRow`, OnBytes/Slice/BlkProxDense.lean).
- That either mark holds at a statement of any description is not shown here.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.Shape.TestKeeps
import Johnson.Desc.K12.Law.CallsWalkG

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Sh
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.Out (like_P5 foldJ_form spendP_form)
open H2K.FoldLaw (bind_ok)
open H2K.JointK H2K.Sw

/-- **The first mark (`stTidyB`) is kept where the test's block accepts.** Hypothesis hl:
`Codes.lengthsOk` at the codes of the statement before the test. -/
theorem k12_tidy_mark (p : P12) (t t' : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t rs gs = .ok t') (hl : t.st.codes.lengthsOk = true)
    (ht : stTidyB t.st = true) : stTidyB t'.st = true :=
  tidy_mark (H2K.Out.calls_tidy OnBytes.Model.Reading.gl (H2K.Out.k12_calls p t t' rs gs h [] [])
    hl (tidy_of ht))

/-! ## The second mark -/

/-- The second mark (`stPlainB`), stated by the numbers of groups and of oracle messages. -/
theorem plain_idx {S : Statement} : stPlainB S = true ↔
    (∀ (q : Nat) (G : Group), S.groups[q]? = some G → ∀ r ∈ G.rows.toList, rowPlainB r = true) ∧
      ∀ (o : Nat) (rows : Array OnBytes.Row), (S.oracles[o]?).map (·.sampleRows) = some rows →
        ∀ r ∈ rows.toList, rowPlainB r = true := by
  rw [plain_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun q G hG => h1 G ?_, fun o rows ho => ?_⟩
    · obtain ⟨hq, rfl⟩ := Array.getElem?_eq_some_iff.1 hG
      exact Array.getElem_mem_toList hq
    · obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 ho
      obtain ⟨hq, rfl⟩ := Array.getElem?_eq_some_iff.1 hx
      exact h2 _ (Array.getElem_mem_toList hq)
  · rintro ⟨h1, h2⟩
    refine ⟨fun G hG => ?_, fun x hx => ?_⟩
    · obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hG
      have hq' : q < S.groups.size := by simpa using hq
      exact h1 q _ (by rw [Array.getElem?_eq_getElem hq']; simp)
    · obtain ⟨o, ho, rfl⟩ := List.getElem_of_mem hx
      have ho' : o < S.oracles.size := by simpa using ho
      exact h2 o _ (by rw [Array.getElem?_eq_getElem ho']; simp)

theorem begun_plain (S : Statement) (g : Nat) (G : Group) (hp : stPlainB S = true) :
    stPlainB (begun S g G) = true :=
  plain_group (closeLedgers_plain _ _ hp) g _ fun _ _ r hr => by cases hr

theorem bat_plain (p : P12) (cut : List Fmt.DeclaredRound) (t t1 : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (batJ p cut).decide t rs gs = .ok t1) (hp : stPlainB t.st = true) :
    stPlainB t1.st = true := by
  obtain ⟨G, row, L, m, _, rfl⟩ := bat_form p cut t t1 rs gs h
  exact begun_plain t.st t.g G hp

theorem withGroup_plain (S : Statement) (a b : Nat) (hp : stPlainB S = true) :
    stPlainB (Ground.withGroup S a b) = true := by
  obtain ⟨h1, h2⟩ := plain_iff.1 hp
  refine plain_iff.2 ⟨fun G hG => ?_, h2⟩
  have hG' : G ∈ (S.groups.push { code := a, maskCode := b }).toList := hG
  rw [Array.toList_push] at hG'
  rcases List.mem_append.1 hG' with hG' | hG'
  · exact h1 G hG'
  · rw [List.mem_singleton.1 hG']
    intro r hr
    cases hr

theorem fold_plain (p : P12) (j : Nat) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound)
    (t t1 : T12) (rs : List Fmt.RoundView) (gs : Gs) (h : (foldJ p j cur cut).decide t rs gs = .ok t1)
    (hp : stPlainB t.st = true) : stPlainB t1.st = true := by
  obtain ⟨row, L, c, nn, id, d1, d', rows, _, _, hcase, hsp, rfl⟩ :=
    foldJ_form p j cur cut t t1 rs gs h
  have hd' := spendP_form hsp
  subst hd'
  refine withGroup_plain _ _ _ ?_
  rcases hcase with ⟨_, rfl⟩ | ⟨_, ids, hr, _⟩
  · exact plain_oracle hp id _ fun _ x => x
  · obtain ⟨lay, _, _, _, rfl⟩ := recvP_ok hr
    exact plain_oracle (sent_plain hp _) id _ fun _ x => x

theorem base_plain (p : P12) (j : Nat) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound)
    (t tE : T12) (rs : List Fmt.RoundView) (gs : Gs) (h : (baseJ5 p j cur cut).decide t rs gs = .ok tE)
    (hp : stPlainB t.st = true) : stPlainB tE.st = true := by
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
    exact plain_oracle hp star _ fun _ x => x
  · cases h

theorem switch_plain (p : P12) (he : p.early = true) (ha : p.answers = 1) (j : Nat)
    (cur nxt : Fmt.M1.Stage) (last : Bool) (cut : List Fmt.DeclaredRound) (t1 t2 t3 : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (hlen : rs.length ≤ 2)
    (h1 : (switchJ p j cur nxt last cut).decide t1 rs gs = .ok t2)
    (h2 : (behindJ p (j + 1) nxt cut).decide t2 [] [] = .ok t3) (hp : stPlainB t1.st = true) :
    stPlainB t3.st = true := by
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
    obtain ⟨p1, p2⟩ := plain_idx.1 hp
    rw [hd.st]
    refine plain_idx.2 ⟨fun q G hG => ?_, fun o rws ho => ?_⟩
    · have hG' : ((closeLedgers _ _).groups.modify gp fun G =>
          { G with inRun := true, rows := #[] })[q]? = some G := hG
      by_cases hq : q = gp
      · rw [Array.getElem?_modify, if_pos hq.symm] at hG'
        obtain ⟨y, _, rfl⟩ := Option.map_eq_some_iff.1 hG'
        intro r hr
        cases hr
      · rw [modify_other _ _ _ _ hq, ProxRun.closeLedgers_groups] at hG'
        unfold Taken.stR Taken.stJ at hG'
        rw [H2K.Out.withRows_groups_other gp q hq] at hG'
        have hG'' : ((ledgerShut _ _ _).groups.modify gp _)[q]? = some G := hG'
        rw [modify_other _ _ _ _ hq, ledgerShut_groups] at hG''
        exact p1 q G hG''
    · rw [begun_rows] at ho
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
        exact rowPlainB_iff.2 (plainRow_form _ _ _ _ _ D.smp hd.form)
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
  · cases h1'

theorem stages_plain (p : P12) (he : p.early = true) (ha : p.answers = 1) :
    ∀ (rest : List Fmt.M1.Stage) (j : Nat) (cur : Fmt.M1.Stage) (la : Laid) (t tE : T12)
      (rs : List Fmt.RoundView) (gs : Gs),
      (stagesFrom guardedProximityTestParts p j cur rest la : Blk').decide t rs gs = .ok tE →
      stPlainB t.st = true → stPlainB tE.st = true
  | [], j, cur, la, t, tE, rs, gs, h, hp => by
    rw [stagesFrom_last] at h
    exact base_plain p _ _ _ _ _ _ _ (ranged_ok _ _ _ _ _ _ h).1 hp
  | nxt :: rest, j, cur, la, t, tE, rs, gs, h, hp => by
    obtain ⟨t1, t2, t3, f1, f2, f3, _, f5⟩ :=
      (stagesFrom_ok guardedProximityTestParts p j cur nxt rest la t tE rs gs).1 h
    have k1 := fold_plain p j cur _ t t1 _ _ ((like_P5 p).fold _ _ _ _ _ _ _ f1) hp
    have hlen : ((rs.drop (foldAt guardedProximityTestParts p j cur la : Blk').rounds.length).take
        (switchAt guardedProximityTestParts p j cur nxt rest.isEmpty la : Blk').rounds.length).length ≤ 2 := by
      refine (List.length_take_le _ _).trans ?_
      show (((la.drop (1 + cur.k)).take 2).map (·.1)).length ≤ 2
      rw [List.length_map]
      exact List.length_take_le _ _
    have k2 := switch_plain p he ha j cur nxt rest.isEmpty _ t1 t2 t3 _ _ hlen
      ((like_P5 p).switch _ _ _ _ _ _ _ _ _ f2) ((like_P5 p).behind _ _ _ _ _ f3) k1
    exact stages_plain p he ha rest (j + 1) nxt _ t3 tE _ _ f5 k2

/-- **The second mark (`stPlainB`) is kept where the test's block accepts.** Hypotheses on the plan:
`p.early = true` and `p.answers = 1`. -/
theorem k12_plain_mark (p : P12) (he : p.early = true) (ha : p.answers = 1) (t t' : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t rs gs = .ok t')
    (hp : stPlainB t.st = true) : stPlainB t'.st = true := by
  obtain ⟨first, rest, ds, tF, t1, hs, hr, hfr, hbat, _, hst⟩ := k12_ok guardedProximityTestParts p t t' rs gs h
  have hF : tF = t := by
    have hfr' := (like_P5 p).front _ _ hfr
    unfold frontJ at hfr'
    dsimp only at hfr'
    split at hfr'
    · obtain ⟨_, _, hfr'⟩ := bind_ok hfr'
      cases hfr'
      rfl
    · cases hfr'
  subst hF
  exact stages_plain p he ha rest 0 first _ _ t' _ _ hst
    (bat_plain p _ _ _ _ _ ((like_P5 p).bat _ _ _ _ _ hbat) hp)

end ProofFile.Honest.Sh

#print axioms ProofFile.Honest.Sh.k12_tidy_mark
#print axioms ProofFile.Honest.Sh.plain_idx
#print axioms ProofFile.Honest.Sh.begun_plain
#print axioms ProofFile.Honest.Sh.bat_plain
#print axioms ProofFile.Honest.Sh.withGroup_plain
#print axioms ProofFile.Honest.Sh.fold_plain
#print axioms ProofFile.Honest.Sh.base_plain
#print axioms ProofFile.Honest.Sh.switch_plain
#print axioms ProofFile.Honest.Sh.stages_plain
#print axioms ProofFile.Honest.Sh.k12_plain_mark
