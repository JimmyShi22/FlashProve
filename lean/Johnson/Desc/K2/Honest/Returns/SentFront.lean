-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/SentFront.lean: WHAT THE LAW ON THE STEP BEHIND THE SENDING ASKS OF
WHAT IT IS HANDED (`FrontFits`, Returns/BehindAt.lean) HOLDS AT WHAT THE SENDING RETURNS (`sentAt`,
Returns/Sends.lean), FROM PREMISES ON THE FRONT ALONE: the statement IN FRONT OF the sending, the
target, the positions drawn. Statements and proofs.

WHY. Returns/BehindAt.lean's head says who must leave which premise, and shows none. HERE: what the
sending must LEAVE (`seated`, `stored`, `sampledG`, `sampledCopies`, `numbers`): off the new
messages as terms (`sentAt_new`); what it must KEEP (`check`, `fits`, `tables`, `reads`:
Returns/AlikeKept.lean; the codes' three); what the front leaves and the sending keeps (the group's
five: `sentAt_groups`).

  `numbers_first`, `numbers_kept`   the new messages' numbers: the first; the next ones, as a list
  `wr_core`, `shapeAt_of`, `new_at`   a sampled new message: its shape, that it is sampled, its pad
  `FrontPlain`      THE PREMISES, AT THE FRONT x: the program's test on the target · the rest lies
                    in main rows · `OldFits` · each kept target has a main row AND AN ANSWER · the
                    codes' lengths and the two bounds · the positions lie in the old code's range ·
                    the new group is there, no test begun, no member; its main code is the target's
                    and the copies' · `TablesFit` · the stored rows read the main table alone
  `FrontCore`, `FrontCore.plain`   the same but for the new group's three clauses: thirteen; with
                    these three it gives `FrontPlain`
  `frontFits_sent`   THE STATEMENT: under `FrontPlain`, where Q has the front's codes and announces
                    the switch's messages: `FrontFits` at `behindArgs P x (sentAt Q ...) rL cols`

Limits. `FrontPlain` is shown nowhere here. That every kept old member is a message of the statement
is no premise: the library's `keptOld_of` (Johnson/Top/H0/K2Hands/AtYes.lean). The library has
statements like `numbers_first` and `numbers_kept`, at its own spellings of the numbers (`ids_zero`,
Johnson/Top/H0/K2Hands/FrameOne.lean; `ids_at`, K2Hands/AtYes.lean; `ids_cut`, on arrays,
Johnson/Top/H0/Tw/K2C/GroupsAtYes.lean). Of `wr_core` the first two clauses are `wr_sampled`'s
(Johnson/Prover/Send/Form.lean), called; the third spells the pad by `padPlaces`. THREE CLAUSES OF
`TablesFit` COMPARE FIELD ELEMENTS OF THE STATE WITH (1, 1): at each written-out variable of a
carried form's or a stored sample row's tensor. Nothing on the book: `ReadFits` is not treated.
Nothing on any property.

-/
import Johnson.Desc.K2.Honest.Returns.SendsMore
import Johnson.Desc.K2.Honest.Returns.AlikeKept
import Johnson.Top.H0.K2Hands.AtYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open Johnson.Prover.Send (numbers shapeAt wr_sampled)
open _root_.Tw.K2 (Par9 Front Col switchNotices readsMainOf)
open VerifiableInference.Desc.First.K2 (behindArgs notices_size notices_zero notices_kept
  keptOld_of)

theorem numbers_first (Q : K1.Par) (n₀ : Nat) (h : 0 < Q.sent.size) :
    (numbers Q n₀).getD 0 noId = n₀ := by
  simp [numbers, Array.getD, h]

theorem numbers_kept (Q : K1.Par) (n₀ k : Nat) (h : 1 + k ≤ Q.sent.size) :
    ((numbers Q n₀).extract 1 (1 + k)).toList = (List.range k).map (n₀ + 1 + ·) := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < k
  · have h1 : i + 1 < Q.sent.size := by omega
    simp [numbers, hi]
    exact ⟨i + 1, by simp [h1], by omega⟩
  · simp [numbers, hi]

theorem wr_core (codes : Codes) (seeds : List (List E × E)) (o : Nat) (s : OracleShape)
    (ys : List E) (h0 : s.answers ≠ 0) :
    (K1.wr codes seeds o s ys).shape = s ∧ (K1.wr codes seeds o s ys).sampled = true ∧
      (K1.wr codes seeds o s ys).pad = (padPlaces codes s).map fun p => (p.part, p.index) := by
  have h := wr_sampled codes seeds o s ys h0
  refine ⟨h.1, h.2.1, ?_⟩
  unfold K1.wr padPlaces
  rw [if_neg h0]

theorem shapeAt_of (Q : K1.Par) (k : Nat) (s : OracleShape)
    (h : (Q.sent[k]?).map (·.shape) = some s) : k < Q.sent.size ∧ shapeAt Q k = s := by
  obtain ⟨n, hn, e⟩ := Option.map_eq_some_iff.1 h
  refine ⟨(Array.getElem?_eq_some_iff.1 hn).1, ?_⟩
  unfold shapeAt
  rw [Array.getD_eq_getD_getElem?, hn]
  exact e

/-- A sampled new message behind the sending. -/
theorem new_at (Q : K1.Par) (S : Statement) (B : TreeBook) (roots : Nat) (rS rL : Fmt.RoundView) (k : Nat)
    (s : OracleShape) (h : (Q.sent[k]?).map (·.shape) = some s) (h0 : s.answers ≠ 0) :
    ∃ m, (sentAt Q S B roots rS rL).st.oracles[S.oracles.size + k]? = some m ∧ m.shape = s ∧
      m.sampled = true ∧ m.pad = (padPlaces Q.codes s).map fun p => (p.part, p.index) := by
  obtain ⟨hk, e⟩ := shapeAt_of Q k s h
  refine ⟨_, sentAt_new Q S B roots rS rL k hk, ?_⟩
  rw [e]
  exact wr_core _ _ _ _ _ h0

/-- **The premises, at the front.** c: the old main code. G: the new group. poss: the positions that
the second round draws. -/
structure FrontPlain (x : Front) (c : Code) (G : Group) (poss : List Nat) : Prop where
  check : switchTargetCheck x.st x.f.rows x.T = true
  restMain : x.T.rest.part = .main
  fits : OldFits x.st x.f.rows
  keptPos : ∀ k ∈ x.T.kept.toList, 0 < k.shape.mainRows
  keptAnswers : ∀ k ∈ x.T.kept.toList, k.shape.answers ≠ 0
  lengths : x.st.codes.lengthsOk = true
  logC : (x.st.codes.base.getD x.f.rows.code default).logN ≤ 32
  logZ : (x.st.codes.mask.getD x.f.rows.maskCode default).logN ≤ 32
  inRange : ∀ v ∈ (Positions.ofDraws c.logN poss).all.toList,
    v < 2 ^ (x.st.codes.base.getD x.f.rows.code default).logN
  group : x.st.groups[x.f.group]? = some G
  noRun : G.inRun = false
  noMember : G.members = #[]
  groupCode : x.T.shape.code = G.code
  copiesCode : ∀ k ∈ x.T.kept.toList, k.shape.code = G.code
  tables : TablesFit x.st x.f.rows x.T
  reads : ∀ o ∈ (switchKept x.f.rows).toList,
    ∀ r ∈ (x.st.oracles.getD o default).sampleRows.toList, readsMainOf o r = true

/-- The premises but for the new group's three: for a front that has just made the group. code: the
group's main code. -/
structure FrontCore (x : Front) (c : Code) (code : Nat) (poss : List Nat) : Prop where
  check : switchTargetCheck x.st x.f.rows x.T = true
  restMain : x.T.rest.part = .main
  fits : OldFits x.st x.f.rows
  keptPos : ∀ k ∈ x.T.kept.toList, 0 < k.shape.mainRows
  keptAnswers : ∀ k ∈ x.T.kept.toList, k.shape.answers ≠ 0
  lengths : x.st.codes.lengthsOk = true
  logC : (x.st.codes.base.getD x.f.rows.code default).logN ≤ 32
  logZ : (x.st.codes.mask.getD x.f.rows.maskCode default).logN ≤ 32
  inRange : ∀ v ∈ (Positions.ofDraws c.logN poss).all.toList,
    v < 2 ^ (x.st.codes.base.getD x.f.rows.code default).logN
  groupCode : x.T.shape.code = code
  copiesCode : ∀ k ∈ x.T.kept.toList, k.shape.code = code
  tables : TablesFit x.st x.f.rows x.T
  reads : ∀ o ∈ (switchKept x.f.rows).toList,
    ∀ r ∈ (x.st.oracles.getD o default).sampleRows.toList, readsMainOf o r = true

theorem FrontCore.plain {x : Front} {c : Code} {G : Group} {poss : List Nat}
    (F : FrontCore x c G.code poss) (hg : x.st.groups[x.f.group]? = some G)
    (hr : G.inRun = false) (hm : G.members = #[]) : FrontPlain x c G poss :=
  ⟨F.check, F.restMain, F.fits, F.keptPos, F.keptAnswers, F.lengths, F.logC, F.logZ, F.inRange, hg,
    hr, hm, F.groupCode, F.copiesCode, F.tables, F.reads⟩

/-- **What the step behind the sending asks holds at what the sending returns.** -/
theorem frontFits_sent (P : Par9) (x : Front) (B : TreeBook) (roots : Nat) (rS rL : Fmt.RoundView)
    (cols : List OpenedColumn) (Q : K1.Par) (hc : Q.codes = x.st.codes)
    (hs : Q.sent = switchNotices x.T x.others) {c : Code} {G : Group}
    (F : FrontPlain x c G rL.drawn.poss) :
    FrontFits (behindArgs P x (sentAt Q x.st B roots rS rL) rL cols) c G := by
  have hk := keptOld_of F.check
    (fun i h => F.keptPos _ (Array.mem_toList_iff.2 (Array.getElem_mem h)))
  have cd : (sentAt Q x.st B roots rS rL).st.codes = x.st.codes := sentAt_codes Q x.st B roots rS rL
  have al : AlikeKept x.f.rows x.st (sentAt Q x.st B roots rS rL).st :=
    ⟨cd, fun o ho => sentAt_old Q x.st B roots rS rL o (hk o ho)⟩
  have hN : Q.sent.size = 1 + x.T.kept.size + x.others.size := by rw [hs, notices_size]
  have hg : (sentAt Q x.st B roots rS rL).ids.getD 0 noId = x.st.oracles.size :=
    numbers_first Q _ (by omega)
  have ha : ((sentAt Q x.st B roots rS rL).ids.extract 1 (1 + x.T.kept.size)).toList =
      (List.range x.T.kept.size).map (x.st.oracles.size + 1 + ·) := numbers_kept Q _ _ (by omega)
  have hat : ∀ a, a < x.T.kept.size →
      ((sentAt Q x.st B roots rS rL).ids.extract 1 (1 + x.T.kept.size))[a]? =
        some (x.st.oracles.size + 1 + a) := fun a h => by
    rw [← Array.getElem?_toList, ha]
    simp [h]
  have hTa : x.T.shape.answers ≠ 0 := by
    have := ((_root_.Tw.K2.targetOk_means x.st x.f.rows x.T).1
      ((_root_.Tw.K2.targetOk_eq x.st x.f.rows x.T).trans F.check)).sampled
    omega
  obtain ⟨m0, e0, s0, p0, d0⟩ := new_at Q x.st B roots rS rL 0 x.T.shape
    (by rw [hs]; exact notices_zero x.T x.others) hTa
  rw [Nat.add_zero] at e0
  have hcopy : ∀ a (h : a < x.T.kept.size), ∃ m,
      (sentAt Q x.st B roots rS rL).st.oracles[x.st.oracles.size + 1 + a]? = some m ∧
        m.shape = x.T.kept[a].shape ∧ m.sampled = true ∧
        m.pad = (padPlaces Q.codes x.T.kept[a].shape).map fun p => (p.part, p.index) :=
    fun a h => by
      have := new_at Q x.st B roots rS rL (1 + a) x.T.kept[a].shape
        (by rw [hs]; exact notices_kept x.T x.others a h)
        (F.keptAnswers _ (Array.mem_toList_iff.2 (Array.getElem_mem h)))
      rwa [← Nat.add_assoc] at this
  refine
    { check := al.check F.check, restMain := F.restMain, fits := al.oldFits F.fits
      keptPos := F.keptPos, seated := ⟨?_, ?_, ?_, ?_⟩
      lengths := by
        show (sentAt Q x.st B roots rS rL).st.codes.lengthsOk = true
        rw [cd]; exact F.lengths
      logC := by
        show ((sentAt Q x.st B roots rS rL).st.codes.base.getD x.f.rows.code default).logN ≤ 32
        rw [cd]; exact F.logC
      logZ := by
        show ((sentAt Q x.st B roots rS rL).st.codes.mask.getD x.f.rows.maskCode default).logN ≤ 32
        rw [cd]; exact F.logZ
      inRange := by
        show ∀ v ∈ (Positions.ofDraws c.logN rL.drawn.poss).all.toList,
          v < 2 ^ ((sentAt Q x.st B roots rS rL).st.codes.base.getD x.f.rows.code default).logN
        rw [cd]; exact F.inRange
      stored := ⟨?_, ?_⟩
      group := by
        show (sentAt Q x.st B roots rS rL).st.groups[x.f.group]? = some G
        rw [sentAt_groups]; exact F.group
      noRun := F.noRun, noMember := F.noMember, groupCode := F.groupCode
      copiesCode := F.copiesCode, sampledG := ?_, sampledCopies := ?_
      tables := al.tables F.fits F.tables
      numbers := by
        show 1 + x.T.kept.size ≤ (sentAt Q x.st B roots rS rL).ids.size
        rw [sentAt_idsSize]; omega
      reads := al.reads F.reads }
  · show ((sentAt Q x.st B roots rS rL).st.oracles[
      (sentAt Q x.st B roots rS rL).ids.getD 0 noId]?).map (fun o : OnBytes.Oracle => o.shape) = _
    rw [hg, e0, Option.map_some, s0]
    rfl
  · intro a k hka
    obtain ⟨h, rfl⟩ := Array.getElem?_eq_some_iff.1 hka
    obtain ⟨m, e, s, _, _⟩ := hcopy a h
    show ((((sentAt Q x.st B roots rS rL).ids.extract 1 (1 + x.T.kept.size))[a]?).bind fun o =>
      ((sentAt Q x.st B roots rS rL).st.oracles[o]?).map fun o : OnBytes.Oracle => o.shape) = _
    rw [hat a h, Option.bind_some, e, Option.map_some, s]
    rfl
  · intro o ho
    show o < (sentAt Q x.st B roots rS rL).st.oracles.size
    rw [sentAt_size]
    have := hk o ho
    omega
  · show ((sentAt Q x.st B roots rS rL).ids.getD 0 noId ::
      ((sentAt Q x.st B roots rS rL).ids.extract 1 (1 + x.T.kept.size)).toList ++
        (switchKept x.f.rows).toList).Nodup
    rw [hg, ha]
    have hnew : ∀ v ∈ (List.range x.T.kept.size).map (x.st.oracles.size + 1 + ·),
        x.st.oracles.size < v := fun v hv => by
      obtain ⟨i, _, rfl⟩ := List.mem_map.1 hv
      omega
    refine List.nodup_cons.2 ⟨fun hin => ?_, List.Nodup.append
      ((List.nodup_range).map fun a b e => by omega) F.fits.once fun v h1 h2 => ?_⟩
    · rcases List.mem_append.1 hin with h | h
      · exact absurd (hnew _ h) (Nat.lt_irrefl _)
      · exact absurd (hk _ h) (Nat.lt_irrefl _)
    · have := hnew v h1
      have := hk v h2
      omega
  · show ((sentAt Q x.st B roots rS rL).st.oracles[
      (sentAt Q x.st B roots rS rL).ids.getD 0 noId]?).map (·.pad) =
        some ((padPlaces (sentAt Q x.st B roots rS rL).st.codes x.T.shape).map fun p =>
          (p.part, p.index))
    rw [hg, e0, Option.map_some, d0, cd, hc]
  · intro a k hka
    obtain ⟨h, rfl⟩ := Array.getElem?_eq_some_iff.1 hka
    obtain ⟨m, e, _, _, d⟩ := hcopy a h
    show ((sentAt Q x.st B roots rS rL).st.oracles[
      ((sentAt Q x.st B roots rS rL).ids.extract 1 (1 + x.T.kept.size)).getD a noId]?).map
        (·.pad) =
      some ((padPlaces (sentAt Q x.st B roots rS rL).st.codes x.T.kept[a].shape).map fun p =>
        (p.part, p.index))
    rw [Array.getD_eq_getD_getElem?, hat a h, Option.getD_some, e, Option.map_some, d, cd, hc]
  · show ((sentAt Q x.st B roots rS rL).st.oracles[
      (sentAt Q x.st B roots rS rL).ids.getD 0 noId]?).map (·.sampled) = some true
    rw [hg, e0, Option.map_some, p0]
  · intro o ho
    have ho' : o ∈ (List.range x.T.kept.size).map (x.st.oracles.size + 1 + ·) := ha ▸ ho
    obtain ⟨a, hr, rfl⟩ := List.mem_map.1 ho'
    obtain ⟨m, e, _, p, _⟩ := hcopy a (List.mem_range.1 hr)
    show ((sentAt Q x.st B roots rS rL).st.oracles[x.st.oracles.size + 1 + a]?).map (·.sampled) = _
    rw [e, Option.map_some, p]

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.numbers_kept
#print axioms VerifiableInference.Desc.K2.Honest.Returns.new_at
#print axioms VerifiableInference.Desc.K2.Honest.Returns.frontFits_sent
#print axioms VerifiableInference.Desc.K2.Honest.Returns.numbers_first
#print axioms VerifiableInference.Desc.K2.Honest.Returns.wr_core
#print axioms VerifiableInference.Desc.K2.Honest.Returns.shapeAt_of
#print axioms VerifiableInference.Desc.K2.Honest.Returns.FrontCore.plain
