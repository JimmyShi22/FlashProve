-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/BehindAt.lean: THE STEP BEHIND THE SENDING OF A CODE SWITCH BETWEEN
TWO SEGMENTS (`switchBehind`, Johnson/Top/H0/Tw/K2/Switch.lean) RETURNS: THE LAW WITH ITS PREMISES
AT WHAT THE STEP IS HANDED: the statement behind the sending, IN FRONT OF the joins. Statements and
proofs.

  `TablesFit`, `TablesFit.make`   the tables have at most 63 index bits; the claim's forms and the
                    kept members' stored sample rows fit their tables; carried to a statement that
                    is alike
  `FrontFits`       all premises, on i: the public ones of `SwitchRowsHold` · the pads are stored ·
                    the group is there, its test has not begun, IT HAS NO MEMBER, its main code is
                    g's and the copies' · g and the copies are sampled · `TablesFit` · and two
                    clauses of «the rows can be made» that follow from nothing else: numbers enough
                    · the stored rows read their member's main table alone
  `copies_list`     the copies with their targets, as a list
  `joinedAt`        THE STATEMENT BEHIND THE JOINS, AS A TERM (`joinedAll`, Returns/Joins.lean)
  `switchBehind_returns_at`   the step returns `joinedAt` with the made rows appended to the group's
                    open rows; and of that term: the codes and every message's core are as in front;
                    the group's test has not begun, its codes and its open rows in front of the made
                    ones are as in front, its members are g and the copies

WHAT IS STILL A PREMISE IN THE FORM «… = .ok …»: that the reading of the old rows returns
(`readOld`).

WHO MUST LEAVE WHAT, for a caller that lays this law behind the switch's front and the sending. THE
SENDING (between the front and this step) must leave: `seated` · `stored` · `sampledG` ·
`sampledCopies` · `numbers`; and must keep, from in front of it: `check` (the kind's own guard
stands at the statement in front of the sending) · `fits` · `tables` · `reads` · `lengths` · the two
lengths. THE FRONT must leave, and the sending keep: `group` · `noRun` · `noMember` · `groupCode` ·
`copiesCode`. THE PLAN's TARGET must have: `restMain` · `keptPos`. THE ROUND "LOC" must leave:
`inRange`. THE READING must leave: one symbol for each row at each position (the law's premise
beside `FrontFits`; paid in Returns/Read.lean). No lemma here shows any of the others.

Limits. Targets whose rest lies in g's main part alone. Nothing on any property.

-/
import Johnson.Desc.K2.Honest.Returns.Behind
import Johnson.Desc.K2.Honest.Returns.Alike

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open OnBytes.Slice (withRows withMessageInGroup)
open _root_.Tw.K2 (SwIn SwOut readOld joinG switchBehind readsMainOf)
open VerifiableInference.Desc.First.K2 (locOk outOf)

/-- The tables' sizes, the claim's forms and the stored sample rows. -/
structure TablesFit (S : Statement) (old : SingleRows) (T : SwitchTarget) : Prop where
  bitsG : switchRowBits T .main + (S.codes.base.getD T.shape.code default).logEll ≤ 63
  bitsKept : ∀ s ∈ (sizesAt S old T).kept,
    ceilLog2 s.mainRows + (S.codes.base.getD old.code default).logEll ≤ 63
  claimMain : Own.formFits old.c (S.codes.base.getD old.code default).logEll = true
  claimKept : ∀ f ∈ old.kept.toList, Own.formFits f.c (S.tableBits f.oracle .main) = true
  stored : ∀ o ∈ (switchKept old).toList, ∀ r ∈ (S.oracles.getD o default).sampleRows.toList,
    (∀ t ∈ r.terms.toList, t.v.pairs.length = S.tableBits o .main ∧ Own.InOrder t.v) ∧
      ∀ u ∈ r.units.toList, u.index < 2 ^ S.tableBits o .main

/-- Carried to a statement that is alike, with the group's members. -/
theorem TablesFit.make {S S' : Statement} {old : SingleRows} {T : SwitchTarget} {g : Nat}
    {anew : Array Nat} {G : Group} (F : TablesFit S old T) (h : Alike S S')
    (h1 : G.members.contains g = true) (h2 : ∀ o ∈ anew.toList, G.members.contains o = true) :
    MakeFits S' old T g anew G :=
  ⟨h1, h2, by rw [h.codes]; exact F.bitsG, by rw [h.sizes, h.codes]; exact F.bitsKept,
    by rw [h.codes]; exact F.claimMain, fun f hf => by rw [h.bits]; exact F.claimKept f hf,
    fun o ho => by rw [h.rowsD, h.bits]; exact F.stored o ho⟩

/-- **All premises on what the step is handed**, but for the symbols' count. c: the old main code.
G: the group in front of the joins. -/
structure FrontFits (i : SwIn) (c : Code) (G : Group) : Prop where
  check : switchTargetCheck i.st i.old i.T = true
  restMain : i.T.rest.part = .main
  fits : OldFits i.st i.old
  keptPos : ∀ k ∈ i.T.kept.toList, 0 < k.shape.mainRows
  seated : SeatedAt i.st i.old i.T (i.ids.getD 0 noId) (i.ids.extract 1 (1 + i.T.kept.size))
  lengths : i.st.codes.lengthsOk = true
  logC : (i.st.codes.base.getD i.old.code default).logN ≤ 32
  logZ : (i.st.codes.mask.getD i.old.maskCode default).logN ≤ 32
  inRange : ∀ x ∈ (Positions.ofDraws c.logN i.drawn.poss).all.toList,
    x < 2 ^ (i.st.codes.base.getD i.old.code default).logN
  stored : PadsStored i.st i.T (i.ids.getD 0 noId) (i.ids.extract 1 (1 + i.T.kept.size))
  group : i.st.groups[i.grp]? = some G
  noRun : G.inRun = false
  noMember : G.members = #[]
  groupCode : i.T.shape.code = G.code
  copiesCode : ∀ k ∈ i.T.kept.toList, k.shape.code = G.code
  sampledG : (i.st.oracles[i.ids.getD 0 noId]?).map (·.sampled) = some true
  sampledCopies : ∀ o ∈ (i.ids.extract 1 (1 + i.T.kept.size)).toList,
    (i.st.oracles[o]?).map (·.sampled) = some true
  tables : TablesFit i.st i.old i.T
  numbers : 1 + i.T.kept.size ≤ i.ids.size
  reads : ∀ o ∈ (switchKept i.old).toList,
    ∀ r ∈ (i.st.oracles.getD o default).sampleRows.toList, readsMainOf o r = true

/-- The copies with their targets, as a list: entry by entry; and the copies' numbers alone. -/
theorem copies_list (anew : Array Nat) (kept : Array KeptTarget) (hsz : anew.size = kept.size) :
    (∀ p ∈ (anew.zip kept).toList, ∃ a : Nat, anew[a]? = some p.1 ∧ kept[a]? = some p.2) ∧
      (anew.zip kept).toList.map (·.1) = anew.toList := by
  rw [Array.toList_zip]
  refine ⟨fun p hp => ?_, List.map_fst_zip (by simp [hsz])⟩
  obtain ⟨a, ha⟩ := List.mem_iff_getElem?.1 hp
  obtain ⟨h1, h2⟩ := List.getElem?_zip_eq_some.1 ha
  exact ⟨a, by rw [← Array.getElem?_toList]; exact h1, by rw [← Array.getElem?_toList]; exact h2⟩

/-- **The statement behind the joins, as a term**: g joins the group, not kept; then the copies, in
their order, each kept if its target says "kept again". G: the group in front. -/
def joinedAt (i : SwIn) (G : Group) : Statement :=
  joinedAll i.grp (fun p : Nat × KeptTarget => p.1) (fun p => p.2.keptAgain)
    ((i.ids.extract 1 (1 + i.T.kept.size)).zip i.T.kept).toList
    (withMessageInGroup i.st i.grp (i.ids.getD 0 noId) false G)

/-- **The step behind the sending returns**: the premises stand at what it is handed; what it
returns is a term: `joinedAt` with the made rows appended to the group's open rows. -/
theorem switchBehind_returns_at (i : SwIn) (c : Code) (B : TreeBook)
    (left : List _root_.Tw.K2.Col) (y : Array E) (G : Group)
    (hCode : i.st.codes.base[i.old.code]? = some c) (hLoc : locOk i c.logN = true)
    (hRead : readOld i (Positions.ofDraws c.logN i.drawn.poss) = .ok (B, left, y))
    (hy : y.size = (Positions.ofDraws c.logN i.drawn.poss).all.size * i.old.rows)
    (F : FrontFits i c G) :
    ∃ S3 G3 rows, S3 = joinedAt i G ∧ Alike i.st S3 ∧ S3.groups[i.grp]? = some G3 ∧
      G3.inRun = false ∧ G3.code = G.code ∧ G3.maskCode = G.maskCode ∧ G3.rows = G.rows ∧
      (∀ o, o ∈ G3.members.toList ↔ o = i.ids.getD 0 noId ∨
        o ∈ (i.ids.extract 1 (1 + i.T.kept.size)).toList) ∧
      Own.swRows S3 i.old i.T (i.ids.getD 0 noId) (i.ids.extract 1 (1 + i.T.kept.size))
        (Positions.ofDraws c.logN i.drawn.poss) y = some rows ∧
      switchBehind i = .ok ⟨withRows S3 i.grp rows, B, left,
        outOf i (Positions.ofDraws c.logN i.drawn.poss)⟩ := by
  have A := atPublic F.check F.restMain F.fits F.keptPos F.seated F.lengths
  have hsz : (i.ids.extract 1 (1 + i.T.kept.size)).size = i.T.kept.size := by
    have := F.numbers
    rw [Array.size_extract]
    omega
  obtain ⟨hzip, hfst⟩ := copies_list _ i.T.kept hsz
  have hap := F.seated.apart
  rw [List.cons_append, List.nodup_cons, List.nodup_append] at hap
  have hgNot : i.ids.getD 0 noId ∉ (i.ids.extract 1 (1 + i.T.kept.size)).toList :=
    fun h => hap.1 (List.mem_append_left _ h)
  -- g joins
  obtain ⟨xg, hxg, hsg⟩ := Option.map_eq_some_iff.1 F.seated.carrying
  have hsamp : xg.sampled = true := by
    have h := F.sampledG
    rw [hxg] at h
    exact Option.some.inj h
  have j1 := joinG_returns i.st i.grp (i.ids.getD 0 noId) false G xg F.group hxg hsamp F.noRun
    (Or.inr (by rw [hsg]; exact F.groupCode)) (Or.inl (by rw [hsg]; exact g_bare A))
    (by rw [F.noMember]; simp) (fun h => by cases h)
  have hG2 := group_joined i.st i.grp (i.ids.getD 0 noId) false G
  rw [F.group] at hG2
  -- the copies join
  obtain ⟨S3, G3, f0, f1, f2, f3, f4, f5, f9, f6, f7, f8⟩ := joins_return i.grp
    (fun p : Nat × KeptTarget => p.1) (fun p => p.2.keptAgain)
    ((i.ids.extract 1 (1 + i.T.kept.size)).zip i.T.kept).toList
    (withMessageInGroup i.st i.grp (i.ids.getD 0 noId) false G) _ hG2 F.noRun
    (fun p hp => by
      obtain ⟨a, h1, h2⟩ := hzip p hp
      have hk : p.2 ∈ i.T.kept.toList := by
        rw [← Array.getElem?_toList] at h2
        exact List.mem_of_getElem? h2
      have ho : p.1 ∈ (i.ids.extract 1 (1 + i.T.kept.size)).toList := by
        rw [← Array.getElem?_toList] at h1
        exact List.mem_of_getElem? h1
      have hs := F.seated.copies a p.2 h2
      rw [h1] at hs
      obtain ⟨x, hx, hxs⟩ := Option.map_eq_some_iff.1 (show (i.st.oracles[p.1]?).map
        (fun x : OnBytes.Oracle => x.shape) = some p.2.shape from hs)
      obtain ⟨_, _, K⟩ := kept_shape A a p.2 h2
      have hsa : x.sampled = true := by
        have h := F.sampledCopies p.1 ho
        rw [hx] at h
        exact Option.some.inj h
      exact MayJoin.of_core (S := i.st) ⟨x, hx, hsa,
        Or.inr (by rw [hxs]; exact F.copiesCode p.2 hk),
        Or.inl (by rw [hxs]; exact K.newBare), fun _ => by rw [hxs]; exact F.keptPos p.2 hk⟩
        (oracle_joined i.st i.grp _ false G p.1))
    (fun p hp hm => by
      obtain ⟨a, h1, _⟩ := hzip p hp
      have ho : p.1 ∈ (i.ids.extract 1 (1 + i.T.kept.size)).toList := by
        rw [← Array.getElem?_toList] at h1
        exact List.mem_of_getElem? h1
      rcases (mem_joined G.members (i.ids.getD 0 noId) p.1).1 hm with h | h
      · rw [F.noMember] at h
        exact absurd h (by simp)
      · exact hgNot (h ▸ ho))
    (by rw [hfst]; exact hap.2.1)
  have hAl : Alike i.st S3 := ⟨f7, fun o => (f8 o).trans (oracle_joined i.st i.grp _ false G o)⟩
  have hmem : ∀ o, o ∈ G3.members.toList ↔ o = i.ids.getD 0 noId ∨
      o ∈ (i.ids.extract 1 (1 + i.T.kept.size)).toList := by
    intro o
    rw [f6 o, hfst]
    show o ∈ (G.members.insertIdxIfInBounds _ _).toList ∨ _ ↔ _
    rw [mem_joined, F.noMember]
    simp
  have hcont : ∀ o, o ∈ G3.members.toList → G3.members.contains o = true := fun o h => by
    simpa using Array.mem_toList_iff.1 h
  have hJoinKept : ((i.ids.extract 1 (1 + i.T.kept.size)).zip i.T.kept).foldlM (fun S p =>
      joinG S i.grp p.1 p.2.keptAgain) (withMessageInGroup i.st i.grp (i.ids.getD 0 noId) false G) =
      .ok S3 := by
    rw [← Array.foldlM_toList]
    exact f1
  have FT := (_root_.Tw.K2.targetOk_means i.st i.old i.T).1
    ((_root_.Tw.K2.targetOk_eq i.st i.old i.T).trans F.check)
  have BF : BehindFits i c y S3 G3 :=
    { check := hAl.check F.check, restMain := F.restMain, fits := hAl.old F.fits
      keptPos := F.keptPos, seated := hAl.seated F.seated
      lengths := by rw [hAl.codes]; exact F.lengths
      logC := by rw [hAl.codes]; exact F.logC
      logZ := by rw [hAl.codes]; exact F.logZ
      inRange := by rw [hAl.codes]; exact F.inRange
      stored := hAl.stored F.stored, group := f2, noRun := f3
      make := F.tables.make hAl (hcont _ ((hmem _).2 (Or.inl rfl)))
        fun o ho => hcont _ ((hmem _).2 (Or.inr ho))
      members := fun o ho => by
        rcases (hmem o).1 ho with h | h
        · exact Or.inl h
        · obtain ⟨a, ha⟩ := List.mem_iff_getElem?.1 h
          have hlt : a < (i.ids.extract 1 (1 + i.T.kept.size)).size := by
            have := (List.getElem?_eq_some_iff.1 ha).1
            rw [Array.length_toList] at this
            exact this
          rw [Array.getElem?_toList] at ha
          refine Or.inr ⟨a, i.T.kept[a]'(by omega), Array.getElem?_eq_getElem (by omega), ?_⟩
          rw [Array.getD_eq_getD_getElem?, ha]
          rfl
      can := rowsCan_of S3 i.old i.T _ c.logN i.drawn.poss y (hAl.target FT) (hAl.old F.fits)
        hy (hsz.trans FT.keptCount) (hAl.reads F.reads) }
  obtain ⟨rows, h1, h2⟩ :=
    switchBehind_returns i c B left y _ S3 G3 hCode hLoc hRead j1 hJoinKept BF
  exact ⟨S3, G3, rows, f0, hAl, f2, f3, f4, f5, f9, hmem, h1, h2⟩

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.switchBehind_returns_at
