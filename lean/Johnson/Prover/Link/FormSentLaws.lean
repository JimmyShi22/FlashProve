-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormSentLaws.lean: THE FORM's HALF AT THE LINK's FRONT: K15's BLOCK WITHOUT A
ROUND ("(rec_gamma), twice": laysRec, Johnson/Desc/K15/K15.lean) RETURNS; the record behind is
written out; and behind it holds what is carried (LinkSeats, Johnson/Prover/Link/FormSeats.lean):
from what stands behind the sending (LinkSent, FormSent.lean).

Main names.
  joinP_yes       a sampled message joins a group.
  FoldMsg.later   a fold's message stays what it is over a joining and over rows.
  mem_groupWith   who is a member behind a joining.
  foldSeat_of_msg a fold is seated, from its message.
  laysOne_yes     one table's share: the record behind is written out, AND EACH ROW LAID IS
    (rec_gamma)'s at a seed of the right length: so that it can be judged again at a later
    statement.
  keys_of, recG1_group, recSt_group, recG1_codes, recSt_codes, FoldMsg.recSt, mem_recG2, seat_recSt,
  laysRec_run     the two shares together, piece by piece.
  laysRec_yes     THE STATEMENT.

Limits. LinkSent is a premise: "LINK point" and the sending in front are not here. The first table's
rows are laid where the first fold alone is a member; that they meet the sentences at the last
statement, with both members, is shown anew from their make.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormSent
import Johnson.Desc.Means.Order

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.Ground
open _root_.Desc.Plain (DState)
open Desc.K15 (St Par15)

/-- **A sampled message joins a group.** -/
theorem joinP_yes {L : Type} (d : DState L) (g o : Nat) (G : Group) (x : OnBytes.Oracle)
    (hG : d.st.groups[g]? = some G) (hx : d.st.oracles[o]? = some x) (hs : x.sampled = true)
    (hi : G.inRun = false) (hc : x.shape.code = G.code) (hz : x.shape.maskRows = 0)
    (hn : o ∉ G.members) : joinP d g o false = some { d with st := withMessageInGroup d.st g o false G } := by
  unfold joinP
  rw [if_pos, hG]
  · rfl
  · unfold Ground.ok joinL
    rw [hG, hx]
    simp [Ground.has, hs, hi, hc, hz, hn]

/-- **A fold's message stays what it is over a joining and over rows laid on a group.** -/
theorem FoldMsg.later {T : Statement} {S : FoldeqShape} {u : FoldedRow} (h : FoldMsg T S u)
    (g o : Nat) (G : Group) (rows : List Row) :
    FoldMsg (withRows (withMessageInGroup T g o false G) g rows) S u := by
  obtain ⟨x, places, h1, h2, h3, h4, h5⟩ := h
  obtain ⟨e1, e2⟩ := withRows_oracles g rows (withMessageInGroup T g o false G)
  unfold FoldMsg
  rw [e1, e2]
  by_cases c : o = u.oracle
  · subst c
    exact ⟨_, places, joined_same T g _ false G x h1, h2, h3, h4, h5⟩
  · exact ⟨x, places, (joined_other T g o false G _ c).trans h1, h2, h3, h4, h5⟩

/-- Who is a member behind a joining. -/
theorem mem_groupWith (G : Group) (o o' : Nat) :
    o' ∈ (groupWith G o).members ↔ o' = o ∨ o' ∈ G.members := by
  show o' ∈ G.members.insertIdxIfInBounds (G.members.filter (· < o)).size o ↔ _
  rw [← Array.mem_toList_iff, Means.toList_insertIdxIfInBounds, ← Array.mem_toList_iff]
  exact List.mem_insertIdx (by rw [Array.length_toList]; exact Array.size_filter_le)

/-- A fold is seated, from its message. -/
theorem foldSeat_of_msg {T : Statement} {G : Group} {S : FoldeqShape} {u : FoldedRow}
    (hm : FoldMsg T S u) (hl : u.lay = vectorLay T.codes S.u S.rowsHigh)
    (hok : foldeqOk T.codes S = true) (hmem : u.oracle ∈ G.members) (hi : G.inRun = false) :
    FoldSeat T G S u := by
  obtain ⟨x, places, h1, h2, _, h4, h5⟩ := hm
  exact foldSeat_of T G S u x places h1 h2 h4 h5 hl hok hmem hi

/-- **One table's share of "(rec_gamma), twice".** b: which table. -/
theorem laysOne_yes (p : Par15) (d : St) (G : Group) (b : Bool) (key : TableKey) (u : FoldedRow)
    (hG : d.st.groups[d.loc.g]? = some G) (hi : G.inRun = false) (hc : G.code = p.S.code)
    (hn : u.oracle ∉ G.members) (hm : FoldMsg d.st (p.S.side b p.samples) u)
    (hl : u.lay = vectorLay d.st.codes (p.S.side b p.samples).u p.S.rowsHigh)
    (hok : foldeqOk d.st.codes (p.S.side b p.samples) = true)
    (hk : Own.keyFits key p.S.table = true) (hg : d.loc.gamma.length = p.S.table.v) :
    ∃ rows : List Row,
      Desc.K15.laysOne p d key u =
        some { d with st := withRows (withMessageInGroup d.st d.loc.g u.oracle false G) d.loc.g rows } ∧
      ∀ row ∈ rows, ∃ (seed : SampleSeed) (a : Nat), seed.z.length = p.S.table.cubeBits ∧
        Desc.K14.recGamma p.S.table seed a (Desc.K15.weights d.loc) key.record u = some row := by
  have hm' := hm
  obtain ⟨x, places, h1, h2, h3, h4, h5⟩ := hm
  have hj := joinP_yes d d.loc.g u.oracle G x hG h1 h3 hi (by rw [h2, hc]; rfl) (by rw [h2]; rfl) hn
  have hG1 : (withMessageInGroup d.st d.loc.g u.oracle false G).groups[d.loc.g]? =
      some (groupWith G u.oracle) := joined_group d.st d.loc.g u.oracle false G hG
  have hseat : FoldSeat (withMessageInGroup d.st d.loc.g u.oracle false G) (groupWith G u.oracle)
      (p.S.side b p.samples) u :=
    foldSeat_of_msg (hm'.later d.loc.g u.oracle G []) hl hok
      ((mem_groupWith G u.oracle u.oracle).2 (Or.inl rfl)) hi
  unfold Own.keyFits at hk
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hk
  obtain ⟨⟨k1, k2⟩, k3⟩ := hk
  have hw : (Desc.K15.weights d.loc).size = p.S.table.rows := by
    unfold Desc.K15.weights
    rw [Desc.K14.Law.eqTable_size, hg]
    rfl
  have hseed : ∀ y ∈ key.seeds.zipIdx, y.1 ∈ key.seeds ∧ y.2 < key.seeds.length := fun y hy =>
    ⟨(List.mem_zipIdx' hy).2 ▸ List.getElem_mem _, (List.mem_zipIdx' hy).1⟩
  obtain ⟨rows, r1, r2⟩ := mapM_some (fun y : SampleSeed × Nat =>
      Desc.K14.recGamma p.S.table y.1 y.2 (Desc.K15.weights d.loc) key.record u) key.seeds.zipIdx
    fun y hy => recGamma_some p.S.table y.1 y.2 _ _ u (k3 y.1 (hseed y hy).1) (le_of_eq hw.symm)
      (by rw [← k2]; exact (hseed y hy).2) (le_of_eq k1.symm)
  have hmade : ∀ row ∈ rows, ∃ (seed : SampleSeed) (a : Nat),
      seed.z.length = p.S.table.cubeBits ∧
      Desc.K14.recGamma p.S.table seed a (Desc.K15.weights d.loc) key.record u = some row := by
    intro row hrow
    obtain ⟨y, hy, e⟩ := r2 row hrow
    exact ⟨y.1, y.2, k3 y.1 (hseed y hy).1, e⟩
  have hcl : ∀ row ∈ rows, K9L.RowClauses (withMessageInGroup d.st d.loc.g u.oracle false G)
      (groupWith G u.oracle) row := by
    intro row hrow
    obtain ⟨seed, a, hz, e⟩ := hmade row hrow
    exact recGamma_clauses _ _ (p.S.side b p.samples) seed a _ _ u row e hz hseat
  refine ⟨rows, ?_, hmade⟩
  unfold Desc.K15.laysOne
  rw [hj]
  show (do
    addRowsP { d with st := withMessageInGroup d.st d.loc.g u.oracle false G } d.loc.g
      (← key.seeds.zipIdx.mapM fun y : SampleSeed × Nat =>
        Desc.K14.recGamma p.S.table y.1 y.2 (Desc.K15.weights d.loc) key.record u)) = _
  rw [r1]
  exact addRowsP_yes { d with st := withMessageInGroup d.st d.loc.g u.oracle false G } d.loc.g _ rows hG1 hi hcl

/-! ## The two shares together -/

/-- What the tests in front of (rec_gamma) say. -/
theorem keys_of (p : Par15) (l : Desc.K15.Tie) (h : Ground.ok (Desc.K15.laysRecL p l) = true) :
    Own.keyFits l.key0 p.S.table = true ∧ Own.keyFits l.key1 p.S.table = true ∧
      l.gamma.length = p.S.table.v := by
  simp only [Ground.ok, Desc.K15.laysRecL, Desc.K15.keyL, List.all_append, List.all_cons,
    List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.2.1, h.1.2.2⟩

theorem recG1_group (T : Statement) (g o0 : Nat) (G : Group) (rows0 : List Row)
    (hG : T.groups[g]? = some G) :
    (withRows (withMessageInGroup T g o0 false G) g rows0).groups[g]? = some (recG1 G o0 rows0) :=
  withRows_group g rows0 _ _ (joined_group T g o0 false G hG)

theorem recSt_group (T : Statement) (g o0 o1 : Nat) (G : Group) (rows0 rows1 : List Row)
    (hG : T.groups[g]? = some G) :
    (recSt T g o0 o1 G rows0 rows1).groups[g]? = some (recG2 G o0 o1 rows0 rows1) :=
  withRows_group g rows1 _ _ (joined_group _ g o1 false _ (recG1_group T g o0 G rows0 hG))

theorem recG1_codes (T : Statement) (g o0 : Nat) (G : Group) (rows0 : List Row) :
    (withRows (withMessageInGroup T g o0 false G) g rows0).codes = T.codes := (withRows_oracles g rows0 _).2

theorem recSt_codes (T : Statement) (g o0 o1 : Nat) (G : Group) (rows0 rows1 : List Row) :
    (recSt T g o0 o1 G rows0 rows1).codes = T.codes :=
  ((withRows_oracles g rows1 _).2).trans (recG1_codes T g o0 G rows0)

theorem FoldMsg.recSt {T : Statement} {S : FoldeqShape} {u : FoldedRow} (h : FoldMsg T S u)
    (g o0 o1 : Nat) (G : Group) (rows0 rows1 : List Row) :
    FoldMsg (Johnson.Prover.Link.recSt T g o0 o1 G rows0 rows1) S u :=
  (h.later g o0 G rows0).later g o1 (recG1 G o0 rows0) rows1

theorem mem_recG2 (G : Group) (o0 o1 : Nat) (rows0 rows1 : List Row) :
    o0 ∈ (recG2 G o0 o1 rows0 rows1).members ∧ o1 ∈ (recG2 G o0 o1 rows0 rows1).members :=
  ⟨(mem_groupWith (recG1 G o0 rows0) o1 o0).2 (Or.inr ((mem_groupWith G o0 o0).2 (Or.inl rfl))),
    (mem_groupWith (recG1 G o0 rows0) o1 o1).2 (Or.inl rfl)⟩

/-- A fold is seated behind "(rec_gamma), twice". -/
theorem seat_recSt {T : Statement} {S : FoldeqShape} {u : FoldedRow} (g o0 o1 : Nat) (G : Group)
    (rows0 rows1 : List Row) (hm : FoldMsg T S u) (hl : u.lay = vectorLay T.codes S.u S.rowsHigh)
    (hok : foldeqOk T.codes S = true) (hi : G.inRun = false)
    (hu : u.oracle ∈ (recG2 G o0 o1 rows0 rows1).members) :
    FoldSeat (recSt T g o0 o1 G rows0 rows1) (recG2 G o0 o1 rows0 rows1) S u :=
  foldSeat_of_msg (hm.recSt g o0 o1 G rows0 rows1) (by rw [recSt_codes]; exact hl)
    (by rw [recSt_codes]; exact hok) hu hi

/-- The two shares run one behind the other. -/
theorem laysRec_run (p : Par15) (d : St) (G : Group) (rs : List Fmt.RoundView) (H : LinkSent p d G) :
    ∃ rows0 rows1 : List Row,
      Desc.K15.laysRec p d rs = some { d with
        st := recSt d.st d.loc.g d.loc.o0.oracle d.loc.o1.oracle G rows0 rows1 } ∧
      (∀ row ∈ rows0, ∃ (seed : SampleSeed) (a : Nat), seed.z.length = p.S.table.cubeBits ∧
        Desc.K14.recGamma p.S.table seed a (Desc.K15.weights d.loc) d.loc.key0.record d.loc.o0 =
          some row) ∧
      ∀ row ∈ rows1, ∃ (seed : SampleSeed) (a : Nat), seed.z.length = p.S.table.cubeBits ∧
        Desc.K14.recGamma p.S.table seed a (Desc.K15.weights d.loc) d.loc.key1.record d.loc.o1 =
          some row := by
  obtain ⟨k0, k1, hg⟩ := keys_of p d.loc H.keys
  obtain ⟨rows0, e0, made0⟩ := laysOne_yes p d G false d.loc.key0 d.loc.o0 H.group H.idle H.code
    (by rw [H.empty]; simp) H.m0 H.lay0 H.ok0 k0 hg
  have hn1 : d.loc.o1.oracle ∉ (recG1 G d.loc.o0.oracle rows0).members := by
    intro c
    rcases (mem_groupWith G _ _).1 c with c | c
    · exact H.two c.symm
    · rw [H.empty] at c
      simp at c
  obtain ⟨rows1, e1, made1⟩ := laysOne_yes p
    { d with st := withRows (withMessageInGroup d.st d.loc.g d.loc.o0.oracle false G) d.loc.g rows0 }
    (recG1 G d.loc.o0.oracle rows0) true d.loc.key1 d.loc.o1
    (recG1_group d.st d.loc.g _ G rows0 H.group) H.idle H.code hn1 (H.m1.later _ _ _ _)
    (by rw [recG1_codes]; exact H.lay1) (by rw [recG1_codes]; exact H.ok1) k1 hg
  refine ⟨rows0, rows1, ?_, made0, made1⟩
  unfold Desc.K15.laysRec
  rw [H.keys]
  show (do
    let d ← Desc.K15.laysOne p d d.loc.key0 d.loc.o0
    Desc.K15.laysOne p d d.loc.key1 d.loc.o1) = _
  rw [e0]
  exact e1

/-- **"(rec_gamma), twice" says yes.** -/
theorem laysRec_yes (p : Par15) (d : St) (G : Group) (rs : List Fmt.RoundView) (H : LinkSent p d G) :
    ∃ rows0 rows1,
      Desc.K15.laysRec p d rs = some { d with
        st := recSt d.st d.loc.g d.loc.o0.oracle d.loc.o1.oracle G rows0 rows1 } ∧
      LinkSeats p { d with
          st := recSt d.st d.loc.g d.loc.o0.oracle d.loc.o1.oracle G rows0 rows1 }
        (recG2 G d.loc.o0.oracle d.loc.o1.oracle rows0 rows1) := by
  obtain ⟨rows0, rows1, e, made0, made1⟩ := laysRec_run p d G rs H
  have s0 := seat_recSt d.loc.g d.loc.o0.oracle d.loc.o1.oracle G rows0 rows1 H.m0 H.lay0 H.ok0
    H.idle (mem_recG2 G _ _ rows0 rows1).1
  have s1 := seat_recSt d.loc.g d.loc.o0.oracle d.loc.o1.oracle G rows0 rows1 H.m1 H.lay1 H.ok1
    H.idle (mem_recG2 G _ _ rows0 rows1).2
  refine ⟨rows0, rows1, e, recSt_group d.st d.loc.g _ _ G rows0 rows1 H.group, s0, s1,
    (keys_of p d.loc H.keys).2.2, fun row hrow => ?_⟩
  have hrow' : row ∈ rows0 ++ rows1 := by
    have : row ∈ ((G.rows ++ rows0.toArray) ++ rows1.toArray).toList := hrow
    rw [H.bare] at this
    simpa using this
  rcases List.mem_append.1 hrow' with c | c
  · obtain ⟨seed, a, hz, e⟩ := made0 row c
    exact recGamma_clauses _ _ (p.S.side false p.samples) seed a _ _ _ row e hz s0
  · obtain ⟨seed, a, hz, e⟩ := made1 row c
    exact recGamma_clauses _ _ (p.S.side true p.samples) seed a _ _ _ row e hz s1

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.joinP_yes
#print axioms Johnson.Prover.Link.FoldMsg.later
#print axioms Johnson.Prover.Link.mem_groupWith
#print axioms Johnson.Prover.Link.foldSeat_of_msg
#print axioms Johnson.Prover.Link.laysOne_yes
#print axioms Johnson.Prover.Link.keys_of
#print axioms Johnson.Prover.Link.recG1_group
#print axioms Johnson.Prover.Link.recSt_group
#print axioms Johnson.Prover.Link.recG1_codes
#print axioms Johnson.Prover.Link.recSt_codes
#print axioms Johnson.Prover.Link.FoldMsg.recSt
#print axioms Johnson.Prover.Link.mem_recG2
#print axioms Johnson.Prover.Link.seat_recSt
#print axioms Johnson.Prover.Link.laysRec_run
#print axioms Johnson.Prover.Link.laysRec_yes
