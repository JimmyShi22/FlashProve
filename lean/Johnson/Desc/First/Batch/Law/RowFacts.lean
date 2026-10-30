-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/RowFacts.lean
(kind K9's soundness lemma): THEOREMS: what the closing of a segment's group asks
of each open row, shown of the row that K9.door lays.
  asRow_plain   the row that K9.asRow makes has no structured vector of the sort "term" and no
                single entry; its runs have the step 1.
  door_row      **where K9.door returns, the row that it has pushed onto the group's rows**
                · fits (the library's RowFits, OnBytes/Iop/RowLaws.lean), at the statement behind
                  the door;
                · fits on masks (the library's MaskFits, OnBytes/Iop/MaskLaws.lean), at every
                  layout of a group: it has no term;
                · NAMES THE GROUP's MEMBERS ALONE: on every entry of both tables of an oracle
                  message that is no member of the segment's group its coefficient reads as 0.
  door_row'     and, of the same row: on a table that an oracle message does not have
                (Statement.has) its coefficients read as 0.
From the door's own tests on the row ("the forms fit their places", "the runs fit their places").
Not claimed: anything on the layout that a closing makes of the group's members.

-/
import OnBytes.Iop.MaskLaws
import Johnson.Desc.First.Batch.Law.Carry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (Ans Equation equation asRow St door)

theorem addTerms_keeps (Rr : ReqRows) (f : ReqFrame) (S : Statement) :
    ∀ (ts : List ReqTerm) (row row' : OnBytes.Row), Rr.addTerms f S ts row = some row' →
      row'.terms = row.terms ∧ row'.units = row.units
  | [], row, row', h => by
    have e : row = row' := Option.some.inj h
    subst e
    exact ⟨rfl, rfl⟩
  | t :: ts, row, row', h => by
    rw [ReqRows.addTerms] at h
    obtain ⟨a, _, h⟩ := some_bind h
    obtain ⟨o', _, h⟩ := some_bind h
    obtain ⟨c, _, h⟩ := some_bind h
    exact addTerms_keeps Rr f S ts (row.addForm o' c) row' h

/-- The sorts of summands of the row that K9.asRow makes. -/
theorem asRow_plain {X : Type} (Rr : ReqRows) (f : ReqFrame) (q : Equation) (d d' : St X)
    (row : OnBytes.Row) (h : asRow Rr f q d = .ok (row, d')) :
    row.terms = #[] ∧ row.units = #[] ∧ ∀ w ∈ row.runs.toList, w.step = 1 := by
  unfold asRow at h
  obtain ⟨row0, h0, h⟩ := ok_bind h
  obtain ⟨k1, k2⟩ := addTerms_keeps Rr f d.st _ {} row0 (termsRow_ok _ _ _ _ _ _ h0)
  obtain ⟨_, k3, _⟩ := addTerms_forms Rr f d.st _ {} row0 (termsRow_ok _ _ _ _ _ _ h0)
  by_cases he : q.onMasks.isEmpty = true
  · simp only [he, if_true] at h
    have e1 : row = { row0 with target := subE zeroE q.constant } :=
      (congrArg Prod.fst (Except.ok.inj h)).symm
    rw [e1]
    refine ⟨k1, k2, fun w hw => ?_⟩
    have hw' : w ∈ row0.runs.toList := hw
    rw [k3] at hw'
    simp at hw'
  · simp only [he, Bool.false_eq_true, if_false] at h
    obtain ⟨m, _, h⟩ := ok_bind h
    obtain ⟨_, _, h⟩ := ok_bind h
    obtain ⟨o', _, h⟩ := ok_bind h
    obtain ⟨x, _, h⟩ := ok_bind h
    obtain ⟨_, _, h⟩ := ok_bind h
    have e1 : row = { row0.addRun o' .mask 0 1 (.own q.onMasks) with
        target := subE zeroE q.constant } := (congrArg Prod.fst (Except.ok.inj h)).symm
    rw [e1]
    refine ⟨k1, k2, fun w hw => ?_⟩
    have hw' : w ∈ (row0.runs.push ⟨o', .mask, 0, 1, .own q.onMasks⟩).toList := hw
    rw [k3] at hw'
    have e : w = ⟨o', .mask, 0, 1, .own q.onMasks⟩ := by simpa using hw'
    rw [e]

theorem rowFits_bits (S S' : Statement) (h : SameBits S S') (row : OnBytes.Row)
    (hr : RowFits S row) : RowFits S' row :=
  ⟨fun t ht => by rw [(h _ _).1]; exact hr.terms t ht, hr.runs,
    fun f hf v hv => by rw [(h _ _).1]; exact hr.forms f hf v hv⟩

variable {K : Type} [CommRing K] (ρ : Reading K)

/-- **The row that the door lays**, with one clause more than door_row: on a table that an oracle
message does not have, the row's coefficients read as 0. -/
theorem door_row' {X : Type} (owed laid : Option Nat) (L : LinkCtx) (F : Fork) (d : St X)
    (out : K9.Out X) (h : door owed laid L F d = .ok out) :
    ∃ (row : OnBytes.Row) (d1 : St X) (G0 : Group),
      out.d = { d1 with st := Slice.withRow d1.st L.check.group row } ∧
      d.st.groups[L.check.group]? = some G0 ∧ RowFits out.d.st row ∧
      (∀ Lg, MaskFits out.d.st Lg row) ∧
      (∀ o, G0.members.contains o = false → ∀ e,
        ρ.val (row.coefficient o .main e) = 0 ∧ ρ.val (row.coefficient o .mask e) = 0) ∧
      ∀ o part, out.d.st.has o part = false → ∀ e, ρ.val (row.coefficient o part e) = 0 := by
  obtain ⟨n, q, G, row, d1, _, hq, _, hr, ho, _, _⟩ := door_parts owed laid L F d out h
  obtain ⟨G0, hG0⟩ := Option.isSome_iff_exists.mp (door_group _ _ _ _ _ _ h)
  have hg1 : d1.st.groups = d.st.groups := asRow_groups _ _ _ _ _ _ hr
  obtain ⟨p1, _, p3⟩ := asRow_plain _ _ _ _ _ _ hr
  obtain ⟨s1, s2⟩ := asRow_shape _ _ _ _ _ _ hr
  obtain ⟨c1, c2, _, _, _⟩ := asRow_coef ρ _ _ q d d1 row (equation_k9 _ _ _ _ hq) hr
  -- the door's tests on the row
  have htests : (∀ fm ∈ row.forms.toList, G0.members.contains fm.oracle = true ∧
      fm.c.fits (d1.st.tableBits fm.oracle .main) = true ∧ d1.st.has fm.oracle .main = true) ∧
      ∀ w ∈ row.runs.toList, G0.members.contains w.oracle = true ∧
        d1.st.has w.oracle w.part = true := by
    unfold door at h
    obtain ⟨_, _, h⟩ := ok_bind h
    obtain ⟨x, hx, h⟩ := ok_bind h
    obtain ⟨_, _, h⟩ := ok_bind h
    obtain ⟨_, _, h⟩ := ok_bind h
    obtain ⟨_, _, h⟩ := ok_bind h
    obtain ⟨y, hy, h⟩ := ok_bind h
    obtain ⟨d2, hd, h⟩ := ok_bind h
    have ex : x = (q, G) := Except.ok.inj (hx.symm.trans hq)
    subst ex
    have ey : y = (row, d1) := Except.ok.inj (hy.symm.trans hr)
    subst ey
    have hd' := there_ok hd
    unfold Ground.addRowP at hd'
    split at hd'
    · rename_i hok
      simp only [Ground.ok, Ground.rowL, List.all_cons, List.all_nil, Bool.and_eq_true,
        Bool.and_true] at hok
      obtain ⟨_, _, _, _, _, hruns, hforms, _⟩ := hok
      simp only [Ground.has, hg1, hG0, Option.map_some, Option.getD_some,
        Array.all_eq_true_iff_forall_mem, Bool.and_eq_true, ← Own.placeFits_agrees,
        ← Own.formFits_agrees, Blk.placeOk] at hruns hforms
      exact ⟨fun fm hfm => ⟨(hforms fm (Array.mem_toList_iff.mp hfm)).1.1.1.1,
          (hforms fm (Array.mem_toList_iff.mp hfm)).2,
          (hforms fm (Array.mem_toList_iff.mp hfm)).1.1.1.2⟩,
        fun w hw => ⟨(hruns w (Array.mem_toList_iff.mp hw)).2.1.1.1,
          (hruns w (Array.mem_toList_iff.mp hw)).2.1.1.2⟩⟩
    · simp at hd'
  have hb1 : SameBits d1.st out.d.st := by
    rw [ho]
    exact withRow_bits _ _ _
  have hhas : ∀ o part, out.d.st.has o part = d1.st.has o part := by
    rw [ho]
    intro o part
    rfl
  refine ⟨row, d1, G0, ho, hG0, rowFits_bits _ _ hb1 row ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro t ht
    rw [p1] at ht
    simp at ht
  · intro w hw
    rw [p3 w hw]
    exact Nat.one_pos
  · intro fm hfm v hv
    have hfit := (htests.1 fm hfm).2.1
    simp only [Form.fits, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hfit
    rw [(hfit.1 v hv).1]
    exact Nat.le_add_right _ _
  · intro Lg t ht
    rw [p1] at ht
    simp at ht
  · intro o hno e
    constructor
    · rw [c1]
      apply List.sum_eq_zero
      intro z hz
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hz
      unfold termAt
      cases ha : reqArray L.check.rows.layout t.born t.array with
      | none => rfl
      | some a =>
        dsimp only
        cases hw : L.check.frame.whereIs t.born a.message with
        | none => rfl
        | some o' =>
          dsimp only
          by_cases hoo : o' = o
          · subst hoo
            obtain ⟨fm, hfm, rfl⟩ := s1 t ht a o' ha hw
            rw [(htests.1 fm hfm).1] at hno
            simp at hno
          · rw [if_neg hoo]
    · rw [c2]
      by_cases hc : maskOracle L.check.frame = some o ∧ e < q.onMasks.size
      · have hne : q.onMasks.isEmpty = false := by
          have : q.onMasks.size ≠ 0 := by omega
          simpa using this
        have hm := (htests.2 _ (s2 hne o hc.1)).1
        rw [hm] at hno
        simp at hno
      · rw [if_neg hc]
  · intro o part hno e
    rw [hhas] at hno
    cases part with
    | main =>
      rw [c1]
      apply List.sum_eq_zero
      intro z hz
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hz
      unfold termAt
      cases ha : reqArray L.check.rows.layout t.born t.array with
      | none => rfl
      | some a =>
        dsimp only
        cases hw : L.check.frame.whereIs t.born a.message with
        | none => rfl
        | some o' =>
          dsimp only
          by_cases hoo : o' = o
          · subst hoo
            obtain ⟨fm, hfm, rfl⟩ := s1 t ht a o' ha hw
            rw [(htests.1 fm hfm).2.2] at hno
            simp at hno
          · rw [if_neg hoo]
    | mask =>
      rw [c2]
      by_cases hc : maskOracle L.check.frame = some o ∧ e < q.onMasks.size
      · have hne : q.onMasks.isEmpty = false := by
          have : q.onMasks.size ≠ 0 := by omega
          simpa using this
        have hm := (htests.2 _ (s2 hne o hc.1)).2
        rw [hm] at hno
        simp at hno
      · rw [if_neg hc]

/-- **The row that the door lays.** -/
theorem door_row {X : Type} (owed laid : Option Nat) (L : LinkCtx) (F : Fork) (d : St X)
    (out : K9.Out X) (h : door owed laid L F d = .ok out) :
    ∃ (row : OnBytes.Row) (d1 : St X) (G0 : Group),
      out.d = { d1 with st := Slice.withRow d1.st L.check.group row } ∧
      d.st.groups[L.check.group]? = some G0 ∧ RowFits out.d.st row ∧
      (∀ Lg, MaskFits out.d.st Lg row) ∧
      ∀ o, G0.members.contains o = false → ∀ e,
        ρ.val (row.coefficient o .main e) = 0 ∧ ρ.val (row.coefficient o .mask e) = 0 := by
  obtain ⟨row, d1, G0, h1, h2, h3, h4, h5, _⟩ := door_row' ρ owed laid L F d out h
  exact ⟨row, d1, G0, h1, h2, h3, h4, h5⟩

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.asRow_plain
#print axioms VerifiableInference.Desc.K9L.door_row'
#print axioms VerifiableInference.Desc.K9L.door_row
