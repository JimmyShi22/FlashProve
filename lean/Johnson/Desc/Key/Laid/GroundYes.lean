-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/Laid/GroundYes.lean: three routines of the plain ground
(Johnson/Desc/First/Base/Ground.lean), their yes read back whole. Theorems; no definition. General
in the record's type.

Main names.
  `takeMaskP_eq`: takeMaskP's yes: the message is there, it has a ledger that is not shut and has an
    entry left; the record behind is the record in front but for that ledger: its next entry is the
    one behind the entry returned, and one entry less is left.
  `addRowP_eq`: addRowP's yes: the record behind is the record in front with
    `Slice.withRow` as its statement.
  `addRowP_in`: addRowP's yes gives `Means.RowIn` of the row, at the statement and the
    group in front of the adding. (The same statement as `addRowP_rowIn`,
    Johnson/Desc/Third/Law/DotIn.lean, which stands beside the last chain's laws; here it imports
    none of them.)

The ground's clauses are carried back to the program's tests, as in DotIn.lean.

Limits. Of the form "a yes gives". Nothing on soundness or on hiding.
-/
import Johnson.Desc.First.Base.Ground
import Johnson.Desc.Means.Keeps
import Johnson.Desc.Own.RowsAgree
import Johnson.Desc.Own.ShapesAgree
import OnBytes.Slice.BlkStLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes OnBytes.Slice
open Desc.Plain (DState)
open VerifiableInference.Desc.Ground (takeMaskP takeMaskL addRowP rowL ok has)

namespace VerifiableInference.Desc.Key

/-- takeMaskP's yes, whole. -/
theorem takeMaskP_eq {L : Type} (d d' : DState L) (o n : Nat) (h : takeMaskP d o = some (n, d')) :
    ∃ (x : Oracle) (l : Ledger), d.st.oracles[o]? = some x ∧ x.ledger = some l ∧
      l.closed = false ∧ 0 < l.left ∧
      d' = { d with st := { d.st with oracles := d.st.oracles.modify o fun x =>
        { x with ledger := some { l with next := n + 1, left := l.left - 1 } } } } := by
  unfold takeMaskP at h
  split at h
  · rename_i hok
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨l, hl, rfl, rfl⟩ := h
    obtain ⟨x, hx, hxl⟩ := Option.bind_eq_some_iff.1 hl
    simp only [ok, takeMaskL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hok
    obtain ⟨_, _, c3, c4⟩ := hok
    rw [hl] at c3 c4
    exact ⟨x, l, hx, hxl, by simpa [has] using c3, by simpa [has] using c4, rfl⟩
  · cases h

/-- addRowP's yes, whole. -/
theorem addRowP_eq {L : Type} (d d' : DState L) (g : Nat) (row : Row)
    (h : addRowP d g row = some d') : d' = { d with st := withRow d.st g row } := by
  unfold addRowP at h
  split at h
  · exact (Option.some.inj h).symm
  · cases h

/-- addRowP's yes: the row lies on tables that the group's members have. -/
theorem addRowP_in {L : Type} (d d' : DState L) (g : Nat) (row : Row) (G : Group)
    (h : addRowP d g row = some d') (hG : d.st.groups[g]? = some G) : Means.RowIn d.st G row := by
  unfold addRowP at h
  split at h
  · rename_i hok
    simp only [ok, rowL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hok
    obtain ⟨_, _, _, t4, t5, t6, t7, _⟩ := hok
    rw [hG] at t4 t5 t6 t7
    -- the ground may ask these clauses in the description's own text of the four tests
    try simp only [← Own.placeFits_agrees, ← Own.formFits_agrees, ← Own.tensorInOrder_agrees,
      ← Own.coeffsInside_agrees] at t4 t5 t6 t7
    have u4 : (row.terms.all fun t => t.v.ok && Blk.placeOk d.st G t.oracle t.part t.v.vars 0) =
        true := t4
    have u5 : (row.units.all fun u =>
        Blk.placeOk d.st G u.oracle u.part (d.st.tableBits u.oracle u.part) u.index) = true := t5
    have u6 : (row.runs.all fun w =>
        w.coeffs.ok && decide (0 < w.coeffs.size) && decide (1 ≤ w.step) &&
          Blk.placeOk d.st G w.oracle w.part (d.st.tableBits w.oracle w.part)
            (w.first + w.step * (w.coeffs.size - 1))) = true := t6
    have u7 : (row.forms.all fun f =>
        Blk.placeOk d.st G f.oracle .main (d.st.tableBits f.oracle .main) 0 &&
          f.c.fits (d.st.tableBits f.oracle .main)) = true := t7
    simp only [Bool.and_eq_true, Array.all_eq_true_iff_forall_mem, decide_eq_true_eq] at u4 u5 u6 u7
    exact ⟨fun t ht => (u4 t (Array.mem_toList_iff.1 ht)).2,
      fun u hu => u5 u (Array.mem_toList_iff.1 hu),
      fun w hw => ⟨(u6 w (Array.mem_toList_iff.1 hw)).1.1.2, (u6 w (Array.mem_toList_iff.1 hw)).1.2,
        (u6 w (Array.mem_toList_iff.1 hw)).2⟩,
      fun f hf => u7 f (Array.mem_toList_iff.1 hf)⟩
  · cases h

end VerifiableInference.Desc.Key
