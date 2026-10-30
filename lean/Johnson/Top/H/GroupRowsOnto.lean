-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/GroupRowsOnto.lean: the form that a group's arrangement carries reaches every vector
off the free rows.

For a group with kept rows (RowsK, Johnson/Top/H/GroupRowsKept.lean) and a vector V on the fold's
input code that is 0 at every kept slot of every super-row but the first: there is a form a on the
group's complex whose carried form (GShape.rho's fm) is V at every coordinate that is not in a free
row (FreeAt, Johnson/Top/H/ArrAdd.lean). Statements and proofs.
  RowsK.fm_onto   under two conditions by name:
     hS  a slot's row names that slot. RowsK.Good does not ask it, and without it the statement is
         false: where two slots hold one row, the carried form is 0 at one of them whatever a is.
     hV  each member's change of shape carries forms onto. Reshape.Laws does not say it.
  Rows.keep_names   where whole members are kept (Rows.keep), hS holds.
Limits: hV is shown of no view here. RowsK.Good is not used.

-/
import Johnson.Top.H.GroupRowsKept
import Johnson.Top.H.ArrAdd
import OnBytes.Slice.BlkProxGp

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes OnBytes.Slice Cb

namespace RowsK
variable {S : Sig GE} (R : RowsK S)

/-- The row at a number has no slot and that number. -/
theorem rowAt_spec {i : ℕ} {r : Σ a : R.G.A, Fin (R.nM a)} (h : R.rowAt i = some r) :
    R.slot r = none ∧ R.atM r = i := by
  unfold rowAt at h
  split at h
  · rename_i hex
    obtain rfl := Option.some.inj h
    exact hex.choose_spec
  · cases h

/-- Where the slot none of the super-row b holds the row r, r's coefficients are placed there. -/
theorem rep_of_ord {b : Fin (R.s.h + R.s.g) → Bool} {r : Σ a : R.G.A, Fin (R.nM a)}
    (h : R.Sh.am.src (b, none) = some r) : R.Sh.am.rep r = (b, none) := by
  obtain ⟨h1, h2⟩ := R.rowAt_spec (i := Sz.rowNo b) h
  have hd : R.Sh.dst r = Sum.inl (vtx (R.s.h + R.s.g) (R.atM r)) := by
    show (R.slot r).elim (Sum.inl (vtx (R.s.h + R.s.g) (R.atM r))) Sum.inr = _
    rw [h1]
    rfl
  simp only [GShape.am, hd]
  rw [h2, ProxRun.vtx_rowNo]
  rfl

/-- A kept row that names its slot has its coefficients in that slot of the first super-row. -/
theorem rep_of_kept (hS : ∀ q, R.slot (R.kept q) = some q) (q : R.Kp) :
    R.Sh.am.rep (R.kept q) = (fun _ => false, some q) := by
  have hd : R.Sh.dst (R.kept q) = Sum.inr q := by
    show (R.slot (R.kept q)).elim (Sum.inl (vtx (R.s.h + R.s.g) (R.atM (R.kept q)))) Sum.inr = _
    rw [hS q]
    rfl
  simp only [GShape.am, hd]
  rfl

open Classical in
/-- Where the mask row b holds the row r, r's coefficients are placed there. -/
theorem rep_of_ordZ {b : Fin R.s.h → Bool} {r : Σ a : R.G.A, Fin (R.nZ a)}
    (h : R.Sh.az.src b = some r) : R.Sh.az.rep r = b := by
  have h' : (if h : ∃ r, R.atZ r = Sz.rowNo b then some h.choose else none) = some r := h
  split at h'
  · rename_i hex
    obtain rfl := Option.some.inj h'
    show vtx R.s.h (R.atZ hex.choose) = b
    rw [hex.choose_spec, ProxRun.vtx_rowNo]
  · cases h'

/-- **The carried form reaches every vector off the free rows.** -/
theorem fm_onto (hS : ∀ q, R.slot (R.kept q) = some q)
    (hV : ∀ a, Function.Surjective (R.view a).fm) (V : R.Sh.Cin.J → GE)
    (hK : ∀ b q x, b ≠ (fun _ => false) → V (.inl (b, (some q, x))) = 0) :
    ∃ a : R.G.C.J → GE, ∀ j, ¬ ArrAdd.FreeAt R.Sh j → R.Sh.rho.fm a j = V j := by
  -- the form on the rows as sent: V at the place where a row's coefficients go
  let c : R.Sh.Cflat.J → GE := fun n => match n with
    | .inl n => V (.inl ((R.Sh.am.rep n.1).1, ((R.Sh.am.rep n.1).2, n.2)))
    | .inr n => V (.inr (R.Sh.az.rep n.1, n.2))
  -- member by member, back through the change of shape
  choose f hf using fun m => hV m fun j =>
    c ((gatE R.Sh.Rm R.Sh.Rz R.Sh.Cb.J R.Sh.Zb.J).symm ⟨m, j⟩)
  refine ⟨fun j => f j.1 j.2, fun j hj => ?_⟩
  have hflat : R.Sh.flat.fm (fun j => f j.1 j.2) = c := by
    funext n
    show (R.view (gatE R.Sh.Rm R.Sh.Rz R.Sh.Cb.J R.Sh.Zb.J n).1).fm
      (f (gatE R.Sh.Rm R.Sh.Rz R.Sh.Cb.J R.Sh.Zb.J n).1)
      (gatE R.Sh.Rm R.Sh.Rz R.Sh.Cb.J R.Sh.Zb.J n).2 = c n
    rw [hf]
    exact congrArg c ((gatE R.Sh.Rm R.Sh.Rz R.Sh.Cb.J R.Sh.Zb.J).symm_apply_apply n)
  rcases j with ⟨b, k, x⟩ | ⟨b, y⟩
  · have hj' : R.Sh.am.src (b, k) ≠ none := hj
    show R.Sh.am.place (fun n => R.Sh.flat.fm (fun j => f j.1 j.2) (.inl n)) ((b, k), x) = _
    rw [hflat]
    cases hs : R.Sh.am.src (b, k) with
    | none => exact absurd hs hj'
    | some r =>
      simp only [Arr.place, hs]
      cases k with
      | none =>
        have e := R.rep_of_ord hs
        split
        · exact congrArg (fun n : (Fin (R.Sh.h + R.Sh.g) → Bool) × Option R.Sh.Kp =>
            V (.inl (n.1, (n.2, x)))) e
        · rename_i hne
          exact absurd e hne
      | some q =>
        have hr : r = R.kept q := (Option.some.inj hs).symm
        subst hr
        have e := R.rep_of_kept hS q
        by_cases hb : b = fun _ => false
        · subst hb
          split
          · exact congrArg (fun n : (Fin (R.Sh.h + R.Sh.g) → Bool) × Option R.Sh.Kp =>
              V (.inl (n.1, (n.2, x)))) e
          · rename_i hne
            exact absurd e hne
        · split
          · rename_i he
            exact absurd (congrArg Prod.fst (e.symm.trans he)).symm hb
          · exact (hK b q x hb).symm
  · have hj' : R.Sh.az.src b ≠ none := hj
    show R.Sh.az.place (fun n => R.Sh.flat.fm (fun j => f j.1 j.2) (.inr n)) (b, y) = _
    rw [hflat]
    cases hs : R.Sh.az.src b with
    | none => exact absurd hs hj'
    | some r =>
      have e := R.rep_of_ordZ hs
      simp only [Arr.place, hs]
      split
      · exact congrArg (fun n : Fin R.Sh.h → Bool => V (.inr (n, y))) e
      · rename_i hne
        exact absurd e hne

end RowsK

namespace Rows
variable {S : Sig GE} (R : Rows S) (kp : {o // R.mem o} → Prop) [DecidablePred kp]

/-- Where whole members are kept, a slot's row names that slot. -/
theorem keep_names (q : (R.keep kp).Kp) : (R.keep kp).slot ((R.keep kp).kept q) = some q := by
  show (if h : kp q.1.1 then some (⟨⟨q.1.1, h⟩, q.2⟩ : Σ a : {a // kp a}, Fin (R.nM a.1))
    else none) = some q
  rw [dif_pos q.1.2]

end Rows

end Johnson.Top.H
