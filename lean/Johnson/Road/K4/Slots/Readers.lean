-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Slots/Readers.lean: THE READERS OF THE TABLES NAME NO SLOT: a form that one of the
environment's readers returns (`U3at`, `limbs`, `shortA`, `shA`, `longA`, `xbA`, `rowCells`,
`rowR`), or that is summed of such (`sumForms`, the folds of the planes), is `SlotsIn S` at every S.
Statements and proofs: those of Johnson/Road/K4/Reads/TermsEnts.lean, RowsEnts.lean and
GatedEnts.lean on entries, carried over to slots by a program (`inTab_x`, `entsIn_longA`,
`entsIn_xbA`, `planesAt_in` are here `sl_x`, `sl_longA`, `sl_xbA`, `sl_planesAt`); the one atom,
`sl_U3at`, is new: `U3at` returns one entry.

Limits. Nothing on which entries are named: that is the Reads files' matter. Nothing on soundness.

-/
import Johnson.Road.K4.Slots.SlotsIn
import Johnson.Road.K4.Reads.RowsEnts
import Johnson.Road.K4.Reads.GatedEnts

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Desc.First.K4.Slots

open OnBytes OnBytes.Model OnBytes.Model.Layer
open OnBytes.Road OnBytes.Road.Rows
open OnBytes.Desc.First.K4.Reads (all_mapM)

variable {v : Env} {S : ℕ → Prop}

theorem sl_aff0 : SlotsIn S aff0 := slotsIn_ofConst _

theorem sl_U3at {t i : ℕ} {f : Aff} (h : v.U3at t i = some f) : SlotsIn S f := by
  unfold Env.U3at at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · cases h
      exact slotsIn_ent _ _ _
    · cases h

/-- A sum made by a fold that may refuse. -/
theorem sl_foldlM {g : ℕ → Option (Aff × E)} (hg : ∀ x p, g x = some p → SlotsIn S p.1) :
    ∀ (l : List ℕ) (a s : Aff), SlotsIn S a →
      l.foldlM (fun a x => (g x).map fun t => a.addMul t.1 t.2) a = some s → SlotsIn S s
  | [], a, s, ha, h => by
    cases h
    exact ha
  | x :: l, a, s, ha, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨b, hb, h⟩ := bind_some h
    obtain ⟨p, hp, e⟩ := map_some hb
    subst e
    exact sl_foldlM hg l _ s (slotsIn_addMul _ ha (hg x p hp)) h

theorem sl_sumForms {n : ℕ} {g : ℕ → Option (Aff × E)} {s : Aff}
    (hg : ∀ x p, g x = some p → SlotsIn S p.1) (h : sumForms n g = some s) : SlotsIn S s :=
  sl_foldlM hg _ _ s sl_aff0 h

theorem sl_limbs {t nl : ℕ} {cell : ℕ → ℕ} {s : Aff} (h : v.limbs t nl cell = some s) :
    SlotsIn S s :=
  sl_sumForms (fun _ p hp => by
    obtain ⟨a, ha, e⟩ := map_some hp
    subst e
    exact sl_U3at ha) h

theorem sl_shortA {t : ℕ} {X : Ten} {i j : ℕ} {s : Aff} (h : v.shortA t X i j = some s) :
    SlotsIn S s := sl_limbs h

theorem sl_shA {X P : String} {i j : ℕ} {s : Aff} (h : v.shA X P i j = some s) : SlotsIn S s := by
  obtain ⟨x, -, h⟩ := bind_some h
  exact sl_shortA h


theorem sl_rowCells {P : String} {i n : ℕ} {cells : Array Aff}
    (h : v.rowCells P i n = some cells) (j : ℕ) : SlotsIn S (cells.getD j aff0) := by
  unfold Env.rowCells at h
  obtain ⟨t, -, h⟩ := bind_some h
  obtain ⟨tr, -, h⟩ := bind_some h
  rw [Array.mapM_eq_mapM_toList] at h
  obtain ⟨ys, hys, e⟩ := map_some h
  subst e
  by_cases hj : j < ys.length
  · have e : ys.toArray.getD j aff0 = ys[j] := by simp [Array.getD, hj]
    rw [e]
    exact all_mapM (Pr := SlotsIn S) (fun _ _ hb => sl_U3at hb) _ ys hys _ (List.getElem_mem hj)
  · have e : ys.toArray.getD j aff0 = aff0 := by simp [Array.getD, hj]
    rw [e]
    exact sl_aff0

/-- The number that digits spell, in the row of five limbs. -/
theorem sl_ledDig {Dg : Array Aff} (hD : ∀ j, SlotsIn S (Dg.getD j (LedK.c zeroE)))
    (first n : ℕ) : SlotsIn S (ledDig Dg first n) :=
  slotsIn_foldl _ (fun _ _ hf => slotsIn_add hf (slotsIn_scale _ (hD _))) _ _ (slotsIn_ofConst _)

/-- The same in the row of four limbs. -/
theorem sl_digits {Dg : Array Aff} (hD : ∀ j, SlotsIn S (Dg.getD j aff0)) (a n : ℕ) :
    SlotsIn S (Env.digits Dg a n) :=
  slotsIn_foldl _ (fun _ _ hf => slotsIn_addMul _ hf (hD _)) _ _ sl_aff0

theorem sl_rowR {P : String} {i : ℕ} {f : Aff} (h : v.rowR P i = some f) : SlotsIn S f := by
  unfold Env.rowR at h
  split at h
  · obtain ⟨r, hr, e⟩ := map_some h
    subst e
    unfold Env.row5At at hr
    obtain ⟨cells, hc, hr⟩ := bind_some hr
    obtain rfl : row5 (fun j => cells.getD j aff0) = r := Option.some.inj hr
    have hD : ∀ j, SlotsIn S ((Array.ofFn (n := 99) fun j : Fin 99 =>
        (LedK.add (cells.getD j.val aff0) (LedK.c (ofNat 128)) : Aff)).getD j (LedK.c zeroE)) := by
      intro j
      by_cases hj : j < 99
      · have e : (Array.ofFn (n := 99) fun j : Fin 99 =>
            (LedK.add (cells.getD j.val aff0) (LedK.c (ofNat 128)) : Aff)).getD j (LedK.c zeroE) =
            LedK.add (cells.getD j aff0) (LedK.c (ofNat 128)) := by
          simp [Array.getD, hj]
        rw [e]
        exact slotsIn_add (sl_rowCells hc j) (slotsIn_ofConst _)
      · have e : (Array.ofFn (n := 99) fun j : Fin 99 =>
            (LedK.add (cells.getD j.val aff0) (LedK.c (ofNat 128)) : Aff)).getD j (LedK.c zeroE) =
            LedK.c zeroE := by
          simp [Array.getD, hj]
        rw [e]
        exact slotsIn_ofConst _
    exact slotsIn_add (sl_ledDig hD 80 3) (slotsIn_scale _ (sl_ledDig hD 83 3))
  · obtain ⟨r, hr, e⟩ := map_some h
    subst e
    unfold Env.rowAt at hr
    obtain ⟨cells, hc, hr⟩ := bind_some hr
    have hr' := Option.some.inj hr
    subst hr'
    have hD : ∀ j, SlotsIn S ((cells.map fun a => a + Aff.ofConst (ofNat 128)).getD j aff0) := by
      intro j
      by_cases hj : j < cells.size
      · have e : (cells.map fun a => a + Aff.ofConst (ofNat 128)).getD j aff0 =
            cells.getD j aff0 + Aff.ofConst (ofNat 128) := by
          simp [Array.getD, hj]
        rw [e]
        exact slotsIn_add (sl_rowCells hc j) (slotsIn_ofConst _)
      · have e : (cells.map fun a => a + Aff.ofConst (ofNat 128)).getD j aff0 = aff0 := by
          simp [Array.getD, hj]
        rw [e]
        exact sl_aff0
    exact slotsIn_add (sl_digits hD 57 3) (slotsIn_scale _ (sl_digits hD 60 3))


theorem sl_longA {t : ℕ} {X : Ten} {i jh : ℕ} {a : Aff} (h : v.longA t X i jh = some a) :
    SlotsIn S a := sl_limbs h

theorem sl_xbA {t kh : ℕ} {a : Aff} (h : v.xbA t kh = some a) : SlotsIn S a := sl_limbs h

/-- A sum made by a fold that may refuse, each member under a weight. -/
theorem sl_foldlM_addMul {g : ℕ → Option Aff} {w : ℕ → E}
    (hg : ∀ x a, g x = some a → SlotsIn S a) : ∀ (l : List ℕ) (a s : Aff), SlotsIn S a →
      l.foldlM (fun (f : Aff) c => (g c).map fun x => Aff.addMul f x (w c)) a = some s → SlotsIn S s
  | [], a, s, ha, h => by
    cases h
    exact ha
  | x :: l, a, s, ha, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨b, hb, h⟩ := bind_some h
    obtain ⟨p, hp, e⟩ := map_some hb
    subst e
    exact sl_foldlM_addMul hg l _ s (slotsIn_addMul _ ha (hg x p hp)) h

/-- The same for a plain sum. -/
theorem sl_foldlM_add {g : ℕ → Option Aff} (hg : ∀ x a, g x = some a → SlotsIn S a) :
    ∀ (l : List ℕ) (a s : Aff), SlotsIn S a →
      l.foldlM (fun (f : Aff) c => (g c).map fun x => f + x) a = some s → SlotsIn S s
  | [], a, s, ha, h => by
    cases h
    exact ha
  | x :: l, a, s, ha, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨b, hb, h⟩ := bind_some h
    obtain ⟨p, hp, e⟩ := map_some hb
    subst e
    exact sl_foldlM_add hg l _ s (slotsIn_add ha (hg x p hp)) h

theorem sl_planesAt {g : Forest.Heard} {lm e : ℕ} {bit : ℕ → ℕ → Option Aff} {s : Aff}
    (hb : ∀ e x a, bit e x = some a → SlotsIn S a) (h : planesAt g lm e bit = some s) :
    SlotsIn S s := by
  unfold planesAt at h
  exact sl_foldlM_addMul (fun x a ha => hb e x a ha) _ _ s (slotsIn_ofConst _) h


end OnBytes.Desc.First.K4.Slots

#print axioms OnBytes.Desc.First.K4.Slots.sl_rowR
#print axioms OnBytes.Desc.First.K4.Slots.sl_planesAt
