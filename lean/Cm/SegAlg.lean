-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegAlg.lean: tools for expressing the model's conditions as families (`Fam`) of
Cb/Req/ReqSpec.lean.

Part of the arithmetisation of the model. The cells (the entries of one matrix for each segment)
must meet zero tests (identities) and table lookups (keys) at the vertices of Boolean cubes
(`SegSpec.Holds`, Cb/Req/ReqSpec.lean). A family has one value at each vertex b < 2^v of a cube: a
sum of terms, each a coefficient (`Term.coef`: a function of the instance and the vertex) times a
product of atoms. This file builds the simplest atoms, affine forms in cells, and families from
them.

On affine forms in cells (`Cb.CForm`): +, -, scalar multiple • (instances scoped to this namespace:
open Cm.Seg).

How to use it: mirror a formula of Inst/Model/ line by line (x + y ↦ +, c * x ↦ (c : E) • , a
numeral n ↦ cK n, Σ over range n ↦ cSum n); then "simp [your definitions, that folder's
definitions]" proves that the form's value is that folder's term. Example: Cm/SegPilotAff.lean.
Limits: nothing here knows a segment, a key or an identity.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req.ReqSpec
import Inst.Model.Tables

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Cm.Seg
open Cb Inst.Model Finset

/-! ## 1. Affine forms -/

section Forms
variable {E : Type} [Field E]

/-- a constant -/
def cK (c : E) : CForm E := ⟨c, []⟩
/-- the entry at one place -/
def cAt (p : Cb.Place) : CForm E := ⟨0, [(1, p)]⟩
scoped instance : Add (CForm E) := ⟨fun f g => ⟨f.c0 + g.c0, f.terms ++ g.terms⟩⟩
scoped instance : SMul E (CForm E) := ⟨fun c f => ⟨c * f.c0, f.terms.map fun t => (c * t.1, t.2)⟩⟩
scoped instance : Sub (CForm E) := ⟨fun f g => f + (-1 : E) • g⟩
/-- f 0 + .. + f (n - 1) -/
def cSum : ℕ → (ℕ → CForm E) → CForm E
  | 0, _ => cK 0
  | n + 1, f => cSum n f + f n

variable (A : ℕ → ℕ → ℕ → E)

@[simp] theorem val_cK (c : E) : (cK c).val A = c := by simp [cK, CForm.val]
@[simp] theorem val_cAt (p : Cb.Place) : (cAt p : CForm E).val A = A p.1 p.2.1 p.2.2 := by
  simp [cAt, CForm.val]
@[simp] theorem val_add (f g : CForm E) : (f + g).val A = f.val A + g.val A := by
  show (f.c0 + g.c0) + ((f.terms ++ g.terms).map fun t => t.1 * A t.2.1 t.2.2.1 t.2.2.2).sum = _
  rw [List.map_append, List.sum_append]
  unfold CForm.val
  ring
@[simp] theorem val_smul (c : E) (f : CForm E) : (c • f).val A = c * f.val A := by
  show c * f.c0 +
      ((f.terms.map fun t => (c * t.1, t.2)).map fun t => t.1 * A t.2.1 t.2.2.1 t.2.2.2).sum = _
  rw [List.map_map]
  unfold CForm.val
  rw [mul_add, ← List.sum_map_mul_left]
  congr 2
  exact List.map_congr_left fun t _ => mul_assoc _ _ _
@[simp] theorem val_sub (f g : CForm E) : (f - g).val A = f.val A - g.val A := by
  show (f + (-1 : E) • g).val A = _
  rw [val_add, val_smul]
  ring
@[simp] theorem val_ite (c : Prop) [Decidable c] (f g : CForm E) :
    (if c then f else g).val A = if c then f.val A else g.val A := by
  split_ifs <;> rfl
@[simp] theorem val_cSum (n : ℕ) (f : ℕ → CForm E) :
    (cSum n f).val A = ∑ k ∈ range n, (f k).val A := by
  induction n with
  | zero => simp [cSum]
  | succ n ih => rw [cSum, val_add, ih, sum_range_succ]

/-- the places of a form -/
def pl (f : CForm E) : List Cb.Place := f.terms.map (·.2)

theorem pl_cK (c : E) : pl (cK c) = [] := rfl
theorem pl_cAt (p : Cb.Place) : pl (cAt p : CForm E) = [p] := rfl
theorem pl_add (f g : CForm E) : pl (f + g) = pl f ++ pl g := List.map_append
theorem pl_smul (c : E) (f : CForm E) : pl (c • f) = pl f := by
  show (f.terms.map fun t => (c * t.1, t.2)).map (·.2) = f.terms.map (·.2)
  rw [List.map_map]
  rfl
theorem pl_sub (f g : CForm E) : pl (f - g) = pl f ++ pl g := by
  show pl (f + (-1 : E) • g) = _
  rw [pl_add, pl_smul]

/-- All places of a form have the property P. -/
def AllPl (P : Cb.Place → Prop) (f : CForm E) : Prop := ∀ p ∈ pl f, P p

variable {P : Cb.Place → Prop}
theorem AllPl.cK (c : E) : AllPl P (cK c) := fun _ h => absurd h List.not_mem_nil
theorem AllPl.cAt {p : Cb.Place} (h : P p) : AllPl P (cAt p : CForm E) := fun q hq => by
  rw [pl_cAt, List.mem_singleton] at hq
  exact hq ▸ h
theorem AllPl.add {f g : CForm E} (hf : AllPl P f) (hg : AllPl P g) :
    AllPl P (f + g) := fun p hp => by
  rw [pl_add, List.mem_append] at hp
  exact hp.elim (hf p) (hg p)
theorem AllPl.smul (c : E) {f : CForm E} (hf : AllPl P f) : AllPl P (c • f) := fun p hp =>
  hf p (by rwa [pl_smul] at hp)
theorem AllPl.sub {f g : CForm E} (hf : AllPl P f) (hg : AllPl P g) :
    AllPl P (f - g) := fun p hp => by
  rw [pl_sub, List.mem_append] at hp
  exact hp.elim (hf p) (hg p)
theorem AllPl.ite {c : Prop} [Decidable c] {f g : CForm E}
    (hf : c → AllPl P f) (hg : ¬ c → AllPl P g) :
    AllPl P (if c then f else g) := by
  split_ifs with h
  · exact hf h
  · exact hg h
theorem AllPl.cSum {n : ℕ} {f : ℕ → CForm E} (h : ∀ k < n, AllPl P (f k)) : AllPl P (cSum n f) := by
  induction n with
  | zero => exact AllPl.cK 0
  | succ n ih =>
    exact AllPl.add (ih fun k hk => h k (Nat.lt_succ_of_lt hk)) (h n (Nat.lt_succ_self n))

end Forms

/-! ## 2. Vertices -/

/-- b = (ℓ · 2^vx + x) · 2^10 + i ↦ (ℓ, x, i), for x < 2^vx and i < 2^10 -/
def dec3 (vx b : ℕ) : ℕ × ℕ × ℕ := (b / 2 ^ 10 / 2 ^ vx, b / 2 ^ 10 % 2 ^ vx, b % 2 ^ 10)
def enc3 (vx l x i : ℕ) : ℕ := (l * 2 ^ vx + x) * 2 ^ 10 + i

theorem dec3_enc3 {vx l x i : ℕ} (hx : x < 2 ^ vx) (hi : i < 2 ^ 10) :
    dec3 vx (enc3 vx l x i) = (l, x, i) := by
  unfold dec3 enc3
  have h1 : ((l * 2 ^ vx + x) * 2 ^ 10 + i) / 2 ^ 10 = l * 2 ^ vx + x := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos 10),
      Nat.div_eq_of_lt hi, Nat.zero_add]
  have h2 : ((l * 2 ^ vx + x) * 2 ^ 10 + i) % 2 ^ 10 = i := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
  have h3 : (l * 2 ^ vx + x) / 2 ^ vx = l := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos vx),
      Nat.div_eq_of_lt hx, Nat.zero_add]
  have h4 : (l * 2 ^ vx + x) % 2 ^ vx = x := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]
  rw [h1, h2, h3, h4]

theorem enc3_lt {vl vx l x i : ℕ} (hl : l < 2 ^ vl) (hx : x < 2 ^ vx) (hi : i < 2 ^ 10) :
    enc3 vx l x i < 2 ^ (vl + vx + 10) := by
  unfold enc3
  have h1 : l * 2 ^ vx + x < 2 ^ vl * 2 ^ vx := by nlinarith [Nat.two_pow_pos vx]
  have h2 : (l * 2 ^ vx + x) * 2 ^ 10 + i < 2 ^ vl * 2 ^ vx * 2 ^ 10 := by
    nlinarith [Nat.two_pow_pos 10]
  rwa [pow_add, pow_add]

theorem dec3_lt {vl vx b : ℕ} (hb : b < 2 ^ (vl + vx + 10)) :
    (dec3 vx b).1 < 2 ^ vl ∧ (dec3 vx b).2.1 < 2 ^ vx ∧ (dec3 vx b).2.2 < 2 ^ 10 := by
  refine ⟨?_, Nat.mod_lt _ (Nat.two_pow_pos vx), Nat.mod_lt _ (Nat.two_pow_pos 10)⟩
  show b / 2 ^ 10 / 2 ^ vx < 2 ^ vl
  rw [Nat.div_div_eq_div_mul, Nat.div_lt_iff_lt_mul (by positivity)]
  calc b < 2 ^ (vl + vx + 10) := hb
    _ = 2 ^ vl * (2 ^ 10 * 2 ^ vx) := by rw [pow_add, pow_add]; ring

/-! ## 3. Families from lists -/

section Fams
variable {X F E : Type} [Field F] [Field E] [Algebra F E]

/-- a family from a list of atoms and a list of terms -/
def fam (v : ℕ) (atoms : List (Atom X E)) (terms : List (Term X E)) : Fam X E :=
  ⟨v, atoms.length, fun j => atoms.getD j (.base (.cell fun _ => cK 0)), terms⟩

/-- A family that is affine in cells: at the vertex b the form f b. -/
def affFam (v : ℕ) (f : ℕ → CForm E) : Fam X E := fam v [.base (.cell f)] [⟨fun _ _ => 1, [0]⟩]

theorem affFam_val (v : ℕ) (f : ℕ → CForm E) (Φ : IdxFmt F) (x : X) (W : ℕ → ℕ → F)
    (A : ℕ → ℕ → ℕ → E) (b : ℕ) :
    (affFam (X := X) v f).val Φ x W A b = (f b).val A := by
  simp [affFam, fam, Fam.val, Term.val, Atom.val, Atom0.val]

theorem affFam_wf (v : ℕ) (f : ℕ → CForm E) (Φ : IdxFmt F) : (affFam (X := X) v f).WF Φ := by
  refine ⟨fun t ht j hj => ?_, fun j hj => ?_⟩
  · rw [show (affFam (X := X) v f).terms = [⟨fun _ _ => 1, [0]⟩] from rfl, List.mem_singleton] at ht
    subst ht
    rw [List.mem_singleton] at hj
    subst hj
    exact Nat.one_pos
  · have hj' : j < 1 := hj
    obtain rfl : j = 0 := by omega
    exact trivial

theorem affFam_places {v : ℕ} {f : ℕ → CForm E}
    {P : Cb.Place → Prop} (h : ∀ b < 2 ^ v, AllPl P (f b)) :
    ∀ p ∈ (affFam (X := X) v f).places, P p := by
  rintro p ⟨j, hj, hp⟩
  have hj' : j < 1 := hj
  obtain rfl : j = 0 := by omega
  obtain ⟨b, hb, t, ht, rfl⟩ := hp
  exact h b hb _ (List.mem_map_of_mem ht)

end Fams

/-! ## 4. Tables -/

/-- a table of Inst/Model/Tables.lean, in a field; it is meant for L.rows = 2^T -/
def tabOf {F : Type} [Field F] (L : Lut) (T : ℕ) : Tab F := ⟨T, fun ι => ((L.row ι : ℤ) : F)⟩

theorem mem_tabOf_iff {F : Type} [Field F] {L : Lut} {T : ℕ} (hL : L.rows = 2 ^ T) (u : F) :
    u ∈ (tabOf L T : Tab F).set ↔ ∃ ι < L.rows, u = ((L.row ι : ℤ) : F) := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hL ▸ hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hL ▸ hk, rfl⟩

end Cm.Seg
