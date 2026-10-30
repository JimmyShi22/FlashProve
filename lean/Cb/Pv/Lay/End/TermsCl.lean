-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/TermsCl.lean: the verifier's claims on the end values of the sumcheck of the terms of
a group of layers, as forms on committed entries, and what they say on cells.

The sumcheck of the terms (the second sumcheck over the token positions of a layers' sub-proof)
shows, at its end point, the reciprocal of every norm and, for every layer with routed experts, the
score and the entries of the selector. What is sent is the hidden value plus the challenge of the
further variable times a mask entry. The verifier claims that each hidden value equals a form in the
tables of reads at the end point. This file writes these claims as forms (Blocks/Form.lean) on
entries of two kinds: entries of the mask row, and entries of the tables of reads, which are sent
late. The forms are functions of what the verifier has heard and drawn (the record TermsE) and of
names for the entries (the record TermsNames). No state of a program occurs.

Definitions.
 - TermsE: the end point rt, the factor β of the end values' masks, and what was shown.
 - TermsNames J: the entries' names in a type J.
 - hT: a hidden end value as a form: what was shown less β times the mask entry.
 - valF: the read-out formula of an array (Inst.Model.FFSeg.val) on the reads of its cells.
 - cRec, cSc, cSel: the claims. termsCl: their list, in the order reciprocals, scores, selectors.
 - TermsTrue: what the entries of the tables of reads are meant to be, on cells t.
 - TermsLast: what the claims say on cells: each hidden end value is the contraction R2, sc2 or sel2
   of the record rdTrue (Inst/Model/FF/Objects.lean) at the end point.

Main theorem: terms_last: on entries y with true tables, if every form of termsCl is worth 0, then
TermsLast.

Limits. The claim that the sumcheck's rounds leave is not in the list: the verifier does not add it.
It divides it by the coefficient that it drew and lays the result into the claimed sum of the next
sumcheck. That the list is a program's is not said here. Identities alone: nothing on a distribution
of a challenge and nothing on soundness.


-/
import Inst.Model.Common.LedgerForms
import Inst.Model.FF.Objects

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End

open Finset
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell Arr led val valU rdTrue)
open Inst.Model.Ledger (RF)
open Blocks (ext Form)

/-- What the claims on the end values read of what the verifier has heard and drawn. -/
structure TermsE (E : Type) where
  /-- the end point of the sumcheck of the terms -/
  rt : ℕ → E
  /-- the challenge of the further variable -/
  β : E
  /-- what was shown, by the number of the end value -/
  sh : ℕ → E

/-- The names of the entries that the claims on the end values read. -/
structure TermsNames (J : Type) where
  /-- the mask entry of an end value, by its number -/
  mT : ℕ → J
  /-- the reads at the end point: cell n of the ledger of norm ν; cell k of the score of routed
  layer l; cell k of entry x of the selector of routed layer l -/
  uRow : ℕ → ℕ → J
  uSc : ℕ → ℕ → J
  uSel : ℕ → ℕ → ℕ → J

section Forms

variable {E J : Type} [Field E] [DecidableEq J] (N : TermsNames J) (e : TermsE E)

/-- Hidden end value number x. -/
def hT (x : ℕ) : Form J E := Form.const (e.sh x) - e.β • Form.ent (N.mT x)

/-- The read-out formula of the array X on the reads u of its cells. -/
def valF (X : Arr) (u : ℕ → J) : Form J E :=
  ∑ k ∈ range X.nCell, (256 ^ k : E) • Form.ent (u k) + Form.const ((X.off : ℤ) : E)

/-- The reciprocal of norm ν against the reads of the ledger. A byte of the ledger is the read-out
of one cell. -/
def cRec (ν : ℕ) : Form J E := hT N e ν - RF fun n => valF .D fun _ => N.uRow ν n

/-- The score of routed layer l. n: the number of norms. -/
def cSc (n l : ℕ) : Form J E := hT N e (n + l) - valF .sc (N.uSc l)

/-- Entry x of the selector of routed layer l. ne: the routed layers; nx: the experts. -/
def cSel (n ne nx l x : ℕ) : Form J E := hT N e (n + ne + l * nx + x) - valF .sel (N.uSel l x)

/-- The claims on the end values. -/
def termsCl (D : Dim) : List (Form J E) :=
  (List.range D.nNu).map (cRec N e) ++ (List.range D.ne).map (cSc N e D.nNu) ++
    (List.range (D.ne * D.nx)).map fun i => cSel N e D.nNu D.ne D.nx (i / D.nx) (i % D.nx)

end Forms

section Means

variable {E J : Type} [Field E] [Fintype J] [DecidableEq J] (N : TermsNames J) (e : TermsE E)

/-- What the entries of the tables of reads are meant to be, on the cells t. -/
structure TermsTrue (D : Dim) (t : Cell → E) (y : J → E) : Prop where
  row : ∀ ν n, ν < D.nNu → n < 99 → y (N.uRow ν n) = ext D.lT (fun i => t ⟨.D, 0, ν, n, i⟩) e.rt
  sc : ∀ l k, l < D.ne → k < 3 → y (N.uSc l k) = ext D.lT (fun i => t ⟨.sc, k, l, 0, i⟩) e.rt
  sel : ∀ l x k, l < D.ne → x < D.nx → k < 1 →
    y (N.uSel l x k) = ext D.lT (fun i => t ⟨.sel, k, l, x, i⟩) e.rt

/-- What the claims on the end values say on cells. z, H1, H2: letters of rdTrue that the three
contractions do not read. -/
structure TermsLast [Scl] (D : Dim) (t : Cell → E) (z : ℕ → E) (H1 H2 : ℕ → ℕ → E) (y : J → E) :
    Prop where
  recip : ∀ ν, ν < D.nNu → e.sh ν - e.β * y (N.mT ν) = (rdTrue D t z e.rt H1 H2).R2 ν
  sc : ∀ l, l < D.ne →
    e.sh (D.nNu + l) - e.β * y (N.mT (D.nNu + l)) = (rdTrue D t z e.rt H1 H2).sc2 l
  sel : ∀ l x, l < D.ne → x < D.nx →
    e.sh (D.nNu + D.ne + l * D.nx + x) - e.β * y (N.mT (D.nNu + D.ne + l * D.nx + x)) =
      (rdTrue D t z e.rt H1 H2).sel2 l x

theorem val_hT (y : J → E) (x : ℕ) : Form.val y (hT N e x) = e.sh x - e.β * y (N.mT x) := by
  unfold hT
  rw [map_sub, map_smul, Form.val_const, Form.val_ent, smul_eq_mul]

omit [Fintype J] in
/-- The extension of an array's value is the read-out formula on the extensions of its cells. -/
theorem ext_val (g : ℕ) (t : Cell → E) (X : Arr) (inst j : ℕ) (u : ℕ → E) :
    ext g (fun i => val t X inst j i) u =
      ∑ k ∈ range X.nCell, 256 ^ k * ext g (fun i => t ⟨X, k, inst, j, i⟩) u +
        ((X.off : ℤ) : E) := by
  unfold Inst.Model.FFSeg.val
  rw [Blocks.ext_add, Blocks.ext_const, Blocks.ext_sum]
  congr 1
  exact sum_congr rfl fun k _ => Blocks.ext_smul g _ _ u

/-- The form valF on reads that are the extensions of the array's cells. -/
theorem val_valF (g : ℕ) (t : Cell → E) (X : Arr) (inst j : ℕ) (pt : ℕ → E) (y : J → E)
    (u : ℕ → J) (h : ∀ k, k < X.nCell → y (u k) = ext g (fun i => t ⟨X, k, inst, j, i⟩) pt) :
    Form.val y (valF (E := E) X u) = ext g (fun i => val t X inst j i) pt := by
  unfold valF
  rw [map_add, map_sum, Form.val_const, ext_val]
  congr 1
  exact sum_congr rfl fun k hk => by
    rw [map_smul, Form.val_ent, smul_eq_mul, h k (mem_range.mp hk)]

omit [Fintype J] [DecidableEq J] in
/-- The reciprocal reads the bytes below 99 alone. -/
theorem R_congr {A B : ℕ → E} (h : ∀ n, n < 99 → A n = B n) :
    Inst.Model.Ledger.R A = Inst.Model.Ledger.R B := by
  have e1 : Inst.Model.Ledger.b256 A 80 3 = Inst.Model.Ledger.b256 B 80 3 :=
    sum_congr rfl fun l hl => by rw [h (80 + l) (by have := mem_range.mp hl; omega)]
  have e2 : Inst.Model.Ledger.b256 A 83 3 = Inst.Model.Ledger.b256 B 83 3 :=
    sum_congr rfl fun l hl => by rw [h (83 + l) (by have := mem_range.mp hl; omega)]
  unfold Inst.Model.Ledger.R Inst.Model.Ledger.Rlo Inst.Model.Ledger.Rhi
  rw [e1, e2]

/-- On entries with true tables, the claims say TermsLast. -/
theorem terms_last [Scl] (D : Dim) (t : Cell → E) (z : ℕ → E) (H1 H2 : ℕ → ℕ → E) (y : J → E)
    (T : TermsTrue N e D t y) (h : ∀ f ∈ termsCl N e D, Form.val y f = 0) :
    TermsLast N e D t z H1 H2 y := by
  have m1 : ∀ ν, ν < D.nNu → Form.val y (cRec N e ν) = 0 := fun ν hν =>
    h _ (by
      simp only [termsCl, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl (Or.inl ⟨ν, hν, rfl⟩))
  have m2 : ∀ l, l < D.ne → Form.val y (cSc N e D.nNu l) = 0 := fun l hl =>
    h _ (by
      simp only [termsCl, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl (Or.inr ⟨l, hl, rfl⟩))
  have m3 : ∀ i, i < D.ne * D.nx →
      Form.val y (cSel N e D.nNu D.ne D.nx (i / D.nx) (i % D.nx)) = 0 := fun i hi =>
    h _ (by
      simp only [termsCl, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩)
  refine ⟨fun ν hν => ?_, fun l hl => ?_, fun l x hl hx => ?_⟩
  · have k := m1 ν hν
    unfold cRec at k
    rw [map_sub, val_hT] at k
    rw [sub_eq_zero.mp k, Inst.Model.Ledger.val_RF]
    have hb : ∀ n, n < 99 → Form.val y (valF (E := E) .D fun _ => N.uRow ν n) =
        ext D.lT (fun i => led t ν i n) e.rt :=
      fun n hn => val_valF D.lT t .D ν n e.rt y _ fun k' hk' => by
        have h1 : k' < 1 := hk'
        have h0 : k' = 0 := by omega
        subst h0
        exact T.row ν n hν hn
    rw [R_congr hb]
    exact (Inst.Model.Ledger.ext_R D.lT (fun m i => led t ν i m) e.rt).symm
  · have k := m2 l hl
    unfold cSc at k
    rw [map_sub, val_hT] at k
    rw [sub_eq_zero.mp k]
    exact val_valF D.lT t .sc l 0 e.rt y _ fun k hk => T.sc l k hl hk
  · have hi : l * D.nx + x < D.ne * D.nx := by
      calc l * D.nx + x < l * D.nx + D.nx := by omega
        _ = (l + 1) * D.nx := by ring
        _ ≤ D.ne * D.nx := Nat.mul_le_mul_right _ hl
    have k := m3 (l * D.nx + x) hi
    have d1 : (l * D.nx + x) / D.nx = l := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hx, Nat.zero_add]
    have d2 : (l * D.nx + x) % D.nx = x := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]
    rw [d1, d2] at k
    unfold cSel at k
    rw [map_sub, val_hT] at k
    rw [sub_eq_zero.mp k]
    exact val_valF D.lT t .sel l x e.rt y _ fun k hk => T.sel l x k hl hx hk

end Means

end Cb.Pv.Lay.End
