-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/Tail/Claims.lean: the equations of the smallness test as a list of claims: linear forms with
targets in the entries of the committed symbols, the committed reads and the digits.

The relation after the test's round (`relOut`, Cb/Pv/Tail/Block.lean) has three clauses: the digits
are in their tables, the ties hold, the reads hold. Here the ties and the reads are written as forms
(`TWhole.Form`, Cb/G6/Led.lean), each with an exponent: the power of a batching element under which
it is meant to stand. The forms are functions of the explicit statement after the round: the weights
of the reads and the drawn matrix.

Main names:
  `J s`: the entries: symbols, reads, low digits, high digits. `vals`: their values.
  `formOf l tg`: the form with the coefficients listed in l. `formOf_holds`.
  `unit`, `pack_lin`: the packing of a column is linear: the coefficient of row i in row i' of
    symbols is the packing of the column that is 1 in row i and 0 elsewhere.
  `tieForm`, `readForm`, `tie_iff`, `read_iff`: a tie and a read as forms. The sign: the digits'
    side less the combination of the committed entries.
  `Exps`: the exponents, as letters. `claims`: the list of (exponent, form), for the ties and for
    the reads that `keep` marks. `cl`: the forms alone.
  `relOut_iff`: if every read that is not kept has weights 0 and values 0, the relation after the
    round says: the digits are in their tables, and every claim of the list holds.
  `layout n L`: the forms laid out by their exponents: place e of n holds the form with the exponent
    e, or the form 0 = 0. `layout_holds`: if the exponents differ from each other and are below n,
    the layout holds iff every form of the list does. `length_layout`.

Limits: the exponents are letters: nothing here says that they differ from each other. The digits
are entries beside the committed ones: at the test's own round they are a part of the witness.

Terms: lean/GLOSSARY.md.
-/
import Cb.G6.Led
import Cb.Pv.Tail.Block

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Tail
open TWhole

/-! ## A form from a list of coefficients -/

section Form
variable {E J : Type} [Field E] [Fintype J] [DecidableEq J]

/-- The form whose coefficient at j is the sum of the entries of l at j. -/
def formOf (l : List (J × E)) (tg : E) : Form E J :=
  ⟨fun j => (l.map fun z => if z.1 = j then z.2 else 0).sum, tg⟩

theorem sum_formOf (m : J → E) : ∀ l : List (J × E),
    ∑ j, (l.map fun z => if z.1 = j then z.2 else 0).sum * m j = (l.map fun z => z.2 * m z.1).sum
  | [] => by simp
  | z :: l => by
      simp only [List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib]
      rw [sum_formOf m l]
      congr 1
      simp [ite_mul, Finset.sum_ite_eq]

theorem formOf_holds (l : List (J × E)) (tg : E) (m : J → E) :
    (formOf l tg).Holds m ↔ (l.map fun z => z.2 * m z.1).sum = tg := by
  unfold Form.Holds Form.gap formOf
  rw [sum_formOf, sub_eq_zero]

end Form

variable {K : Type} [Field K] {s : Size} (Λ : Letters K s)

/-! ## The entries -/

/-- a symbol; a read at a column; a digit -/
abbrev JSym (s : Size) : Type := Σ μ : Fin s.NM, Fin (Alg.symRows (s.m μ)) × Fin (s.k μ)
abbrev JTab (s : Size) : Type := Σ μ : Fin s.NM, Fin (s.nr μ) × Fin (s.k μ)
abbrev JDig (s : Size) : Type := Σ μ : Fin s.NM, Fin s.tau × Fin (s.m μ)

/-- The entries that the claims read: symbols, reads, low digits, high digits. -/
abbrev J (s : Size) : Type := (JSym s ⊕ JTab s) ⊕ (JDig s ⊕ JDig s)

/-- The values of the entries. -/
def vals (msg : Λ.M) (Z : Dig K s) : J s → K
  | .inl (.inl ⟨μ, i', c⟩) => Λ.sym msg μ i' c
  | .inl (.inr ⟨μ, r, c⟩) => Λ.tab msg μ r c
  | .inr (.inl ⟨μ, u, i⟩) => Z.zl μ u i
  | .inr (.inr ⟨μ, u, i⟩) => Z.zh μ u i

/-! ## The packing is linear -/

/-- the column that is 1 in row i and 0 elsewhere -/
def unit {m : ℕ} (i : Fin m) : Fin m → K := fun i₂ => if i₂ = i then 1 else 0

theorem pack_lin (rad : ℤ) {m : ℕ} (a : Fin m → K) (i' : ℕ) :
    Alg.pack rad a i' = ∑ i, a i * Alg.pack rad (unit i) i' := by
  have e : a = fun i₂ => ∑ i, a i * unit (K := K) i i₂ := by
    funext i₂
    simp [unit, Finset.sum_ite_eq]
  conv_lhs => rw [e]
  rw [Alg.pack_sum]
  exact Finset.sum_congr rfl fun i _ => Alg.pack_mul_left _ _ _ _

/-! ## A tie and a read as forms -/

/-- the coefficient of row i of cells in row i' of symbols -/
def cf (s : Size) (μ : Fin s.NM) (i' : ℕ) (i : Fin (s.m μ)) : K :=
  Alg.pack (s.rad : ℤ) (unit i) i'

/-- A tie. -/
def tieForm (β : Dr s) (μ : Fin s.NM) (u : Fin s.tau) (i' : Fin (Alg.symRows (s.m μ))) :
    Form K (J s) :=
  formOf
    ((List.finRange (s.k μ)).map (fun c =>
        ((.inl (.inl ⟨μ, i', c⟩) : J s), -(((β μ u c).val : ℤ) : K))) ++
      ((List.finRange (s.m μ)).map (fun i =>
        ((.inr (.inl ⟨μ, u, i⟩) : J s), cf s μ i' i)) ++
      (List.finRange (s.m μ)).map (fun i =>
        ((.inr (.inr ⟨μ, u, i⟩) : J s), (s.lo : K) * cf s μ i' i))))
    ((s.beta : K) * ∑ i, cf s μ i' i)

/-- A read. -/
def readForm (x : Λ.X) (β : Dr s) (μ : Fin s.NM) (u : Fin s.tau) (r : Fin (s.nr μ)) :
    Form K (J s) :=
  formOf
    ((List.finRange (s.k μ)).map (fun c =>
        ((.inl (.inr ⟨μ, r, c⟩) : J s), -(((β μ u c).val : ℤ) : K))) ++
      ((List.finRange (s.m μ)).map (fun i =>
        ((.inr (.inl ⟨μ, u, i⟩) : J s), Λ.w x μ r i)) ++
      (List.finRange (s.m μ)).map (fun i =>
        ((.inr (.inr ⟨μ, u, i⟩) : J s), (s.lo : K) * Λ.w x μ r i))))
    ((s.beta : K) * ∑ i, Λ.w x μ r i)

/-- a sum over a list of all numbers below n -/
theorem sum_finRange {n : ℕ} (f : Fin n → K) : ((List.finRange n).map f).sum = ∑ i, f i :=
  (Fin.sum_univ_def f).symm

/-- three sums against a weighted sum of combinations -/
theorem three_sums {n m : ℕ} (lo beta : K) (t y : Fin n → K) (w zl zh : Fin m → K) :
    ∑ c, -t c * y c + (∑ i, w i * zl i + ∑ i, lo * w i * zh i) = beta * ∑ i, w i ↔
      ∑ c, t c * y c = ∑ i, w i * (zl i + lo * zh i - beta) := by
  have e : ∑ i, w i * (zl i + lo * zh i - beta) =
      (∑ i, w i * zl i + ∑ i, lo * w i * zh i) - beta * ∑ i, w i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ c, -t c * y c = -∑ c, t c * y c := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [e, e2]
  constructor
  · intro h
    linear_combination -h
  · intro h
    linear_combination -h

theorem tie_iff (β : Dr s) (msg : Λ.M) (Z : Dig K s) (μ : Fin s.NM) (u : Fin s.tau)
    (i' : Fin (Alg.symRows (s.m μ))) :
    (tieForm β μ u i').Holds (vals Λ msg Z) ↔
      ∑ c, (((β μ u c).val : ℤ) : K) * Λ.sym msg μ i' c =
        Alg.pack (s.rad : ℤ) (comb Z μ u) i' := by
  unfold tieForm
  rw [formOf_holds, List.map_append, List.map_append, List.sum_append, List.sum_append,
    List.map_map, List.map_map, List.map_map, sum_finRange, sum_finRange, sum_finRange, pack_lin]
  have e : ∑ i, comb Z μ u i * Alg.pack (s.rad : ℤ) (unit i) (i' : ℕ) =
      ∑ i, cf s μ i' i * (Z.zl μ u i + (s.lo : K) * Z.zh μ u i - (s.beta : K)) :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e]
  exact three_sums _ _ _ _ _ _ _

theorem read_iff (x : Λ.X) (β : Dr s) (msg : Λ.M) (Z : Dig K s) (μ : Fin s.NM) (u : Fin s.tau)
    (r : Fin (s.nr μ)) :
    (readForm Λ x β μ u r).Holds (vals Λ msg Z) ↔
      ∑ c, (((β μ u c).val : ℤ) : K) * Λ.tab msg μ r c = ∑ i, Λ.w x μ r i * comb Z μ u i := by
  unfold readForm
  rw [formOf_holds, List.map_append, List.map_append, List.sum_append, List.sum_append,
    List.map_map, List.map_map, List.map_map, sum_finRange, sum_finRange, sum_finRange]
  exact three_sums _ _ _ _ _ _ _

/-! ## The list -/

/-- The exponents under which the ties and the reads are meant to stand. -/
structure Exps (s : Size) where
  tie : ∀ μ : Fin s.NM, Fin s.tau → Fin (Alg.symRows (s.m μ)) → ℕ
  read : ∀ μ : Fin s.NM, Fin s.tau → Fin (s.nr μ) → ℕ

/-- The claims, each with its exponent: the ties, then the reads that `keep` marks; matrix by
matrix. -/
def claims (e : Exps s) (keep : ∀ μ : Fin s.NM, Fin (s.nr μ) → Bool) (x : Λ.X × Dr s) :
    List (ℕ × Form K (J s)) :=
  ((List.finRange s.NM).flatMap fun (μ : Fin s.NM) => (List.finRange s.tau).flatMap fun u =>
      (List.finRange (Alg.symRows (s.m μ))).map fun i' => (e.tie μ u i', tieForm x.2 μ u i')) ++
    (List.finRange s.NM).flatMap fun (μ : Fin s.NM) => (List.finRange s.tau).flatMap fun u =>
      ((List.finRange (s.nr μ)).filter (keep μ)).map fun r =>
        (e.read μ u r, readForm Λ x.1 x.2 μ u r)

/-- The forms alone. -/
def cl (e : Exps s) (keep : ∀ μ : Fin s.NM, Fin (s.nr μ) → Bool) (x : Λ.X × Dr s) :
    Ledger K (J s) := (claims Λ e keep x).map Prod.snd

/-- The relation after the round: the digits are in their tables, and every claim holds. -/
theorem relOut_iff (e : Exps s) (keep : ∀ μ : Fin s.NM, Fin (s.nr μ) → Bool) (x : Λ.X) (β : Dr s)
    (msg : Λ.M) (Z : Dig K s)
    (hk : ∀ μ r, keep μ r = false → (∀ i, Λ.w x μ r i = 0) ∧ ∀ c, Λ.tab msg μ r c = 0) :
    relOut Λ x β msg Z ↔
      (∀ μ u i, Cb.Rng.InTab s.lo (Z.zl μ u i) ∧ Cb.Rng.InTab s.hi (Z.zh μ u i)) ∧
        (cl Λ e keep (x, β)).Holds (vals Λ msg Z) := by
  unfold relOut
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨hT, hR⟩ f hf
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hf
    rcases List.mem_append.1 hz with hz | hz
    · obtain ⟨μ, -, hz⟩ := List.mem_flatMap.1 hz
      obtain ⟨u, -, hz⟩ := List.mem_flatMap.1 hz
      obtain ⟨i', -, rfl⟩ := List.mem_map.1 hz
      exact (tie_iff Λ β msg Z μ u i').2 (hT μ u i')
    · obtain ⟨μ, -, hz⟩ := List.mem_flatMap.1 hz
      obtain ⟨u, -, hz⟩ := List.mem_flatMap.1 hz
      obtain ⟨r, -, rfl⟩ := List.mem_map.1 hz
      exact (read_iff Λ x β msg Z μ u r).2 (hR μ u r)
  · intro h
    refine ⟨fun μ u i' => (tie_iff Λ β msg Z μ u i').1 (h _ ?_), fun μ u r => ?_⟩
    · exact List.mem_map.2 ⟨(e.tie μ u i', tieForm β μ u i'),
        List.mem_append_left _ (List.mem_flatMap.2 ⟨μ, List.mem_finRange _,
          List.mem_flatMap.2 ⟨u, List.mem_finRange _,
            List.mem_map.2 ⟨i', List.mem_finRange _, rfl⟩⟩⟩), rfl⟩
    · cases hr : keep μ r with
      | false =>
        obtain ⟨h1, h2⟩ := hk μ r hr
        simp [h1, h2]
      | true =>
        refine (read_iff Λ x β msg Z μ u r).1 (h _ ?_)
        exact List.mem_map.2 ⟨(e.read μ u r, readForm Λ x β μ u r),
          List.mem_append_right _ (List.mem_flatMap.2 ⟨μ, List.mem_finRange _,
            List.mem_flatMap.2 ⟨u, List.mem_finRange _,
              List.mem_map.2 ⟨r, List.mem_filter.2 ⟨List.mem_finRange _, hr⟩, rfl⟩⟩⟩), rfl⟩

/-! ## The forms laid out by their exponents -/

section Layout
variable {E Jx : Type} [Field E] [Fintype Jx]

/-- Place e of n holds the first form of the list with the exponent e, or the form 0 = 0. -/
def layout (n : ℕ) (L : List (ℕ × Form E Jx)) : Ledger E Jx :=
  (List.range n).map fun e => ((L.find? fun z => z.1 == e).map Prod.snd).getD ⟨fun _ => 0, 0⟩

omit [Fintype Jx] in
theorem length_layout (n : ℕ) (L : List (ℕ × Form E Jx)) : (layout n L).length = n := by
  simp [layout]

theorem layout_holds (n : ℕ) (L : List (ℕ × Form E Jx)) (m : Jx → E)
    (hinj : ∀ z ∈ L, ∀ z' ∈ L, z.1 = z'.1 → z = z') (hlt : ∀ z ∈ L, z.1 < n) :
    (layout n L).Holds m ↔ ∀ z ∈ L, z.2.Holds m := by
  constructor
  · intro h z hz
    have hf : ∃ z', L.find? (fun y => y.1 == z.1) = some z' := by
      cases hq : L.find? (fun y => y.1 == z.1) with
      | some z' => exact ⟨z', rfl⟩
      | none =>
        have := List.find?_eq_none.1 hq z hz
        simp at this
    obtain ⟨z', hz'⟩ := hf
    have h1 : z'.1 = z.1 := by simpa using List.find?_some hz'
    have h2 : z' = z := hinj z' (List.mem_of_find?_eq_some hz') z hz h1
    have h3 := h _ (List.mem_map.2 ⟨z.1, List.mem_range.2 (hlt z hz), rfl⟩)
    rw [hz', h2] at h3
    exact h3
  · intro h f hf
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 hf
    cases hq : L.find? (fun y => y.1 == e) with
    | some z' => exact h z' (List.mem_of_find?_eq_some hq)
    | none =>
      show Form.Holds (⟨fun _ => 0, 0⟩ : Form E Jx) m
      simp [Form.Holds, Form.gap]

end Layout

end Cb.Pv.Tail

#print axioms Cb.Pv.Tail.formOf_holds
#print axioms Cb.Pv.Tail.pack_lin
#print axioms Cb.Pv.Tail.tie_iff
#print axioms Cb.Pv.Tail.read_iff
#print axioms Cb.Pv.Tail.relOut_iff
#print axioms Cb.Pv.Tail.layout_holds
