-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/Tail/Tables.lean: the smallness test's block at reads that are given by tables.

In Cb/Pv/Tail/Block.lean a read is a number r with weights on all rows of cells. The sub-proofs give
their reads by tables: a table has a matrix, a length and a first entry in the vector of reads. For
each column c and each stretch sg of `len` rows, the entry `start + c * (m / len) + sg` of that
vector is meant to be the sum of the cells of that stretch of that column under the table's weights.
Here such tables are turned into reads, and the relation before the round is said in their terms.

Main names:
  `Tab`, `TSize`, `TLetters`: a table; the public numbers with a list of tables; the letters with
    the tables' weights `phi`, the symbols and the vector of reads `u3` at plain numbers.
  `TSize.size`, `TLetters.letters`: the size and the letters of Cb/Pv/Tail/Block.lean. Read number
    n * (m + 1) + sg of a matrix with m rows is segment sg of table number n; a number that stands
    for no segment of a table on this matrix is a read with weights 0 and value 0.
  `reads_of_relIn`: before the round there is one integer matrix for each committed matrix, small,
    with the committed packing, such that for every table, column and segment the entry of the
    vector of reads is the sum over j below `len` of `phi n j` times cell `sg * len + j` of that
    column.
  `knowAt_tables`: the block's soundness property at these letters.

Limits: nothing here says that the tables are those of a sub-proof, that they tile the vector of
reads, or that the weights were fixed before the matrix is drawn: the weights come from the explicit
statement, which stands before the round.

Terms: lean/GLOSSARY.md.
-/
import Cb.Pv.Tail.Cells
import Cb.Pv.Tail.Know

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Tail
open Iop

/-- A table of reads. -/
structure Tab where
  mat : ℕ
  len : ℕ
  start : ℕ

/-- The public numbers, with a list of tables. -/
structure TSize where
  NM : ℕ
  m : ℕ → ℕ
  k : ℕ → ℕ
  tau : ℕ
  rad : ℕ
  lo : ℕ
  hi : ℕ
  beta : ℕ
  tabs : List Tab

namespace TSize

/-- The size of Cb/Pv/Tail/Size.lean. -/
def size (t : TSize) : Size :=
  ⟨t.NM, t.m, t.k, fun μ => t.tabs.length * (t.m μ + 1), t.tau, t.rad, t.lo, t.hi, t.beta⟩

/-- The table and the segment for which read number r of matrix μ stands, if any. -/
def dec (t : TSize) (μ r : ℕ) : Option (ℕ × Tab × ℕ) :=
  match t.tabs[r / (t.m μ + 1)]? with
  | some T =>
    if T.mat = μ ∧ r % (t.m μ + 1) < t.m μ / T.len then
      some (r / (t.m μ + 1), T, r % (t.m μ + 1))
    else none
  | none => none

/-- the number of the read that stands for segment sg of table number n -/
def enc (t : TSize) (μ n sg : ℕ) : ℕ := n * (t.m μ + 1) + sg

theorem dec_enc (t : TSize) {μ n sg : ℕ} {T : Tab} (hT : t.tabs[n]? = some T) (hm : T.mat = μ)
    (hs : sg < t.m μ / T.len) : t.dec μ (t.enc μ n sg) = some (n, T, sg) := by
  have h1 : sg < t.m μ + 1 := lt_of_lt_of_le hs (le_trans (Nat.div_le_self _ _) (Nat.le_succ _))
  have hd : (n * (t.m μ + 1) + sg) / (t.m μ + 1) = n := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.succ_pos _), Nat.div_eq_of_lt h1, Nat.zero_add]
  have hr : (n * (t.m μ + 1) + sg) % (t.m μ + 1) = sg := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h1]
  unfold dec enc
  rw [hd, hr, hT]
  exact if_pos ⟨hm, hs⟩

theorem enc_lt (t : TSize) {μ n sg : ℕ} {T : Tab} (hT : t.tabs[n]? = some T)
    (hs : sg < t.m μ / T.len) : t.enc μ n sg < t.tabs.length * (t.m μ + 1) := by
  have h1 : sg < t.m μ + 1 := lt_of_lt_of_le hs (le_trans (Nat.div_le_self _ _) (Nat.le_succ _))
  have hn : n < t.tabs.length := (List.getElem?_eq_some_iff.1 hT).1
  unfold enc
  calc n * (t.m μ + 1) + sg < n * (t.m μ + 1) + (t.m μ + 1) := Nat.add_lt_add_left h1 _
    _ = (n + 1) * (t.m μ + 1) := (Nat.succ_mul _ _).symm
    _ ≤ t.tabs.length * (t.m μ + 1) := Nat.mul_le_mul_right _ hn

end TSize

/-- The letters, at plain numbers. -/
structure TLetters (K : Type) (t : TSize) where
  X : Type
  M : Type
  E : ExtSpec
  W : Type
  /-- the weights of table number n -/
  phi : X → ℕ → ℕ → K
  /-- the committed symbols: matrix, row of symbols, column -/
  sym : M → ℕ → ℕ → ℕ → K
  /-- the committed vector of reads -/
  u3 : M → ℕ → K
  dig : W → Dig K t.size
  ride : X × E.Str → M → W → Prop

variable {K : Type} [CommRing K] {t : TSize} (Θ : TLetters K t)

/-- the weight of read number r of matrix μ on row i -/
def wOf (t : TSize) (phi : ℕ → ℕ → K) (μ r i : ℕ) : K :=
  match t.dec μ r with
  | some z => if z.2.2 * z.2.1.len ≤ i ∧ i < z.2.2 * z.2.1.len + z.2.1.len then
      phi z.1 (i - z.2.2 * z.2.1.len) else 0
  | none => 0

/-- the value of read number r of matrix μ at column c -/
def tabOf (t : TSize) (u3 : ℕ → K) (μ r c : ℕ) : K :=
  match t.dec μ r with
  | some z => u3 (z.2.1.start + c * (t.m μ / z.2.1.len) + z.2.2)
  | none => 0

/-- The letters of Cb/Pv/Tail/Block.lean. -/
def TLetters.letters : Letters K t.size where
  X := Θ.X
  M := Θ.M
  E := Θ.E
  W := Θ.W
  w := fun x μ r i => wOf t (Θ.phi x) μ r i
  sym := fun msg μ i' c => Θ.sym msg μ i' c
  tab := fun msg μ r c => tabOf t (Θ.u3 msg) μ r c
  dig := Θ.dig
  ride := Θ.ride

/-- A sum over all rows under weights that live on one stretch. -/
theorem sum_stretch (m a len : ℕ) (h : a + len ≤ m) (p : ℕ → K) (v : ℕ → K) :
    ∑ i : Fin m, (if a ≤ (i : ℕ) ∧ (i : ℕ) < a + len then p ((i : ℕ) - a) else 0) * v i =
      ∑ j ∈ Finset.range len, p j * v (a + j) := by
  rw [Fin.sum_univ_eq_sum_range
    (fun i => (if a ≤ i ∧ i < a + len then p (i - a) else 0) * v i) m]
  have e : ∀ i ∈ Finset.range m, (if a ≤ i ∧ i < a + len then p (i - a) else 0) * v i =
      if a ≤ i ∧ i < a + len then p (i - a) * v i else 0 := by
    intro i _
    split_ifs <;> simp
  rw [Finset.sum_congr rfl e, ← Finset.sum_filter]
  have hf : (Finset.range m).filter (fun i => a ≤ i ∧ i < a + len) = Finset.Ico a (a + len) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · exact fun z => z.2
    · exact fun z => ⟨lt_of_lt_of_le z.2 h, z⟩
  rw [hf, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  exact Finset.sum_congr rfl fun j _ => by rw [Nat.add_sub_cancel_left]

/-- Before the round, in the tables' terms. -/
theorem reads_of_relIn {x : Θ.X} {msg : Θ.M} (h : relIn Θ.letters x msg) :
    ∃ a : ℕ → ℕ → ℕ → ℤ,
      (∀ μ, μ < t.NM → ∀ c, c < t.k μ → ∀ i, i < t.m μ → |a μ c i| < 2 * (t.beta : ℤ)) ∧
      (∀ μ, μ < t.NM → ∀ c, c < t.k μ → ∀ i', i' < Alg.symRows (t.m μ) →
        Θ.sym msg μ i' c =
          ((Alg.pack (t.rad : ℤ) (fun i : Fin (t.m μ) => a μ c i) i' : ℤ) : K)) ∧
      (∀ n T, t.tabs[n]? = some T → T.mat < t.NM → ∀ c, c < t.k T.mat →
        ∀ sg, sg < t.m T.mat / T.len →
          Θ.u3 msg (T.start + c * (t.m T.mat / T.len) + sg) =
            ∑ j ∈ Finset.range T.len, Θ.phi x n j * ((a T.mat c (sg * T.len + j) : ℤ) : K)) := by
  obtain ⟨b, h1, h2, h3⟩ := cells_of_relIn Θ.letters h
  let a : ℕ → ℕ → ℕ → ℤ := fun μ c i =>
    if hμ : μ < t.NM then
      if hc : c < t.k μ then
        if hi : i < t.m μ then b ⟨μ, hμ⟩ ⟨c, hc⟩ ⟨i, hi⟩ else 0
      else 0
    else 0
  have ha : ∀ (μ : ℕ) (hμ : μ < t.NM) (c : ℕ) (hc : c < t.k μ) (i : Fin (t.m μ)),
      a μ c i = b ⟨μ, hμ⟩ ⟨c, hc⟩ i := by
    intro μ hμ c hc i
    show (if hμ : μ < t.NM then
      if hc : c < t.k μ then
        if hi : (i : ℕ) < t.m μ then b ⟨μ, hμ⟩ ⟨c, hc⟩ ⟨i, hi⟩ else 0
      else 0
    else 0) = _
    rw [dif_pos hμ, dif_pos hc, dif_pos i.2]
    rfl
  refine ⟨a, fun μ hμ c hc i hi => ?_, fun μ hμ c hc i' hi' => ?_,
    fun n T hT hμ c hc sg hs => ?_⟩
  · have e : a μ c i = b ⟨μ, hμ⟩ ⟨c, hc⟩ ⟨i, hi⟩ := ha μ hμ c hc ⟨i, hi⟩
    rw [e]
    exact h1 _ _ _
  · have e : (fun i : Fin (t.m μ) => a μ c i) = b ⟨μ, hμ⟩ ⟨c, hc⟩ := funext (ha μ hμ c hc)
    rw [e]
    exact h2 ⟨μ, hμ⟩ ⟨c, hc⟩ ⟨i', hi'⟩
  · have hd := t.dec_enc hT rfl hs
    have hlen : sg * T.len + T.len ≤ t.m T.mat := by
      have h0 : 0 < T.len := by
        rcases Nat.eq_zero_or_pos T.len with h | h
        · rw [h, Nat.div_zero] at hs
          exact absurd hs (Nat.not_lt_zero _)
        · exact h
      have h5 := (Nat.le_div_iff_mul_le h0).1 (Nat.succ_le_of_lt hs)
      rw [Nat.succ_mul] at h5
      exact h5
    have h3' := h3 ⟨T.mat, hμ⟩ ⟨c, hc⟩ ⟨t.enc T.mat n sg, t.enc_lt hT hs⟩
    have eT : tabOf t (Θ.u3 msg) T.mat (t.enc T.mat n sg) c =
        Θ.u3 msg (T.start + c * (t.m T.mat / T.len) + sg) := by
      unfold tabOf
      rw [hd]
    have eW : ∀ i : ℕ, wOf t (Θ.phi x) T.mat (t.enc T.mat n sg) i =
        if sg * T.len ≤ i ∧ i < sg * T.len + T.len then Θ.phi x n (i - sg * T.len) else 0 := by
      intro i
      unfold wOf
      rw [hd]
    rw [← eT]
    refine h3'.trans ?_
    rw [← sum_stretch (t.m T.mat) (sg * T.len) T.len hlen (Θ.phi x n)
      (fun i => ((a T.mat c i : ℤ) : K))]
    exact Finset.sum_congr rfl fun i _ => by
      show wOf t (Θ.phi x) T.mat (t.enc T.mat n sg) i * _ = _
      rw [eW, ha T.mat hμ c hc i]

/-- The block's soundness property at these letters. -/
theorem knowAt_tables (hs : t.size.OK) :
    TWhole.KnowAt (R Θ.letters) (A Θ.letters) (B Θ.letters) (fun _ _ _ wp => wp)
      (eps Θ.letters) :=
  knowAt Θ.letters hs

end Cb.Pv.Tail

#print axioms Cb.Pv.Tail.reads_of_relIn
#print axioms Cb.Pv.Tail.knowAt_tables
