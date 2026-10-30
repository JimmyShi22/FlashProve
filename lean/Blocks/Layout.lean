-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/Layout.lean: the layout of the weights in the hidden matrix.

A weight tensor ("unit") W[i_1, ..., i_n] is stored in a matrix with h rows and 2^k columns. Every
coordinate i_g splits into a column part and a row part. The column parts, side by side, are the
number of the column; the byte and the row parts, as digits in a mixed radix, are the number of the
row inside the unit; the units are one below the other.
  1  `CSplit`, `Tup`, `split`, `colN`, `rowN`: the split of a coordinate as a bijection onto all
     pairs; col and row, which are injective
  2  `LUnit`, `LUnit.toTLay`: a unit gives the structure `MG.TLay` of Blocks/MergeBlock.lean, on
     which `MG.TLay.Tn_eq` writes a tensor claim as a sum over columns
  3  `Fac`, `IsSplit`, `LUnit.Tn_eq_sum`: factors that are products over the coordinates and over
     the split: the functional of a tensor claim as a sum over index tuples
  4  `MG.TLay.mle_eps`: the extension of the column weights of any layout: ∑ over the column parts
     of fᶜ[iᶜ] eq(z, col iᶜ)
  5  `Kind`, `Coord`, `toSplit`, `assign`, `bitsOf_assign_le`: the three kinds of coordinates, and
     the counter of bits

Bits. The first coordinate of a unit takes the lowest bits of a column number. A column is given
here by its bits `Fin k → Bool` with the variable 0 for the highest bit (`Alg.bits`, `Blocks.eqN`).
So the first coordinate of a unit has the last variables.

Generality. A unit may have any number of coordinates and of bytes. A coordinate is given with some
power 2^s that divides its extent (not necessarily the largest).

Limits: not here: the pairs of rows of the units with two bytes, which the definition of well-formed
matrices uses; the product formula for the extension of the column weights; the units of a layout
one below the other, and that different units have different rows.
-/
import Blocks.MergeBlock

set_option autoImplicit false

namespace Blocks
namespace Layout

open Alg

/-! ## 1. Splits of the coordinates, columns and rows -/

/-- The split of one coordinate: the data. The coordinate has the extent R and takes t bits of the
number of the column. Every i < R splits into a column part below C ≤ 2^t and a row part below l,
and all pairs occur. -/
structure CSplit where
  R : ℕ
  t : ℕ
  C : ℕ
  l : ℕ
  hC : C ≤ 2 ^ t
  e : Fin R ≃ Fin C × Fin l

/-- Index tuples, their column parts and their row parts. -/
def Tup : List CSplit → Type
  | [] => Unit
  | c :: cs => Fin c.R × Tup cs
def TupC : List CSplit → Type
  | [] => Unit
  | c :: cs => Fin c.C × TupC cs
def TupR : List CSplit → Type
  | [] => Unit
  | c :: cs => Fin c.l × TupR cs

instance instFintypeTup : ∀ cs, Fintype (Tup cs)
  | [] => inferInstanceAs (Fintype Unit)
  | c :: cs => haveI := instFintypeTup cs; inferInstanceAs (Fintype (Fin c.R × Tup cs))
instance instFintypeTupC : ∀ cs, Fintype (TupC cs)
  | [] => inferInstanceAs (Fintype Unit)
  | c :: cs => haveI := instFintypeTupC cs; inferInstanceAs (Fintype (Fin c.C × TupC cs))
instance instFintypeTupR : ∀ cs, Fintype (TupR cs)
  | [] => inferInstanceAs (Fintype Unit)
  | c :: cs => haveI := instFintypeTupR cs; inferInstanceAs (Fintype (Fin c.l × TupR cs))

/-- The split of an index tuple, coordinate by coordinate: a bijection onto all pairs of a column
part and a row part. -/
def split : (cs : List CSplit) → Tup cs ≃ TupC cs × TupR cs
  | [] => ⟨fun _ => ((), ()), fun _ => (), fun _ => rfl, fun _ => rfl⟩
  | c :: cs => (Equiv.prodCongr c.e (split cs)).trans (Equiv.prodProdProdComm _ _ _ _)

/-- The number of bits of the column number that the coordinates take, and the number of row
parts. -/
def bitsOf (cs : List CSplit) : ℕ := (cs.map fun c => c.t).sum
def rowsOf (cs : List CSplit) : ℕ := (cs.map fun c => c.l).prod

/-- col: the column parts side by side, the first coordinate in the lowest bits. -/
def colN : (cs : List CSplit) → TupC cs → ℕ
  | [], _ => 0
  | c :: cs, (u, r) => colN cs r * 2 ^ c.t + u.val

/-- row: the number with the digits b, iʳ_n, ..., iʳ_1, most significant first, in the mixed radix
(·, l_n, ..., l_1). -/
def rowN : (cs : List CSplit) → TupR cs → ℕ → ℕ
  | [], _, b => b
  | c :: cs, (u, r), b => rowN cs r b * c.l + u.val

theorem colN_lt : ∀ (cs : List CSplit) (ic : TupC cs), colN cs ic < 2 ^ bitsOf cs
  | [], _ => by simp [colN, bitsOf]
  | c :: cs, (u, r) => by
      have h1 := colN_lt cs r
      have h2 : u.val < 2 ^ c.t := lt_of_lt_of_le u.2 c.hC
      have h3 : bitsOf (c :: cs) = c.t + bitsOf cs := by simp [bitsOf]
      show colN cs r * 2 ^ c.t + u.val < _
      rw [h3, pow_add]
      calc colN cs r * 2 ^ c.t + u.val < colN cs r * 2 ^ c.t + 2 ^ c.t := by omega
        _ = (colN cs r + 1) * 2 ^ c.t := by ring
        _ ≤ 2 ^ bitsOf cs * 2 ^ c.t := Nat.mul_le_mul_right _ h1
        _ = 2 ^ c.t * 2 ^ bitsOf cs := by ring

/-- col is injective. -/
theorem colN_injective : ∀ cs : List CSplit, Function.Injective (colN cs)
  | [], _, _, _ => rfl
  | c :: cs, (u, r), (u', r'), h => by
      have h2 : u.val < 2 ^ c.t := lt_of_lt_of_le u.2 c.hC
      have h2' : u'.val < 2 ^ c.t := lt_of_lt_of_le u'.2 c.hC
      have h : colN cs r * 2 ^ c.t + u.val = colN cs r' * 2 ^ c.t + u'.val := h
      have hm : u.val = u'.val := by
        have := congrArg (· % 2 ^ c.t) h
        simpa [Nat.mul_add_mod_of_lt, Nat.add_mod, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h2']
          using this
      have hd : colN cs r = colN cs r' := by
        rw [hm] at h
        exact Nat.eq_of_mul_eq_mul_right (by positivity) (Nat.add_right_cancel h)
      rw [Fin.ext hm, colN_injective cs hd]

theorem rowN_lt :
    ∀ (cs : List CSplit) (ir : TupR cs) {b nB : ℕ}, b < nB → rowN cs ir b < nB * rowsOf cs
  | [], _, b, nB, hb => by simpa [rowN, rowsOf] using hb
  | c :: cs, (u, r), b, nB, hb => by
      have h1 := rowN_lt cs r hb
      have h3 : rowsOf (c :: cs) = c.l * rowsOf cs := by simp [rowsOf]
      show rowN cs r b * c.l + u.val < _
      rw [h3]
      calc rowN cs r b * c.l + u.val < rowN cs r b * c.l + c.l := by have := u.2; omega
        _ = (rowN cs r b + 1) * c.l := by ring
        _ ≤ (nB * rowsOf cs) * c.l := Nat.mul_le_mul_right _ h1
        _ = nB * (c.l * rowsOf cs) := by ring

/-- row is injective in the byte and the row part together. -/
theorem rowN_injective :
    ∀ (cs : List CSplit) {ir ir' : TupR cs} {b b' : ℕ},
      rowN cs ir b = rowN cs ir' b' → ir = ir' ∧ b = b'
  | [], _, _, _, _, h => ⟨rfl, h⟩
  | c :: cs, (u, r), (u', r'), b, b', h => by
      have h : rowN cs r b * c.l + u.val = rowN cs r' b' * c.l + u'.val := h
      have hl : 0 < c.l := lt_of_le_of_lt (Nat.zero_le _) u.2
      have hm : u.val = u'.val := by
        have := congrArg (· % c.l) h
        simpa [Nat.add_mod, Nat.mod_eq_of_lt u.2, Nat.mod_eq_of_lt u'.2] using this
      have hd : rowN cs r b = rowN cs r' b' := by
        rw [hm] at h
        exact Nat.eq_of_mul_eq_mul_right hl (Nat.add_right_cancel h)
      obtain ⟨h1, h2⟩ := rowN_injective cs hd
      exact ⟨by rw [Fin.ext hm, h1], h2⟩

/-- row reaches every number below nB · ∏ l (a bijection onto the rows of the unit). -/
theorem rowN_surjective :
    ∀ (cs : List CSplit) {nB y : ℕ},
      y < nB * rowsOf cs → ∃ (ir : TupR cs) (b : ℕ), b < nB ∧ rowN cs ir b = y
  | [], nB, y, h => ⟨(), y, by simpa [rowsOf] using h, rfl⟩
  | c :: cs, nB, y, h => by
      have h3 : rowsOf (c :: cs) = c.l * rowsOf cs := by simp [rowsOf]
      rw [h3] at h
      have hl : 0 < c.l := by
        rcases Nat.eq_zero_or_pos c.l with h0 | h0
        · rw [h0] at h; simp at h
        · exact h0
      have h1 : y / c.l < nB * rowsOf cs := by
        rw [Nat.div_lt_iff_lt_mul hl]
        calc y < nB * (c.l * rowsOf cs) := h
          _ = nB * rowsOf cs * c.l := by ring
      obtain ⟨ir, b, hb, hy⟩ := rowN_surjective cs h1
      refine ⟨(⟨y % c.l, Nat.mod_lt _ hl⟩, ir), b, hb, ?_⟩
      show rowN cs ir b * c.l + y % c.l = y
      rw [hy]
      exact Nat.div_add_mod' y c.l

/-! ## 2. A unit -/

/-- A unit in a matrix with h rows and 2^k columns: the data. The splits of its coordinates, the
number nB of bytes of an entry, and the number `off` of the rows of all earlier units. The bits fit
into the number of a column and the rows into the matrix. -/
structure LUnit (h k : ℕ) where
  cs : List CSplit
  nB : ℕ
  off : ℕ
  hbits : bitsOf cs ≤ k
  hrows : off + nB * rowsOf cs ≤ h

variable {h k : ℕ}

/-- The layout of the unit, as the merge of tensor claims uses it. Byte b of the entry i is in the
row off + row(b, iʳ) and the column col(iᶜ). A column is given by its bits; the variable 0 is the
highest bit. -/
def LUnit.toTLay (U : LUnit h k) : MG.TLay (Fin h) (Fin k) where
  I := Tup U.cs
  Ic := TupC U.cs
  Ir := TupR U.cs
  nB := U.nB
  split := split U.cs
  col := fun ic => bits k (colN U.cs ic)
  row := fun b ir => ⟨U.off + rowN U.cs ir b.val, by
    have h1 := rowN_lt U.cs ir b.2
    have h2 := U.hrows
    omega⟩

theorem LUnit.col_injective (U : LUnit h k) : Function.Injective U.toTLay.col := by
  intro ic ic' he
  have hlt : ∀ q : TupC U.cs, colN U.cs q < 2 ^ k := fun q =>
    lt_of_lt_of_le (colN_lt U.cs q) (Nat.pow_le_pow_right (by norm_num) U.hbits)
  have h1 : num (bits k (colN U.cs ic)) = num (bits k (colN U.cs ic')) := congrArg num he
  rw [num_bits (hlt ic), num_bits (hlt ic')] at h1
  exact colN_injective U.cs h1

theorem LUnit.row_injective (U : LUnit h k) :
    Function.Injective fun q : Fin U.toTLay.nB × U.toTLay.Ir => U.toTLay.row q.1 q.2 := by
  rintro ⟨b, ir⟩ ⟨b', ir'⟩ he
  have h1 : U.off + rowN U.cs ir b.val = U.off + rowN U.cs ir' b'.val := congrArg Fin.val he
  obtain ⟨h2, h3⟩ := rowN_injective U.cs (Nat.add_left_cancel h1)
  exact Prod.ext (Fin.ext h3) h2

/-- The rows of the unit are exactly the numbers from off up to, but not including, off + nB ∏ l. -/
theorem LUnit.mem_rows_iff (U : LUnit h k) (y : Fin h) :
    (∃ b ir, U.toTLay.row b ir = y) ↔ U.off ≤ y.val ∧ y.val < U.off + U.nB * rowsOf U.cs := by
  constructor
  · rintro ⟨b, ir, rfl⟩
    have h1 := rowN_lt U.cs ir b.2
    exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left h1 _⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨ir, b, hb, hy⟩ := rowN_surjective U.cs (nB := U.nB) (y := y.val - U.off) (by omega)
    exact ⟨⟨b, hb⟩, ir, Fin.ext (by show U.off + rowN U.cs ir b = y.val; omega)⟩

/-! ## 3. Factors that are products over the coordinates -/

variable {E : Type}

/-- A factor for each coordinate: on the coordinate itself, on its column part, on its row part. -/
def Fac (E : Type) : List CSplit → Type
  | [] => Unit
  | c :: cs => (Fin c.R → E) × Fac E cs
def FacC (E : Type) : List CSplit → Type
  | [] => Unit
  | c :: cs => (Fin c.C → E) × FacC E cs
def FacR (E : Type) : List CSplit → Type
  | [] => Unit
  | c :: cs => (Fin c.l → E) × FacR E cs

variable [Field E]

/-- ∏_g f_g[i_g], and the same for column parts and row parts. -/
def prodF : (cs : List CSplit) → Fac E cs → Tup cs → E
  | [], _, _ => 1
  | _ :: cs, (f, fs), (u, r) => f u * prodF cs fs r
def prodC : (cs : List CSplit) → FacC E cs → TupC cs → E
  | [], _, _ => 1
  | _ :: cs, (f, fs), (u, r) => f u * prodC cs fs r
def prodR : (cs : List CSplit) → FacR E cs → TupR cs → E
  | [], _, _ => 1
  | _ :: cs, (f, fs), (u, r) => f u * prodR cs fs r

/-- The factors are products over the split: f_g[i_g] = fʳ_g[iʳ_g] fᶜ_g[iᶜ_g]. -/
def IsSplit : (cs : List CSplit) → Fac E cs → FacC E cs → FacR E cs → Prop
  | [], _, _, _ => True
  | c :: cs, (f, fs), (g, gs), (r, rs) =>
    (∀ i, f i = r (c.e i).2 * g (c.e i).1) ∧ IsSplit cs fs gs rs

theorem prodF_eq :
    ∀ (cs : List CSplit) (fs : Fac E cs) (gs : FacC E cs) (rs : FacR E cs), IsSplit cs fs gs rs →
      ∀ i : Tup cs, prodF cs fs i = prodC cs gs (split cs i).1 * prodR cs rs (split cs i).2
  | [], _, _, _, _, _ => by simp [prodF, prodC, prodR]
  | c :: cs, (f, fs), (g, gs), (r, rs), hs, (u, i) => by
      have ih := prodF_eq cs fs gs rs hs.2 i
      show f u * prodF cs fs i =
        (g (c.e u).1 * prodC cs gs (split cs i).1) * (r (c.e u).2 * prodR cs rs (split cs i).2)
      rw [hs.1 u, ih]
      ring

/-- Under `IsSplit`: the functional of a tensor claim is ∑_i ∏_g f_g[i_g] · (entry i of the tensor
that W' holds). -/
theorem LUnit.Tn_eq_sum (U : LUnit h k) (fs : Fac E U.cs) (gs : FacC E U.cs) (rs : FacR E U.cs)
    (hs : IsSplit U.cs fs gs rs) (W' : Fin h → (Fin k → Bool) → E) :
    U.toTLay.Tn (prodC U.cs gs) (prodR U.cs rs) W' =
      ∑ i : Tup U.cs, prodF U.cs fs i * U.toTLay.entry W' i :=
  Finset.sum_congr rfl fun i _ => by rw [prodF_eq U.cs fs gs rs hs i]; rfl

/-! ## 4. The extension of the column weights -/


end Layout

/-- The extension of the column weights of any layout: ∑ over the column parts of fᶜ[iᶜ] eq(z, col
iᶜ). -/
theorem MG.TLay.mle_eps {E Rw ι : Type} [Field E] [Fintype ι] [DecidableEq ι] (T : MG.TLay Rw ι)
    (fc : T.Ic → E) (z : ι → E) :
    Alg.mle (T.eps fc) z = ∑ ic, fc ic * Alg.eqk z (T.col ic) := by
  unfold Alg.mle MG.TLay.eps
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ic _ => ?_
  simp [mul_comm]

namespace Layout

open Alg

variable {h k : ℕ} {E : Type} [Field E]

/-! ## 5. The three kinds of coordinates -/

/-- i ↦ (i mod m, i div m), a bijection of [0, l m) onto [0, m) × [0, l). -/
def divMod (l m : ℕ) : Fin (l * m) ≃ Fin m × Fin l :=
  finProdFinEquiv.symm.trans (Equiv.prodComm _ _)

theorem divMod_fst (l m : ℕ) (i : Fin (l * m)) : ((divMod l m i).1 : ℕ) = i.val % m := rfl
theorem divMod_snd (l m : ℕ) (i : Fin (l * m)) : ((divMod l m i).2 : ℕ) = i.val / m := rfl

inductive Kind
  | low
  | high
  | whole
  deriving DecidableEq

/-- A coordinate of a unit: its extent R, a power 2^s that divides R (not necessarily the largest
one), and its kind. -/
structure Coord where
  R : ℕ
  s : ℕ
  hs : 2 ^ s ∣ R
  kind : Kind

namespace Coord

/-- Kind low, with t ≤ s bits: i = iʳ 2^t + iᶜ. -/
def lowSplit (c : Coord) (t : ℕ) (ht : t ≤ c.s) : CSplit where
  R := c.R
  t := t
  C := 2 ^ t
  l := c.R / 2 ^ t
  hC := le_rfl
  e := (finCongr (Nat.div_mul_cancel (dvd_trans (pow_dvd_pow 2 ht) c.hs)).symm).trans (divMod _ _)

theorem lowSplit_fst (c : Coord) (t : ℕ) (ht : t ≤ c.s) (i : Fin c.R) :
    (((c.lowSplit t ht).e i).1 : ℕ) = i.val % 2 ^ t := rfl
theorem lowSplit_snd (c : Coord) (t : ℕ) (ht : t ≤ c.s) (i : Fin c.R) :
    (((c.lowSplit t ht).e i).2 : ℕ) = i.val / 2 ^ t := rfl

theorem high_aux (c : Coord) (t : ℕ) (ht : t ≤ c.s) :
    c.R = (c.R / 2 ^ c.s * 2 ^ t) * 2 ^ (c.s - t) := by
  have h1 : 2 ^ c.s = 2 ^ t * 2 ^ (c.s - t) := by rw [← pow_add]; congr 1; omega
  calc c.R = c.R / 2 ^ c.s * 2 ^ c.s := (Nat.div_mul_cancel c.hs).symm
    _ = _ := by rw [h1, Nat.mul_assoc]

/-- Kind high, with t ≤ s bits and s' = s − t: i = a 2^s + b 2^s' + e with b < 2^t and e < 2^s';
then iᶜ = b and iʳ = a 2^s' + e. -/
def highSplit (c : Coord) (t : ℕ) (ht : t ≤ c.s) : CSplit where
  R := c.R
  t := t
  C := 2 ^ t
  l := c.R / 2 ^ c.s * 2 ^ (c.s - t)
  hC := le_rfl
  e := (finCongr (c.high_aux t ht)).trans <| (divMod _ _).trans <|
    (Equiv.prodCongr (Equiv.refl _) (divMod _ _)).trans <|
    (⟨fun x => (x.2.1, (x.2.2, x.1)), fun y => (y.2.2, (y.1, y.2.1)),
          fun _ => rfl, fun _ => rfl⟩ : Fin
          (2 ^ (c.s - t)) ×
        (Fin (2 ^ t) × Fin (c.R / 2 ^ c.s)) ≃
      Fin (2 ^ t) × (Fin (c.R / 2 ^ c.s) × Fin (2 ^ (c.s - t)))).trans <|
    Equiv.prodCongr (Equiv.refl _) finProdFinEquiv

theorem highSplit_fst (c : Coord) (t : ℕ) (ht : t ≤ c.s) (i : Fin c.R) :
    (((c.highSplit t ht).e i).1 : ℕ) = i.val / 2 ^ (c.s - t) % 2 ^ t := rfl
theorem highSplit_snd (c : Coord) (t : ℕ) (ht : t ≤ c.s) (i : Fin c.R) :
    (((c.highSplit t ht).e i).2 : ℕ) =
      i.val % 2 ^ (c.s - t) + 2 ^ (c.s - t) * (i.val / 2 ^ (c.s - t) / 2 ^ t) := rfl

/-- The split of kind high, with t ≤ s bits: if i = a 2^s + b 2^s' + e with s' = s − t, b < 2^t and
e < 2^s', then iᶜ = b and iʳ = a 2^s' + e. -/
theorem highSplit_apply (c : Coord) (t : ℕ) (ht : t ≤ c.s) (i : Fin c.R) {a b e : ℕ}
    (hb : b < 2 ^ t) (he : e < 2 ^ (c.s - t)) (hi : i.val = a * 2 ^ c.s + b * 2 ^ (c.s - t) + e) :
    (((c.highSplit t ht).e i).1 : ℕ) = b ∧
    (((c.highSplit t ht).e i).2 : ℕ) = a * 2 ^ (c.s - t) + e := by
  have h1 : 2 ^ c.s = 2 ^ t * 2 ^ (c.s - t) := by rw [← pow_add]; congr 1; omega
  have hp : 0 < 2 ^ (c.s - t) := by positivity
  have hq : 0 < 2 ^ t := by positivity
  have h2 : i.val = (a * 2 ^ t + b) * 2 ^ (c.s - t) + e := by rw [hi, h1]; ring
  have h3 : i.val / 2 ^ (c.s - t) = a * 2 ^ t + b := by
    rw [h2, Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt he, Nat.zero_add]
  have h4 : i.val % 2 ^ (c.s - t) = e := by
    rw [h2, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt he]
  rw [highSplit_fst, highSplit_snd, h3, h4]
  constructor
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
  · rw [Nat.add_comm (a * 2 ^ t), Nat.add_mul_div_right _ _ hq, Nat.div_eq_of_lt hb, Nat.zero_add]
    ring

/-- In the kinds low and high, with t ≤ s bits, the number of row parts is R / 2^t. -/
theorem highSplit_l (c : Coord) (t : ℕ) (ht : t ≤ c.s) : (c.highSplit t ht).l = c.R / 2 ^ t := by
  have hq : 0 < 2 ^ t := by positivity
  show c.R / 2 ^ c.s * 2 ^ (c.s - t) = c.R / 2 ^ t
  conv_rhs => rw [c.high_aux t ht]
  rw [Nat.mul_right_comm, Nat.mul_div_cancel _ hq]

/-- Kind whole with bits: (iᶜ, iʳ) = (i, 0). -/
def wholeCol (c : Coord) : CSplit where
  R := c.R
  t := Nat.clog 2 c.R
  C := c.R
  l := 1
  hC := Nat.le_pow_clog (by norm_num) _
  e := (Equiv.prodUnique (Fin c.R) (Fin 1)).symm

/-- Kind whole without bits: (iᶜ, iʳ) = (0, i). -/
def wholeRow (c : Coord) : CSplit where
  R := c.R
  t := 0
  C := 1
  l := c.R
  hC := le_rfl
  e := (Equiv.uniqueProd (Fin c.R) (Fin 1)).symm

/-- The split of a coordinate when `left` bits of the column number are left: a coordinate of kind
low or high takes min(s, left) bits; one of kind whole takes ⌈log₂ R⌉ bits if that many are left,
and none otherwise. -/
def toSplit (c : Coord) (left : ℕ) : CSplit :=
  match c.kind with
  | .low => c.lowSplit (min c.s left) (Nat.min_le_left _ _)
  | .high => c.highSplit (min c.s left) (Nat.min_le_left _ _)
  | .whole => if 0 < Nat.clog 2 c.R ∧ Nat.clog 2 c.R ≤ left then c.wholeCol else c.wholeRow

theorem toSplit_t_le (c : Coord) (left : ℕ) : (c.toSplit left).t ≤ left := by
  unfold toSplit
  cases c.kind with
  | low => exact Nat.min_le_right _ _
  | high => exact Nat.min_le_right _ _
  | whole =>
    show (if 0 < Nat.clog 2 c.R ∧ Nat.clog 2 c.R ≤ left then c.wholeCol else c.wholeRow).t ≤ left
    split_ifs with h
    · exact h.2
    · exact Nat.zero_le _

theorem toSplit_R (c : Coord) (left : ℕ) : (c.toSplit left).R = c.R := by
  unfold toSplit
  cases c.kind with
  | low => rfl
  | high => rfl
  | whole =>
    show (if 0 < Nat.clog 2 c.R ∧ Nat.clog 2 c.R ≤ left then c.wholeCol else c.wholeRow).R = c.R
    split_ifs <;> rfl

end Coord

/-- The splits of all coordinates of a unit: go through the coordinates with a counter of the bits
that are left. -/
def assign : List Coord → ℕ → List CSplit
  | [], _ => []
  | c :: cs, left => c.toSplit left :: assign cs (left - (c.toSplit left).t)

/-- The coordinates take at most the bits that there are. -/
theorem bitsOf_assign_le : ∀ (cs : List Coord) (left : ℕ), bitsOf (assign cs left) ≤ left
  | [], _ => Nat.zero_le _
  | c :: cs, left => by
      have h1 := bitsOf_assign_le cs (left - (c.toSplit left).t)
      have h2 := c.toSplit_t_le left
      have h3 : bitsOf (assign (c :: cs) left) =
          (c.toSplit left).t + bitsOf (assign cs (left - (c.toSplit left).t)) := by
        simp [assign, bitsOf]
      omega

/-! ## 6. `lowSplit` at equal numbers of bits -/


theorem Coord.lowSplit_congr (c : Coord) {t t' : ℕ} (h : t = t') (ht : t ≤ c.s) :
    c.lowSplit t ht = c.lowSplit t' (h ▸ ht) := by
  subst h; rfl


end Layout
end Blocks
