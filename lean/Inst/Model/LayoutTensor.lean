-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/LayoutTensor.lean: under the hypotheses of `Tn_eq_tlay`, a tensor claim on numbers is a
tensor claim of the merge.
To audit the relation `RinfPP` (Inst/Model/Scales.lean), nothing of this file need be read.

Inst/Model/Common/TensorClaim.lean has the functional Tn_a(W) = Σ_i Π_g f_g[i_g] W_W[i] of a
tensor claim on a unit of Inst/Model/Layout.lean, on numbers (indices are natural numbers). The
merge of tensor claims (`MG.TLay.toTen`, `MG.TLay.tval_toTen`) consumes a layout `MG.TLay`
(Blocks/MergeBlock.lean; the merge of tensor claims as one block is not there: Limits in that file's
head) with a factor on column parts and a factor on row parts. Here the two are tied:
    Part 1  `toSplit_spec`: the split of one coordinate in Blocks/Layout.lean (a bijection of finite
            types) has the bits, the number of row parts and the values of the split of
            Inst/Model/Layout.lean
    Part 2  `toL`, `col_eq`, `row_eq`, `rowsOf_eq`: index tuples as lists of numbers; `col` and
            `row` of the two files agree; so do the numbers of row parts
    Part 3  `facOf`, `facCOf`, `facROf`, `SplitOK`, `isSplit_of`: factors on numbers as factors on
            finite types; "products over the split" on numbers
    Part 4  `sum_tup`: a sum over the index tuples is `boxSum`
    Part 5  `lunit`, `matOf`, `entry_eq`, `Tn_eq_tlay`: a.Tn P k W = (lunit ..).toTLay.Tn (prodC ..)
            (prodR ..) (matOf W) (if the unit's rows are inside the matrix and `SplitOK` holds)
Part 1 follows the cases of `Bridge.good_split` (Inst/Model/LayoutBridge.lean).
Notation: `left`: a natural number; in `Coord.toSplit` (Blocks/Layout.lean), the bits of the column
number that are left; `R`, `t`, `l`, `e`: fields of `CSplit` (Blocks/Layout.lean): the coordinate
has the extent R and takes t bits of the number of the column, the column part is below C, the row
part below l, and `e : Fin R ≃ Fin C × Fin l`; `cB c`: a `Blocks.Layout.Coord`: the same coordinate
in the form of Blocks/Layout.lean (Inst/Model/LayoutBridge.lean); `tOf c left`, `lOf c t`: natural
numbers, t_g and l_g of Inst/Model/Layout.lean; `h`, `k`: natural numbers;
`matOf W : Fin h → (Fin k → Bool) → E`.
-/
import Inst.Model.LayoutBridge
import Inst.Model.Common.TensorClaim

set_option autoImplicit false

namespace Inst.Model.Layout.Tensor

open Finset Inst.Model Inst.Model.Layout Inst.Model.Layout.Bridge
open Blocks.Layout
  (CSplit Tup TupC TupR Fac FacC FacR prodF prodC prodR IsSplit colN rowN
    assign bitsOf rowsOf LUnit)

/-! ## Part 1. One coordinate -/

theorem toSplit_spec (c : Coord) (left : ℕ) :
    ((cB c).toSplit left).t = tOf c left ∧
    ((cB c).toSplit left).l = lOf c (tOf c left) ∧
    ∀ i : Fin ((cB c).toSplit left).R,
      ((((cB c).toSplit left).e i).1 : ℕ) = (split c (tOf c left) i.val).1 ∧
      ((((cB c).toSplit left).e i).2 : ℕ) = (split c (tOf c left) i.val).2 := by
  obtain ⟨R, kind⟩ := c
  cases kind with
  | low => exact ⟨rfl, rfl, fun i => ⟨rfl, rfl⟩⟩
  | high =>
    have ht : min (sOf R) left ≤ sOf R := Nat.min_le_left _ _
    refine ⟨rfl, Blocks.Layout.Coord.highSplit_l _ _ ht, fun i => ⟨rfl, ?_⟩⟩
    show (((cB ⟨R, .high⟩).highSplit (min (sOf R) left) ht).e i).2.val = _
    rw [Blocks.Layout.Coord.highSplit_snd]
    show i.val % 2 ^ (sOf R - min (sOf R) left) +
        2 ^ (sOf R - min (sOf R) left) *
          (i.val / 2 ^ (sOf R - min (sOf R) left) / 2 ^ min (sOf R) left) =
      i.val / 2 ^ sOf R * 2 ^ (sOf R - min (sOf R) left) + i.val % 2 ^ (sOf R - min (sOf R) left)
    rw [Nat.div_div_eq_div_mul, ← pow_add, Nat.sub_add_cancel ht]
    ring
  | whole =>
    by_cases hc : 0 < Nat.clog 2 R ∧ Nat.clog 2 R ≤ left
    · have e : (cB ⟨R, .whole⟩).toSplit left = (cB ⟨R, .whole⟩).wholeCol := if_pos hc
      have et : tOf ⟨R, .whole⟩ left = Nat.clog 2 R := if_pos hc.2
      rw [e, et]
      refine ⟨rfl, (if_pos hc.1 : lOf ⟨R, .whole⟩ (Nat.clog 2 R) = 1).symm, fun i => ?_⟩
      have : split ⟨R, .whole⟩ (Nat.clog 2 R) i.val = (i.val, 0) := if_pos hc.1
      rw [this]
      exact ⟨rfl, by simp [Blocks.Layout.Coord.wholeCol]⟩
    · have e : (cB ⟨R, .whole⟩).toSplit left = (cB ⟨R, .whole⟩).wholeRow := if_neg hc
      have et : tOf ⟨R, .whole⟩ left = 0 := by
        show (if Nat.clog 2 R ≤ left then Nat.clog 2 R else 0) = 0
        split_ifs with h
        · by_contra h0
          exact hc ⟨Nat.pos_of_ne_zero h0, h⟩
        · rfl
      rw [e, et]
      exact ⟨rfl, rfl, fun i => ⟨by simp [Blocks.Layout.Coord.wholeRow, split], rfl⟩⟩

/-! ## Part 2. Index tuples -/

/-- an index tuple as a list of numbers -/
def toL : (cs : List CSplit) → Tup cs → List ℕ
  | [], _ => []
  | _ :: cs, (u, r) => u.val :: toL cs r

/-- the splits of the coordinates of a unit of the model -/
abbrev csOf (cs : List Coord) (left : ℕ) : List CSplit := assign (cs.map cB) left

theorem col_eq :
    ∀ (cs : List Coord) (left : ℕ) (i : Tup (csOf cs left)),
      colN (csOf cs left) (Blocks.Layout.split (csOf cs left) i).1 =
        col cs (bits cs left) (toL (csOf cs left) i)
  | [], _, _ => rfl
  | c :: cs, left, (u, r) => by
      obtain ⟨h1, _, h3⟩ := toSplit_spec c left
      have ih := col_eq cs (left - ((cB c).toSplit left).t) r
      show colN (assign (cs.map cB) (left - ((cB c).toSplit left).t)) (Blocks.Layout.split _ r).1 *
            2 ^ ((cB c).toSplit left).t +
          ((((cB c).toSplit left).e u).1 : ℕ) =
        (split c (tOf c left) u.val).1 +
          2 ^ tOf c left * col cs (bits cs (left - tOf c left)) (toL _ r)
      have ih' : colN (assign (cs.map cB) (left - ((cB c).toSplit left).t))
            (Blocks.Layout.split (assign (cs.map cB) (left - ((cB c).toSplit left).t)) r).1 =
          col cs (bits cs (left - ((cB c).toSplit left).t))
            (toL (assign (cs.map cB) (left - ((cB c).toSplit left).t)) r) := ih
      rw [ih', (h3 u).1]
      generalize toL (assign (cs.map cB) (left - ((cB c).toSplit left).t)) r = is
      rw [h1]
      ring

theorem row_eq (b : ℕ) :
    ∀ (cs : List Coord) (left : ℕ) (i : Tup (csOf cs left)),
      rowN (csOf cs left) (Blocks.Layout.split (csOf cs left) i).2 b =
        row b cs (bits cs left) (toL (csOf cs left) i)
  | [], _, _ => rfl
  | c :: cs, left, (u, r) => by
      obtain ⟨h1, h2, h3⟩ := toSplit_spec c left
      have ih := row_eq b cs (left - ((cB c).toSplit left).t) r
      show rowN (assign (cs.map cB) (left - ((cB c).toSplit left).t))
              (Blocks.Layout.split _ r).2 b *
            ((cB c).toSplit left).l +
          ((((cB c).toSplit left).e u).2 : ℕ) =
        (split c (tOf c left) u.val).2 +
          lOf c (tOf c left) * row b cs (bits cs (left - tOf c left)) (toL _ r)
      have ih' : rowN (assign (cs.map cB) (left - ((cB c).toSplit left).t))
            (Blocks.Layout.split (assign (cs.map cB) (left - ((cB c).toSplit left).t)) r).2 b =
          row b cs (bits cs (left - ((cB c).toSplit left).t))
            (toL (assign (cs.map cB) (left - ((cB c).toSplit left).t)) r) := ih
      rw [ih', (h3 u).2, h2]
      generalize toL (assign (cs.map cB) (left - ((cB c).toSplit left).t)) r = is
      rw [h1]
      ring

theorem rowsOf_eq : ∀ (cs : List Coord) (left : ℕ), rowsOf (csOf cs left) = lprod cs left
  | [], _ => rfl
  | c :: cs, left => by
      obtain ⟨h1, h2, _⟩ := toSplit_spec c left
      have ih := rowsOf_eq cs (left - ((cB c).toSplit left).t)
      show (((cB c).toSplit left).l ::
          (csOf cs (left - ((cB c).toSplit left).t)).map fun c => c.l).prod =
        lOf c (tOf c left) * lprod cs (left - tOf c left)
      rw [List.prod_cons, h2]
      congr 1
      rw [← h1]
      exact ih

/-! ## Part 3. Factors -/

variable {E : Type} [Field E]

/-- factors on numbers, as factors on the coordinates; a missing factor is 0, as in `boxSum` -/
def facOf : (cs : List CSplit) → List (ℕ → E) → Fac E cs
  | [], _ => ()
  | _ :: cs, [] => (fun _ => 0, facOf cs [])
  | _ :: cs, f :: fs => (fun u => f u.val, facOf cs fs)
/-- on the column parts -/
def facCOf : (cs : List CSplit) → List (ℕ → E) → FacC E cs
  | [], _ => ()
  | _ :: cs, [] => (fun _ => 0, facCOf cs [])
  | _ :: cs, f :: fs => (fun u => f u.val, facCOf cs fs)
/-- on the row parts -/
def facROf : (cs : List CSplit) → List (ℕ → E) → FacR E cs
  | [], _ => ()
  | _ :: cs, [] => (fun _ => 0, facROf cs [])
  | _ :: cs, f :: fs => (fun u => f u.val, facROf cs fs)

/-- The factors are products over the split, on numbers: f_g[i] = fʳ_g[iʳ] fᶜ_g[iᶜ] for all i < R_g,
with the split of Inst/Model/Layout.lean when "left" bits are left. -/
def SplitOK : List Coord → ℕ → List (ℕ → E) → List (ℕ → E) → List (ℕ → E) → Prop
  | [], _, _, _, _ => True
  | c :: cs, left, f :: fs, g :: gs, r :: rs =>
      (∀ i < c.R, f i = r (split c (tOf c left) i).2 * g (split c (tOf c left) i).1) ∧
      SplitOK cs (left - tOf c left) fs gs rs
  | _ :: _, _, _, _, _ => False

theorem isSplit_of :
    ∀ (cs : List Coord) (left : ℕ) (fs gs rs : List (ℕ → E)),
      SplitOK cs left fs gs rs → IsSplit (csOf cs left) (facOf _ fs) (facCOf _ gs) (facROf _ rs)
  | [], _, _, _, _, _ => trivial
  | c :: cs, left, f :: fs, g :: gs, r :: rs, h => by
      obtain ⟨h1, _, h3⟩ := toSplit_spec c left
      refine ⟨fun i => ?_, isSplit_of cs (left - ((cB c).toSplit left).t) fs gs rs (h1 ▸ h.2)⟩
      show f i.val = r ((((cB c).toSplit left).e i).2 : ℕ) * g ((((cB c).toSplit left).e i).1 : ℕ)
      rw [(h3 i).1, (h3 i).2]
      exact h.1 i.val (lt_of_lt_of_eq i.2 ((cB c).toSplit_R left))
  | _ :: _, _, [], _, _, h => h.elim
  | _ :: _, _, _ :: _, [], _, h => h.elim
  | _ :: _, _, _ :: _, _ :: _, [], h => h.elim

/-! ## Part 4. A sum over the index tuples -/

theorem sum_tup : ∀ (cs : List Coord) (left : ℕ) (fs : List (ℕ → E)) (F : List ℕ → E),
    ∑ i : Tup (csOf cs left), prodF (csOf cs left) (facOf _ fs) i * F (toL _ i) = boxSum cs fs F
  | [], _, _, F => by
      show ∑ _i : Unit, (1 : E) * F [] = F []
      simp
  | c :: cs, left, [], F => by
      show ∑ i : Fin ((cB c).toSplit left).R × Tup (csOf cs (left - ((cB c).toSplit left).t)),
          ((0 : E) * prodF _ (facOf _ []) i.2) * F (i.1.val :: toL _ i.2) = 0
      simp
  | c :: cs, left, f :: fs, F => by
      show ∑ i : Fin ((cB c).toSplit left).R × Tup (csOf cs (left - ((cB c).toSplit left).t)),
          (f i.1.val * prodF _ (facOf _ fs) i.2) * F (i.1.val :: toL _ i.2) =
        ∑ i ∈ range c.R, f i * boxSum cs fs fun is => F (i :: is)
      rw [Fintype.sum_prod_type]
      have e : ∀ u : Fin ((cB c).toSplit left).R,
          (∑ y : Tup (csOf cs (left - ((cB c).toSplit left).t)),
              (f u.val * prodF _ (facOf _ fs) y) * F (u.val :: toL _ y)) =
            f u.val * boxSum cs fs fun is => F (u.val :: is) := fun u => by
        rw [← sum_tup cs (left - ((cB c).toSplit left).t) fs fun is => F (u.val :: is), mul_sum]
        exact sum_congr rfl fun y _ => mul_assoc _ _ _
      rw [Fintype.sum_congr _ _ e,
        Fin.sum_univ_eq_sum_range (fun i => f i * boxSum cs fs fun is => F (i :: is)),
        (cB c).toSplit_R left]
      rfl

/-! ## Part 5. The unit, the matrix, the claim -/

/-- a matrix that is read on numbers, as the merge reads it: a row is a number below h, a column a
vertex of the hypercube {0, 1}^k, the variable 0 for the highest bit -/
def matOf {h k : ℕ} (W : ℕ → ℕ → E) : Fin h → (Fin k → Bool) → E := fun y c => W y.val (Alg.num c)

/-- The unit U with the number n, in the form of Blocks/Layout.lean. Required: its rows are inside
the matrix. -/
def lunit (k h : ℕ) (us : List UnitS) (n : ℕ) (U : UnitS) (hr : off k us n + rows k U ≤ h) :
    LUnit h k :=
  ⟨csOf U.coords k, U.nU, off k us n, Blocks.Layout.bitsOf_assign_le _ _,
    by rw [rowsOf_eq, ← hU_eq]; exact hr⟩

theorem entry_eq (P : Params) (k h : ℕ) (W : ℕ → ℕ → E) (n : ℕ) (U : UnitS)
    (hr : off k (units P) n + rows k U ≤ h) (i : Tup (csOf U.coords k)) :
    (lunit k h (units P) n U hr).toTLay.entry (matOf W) i = entryW P k W n U (toL _ i) := by
  have hlt : colN (csOf U.coords k) (Blocks.Layout.split (csOf U.coords k) i).1 < 2 ^ k :=
    lt_of_lt_of_le (Blocks.Layout.colN_lt _ _)
      (Nat.pow_le_pow_right (by norm_num) (Blocks.Layout.bitsOf_assign_le _ _))
  show ∑ b : Fin U.nU, (256 : E) ^ (b : ℕ) *
      W (off k (units P) n +
          rowN (csOf U.coords k) (Blocks.Layout.split (csOf U.coords k) i).2 b.val)
        (Alg.num
          (Alg.bits k (colN (csOf U.coords k) (Blocks.Layout.split (csOf U.coords k) i).1))) = _
  rw [Alg.num_bits hlt, col_eq,
    Fin.sum_univ_eq_sum_range (fun b =>
      (256 : E) ^ b *
        W (off k (units P) n + rowN (csOf U.coords k) (Blocks.Layout.split (csOf U.coords k) i).2 b)
          (col U.coords (bits U.coords k) (toL _ i)))]
  exact sum_congr rfl fun b _ => by rw [row_eq]; rfl

/-- A tensor claim on numbers is a tensor claim of the merge. If the rows of the unit are inside the
matrix and the factors are products over the split, with the factors gs on the column parts and rs
on the row parts, then the functional of the claim is the functional `MG.TLay.Tn` of the unit, for
the products of these factors, on the matrix as the merge reads it. -/
theorem Tn_eq_tlay (P : Params) (k h : ℕ) (W : ℕ → ℕ → E)
    (a : TClaim E) (hr : off k (units P) a.n + rows k a.U ≤ h)
    (gs rs : List (ℕ → E)) (hs : SplitOK a.U.coords k a.f gs rs) :
    a.Tn P k W =
      (lunit k h (units P) a.n a.U hr).toTLay.Tn
        (prodC _ (facCOf _ gs)) (prodR _ (facROf _ rs)) (matOf W) := by
  rw [LUnit.Tn_eq_sum (lunit k h (units P) a.n a.U hr) (facOf _ a.f) (facCOf _ gs)
      (facROf _ rs) (isSplit_of _ _ _ _ _ hs)]
  simp only [entry_eq]
  exact (sum_tup a.U.coords k a.f fun i => entryW P k W a.n a.U i).symm

/-- The rows of a unit of the list are inside a matrix that holds all units. -/
theorem rows_fit (k h : ℕ) (us : List UnitS) (n : ℕ) (U : UnitS)
    (hU : us[n]? = some U) (hh : off k us us.length ≤ h) : off k us n + rows k U ≤ h := by
  have hn : n < us.length := (List.getElem?_eq_some_iff.mp hU).1
  rw [← off_succ k us n U hU]
  exact le_trans (off_mono k us hn) hh

end Inst.Model.Layout.Tensor

