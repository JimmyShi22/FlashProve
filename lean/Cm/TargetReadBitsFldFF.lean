-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetReadBitsFldFF.lean: under the premises below, the cells and values of the feed-forward
segments are separable at a row side (`SepB`, `SepK`, Cm/TargetReadBitsFldRow.lean). That row side
depends on their group, their matrix, the split (`cs`, `rs`), the row guard `gT` and what is read
off the row side (`jl`, `pos`) alone; in `sepB_cCellLo`, `sepB_cCellHi`, `sepK_cValLo`,
`sepK_cValHi` also on OFF X' mod 2^f. So, under the premises below, all cells and values that share
all of these cost together at most one piece for each block of that row side: one a part of the
matrix; in these four theorems, where there are two row sides, "no carry" and "carry", two a part;
in the fall-back 2^f a part.

Separable with at most n pieces in the shapes R, C (the numbers of rows and columns of each
segment's matrix), of a function F of a vertex b < 2^v of a cube and of matrices A: at every vertex
b and for all A the value F b A is a constant k b plus at most n pieces, the same at all vertices
(`Sep`, `SepV`, `SPiece`, Cm/TargetReadBits.lean). What a piece is: the sentence "Separable …" of
Cm/TargetReadBitsFldRow.lean's head holds here too.

A row side W (`RowT`, Cm/TargetReadBitsFldRow.lean) is a segment seg, lists cs, rs of row and column
sources, a guard gT on t, a row map ρ and a list L of block numbers; t and u are the numbers that cs
and rs form at the vertex. A value function is separable at W up to a constant (`SepK`) if there are
column tables β, the same at all vertices, such that at each vertex b and for all matrices A its
value is a constant k b plus, where gT t holds, Σ_{j ∈ L} Σ_{y < C seg} β j u y · A seg (ρ t j) y;
and where gT t holds, the row ρ t j is below R seg wherever β j u y is not 0 (j ∈ L, y < C seg).
`SepB`: the same without the constant k b.

Definitions, statements as theorems, proofs, in one file. At the model's own sizes (`DF`: the
reference parameters of Inst/Model/FF/Index.lean); any field.

What a value is (Cm/SegPilotKit.lean): cVal g X a j i = Σ_{k < nCell X} 256^k · (cell k of array X,
instance a, channel j, position i) + an offset; cCell g c: one cell. The cell's place: feature OFF X
+ (k · cnt X + a) · width X + j; row (feature mod 2^f) · T + i, column feature / 2^f, f = fBitsX X
(6, 5 or 3 by the matrix); stacked in parts of width 5,990 from the matrix's slot (`plFF`,
Cm/SegLayout.lean).
Fields of b become numbers of sources by Cm/TargetReadBitsFld.lean (`fldsS`, `Spec.flds_num`,
`Spec.flds_ok`; proved in Cm/TargetReadBitsFldProofs.lean). All premises on t and u are asked at
vertices b < 2^v, under the guards gT t, gU u.

Main names:
  `OwnAs g X g' X'` (`ownFF`, Cm/SegLayout.lean): `own_self` (X' = X, g' = g, unless X = x0 and 0 <
    g); `own_x0` (x0 of a later group is x8 of the group before).
  `ff_clean`, which arrays are clean: 2^f divides the width of every array but sc and D; 2^f divides
    OFF X for every array but D, ly, l3; these four arrays lie in the matrix ar.
  The form: if gT t ∧ gU u then cf u · (the cell or value at instance a u, channel 2^f · jh u + jl
    t, position pos t) else 0: the instance and the channel's high digits are read off the column
    side, its low f digits and the position off the row side; a, jh, jl, pos, cf are any functions.
  Premises: `hown : OwnAs g X g' X'`: f, OFF, width, slot and parts below are those of X'; "their
    group", "their matrix" in the title are g' and the matrix of X'. For a cell: k < nCell X. At
    vertices under the guards: jl t < 2^f, pos t < T, a u < cnt X, 2^f · jh u + 2^f ≤ width X.
    `hSh`: every place of a valid cell that the segment reads (`IsFF g`, Cm/SegPilotKit.lean) lies
    in the shapes (row < R, column < C of its segment).
  `sepB_cCell0`, `sepK_cVal0`: 2^f ∣ OFF, 2^f ∣ width: at rowF (2 g') cs rs gT jl pos T (the
    matrix's slot) (its parts).
  `sepB_cCellLo`, `sepK_cValLo`: 2^f ∣ width, c₀ := OFF mod 2^f: under the further row guard "no
    carry" (c₀ + jl t < 2^f): at rowF with the row digit c₀ + jl t.
  `sepB_cCellHi`, `sepK_cValHi`: the same under "carry" (2^f ≤ c₀ + jl t): at rowF with the row
    digit c₀ + jl t − 2^f.
  `sepB_cCellAny`, `sepK_cValAny`, the fall-back, every array: instance a u and channel j u < width
    X any functions of the column side's number: at rowAny.
  Then (Cm/TargetReadBitsFldRow.lean): sums, differences, multiples and guards on the column side
    stay at the same row side. By `sepK_sepV`, if Src.OK (cs ++ rs) v, they cost at most as many
    pieces as blocks: nPartX | nPartX | nPartX | nPartX · 2^f, in the order of the four rows above.

Limits: this file does not say that the families' atoms have this form.
It says nothing on the look-up's bits (matrix b).
It does not say that so many pieces are needed.

Terms: lean/GLOSSARY.md.
-/
import Cm.TargetReadBitsFldRow
import Cm.TargetReadBitsFldProofs
import Cm.SegPilotKit
import Inst.Model.FF.IndexFacts

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.TR

open Cb Blocks Finset Inst.Model Inst.Model.All Cm.Seg

/-- The number of bits of the features in a column of the array's matrix. -/
def fBitsX (X : FFSeg.Arr) : ℕ := FFSeg.lFeat DF X.mx

/-- The number of parts of its matrix. -/
def nPartX (X : FFSeg.Arr) : ℕ := if X.mx = .af then 3 else 1

/-- The row side of a stacked matrix: the row digit rd t and the position pos t in the block
slot + j. -/
def rowF (seg : ℕ) (cs rs : List Src) (gT : ℕ → Prop) [DecidablePred gT]
    (rd pos : ℕ → ℕ) (T slot Q : ℕ) : RowT :=
  ⟨seg, cs, rs, gT, fun t j => (slot + j) * hSlot + (rd t * T + pos t), List.range Q⟩

theorem nCol_le (X : FFSeg.Arr) : FFSeg.nCol DF X.mx ≤ colsFF * nPartX X := by
  cases X <;> decide +kernel

theorem plFF_eq (c : FFSeg.Cell) :
    plFF c = ((slotFF c.X.mx + FFSeg.feat DF c.X c.k c.inst c.j / 2 ^ fBitsX c.X / colsFF) * hSlot +
          (FFSeg.feat DF c.X c.k c.inst c.j % 2 ^ fBitsX c.X * DF.T + c.i),
        FFSeg.feat DF c.X c.k c.inst c.j / 2 ^ fBitsX c.X % colsFF) := rfl

variable {E : Type} [Field E]

theorem sepB_ffCore (R C : ℕ → ℕ) (v g' : ℕ) (X : FFSeg.Arr) (k : ℕ) (cs rs : List Src)
    (gT gU : ℕ → Prop) [DecidablePred gT] [DecidablePred gU] (cf : ℕ → E)
    (inst chan : ℕ → ℕ → ℕ) (rd pos col : ℕ → ℕ)
    (hv : ∀ b < 2 ^ v, gT (Src.num cs v b) → gU (Src.num rs v b) →
      (⟨X, k, inst (Src.num cs v b) (Src.num rs v b), chan (Src.num cs v b) (Src.num rs v b),
        pos (Src.num cs v b)⟩ : FFSeg.Cell).Valid DF ∧
      FFSeg.feat DF X k (inst (Src.num cs v b) (Src.num rs v b))
            (chan (Src.num cs v b) (Src.num rs v b)) % 2 ^ fBitsX X =
        rd (Src.num cs v b) ∧
      FFSeg.feat DF X k (inst (Src.num cs v b) (Src.num rs v b))
            (chan (Src.num cs v b) (Src.num rs v b)) / 2 ^ fBitsX X =
        col (Src.num rs v b))
    (hSh : ∀ c : FFSeg.Cell,
      c.Valid DF → c.X = X → (plFF c).1 < R (2 * g') ∧ (plFF c).2 < C (2 * g')) :
    SepB R C v (rowF (2 * g') cs rs gT rd pos DF.T (slotFF X.mx) (nPartX X)) fun b A => if gT (Src.num cs v b) ∧ gU (Src.num rs v b) then
      cf (Src.num rs v b) *
        A (2 * g')
          (plFF ⟨X, k, inst (Src.num cs v b) (Src.num rs v b),
              chan (Src.num cs v b) (Src.num rs v b), pos (Src.num cs v b)⟩).1
          (plFF ⟨X, k, inst (Src.num cs v b) (Src.num rs v b),
              chan (Src.num cs v b) (Src.num rs v b), pos (Src.num cs v b)⟩).2
      else 0 := by
  have hpl : ∀ b < 2 ^ v, gT (Src.num cs v b) → gU (Src.num rs v b) →
      plFF ⟨X, k, inst (Src.num cs v b) (Src.num rs v b),
            chan (Src.num cs v b) (Src.num rs v b), pos (Src.num cs v b)⟩ =
        ((slotFF X.mx + col (Src.num rs v b) / colsFF) * hSlot +
            (rd (Src.num cs v b) * DF.T + pos (Src.num cs v b)),
          col (Src.num rs v b) % colsFF) := fun b hb h1 h2 => by
    obtain ⟨-, e1, e2⟩ := hv b hb h1 h2
    rw [plFF_eq]
    show ((slotFF X.mx + FFSeg.feat DF X k _ _ / 2 ^ fBitsX X / colsFF) * hSlot +
          (FFSeg.feat DF X k _ _ % 2 ^ fBitsX X * DF.T + pos _),
        FFSeg.feat DF X k _ _ / 2 ^ fBitsX X % colsFF) = _
    rw [e1, e2]
  refine sepB_congr E R C v _ _ _ (fun b hb A => ?_)
    (sepB_cell E R C v (rowF (2 * g') cs rs gT rd pos DF.T (slotFF X.mx) (nPartX X)) gU cf
      (fun u => col u / colsFF) (fun u => col u % colsFF) (fun b hb h1 h2 => ?_) List.nodup_range)
  · by_cases hg : gT (Src.num cs v b) ∧ gU (Src.num rs v b)
    · rw [if_pos hg, hpl b hb hg.1 hg.2]
      exact (if_pos hg).symm
    · rw [if_neg hg]
      exact (if_neg hg).symm
  · obtain ⟨hc, -, e2⟩ := hv b hb h1 h2
    have hs := hSh _ hc rfl
    rw [hpl b hb h1 h2] at hs
    refine ⟨List.mem_range.2 ?_, hs.1, hs.2⟩
    have h3 := (FFSeg.IndexFacts.addrRange DF FFSeg.ref_ok _ hc).2
    have h4 : col (Src.num rs v b) < FFSeg.nCol DF X.mx := by
      rw [← e2]
      exact h3
    exact Nat.div_lt_of_lt_mul (lt_of_lt_of_le h4 (nCol_le X))


/-- The fall-back's row side. -/
def rowAny (seg : ℕ) (cs rs : List Src) (gT : ℕ → Prop) [DecidablePred gT]
    (pos : ℕ → ℕ) (f T slot Q : ℕ) : RowT :=
  ⟨seg, cs, rs, gT, fun t j => (slot + j / 2 ^ f) * hSlot + (j % 2 ^ f * T + pos t),
    List.range (Q * 2 ^ f)⟩

/-- The segment of group g reads the cells of X under the own names of X' in group g', and X' has
the nCell, cnt and width of X. -/
structure OwnAs (g : ℕ) (X : FFSeg.Arr) (g' : ℕ) (X' : FFSeg.Arr) : Prop where
  own : ∀ k a j i, ownFF g ⟨X, k, a, j, i⟩ = .ff g' ⟨X', k, a, j, i⟩
  nCell : X'.nCell = X.nCell
  cnt : X'.cnt DF = X.cnt DF
  width : X'.width DF = X.width DF

theorem own_self (g : ℕ) (X : FFSeg.Arr) (h : ¬ (X = .x0 ∧ 0 < g)) : OwnAs g X g X :=
  ⟨fun _ _ _ _ => if_neg h, rfl, rfl, rfl⟩

theorem own_x0 (g : ℕ) (h : 0 < g) : OwnAs g .x0 (g - 1) .x8 :=
  ⟨fun _ _ _ _ => if_pos ⟨rfl, h⟩, rfl, rfl, rfl⟩

/-- Which arrays are clean. -/
theorem ff_clean :
    (∀ X : FFSeg.Arr, X ≠ .sc → X ≠ .D → 2 ^ fBitsX X ∣ X.width DF) ∧
    (∀ X : FFSeg.Arr, X ≠ .D → X ≠ .ly → X ≠ .l3 → 2 ^ fBitsX X ∣ FFSeg.OFF DF X) ∧
    ∀ X : FFSeg.Arr, X = .sc ∨ X = .D ∨ X = .ly ∨ X = .l3 → X.mx = .ar := by
  refine ⟨fun X h1 h2 => ?_, fun X h1 h2 h3 => ?_, fun X h => ?_⟩
  · cases X <;> first | exact absurd rfl h1 | exact absurd rfl h2 | decide +kernel
  · cases X <;> first | exact absurd rfl h1 | exact absurd rfl h2 | exact absurd rfl h3 | decide +kernel
  · rcases h with rfl | rfl | rfl | rfl <;> rfl

/-- The cell's value, at the own name. -/
theorem val_ownAs {g g' : ℕ} {X X' : FFSeg.Arr} (h : OwnAs g X g' X')
    (k a j i : ℕ) (A : ℕ → ℕ → ℕ → E) :
    (cCell g ⟨X, k, a, j, i⟩ : CForm E).val A =
      A (2 * g') (plFF ⟨X', k, a, j, i⟩).1 (plFF ⟨X', k, a, j, i⟩).2 := by
  rw [val_cCell]
  unfold tA
  rw [h.own]
  rfl

/-- The shapes, at the own names. -/
theorem sh_ownAs {g g' : ℕ} {X X' : FFSeg.Arr} (h : OwnAs g X g' X') (R C : ℕ → ℕ)
    (hSh : ∀ p : Cb.Place, IsFF g p → p.2.1 < R p.1 ∧ p.2.2 < C p.1) (c : FFSeg.Cell)
    (hc : c.Valid DF) (hX : c.X = X') :
    (plFF c).1 < R (2 * g') ∧ (plFF c).2 < C (2 * g') := by
  obtain ⟨X₀, k, a, j, i⟩ := c
  obtain rfl : X₀ = X' := hX
  have hc' : (⟨X, k, a, j, i⟩ : FFSeg.Cell).Valid DF :=
    ⟨h.nCell ▸ hc.1, h.cnt ▸ hc.2.1, h.width ▸ hc.2.2.1, hc.2.2.2⟩
  have := hSh _ ⟨_, hc', rfl⟩
  rw [h.own] at this
  exact this

/-- The feature of (instance, high digits, low digits). -/
theorem feat_eq (X : FFSeg.Arr) (k a M jh jl : ℕ) :
    FFSeg.feat DF X k a (M * jh + jl) =
      (FFSeg.OFF DF X + (k * X.cnt DF + a) * X.width DF) + M * jh + jl := by
  unfold FFSeg.feat
  omega

/-- The offset of (k, instance) modulo 2^f, where 2^f divides the width. -/
theorem base_mod (X : FFSeg.Arr) (k a M : ℕ) (hW : M ∣ X.width DF) :
    (FFSeg.OFF DF X + (k * X.cnt DF + a) * X.width DF) % M = FFSeg.OFF DF X % M := by
  obtain ⟨w, hw⟩ := hW
  rw [hw, ← Nat.mul_assoc, Nat.mul_comm _ M, Nat.mul_assoc, Nat.add_mul_mod_self_left]

theorem sepB_cCell0 (R C : ℕ → ℕ) (v g g' : ℕ) (X X' : FFSeg.Arr) (cs rs : List Src)
    (gT gU : ℕ → Prop) [DecidablePred gT] [DecidablePred gU] (cf : ℕ → E) (k : ℕ)
    (a jh jl pos : ℕ → ℕ) (hown : OwnAs g X g' X') (hk : k < X.nCell)
    (hO : 2 ^ fBitsX X' ∣ FFSeg.OFF DF X') (hW : 2 ^ fBitsX X' ∣ X'.width DF)
    (hv : ∀ b < 2 ^ v, gT (Src.num cs v b) → gU (Src.num rs v b) →
      jl (Src.num cs v b) < 2 ^ fBitsX X' ∧
      pos (Src.num cs v b) < DF.T ∧
      a (Src.num rs v b) < X.cnt DF ∧
      2 ^ fBitsX X' * jh (Src.num rs v b) + 2 ^ fBitsX X' ≤ X.width DF)
    (hSh : ∀ p : Cb.Place, IsFF g p → p.2.1 < R p.1 ∧ p.2.2 < C p.1) :
    SepB R C v (rowF (2 * g') cs rs gT jl pos DF.T (slotFF X'.mx) (nPartX X')) fun b A =>
      if gT (Src.num cs v b) ∧ gU (Src.num rs v b) then
        cf (Src.num rs v b) *
          (cCell g ⟨X, k, a (Src.num rs v b),
              2 ^ fBitsX X' * jh (Src.num rs v b) + jl (Src.num cs v b),
              pos (Src.num cs v b)⟩ : CForm E).val A
      else 0 := by
  have hM : 0 < 2 ^ fBitsX X' := Nat.pos_of_ne_zero (by positivity)
  refine sepB_congr E R C v _ _ _ (fun b _ A => by rw [val_ownAs hown])
    (sepB_ffCore R C v g' X' k cs rs gT gU cf (fun _ u => a u)
      (fun t u => 2 ^ fBitsX X' * jh u + jl t) jl pos
      (fun u => (FFSeg.OFF DF X' + (k * X'.cnt DF + a u) * X'.width DF) / 2 ^ fBitsX X' + jh u)
      (fun b hb hT hU => ?_) (sh_ownAs hown R C hSh))
  obtain ⟨h1, h2, h3, h4⟩ := hv b hb hT hU
  refine ⟨⟨hown.nCell ▸ hk, hown.cnt ▸ h3, (by
    show 2 ^ fBitsX X' * jh (Src.num rs v b) + jl (Src.num cs v b) < X'.width DF
    rw [hown.width]
    omega), h2⟩, ?_⟩
  · show FFSeg.feat DF X' k (a (Src.num rs v b))
            (2 ^ fBitsX X' * jh (Src.num rs v b) + jl (Src.num cs v b)) % 2 ^ fBitsX X' = _ ∧
      FFSeg.feat DF X' k (a (Src.num rs v b))
            (2 ^ fBitsX X' * jh (Src.num rs v b) + jl (Src.num cs v b)) / 2 ^ fBitsX X' = _
    obtain ⟨s1, s2⟩ := feat_split (2 ^ fBitsX X')
      (FFSeg.OFF DF X' + (k * X'.cnt DF + a (Src.num rs v b)) * X'.width DF) (jh (Src.num rs v b))
      (jl (Src.num cs v b)) hM
    rw [feat_eq]
    have hb0 : (FFSeg.OFF DF X' + (k * X'.cnt DF + a (Src.num rs v b)) * X'.width DF) %
          2 ^ fBitsX X' = 0 := by
      rw [base_mod X' k _ _ hW, Nat.mod_eq_zero_of_dvd hO]
    rw [s1, s2, hb0, Nat.zero_add, Nat.mod_eq_of_lt h1, Nat.div_eq_of_lt h1]
    exact ⟨rfl, rfl⟩

theorem sepK_cVal0 (R C : ℕ → ℕ) (v g g' : ℕ) (X X' : FFSeg.Arr) (cs rs : List Src)
    (gT gU : ℕ → Prop) [DecidablePred gT] [DecidablePred gU] (cf : ℕ → E)
    (a jh jl pos : ℕ → ℕ) (hown : OwnAs g X g' X')
    (hO : 2 ^ fBitsX X' ∣ FFSeg.OFF DF X') (hW : 2 ^ fBitsX X' ∣ X'.width DF)
    (hv : ∀ b < 2 ^ v, gT (Src.num cs v b) → gU (Src.num rs v b) →
      jl (Src.num cs v b) < 2 ^ fBitsX X' ∧
      pos (Src.num cs v b) < DF.T ∧
      a (Src.num rs v b) < X.cnt DF ∧
      2 ^ fBitsX X' * jh (Src.num rs v b) + 2 ^ fBitsX X' ≤ X.width DF)
    (hSh : ∀ p : Cb.Place, IsFF g p → p.2.1 < R p.1 ∧ p.2.2 < C p.1) :
    SepK R C v (rowF (2 * g') cs rs gT jl pos DF.T (slotFF X'.mx) (nPartX X')) fun b A =>
      if gT (Src.num cs v b) ∧ gU (Src.num rs v b) then
        cf (Src.num rs v b) *
          (cVal g X (a (Src.num rs v b)) (2 ^ fBitsX X' * jh (Src.num rs v b) + jl (Src.num cs v b))
            (pos (Src.num cs v b)) : CForm E).val A
      else 0 := by
  refine sepK_congr E R C v _ _ _ (fun b _ A => ?_)
    (sepK_add E R C v _ _ _
      (sepK_sum E R C v X.nCell _
        (fun k b A =>
          (256 : E) ^ k *
            (if gT (Src.num cs v b) ∧ gU (Src.num rs v b) then
                cf (Src.num rs v b) *
                  (cCell g ⟨X, k, a (Src.num rs v b),
                      2 ^ fBitsX X' * jh (Src.num rs v b) + jl (Src.num cs v b),
                      pos (Src.num cs v b)⟩ : CForm E).val A
              else 0)) fun k hk =>
                sepK_smul E R C v _ ((256 : E) ^ k) _
                  (sepK_ofB E R C v _ _
                    (sepB_cCell0 R C v g g' X X' cs rs gT gU cf k a jh jl
                      pos hown hk hO hW hv hSh)))
      (sepK_const E R C v _ fun b =>
        if gT (Src.num cs v b) ∧ gU (Src.num rs v b) then cf (Src.num rs v b) * ((X.off : ℤ) : E)
        else 0))
  by_cases hg : gT (Src.num cs v b) ∧ gU (Src.num rs v b)
  · simp only [if_pos hg, val_cVal, val_cCell, FFSeg.val]
    rw [mul_add, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  · simp only [if_neg hg, mul_zero, Finset.sum_const_zero, add_zero]

theorem sepB_cCellLo (R C : ℕ → ℕ) (v g g' : ℕ) (X X' : FFSeg.Arr)
    (cs rs : List Src) (gT gU : ℕ → Prop) [DecidablePred gT] [DecidablePred gU]
    (cf : ℕ → E) (k : ℕ) (a jh jl pos : ℕ → ℕ) (hown : OwnAs g X g' X')
    (hk : k < X.nCell)  (hW : 2 ^ fBitsX X' ∣ X'.width DF)
    (hv : ∀ b < 2 ^ v, gT (Src.num cs v b) → gU (Src.num rs v b) →
      jl (Src.num cs v b) < 2 ^ fBitsX X' ∧
      pos (Src.num cs v b) < DF.T ∧
      a (Src.num rs v b) < X.cnt DF ∧
      2 ^ fBitsX X' * jh (Src.num rs v b) + 2 ^ fBitsX X' ≤ X.width DF)
    (hSh : ∀ p : Cb.Place, IsFF g p → p.2.1 < R p.1 ∧ p.2.2 < C p.1) :
    SepB R C v
      (rowF (2 * g') cs rs (fun t => gT t ∧ FFSeg.OFF DF X' % 2 ^ fBitsX X' + jl t < 2 ^ fBitsX X')
        (fun t => FFSeg.OFF DF X' % 2 ^ fBitsX X' + jl t) pos DF.T (slotFF X'.mx) (nPartX X'))
      fun b A =>
        if (gT (Src.num cs v b) ∧
              FFSeg.OFF DF X' % 2 ^ fBitsX X' + jl (Src.num cs v b) < 2 ^ fBitsX X') ∧
            gU (Src.num rs v b) then
          cf (Src.num rs v b) *
            (cCell g ⟨X, k, a (Src.num rs v b),
                2 ^ fBitsX X' * jh (Src.num rs v b) + jl (Src.num cs v b),
                pos (Src.num cs v b)⟩ : CForm E).val A
        else 0 := by
  have hM : 0 < 2 ^ fBitsX X' := Nat.pos_of_ne_zero (by positivity)
  refine sepB_congr E R C v _ _ _ (fun b _ A => by rw [val_ownAs hown])
    (sepB_ffCore R C v g' X' k cs rs
      (fun t => gT t ∧ FFSeg.OFF DF X' % 2 ^ fBitsX X' + jl t < 2 ^ fBitsX X') gU cf
      (fun _ u => a u) (fun t u => 2 ^ fBitsX X' * jh u + jl t)
      (fun t => FFSeg.OFF DF X' % 2 ^ fBitsX X' + jl t) pos
      (fun u => (FFSeg.OFF DF X' + (k * X'.cnt DF + a u) * X'.width DF) / 2 ^ fBitsX X' + jh u)
      (fun b hb hT hU => ?_) (sh_ownAs hown R C hSh))
  obtain ⟨h1, h2, h3, h4⟩ := hv b hb hT.1 hU
  refine ⟨⟨hown.nCell ▸ hk, hown.cnt ▸ h3, (by
    show 2 ^ fBitsX X' * jh (Src.num rs v b) + jl (Src.num cs v b) < X'.width DF
    rw [hown.width]
    omega), h2⟩, ?_⟩
  · show FFSeg.feat DF X' k (a (Src.num rs v b))
            (2 ^ fBitsX X' * jh (Src.num rs v b) + jl (Src.num cs v b)) % 2 ^ fBitsX X' = _ ∧
      FFSeg.feat DF X' k (a (Src.num rs v b))
            (2 ^ fBitsX X' * jh (Src.num rs v b) + jl (Src.num cs v b)) / 2 ^ fBitsX X' = _
    obtain ⟨s1, s2⟩ := feat_split (2 ^ fBitsX X')
      (FFSeg.OFF DF X' + (k * X'.cnt DF + a (Src.num rs v b)) * X'.width DF) (jh (Src.num rs v b))
      (jl (Src.num cs v b)) hM
    rw [feat_eq]
    rw [s1, s2, base_mod X' k _ _ hW, Nat.mod_eq_of_lt hT.2, Nat.div_eq_of_lt hT.2]
    exact ⟨rfl, rfl⟩

theorem sepK_cValLo (R C : ℕ → ℕ) (v g g' : ℕ) (X X' : FFSeg.Arr) (cs rs : List Src)
    (gT gU : ℕ → Prop) [DecidablePred gT] [DecidablePred gU] (cf : ℕ → E) (a jh jl pos : ℕ → ℕ)
    (hown : OwnAs g X g' X')  (hW : 2 ^ fBitsX X' ∣ X'.width DF)
    (hv : ∀ b < 2 ^ v, gT (Src.num cs v b) → gU (Src.num rs v b) →
      jl (Src.num cs v b) < 2 ^ fBitsX X' ∧
      pos (Src.num cs v b) < DF.T ∧
      a (Src.num rs v b) < X.cnt DF ∧
      2 ^ fBitsX X' * jh (Src.num rs v b) + 2 ^ fBitsX X' ≤ X.width DF)
    (hSh : ∀ p : Cb.Place, IsFF g p → p.2.1 < R p.1 ∧ p.2.2 < C p.1) :
    SepK R C v
      (rowF (2 * g') cs rs (fun t => gT t ∧ FFSeg.OFF DF X' % 2 ^ fBitsX X' + jl t < 2 ^ fBitsX X')
        (fun t => FFSeg.OFF DF X' % 2 ^ fBitsX X' + jl t) pos DF.T (slotFF X'.mx) (nPartX X'))
      fun b A =>
        if (gT (Src.num cs v b) ∧
              FFSeg.OFF DF X' % 2 ^ fBitsX X' + jl (Src.num cs v b) < 2 ^ fBitsX X') ∧
            gU (Src.num rs v b) then
          cf (Src.num rs v b) *
            (cVal g X (a (Src.num rs v b))
              (2 ^ fBitsX X' * jh (Src.num rs v b) + jl (Src.num cs v b))
              (pos (Src.num cs v b)) : CForm E).val A
        else 0 := by
  refine sepK_congr E R C v _ _ _ (fun b _ A => ?_)
    (sepK_add E R C v _ _ _
      (sepK_sum E R C v X.nCell _
        (fun k b A =>
          (256 : E) ^ k *
            (if (gT (Src.num cs v b) ∧
                    FFSeg.OFF DF X' % 2 ^ fBitsX X' + jl (Src.num cs v b) < 2 ^ fBitsX X') ∧
                  gU (Src.num rs v b) then
                cf (Src.num rs v b) *
                  (cCell g ⟨X, k, a (Src.num rs v b),
                      2 ^ fBitsX X' * jh (Src.num rs v b) + jl (Src.num cs v b),
                      pos (Src.num cs v b)⟩ : CForm E).val A
              else 0)) fun k hk =>
                sepK_smul E R C v _ ((256 : E) ^ k) _
                  (sepK_ofB E R C v _ _
                    (sepB_cCellLo R C v g g' X X' cs rs gT gU cf k a jh jl pos hown hk hW hv hSh)))
      (sepK_const E R C v _ fun b =>
        if (gT (Src.num cs v b) ∧
              FFSeg.OFF DF X' % 2 ^ fBitsX X' + jl (Src.num cs v b) < 2 ^ fBitsX X') ∧
            gU (Src.num rs v b) then
          cf (Src.num rs v b) * ((X.off : ℤ) : E)
        else 0))
  by_cases hg : (gT (Src.num cs v b) ∧
      FFSeg.OFF DF X' % 2 ^ fBitsX X' + jl (Src.num cs v b) < 2 ^ fBitsX X') ∧
    gU (Src.num rs v b)
  · simp only [if_pos hg, val_cVal, val_cCell, FFSeg.val]
    rw [mul_add, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  · simp only [if_neg hg, mul_zero, Finset.sum_const_zero, add_zero]

theorem sepB_cCellHi (R C : ℕ → ℕ) (v g g' : ℕ) (X X' : FFSeg.Arr)
    (cs rs : List Src) (gT gU : ℕ → Prop) [DecidablePred gT] [DecidablePred gU]
    (cf : ℕ → E) (k : ℕ) (a jh jl pos : ℕ → ℕ) (hown : OwnAs g X g' X')
    (hk : k < X.nCell)  (hW : 2 ^ fBitsX X' ∣ X'.width DF)
    (hv : ∀ b < 2 ^ v, gT (Src.num cs v b) → gU (Src.num rs v b) →
      jl (Src.num cs v b) < 2 ^ fBitsX X' ∧
      pos (Src.num cs v b) < DF.T ∧
      a (Src.num rs v b) < X.cnt DF ∧
      2 ^ fBitsX X' * jh (Src.num rs v b) + 2 ^ fBitsX X' ≤ X.width DF)
    (hSh : ∀ p : Cb.Place, IsFF g p → p.2.1 < R p.1 ∧ p.2.2 < C p.1) :
    SepB R C v
      (rowF (2 * g') cs rs (fun t => gT t ∧ 2 ^ fBitsX X' ≤ FFSeg.OFF DF X' % 2 ^ fBitsX X' + jl t)
        (fun t => FFSeg.OFF DF X' % 2 ^ fBitsX X' + jl t - 2 ^ fBitsX X') pos DF.T (slotFF X'.mx)
        (nPartX X')) fun b A =>
          if (gT (Src.num cs v b) ∧
                2 ^ fBitsX X' ≤ FFSeg.OFF DF X' % 2 ^ fBitsX X' + jl (Src.num cs v b)) ∧
              gU (Src.num rs v b) then
            cf (Src.num rs v b) *
              (cCell g ⟨X, k, a (Src.num rs v b),
                  2 ^ fBitsX X' * jh (Src.num rs v b) + jl (Src.num cs v b),
                  pos (Src.num cs v b)⟩ : CForm E).val A
          else 0 := by
  have hM : 0 < 2 ^ fBitsX X' := Nat.pos_of_ne_zero (by positivity)
  refine sepB_congr E R C v _ _ _ (fun b _ A => by rw [val_ownAs hown])
    (sepB_ffCore R C v g' X' k cs rs
      (fun t => gT t ∧ 2 ^ fBitsX X' ≤ FFSeg.OFF DF X' % 2 ^ fBitsX X' + jl t) gU cf
      (fun _ u => a u) (fun t u => 2 ^ fBitsX X' * jh u + jl t)
      (fun t => FFSeg.OFF DF X' % 2 ^ fBitsX X' + jl t - 2 ^ fBitsX X') pos
      (fun u => (FFSeg.OFF DF X' + (k * X'.cnt DF + a u) * X'.width DF) / 2 ^ fBitsX X' + jh u + 1)
      (fun b hb hT hU => ?_) (sh_ownAs hown R C hSh))
  obtain ⟨h1, h2, h3, h4⟩ := hv b hb hT.1 hU
  refine ⟨⟨hown.nCell ▸ hk, hown.cnt ▸ h3, (by
    show 2 ^ fBitsX X' * jh (Src.num rs v b) + jl (Src.num cs v b) < X'.width DF
    rw [hown.width]
    omega), h2⟩, ?_⟩
  · show FFSeg.feat DF X' k (a (Src.num rs v b))
            (2 ^ fBitsX X' * jh (Src.num rs v b) + jl (Src.num cs v b)) % 2 ^ fBitsX X' = _ ∧
      FFSeg.feat DF X' k (a (Src.num rs v b))
            (2 ^ fBitsX X' * jh (Src.num rs v b) + jl (Src.num cs v b)) / 2 ^ fBitsX X' = _
    obtain ⟨s1, s2⟩ := feat_split (2 ^ fBitsX X')
      (FFSeg.OFF DF X' + (k * X'.cnt DF + a (Src.num rs v b)) * X'.width DF) (jh (Src.num rs v b))
      (jl (Src.num cs v b)) hM
    rw [feat_eq]
    have hc : FFSeg.OFF DF X' % 2 ^ fBitsX X' < 2 ^ fBitsX X' := Nat.mod_lt _ hM
    have e : FFSeg.OFF DF X' % 2 ^ fBitsX X' + jl (Src.num cs v b) =
        (FFSeg.OFF DF X' % 2 ^ fBitsX X' + jl (Src.num cs v b) - 2 ^ fBitsX X') +
          2 ^ fBitsX X' * 1 := by omega
    have m1 : (FFSeg.OFF DF X' % 2 ^ fBitsX X' + jl (Src.num cs v b)) % 2 ^ fBitsX X' =
        FFSeg.OFF DF X' % 2 ^ fBitsX X' + jl (Src.num cs v b) - 2 ^ fBitsX X' := by
      rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      omega
    have d1 : (FFSeg.OFF DF X' % 2 ^ fBitsX X' + jl (Src.num cs v b)) / 2 ^ fBitsX X' = 1 := by
      rw [e, Nat.add_mul_div_left _ _ hM, Nat.div_eq_of_lt (by omega)]
    rw [s1, s2, base_mod X' k _ _ hW, m1, d1]
    exact ⟨rfl, rfl⟩

theorem sepK_cValHi (R C : ℕ → ℕ) (v g g' : ℕ) (X X' : FFSeg.Arr) (cs rs : List Src)
    (gT gU : ℕ → Prop) [DecidablePred gT] [DecidablePred gU] (cf : ℕ → E) (a jh jl pos : ℕ → ℕ)
    (hown : OwnAs g X g' X')  (hW : 2 ^ fBitsX X' ∣ X'.width DF)
    (hv : ∀ b < 2 ^ v, gT (Src.num cs v b) → gU (Src.num rs v b) →
      jl (Src.num cs v b) < 2 ^ fBitsX X' ∧
      pos (Src.num cs v b) < DF.T ∧
      a (Src.num rs v b) < X.cnt DF ∧
      2 ^ fBitsX X' * jh (Src.num rs v b) + 2 ^ fBitsX X' ≤ X.width DF)
    (hSh : ∀ p : Cb.Place, IsFF g p → p.2.1 < R p.1 ∧ p.2.2 < C p.1) :
    SepK R C v
      (rowF (2 * g') cs rs (fun t => gT t ∧ 2 ^ fBitsX X' ≤ FFSeg.OFF DF X' % 2 ^ fBitsX X' + jl t)
        (fun t => FFSeg.OFF DF X' % 2 ^ fBitsX X' + jl t - 2 ^ fBitsX X') pos DF.T (slotFF X'.mx)
        (nPartX X')) fun b A =>
          if (gT (Src.num cs v b) ∧
                2 ^ fBitsX X' ≤ FFSeg.OFF DF X' % 2 ^ fBitsX X' + jl (Src.num cs v b)) ∧
              gU (Src.num rs v b) then
            cf (Src.num rs v b) *
              (cVal g X (a (Src.num rs v b))
                (2 ^ fBitsX X' * jh (Src.num rs v b) + jl (Src.num cs v b))
                (pos (Src.num cs v b)) : CForm E).val A
          else 0 := by
  refine sepK_congr E R C v _ _ _ (fun b _ A => ?_)
    (sepK_add E R C v _ _ _
      (sepK_sum E R C v X.nCell _
        (fun k b A =>
          (256 : E) ^ k *
            (if (gT (Src.num cs v b) ∧
                    2 ^ fBitsX X' ≤ FFSeg.OFF DF X' % 2 ^ fBitsX X' + jl (Src.num cs v b)) ∧
                  gU (Src.num rs v b) then
                cf (Src.num rs v b) *
                  (cCell g ⟨X, k, a (Src.num rs v b),
                      2 ^ fBitsX X' * jh (Src.num rs v b) + jl (Src.num cs v b),
                      pos (Src.num cs v b)⟩ : CForm E).val A
              else 0)) fun k hk =>
                sepK_smul E R C v _ ((256 : E) ^ k) _
                  (sepK_ofB E R C v _ _
                    (sepB_cCellHi R C v g g' X X' cs rs gT gU cf k a jh jl pos hown hk hW hv hSh)))
      (sepK_const E R C v _ fun b =>
        if (gT (Src.num cs v b) ∧
              2 ^ fBitsX X' ≤ FFSeg.OFF DF X' % 2 ^ fBitsX X' + jl (Src.num cs v b)) ∧
            gU (Src.num rs v b) then
          cf (Src.num rs v b) * ((X.off : ℤ) : E)
        else 0))
  by_cases hg : (gT (Src.num cs v b) ∧
      2 ^ fBitsX X' ≤ FFSeg.OFF DF X' % 2 ^ fBitsX X' + jl (Src.num cs v b)) ∧
    gU (Src.num rs v b)
  · simp only [if_pos hg, val_cVal, val_cCell, FFSeg.val]
    rw [mul_add, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  · simp only [if_neg hg, mul_zero, Finset.sum_const_zero, add_zero]

theorem sepB_cCellAny (R C : ℕ → ℕ) (v g g' : ℕ) (X X' : FFSeg.Arr) (cs rs : List Src)
    (gT gU : ℕ → Prop) [DecidablePred gT] [DecidablePred gU] (cf : ℕ → E) (k : ℕ) (a j pos : ℕ → ℕ)
    (hown : OwnAs g X g' X') (hk : k < X.nCell)
    (hv : ∀ b < 2 ^ v, gT (Src.num cs v b) → gU (Src.num rs v b) →
      pos (Src.num cs v b) < DF.T ∧ a (Src.num rs v b) < X.cnt DF ∧ j (Src.num rs v b) < X.width DF)
    (hSh : ∀ p : Cb.Place, IsFF g p → p.2.1 < R p.1 ∧ p.2.2 < C p.1) :
    SepB R C v (rowAny (2 * g') cs rs gT pos (fBitsX X') DF.T (slotFF X'.mx) (nPartX X')) fun b A =>
      if gT (Src.num cs v b) ∧ gU (Src.num rs v b) then
        cf (Src.num rs v b) *
          (cCell g
            ⟨X, k, a (Src.num rs v b), j (Src.num rs v b), pos (Src.num cs v b)⟩ : CForm E).val A
      else 0 := by
  have hM : 0 < 2 ^ fBitsX X' := Nat.pos_of_ne_zero (by positivity)
  have hq1 : ∀ x : ℕ, (x / 2 ^ fBitsX X' / colsFF * 2 ^ fBitsX X' + x % 2 ^ fBitsX X') /
        2 ^ fBitsX X' =
      x / 2 ^ fBitsX X' / colsFF := fun x => by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hM,
      Nat.div_eq_of_lt (Nat.mod_lt _ hM), Nat.zero_add]
  have hq2 : ∀ x : ℕ, (x / 2 ^ fBitsX X' / colsFF * 2 ^ fBitsX X' + x % 2 ^ fBitsX X') %
        2 ^ fBitsX X' =
      x % 2 ^ fBitsX X' := fun x => by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_mod]
  have hpl : ∀ u i : ℕ, plFF ⟨X', k, a u, j u, i⟩ =
      ((slotFF X'.mx +
              (FFSeg.feat DF X' k (a u) (j u) / 2 ^ fBitsX X' / colsFF * 2 ^ fBitsX X' +
                  FFSeg.feat DF X' k (a u) (j u) % 2 ^ fBitsX X') / 2 ^ fBitsX X') * hSlot +
          ((FFSeg.feat DF X' k (a u) (j u) / 2 ^ fBitsX X' / colsFF * 2 ^ fBitsX X' +
                FFSeg.feat DF X' k (a u) (j u) % 2 ^ fBitsX X') %
              2 ^ fBitsX X' * DF.T + i),
        FFSeg.feat DF X' k (a u) (j u) / 2 ^ fBitsX X' % colsFF) := fun u i => by
    rw [hq1, hq2]
    rfl
  refine sepB_congr E R C v _ _ _ (fun b _ A => ?_)
    (sepB_cell E R C v
      (rowAny (2 * g') cs rs gT pos (fBitsX X') DF.T (slotFF X'.mx) (nPartX X')) gU cf
      (fun u =>
        FFSeg.feat DF X' k (a u) (j u) / 2 ^ fBitsX X' / colsFF * 2 ^ fBitsX X' +
          FFSeg.feat DF X' k (a u) (j u) % 2 ^ fBitsX X')
      (fun u => FFSeg.feat DF X' k (a u) (j u) / 2 ^ fBitsX X' % colsFF)
      (fun b hb hT hU => ?_) List.nodup_range)
  · by_cases hg : gT (Src.num cs v b) ∧ gU (Src.num rs v b)
    · rw [if_pos hg, val_ownAs hown, hpl]
      exact (if_pos hg).symm
    · rw [if_neg hg]
      exact (if_neg hg).symm
  · obtain ⟨h2, h3, h4⟩ := hv b hb hT hU
    have hc : (⟨X', k, a (Src.num rs v b), j (Src.num rs v b),
        pos (Src.num cs v b)⟩ : FFSeg.Cell).Valid DF :=
      ⟨hown.nCell ▸ hk, hown.cnt ▸ h3, hown.width ▸ h4, h2⟩
    have hs := sh_ownAs hown R C hSh _ hc rfl
    rw [hpl] at hs
    refine ⟨List.mem_range.2 ?_, hs.1, hs.2⟩
    have h5 : FFSeg.feat DF X' k (a (Src.num rs v b)) (j (Src.num rs v b)) / 2 ^ fBitsX X' <
        FFSeg.nCol DF X'.mx :=
      (FFSeg.IndexFacts.addrRange DF FFSeg.ref_ok _ hc).2
    have h6 : FFSeg.feat DF X' k (a (Src.num rs v b)) (j (Src.num rs v b)) /
          2 ^ fBitsX X' / colsFF < nPartX X' :=
      Nat.div_lt_of_lt_mul (lt_of_lt_of_le h5 (nCol_le X'))
    have h7 := Nat.mod_lt (FFSeg.feat DF X' k (a (Src.num rs v b)) (j (Src.num rs v b))) hM
    calc
      FFSeg.feat DF X' k (a (Src.num rs v b)) (j (Src.num rs v b)) / 2 ^ fBitsX X' /
              colsFF * 2 ^ fBitsX X' +
            FFSeg.feat DF X' k (a (Src.num rs v b)) (j (Src.num rs v b)) % 2 ^ fBitsX X' <
          FFSeg.feat DF X' k (a (Src.num rs v b)) (j (Src.num rs v b)) / 2 ^ fBitsX X' /
              colsFF * 2 ^ fBitsX X' + 2 ^ fBitsX X' :=
        Nat.add_lt_add_left h7 _
      _ = (FFSeg.feat DF X' k (a (Src.num rs v b)) (j (Src.num rs v b)) / 2 ^ fBitsX X' / colsFF +
              1) *
            2 ^ fBitsX X' := by ring
      _ ≤ nPartX X' * 2 ^ fBitsX X' := Nat.mul_le_mul_right _ h6

theorem sepK_cValAny (R C : ℕ → ℕ) (v g g' : ℕ) (X X' : FFSeg.Arr) (cs rs : List Src)
    (gT gU : ℕ → Prop) [DecidablePred gT] [DecidablePred gU] (cf : ℕ → E)
    (a j pos : ℕ → ℕ) (hown : OwnAs g X g' X')
    (hv : ∀ b < 2 ^ v, gT (Src.num cs v b) → gU (Src.num rs v b) →
      pos (Src.num cs v b) < DF.T ∧ a (Src.num rs v b) < X.cnt DF ∧ j (Src.num rs v b) < X.width DF)
    (hSh : ∀ p : Cb.Place, IsFF g p → p.2.1 < R p.1 ∧ p.2.2 < C p.1) :
    SepK R C v (rowAny (2 * g') cs rs gT pos (fBitsX X') DF.T (slotFF X'.mx) (nPartX X')) fun b A =>
      if gT (Src.num cs v b) ∧ gU (Src.num rs v b) then
        cf (Src.num rs v b) *
          (cVal g X (a (Src.num rs v b)) (j (Src.num rs v b))
            (pos (Src.num cs v b)) : CForm E).val A
      else 0 := by
  refine sepK_congr E R C v _ _ _ (fun b _ A => ?_)
    (sepK_add E R C v _ _ _
      (sepK_sum E R C v X.nCell _
        (fun k b A =>
          (256 : E) ^ k *
            (if gT (Src.num cs v b) ∧ gU (Src.num rs v b) then
                cf (Src.num rs v b) *
                  (cCell g ⟨X, k, a (Src.num rs v b), j (Src.num rs v b),
                      pos (Src.num cs v b)⟩ : CForm E).val A
              else 0)) fun k hk =>
                sepK_smul E R C v _ ((256 : E) ^ k) _
                  (sepK_ofB E R C v _ _
                    (sepB_cCellAny R C v g g' X X' cs rs gT gU cf k a j pos hown hk hv hSh)))
      (sepK_const E R C v _ fun b =>
        if gT (Src.num cs v b) ∧ gU (Src.num rs v b) then cf (Src.num rs v b) * ((X.off : ℤ) : E)
        else 0))
  by_cases hg : gT (Src.num cs v b) ∧ gU (Src.num rs v b)
  · simp only [if_pos hg, val_cVal, val_cCell, FFSeg.val]
    rw [mul_add, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  · simp only [if_neg hg, mul_zero, Finset.sum_const_zero, add_zero]

/-- The numbers of blocks. -/
theorem rowF_len (seg : ℕ) (cs rs : List Src) (gT : ℕ → Prop) [DecidablePred gT]
    (rd pos : ℕ → ℕ) (T slot Q : ℕ) :
    (rowF seg cs rs gT rd pos T slot Q).L.length = Q :=
  List.length_range
theorem rowAny_len (seg : ℕ) (cs rs : List Src) (gT : ℕ → Prop) [DecidablePred gT]
    (pos : ℕ → ℕ) (f T slot Q : ℕ) :
    (rowAny seg cs rs gT pos f T slot Q).L.length = Q * 2 ^ f :=
  List.length_range
theorem rowF_nodup (seg : ℕ) (cs rs : List Src) (gT : ℕ → Prop) [DecidablePred gT]
    (rd pos : ℕ → ℕ) (T slot Q : ℕ) :
    (rowF seg cs rs gT rd pos T slot Q).L.Nodup := List.nodup_range
theorem rowAny_nodup (seg : ℕ) (cs rs : List Src) (gT : ℕ → Prop) [DecidablePred gT]
    (pos : ℕ → ℕ) (f T slot Q : ℕ) :
    (rowAny seg cs rs gT pos f T slot Q).L.Nodup := List.nodup_range

end Cm.TR
