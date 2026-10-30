-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetReadBitsFld.lean: the fields of a vertex as numbers of sources of bits; and the base rule
of "separable" (Cm/TargetReadBits.lean) for a cell whose place is given by a feature and a position,
in a matrix that is stacked in parts of a width that need be no power of two.

Separable with at most n pieces in the shapes R, C (the numbers of rows and columns of each
segment's matrix), of a function F of a vertex b < 2^v of a cube and of matrices A: at every vertex
b and for all A the value F b A is a constant k b plus at most n pieces, the same at all vertices; a
piece is Σ_{r < R seg, y < C seg} α t r · β u y · A seg r y: one segment, a table on rows times a
table on columns, t and u the numbers that two lists cs, rs of sources of bits form at b, which
together name no variable twice and none outside the cube (`Sep`, `SepV`, `SPiece`,
Cm/TargetReadBits.lean).

Definitions and statements (in `Cm.TR.Spec`: `fld_num` to `flds_two`, `sep_cases`, `sep_feat0`,
`sep_feat`, `sep_featAny`); the proofs are in Cm/TargetReadBitsFldProofs.lean. Generic: any field;
no model's sizes, but for the height 65,536 of a slot (`hSlot`, Cm/SegLayout.lean), which `stack`
has. The three rules on one cell are said of
m cells in Cm/TargetReadBitsFldBlk.lean.

Why: a model's cell atoms read cells at places whose arguments are fields of the vertex b (b / 2^o %
2^w). The calculus of Cm/TargetReadBits.lean speaks of numbers of lists of sources. Part 1 joins the
two. Part 2 is the one kind of place of the feed-forward segments and the head: feature φ, position
i ↦ row (φ mod 2^f) · T + i, column φ / 2^f (`featAt`, Inst/Model/FF/Index.lean), then stacked:
column c lies in part c / W (`stack`, Cm/SegLayout.lean).

Part 1:
  `Spec.fld_num`: o + w ≤ v ⇒ the number of fldS v o w at the vertex b is fld o w b (for every b).
  `Spec.flds_num`: FldFits v l ⇒ the number of fldsS v l at b is fldsN l b.
  `Spec.flds_ok`: FldFits v (l ++ l'), FldApart (l ++ l') ⇒ Src.OK (fldsS v l ++ fldsS v l') v: the
    premise of the base rule for row fields l and column fields l'.
Part 2:
  The cell: t the number of the row sources cs, u of the column sources rs, Src.OK (cs ++ rs) v; the
    feature φ := c + 2^f · jh u + jl t (c any constant; jl t < 2^f: the low digits of the channel
    (`Cell`, Inst/Model/FF/Index.lean); jh u: its high digits, and all else that enters with a
    factor 2^f); the position pos t; the place stack W slot ((φ mod 2^f) · T + pos t) (φ / 2^f),
    which under the guards gT t, gU u lies in the shapes R, C (row below R seg, column below C seg);
    F b A := if gT t ∧ gU u then cf u · A seg (the place) else 0. All premises run only over the
    numbers t < 2^|cs|, u < 2^|rs|, as the base rule's do: so the premises can be met with a guard
    that always holds. Each premise on t alone stands under gT t, each on u alone under gU u.
  `Spec.sep_feat0`: 2^f ∣ c, the part (c / 2^f + jh u) / W < Q ⇒ at most Q pieces (row: jl t · T +
    pos t in the block slot + part; column: (c / 2^f + jh u) mod W).
  `Spec.sep_feat`: any c, (c / 2^f + jh u + 1) / W < Q ⇒ at most 2 · Q pieces: the carry of (c mod
    2^f) + jl t into the column is a guard on the row sources: one cell where there is no carry, one
    where there is.
  `Spec.sep_featAny`, the fall-back: the feature is any function φ u of the column sources, the
    position is read off the row sources; φ u / 2^f / W < Q ⇒ at most Q · 2^f pieces (the block
    number: the part and φ u mod 2^f). So, under these premises, no cell at (feature, position) is
    outside the calculus; low digits of the channel as row sources are the saving: 1 or 2 pieces a
    part in the place of 2^f.

Limits: this file does not say that a model's atoms have this form.
It says nothing on places of the look-up's bits (`addrB`,
Inst/Model/FF/Index.lean) and of the attention segments. It does not say that 2 · Q, or m · n
(`Spec.sep_cases`), pieces are needed.

Terms: lean/GLOSSARY.md.
-/
import Cm.TargetReadBits
import Cm.SegIdxRun
import Cm.SegLayout

set_option autoImplicit false

namespace Cm.TR

open Cb Blocks Finset

/-- The field of w bits whose lowest bit is bit o. -/
def fld (o w b : ℕ) : ℕ := b / 2 ^ o % 2 ^ w

/-- Its sources in a cube of v variables (variable 0 = most significant bit; `Src.run`,
Cm/SegIdxRun.lean). -/
def fldS (v o w : ℕ) : List Src := Src.run (v - o - w) w

/-- Several fields, one after the other: the sources. -/
def fldsS (v : ℕ) : List (ℕ × ℕ) → List Src
  | [] => []
  | p :: l => fldS v p.1 p.2 ++ fldsS v l

/-- The sum of the widths. -/
def fldsW : List (ℕ × ℕ) → ℕ
  | [] => 0
  | p :: l => p.2 + fldsW l

/-- Several fields: the number: the fields as digits, the first the most significant. -/
def fldsN : List (ℕ × ℕ) → ℕ → ℕ
  | [], _ => 0
  | p :: l, b => fld p.1 p.2 b * 2 ^ fldsW l + fldsN l b

/-- Every field lies below bit v. -/
def FldFits (v : ℕ) (l : List (ℕ × ℕ)) : Prop := ∀ p ∈ l, p.1 + p.2 ≤ v

/-- The fields are pairwise disjoint ranges of bits. -/
def FldApart (l : List (ℕ × ℕ)) : Prop := l.Pairwise fun p q => p.1 + p.2 ≤ q.1 ∨ q.1 + q.2 ≤ p.1

/-- The feature. -/
def featOf (c f : ℕ) (jl jh : ℕ → ℕ) (t u : ℕ) : ℕ := c + 2 ^ f * jh u + jl t

/-- The place of (feature, position) in a matrix that begins at a slot, stacked in parts of width
W. -/
def featPl (W slot f T φ i : ℕ) : ℕ × ℕ := Seg.stack W slot ((φ % 2 ^ f) * T + i) (φ / 2 ^ f)

namespace Spec

def fld_num : Prop := ∀ v o w b : ℕ, o + w ≤ v → Src.num (fldS v o w) v b = fld o w b

def flds_num : Prop :=
  ∀ (v : ℕ) (l : List (ℕ × ℕ)) (b : ℕ), FldFits v l → Src.num (fldsS v l) v b = fldsN l b

def flds_ok : Prop :=
  ∀ (v : ℕ) (l l' : List (ℕ × ℕ)),
    FldFits v (l ++ l') → FldApart (l ++ l') → Src.OK (fldsS v l ++ fldsS v l') v

def flds_two : Prop :=
  ∀ o w o' w' b : ℕ,
    fldsN [(o, w), (o', w')] b = fld o w b * 2 ^ w' + fld o' w' b ∧
    fldsN [(o, w), (o', w')] b / 2 ^ w' = fld o w b ∧
    fldsN [(o, w), (o', w')] b % 2 ^ w' = fld o' w' b

/-- States: if h b < m at every vertex and each function "F where h b = a, else 0" is separable with
at most n pieces, F is separable with at most m · n pieces. The use: a field that row and column
both read. -/
def sep_cases : Prop :=
  ∀ (E : Type) [Field E] (R C : ℕ → ℕ) (v n m : ℕ) (h : ℕ → ℕ) (F : ℕ → (ℕ → ℕ → ℕ → E) → E),
    (∀ b < 2 ^ v, h b < m) →
    (∀ a < m, SepV R C v n fun b A => if h b = a then F b A else 0) → SepV R C v (m * n) F

/-- The cell at (feature, position): the offset is a multiple of 2^f. -/
def sep_feat0 : Prop :=
  ∀ (E : Type) [Field E] (R C : ℕ → ℕ) (v seg Q : ℕ) (cs rs : List Src) (gT gU : ℕ → Prop)
      [DecidablePred gT] [DecidablePred gU] (cf : ℕ → E) (jl pos jh : ℕ → ℕ) (c f T W slot : ℕ),
    Src.OK (cs ++ rs) v → 2 ^ f ∣ c → (∀ t < 2 ^ cs.length, gT t → jl t < 2 ^ f) →
    (∀ u < 2 ^ rs.length, gU u → (c / 2 ^ f + jh u) / W < Q) →
    (∀ t < 2 ^ cs.length, ∀ u < 2 ^ rs.length, gT t → gU u →
      (featPl W slot f T (featOf c f jl jh t u) (pos t)).1 < R seg ∧
      (featPl W slot f T (featOf c f jl jh t u) (pos t)).2 < C seg) →
    SepV R C v Q fun b A => if gT (Src.num cs v b) ∧ gU (Src.num rs v b) then
      cf (Src.num rs v b) *
        A seg (featPl W slot f T (featOf c f jl jh (Src.num cs v b) (Src.num rs v b))
            (pos (Src.num cs v b))).1
          (featPl W slot f T (featOf c f jl jh (Src.num cs v b) (Src.num rs v b))
            (pos (Src.num cs v b))).2
      else 0

/-- The cell at (feature, position): any offset. -/
def sep_feat : Prop :=
  ∀ (E : Type) [Field E] (R C : ℕ → ℕ) (v seg Q : ℕ) (cs rs : List Src) (gT gU : ℕ → Prop)
      [DecidablePred gT] [DecidablePred gU] (cf : ℕ → E) (jl pos jh : ℕ → ℕ) (c f T W slot : ℕ),
    Src.OK (cs ++ rs) v → (∀ t < 2 ^ cs.length, gT t → jl t < 2 ^ f) →
    (∀ u < 2 ^ rs.length, gU u → (c / 2 ^ f + jh u + 1) / W < Q) →
    (∀ t < 2 ^ cs.length, ∀ u < 2 ^ rs.length, gT t → gU u →
      (featPl W slot f T (featOf c f jl jh t u) (pos t)).1 < R seg ∧
      (featPl W slot f T (featOf c f jl jh t u) (pos t)).2 < C seg) →
    SepV R C v (2 * Q) fun b A => if gT (Src.num cs v b) ∧ gU (Src.num rs v b) then
      cf (Src.num rs v b) *
        A seg (featPl W slot f T (featOf c f jl jh (Src.num cs v b) (Src.num rs v b))
            (pos (Src.num cs v b))).1
          (featPl W slot f T (featOf c f jl jh (Src.num cs v b) (Src.num rs v b))
            (pos (Src.num cs v b))).2
      else 0

/-- The fall-back: the feature is any function of the column sources. -/
def sep_featAny : Prop :=
  ∀ (E : Type) [Field E] (R C : ℕ → ℕ) (v seg Q : ℕ) (cs rs : List Src) (gT gU : ℕ → Prop)
      [DecidablePred gT] [DecidablePred gU] (cf : ℕ → E) (pos φ : ℕ → ℕ) (f T W slot : ℕ),
    Src.OK (cs ++ rs) v → (∀ u < 2 ^ rs.length, gU u → φ u / 2 ^ f / W < Q) →
    (∀ t < 2 ^ cs.length, ∀ u < 2 ^ rs.length, gT t → gU u →
      (featPl W slot f T (φ u) (pos t)).1 < R seg ∧ (featPl W slot f T (φ u) (pos t)).2 < C seg) →
    SepV R C v (Q * 2 ^ f) fun b A => if gT (Src.num cs v b) ∧ gU (Src.num rs v b) then
      cf (Src.num rs v b) *
        A seg (featPl W slot f T (φ (Src.num rs v b)) (pos (Src.num cs v b))).1
          (featPl W slot f T (φ (Src.num rs v b)) (pos (Src.num cs v b))).2
      else 0

end Spec

end Cm.TR
