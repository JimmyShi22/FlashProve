-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBldSwOrd.lean: book-keeping for one step of the proximity test, the code switch from one
fold into the next: at which coordinate of the new code's message each entry of the old message and
randomness is, and which vertex of a cube each coordinate and each batched row gets.

Definitions and statements; the proofs are in Cb/Ld/LdBldSwOrdProofs.lean. Generic: any finite
field, any two folds whose coordinates are numbered. Nothing assumed beyond the hypotheses of the
statements and whatever the arguments hold as proofs; no place, corner or row's number is taken by
choice (`pZo`, `swP` are noncomputable through `swZo`, Cb/Ld/LdBldSw.lean). The parts of a switch
and equality weights are told in the head of Cb/Ld/LdBldSw.lean.

Places can come from an enumeration by choice (`swPlaceN`, Cb/Ld/LdBldSw.lean). Here they are the
ones that a write-up of ours that is not in this repository (lean/CREDITS.md) fixes (by reading):
  the folded main message fills the next stage's main rows; the next mask rows hold, in this order:
    the folded carried mask's message, the folded fresh mask's message, the randomness of the three
    encodings, folded (main, carried mask, fresh mask), the uniform filler entries, and the pad at
    the last place of the last mask row;
  the sample's point has mv coordinates; a main entry at (row b, place c) has the corner
    (b, c, 0 .. 0, 0), a mask entry the corner (b, c, 0 .. 0, 1): the last coordinate tells the
    kind (for k + lc < mv: `corAt`);
  two conventions, once for all: a corner of a cube is read as a number with its first coordinate as
    the least significant bit; row variables come first.

Main names:
  `FoldNo Y`: a numbering of a fold's coordinates: numbers m, r (main row: message, randomness), m',
    r' (mask row), c (coordinates of a long symbol of the output code).
  `SwEqP N N' fl mv lc lz ts gb`: what the numbers of two consecutive stages have to meet, with k, h
    for `Y'.k`, `Y'.h` (the next fold's main rows stand on the cube of k variables, its mask rows on
    that of h: `SumPar`, Cb/Ld/LdSum.lean): N.m = 2^k N'.m (the next main rows are filled);
    (N.m' + N.m') + (N.r + (N.r' + N.r')) + (fl + 1) = 2^h N'.m' (the next mask rows, with fl filler
    entries and the pad); N'.m ≤ 2^lc, N'.m' ≤ 2^lz (lc, lz coordinates for a place in a row);
    k + lc < mv, h + lz < mv; 1 + (1 + ts N.c) ≤ 2^gb (the batching's rows); ts, gb: the rows of
    `sw`, `swZb` in the head of Cb/Ld/LdBldSw.lean.
  `pPlace h`, `pCor`, `pNum`; `pZo h`, `pZb`; `swP h`, for `h : SwEqP N N' fl mv lc lz ts gb`: the
    placing, the corners, the rows' corners; the sample, the zero-evader, the data of the switch
    (the parts of Cb/Ld/LdBldSw.lean at these; for `swP` the fold's long positions are not empty).
  `Spec.bldSwP_ok`: for every such h, and long positions P of the fold Y that are not empty: the
    sample is a zero-evader on all vectors and private with a simulator, the evader evades; both of
    their forms. Nothing assumed beyond the hypotheses of its statement and whatever the arguments
    hold as proofs.
  `Spec.bldSwP_at`: for every such h, where `pPlace h` puts each entry.
  `Spec.bldSwP_rows`: the old claim has the number 0, the answer 1, the coordinate α of the symbol
    at the i-th location 2 + (i c + α's number); a row's corner is its number's, least significant
    bit first; for 1 + (1 + ts c) ≤ 2^gb different rows have different corners.

Why: by its definition (`SumPar.Zw`, Cb/Ld/LdSum.lean) the fresh mask has the carried mask's
coordinates (`Y.Zw.J` is `Y.Z.J`, `Y.Zw.Q` is `Y.Z.Q`): one numbering is used for both.

Limits: declared: which of the three vectors of randomness comes first (here: main, carried mask,
fresh mask: the order in which the fold lists its witnesses), and the order of the rows within the
locations of the batching, are ours.
What the head of Cb/Ld/LdBldSw.lean lists as not said is not said here either. This file does not
say that `SwEqP` can be met.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdBldSw
import Mathlib.Logic.Equiv.Fin.Basic
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Prob Blocks Alg Cb.Ood

namespace Bld

/-- two numbered types side by side: the first, then the second -/
def sumNo {A B : Type} {a b : ℕ} (eA : A ≃ Fin a) (eB : B ≃ Fin b) : A ⊕ B ≃ Fin (a + b) :=
  (Equiv.sumCongr eA eB).trans finSumFinEquiv

/-- the corner of a number: the first coordinate is the least significant bit -/
def bitsL (n c : ℕ) : Fin n → Bool := fun i => c.testBit i.val

/-- The cube and the numbers below 2^n; the first coordinate is the least significant bit. -/
def cubeL (n : ℕ) : (Fin n → Bool) ≃ Fin (2 ^ n) where
  toFun b := ⟨Nat.ofBits b, Nat.ofBits_lt_two_pow b⟩
  invFun c := bitsL n c.val
  left_inv b := funext fun i => Nat.testBit_ofBits_lt b i.val i.2
  right_inv c := Fin.ext ((Nat.ofBits_testBit c.val n).trans (Nat.mod_eq_of_lt c.2))

/-- Rows on a cube over a numbered type; row variables come first: (row b, place j) has the index
(number of b) + 2^k · (number of j). -/
def rowsNo (k : ℕ) {J : Type} {n : ℕ} (no : J ≃ Fin n) : (Fin k → Bool) × J ≃ Fin (2 ^ k * n) :=
  (Equiv.prodComm (Fin k → Bool) J).trans
    (((Equiv.prodCongr no (cubeL k)).trans finProdFinEquiv).trans
      (finCongr (Nat.mul_comm n (2 ^ k))))

/-- the one entry -/
def unitNo : Unit ≃ Fin 1 := Equiv.ofUnique Unit (Fin 1)

/-- The corner (b, c, 0 .. 0, kind), for k + lc < mv. -/
def corAt (mv k lc : ℕ) (b : Fin k → Bool) (c : Fin lc → Bool) (kind : Bool) :
    Fin mv → Bool := fun i =>
  if h₁ : i.val < k then b ⟨i.val, h₁⟩
  else if h₂ : i.val - k < lc then c ⟨i.val - k, h₂⟩
  else (decide (i.val + 1 = mv) && kind)

/-- A numbering of a fold's coordinates. -/
structure FoldNo {E P : Type} [Field E] (Y : SumPar E P) where
  m   : ℕ
  r   : ℕ
  m'  : ℕ
  r'  : ℕ
  c   : ℕ
  cJ  : Y.C.J ≃ Fin m
  cQ  : Y.C.Q ≃ Fin r
  zJ  : Y.Z.J ≃ Fin m'
  zQ  : Y.Z.Q ≃ Fin r'
  aa  : Y.Cout.Aa ≃ Fin c

variable {E P P' : Type} [Field E] {Y : SumPar E P} {Y' : SumPar E P'}

/-- What the numbers of two consecutive stages have to meet. -/
structure SwEqP (N : FoldNo Y) (N' : FoldNo Y') (fl mv lc lz ts gb : ℕ) : Prop where
  main : N.m = 2 ^ Y'.k * N'.m
  rest : (N.m' + N.m') + (N.r + (N.r' + N.r')) + (fl + 1) = 2 ^ Y'.h * N'.m'
  bC   : N'.m ≤ 2 ^ lc
  bZ   : N'.m' ≤ 2 ^ lz
  vC   : Y'.k + lc < mv
  vZ   : Y'.h + lz < mv
  rows : 1 + (1 + ts * N.c) ≤ 2 ^ gb

variable {N : FoldNo Y} {N' : FoldNo Y'} {fl mv lc lz ts gb : ℕ}

/-- what goes into the next mask rows, numbered in its order -/
def restNo (N : FoldNo Y) (fl : ℕ) :
    ((Y.Z.J ⊕ Y.Zw.J) ⊕ Y.Cout.Q) ⊕ (Fin fl ⊕ Unit) ≃
      Fin ((N.m' + N.m') + (N.r + (N.r' + N.r')) + (fl + 1)) :=
  sumNo (sumNo (sumNo N.zJ N.zJ) (sumNo N.cQ (sumNo N.zQ N.zQ)))
    (sumNo (Equiv.refl (Fin fl)) unitNo)

/-- The placing. -/
def pPlace (h : SwEqP N N' fl mv lc lz ts gb) :
    (Y.Cout.J ⊕ Y.Cout.Q) ⊕ (Fin fl ⊕ Unit) ≃ Y'.Cin.J :=
  swPlace (N.cJ.trans ((finCongr h.main).trans (rowsNo Y'.k N'.cJ).symm))
    ((restNo N fl).trans ((finCongr h.rest).trans (rowsNo Y'.h N'.zJ).symm))

/-- The corners. -/
def pCor (N' : FoldNo Y') (mv lc lz : ℕ) : Y'.Cin.J → Fin mv → Bool
  | .inl x => corAt mv Y'.k lc x.1 (bitsL lc (N'.cJ x.2).val) false
  | .inr x => corAt mv Y'.h lz x.1 (bitsL lz (N'.zJ x.2).val) true

/-- the batching's rows, numbered in their order -/
def rowNo (N : FoldNo Y) (ts : ℕ) : LdRow Unit ts Y.Cout.Aa ≃ Fin (1 + (1 + ts * N.c)) :=
  sumNo unitNo (sumNo unitNo ((Equiv.prodCongr (Equiv.refl (Fin ts)) N.aa).trans finProdFinEquiv))

/-- The rows' corners. -/
def pNum (N : FoldNo Y) (ts gb : ℕ) : LdRow Unit ts Y.Cout.Aa → Fin gb → Bool := fun x =>
  bitsL gb (rowNo N ts x).val

variable [Fintype E]

/-- The sample. -/
def pZo (h : SwEqP N N' fl mv lc lz ts gb) :
    Sample E ((Y.Cout.J ⊕ Y.Cout.Q) ⊕ (Fin fl ⊕ Unit)) :=
  swZo E (pPlace h) mv (pCor N' mv lc lz)

/-- The zero-evader. -/
def pZb (N : FoldNo Y) (ts gb : ℕ) : Evader E (LdRow Unit ts Y.Cout.Aa) := swZb E gb (pNum N ts gb)

/-- The switch from Y into Y'. -/
def swP [Fintype P] [Nonempty P]
    [Fintype Y.Cout.Aa] (h : SwEqP N N' fl mv lc lz ts gb) : LdSwD Y P' :=
  sw Y Y'.Cin (Fin fl) (pPlace h) mv (pCor N' mv lc lz) ts gb (pNum N ts gb)

end Bld

namespace Spec
open Cb.Bld

/-- For every `h : SwEqP N N' fl mv lc lz ts gb` and P not empty, the switch with every place named
meets what the records of a tower require of its two maps (`LdSw.Hyp`, Cb/Ld/LdTower.lean: okO, okB,
priv; the two forms: Cb/Gl/GlFinalEv.lean). -/
def bldSwP_ok : Prop :=
  ∀ (E P P' : Type) [Field E] [Fintype E] [Fintype P] [Nonempty P] (Y : SumPar E P)
      [Fintype Y.Cout.Aa] (Y' : SumPar E P') (N : FoldNo Y) (N' : FoldNo Y')
      (fl mv lc lz ts gb : ℕ) (h : SwEqP N N' fl mv lc lz ts gb),
    ((pZo h).OK ∧ (pZb (E := E) N ts gb).OK ∧ (pZo h).PrivateSim E ∧
      (pZo h).PadFillForm ∧ (pZb (E := E) N ts gb).Form) ∧
    ∀ e : ℕ, ((swP h).D e).Zo.OK ∧ ((swP h).D e).Zb.OK ∧ ((swP h).D e).Zo.PrivateSim E ∧
      ((swP h).D e).Zo.PadFillForm ∧ ((swP h).D e).Zb.Form

/-- Its numbers. -/
def bldSwP_nums : Prop :=
  ∀ (E P P' : Type) [Field E] [Fintype E] (Y : SumPar E P) (Y' : SumPar E P') (N : FoldNo Y)
      (N' : FoldNo Y') (fl mv lc lz ts gb : ℕ) (h : SwEqP N N' fl mv lc lz ts gb),
    (pZo h).err =
      max (mv * Fintype.card E ^ (mv - 1) * (Fintype.card E - 1)) (Fintype.card E ^ mv) ∧
    Fintype.card (pZo h).D = Fintype.card E ^ mv * (Fintype.card E - 1) ∧
    (pZb (E := E) N ts gb).err = gb * Fintype.card E ^ (gb - 1) ∧
    Fintype.card (pZb (E := E) N ts gb).D = Fintype.card E ^ gb

/-- Where each entry stands. -/
def bldSwP_at : Prop :=
  ∀ (E P P' : Type) [Field E] (Y : SumPar E P) (Y' : SumPar E P') (N : FoldNo Y) (N' : FoldNo Y')
      (fl mv lc lz ts gb : ℕ) (h : SwEqP N N' fl mv lc lz ts gb),
    (∀ j : Y.C.J,
      ∃ x, pPlace h (.inl (.inl (.inl j))) = .inl x ∧ (rowsNo Y'.k N'.cJ x).val = (N.cJ j).val) ∧
    (∀ j : Y.Z.J, ∃ x,
      pPlace h (.inl (.inl (.inr (.inl j)))) = .inr x ∧ (rowsNo Y'.h N'.zJ x).val = (N.zJ j).val) ∧
    (∀ j : Y.Zw.J, ∃ x,
      pPlace h (.inl (.inl (.inr (.inr j)))) = .inr x ∧
      (rowsNo Y'.h N'.zJ x).val = N.m' + (N.zJ j).val) ∧
    (∀ q : Y.C.Q, ∃ x,
      pPlace h (.inl (.inr (.inl q))) = .inr x ∧
      (rowsNo Y'.h N'.zJ x).val = (N.m' + N.m') + (N.cQ q).val) ∧
    (∀ q : Y.Z.Q, ∃ x,
      pPlace h (.inl (.inr (.inr (.inl q)))) = .inr x ∧
      (rowsNo Y'.h N'.zJ x).val = (N.m' + N.m') + (N.r + (N.zQ q).val)) ∧
    (∀ q : Y.Zw.Q, ∃ x,
      pPlace h (.inl (.inr (.inr (.inr q)))) = .inr x ∧
      (rowsNo Y'.h N'.zJ x).val = (N.m' + N.m') + (N.r + (N.r' + (N.zQ q).val))) ∧
    (∀ f : Fin fl, ∃ x,
      pPlace h (.inr (.inl f)) = .inr x ∧
      (rowsNo Y'.h N'.zJ x).val = (N.m' + N.m') + (N.r + (N.r' + N.r')) + f.val) ∧
    ∃ x, pPlace h (.inr (.inr ())) = .inr x ∧ (rowsNo Y'.h N'.zJ x).val + 1 = 2 ^ Y'.h * N'.m'

/-- The index of (row b, place j). -/
def bldSwP_rowsNo : Prop :=
  ∀ (k n : ℕ) (J : Type) (no : J ≃ Fin n) (b : Fin k → Bool) (j : J),
    (rowsNo k no (b, j)).val = Nat.ofBits b + 2 ^ k * (no j).val

/-- The batching's rows. -/
def bldSwP_rows : Prop :=
  ∀ (E P : Type) [Field E] (Y : SumPar E P) (N : FoldNo Y) (ts gb : ℕ),
    (rowNo N ts (.inl ())).val = 0 ∧
    (rowNo N ts (.inr (.inl ()))).val = 1 ∧
    (∀ (i : Fin ts) (α : Y.Cout.Aa),
      (rowNo N ts (.inr (.inr (i, α)))).val = 1 + (1 + ((N.aa α).val + N.c * i.val))) ∧
    (∀ x, pNum N ts gb x = bitsL gb (rowNo N ts x).val) ∧
    (1 + (1 + ts * N.c) ≤ 2 ^ gb → Function.Injective (pNum N ts gb))

/-- For `Y'.k + lc < mv` and `Y'.h + lz < mv`, the last coordinate of a corner tells the kind; the
first ones are the row. -/
def bldSwP_kind : Prop :=
  ∀ (E P' : Type) [Field E] (Y' : SumPar E P') (N' : FoldNo Y') (mv lc lz : ℕ) (hm : 0 < mv), Y'.k +
        lc < mv →
    Y'.h + lz < mv →
    (∀ x, pCor N' mv lc lz (.inl x) ⟨mv - 1, Nat.sub_lt hm Nat.one_pos⟩ = false) ∧
    (∀ x, pCor N' mv lc lz (.inr x) ⟨mv - 1, Nat.sub_lt hm Nat.one_pos⟩ = true) ∧
    (∀ x (i : Fin mv) (hi : i.val < Y'.k), pCor N' mv lc lz (.inl x) i = x.1 ⟨i.val, hi⟩) ∧
    (∀ x (i : Fin mv) (hi : i.val < Y'.h), pCor N' mv lc lz (.inr x) i = x.1 ⟨i.val, hi⟩)

def bldSwP_cor : Prop :=
  ∀ (E P' : Type) [Field E] (Y' : SumPar E P') (N' : FoldNo Y') (mv lc lz : ℕ), N'.m ≤ 2 ^ lc →
    N'.m' ≤ 2 ^ lz → Y'.k + lc < mv → Y'.h + lz < mv → Function.Injective (pCor N' mv lc lz)

end Spec
end Cb
