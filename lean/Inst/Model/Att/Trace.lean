-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Inst/Model/Att/Trace.lean: the trace of an attention segment (its witness) and the field relation
  on it.

  The file defines the cells, the arrays that they encode, the vectors of looked-up values (keys in
  Lean names) of the four calls, the identities, the field relation `RFraw`, the addresses of the
  cells in the matrices and the honest trace `hon`. Four theorems are only stated here, as
  definitions `Spec.*` of type Prop: three on the addresses, and `Spec.honest` (the honest trace
  meets the relation). From the relation to the program: `noWrapK`, Inst/Model/Bound/AttK.lean.
  * A cell has a name (`Raw`): the array, the number of the cell in a value, and the indices, as
    natural numbers. `Raw.Valid` says which names are cells. A trace is a function on names; the
    relation reads valid names only (at the reference sizes, for the looked-up values and the
    identities: `keyVec_agree`, `idnVal_agree`, Cm/SegAttAgree.lean; for every D: not proved in this
    library).
  * Every array, every function of the cells and every looked-up value is defined over an arbitrary
    commutative ring R, from t : Raw → R. With R = ℤ these are the integer versions, with R a field
    the protocol's.
  * The cells are in five matrices (`Mx`): as, ah, ao hold the segment's own cells, b the
    multiplicity bits of the lookup argument, qa the borrowed cells.
  * The four arrays qry, key, val, out are cells of the preceding feed-forward segment (`Raw.Own` is
    false for them): the segment borrows the matrix qa. They are cells of this file's trace all the
    same, because looked-up values and identities read them. In the trace of the whole reduction
    each of them occurs once, in the feed-forward segment.
  * A call is one vector of looked-up values with its table. Such a vector (`keyVec`) is defined at
    every natural number: in a piece by its formula, after the last piece by the padding value of
    the table. The field relation is about the values at the indices in pieces.
  * The shift sh is read from the table of scales, an instance argument `[scl : Scl]` (`Dim.sh`,
    Inst/Model/Att/Index.lean). `Lawful`: the scales are valid for attention. `refP l`: the
    reference sizes with the scales of layer l.
  * Entries of the regions M and D are numbers, as in Inst/Model/Att/Index.lean.
  * (PL5), (PL6), (PA1) to (PA7) are labels in the docstrings of Inst/Model/Program.lean; the other
    labels link docstrings.
  Proofs: `Spec.addrRange`, `Spec.addrInj`, `Spec.addrBFacts` in Inst/Model/Att/AddrFacts.lean; for
  valid scales, `Spec.honest` in Inst/Model/Att/Honest.lean.

  Notation:
    b, g, i, j, n, lam (Inst/Model/Att/Index.lean): natural numbers: pairs b = na λ + a of a layer λ
      of the segment and the number a of a query head among those of its key/value head (`Dim.nb`);
      key/value heads g (`Dim.nG`); positions i, j (`Dim.T`); channels n (`Dim.ch`); lam: a layer of
      the segment (`Dim.nl`);
    P, s (in `rowSum`; Inst/Model/Att/Index.lean): natural numbers: rows P of region M (`Dim.hP`); s
      also runs below nBlk (`Dim.nBlk`: blocks I, J of positions);
    r0, r1, fl, w0, w1 (`Raw.c ρ jj b x`): cell number jj < 5 of the entry x of the region, for the
      pair b: r0 - 128, r1 - 128, fl, w0 - 128, w1; `rm`: the remainder rm = r0 + 256 r1; `wtV`: the
      weight wt = w0 + 256 w1;
    qh, qh' (`Raw.qh`, `Raw.qh'`): cells; `qhV`, `qhV'` are these cells plus 128;
    χ (`key3W`): a natural number, the first part of the inner index (χ | g | i | n) of family 3W;
    θ (`Calls.callOf`): a natural number, the number of a tree; t, θ, π (`addrB`): natural numbers:
      the bit B[t, θ, π] of the multiplicities.
-/
import Inst.Model.Att.Index
import Inst.Model.Tables
import Inst.Model.Widened
import Blocks.Segment
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace Inst.Model.AttSeg

open Finset

/-- the two regions -/
inductive Reg
  | M
  | D
  deriving DecidableEq

/-- The names of the cells (without the multiplicity bits). k is the number of the cell in a value
of several cells. -/
inductive Raw
  /-- cell number jj < 5 of the entry x of the region, for the pair b: r0 - 128, r1 - 128, fl, w0 -
  128, w1 -/
  | c (ρ : Reg) (jj b x : ℕ)
  | mx (k b g i : ℕ)
  | den (k b g i : ℕ)
  /-- the bit of weight 2^k of the index at which the greatest score is attained -/
  | ib (k b g i : ℕ)
  | qh (b g i n : ℕ)
  | qh' (b g i n : ℕ)
  | qry (k b g i n : ℕ)
  | out (k b g i n : ℕ)
  | key (k lam g j n : ℕ)
  | val (k lam g j n : ℕ)
  deriving DecidableEq

variable (D : Dim)

/-- the number of bits of an entry of a region -/
def Dim.lReg : Reg → ℕ
  | .M => D.lM
  | .D => D.lD

/-- which names are cells -/
def Raw.Valid : Raw → Prop
  | .c ρ jj b x => jj < 5 ∧ b < D.nb ∧ x < 2 ^ D.lReg ρ
  | .mx k b g i => k < 4 ∧ b < D.nb ∧ g < D.nG ∧ i < D.T
  | .den k b g i => k < 4 ∧ b < D.nb ∧ g < D.nG ∧ i < D.T
  | .ib k b g i => k < D.lT ∧ b < D.nb ∧ g < D.nG ∧ i < D.T
  | .qh b g i n => b < D.nb ∧ g < D.nG ∧ i < D.T ∧ n < D.ch
  | .qh' b g i n => b < D.nb ∧ g < D.nG ∧ i < D.T ∧ n < D.ch
  | .qry k b g i n => k < 2 ∧ b < D.nb ∧ g < D.nG ∧ i < D.T ∧ n < D.ch
  | .out k b g i n => k < 2 ∧ b < D.nb ∧ g < D.nG ∧ i < D.T ∧ n < D.ch
  | .key k lam g j n => k < 2 ∧ lam < D.nl ∧ g < D.nG ∧ j < D.T ∧ n < D.ch
  | .val k lam g j n => k < 2 ∧ lam < D.nl ∧ g < D.nG ∧ j < D.T ∧ n < D.ch

instance (c : Raw) : Decidable (c.Valid D) := by
  cases c <;> unfold Raw.Valid <;> infer_instance

/-- the cells of the segment's own matrices as, ah, ao; the others are in the borrowed matrix qa -/
def Raw.Own : Raw → Bool
  | .qry .. => false
  | .out .. => false
  | .key .. => false
  | .val .. => false
  | _ => true

/-! ## Arrays: a value with n cells c_0, .., c_(n-1) is ∑ 256^k c_k plus the offset -/

section Arrays
variable [scl : Scl]
variable {R : Type} [CommRing R] (t : Raw → R)

def r0 (ρ : Reg) (b x : ℕ) : R := t (.c ρ 0 b x) + 128
def r1 (ρ : Reg) (b x : ℕ) : R := t (.c ρ 1 b x) + 128
def flV (ρ : Reg) (b x : ℕ) : R := t (.c ρ 2 b x)
def w0 (ρ : Reg) (b x : ℕ) : R := t (.c ρ 3 b x) + 128
def w1 (ρ : Reg) (b x : ℕ) : R := t (.c ρ 4 b x)
/-- the remainder rm = r0 + 256 r1 -/
def rm (ρ : Reg) (b x : ℕ) : R := r0 t ρ b x + 256 * r1 t ρ b x
/-- the weight wt = w0 + 256 w1 -/
def wtV (ρ : Reg) (b x : ℕ) : R := w0 t ρ b x + 256 * w1 t ρ b x
def mxV (b g i : ℕ) : R := ∑ k ∈ range 4, 256 ^ k * t (.mx k b g i)
def denV (b g i : ℕ) : R := ∑ k ∈ range 4, 256 ^ k * t (.den k b g i)
def ibV (k b g i : ℕ) : R := t (.ib k b g i)
def qhV (b g i n : ℕ) : R := t (.qh b g i n) + 128
def qhV' (b g i n : ℕ) : R := t (.qh' b g i n) + 128
def qryV (b g i n : ℕ) : R := ∑ k ∈ range 2, 256 ^ k * t (.qry k b g i n)
def outV (b g i n : ℕ) : R := ∑ k ∈ range 2, 256 ^ k * t (.out k b g i n)
def keyV (lam g j n : ℕ) : R := ∑ k ∈ range 2, 256 ^ k * t (.key k lam g j n)
def valV (lam g j n : ℕ) : R := ∑ k ∈ range 2, 256 ^ k * t (.val k lam g j n)

/-! ## Functions of the cells that are not sent -/

/-- sc_b[g, i, j] = ∑_n qry_b[g, i, n] key_λ[g, j, n] -/
def scV (b g i j : ℕ) : R := ∑ n ∈ range D.ch, qryV t b g i n * keyV t (D.lamOf b) g j n

/-- ∑ over the entries x of row (g, i), empty ones excluded, masked ones included, of wt_b(x)
G(j(x)) -/
def rowSum (G : ℕ → R) (b g i : ℕ) : R :=
  (∑ P ∈ range D.hP, ∑ s ∈ range (D.nBlk - 1), if D.rowBlk P s = i / D.B then
        ∑ j' ∈ range D.B, wtV t .M b (D.codeM g P s (i % D.B) j') * G (D.B * D.colBlk P s + j')
      else 0) +
    ∑ j' ∈ range D.B, wtV t .D b (D.codeD g (i / D.B) (i % D.B) j') * G (D.B * (i / D.B) + j')

/-- EF_b[g, i] = ∑_x wt_b(x) -/
def EF (b g i : ℕ) : R := rowSum D t (fun _ => 1) b g i
/-- AC_b[g, i, n] = ∑_x wt_b(x) val_λ[g, j(x), n] -/
def AC (b g i n : ℕ) : R := rowSum D t (fun j => valV t (D.lamOf b) g j n) b g i
/-- RE_b = 2 AC_b + den_b - 2 den_b out_b -/
def RE (b g i n : ℕ) : R := 2 * AC D t b g i n + denV t b g i - 2 * denV t b g i * outV t b g i n

/-- eq1(u, y) = u y + (1 - u)(1 - y) -/
def eq1 (u y : R) : R := u * y + (1 - u) * (1 - y)
/-- bit_k(j), the bit of weight 2^k -/
def bitR (R : Type) [CommRing R] (k j : ℕ) : R := if j.testBit k then 1 else 0

/-- sel_b[g, i, n] = ∑_j key_λ[g, j, n] ∏_k eq1(ib_(b,k)[g, i], bit_k(j)) -/
def sel (b g i n : ℕ) : R :=
  ∑ j ∈ range D.T, keyV t (D.lamOf b) g j n * ∏ k ∈ range D.lT, eq1 (ibV t k b g i) (bitR R k j)

/-- the cut-off C = 2^sh u0, the step st = 2^16 − 2^sh of the dead rows, at the shift and the live
rows of the segment (Inst/Model/Tables.lean) -/
abbrev Dim.cutC : ℤ := Inst.Model.cutC D.sh D.u0
@[inherit_doc Dim.cutC] abbrev Dim.stp : ℤ := Inst.Model.stp D.sh

/-- Om = 2 S_max + C -/
def Om : ℤ := 2 * Smax + D.cutC

/-- The extended gap: mx - sc; the constant C at an empty entry of M; Om is added at a masked entry
of D. -/
def gp : Reg → ℕ → ℕ → R
  | .M, b, x =>
    if D.EmptyM x then ((D.cutC : ℤ) : R)
    else mxV t b (D.mG x) (D.iM x) - scV D t b (D.mG x) (D.iM x) (D.jM x)
  | .D, b, x =>
    mxV t b (D.dG x) (D.iD x) - scV D t b (D.dG x) (D.iD x) (D.jD x) +
      if D.MaskedD x then ((Om D : ℤ) : R) else 0

/-! ## The looked-up values -/

/-- the looked-up value of families 1M, 1D, at an entry -/
def key1 (ρ : Reg) (b x : ℕ) : R := r0 t ρ b x + 2 ^ 20 * r1 t ρ b x + 2 ^ 40 * flV t ρ b x
/-- the looked-up value of families 2M, 2D, at an entry -/
def key2 (ρ : Reg) (b x : ℕ) : R :=
  gp D t ρ b x - rm t ρ b x + 2 ^ 32 * flV t ρ b x + 2 ^ 33 * wtV t ρ b x
/-- the looked-up value of family 3W, at (χ | g | i | n) -/
def key3W (χ b g i n : ℕ) : R :=
  if χ = 0 then RE D t b g i n - 2 ^ 16 * qhV t b g i n
  else 2 * denV t b g i - 1 - RE D t b g i n - 2 ^ 16 * qhV' t b g i n
/-- the looked-up value of family 3X, at (g | i): 2^(16 - lT) (i - ∑_k 2^k ib_k); at the reference
parameters the factor is 2^6. Meant for lT ≤ 16 (the subtraction is truncated). -/
def key3X (b g i : ℕ) : R := 2 ^ (16 - D.lT) * ((i : R) - ∑ k ∈ range D.lT, 2 ^ k * ibV t k b g i)
/-- the looked-up value of family 4, at (g | i | n) -/
def key4 (b g i n : ℕ) : R := qhV t b g i n + 2 ^ 20 * qhV' t b g i n

end Arrays

/-! ## The vectors of looked-up values of the four calls: pieces and padding -/

/-- the numbers of bits of the inner index of the pieces 3W (χ | g | i | n), 3X (g | i), 4 (g | i |
n) -/
def Dim.lW : ℕ := 1 + D.lg + D.lT + D.ln
def Dim.lX : ℕ := D.lg + D.lT
def Dim.l4 : ℕ := D.lg + D.lT + D.ln

/-- the tables of the four calls: τ1, τ2, τ3, τ4 -/
def lut [scl : Scl] (tb : Tables) : Fin 4 → Lut
  | 0 => tau1 D.sh
  | 1 => tau2 D.sh D.u0 tb
  | 2 => tau3
  | 3 => tau4

/-- how many indices of a call are in pieces -/
def Dim.used : Fin 4 → ℕ
  | 0 => D.nb * 2 ^ D.lM + D.nb * 2 ^ D.lD
  | 1 => D.nb * 2 ^ D.lM + D.nb * 2 ^ D.lD
  | 2 => D.nb * 2 ^ D.lW + D.nb * 2 ^ D.lX
  | 3 => D.nb * 2 ^ D.l4

section KeyVec
variable [scl : Scl]
variable {R : Type} [CommRing R] (tb : Tables) (t : Raw → R)

/-- a vector of two families of pieces, the first of nb pieces of 2^l keys, the second of nb pieces
of 2^l' keys, then the padding value -/
def twoFam (nb l l' : ℕ) (f f' : ℕ → ℕ → R) (pad : R) (X : ℕ) : R :=
  if X < nb * 2 ^ l then f (X / 2 ^ l) (X % 2 ^ l)
  else if X - nb * 2 ^ l < nb * 2 ^ l' then
    f' ((X - nb * 2 ^ l) / 2 ^ l') ((X - nb * 2 ^ l) % 2 ^ l')
  else pad

/-- The vector of looked-up values of call c, at every index. In each call the pieces come family by
family, and in a family in the order b = 0, 1, ... Call 4 has one family; its second "family" here
consists of padding values. -/
def keyVec : Fin 4 → ℕ → R
  | 0 => twoFam D.nb D.lM D.lD (key1 t .M) (key1 t .D) (((lut D tb 0).pad : ℤ) : R)
  | 1 => twoFam D.nb D.lM D.lD (key2 D t .M) (key2 D t .D) (((lut D tb 1).pad : ℤ) : R)
  | 2 =>
    twoFam D.nb D.lW D.lX
      (fun b y =>
        key3W D t (y / D.ch / D.T / D.nG) b (y / D.ch / D.T % D.nG) (y / D.ch % D.T) (y % D.ch))
      (fun b y => key3X D t b (y / D.T) (y % D.T)) (((lut D tb 2).pad : ℤ) : R)
  | 3 =>
    twoFam D.nb D.l4 0 (fun b y => key4 t b (y / D.ch / D.T) (y / D.ch % D.T) (y % D.ch))
      (fun _ _ => (((lut D tb 3).pad : ℤ) : R)) (((lut D tb 3).pad : ℤ) : R)

/-- the entries of a table, in R -/
def lutSet (L : Lut) : Set R := {v | ∃ ι : ℕ, ι < L.rows ∧ v = ((L.row ι : ℤ) : R)}

/-! ## The further identities -/

inductive Idn
  | at1 (k b g i : ℕ)
  | at2 (b g i : ℕ)
  | at3 (b g i : ℕ)

def Idn.Valid : Idn → Prop
  | .at1 k b g i => k < D.lT ∧ b < D.nb ∧ g < D.nG ∧ i < D.T
  | .at2 b g i => b < D.nb ∧ g < D.nG ∧ i < D.T
  | .at3 b g i => b < D.nb ∧ g < D.nG ∧ i < D.T

/-- the polynomial that has to vanish -/
def idnVal : Idn → R
  | .at1 k b g i => ibV t k b g i * (ibV t k b g i - 1)
  | .at2 b g i => mxV t b g i - ∑ n ∈ range D.ch, qryV t b g i n * sel D t b g i n
  | .at3 b g i => denV t b g i - EF D t b g i

end KeyVec

/-! ## The field relation -/

/-- a trace of integers, mapped into a ring -/
def castT {R : Type} [CommRing R] (t : Raw → ℤ) : Raw → R := fun c => ((t c : ℤ) : R)

/-- The field relation, for a function on all names: (1) every cell is below 2^18 in absolute value,
(2) every looked-up value in a piece is an entry of its table, (3) the identities hold; looked-up
values and identities are formed in F. This is the form in which the relation of the whole reduction
takes the conjunction over the segments. -/
def RFraw [scl : Scl] (tb : Tables) (F : Type) [CommRing F] (t : Raw → ℤ) : Prop :=
  (∀ c : Raw, c.Valid D → |t c| < 2 ^ 18) ∧
  (∀ (c : Fin 4) (X : ℕ),
    X < D.used c → keyVec D tb (castT t : Raw → F) c X ∈ lutSet (lut D tb c)) ∧
  ∀ j : Idn, j.Valid D → idnVal D (castT t : Raw → F) j = 0

/-- Own cells beside given borrowed cells. In the chain of all segments the cells of qa are given
when an attention segment begins, and "there is a trace" means: there are own cells. The relation
for given borrowed cells bor is `RFraw D tb F (join own bor)`. -/
def join (own bor : Raw → ℤ) : Raw → ℤ := fun c => if c.Own = true then own c else bor c

section Cast
variable [scl : Scl]
variable {R : Type} [CommRing R] (tb : Tables) (t : Raw → ℤ)

omit [scl : Scl] in
theorem bitR_cast (k j : ℕ) : ((bitR ℤ k j : ℤ) : R) = bitR R k j := by
  unfold bitR
  split_ifs <;> simp

omit [scl : Scl] in
/-- The identities commute with the map from the integers to a ring. -/
theorem idn_cast (j : Idn) : idnVal D (castT t : Raw → R) j = ((idnVal D t j : ℤ) : R) := by
  cases j
  · unfold idnVal ibV castT
    push_cast
    rfl
  · unfold idnVal mxV qryV sel keyV eq1 ibV castT
    push_cast
    simp only [bitR_cast]
  · unfold idnVal denV EF rowSum wtV w0 w1 castT
    push_cast
    rfl

/-- The looked-up values commute with the map from the integers to a ring. -/
theorem key_cast (X : ℕ) :
    ∀ c : Fin 4, keyVec D tb (castT t : Raw → R) c X = ((keyVec D tb t c X : ℤ) : R)
  | 0 => by
    unfold keyVec twoFam key1 r0 r1 flV castT
    push_cast
    norm_num
  | 1 => by
    unfold keyVec twoFam key2 gp scV rm wtV r0 r1 flV w0 w1 mxV qryV keyV castT
    push_cast
    norm_num
  | 2 => by
    unfold keyVec twoFam key3W key3X RE AC rowSum wtV w0 w1 denV outV valV qhV qhV' ibV castT
    dsimp only
    split_ifs <;> first | (push_cast; rfl) | (push_cast; ring1) | simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_sub, Int.cast_natCast, Int.cast_sum]
  | 3 => by
    unfold keyVec twoFam key4 qhV qhV' castT
    push_cast
    norm_num

omit [scl : Scl] in
theorem castT_int : (castT t : Raw → ℤ) = t := funext fun _ => Int.cast_id

/-- The relation over the integers gives the relation over every commutative ring. -/
theorem rfraw_of_int (F : Type) [CommRing F] (h : RFraw D tb ℤ t) : RFraw D tb F t := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, fun c X hX => ?_, fun j hj => ?_⟩
  · obtain ⟨ι, hι, he⟩ := h2 c X hX
    rw [castT_int] at he
    refine ⟨ι, hι, ?_⟩
    rw [key_cast, he]
    simp
  · have h3' := h3 j hj
    rw [castT_int] at h3'
    rw [idn_cast, h3', Int.cast_zero]

/-- If u0 < 2^16, the padding value of a table is one of its entries (rows 0, u0, 0, 0). -/
theorem pad_mem (hu : D.u0 < 2 ^ 16) :
    ∀ c : Fin 4, (((lut D tb c).pad : ℤ) : R) ∈ (lutSet (lut D tb c) : Set R)
  | 0 => ⟨0, by norm_num [lut, tau1], by simp [lut, tau1]⟩
  | 1 => ⟨D.u0, hu, by simp [lut, tau2, nd]⟩
  | 2 => ⟨0, by norm_num [lut, tau3, R16], by norm_num [lut, tau3, R16]⟩
  | 3 => ⟨0, by norm_num [lut, tau4], by norm_num [lut, tau4]⟩

end Cast

/-! ## A sum over the entries of a row, as one sum over the positions -/

section RowSum
variable [scl : Scl]
variable {R : Type} [CommRing R] (t : Raw → R)

/-- the weight at the entry for the pair of positions (i, j), j < B (⌊i/B⌋ + 1): an entry of M if j
is in an earlier block than i, of D if in the same -/
def wtIJ (b g i j : ℕ) : R :=
  if j / D.B < i / D.B then
    wtV t .M b (D.codeM g (D.slotP (i / D.B)) (D.slotS (i / D.B) (j / D.B)) (i % D.B) (j % D.B))
  else wtV t .D b (D.codeD g (i / D.B) (i % D.B) (j % D.B))

omit [scl : Scl] in
/-- For i < T, a sum over the entries of row (g, i) is a sum over the positions j < B (I + 1), I the
block of i; those with j > i belong to masked entries. -/
theorem rowSum_eq (G : ℕ → R) (b g : ℕ) {i : ℕ} (hi : i < D.T) :
    rowSum D t G b g i = ∑ j ∈ range (D.B * (i / D.B + 1)), wtIJ D t b g i j * G j := by
  have hI : i / D.B < D.nBlk := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hi)
  unfold rowSum
  rw [D.sum_slots2 hI fun P s =>
      ∑ j' ∈ range D.B, wtV t .M b (D.codeM g P s (i % D.B) j') * G (D.B * D.colBlk P s + j')]
  have hM : ∀ J ∈ range (i / D.B),
      (∑ j' ∈ range D.B,
          wtV t .M b (D.codeM g (D.slotP (i / D.B)) (D.slotS (i / D.B) J) (i % D.B) j') *
            G (D.B * D.colBlk (D.slotP (i / D.B)) (D.slotS (i / D.B) J) + j')) =
        ∑ j' ∈ range D.B,
          (if J < i / D.B then
                wtV t .M b (D.codeM g (D.slotP (i / D.B)) (D.slotS (i / D.B) J) (i % D.B) j')
              else wtV t .D b (D.codeD g (i / D.B) (i % D.B) j')) *
            G (D.B * J + j') := fun J hJ => by
    rw [(D.slot_of_blk (mem_range.mp hJ) hI).2.2.2]
    exact sum_congr rfl fun j' _ => by rw [if_pos (mem_range.mp hJ)]
  have hD : (∑ j' ∈ range D.B,
        wtV t .D b (D.codeD g (i / D.B) (i % D.B) j') * G (D.B * (i / D.B) + j')) =
      ∑ j' ∈ range D.B,
        (if i / D.B < i / D.B then
              wtV t .M b (D.codeM g (D.slotP (i / D.B)) (D.slotS (i / D.B) (i / D.B)) (i % D.B) j')
            else wtV t .D b (D.codeD g (i / D.B) (i % D.B) j')) *
          G (D.B * (i / D.B) + j') :=
    sum_congr rfl fun j' _ => by rw [if_neg (lt_irrefl _)]
  rw [sum_congr rfl hM, hD,
    ← sum_range_succ
      (fun J =>
        ∑ j' ∈ range D.B,
          (if J < i / D.B then
                wtV t .M b (D.codeM g (D.slotP (i / D.B)) (D.slotS (i / D.B) J) (i % D.B) j')
              else wtV t .D b (D.codeD g (i / D.B) (i % D.B) j')) *
            G (D.B * J + j')) (i / D.B),
    D.sum_blocks2 (fun J j' =>
      (if J < i / D.B then
            wtV t .M b (D.codeM g (D.slotP (i / D.B)) (D.slotS (i / D.B) J) (i % D.B) j')
          else wtV t .D b (D.codeD g (i / D.B) (i % D.B) j')) *
        G (D.B * J + j'))]
  refine sum_congr rfl fun j _ => ?_
  unfold wtIJ
  rw [Nat.div_add_mod]

end RowSum

/-! ## The trees of the main lookup argument -/

/-- The numbers of the main lookup argument: call c has 2^(a c) indices; a tree has 2^Dk looked-up
values; 2^sg tree numbers. -/
structure Calls where
  a : Fin 4 → ℕ
  Dk : ℕ
  sg : ℕ

/-- a_c = 27, 27, 26, 25; Dk = 25; sg = 4 -/
def Calls.ref : Calls := ⟨![27, 27, 26, 25], 25, 4⟩

namespace Calls
variable (C : Calls)

/-- the number of trees of a call, and its first tree -/
def trees (c : Fin 4) : ℕ := 2 ^ (C.a c - C.Dk)
def first : Fin 4 → ℕ
  | 0 => 0
  | 1 => C.trees 0
  | 2 => C.trees 0 + C.trees 1
  | 3 => C.trees 0 + C.trees 1 + C.trees 2
/-- N_T, the number of trees -/
def NT : ℕ := C.trees 0 + C.trees 1 + C.trees 2 + C.trees 3
/-- the call of a tree -/
def callOf (θ : ℕ) : Fin 4 :=
  if θ < C.first 1 then 0 else if θ < C.first 2 then 1 else if θ < C.first 3 then 2 else 3

/-- The numbers fit: the pieces of each call fit into it, a call consists of whole trees, the trees
fit into the tree numbers, and each call starts at a multiple of its number of trees (so that it has
a prefix); and the two conditions `ten` and `ex`. -/
structure OK [scl : Scl] (D : Dim) : Prop where
  fits : ∀ c, D.used c ≤ 2 ^ C.a c
  le : ∀ c, C.Dk ≤ C.a c
  nt : C.NT ≤ 2 ^ C.sg
  aligned : ∀ c, C.trees c ∣ C.first c
  /-- `PL.rangeOrd` (Blocks/Ext.lean), the order of the last layer of the product tree over the
  looked-up values, needs nine bits of the index in a tree below that layer's top bit -/
  ten : 10 ≤ C.Dk
  /-- the input shift of the exponential and the number of its live rows are valid
  (Inst/Model/Tables.lean) -/
  ex : ExpOK D.sh D.u0

/-- Under `C.OK D`, the padding row of τ2, the first row that is not live, is a row of the table -/
theorem OK.u0 [scl : Scl] {C : Calls} {D : Dim} (h : C.OK D) : D.u0 < 2 ^ 16 := by
  have h1 := h.ex.room
  have h2 : 0 < nd D.sh := Nat.succ_pos _
  omega

end Calls

/-- looked-up value number i of tree θ. (Under `C.OK D`, for a tree number θ ≥ N_T, which no
statement reads, this is a padding value of call 4.) -/
def forestKey [scl : Scl] {R : Type} [CommRing R] (C : Calls) (tb : Tables)
    (t : Raw → R) (θ i : ℕ) : R :=
  keyVec D tb t (C.callOf θ) ((θ - C.first (C.callOf θ)) * 2 ^ C.Dk + i)

/-- ϕ_θ: the number of padding positions of tree θ -/
def padCount (C : Calls) (θ : ℕ) : ℕ :=
  2 ^ C.Dk - min (2 ^ C.Dk) (D.used (C.callOf θ) - (θ - C.first (C.callOf θ)) * 2 ^ C.Dk)

/-! ## Addresses -/

/-- the cell matrices of the segment, in the order of the range proof -/
inductive Mx
  | as
  | ah
  | ao
  | b
  | qa
  deriving DecidableEq

/-- a column of ah holds 2^fh features (at the reference parameters 8); a column of ao and of qa
2^(ln - 1) (64) -/
structure Cols where
  fh : ℕ

def Cols.ref : Cols := ⟨3⟩

section Addr
variable (K : Cols)

/-- the number of query heads in all -/
def Dim.nH : ℕ := D.nG * D.na

/-- the number of bits of a row of a matrix. The matrix b has 2^(9 + 5) rows: the last nine bits of
a row of a table, and the bit plane. -/
def lRow : Mx → ℕ
  | .as => (D.lP + 1) + D.lB + D.lB
  | .ah => K.fh + D.lT
  | .ao => (D.ln - 1) + D.lT
  | .b => 14
  | .qa => (D.ln - 1) + D.lT

/-- feature φ at position i, in a matrix with 2^f features in a column: (row, column) -/
def featAt (f φ i : ℕ) : ℕ × ℕ := ((φ % 2 ^ f) * D.T + i, φ / 2 ^ f)

/-- an address A in the matrix as: (row, column) -/
def asAt (A : ℕ) : ℕ × ℕ := (A % 2 ^ lRow D K .as, A / 2 ^ lRow D K .as)

/-- The address of a cell: its matrix, row and column. -/
def addr : Raw → Mx × ℕ × ℕ
  | .c .M jj b x => (.as, asAt D K ((D.nb * jj + b) * 2 ^ D.lM + x))
  | .c .D jj b x => (.as, asAt D K (5 * D.nb * 2 ^ D.lM + (D.nb * jj + b) * 2 ^ D.lD + x))
  | .mx k b g i => (.ah, featAt D K.fh (D.nH * (D.nl * k + D.lamOf b) + D.head g b) i)
  | .den k b g i =>
    (.ah, featAt D K.fh (4 * D.nl * D.nH + D.nH * (D.nl * k + D.lamOf b) + D.head g b) i)
  | .ib k b g i =>
    (.ah, featAt D K.fh (8 * D.nl * D.nH + D.lT * D.nH * D.lamOf b + D.nH * k + D.head g b) i)
  | .qh b g i n => (.ao, featAt D (D.ln - 1) (D.nH * D.ch * D.lamOf b + D.ch * D.head g b + n) i)
  | .qh' b g i n =>
    (.ao, featAt D (D.ln - 1)
        (D.nl * D.nH * D.ch + D.nH * D.ch * D.lamOf b + D.ch * D.head g b + n) i)
  | .qry k b g i n =>
    (.qa, featAt D (D.ln - 1) (D.nH * D.ch * (D.nl * k + D.lamOf b) + D.ch * D.head g b + n) i)
  | .key k lam g j n =>
    (.qa, featAt D (D.ln - 1)
        (2 * D.nl * D.nH * D.ch + D.nG * D.ch * (D.nl * k + lam) + D.ch * g + n) j)
  | .val k lam g j n =>
      (.qa, featAt D (D.ln - 1)
          (2 * D.nl * D.nH * D.ch + 2 * D.nl * D.nG * D.ch +
            D.nG * D.ch * (D.nl * k + lam) + D.ch * g + n) j)
  | .out k b g i n =>
      (.qa, featAt D (D.ln - 1)
          (2 * D.nl * D.nH * D.ch + 4 * D.nl * D.nG * D.ch +
            D.nH * D.ch * (D.nl * k + D.lamOf b) + D.ch * D.head g b + n) i)

/-- the bit B[t, θ, π] of the multiplicities: row 32 (t mod 2^9) + π, column 128 θ + ⌊t / 2^9⌋ of
the matrix b -/
def addrB (t θ π : ℕ) : ℕ × ℕ := (32 * (t % 2 ^ 9) + π, 128 * θ + t / 2 ^ 9)

/-- the number of columns of a matrix -/
def nCol (C : Calls) : Mx → ℕ
  | .as => (5 * D.nb * 2 ^ D.lM + 5 * D.nb * 2 ^ D.lD) / 2 ^ lRow D K .as
  | .ah => (8 * D.nl * D.nH + D.nl * D.lT * D.nH) / 2 ^ K.fh
  | .ao => 2 * D.nl * D.nH * D.ch / 2 ^ (D.ln - 1)
  | .b => 128 * C.NT
  | .qa => (4 * D.nl * D.nH * D.ch + 4 * D.nl * D.nG * D.ch) / 2 ^ (D.ln - 1)

end Addr

/-! ## The reference parameters: the numbers; the conditions `Lawful` and `Dim.OK` -/

theorem ref_cols :
    nCol Dim.ref Cols.ref Calls.ref .as = 7200 ∧
    nCol Dim.ref Cols.ref Calls.ref .ah = 360 ∧
    nCol Dim.ref Cols.ref Calls.ref .ao = 640 ∧
    nCol Dim.ref Cols.ref Calls.ref .b = 1408 ∧
    nCol Dim.ref Cols.ref Calls.ref .qa = 1536 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem ref_rows :
    lRow Dim.ref Cols.ref .as = 16 ∧
    lRow Dim.ref Cols.ref .ah = 13 ∧
    lRow Dim.ref Cols.ref .ao = 16 ∧
    lRow Dim.ref Cols.ref .b = 14 ∧
    lRow Dim.ref Cols.ref .qa = 16 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem ref_used :
    Dim.ref.used 0 = 94371840 ∧ Dim.ref.used 1 = 94371840 ∧
    Dim.ref.used 2 = 42106880 ∧ Dim.ref.used 3 = 20971520 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem ref_trees :
    Calls.ref.NT = 11 ∧ Calls.ref.first 0 = 0 ∧ Calls.ref.first 1 = 4 ∧
    Calls.ref.first 2 = 8 ∧ Calls.ref.first 3 = 10 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The numbers of padding positions of the 11 trees, at the reference parameters. -/
theorem ref_padCount : (List.range 11).map (padCount Dim.ref Calls.ref) =
    [0, 0, 6291456, 33554432, 0, 0, 6291456, 33554432, 0, 25001984, 12582912] := by
  decide +kernel

/-- The sizes are those of the program's parameters. -/
theorem ref_ppref :
    Dim.ref.nG = ppref.nkv ∧ Dim.ref.nH = ppref.nq ∧ Dim.ref.ch = ppref.ch ∧ Dim.ref.T = ppref.T ∧
    Dim.ref.na = ppref.nq / ppref.nkv ∧ ppref.layers = 12 * Dim.ref.nl := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The scales of the segment are valid for attention: the input shift of the exponential and the
2,307 live rows are a valid pair (`ExpOK`); all layers of the segment have this shift and this
number of rows. -/
class Lawful [scl : Scl] : Prop where
  ex : ExpOK (scl.κ 0).sh 2307
  sh : ∀ l, (scl.κ l).sh = (scl.κ 0).sh
  rows : ∀ l, (scl.κ l).expRows = 2307

/-- the reference scales are valid -/
instance Lawful.ref : @Lawful Scl.ref := ⟨by decide +kernel, fun _ => rfl, fun _ => rfl⟩

/-- The numbers of the main lookup argument fit, at the reference sizes and valid scales. -/
theorem ref_calls_ok [scl : Scl] [law : Lawful] : Calls.ref.OK Dim.ref where
  fits := by decide +kernel
  le := by decide +kernel
  nt := by decide +kernel
  aligned := by decide +kernel
  ten := by decide +kernel
  ex := law.ex

/-- what the facts on addresses need of the sizes: the features of ah fill whole columns -/
structure Dim.OK (K : Cols) : Prop where
  ah : 2 ^ K.fh ∣ 8 * D.nl * D.nH + D.nl * D.lT * D.nH

theorem ref_dim_ok : Dim.ref.OK Cols.ref := ⟨by decide +kernel⟩

/-! ## The relation and the program -/

/-- The inputs of layer lam of the segment are those of the program, for the weights w of a layer,
its number L and the stream x before its attention block: the arrays qry, key, val hold q, kx, v of
step (PL5). -/
def InputsAre (P : Params) (tb : Tables) (w : LayerW) (L : ℕ) (x : ℕ → Vec)
    (lam : ℕ) (t : Raw → ℤ) : Prop :=
  (∀ b < D.nb, D.lamOf b = lam →
    ∀ g < D.nG,
      ∀ i < D.T, ∀ n < D.ch, qryV t b g i n = Att.q P tb w L x i (D.ch * D.head g b + n)) ∧
  ∀ g < D.nG, ∀ j < D.T, ∀ n < D.ch,
    keyV t lam g j n = Att.kx P tb w L x j (D.ch * g + n) ∧
    valV t lam g j n = Att.v P w x j (D.ch * g + n)

/-- The output of layer lam of the segment is that of the program: out holds o of step (PL6), that
is of (PA1) to (PA7). -/
def OutputIs (P : Params) (tb : Tables) (w : LayerW) (L : ℕ) (x : ℕ → Vec) (lam : ℕ) (t : Raw → ℤ) :
    Prop :=
  ∀ b < D.nb, D.lamOf b = lam →
    ∀ g < D.nG, ∀ i < D.T, ∀ n < D.ch, outV t b g i n = Att.o P tb w L x i (D.ch * D.head g b + n)

/-! ## The honest trace -/

section Honest
/- P lam: the parameters at which layer lam of the segment runs -/
variable (P : ℕ → Params) (tb : Tables) (w : ℕ → LayerW) (L0 : ℕ) (x : ℕ → ℕ → Vec)

/-- sc_ij of (PA1) for the pair b and the key/value head g: query head na g + a(b) of layer L0 +
λ(b). At a masked entry, j > i, it is formed by the same formula. -/
def hSc (b g i j : ℕ) : ℤ :=
  Att.sc (P (D.lamOf b)) tb (w (D.lamOf b)) (L0 + D.lamOf b) (x (D.lamOf b)) (D.head g b) i j
/-- mx_i of (PA2) -/
def hMx (b g i : ℕ) : ℤ :=
  Att.mx (P (D.lamOf b)) tb (w (D.lamOf b)) (L0 + D.lamOf b) (x (D.lamOf b)) (D.head g b) i
/-- den_i of (PA5) -/
def hDen (b g i : ℕ) : ℤ :=
  Att.den (P (D.lamOf b)) tb (w (D.lamOf b)) (L0 + D.lamOf b) (x (D.lamOf b)) (D.head g b) i
/-- ac_i[n] of (PA6) -/
def hAc (b g i n : ℕ) : ℤ :=
  Att.ac (P (D.lamOf b)) tb (w (D.lamOf b)) (L0 + D.lamOf b) (x (D.lamOf b)) (D.head g b) i n
/-- out_i[h][n] of (PA7) -/
def hOut (b g i n : ℕ) : ℤ :=
  Att.o (P (D.lamOf b)) tb (w (D.lamOf b)) (L0 + D.lamOf b) (x (D.lamOf b))
    i (D.ch * D.head g b + n)
/-- RE = 2 ac + den - 2 den out -/
def hRE (b g i n : ℕ) : ℤ :=
  2 * hAc D P tb w L0 x b g i n + hDen D P tb w L0 x b g i -
    2 * hDen D P tb w L0 x b g i * hOut D P tb w L0 x b g i n

/-- the extended gap at an entry, from the program's values -/
def hGp [scl : Scl] : Reg → ℕ → ℕ → ℤ
  | .M, b, y =>
    if D.EmptyM y then D.cutC
    else hMx D P tb w L0 x b (D.mG y) (D.iM y) - hSc D P tb w L0 x b (D.mG y) (D.iM y) (D.jM y)
  | .D, b, y =>
    hMx D P tb w L0 x b (D.dG y) (D.iD y) -
      hSc D P tb w L0 x b (D.dG y) (D.iD y) (D.jD y) + if D.MaskedD y then Om D else 0

/-- (rm, fl, wt) = (gp mod 2^sh, 0, Exp[⌊gp / 2^sh⌋]) if gp < C, and (2^sh + ((gp - C) mod st), 1,
0) if gp ≥ C -/
def hRm [scl : Scl] (ρ : Reg) (b y : ℕ) : ℤ :=
  if hGp D P tb w L0 x ρ b y < D.cutC then hGp D P tb w L0 x ρ b y % 2 ^ D.sh
  else 2 ^ D.sh + (hGp D P tb w L0 x ρ b y - D.cutC) % D.stp
@[inherit_doc hRm] def hFl [scl : Scl] (ρ : Reg) (b y : ℕ) : ℤ :=
  if hGp D P tb w L0 x ρ b y < D.cutC then 0 else 1
@[inherit_doc hRm] def hWt [scl : Scl] (ρ : Reg) (b y : ℕ) : ℤ :=
  if hGp D P tb w L0 x ρ b y < D.cutC then tb.Exp (hGp D P tb w L0 x ρ b y / 2 ^ D.sh) else 0

/-- The honest trace, a function of the weights of the layers and of the streams before their
attention blocks, hence of the index and the instance. The values mx, den, qry, out, key, val are
written in cells by the rule of Inst/Model/Widened.lean. The cells of qry, key, val, out belong to
the preceding feed-forward segment; they are listed here because the relation of this segment reads
them. That the feed-forward segment's honest trace writes the same numbers is a statement about both
traces and is not made in this file. -/
def hon [scl : Scl] : Raw → ℤ
  | .c ρ 0 b y => hRm D P tb w L0 x ρ b y % 256 - 128
  | .c ρ 1 b y => hRm D P tb w L0 x ρ b y / 256 - 128
  | .c ρ 2 b y => hFl D P tb w L0 x ρ b y
  | .c ρ 3 b y => hWt D P tb w L0 x ρ b y % 256 - 128
  | .c ρ _ b y => hWt D P tb w L0 x ρ b y / 256
  | .mx k b g i => cellW 4 (hMx D P tb w L0 x b g i) k
  | .den k b g i => cellW 4 (hDen D P tb w L0 x b g i) k
  | .ib k b g i => if (argTo (hSc D P tb w L0 x b g i) i).testBit k then 1 else 0
  | .qh b g i n => hRE D P tb w L0 x b g i n / 2 ^ 16 - 128
  | .qh' b g i n => (2 * hDen D P tb w L0 x b g i - 1 - hRE D P tb w L0 x b g i n) / 2 ^ 16 - 128
  | .qry k b g i n =>
    cellW 2 (Att.q (P (D.lamOf b)) tb (w (D.lamOf b)) (L0 + D.lamOf b) (x (D.lamOf b))
        i (D.ch * D.head g b + n)) k
  | .out k b g i n => cellW 2 (hOut D P tb w L0 x b g i n) k
  | .key k lam g j n => cellW 2 (Att.kx (P lam) tb (w lam) (L0 + lam) (x lam) j (D.ch * g + n)) k
  | .val k lam g j n => cellW 2 (Att.v (P lam) (w lam) (x lam) j (D.ch * g + n)) k

/-- The honest trace holds the program's inputs. -/
theorem hon_inputs [scl : Scl] (lam : ℕ) :
    InputsAre D (P lam) tb (w lam) (L0 + lam) (x lam) lam (hon D P tb w L0 x) := by
  refine ⟨fun b _ hb g _ i _ n _ => ?_, fun g _ j _ n _ => ⟨?_, ?_⟩⟩
  · subst hb
    exact sum_cellW (by norm_num) _
  · exact sum_cellW (by norm_num) _
  · exact sum_cellW (by norm_num) _

/-- The honest trace holds the program's output. -/
theorem hon_output [scl : Scl] (lam : ℕ) :
    OutputIs D (P lam) tb (w lam) (L0 + lam) (x lam) lam (hon D P tb w L0 x) := by
  intro b _ hb g _ i _ n _
  subst hb
  exact sum_cellW (by norm_num) _

end Honest

/-! ## The statements -/

namespace Spec

/-- Under `D.OK K` every cell is inside its matrix. -/
def addrRange : Prop :=
  ∀ (D : Dim) (K : Cols) (C : Calls), D.OK K → ∀ c : Raw, c.Valid D →
    (addr D K c).2.1 < 2 ^ lRow D K (addr D K c).1 ∧ (addr D K c).2.2 < nCol D K C (addr D K c).1

/-- Under `D.OK K`, no two cells have the same address. -/
def addrInj : Prop :=
  ∀ (D : Dim) (K : Cols),
    D.OK K → ∀ c c' : Raw, c.Valid D → c'.Valid D → addr D K c = addr D K c' → c = c'

/-- The multiplicity bits B[t, θ, π], t < 2^16, θ < N_T, π < 32, fill the matrix b: each is inside
it, no two at one address, and every address holds one. -/
def addrBFacts : Prop :=
  ∀ (D : Dim) (K : Cols) (C : Calls),
    (∀ t < 2 ^ 16,
      ∀ θ < C.NT, ∀ π < 32, (addrB t θ π).1 < 2 ^ lRow D K .b ∧ (addrB t θ π).2 < nCol D K C .b) ∧
    (∀ t < 2 ^ 16, ∀ π < 32,
      ∀ t' < 2 ^ 16, ∀ π' < 32, ∀ θ θ', addrB t θ π = addrB t' θ' π' → t = t' ∧ θ = θ' ∧ π = π') ∧
    ∀ row < 2 ^ lRow D K .b,
      ∀ col < nCol D K C .b, ∃ t < 2 ^ 16, ∃ θ < C.NT, ∃ π < 32, addrB t θ π = (row, col)

/-- The honest trace satisfies the relation, at the reference sizes and the scales of the instance
argument, for tables with the ranges of (Tab) (`tb.OK ppref`): over the integers, and with cells of
absolute value at most 128. (The bound is that of the widened cell rule.) By `rfraw_of_int` the
relation then holds over every commutative ring. -/
def honest [scl : Scl] : Prop :=
  ∀ tb : Tables, tb.OK ppref →
    ∀ (w : ℕ → LayerW) (L0 : ℕ) (x : ℕ → ℕ → Vec),
      RFraw Dim.ref tb ℤ (hon Dim.ref refP tb w L0 x) ∧
      ∀ c : Raw, c.Valid Dim.ref → |hon Dim.ref refP tb w L0 x c| ≤ 128

end Spec

end Inst.Model.AttSeg
