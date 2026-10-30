-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadSizes.lean: the arrays, keys and identities of the output head, with the sizes as
letters.

The library describes the output head at one size: 1,024 positions, width 5,120, a vocabulary of
202,048 tokens. These numbers, and sums and products of them, stand in its text as numerals. This
file has text of four of its files with the four sizes as the fields of a record (Sizes):
  the features and the arrays bl to nrm, lg, K1, K2, mg, dB4 to sB3, len: Inst/Model/Head/Index.lean
    and Inst/Model/Head/Trace.lean;
  key: Policy/Rel/LedgerHead.lean (not the key of Inst/Model/Head/Trace.lean, which differs at the
    third digit of a margin and takes a number from the table of scales);
  plainKey: Cm/TargetPHead.lean; plainMg, plainLen: Cm/Head.lean; idn: Inst/Model/Head/TraceN.lean.
At the record `ref`, which holds the library's numbers, each definition is the library's: the
theorems with names that end in _ref say which.

Why. A statement with letters can be evaluated at a small size, and a proof with letters does not
meet numerals of six digits.

Main definitions: Sizes, ref; the features fX to fNrm; the arrays bl, xv, nw, rn, d1, d2, ex, nrm;
lg, K1, K2, rhoC, NB, mg, dB4, dZ, sB2, sB3; len, key, idn; plainMg, plainLen, plainKey.
Main theorems: key_ref, idn_ref, len_ref, plainKey_ref, plainLen_ref, dB4_ref, dZ_ref, sB2_ref,
sB3_ref.

What is not claimed. Nothing is said about a verifier, a proof or a protocol. Away from `ref` no
definition of this file is compared with anything. What does not depend on a size (Head.rd, Head.Dv,
the six numbers Head.hidC to Head.hidS, Head.Req.rho, the ledger of Inst/Model/Common/Ledger.lean)
is taken from the library as it stands. The program does not import this file.
-/
import Policy.Rel.LedgerHead

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.HeadSizes

open Finset
open Inst.Model

/-- The sizes: the number of positions, the width, the size of the vocabulary, and the number of
entries of the first of the two families of looked-up values. -/
structure Sizes where
  T : ℕ
  d : ℕ
  V : ℕ
  Va : ℕ

/-- The library's sizes. -/
def ref : Sizes := ⟨1024, 5120, 202048, 131072⟩

/-! ## Features -/

/-- The feature of the stream's matrix that holds cell l of channel j. -/
def fX (z : Sizes) (l j : ℕ) : ℕ := z.d * l + j
/-- The feature of hf that holds cell l of the normalisation's quotient at channel j. -/
def fNw (z : Sizes) (l j : ℕ) : ℕ := z.d * l + j
/-- The feature of hf that holds cell l of the high digit of its remainder at channel j. -/
def fRn (z : Sizes) (l j : ℕ) : ℕ := 2 * z.d + z.d * l + j
/-- The feature of hf that holds cell l of the middle digit of the margin of entry v. -/
def fD1 (z : Sizes) (l v : ℕ) : ℕ := 4 * z.d + z.V * l + v
/-- The feature of hf that holds the low digit of the margin of entry v. -/
def fD2 (z : Sizes) (v : ℕ) : ℕ := 4 * z.d + 2 * z.V + v
/-- The feature of hf that holds cell l of the looked-up value of entry v. -/
def fEx (z : Sizes) (l v : ℕ) : ℕ := 4 * z.d + 3 * z.V + z.V * l + v
/-- The feature of hd that holds cell l of the clamped value of channel j. -/
def fNrm (z : Sizes) (l j : ℕ) : ℕ := z.d * l + j

theorem fX_ref (l j : ℕ) : fX ref l j = Head.fX l j := rfl
theorem fNw_ref (l j : ℕ) : fNw ref l j = Head.fNw l j := rfl
theorem fRn_ref (l j : ℕ) : fRn ref l j = Head.fRn l j := rfl
theorem fD1_ref (l v : ℕ) : fD1 ref l v = Head.fD1 l v := rfl
theorem fD2_ref (v : ℕ) : fD2 ref v = Head.fD2 v := rfl
theorem fEx_ref (l v : ℕ) : fEx ref l v = Head.fEx l v := rfl
theorem fNrm_ref (l j : ℕ) : fNrm ref l j = Head.fNrm l j := rfl

/-! ## Arrays -/

section Arrays

variable {K : Type} [CommRing K]

/-- The five cells of a value of the stream, and the value. -/
def bl (z : Sizes) (t : Head.Cells K) (l j i : ℕ) : K := t.x (fX z l j) i
def xv (z : Sizes) (t : Head.Cells K) (j i : ℕ) : K := Head.rd 5 fun l => bl z t l j i
/-- The quotient of the normalisation, and the high digit of its remainder. -/
def nw (z : Sizes) (t : Head.Cells K) (j i : ℕ) : K := Head.rd 2 fun l => t.hf (fNw z l j) i
def rn (z : Sizes) (t : Head.Cells K) (j i : ℕ) : K :=
  32896 + Head.rd 2 fun l => t.hf (fRn z l j) i
/-- The cells of the middle and of the low digit of a margin, and the looked-up value. -/
def d1 (z : Sizes) (t : Head.Cells K) (v i : ℕ) : K := Head.rd 2 fun l => t.hf (fD1 z l v) i
def d2 (z : Sizes) (t : Head.Cells K) (v i : ℕ) : K := t.hf (fD2 z v) i
def ex (z : Sizes) (t : Head.Cells K) (v i : ℕ) : K :=
  8421505 + Head.rd 3 fun l => t.hf (fEx z l v) i
/-- The clamped output of the normalisation. -/
def nrm (z : Sizes) (t : Head.Cells K) (j i : ℕ) : K := Head.rd 2 fun l => t.hd (fNrm z l j) i

/-- The logit of token v at position i. -/
def lg (z : Sizes) (t : Head.Cells K) (H : ℕ → ℕ → K) (i v : ℕ) : K :=
  ∑ j ∈ range z.d, nrm z t j i * H j v
/-- The middle and the low digit of a margin. -/
def K1 (z : Sizes) (t : Head.Cells K) (y : Head.Req) (v i : ℕ) : K :=
  d1 z t v i + 32896 * (y.rho i : K)
def K2 (z : Sizes) (t : Head.Cells K) (y : Head.Req) (v i : ℕ) : K :=
  d2 z t v i + 128 * (y.rho i : K)

/-- The indicator of the counted positions: covered, and below the last position. -/
def rhoC (z : Sizes) (y : Head.Req) (i : ℕ) : ℤ :=
  if y.r ≤ i ∧ i < min y.e (z.T - 1) then 1 else 0
/-- The number of counted positions. -/
def NB (z : Sizes) (y : Head.Req) : ℕ := min y.e (z.T - 1) - y.r

/-- The margin of token v at position i. -/
def mg (z : Sizes) (t : Head.Cells K) (H : ℕ → ℕ → K) (y : Head.Req) (v i : ℕ) : K :=
  (y.rho i : K) * (lg z t H i (y.win i) - lg z t H i v - if v < y.win i then 1 else 0) +
    (rhoC z y i : K) * (Head.hidC t i + 2 ^ 37 * Head.hidB t i)

/-- The four clauses of the cost ledger, each as left side minus right side. -/
def dB4 (z : Sizes) (t : Head.Cells K) (y : Head.Req) (i : ℕ) : K :=
  (rhoC z y i : K) * (Head.hidC t i + Head.hidK t i - (y.pol.C : K))
def dZ (z : Sizes) (t : Head.Cells K) (y : Head.Req) (i : ℕ) : K :=
  (rhoC z y i : K) * (Head.hidS t i + ∑ v ∈ range z.V, ex z t v i - 2 ^ 24)
def sB2 (z : Sizes) (t : Head.Cells K) (y : Head.Req) : K :=
  ∑ i ∈ range z.T, (rhoC z y i : K) * (Head.hidC t i + (y.pol.C : K) * Head.hidB t i +
    Head.hidU t i) - (y.pol.theta : K) * (NB z y : K)
def sB3 (z : Sizes) (t : Head.Cells K) (y : Head.Req) : K :=
  ∑ i ∈ range z.T, (rhoC z y i : K) * (Head.hidB t i + Head.hidZ t i) -
    if 0 < NB z y then (y.pol.cap : K) else 0

/-- The key of family s at the entry x and the position i: nine families. -/
def key (z : Sizes) (np : NormPar) (t : Head.Cells K) (H : ℕ → ℕ → K) (y : Head.Req) :
    Head.Fam → ℕ → ℕ → K
  | .NF, j, i =>
    xv z t j i * Ledger.R (fun n => Head.Dv t n i) + 2 ^ (np.K - 1) - 2 ^ np.K * nw z t j i -
      2 ^ 16 * rn z t j i
  | .NFH, j, i => ((2 ^ (32 - np.K) : ℕ) : K) * rn z t j i
  | .HD0, v, i => mg z t H y v i - 2 ^ 8 * K1 z t y v i - K2 z t y v i
  | .HD1, v, i => K1 z t y v i
  | .ROW, n, i => (Ledger.mu n : K) * Head.Dv t n i
  | .HD2, v, i => K2 z t y v i
  | .HE0, v, i => K1 z t y v i + 2 ^ 16 * ex z t v i
  | .HE1, v, i => K1 z t y (z.Va + v) i + 2 ^ 16 * ex z t (z.Va + v) i
  | .CNF, j, i => (nw z t j i + 2 ^ 15) + 2 ^ 28 * (nrm z t j i + 2 ^ 11)

/-- The 17 identities at position i. -/
def idn (z : Sizes) (np : NormPar) (t : Head.Cells K) (i k : ℕ) : K :=
  Ledger.idn np (Ledger.Wsum z.d fun l j => bl z t l j i) (fun n => Head.Dv t n i) k

/-- The margin without a cost. -/
def plainMg (z : Sizes) (t : Head.Cells K) (H : ℕ → ℕ → K) (y : Head.Req) (v i : ℕ) : K :=
  (y.rho i : K) * (lg z t H i (y.win i) - lg z t H i v - if v < y.win i then 1 else 0)

/-- The key of family s at the entry x and the position i: the seven families of the head without a
cost. -/
def plainKey (z : Sizes) (np : NormPar) (t : Head.Cells K) (H : ℕ → ℕ → K) (y : Head.Req) :
    Cm.Plain.Fam → ℕ → ℕ → K
  | .NF, j, i =>
    xv z t j i * Ledger.R (fun n => Head.Dv t n i) + 2 ^ (np.K - 1) - 2 ^ np.K * nw z t j i -
      2 ^ 16 * rn z t j i
  | .NFH, j, i => ((2 ^ (32 - np.K) : ℕ) : K) * rn z t j i
  | .HD0, v, i => plainMg z t H y v i - 2 ^ 8 * K1 z t y v i - K2 z t y v i
  | .HD1, v, i => K1 z t y v i
  | .ROW, n, i => (Ledger.mu n : K) * Head.Dv t n i
  | .HD2, v, i => K2 z t y v i
  | .CNF, j, i => (nw z t j i + 2 ^ 15) + 2 ^ 28 * (nrm z t j i + 2 ^ 11)

end Arrays

/-- The number of keys of a family at one position. -/
def len (z : Sizes) : Head.Fam → ℕ
  | .NF => z.d | .NFH => z.d | .HD0 => z.V | .HD1 => z.V | .ROW => 120 | .HD2 => z.V
  | .HE0 => z.Va | .HE1 => z.V - z.Va | .CNF => z.d

def plainLen (z : Sizes) : Cm.Plain.Fam → ℕ
  | .NF => z.d | .NFH => z.d | .HD0 => z.V | .HD1 => z.V | .ROW => 99 | .HD2 => z.V | .CNF => z.d

/-! ## At the library's sizes -/

section Ref

variable {K : Type} [CommRing K] (np : NormPar) (t : Head.Cells K) (H : ℕ → ℕ → K) (y : Head.Req)

omit [CommRing K] in
theorem bl_ref (l j i : ℕ) : bl ref t l j i = Head.bl t l j i := rfl
theorem xv_ref (j i : ℕ) : xv ref t j i = Head.xv t j i := rfl
theorem nw_ref (j i : ℕ) : nw ref t j i = Head.nw t j i := rfl
theorem rn_ref (j i : ℕ) : rn ref t j i = Head.rn t j i := rfl
theorem d1_ref (v i : ℕ) : d1 ref t v i = Head.d1 t v i := rfl
omit [CommRing K] in
theorem d2_ref (v i : ℕ) : d2 ref t v i = Head.d2 t v i := rfl
theorem ex_ref (v i : ℕ) : ex ref t v i = Head.ex t v i := rfl
theorem nrm_ref (j i : ℕ) : nrm ref t j i = Head.nrm t j i := rfl
theorem lg_ref (i v : ℕ) : lg ref t H i v = Head.lg t H i v := rfl
theorem K1_ref (v i : ℕ) : K1 ref t y v i = Head.K1 t y v i := rfl
theorem K2_ref (v i : ℕ) : K2 ref t y v i = Head.K2 t y v i := rfl
theorem rhoC_ref (i : ℕ) : rhoC ref y i = y.rhoC i := rfl
theorem NB_ref : NB ref y = y.NB := rfl
theorem mg_ref (v i : ℕ) : mg ref t H y v i = Head.mg t H y v i := rfl
theorem dB4_ref (i : ℕ) : dB4 ref t y i = Head.dB4 t y i := rfl
theorem dZ_ref (i : ℕ) : dZ ref t y i = Head.dZ t y i := rfl
theorem sB2_ref : sB2 ref t y = Head.sB2 t y := rfl
theorem sB3_ref : sB3 ref t y = Head.sB3 t y := rfl
theorem plainMg_ref (v i : ℕ) : plainMg ref t H y v i = Cm.Plain.mg t H y v i := rfl

/-- At the library's sizes the nine families' keys are those of Policy/Rel/LedgerHead.lean. -/
theorem key_ref (s : Head.Fam) (x i : ℕ) :
    key ref np t H y s x i = Policy.LedgerHead.key np t H y s x i := by
  cases s <;> rfl

/-- At the library's sizes the seven families' keys are those of Cm/TargetPHead.lean. -/
theorem plainKey_ref (s : Cm.Plain.Fam) (x i : ℕ) :
    plainKey ref np t H y s x i = Cm.Plain.TP.key np t H y s x i := by
  cases s <;> rfl

/-- At the library's sizes the identities are those of Inst/Model/Head/TraceN.lean, which are also
those of Cm/Head.lean. -/
theorem idn_ref (i k : ℕ) : idn ref np t i k = Head.N.idn np t i k := rfl
theorem idn_ref_plain (i k : ℕ) : idn ref np t i k = Cm.Plain.idn np t i k := rfl

end Ref

theorem len_ref (s : Head.Fam) : len ref s = Head.len s := by cases s <;> rfl
theorem plainLen_ref (s : Cm.Plain.Fam) : plainLen ref s = Cm.Plain.len s := by cases s <;> rfl
theorem T_ref : ref.T = Head.nT := rfl
theorem d_ref : ref.d = Head.nD := rfl
theorem V_ref : ref.V = Head.nV := rfl

#print axioms key_ref
#print axioms plainKey_ref
#print axioms idn_ref
#print axioms dZ_ref
#print axioms sB2_ref

/-! ## An evaluation, on made-up cells

One guard: key at ref is the library's key (Policy.LedgerHead.key), at nine families, five entries
and four positions. Nothing is evaluated at a small size: small, reqS, cellsP and matP are read by
no command of this file. -/

/-- Made-up cells, each from -125 to 125. -/
def cellsZ : Head.Cells ℤ :=
  ⟨fun φ i => (((φ * 7 + i * 3) % 251 : ℕ) : ℤ) - 125,
    fun φ i => (((φ * 5 + i) % 251 : ℕ) : ℤ) - 125,
    fun φ i => (((φ + i * 11) % 251 : ℕ) : ℤ) - 125,
    fun φ i => (((φ * 3 + i * 13) % 251 : ℕ) : ℤ) - 125⟩
/-- A made-up output matrix, each entry from -4,096 to 4,094. -/
def matZ : ℕ → ℕ → ℤ := fun j v => (((j * 31 + v * 17) % 8191 : ℕ) : ℤ) - 4096
/-- The final normalisation of the reference. -/
def npZ : NormPar := ⟨44, 30, 53687⟩
/-- A request that covers the positions 1,000 to 1,023. -/
def reqZ : Head.Req := ⟨1000, 1024, fun i => (i * 977) % 202048, ⟨256, 256, 0⟩⟩
/-- A small size, and a request that covers its positions 5 to 7. -/
def small : Sizes := ⟨8, 4, 6, 4⟩
def reqS : Head.Req := ⟨5, 8, fun i => (i * 5) % 6, ⟨256, 256, 0⟩⟩

#guard [Head.Fam.NF, .NFH, .HD0, .HD1, .ROW, .HD2, .HE0, .HE1, .CNF].all fun s =>
  [0, 1, 63, 64, 119].all fun x => [0, 1000, 1022, 1023].all fun i =>
    key ref npZ cellsZ matZ reqZ s x i == Policy.LedgerHead.key npZ cellsZ matZ reqZ s x i

/-- The same cells and matrix modulo 2^64 - 2^32 + 1. -/
def cellsP : Head.Cells (ZMod 18446744069414584321) := cellsZ.cast _
def matP : ℕ → ℕ → ZMod 18446744069414584321 := fun j v => (matZ j v : ZMod 18446744069414584321)

end OnBytes.Road.HeadSizes
