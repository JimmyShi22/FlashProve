-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/Common/Ledger.lean: the ledger of a normalisation (99 auxiliary bytes) and its
identities: definitions, used by the head's and the feed-forward segments.

The integer model admits V = Σ_j x[j]² up to 2^78, above the prime 2^64 − 2^32 + 1 of the
protocol's field. So the sum of squares, the square root and the reciprocal are written in bytes
with carries, and the identities (J1) to (J9), which Inst/Model/Head/ calls (JH1) to (JH9), are
equations between these bytes, the sums W_s and the constants of np.
A ledger is here the function D from the number of a byte to its value, in [0, 255] for the honest
prover (the cell, the small integer that is committed for it, is D − 128). The values are in any
commutative ring K: the integers for the relation, a field for the protocol (extensions of the bytes
at a point). Definitions only.
Text in double quotes: see the head of Inst/Model/Program.lean.
Notation: `np : NormPar`: "exponent of the reciprocal; shift; constant" of a normalisation: its
fields M, K, eps (Inst/Model/Program.lean).
-/
import Inst.Model.Program

set_option autoImplicit false

namespace Inst.Model.Ledger

/-- n bytes from byte a on, "read in base 256, low byte first" -/
def b256 {K : Type} [CommRing K] (D : ℕ → K) (a n : ℕ) : K :=
  ∑ l ∈ Finset.range n, 256 ^ l * D (a + l)

section Rows
variable {K : Type} [CommRing K] (D : ℕ → K)

/-- bytes 0..5; 6..9: V = Vlo + 2^48 Vhi -/
def Vlo : K := b256 D 0 6
def Vhi : K := b256 D 6 4
/-- "c_s = (six bytes) − 2^47, bytes 10 + 6 (s − 1) and the next five, s = 1..8; c_0 = 0, c_9 =
D_9" -/
def cs (s : ℕ) : K :=
  if s = 0 then 0 else if s = 9 then D 9 else b256 D (10 + 6 * (s - 1)) 6 - 2 ^ 47
/-- bytes 58..61: "sa = 2 D_58 + D_59 + 2^8 D_60 + 2^16 D_61; s0 = D_59" -/
def sa : K := 2 * D 58 + D 59 + 2 ^ 8 * D 60 + 2 ^ 16 * D 61
def s0 : K := D 59
/-- bytes 62, 63: "sb = D_62 + 2^8 D_63; ς = sa + 2^24 sb" -/
def sb : K := D 62 + 2 ^ 8 * D 63
def sig : K := sa D + 2 ^ 24 * sb D
/-- bytes 64..68; 69..73 -/
def l1 : K := b256 D 64 5
def h1 : K := b256 D 69 5
/-- bytes 74..76; 77, 78 -/
def Blo : K := b256 D 74 3
def Bhi : K := b256 D 77 2
/-- byte 79: "kc = D_79 − 4" -/
def kc : K := D 79 - 4
/-- bytes 80..82; 83..85: "R = Rlo + 2^24 Rhi" -/
def Rlo : K := b256 D 80 3
def Rhi : K := b256 D 83 3
def R : K := Rlo D + 2 ^ 24 * Rhi D
/-- bytes 86..88; 89..93; 94..98 -/
def q1 : K := b256 D 86 3
def rr : K := b256 D 89 5
def rq : K := b256 D 94 5

end Rows

/-- The multiplier µ_n of byte n in the keys (looked-up values) µ_n D_n of the family ROW
(`Fam.ROW`, Inst/Model/FF/Index.lean):
"µ_9 = 4; µ_58 = 2, µ_59 = 128; µ_63 = 2; µ_76 = 2; µ_79 = 32"; 1 otherwise.
µ_n D_n ≤ 255 bounds the byte by 255 / µ_n. -/
def mu (n : ℕ) : ℤ :=
  if n = 9 then 4
  else if n = 58 then 2
  else if n = 59 then 128
  else if n = 63 then 2
  else if n = 76 then 2
  else if n = 79 then 32
  else 1

/-- W_s = Σ_j Σ_{l + l' = s} b_l[j] b_l'[j], for the five cells b_0..b_4 of the d values x[j] -/
def Wsum {K : Type} [CommRing K] (d : ℕ) (b : ℕ → ℕ → K) (s : ℕ) : K :=
  ∑ j ∈ Finset.range d, ∑ l ∈ Finset.range 5, ∑ l' ∈ Finset.range 5, if l + l' = s then
    b l j * b l' j
  else 0

/-- The 17 identities, each as "left side minus right side": number k < 9 is (J1) for s = k; 9..16
are (J2) to (J9). np holds M and ϵ. -/
def idn {K : Type} [CommRing K] (np : NormPar) (Ws : ℕ → K) (D : ℕ → K) (k : ℕ) : K :=
  if k < 9 then Ws k + cs D k - D k - 256 * cs D (k + 1)
  else match k with
    | 9 => sa D * sb D - Blo D - 2 ^ 23 * Bhi D
    | 10 => Vlo D + (np.eps : K) - sa D ^ 2 - 2 ^ 25 * Blo D - l1 D + 2 ^ 48 * kc D
    | 11 => Vhi D - Bhi D - sb D ^ 2 - kc D
    | 12 => l1 D + h1 D - 2 * sig D
    | 13 => Rlo D * sb D + Rhi D * sa D - q1 D
    | 14 => Rhi D * sb D
    | 15 => 2 ^ (np.M + 1) + sig D - s0 D - 2 * (Rlo D * sa D) - 2 ^ 25 * q1 D - 2 * rr D
    | 16 => rr D + rq D - sig D + 1
    | _ => 0

end Inst.Model.Ledger
