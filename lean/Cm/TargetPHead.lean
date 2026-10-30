-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetPHead.lean: the plain head without a prime in its conditions: the third digit of a margin
by a scaled table.

This file defines the lookup keys with their tables, and the relation `RF` that asks each key to
lie in its table and Cm/Head.lean's identities to be 0, for the model's last part: the final
normalisation, and the check that at every covered position the checked token is the least token
with the greatest logit.
Definitions only. This file has the tables, keys and field relation (`tableOf`, `key`, `RF`); all
else (families, lengths, the plain margin `mg`, the 17 identities `idn`, `Small`) is Cm/Head.lean's.

Why: the key of a margin's third digit is mg - 2^8 K_1 - K_2 in the table 2^23 · [0, 2^16) (`R23`:
the range table of width 16, every entry multiplied by 2^23): the power of two stands in the table
and no inverse occurs. By a reading this is how a write-up of ours (lean/CREDITS.md) writes that key
(restated in our own words).

Main names:
  `tableOf`, `key`: the seven families' tables and keys; of the tables only that of the family HD0
    differs from `tableOf` of Cm/Head.lean.
  `RF np H y t`: the field relation over a commutative ring F: cells below 2^18
    (its fields: see the record).

Limits: what the head of Cm/Head.lean lists as not said is not said here either. The remaining
conditions are the copied library's. By a reading that held them against the write-up:
the 17 identities and the three margin keys with the tables (`R8`, `R16`, `R23`) are the technical
report's at its reference, one for one, but for the order of the digits of one number (`Ledger.sa`,
Inst/Model/Common/Ledger.lean), which is by reading, not machine-checked; the digit keys of the
normalisation lie in the table of width 8 with a public multiplier, there in the table of width 16.
Terms: lean/GLOSSARY.md.
The margin in three digits follows this protocol's technical report, which follows the texts named
in lean/CREDITS.md; the remaining conditions are the copied library's; the text is this library's.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
"The technical report": this protocol's technical report (lean/CREDITS.md).
-/
import Cm.Head

set_option autoImplicit false

namespace Cm.Plain.TP

open Inst.Model Inst.Model.Head

/-- the range table of width 16, every entry multiplied by 2^23 -/
def R23 : Lut := ⟨2 ^ 16, fun ι => 2 ^ 23 * ι, 0⟩

/-- the table of a family -/
def tableOf : Fam → Lut
  | .NF => R16 | .NFH => R16 | .HD0 => R23 | .HD1 => R16 | .ROW => R8 | .HD2 => R8 | .CNF => FC

section Arrays
variable {K : Type} [CommRing K] (np : NormPar) (t : Cells K) (H : ℕ → ℕ → K) (y : Req)

/-- The key of family s at (x, i). NF is the low key of the rounding nw = rhu(x R, K) (`rhu`:
Inst/Model/Program.lean) with the high digit rn, NFH its high key; CNF the clamp; ROW a ledger
byte; HD2, HD1 the two low digits of a margin, HD0 what is left of it (2^23 times the third
digit). -/
def key : Fam → ℕ → ℕ → K
  | .NF, j, i => xv t j i * Ledger.R (fun n => Dv t n i) + 2 ^ (np.K - 1) - 2 ^ np.K * nw t j i - 2 ^ 16 * rn t j i
  | .NFH, j, i => ((2 ^ (32 - np.K) : ℕ) : K) * rn t j i
  | .HD0, v, i => mg t H y v i - 2 ^ 8 * K1 t y v i - K2 t y v i
  | .HD1, v, i => K1 t y v i
  | .ROW, n, i => (Ledger.mu n : K) * Dv t n i
  | .HD2, v, i => K2 t y v i
  | .CNF, j, i => (nw t j i + 2 ^ 15) + 2 ^ 28 * (nrm t j i + 2 ^ 11)

end Arrays

/-- The field relation of the plain head, over a commutative ring F: for the final normalisation
np, the output matrix H with entries in F, what the head reads of the request (r, e, the checked
tokens) and integer cells t. -/
structure RF {F : Type} [CommRing F] (np : NormPar) (H : ℕ → ℕ → F) (y : Req) (t : Cells ℤ) :
    Prop where
  small : Small (2 ^ 18) t
  keys : ∀ s x i, x < len s → i < nT → InLut (tableOf s) (key np (t.cast F) H y s x i)
  idns : ∀ i < nT, ∀ k < 17, idn np (t.cast F) i k = 0

end Cm.Plain.TP
