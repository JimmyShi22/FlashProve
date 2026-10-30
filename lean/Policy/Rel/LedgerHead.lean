-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Policy/Rel/LedgerHead.lean

The head with the cost ledger, with no prime in its conditions.

With the cost ledger of an acceptance policy the head has six hidden numbers at each position (c, b,
u, k, z, zs), read at the counted positions, and four clauses on them. They lie in bytes 99 to 119
of the array whose bytes 0 to 98 are the final normalisation's ledger
(Inst/Model/Common/Ledger.lean).

`tableOf` is `Head.tableOf` (Inst/Model/Head/Trace.lean) off the family HD0, the third digit of a
margin (`tableOf_of_ne`). At HD0 the key is mg - 2^8 K_1 - K_2 in the table 2^23 · [0, 2^16) (`R23`,
Cm/TargetPHead.lean, which does the same for the plain head). With the inverse of 2^23 that is the
table R16 (`inLut_R23_iff`, Policy/Rel/LedgerThirdDigit.lean).

Limits:
* This file says nothing on what the relation forces or admits.
* "Hidden numbers" is this library's name for the six (`Hid`, Inst/Model/Head/PolicyDefs.lean); the
  name claims nothing.
* That no number of this head depends on a prime is a reading; the theorem behind it is
  `ledger_lang` (Policy/Rel/LedgerRelLaws.lean), for every prime p with 2^61 - 1 ≤ p and every
  table with `LedgerRel.TableOK`.
* The constants are those of Inst/Model/Head/Trace.lean: 2^24 in the clause (Z), 2^37 in the margin,
  and in the table FE the step table (`EX`, Inst/Model/Tables.lean).
* Inst/Model/Head/Index.lean groups the nine families in six calls of the look-up, one table a call.
  That grouping does not hold here: HD0 has a table of its own (five tables: R16, R23, R8, FE, FC).
* What the heads of Inst/Model/Head/Trace.lean and Inst/Model/Head/TraceN.lean list as not said is
  not said here either.
-/
import Cm.TargetPHead
import Inst.Model.Head.TraceN

set_option autoImplicit false

/- The next line removes the default table of scales (the instance `Scl.ref`) in this file.
Whatever reads a table here says which table. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Policy.LedgerHead

open Inst.Model Inst.Model.Head

/-- the table of a family -/
def tableOf : Fam → Lut
  | .NF => R16 | .NFH => R16 | .HD0 => Cm.Plain.TP.R23 | .HD1 => R16 | .ROW => R8 | .HD2 => R8
  | .HE0 => FE | .HE1 => FE | .CNF => FC

section Arrays
variable {K : Type} [CommRing K] (np : NormPar) (t : Cells K) (H : ℕ → ℕ → K) (y : Req)

/-- The key of family s at (x, i). NF is the low key of the rounding nw = rhu(x R, np.K) (`rhu`:
Inst/Model/Program.lean) with the high digit rn, NFH its high key; CNF the clamp; ROW a ledger
byte; HD2, HD1 the two low digits of a margin, HD0 what is left of it (2^23 times the third
digit); HE0, HE1 the middle digit with the value looked up at it. -/
def key : Fam → ℕ → ℕ → K
  | .NF, j, i =>
    xv t j i * Ledger.R (fun n => Dv t n i) + 2 ^ (np.K - 1) - 2 ^ np.K * nw t j i -
      2 ^ 16 * rn t j i
  | .NFH, j, i => ((2 ^ (32 - np.K) : ℕ) : K) * rn t j i
  | .HD0, v, i => mg t H y v i - 2 ^ 8 * K1 t y v i - K2 t y v i
  | .HD1, v, i => K1 t y v i
  | .ROW, n, i => (Ledger.mu n : K) * Dv t n i
  | .HD2, v, i => K2 t y v i
  | .HE0, v, i => K1 t y v i + 2 ^ 16 * ex t v i
  | .HE1, v, i => K1 t y (131072 + v) i + 2 ^ 16 * ex t (131072 + v) i
  | .CNF, j, i => (nw t j i + 2 ^ 15) + 2 ^ 28 * (nrm t j i + 2 ^ 11)

end Arrays

/-- Off the family HD0 the table is that of Inst/Model/Head/Trace.lean. -/
theorem tableOf_of_ne {s : Fam} (hs : s ≠ .HD0) : tableOf s = Head.tableOf s := by
  cases s <;> first | exact absurd rfl hs | rfl

/-- The field relation of the head with the ledger, over a commutative ring F: for the final
normalisation np, the output matrix H with entries in F, what the head reads of the request and the
policy, y (r, e, the checked tokens, the policy's three numbers), and integer cells t. -/
structure RF {F : Type} [CommRing F] (np : NormPar) (H : ℕ → ℕ → F) (y : Req) (t : Cells ℤ) :
    Prop where
  small : Head.Small t
  keys : ∀ s x i, x < len s → i < nT → Head.InLut (tableOf s) (key np (t.cast F) H y s x i)
  idns : ∀ i < nT, ∀ k < 17, N.idn np (t.cast F) i k = 0
  /-- (B4) c + k = C and (Z) zs + Σ ex = 2^24, at every position, masked by ρC. They are separate
  clauses, not among the 17 identities, because the protocol tests them at z_pos, not at the fresh
  point p_V. -/
  jc : ∀ i < nT, dB4 (t.cast F) y i = 0 ∧ dZ (t.cast F) y i = 0
  /-- (B2) Σ (c + C b + u) = θ NB and (B3) Σ (b + z) = cap, or 0 if NB = 0: sums over the counted
  positions, whose number is NB -/
  sums : sB2 (t.cast F) y = 0 ∧ sB3 (t.cast F) y = 0

end Policy.LedgerHead
