--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/Moves.lean: what an honest prover lays and sends in the linear claim's
shared rounds, as plain functions over a field. This file holds definitions only; no theorem is
stated. The same with code, on the program's own elements: Johnson/Desc/K14/Honest/Coded.lean.

The committed table has rows under one code. Rw r is row r before encoding, laid out as the folded
row is: its message (pads among it) at the places below ell, its random tail from the place
tailFirst on. That is the convention of Johnson/Desc/K14/Law/NearRows.lean and HonestRows.lean.

  foldRows   the fold of rows with weights, place by place
  uHon       the data of the message o_u: the rows' fold with the weights w, which are the equality
             vector's entries at gamma
  omegaHon   the data of the message o_omega: for each row of the matrix, what the folded row gives
             at psi_lo on that row's 2 ^ kLo places
  muHon      the scalar sent at "SPLIT": omega_col at the point z_fd, over the matrix's rows, plus
             one entry of the mask message o_sp

What these functions are not. uHon and omegaHon say what stands at the places that the rounds'
equations read. THE 0 AT ALL OTHER PLACES IS A PLACEHOLDER OF THE DEFINITION. The pad of the
message's own out-of-domain sample lies in the same main table beyond these places, and is sampled
at random: it is no part of these vectors, and whoever fills a table lays the pad there, not this 0.
The random tails of the messages' rows under the messages' own codes, the pads, the entries of o_sp
and the first mask's random values are coins, and are not here either.
What is not claimed. Nothing: no statement is made.

-/
import Johnson.Desc.K14.Law.Base

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open Desc.K14.Law

variable {K : Type} [Field K]

/-- The fold of n rows with the weights w, at the place k. -/
def foldRows (n : Nat) (w : Nat → K) (Rw : Nat → Nat → K) (k : Nat) : K :=
  ∑ r ∈ Finset.range n, w r * Rw r k

/-- **The folded row**, at the places that a row takes. The 0 beyond them is a placeholder: the pad
of the message's own sample lies there, and is no part of this vector. -/
def uHon (S : FoldeqShape) (w : Nat → K) (Rw : Nat → Nat → K) (k : Nat) : K :=
  if k < S.entries then foldRows S.index.rows w Rw k else 0

/-- **omega_col**: entry j is what the folded row gives at psi_lo on the 2 ^ kLo places of row j
of the matrix. The 0 beyond the matrix's rows is a placeholder: the pad of the message's own sample
lies there, and is no part of this vector. -/
def omegaHon (S : LinShape) (psiLo : List K) (u : Nat → K) (j : Nat) : K :=
  if j < S.matrixRows then
    ∑ t ∈ Finset.range (2 ^ S.kLo), eqK psiLo t * u (t + 2 ^ S.kLo * j)
  else 0

/-- **The scalar at "SPLIT"**: omega_col at z_fd, over the matrix's rows, plus the mask's entry. -/
def muHon (S : LinShape) (z : List K) (omega : Nat → K) (kappa : K) : K :=
  (∑ j ∈ Finset.range S.matrixRows, eqK z j * omega j) + kappa

end Desc.K14.Honest
