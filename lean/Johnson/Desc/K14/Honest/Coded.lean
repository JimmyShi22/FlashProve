--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/Coded.lean: what an honest prover lays and sends in the linear claim's
shared rounds, WITH CODE, on the program's own elements of the extension field. This file holds
definitions only; no theorem is stated.

RwE r is row r of the committed table before encoding, laid out as the folded row is: its message
(pads among it) at the places below ell, its random tail from the place tailFirst on.

  foldRowsE   the fold of rows with weights, place by place
  uHonE       the data of the message o_u, at gamma
  omegaHonE   the data of the message o_omega, at psi_lo and a folded row
  muHonE      the scalar sent at "SPLIT", at z_fd, omega_col and one entry of the mask message
  uAtE, omegaAtE, muAtE   the three as functions of the shared point psi_sh = (psi_lo, gamma)

Read into a field they are the functions of Johnson/Desc/K14/Honest/Moves.lean: CodedReads.lean.
What that file's head says of the 0 outside the places named holds here too: it is a placeholder;
the pad of a message's own out-of-domain sample lies there and is no part of these vectors.
What is not claimed. Nothing: no statement is made.

-/
import Johnson.Desc.K14.Law.NearB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open Desc.K14.Law (sumE eqE)

/-- The fold of n rows with the weights w, at the place k. -/
def foldRowsE (n : Nat) (w : Nat → E) (RwE : Nat → Nat → E) (k : Nat) : E :=
  sumE n fun r => mulE (w r) (RwE r k)

/-- **The folded row**, at the places that a row takes; beyond them a placeholder. -/
def uHonE (S : FoldeqShape) (gam : List E) (RwE : Nat → Nat → E) (k : Nat) : E :=
  if k < S.entries then foldRowsE S.index.rows (eqE gam) RwE k else zeroE

/-- **omega_col**, on the matrix's rows; beyond them a placeholder. -/
def omegaHonE (S : LinShape) (psiLo : List E) (u : Nat → E) (j : Nat) : E :=
  if j < S.matrixRows then sumE (2 ^ S.kLo) fun t => mulE (eqE psiLo t) (u (t + 2 ^ S.kLo * j))
  else zeroE

/-- **The scalar at "SPLIT"**. -/
def muHonE (S : LinShape) (z : List E) (omega : Nat → E) (kappa : E) : E :=
  addE (sumE S.matrixRows fun j => mulE (eqE z j) (omega j)) kappa

/-- The folded row at the shared point. -/
def uAtE (S : LinShape) (psi : List E) (RwE : Nat → Nat → E) : Nat → E :=
  uHonE S.fold (psi.drop S.kLo) RwE

/-- omega_col at the shared point. -/
def omegaAtE (S : LinShape) (psi : List E) (RwE : Nat → Nat → E) : Nat → E :=
  omegaHonE S (psi.take S.kLo) (uAtE S psi RwE)

/-- The scalar at the shared point and z_fd. -/
def muAtE (S : LinShape) (psi z : List E) (RwE : Nat → Nat → E) (kappa : E) : E :=
  muHonE S z (omegaAtE S psi RwE) kappa

end Desc.K14.Honest
