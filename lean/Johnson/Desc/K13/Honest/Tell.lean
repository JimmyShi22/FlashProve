--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K13/Honest/Tell.lean: THE SIMULATOR's CORE FOR A MASKED SUMCHECK, WITH CODE, over any
type of scalars with a 0: plain weights, round polynomials of degree 2, no value shown at the end.
DEFINITIONS ALONE: this file defines part of a simulator; what is proved of it stands in Bij.lean
and BijLaw.lean of this folder.

What it does. It is handed 2 n + 1 scalars of its own and puts them in the shape of what the honest
prover sends (Johnson/Desc/K13/Honest/Moves.lean: `sumU`, `sentL`, `sent`): one scalar, then n
pairs. It is handed nothing else: no witness, no statement, no challenge.
Main names:
  `onNat v`: finitely many values as a function of a number; 0 beyond them.
  `pairsOf w n`: the first 2 n scalars of a row, as n pairs.
  `tellL c n`: **a row of 2 n + 1 scalars in the shape of what is sent.**

What is not claimed. No theorem stands in this file. Nothing on soundness or on hiding.

-/
import Mathlib.Data.Nat.Notation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest

variable {K : Type}

/-- Finitely many values as a function of a number: 0 beyond them. -/
def onNat [Zero K] {N : ℕ} (v : Fin N → K) : ℕ → K := fun j => if h : j < N then v ⟨j, h⟩ else 0

/-- The first 2 n scalars of a row, as n pairs. -/
def pairsOf : (ℕ → K) → ℕ → List (K × K)
  | _, 0 => []
  | w, n + 1 => (w 0, w 1) :: pairsOf (fun j => w (j + 2)) n

/-- **A row of 2 n + 1 scalars in the shape of what is sent**: one scalar, then n pairs. -/
def tellL (c : ℕ → K) (n : ℕ) : K × List (K × K) := (c 0, pairsOf (fun j => c (j + 1)) n)

end VerifiableInference.Desc.K13.Honest
