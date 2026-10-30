-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Law/BaseChecksIs.lean: the base case's checks, as the description's own
text writes them (Johnson/Desc/Prox/BaseChecks.lean: linearOk, symbolsOk, baseChecks; called by
baseDecide in Johnson/Desc/Prox/BaseCase.lean), are the format library's baseB1, baseB2At and
baseOK at the field .two (Fmt/M1Fold.lean). Three equations, each by rfl.
What for. A check, and a bridge for proofs: the laws that were proved of the format library's three
functions carry over by it. It discharges no premise: no law's statement need name these functions.
The executable verify-on-bytes (root OnBytes/Main.lean) does not import this file, directly or
through other files.
No soundness is claimed.
-/
import Johnson.Desc.Prox.BaseChecks
import Fmt.M1Fold

set_option autoImplicit false

namespace VerifiableInference.Desc.Prox

theorem linearOk_eq (c d : Array Fmt.M1.E) (tau tauS lam : Fmt.M1.E) (M0 M1 : List Fmt.M1.E) :
    linearOk c d tau tauS lam M0 M1 = Fmt.M1.baseB1 .two c d tau tauS lam M0 M1 := rfl

theorem symbolsOk_eq (C Z : Fmt.M1.Code) (lam : Fmt.M1.E) (M0 M1 R0 R1 : List Fmt.M1.E) (x : Nat)
    (o : Fmt.M1.E × Fmt.M1.E × Fmt.M1.E × Fmt.M1.E) :
    symbolsOk C Z lam M0 M1 R0 R1 x o = Fmt.M1.baseB2At .two C Z lam M0 M1 R0 R1 x o := rfl

theorem baseChecks_eq (C Z : Fmt.M1.Code) (c d : Array Fmt.M1.E) (tau tauS lam : Fmt.M1.E)
    (M0 M1 R0 R1 : List Fmt.M1.E) (xs : List Nat)
    (col : Nat → Option (Fmt.M1.E × Fmt.M1.E × Fmt.M1.E × Fmt.M1.E)) :
    baseChecks C Z c d tau tauS lam M0 M1 R0 R1 xs col =
      Fmt.M1.baseOK .two C Z c d tau tauS lam M0 M1 R0 R1 xs col := rfl

end VerifiableInference.Desc.Prox

#print axioms VerifiableInference.Desc.Prox.linearOk_eq
#print axioms VerifiableInference.Desc.Prox.symbolsOk_eq
#print axioms VerifiableInference.Desc.Prox.baseChecks_eq
