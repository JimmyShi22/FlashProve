-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/TargetAtPolicy.lean: the claim of a request on a matrix, and the two records of claims
built on it, at a table pp : ScalesAndPolicy that holds the scales and the acceptance policy. The forms RelL
(Johnson/Flat/LedgerClaim.lean), claimsLedgerOn and claimsReq (Johnson/Flat/ClaimsReq.lean) take a
table of scales s and fix the policy at exact match (AcceptancePolicy.exact).

Main names:
  Flat.RelLAt pp M x: M holds an index at which some trace meets the relaxed relation with the cost
    ledger at the protocol's prime and at pp (Policy.LedgerRel.Rno, Policy/Rel/LedgerRel.lean).
  claimsLedgerOnAt D N pp req, claimsReqAt D N pp: claimsLedgerOn and claimsReq with RelLAt pp in
    the place of RelL s.
  relLAt_exact, claimsLedgerOnAt_exact, claimsReqAt_exact: at pp := Policy.ppOf s AcceptancePolicy.exact each is
    the form at s. Each proof is rfl: if a definition on either side changes so that the two differ,
    this file no longer compiles.

Limits. Definitions and three equations: nothing else is said of RelLAt here. The request stays at
the reference sizes (Instance ppref). pp is any table: nothing asks that its scales be valid or its
policy within bounds. Nothing on soundness or on hiding.

-/
import Johnson.Flat.ClaimsReq

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.OnPublicFiles.Flat

open Inst.Model

variable {rows cols : ℕ}

/-- **The claim of a request on a matrix, at a table of scales and policy**: the matrix holds an
index at which some trace meets the relaxed relation with the cost ledger, at the protocol's prime
and at pp. -/
def RelLAt (pp : ScalesAndPolicy) (M : Fin rows → Fin cols → GE) (x : Instance ppref) : Prop :=
  ∃ i : Cm.Idx, Holds M i ∧ ∃ T, Policy.LedgerRel.Rno Cb.Gl.p pp i x T

/-- At exact match it is RelL s, as functions of the matrix and the request. -/
theorem relLAt_exact (s : Cm.Scales) :
    (RelLAt (Policy.ppOf s AcceptancePolicy.exact) : (Fin rows → Fin cols → GE) → Instance ppref → Prop) =
      RelL s := rfl

end VerifiableInference.OnPublicFiles.Flat

namespace OnBytes.Flat

open OnBytes.Slice Inst.Model VerifiableInference

variable (D : DecR) (N : MatrixNums)

/-- What the statements read of a decoded table, at a table pp of scales and policy; req: the
request that an instance says. -/
def claimsLedgerOnAt {X : Type} (pp : ScalesAndPolicy) (req : X → Instance ppref) : D.Claims X where
  Mat := Cells D N
  mat := cellsOf D N
  inRange := OnPublicFiles.Flat.InRange
  Rel := fun M x => OnPublicFiles.Flat.RelLAt pp M (req x)
  mat_cut := cellsOf_cut D N

/-- The record of claims at the requests that the program's reader takes, at a table of scales and
policy. -/
def claimsReqAt (pp : ScalesAndPolicy) : D.Claims OnPublicFiles.Flat.Req := claimsLedgerOnAt D N pp Subtype.val

/-- At exact match it is claimsLedgerOn at s. -/
theorem claimsLedgerOnAt_exact {X : Type} (s : Cm.Scales) (req : X → Instance ppref) :
    claimsLedgerOnAt D N (Policy.ppOf s AcceptancePolicy.exact) req = claimsLedgerOn D N s req := rfl

/-- At exact match it is claimsReq at s. -/
theorem claimsReqAt_exact (s : Cm.Scales) :
    claimsReqAt D N (Policy.ppOf s AcceptancePolicy.exact) = claimsReq D N s := rfl

end OnBytes.Flat

#print axioms VerifiableInference.OnPublicFiles.Flat.relLAt_exact
#print axioms OnBytes.Flat.claimsLedgerOnAt_exact
#print axioms OnBytes.Flat.claimsReqAt_exact
