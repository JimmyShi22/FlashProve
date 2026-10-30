-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/LookClaimsHon.lean

Every claim of a sub-proof's lookup (Fo.claimsOf, OnBytes/Tie/Pv/Lookup/Forest/FoClaims.lean), at
the caller's values Fo.colsK (at zb0 and zb1) and Cb.Fo.Pin.pinColK of ν and keysAt of kv, is 0 at
the rounds rsF of Johnson/HonestTrace/LookDefs.lean, under the premises PremF alone.

Johnson/HonestTrace/LookClaims.lean shows this under three statements on plain numbers. They are
theorems: "trace_hon" (Johnson/HonestTrace/LookTrace.lean), "rows16_hon" and "keyEnd_hon"
(Johnson/HonestTrace/LookRows.lean), each under PremT, which "premT_of_premF" (LookClaims.lean)
gives from PremF. This file puts them together.

PremF h lm jLK kv θ al ν C asks: FoNums.ok h = true; 5 ≤ lm ≤ h.kT + 5; θ = 0 where there is one
call; ν reads 0 at the place "zero"; Cb.Lkp.MidP at the joint key vector of kv, the joint table, the
public padding and the bits that ν reads at the planes' places, at θ and al; and the lists of
challenges in C have the lengths that C.Fits fixes.

Main theorems, each under PremF h lm jLK kv θ al ν C, at the rounds rsF h lm jLK kv θ al ν C:
* "k3Rows_hon": K3Rows: the residue of every row of the sumchecks is 0.
* "k3Planes_hon": K3Planes: Fo.claimLeaves, Fo.claimBits and Cb.Fo.Pin.countK are 0.
* "k3Keys_hon": K3Keys at the key vectors kv: Fo.claimJoin is 0.
* "claims_hon": every member of Fo.claimsOf, at these caller's values, is 0.
K3Rows, K3Planes and K3Keys are those of Johnson/Top/H/K3RowOut.lean.

Limits. The mask entries (what ν reads at the places "mask"), al and the elements in C's lists,
whose lengths C.Fits fixes, are arbitrary arguments: nothing is drawn. θ is arbitrary where there
are several calls, and 0 where there is one. K is any field. That PremF holds of anything is not
shown in this file. rsF is a specification, not a program for real sizes.

Not claimed: that a prover's program sends the scalars of rsF; that the Lean verifier's function
which reads these rounds returns a value, or that the forms it then holds have the values of
Fo.claimsOf; that a verifier accepts (completeness of the protocol); anything on what the rounds
show of the keys.

-/
import Johnson.HonestTrace.LookClaims
import Johnson.HonestTrace.LookTrace
import Johnson.HonestTrace.LookRows

set_option autoImplicit false

namespace OnBytes.HonestTrace.Look

open TwV
open OnBytes.Model
open VerifiableInference.OnPublicFiles (K3Rows K3Planes K3Keys keysAt)

section
variable {K : Type} [Field K]
variable (h : Forest.Shape) (lm jLK : ℕ) (kv : ℕ → ℕ → K) (θ al : K) (ν : _root_.Fo.Pl → K)
  (C : Chal K)

/-- Under PremF h lm jLK kv θ al ν C, K3Rows h lm jLK ν holds at rsF: the residue of every row of
the sumchecks is 0. -/
theorem k3Rows_hon (H : PremF h lm jLK kv θ al ν C) :
    K3Rows h lm jLK ν (rsF h lm jLK kv θ al ν C) :=
  k3Rows_of H (trace_hon _ _ _ (premT_of_premF H)) (rows16_hon _ _ _ (premT_of_premF H))

/-- Under PremF h lm jLK kv θ al ν C, K3Planes h lm jLK ν holds at rsF: Fo.claimLeaves, Fo.claimBits
and Cb.Fo.Pin.countK are 0. -/
theorem k3Planes_hon (H : PremF h lm jLK kv θ al ν C) :
    K3Planes h lm jLK ν (rsF h lm jLK kv θ al ν C) :=
  k3Planes_of H (trace_hon _ _ _ (premT_of_premF H)) (rows16_hon _ _ _ (premT_of_premF H))

/-- Under PremF h lm jLK kv θ al ν C, K3Keys h lm jLK ν kv holds at rsF: Fo.claimJoin, at each
call's key vector kv c extended at the call's point, is 0. -/
theorem k3Keys_hon (H : PremF h lm jLK kv θ al ν C) :
    K3Keys h lm jLK ν kv (rsF h lm jLK kv θ al ν C) :=
  k3Keys_of H (trace_hon _ _ _ (premT_of_premF H)) (keyEnd_hon _ _ _ (premT_of_premF H))

/-- **Every claim of the lookup is 0 at rsF.** Under PremF h lm jLK kv θ al ν C, every member of
Fo.claimsOf at rsF, at the columns' sums Fo.colsK and Cb.Fo.Pin.pinColK of ν and the keys keysAt of
kv, is 0. -/
theorem claims_hon (H : PremF h lm jLK kv θ al ν C) :
    ∀ y ∈ _root_.Fo.claimsOf h lm jLK (rsF h lm jLK kv θ al ν C) ν
      (_root_.Fo.colsK h lm (_root_.Fo.endsOf h lm jLK (rsF h lm jLK kv θ al ν C)).zb0 ν)
      (_root_.Fo.colsK h lm (_root_.Fo.endsOf h lm jLK (rsF h lm jLK kv θ al ν C)).zb1 ν)
      (Cb.Fo.Pin.pinColK lm ν) (keysAt h lm jLK kv (rsF h lm jLK kv θ al ν C)), y = 0 :=
  claims_of H (trace_hon _ _ _ (premT_of_premF H)) (rows16_hon _ _ _ (premT_of_premF H))
    (keyEnd_hon _ _ _ (premT_of_premF H))

end

end OnBytes.HonestTrace.Look

#print axioms OnBytes.HonestTrace.Look.k3Rows_hon
#print axioms OnBytes.HonestTrace.Look.k3Planes_hon
#print axioms OnBytes.HonestTrace.Look.k3Keys_hon
#print axioms OnBytes.HonestTrace.Look.claims_hon
