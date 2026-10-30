-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Shared/Step0.lean: round 0 of the shared chain: the shared point is drawn and the two
groups are created.

Definitions only; no theorem is stated. The words are explained in State.lean, and what has been run
and what is not checked is told in Fold.lean.

Main names:
  drawnOnly r n: the round holds no item and draws exactly n elements, no position and no matrix
    entry.
  step0: refuses unless the codes' message lengths are powers of two (Codes.lengthsOk), the shape
    fits the codes (linOk), there is exactly one round, it draws exactly kCol elements, and the
    groups can be created (Ground.newGroup). It writes the shared point and the two groups' numbers.
    Where G_u and Omega have the same code (sharedSplitNeeded is false) one group is created, and
    both numbers name it.

What is not claimed. Nothing on soundness, on an honest prover or on hiding.
What this comment says of the code rests on reading and is not machine-checked.


-/
import Johnson.Desc.Shared.Ground

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.Shared
open OnBytes OnBytes.Params

/-- The round holds no item and draws exactly n elements, no position and no matrix entry. -/
def drawnOnly (r : Fmt.RoundView) (n : Nat) : Bool :=
  r.vals.isEmpty && r.drawn.elems.length == n && r.drawn.poss.isEmpty && r.drawn.trits.isEmpty

/-- Round 0: the shared point and the two groups. -/
def step0 (G : Ground Loc) (p : Par) (d : DState Loc) : List Fmt.RoundView → Option (DState Loc)
  | [r] => do
    if d.st.codes.lengthsOk && linOk d.st.codes p.S && drawnOnly r p.S.kCol then
      let (gU, d₁) ← G.newGroup p d p.S.fold.u.code p.S.sharedMaskCode
      let (gO, d₂) ← if p.S.sharedSplitNeeded then
          G.newGroup p d₁ p.S.omega.code p.S.sharedMaskCode
        else some (gU, d₁)
      some { d₂ with loc := { d.loc with psi := r.drawn.elems.map E.ofTriple, gU := gU, gO := gO } }
    else none
  | _ => none

end Desc.Shared
