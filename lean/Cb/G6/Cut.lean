-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/G6/Cut.lean: the bundle `GoodAt` (Cb/Ld/LdSigLift.lean) cut in two: the clauses that speak of the
verifier alone, and the clauses on the honest prover.

Definitions and two small theorems. No protocol occurs here. `GoodAt R H A B ext P` has ten clauses
and takes an honest side H in its type. A statement on soundness that has a `GoodAt` as a premise so
names an honest prover. The cut lets a block's soundness be stated, proved and joined without one.

Main names:
  `KnowAt R A B ext ε`: four of the ten clauses, to the letter: the rounds are point queries
    (`point`), the verifier is local (`isLocal`), the condition on statements is carried (`onOut`),
    and, for each fixed tuple of messages, round-by-round knowledge soundness (`know`). The errors ε
    stand where `GoodAt` has `P.err`.
  `HonAt R H A B P`: the other six clauses.
  `goodAt_iff`: `GoodAt` is the two together.
  `errList ε`: the errors as a list of numbers, round by round. `errList_app`: the list of two lists
    of errors in a row. (It is the library's `Err.toList`: `errList_toList`, Cb/G6/Join.lean.)

Limits: `KnowAt` takes joints (`IOR.Rels`), whose first field is the exact relation; no clause of
`KnowAt` reads it. `KnowAt` says nothing on how large the errors are.

-/
import Cb.Ld.LdSigLift

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TWhole
open Iop Prob Cb

variable {K M Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type}

/-- The clauses on the verifier alone. -/
structure KnowAt (R : IOR Xi Ei Xo Eo) (A : IOR.Rels K Xi Ei (M × Wi))
    (B : IOR.Rels K Xo Eo (M × Wo)) (ext : M → Xi × Ei.Str → Tr R.shape → Wo → Wi)
    (ε : Err R.shape) : Prop where
  point   : Nonempty R.shape.IsPoint
  isLocal : R.IsLocal
  onOut   : ∀ a τ b, A.on a → R.red.out a τ = some b → B.on b
  know    : ∀ m,
    R.red.Know A.on (fun a wp => A.relR a (m, wp)) (fun b wp => B.relR b (m, wp)) (ext m) ε

/-- The clauses on the honest prover. -/
structure HonAt (R : IOR Xi Ei Xo Eo) (H : R.Honest (M × Wi) (M × Wo))
    (A : IOR.Rels K Xi Ei (M × Wi)) (B : IOR.Rels K Xo Eo (M × Wo)) (P : IOR.Nums K R) : Prop where
  acc     : H.Acc A.rel B.rel
  keeps   : ∀ w x c ρ, B.core ((H.strat w x c).run ρ).2.2 = A.core w
  prBad   : prRho H.Bad ≤ P.pBad
  cover   : ∀ w x, H.Hid w x ⊆ P.cov (A.core w)
  prCov   : ∀ k, prRho (P.cov k) ≤ P.pHid
  same    : ∀ w x c ρ, ((H.strat w x c).run ρ).2.2.1 = w.1

/-- `GoodAt` is the two together. -/
theorem goodAt_iff (R : IOR Xi Ei Xo Eo) (H : R.Honest (M × Wi) (M × Wo))
    (A : IOR.Rels K Xi Ei (M × Wi)) (B : IOR.Rels K Xo Eo (M × Wo))
    (ext : M → Xi × Ei.Str → Tr R.shape → Wo → Wi) (P : IOR.Nums K R) :
    GoodAt R H A B ext P ↔ KnowAt R A B ext P.err ∧ HonAt R H A B P :=
  ⟨fun h => ⟨⟨h.point, h.isLocal, h.onOut, h.know⟩,
      ⟨h.acc, h.keeps, h.prBad, h.cover, h.prCov, h.same⟩⟩,
    fun h => ⟨h.1.point, h.1.isLocal, h.2.acc, h.1.onOut, h.2.keeps, h.2.prBad, h.2.cover,
      h.2.prCov, h.2.same, h.1.know⟩⟩

/-- The errors as a list of numbers, round by round. -/
def errList : {s : Shape} → Err s → List ℕ
  | [], _ => []
  | _ :: _, (e, ε) => e :: errList ε

/-- The list of two lists of errors in a row. -/
theorem errList_app : ∀ {s t : Shape} (a : Err s) (b : Err t),
    errList (Err.app a b) = errList a ++ errList b
  | [], _, _, _ => rfl
  | _ :: _, _, (e, a), b => congrArg (e :: ·) (errList_app a b)

end TWhole
