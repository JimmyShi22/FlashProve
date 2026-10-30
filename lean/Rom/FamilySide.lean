-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/FamilySide.lean: the writing side of an encoding of typed queries (`OracleCoding`, Rom/Family.lean), and
a copy of `OComp.overOne`, which carries an algorithm over the one hash function, typed over that
side.

Why. `OracleCoding` holds, beside the three fields that an algorithm over the hash function reads, a
decoding and proofs that the theorems use. A verifier compiled at a concrete encoding needs the
three fields alone.
Main names: `ImplV`, `OracleCoding.v`, `OComp.overOneV`.
The tie (`OComp.overOne_v`): `overOne` at m equals `overOneV` at `m.v`, at every algorithm. The
proof of `innerCompiledVerifier_eq` (Johnson/Top/InnerCompiledVerifierSide.lean) rests on it. If one of the two copies is
changed alone, this file no longer compiles: do not drop the tie in a clean-up.
Limits: definitions and this equation. Nothing on soundness.

-/
import Rom.Family

set_option autoImplicit false

namespace Rom
open ZKCP
open scoped ENNReal

variable {S : OSpec} {lam : ℕ} {α : Type}

/-- The writing side of an encoding of typed queries: what an algorithm over f reads. -/
structure ImplV (S : OSpec) (lam : ℕ) where
  blocks : S.ι → ℕ
  rng : ∀ o, S.Rng o ≃ (Fin (blocks o) → Fin lam → Bool)
  code : (o : S.ι) → S.Dom o → Fin (blocks o) → List Bool

/-- The writing side of an encoding. -/
@[reducible] def OracleCoding.v (m : OracleCoding S lam) : ImplV S lam := ⟨m.blocks, m.rng, m.code⟩

/-- the same algorithm over f -/
def OComp.overOneV (m : ImplV S lam) : OComp S α → OComp (rom lam) α
  | .pure a => .pure a
  | .sample n k => .sample n fun r => (k r).overOneV m
  | .query o q k =>
    (askAll lam (m.blocks o) (m.code o q)).bind fun bs => (k ((m.rng o).symm bs)).overOneV m

/-! ## The tie -/

/-- `overOne` is written as a recursion on the algorithm, so its tie goes by induction. -/
theorem OComp.overOne_v (m : OracleCoding S lam) (c : OComp S α) : c.overOne m = c.overOneV m.v := by
  induction c with
  | pure a => rfl
  | sample n k ih => exact congrArg (OComp.sample n) (funext ih)
  | query o q k ih =>
    exact congrArg ((askAll lam (m.blocks o) (m.code o q)).bind) (funext fun bs => ih _)

end Rom

#print axioms Rom.OComp.overOne_v
