-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Thin/K4/PL.lean.
THE BOTTOM: what the compiler wants of a link's SHAPE AND VERIFIER ALONE: point oracles, locality:
two of GoodT's ten fields. It is closed under «two in a row» by itself, so a chain's side is the
library's own Each (Cb/Ld/LdLayWGive.lean:55).
IMPORTS THE LIBRARY ALONE (Cb/Thin/K3/GoodK.lean's first two fields are to REST on this file, not to
stand beside it).
SOUGHT FIRST, NOT FOUND outside a bundle: inside: goodT_seq | chain_goodT.

-/
import Cb.Ld.LdLayWGive

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Iop
open Prob IOR IOR.Chain

namespace IOR

/-- D1: the link's oracles are point oracles; its verifier is local. -/
structure Link.PL {K : Type} {A B : Joint K} (l : Link K A B) : Prop where
  point   : Nonempty l.R.shape.IsPoint
  isLocal : l.R.IsLocal

/-- D2: the predicate, for the library's `Each`. -/
def PLk (K : Type) : ∀ A B : Joint K, Link K A B → Prop := fun _ _ l => l.PL

end IOR

/-- T1: two in a row. -/
theorem pl_seq {K : Type} {A B C : Joint K} (l : Link K A B) (l' : Link K B C) (d : A.W)
    (g₁ : l.PL) (g₂ : l'.PL) : (l.seq l' d).PL :=
  { point := g₁.point.elim fun p₁ => g₂.point.elim fun p₂ => ⟨Shape.IsPoint.append p₁ p₂⟩
    isLocal := g₁.isLocal.seq g₂.isLocal }

/-- T2: the rule, generic in the length. -/
theorem chain_pl {K : Type} {A B : Joint K} (c : Chain K A B) (d : A.W) :
    c.Each (PLk K) → (c.link d).PL := by
  induction c with
  | one l =>
      intro h
      rw [Chain.link_one]
      exact (each_one _ l).1 h
  | snoc c l ih =>
      intro h
      rw [Chain.link_snoc]
      exact pl_seq _ l d (ih ((each_snoc _ c l).1 h).1) ((each_snoc _ c l).1 h).2

end Iop

