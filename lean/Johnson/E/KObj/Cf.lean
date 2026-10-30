-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/E/KObj/Cf.lean: a bare block between two joints over a signature stands, by type, between
two of the library's stages.

The library's stage ⟨S, St, E₀, Wp, A⟩ has the joint `(S.over A).cf`: its condition is met by all
statements, and its relaxed relation is enlarged by the statements outside the old condition
(Ior/KnowCollGood.lean). Definitions and proofs. No library file turns.
Main names:
  `JK.cf`, `BK.cf`: the same reduction, extractor and errors between the enlarged joints.
  `BK.good_cf`: a block has its property if and only if its `.cf` has: knowledge soundness into the
    next condition is the library's knowledge soundness at `.cf` (`knowInto_iff`).
  `LK.cf`, `LK.each_cf`: along a typed list.
  An example: `(jOver S A).cf` is the library's stage's joint, by `rfl`.
Limits: nothing here says that a block has its property.
-/
import Johnson.E.KObj.Arrows
import Cb.Req1.LdSeg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace KObj
open Iop Prob Hiop Cb IOR

/-- (C1) -/
@[reducible] def JK.cf (A : JK) : JK := ⟨A.X, A.E, A.W, fun _ => True, Reduction.orOff A.on A.relR⟩
@[reducible] def BK.cf {A B : JK} (b : BK A B) : BK A.cf B.cf := ⟨b.R, b.ext, b.err⟩

/-- (C2) -/
theorem BK.good_cf {A B : JK} (b : BK A B) : b.Good ↔ b.cf.Good := by
  constructor
  · intro h
    exact ⟨h.point, h.isLocal, (know_of_knowInto _ _ _ _ _ _ _ _ _ _).2
      ((knowInto_iff _ _ _ _ _ _ _ _ _ _ _).1 h.know)⟩
  · intro h
    exact ⟨h.point, h.isLocal, (knowInto_iff _ _ _ _ _ _ _ _ _ _ _).2
      ((know_of_knowInto _ _ _ _ _ _ _ _ _ _).1 h.know)⟩

/-- (C3) the library's stage's joint, the verifier's side alone, is (jOver S A).cf -/
example {E Kc : Type} [Field E] [Fintype E] (a : LdStage E Kc) :
    (⟨a.J.X, a.J.E, a.J.W, a.J.rels.on, a.J.rels.relR⟩ : JK) = (jOver a.S a.A).cf := rfl

/-- (C4) along a list -/
def LK.cf {A : JK} : {B : JK} → LK A B → LK A.cf B.cf
  | _, .one b => .one b.cf
  | _, .snoc l b => .snoc (LK.cf l) b.cf

theorem LK.each_cf {A B : JK} (l : LK A B) : l.Each PG ↔ l.cf.Each PG := by
  induction l with
  | one b => rw [LK.cf, LK.each_one, LK.each_one]; exact b.good_cf
  | snoc l b ih =>
    rw [LK.cf, LK.each_snoc, LK.each_snoc, ih]
    exact and_congr_right fun _ => b.good_cf

attribute [irreducible] LK.cf

#print axioms KObj.BK.good_cf
#print axioms KObj.LK.each_cf

end KObj
