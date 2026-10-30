-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/Att/RanCond.lean: a condition on statements is carried past a block.

Definitions, statements and proofs.
A block's two joints may have conditions that say less than what is known of the statement in front
of the block: a round in which the verifier draws is sound at all statements, so its joints may have
the condition "true". Behind such a block what was known in front is lost: that a ledger has at most
n claims, that the statement was put out by a run. Here a further condition P is laid beside the
first joint's and P' beside the second's, where the block's output at a statement with P has P'.
That costs nothing: knowledge soundness on fewer statements is less to prove.

Main names:
  `ranCond A P`: the joint A, with the condition: A's, and P.
  `knowAt_ranCond`: `KnowAt R A B ext ε`, and "what R puts out at a statement with A's condition and
    P has P'", give `KnowAt R (ranCond A P) (ranCond B P') ext ε`.
  `knowAt_ranDraw`: the case of a round in which the verifier draws and keeps the statement beside
    the draw: P' reads P off the statement's first part.

Limits: nothing new on soundness. Nothing on an honest prover or on zero knowledge.
-/
import Cb.G6.Join

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att
open Iop Prob Cb IOR TWhole

/-- The joint A, with a further condition on statements. -/
def ranCond {K X W : Type} {Ex : ExtSpec} (A : Rels K X Ex W) (P : X × Ex.Str → Prop) :
    Rels K X Ex W := ⟨A.rel, A.relR, fun a => A.on a ∧ P a, A.core⟩

/-- A condition on statements is carried past a block. -/
theorem knowAt_ranCond {K M X X' Wp Wp' : Type} {Ei Eo : ExtSpec} {R : IOR X Ei X' Eo}
    {A : Rels K X Ei (M × Wp)} {B : Rels K X' Eo (M × Wp')}
    {ext : M → X × Ei.Str → Tr R.shape → Wp' → Wp} {ε : Err R.shape} (P : X × Ei.Str → Prop)
    (P' : X' × Eo.Str → Prop) (h : KnowAt R A B ext ε)
    (hP : ∀ a τ b, A.on a → P a → R.red.out a τ = some b → P' b) :
    KnowAt R (ranCond A P) (ranCond B P') ext ε :=
  ⟨h.point, h.isLocal, fun a τ b ha hb => ⟨h.onOut a τ b ha.1 hb, hP a τ b ha.1 ha.2 hb⟩,
    fun m a ha => h.know m a ha.1⟩

/-- The same for a round in which the verifier draws and keeps the statement beside the draw. -/
theorem knowAt_ranDraw {K M X D Wp Wp' : Type} [Fintype D] [Nonempty D] {Ex : ExtSpec}
    {A : Rels K X Ex (M × Wp)} {B : Rels K (X × D) Ex (M × Wp')}
    {ext : M → X × Ex.Str → Tr (IOR.draw D (Prod.mk : X → D → X × D) Ex).shape → Wp' → Wp}
    {ε : Err (IOR.draw D (Prod.mk : X → D → X × D) Ex).shape} (P : X × Ex.Str → Prop)
    (h : KnowAt (IOR.draw D (Prod.mk : X → D → X × D) Ex) A B ext ε) :
    KnowAt (IOR.draw D (Prod.mk : X → D → X × D) Ex) (ranCond A P)
      (ranCond B fun b => P (b.1.1, b.2)) ext ε :=
  knowAt_ranCond P _ h fun a τ b _ hp hb => by
    have e : b = ((a.1, IOR.drawn τ), a.2) := (Option.some.inj hb).symm
    rw [e]
    exact hp

end Cb.Pv.Att

#print axioms Cb.Pv.Att.knowAt_ranCond
#print axioms Cb.Pv.Att.knowAt_ranDraw
