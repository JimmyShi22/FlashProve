-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Thin/K3/GoodK.lean.
THE THIN ROAD. «every link of a chain has Q» STANDS IN THE LIBRARY: Chain.Each
(Cb/Ld/LdLayWGive.lean:55): a chain's side is Each (PK K).
FOR know AND onOut: Ior/KnowChain (Link.KnowT, Link.OnOut, knowT_seq, onOut_seq): Link.GoodK :=
KnowT ∧ OnOut ∧ point ∧ isLocal; these two fields of goodK_seq are CALLS; point and isLocal along a
chain, and fam_goodK, are this file's own.

-/
import Ior.KnowChainProofs
import Cb.Ld.LdLayWGive

set_option autoImplicit false

namespace Iop
open Prob IOR IOR.Chain

namespace IOR

/-- The «know» side of a link, with what the compiler wants: four of GoodT's ten fields. -/
structure Link.GoodK {K : Type} {A B : Joint K} (l : Link K A B) : Prop where
  point   : Nonempty l.R.shape.IsPoint
  isLocal : l.R.IsLocal
  onOut   : l.OnOut
  know    : l.KnowT

/-- The predicate of tier K. -/
def PK (K : Type) : ∀ A B : Joint K, Link K A B → Prop := fun _ _ l => l.GoodK

end IOR

/-- CONTROLS: the library's bundles give the four. -/
theorem goodK_of_goodT {K : Type} {A B : Joint K} (l : Link K A B) (g : l.GoodT) : l.GoodK :=
  ⟨g.point, g.isLocal, g.onOut, g.know⟩

theorem goodK_of_goodB {K : Type} {A B : Joint K} (l : Link K A B) (g : l.GoodB) : l.GoodK :=
  ⟨g.point, g.isLocal, g.onOut, g.know⟩

theorem goodK_seq {K : Type} {A B C : Joint K} (l : Link K A B) (l' : Link K B C) (d : A.W)
    (g₁ : l.GoodK) (g₂ : l'.GoodK) : (l.seq l' d).GoodK :=
  { point := g₁.point.elim fun p₁ => g₂.point.elim fun p₂ => ⟨Shape.IsPoint.append p₁ p₂⟩
    isLocal := g₁.isLocal.seq g₂.isLocal
    onOut := onOut_seq K A B C l l' d g₁.onOut g₂.onOut
    know := knowT_seq K A B C l l' d g₁.know g₁.onOut g₂.know }

/-- THE RULE, GENERIC IN THE LENGTH. -/
theorem chain_goodK {K : Type} {A B : Joint K} (c : Chain K A B) (d : A.W) :
    c.Each (PK K) → (c.link d).GoodK := by
  induction c with
  | one l =>
      intro h
      rw [Chain.link_one]
      exact (each_one _ l).1 h
  | snoc c l ih =>
      intro h
      rw [Chain.link_snoc]
      exact goodK_seq _ l d (ih ((each_snoc _ c l).1 h).1) ((each_snoc _ c l).1 h).2

/-- AND IN THE LEVEL: a family of links b 0 … b n. THE INDUCTION IS OVER THE LENGTH; (b l).GoodK for
all l is its PREMISE. -/
theorem fam_goodK {K : Type} (J : ℕ → Joint K) (b : ∀ l, Link K (J l) (J (l + 1)))
    (h : ∀ l, (b l).GoodK) (d : (J 0).W) : ∀ n, ((Chain.fam J b n).link d).GoodK := by
  intro n
  refine chain_goodK _ d ?_
  induction n with
  | zero =>
      rw [Chain.fam]
      exact (each_one _ _).2 (h 0)
  | succ n ih =>
      rw [Chain.fam]
      exact (each_snoc _ _ _).2 ⟨ih, h (n + 1)⟩

/-- THE JOIN WITH THE FORMS OF Ior/KnowChain: a chain with Each GoodK has their Chain.KnowT and
Chain.OnOut. -/
theorem knowT_onOut_of_each {K : Type} {A B : Joint K} (c : Chain K A B) :
    c.Each (PK K) → c.KnowT ∧ c.OnOut := by
  induction c with
  | one l =>
      intro h
      have g : l.GoodK := (each_one _ l).1 h
      rw [Chain.KnowT, Chain.OnOut]
      exact ⟨g.know, g.onOut⟩
  | snoc c l ih =>
      intro h
      have g : l.GoodK := ((each_snoc _ c l).1 h).2
      have i := ih ((each_snoc _ c l).1 h).1
      rw [Chain.KnowT, Chain.OnOut]
      exact ⟨⟨i.1, g.know⟩, ⟨i.2, g.onOut⟩⟩

end Iop

