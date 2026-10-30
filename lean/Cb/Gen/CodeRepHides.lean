-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/CodeRepHides.lean: what a code complex hides when it is read at common positions. Statements
and proofs.

A code complex K (Cb/Gen/Code.lean) is a family of components, each encoded by itself with its own
randomness. A reading T (Cb/Gen/CodeRep.lean) of its codes shows, at a long position x, the columns
of all components at their positions pos a x.

Main names:
  `Cx.showsT`: what an encoding shows at a set S of long positions.
  `Spec.hides_under`: if the complex hides (`Hiop.Enc.Hides` with the budget "b columns in each
    component"), then on every set S of long positions whose image in each component has at most b
    elements, the law of what is shown does not depend on the message. Error 0. Any reading:
    evenness is not needed.
  `Spec.hides_under_t`: in particular on every set of at most t long positions, if t <= b for every
    component (t long positions read at most t positions, perhaps repeated, of each component): the
    budget is not split among the components.
  `Spec.cx_hides_core`: a complex hides as soon as its codes have `Enc.Core` (Cb/Gen/CodeList.lean):
    unique decoding plays no part in hiding.

The form. "For every fixed set of at most t positions" (the strong form of the paper that this
protocol builds on (lean/CREDITS.md)); positions drawn at random are a mixture of these. The errors
of the components are 0 here, so their sum is 0.

Limits: this file says nothing on an oracle that lies in several groups. Its budget then has to bear
the positions of all their readings together. `Spec.hides_under` asks nothing of the reading, but
the reading whose long positions are the disjoint union of theirs is not written out here. No
simulator is written out: the statement is that the law is the same for all messages.

Terms: lean/GLOSSARY.md.
-/
import Cb.Gen.CodeRep
import Cb.Gen.CodeListProofs
import Cb.Gen.CodeProofsComp
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Blocks Hiop

section
variable {F : Type} [Field F] [Fintype F] (E : Type) [Field E] [Fintype E] [Algebra F E]

/-- What an encoding of a complex shows at the long positions in S. -/
def Cx.showsT (K : Cx F) (T : Reading fun a => (K.comp a).code) (S : Finset T.P)
    (m : (K.enc E).Msg) (r : (K.enc E).Rnd) :
    S → ∀ a, (K.comp a).R → Kf F E (K.comp a).overF :=
  fun x a => (K.enc E).enc m r a (T.pos a x)

end

namespace Spec
variable (F : Type) [Field F] [Fintype F] (E : Type) [Field E] [Fintype E] [Algebra F E]

def hides_under : Prop :=
  ∀ (K : Cx F) (T : Reading fun a => (K.comp a).code), (K.enc E).Hides (K.bud E) →
    ∀ S : Finset T.P, (∀ a, (S.image (T.pos a)).card ≤ (K.comp a).code.b) →
      ∀ m m',
        (unif (K.enc E).Rnd).map (K.showsT E T S m) = (unif (K.enc E).Rnd).map (K.showsT E T S m')

def hides_under_t : Prop :=
  ∀ (K : Cx F) (T : Reading fun a => (K.comp a).code), (K.enc E).Hides (K.bud E) →
    ∀ t : ℕ, (∀ a, t ≤ (K.comp a).code.b) →
      ∀ S : Finset T.P, S.card ≤ t →
        ∀ m m',
          (unif (K.enc E).Rnd).map (K.showsT E T S m) = (unif (K.enc E).Rnd).map (K.showsT E T S m')

def cx_hides_core : Prop := ∀ K : Cx F, (∀ a, (K.comp a).code.Core) → (K.enc E).Hides (K.bud E)

end Spec

section
variable (F : Type) [Field F] [Fintype F] (E : Type) [Field E] [Fintype E] [Algebra F E]

theorem hides_under : Spec.hides_under F E := by
  intro K T h S hS m m'
  classical
  let S' : Finset (K.ext E).Pos := Finset.univ.sigma fun a => S.image (T.pos a)
  have hbud : K.bud E S' := fun a =>
    le_trans (Finset.card_le_card fun p hp =>
      (Finset.mem_sigma.mp ((mem_fibre S' a p).mp hp)).2) (hS a)
  obtain ⟨e, he⟩ := (hides_iff_equiv (K.ext E) (K.enc E) (K.bud E)).mp h S' hbud m m'
  have h1 : K.showsT E T S m = K.showsT E T S m' ∘ e := by
    funext r x
    funext a
    have h2 := he r ⟨a, T.pos a x.1⟩
      (Finset.mem_sigma.mpr ⟨Finset.mem_univ a, Finset.mem_image_of_mem _ x.2⟩)
    exact eq_of_heq (Sigma.mk.inj h2).2
  rw [h1, ← PMF.map_comp, map_unif_equiv e]

theorem hides_under_t : Spec.hides_under_t F E := fun K T h _ ht S hS =>
  hides_under F E K T h S fun a => (Finset.card_image_le.trans hS).trans (ht a)

/-- One component whose code has `Enc.Core`: the encoder does not look at the radius, so the code
may be taken at the radius 0, where it has all the properties of Code/Iface.lean. -/
theorem comp_hides_core (c : Comp F) (h : c.code.Core) : (c.enc E).Hides (c.bud E) := by
  obtain ⟨code, R, overF⟩ := c
  cases overF
  · exact comp_hides F E ⟨code.atRadius 0 1, R, false⟩ (core_props F E code h)
  · exact comp_hides F E ⟨code.atRadius 0 1, R, true⟩ (core_props F E code h)

theorem cx_hides_core : Spec.cx_hides_core F E := fun K h =>
  hides_fam K.A _ _ _ fun a => comp_hides_core F E (K.comp a) (h a)

end
end Cb
