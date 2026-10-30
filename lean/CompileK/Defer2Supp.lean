-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/Defer2Supp.lean: the property at a halt in the hypothesis `AdvAlw` of the lemma on deferred
programming of the random oracle (`Spec.defer2`, CompileK/SpecDefer2.lean) can be taken from a
theorem on the support of the run in mode I.

Two statements (`Rom.DeferTail2.Spec.alw_supp`, `Rom.DeferTail2.Spec.advAlw_supp`) and their proofs.
Generic. Nothing assumed beyond the hypotheses of the statements and whatever the arguments hold as
proofs. Programs, states and the two modes: Rom/Defer.lean.

Why: Compile/Batch/DisciplineWorld.lean (`within_interactB`) and its like prove their counts for
final states of runs ("for every x in the support of interact (C.world m) A s: .."): the states that
`AdvAlw`'s recursion visits are those of the run in mode I: every coin, every fresh string, every
fresh answer has positive probability. So these theorems give `AdvAlw`'s clause on counts as they
stand, where the classes are the oracles' names.
The branch with a violation: at a marked evaluation that breaks a rule the run sets its flag and
goes on; `postMarked` is that very state, flag included (Rom/DeferProof_tail.lean: `run_marked_I`,
by rfl): so the recursion and the run agree in that branch too; nothing is excluded by the premise
on the support for that branch: it speaks of every run in the support, the flag set or not.

Notation: `cl`: `PtCls S K` (CompileK/SpecDefer2.lean): classes of points; `J`: `K → Bool`;
`J κ = true`: κ is a joint class (CompileK/SpecDefer2.lean); `G`, `Fn`: `DSt S → Prop`: predicates
on states; in `Spec.defer2` (CompileK/SpecDefer2.lean): `DSt.Ok2`, `DSt.CntK2`; `Step.Alw` (written
`c.Alw`), `AdvAlw` (CompileK/SpecDefer2.lean): predicates, by recursion along a step of the
challenger and along the adversary; `true`: mode I, as the argument `modeI` of `run` and `world`
(Rom/Defer.lean).

Limits: it does not give the properties on the way (`PtFit`, `MarkFit`, G after every marked
evaluation and every reveal): these are its premise.
-/
import CompileK.Defer2Adv

set_option autoImplicit false

namespace Rom
namespace DeferTail2
open DeferTail

namespace Spec

/-- States, for one step: if c.Alw holds with the end condition Post, and Post implies Post' on the
support of c's run in mode I, then c.Alw holds with Post'. -/
def alw_supp : Prop :=
  ∀ (S : OSpec) (sp : Split S) (K : Type) (cl : PtCls S K) (J : K → Bool) (G : DSt S → Prop)
      (α : Type) (c : Step S sp α) (d : DSt S) (Post Post' : α × DSt S → Prop),
    c.Alw cl J G d Post → (∀ y ∈ (c.run true d).support, Post y → Post' y) → c.Alw cl J G d Post'

/-- States, for a whole run: `AdvAlw` with nothing asked at a halt, and Fn of the final state of
every run in the support of the run in mode I, give `AdvAlw` with Fn. -/
def advAlw_supp : Prop :=
  ∀ (S : OSpec) (sp : Split S) (K : Type) (cl : PtCls S K) (J : K → Bool) (G Fn : DSt S → Prop)
      (Out In α : Type) (C : Chall S sp Out In) (A : Adv S Out In α) (s : C.τ × DSt S),
    AdvAlw C cl J G (fun _ => True) A s →
    (∀ x ∈ (interact (C.world true) A s).support, Fn x.2.2) → AdvAlw C cl J G Fn A s

end Spec

theorem alw_supp : Spec.alw_supp := by
  intro S sp K cl J G α c
  induction c with
  | pure a =>
    intro d Post Post' h hs
    exact hs (a, d) (by rw [run_pure]; exact (PMF.mem_support_pure_iff _ _).2 rfl) h
  | sample n k ih =>
    intro d Post Post' h hs r
    exact ih r d Post Post' (h r) fun y hy => hs y (by
      rw [run_sample]
      exact (PMF.mem_support_bind_iff _ _ _).2 ⟨r, PMF.mem_support_uniformOfFintype r, hy⟩)
  | plain o q k ih =>
    intro d Post Post' h hs y hy
    exact ih y.1 _ Post Post' (h y hy) fun z hz => hs z (by
      rw [run_plain]
      exact (PMF.mem_support_bind_iff _ _ _).2 ⟨y, hy, hz⟩)
  | fresh L k ih =>
    intro d Post Post' h hs u
    exact ih _ _ Post Post' (h u) fun z hz => hs z (by
      rw [run_fresh]
      exact (PMF.mem_support_bind_iff _ _ _).2 ⟨u, PMF.mem_support_uniformOfFintype u, hz⟩)
  | marked o t us pt inj k ih =>
    intro d Post Post' h hs
    refine ⟨h.1, h.2.1, fun r => ⟨(h.2.2 r).1, ih _ _ _ Post Post' (h.2.2 r).2 fun z hz => hs z ?_⟩⟩
    rw [run_marked_I]
    exact (PMF.mem_support_bind_iff _ _ _).2 ⟨r, PMF.mem_support_uniformOfFintype r, hz⟩
  | reveal ts k ih =>
    intro d Post Post' h hs
    refine ⟨h.1, ih _ _ Post Post' h.2 fun z hz => hs z ?_⟩
    rw [run_reveal]
    exact hz

theorem advAlw_supp : Spec.advAlw_supp := by
  intro S sp K cl J G Fn Out In α C A
  induction A with
  | halt a =>
    intro s _ hs
    exact hs (a, s) ((PMF.mem_support_pure_iff _ _).2 rfl)
  | sample n k ih =>
    intro s h hs r
    exact ih r s (h r) fun x hx =>
      hs x ((PMF.mem_support_bind_iff _ _ _).2 ⟨r, PMF.mem_support_uniformOfFintype r, hx⟩)
  | query o q k ih =>
    intro s h hs y hy
    refine ih y.1 _ (h y hy) fun x hx =>
      hs x ((PMF.mem_support_bind_iff _ _ _).2 ⟨(y.1, (s.1, withT s.2 y.2)), ?_, hx⟩)
    exact (PMF.mem_support_map_iff _ _ _).2 ⟨y, hy, rfl⟩
  | call m k ih =>
    intro s h hs
    refine alw_supp S sp K cl J G _ (C.step s.1 m) s.2 _ _ h fun y hy hA => ?_
    refine ih y.1.1 _ hA fun x hx =>
      hs x ((PMF.mem_support_bind_iff _ _ _).2 ⟨(y.1.1, (y.1.2, y.2)), ?_, hx⟩)
    exact (PMF.mem_support_map_iff _ _ _).2 ⟨y, hy, rfl⟩

end DeferTail2
end Rom
