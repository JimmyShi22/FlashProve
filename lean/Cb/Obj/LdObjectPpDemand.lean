-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectPpDemand.lean: auxiliary lemmas for the assembly of the holographic IOP from its
sub-protocols: demands that are counts: two equations.

Statements and proofs. Generic. Auxiliary lemmas that connect a request without an exit step and the
object.
A demand says which finite sets of positions a verifier may read. `S.qFam q₀ b`
(Cb/Ld/LdSendPiece.lean): q₀ of the further oracles' positions, at most b a long positions of each
member a of S.

Main names:
  `Spec.ldDemand_sum`: after a sending of a family N, the demand "the old part is allowed by
    `S.qFam q₀ b`; at most t a positions of each new member" (`S.qSum N`) is
    `(S.sum N).qFam q₀ (Sum.elim b t)`.
  `Spec.ldDemand_end`: the demand at which the object lets the batch linear test begin,
    `O.P.q0 (O.qaIn qa)`, at qa := "nothing of further oracles, at most ba a positions of each
    message left", is `O.S.qFam` (at most `O.P.t` positions of the encoded index) ba.

So a request that ends without an exit step and whose demand is made of counts meets the object's
demand by an equation.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectLinFull
import Cb.Ld.LdSendPiece

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace Spec

def ldDemand_sum : Prop :=
  ∀ (E : Type) [Field E] (S N : Sig E) (E₀ : ExtSpec) (q₀ : Finset E₀.Pos → Prop)
      (b : S.O → ℕ) (t : N.O → ℕ),
    S.qSum N (S.qFam (E₀ := E₀) q₀ b) t = (S.sum N).qFam (E₀ := E₀) q₀ (Sum.elim b t)

def ldDemand_end : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
      (O : LdOL F E) (ba : O.toC.Sa.O → ℕ),
    O.P.q0 (O.qaIn (O.toC.Sa.qFam (E₀ := O.toC.E₀) (fun U => U = ∅) ba)) =
      O.S.qFam (E₀ := O.Cf.conf.E0) (fun U₀ => U₀.card ≤ O.P.t) ba

end Spec

theorem ldDemand_sum : Spec.ldDemand_sum := by
  classical
  intro E _ S N E₀ q₀ b t
  funext U
  -- the old part of U
  let ι : (E₀.prod S.ext).Pos → (E₀.prod (S.sum N).ext).Pos := fun p => match p with
    | .inl p => .inl p
    | .inr ⟨a, x⟩ => .inr ⟨.inl a, x⟩
  have hι : ∀ (p : (E₀.prod S.ext).Pos) (u : (E₀.prod (S.sum N).ext).Pos),
      (Sum.inl p : ((E₀.prod S.ext).prod N.ext).Pos) ∈ (S.mergeE N E₀).src u ↔ u = ι p := by
    rintro p (u | ⟨a | a, x⟩)
    · show Sum.inl p ∈ ({Sum.inl (Sum.inl u)} : Finset _) ↔ _
      rw [Finset.mem_singleton]
      rcases p with p | ⟨a', x'⟩
      · exact ⟨fun e => by rw [Sum.inl.inj (Sum.inl.inj e)], fun e => by rw [Sum.inl.inj e]⟩
      · exact ⟨fun e => (by cases e), fun e => (by cases e)⟩
    · show Sum.inl p ∈ ({Sum.inl (Sum.inr ⟨a, x⟩)} : Finset _) ↔ _
      rw [Finset.mem_singleton]
      rcases p with p | ⟨a', x'⟩
      · exact ⟨fun e => (by cases e), fun e => (by cases e)⟩
      · constructor
        · intro e
          have e' : (⟨a', x'⟩ : S.ext.Pos) = ⟨a, x⟩ := Sum.inr.inj (Sum.inl.inj e)
          cases e'
          rfl
        · intro e
          have e' : (⟨Sum.inl a, x⟩ : (S.sum N).ext.Pos) = ⟨Sum.inl a', x'⟩ := Sum.inr.inj e
          cases e'
          rfl
    · show Sum.inl p ∈ ({Sum.inr (⟨a, x⟩ : N.ext.Pos)} : Finset ((E₀.prod S.ext).prod N.ext).Pos) ↔
        _
      rw [Finset.mem_singleton]
      rcases p with p | ⟨a', x'⟩
      · exact ⟨fun e => (by cases e), fun e => (by cases e)⟩
      · refine ⟨fun e => (by cases e), fun e => ?_⟩
        have e' : (⟨Sum.inr a, x⟩ : (S.sum N).ext.Pos) = ⟨Sum.inl a', x'⟩ := Sum.inr.inj e
        cases e'
  have hinj : Function.Injective ι := by
    rintro (p | ⟨a, x⟩) (p' | ⟨a', x'⟩) e
    · rw [Sum.inl.inj e]
    · cases e
    · cases e
    · have e' : (⟨Sum.inl a, x⟩ : (S.sum N).ext.Pos) = ⟨Sum.inl a', x'⟩ := Sum.inr.inj e
      cases e'
      rfl
  have hV : ∀ V : Finset (E₀.prod S.ext).Pos,
      (∀ p,
        p ∈ V ↔ ∃ u ∈ U, (Sum.inl p : ((E₀.prod S.ext).prod N.ext).Pos) ∈ (S.mergeE N E₀).src u) ↔
      ∀ p, p ∈ V ↔ ι p ∈ U := by
    intro V
    refine forall_congr' fun p => ?_
    refine Iff.intro
      (fun h =>
        h.trans ⟨fun ⟨u, hu, hs⟩ => ((hι p u).1 hs) ▸ hu, fun hp => ⟨ι p, hp, (hι p _).2 rfl⟩⟩)
      (fun h =>
        h.trans ⟨fun hp => ⟨ι p, hp, (hι p _).2 rfl⟩, fun ⟨u, hu, hs⟩ => ((hι p u).1 hs) ▸ hu⟩)
  have key : ∀ V : Finset (E₀.prod S.ext).Pos, (∀ p, p ∈ V ↔ ι p ∈ U) →
      (S.qFam (E₀ := E₀) q₀ b V ↔
        q₀ U.toLeft ∧
        ∀ a, cnt
            (fun x : (S.om a).P => (Sum.inr ⟨Sum.inl a, x⟩ : (E₀.prod (S.sum N).ext).Pos) ∈ U) ≤
          b a) := by
    intro V h
    have e1 : V.toLeft = U.toLeft := by
      ext p
      rw [Finset.mem_toLeft, Finset.mem_toLeft]
      exact h (.inl p)
    unfold Sig.qFam
    rw [e1]
    refine and_congr Iff.rfl (forall_congr' fun a => ?_)
    have e2 : (fun x : (S.om a).P => (Sum.inr ⟨a, x⟩ : (E₀.prod S.ext).Pos) ∈ V) =
        fun x : (S.om a).P => (Sum.inr ⟨Sum.inl a, x⟩ : (E₀.prod (S.sum N).ext).Pos) ∈ U :=
      funext fun x => propext (h (.inr ⟨a, x⟩))
    rw [e2]
  refine propext ⟨fun h => ?_, fun h => ?_⟩
  · have h1 := (key (U.preimage ι hinj.injOn) fun p => Finset.mem_preimage).1
      (h.1 _ ((hV _).2 fun p => Finset.mem_preimage))
    exact ⟨h1.1, fun a => match a with
      | .inl a => h1.2 a
      | .inr a => h.2 a⟩
  · exact ⟨fun V hv => (key V ((hV V).1 hv)).2 ⟨h.1, fun a => h.2 (.inl a)⟩, fun a => h.2 (.inr a)⟩

theorem ldDemand_end : Spec.ldDemand_end := by
  classical
  intro F E _ _ _ _ _ O ba
  funext U
  refine propext (and_congr Iff.rfl ⟨fun h a => ?_, fun h => ⟨?_, fun a => ?_⟩⟩)
  · refine le_trans (le_of_eq (congrArg cnt (funext fun x => propext ?_))) (h.2 a)
    exact ⟨fun hx => Finset.mem_map.2 ⟨⟨a, x⟩, Finset.mem_toRight.2 hx, rfl⟩, fun hx => by
      obtain ⟨y, hy, e⟩ := Finset.mem_map.1 hx
      have e' : y = ⟨a, x⟩ := Sum.inr.inj e
      exact Finset.mem_toRight.1 (e' ▸ hy)⟩
  · refine Finset.eq_empty_iff_forall_notMem.2 fun y hy => ?_
    obtain ⟨z, -, e⟩ := Finset.mem_map.1 (Finset.mem_toLeft.1 hy)
    cases e
  · refine le_trans (le_of_eq (congrArg cnt (funext fun x => propext ?_))) (h a)
    exact ⟨fun hx => by
      obtain ⟨y, hy, e⟩ := Finset.mem_map.1 hx
      have e' : y = ⟨a, x⟩ := Sum.inr.inj e
      exact Finset.mem_toRight.1 (e' ▸ hy),
        fun hx => Finset.mem_map.2 ⟨⟨a, x⟩, Finset.mem_toRight.2 hx, rfl⟩⟩

end Cb
