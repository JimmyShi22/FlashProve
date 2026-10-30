-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdWfPre.lean: conditions on how each step of a sub-protocol treats the encoded index, its
record and the prover encoded index, with rules for composing them.
The formats of a preamble, link by link: the encoded index is not read and is copied; the record is
handed on; the honest prover hands its prover encoded index on.

Definitions, statements and proofs. No protocol of its own, no code occurs here.

Why: the list of a preamble (Hiop/RecSubs.lean: `PreListR`) asks, beside the bundle of a chain: the
verifier does not read the index; no oracle sent gives away a symbol of it (data: see `given`,
Ior/Honest.lean); the new implicit instance begins with the index, unchanged; the record is handed
on; the honest prover hands its prover encoded index on. Of the oracles that are left it asks
nothing, but that no symbol of them comes from the index (`srcAux`).
A chain that closes a group in its middle passes joints whose oracles are folds at verifier
messages, so the oracles left need not be a function of the oracles sent alone: the notions here do
not ask that.

Main names:
  `F.IdxPrefix`: from the index alone to (index, any oracles): not read; nothing tied; copied; a
    symbol of the copy comes from that symbol alone; no other new symbol comes from the index.
  `F.IdxStep`: the same from (index, any oracles) to (index, any oracles).
  `IdxPrefix.seq`: a prefix, then a step, is a prefix.
  `IdxStep.keep`: a block R whose only oracle is the index, which it neither reads nor ties and only
    copies, set beside further oracles F that are handed on (`R.keep Z F`): a step.
  `IdxStep.post`, `IdxStep.pre`, `IdxPrefix.pre`: a re-bracketing of the explicit part alone, after
    or before, changes nothing.
  `R.OnlyCopies`, `OnlyCopies.seq`, `OnlyCopies.draw`: a block that reads none of its input oracles,
    ties nothing and only copies its oracles; two in a row; the step in which the verifier draws a
    value (`IOR.draw`, Ior/Draw.lean).
  `R.Passes rc rc'`: what is read off the explicit part is handed on: whenever the verifier outputs
    x', rc' x' = rc x.
  `H.Hands Ri px px'`: what is read off the witness is handed on by the honest prover, on inputs in
    Ri, at verifier messages that are not withheld. `Hands.seq` (asks completeness of the first).

Limits: this file says nothing on relations, but for those that `Hands` and its rules take as
parameters.

Terms: lean/GLOSSARY.md.
-/
import Hiop.Chain
import Ior.Draw
import Ior.KnowCollRulesFrame

set_option autoImplicit false

namespace Iop
open Prob

/-- The errors of a list, in the order of the rounds. -/
def Err.list : {s : Shape} → Err s → List ℕ
  | [], _ => []
  | _ :: _, (e, ε) => e :: Err.list ε

theorem Err.list_app :
    ∀ {s t : Shape} (ε : Err s) (ε' : Err t), (Err.app ε ε').list = ε.list ++ ε'.list
  | [], _, _, _ => rfl
  | _ :: _, _, (e, ε), ε' => congrArg (List.cons e) (Err.list_app ε ε')

namespace IOR
variable {X₁ X₂ X₃ X X' Z : Type} {E0 Ea Eb Ec E E' E₁ E₂ E₃ F : ExtSpec}

/-- A prefix: from the encoded index alone to (the encoded index, any oracles). -/
structure IdxPrefix (R : IOR X₁ E0 X₂ (E0.prod Ea)) : Prop where
  noReads : ∀ ρ, R.extReads ρ = ∅
  noTie   : ∀ ρ p, R.tie ρ p = ∅
  copy    : ∀ y τ, (R.imp y τ).1 = y
  srcIdx  : ∀ ρ p, R.srcE ρ (Sum.inl p) = {p} ∧ R.srcO ρ (Sum.inl p) = ∅
  srcAux  : ∀ ρ q, R.srcE ρ (Sum.inr q) = ∅

/-- A step: from (the encoded index, any oracles) to (the encoded index, any oracles). -/
structure IdxStep (R : IOR X₁ (E0.prod Ea) X₂ (E0.prod Eb)) : Prop where
  noIdx   : ∀ ρ p, Sum.inl p ∉ R.extReads ρ
  noTie   : ∀ ρ p q, Sum.inl q ∉ R.tie ρ p
  copy    : ∀ y τ, (R.imp y τ).1 = y.1
  srcIdx  : ∀ ρ p, R.srcE ρ (Sum.inl p) = {Sum.inl p} ∧ R.srcO ρ (Sum.inl p) = ∅
  srcAux  : ∀ ρ q p, Sum.inl p ∉ R.srcE ρ (Sum.inr q)

/-- A prefix followed by a step is a prefix. -/
theorem IdxPrefix.seq {F₁ : IOR X₁ E0 X₂ (E0.prod Ea)} {F₂ : IOR X₂ (E0.prod Ea) X₃ (E0.prod Eb)}
    (h₁ : F₁.IdxPrefix) (h₂ : F₂.IdxStep) : (F₁.seq F₂).IdxPrefix where
  noReads := fun ρ => Finset.eq_empty_of_forall_notMem fun p hp => by
    rcases (mem_seq_extReads F₁ F₂ ρ p).1 hp with h | ⟨q, hq, hpq⟩
    · rw [h₁.noReads] at h
      exact Finset.notMem_empty _ h
    · cases q with
      | inl q => exact h₂.noIdx _ _ hq
      | inr q =>
        rw [h₁.srcAux] at hpq
        exact Finset.notMem_empty _ hpq
  noTie := fun ρ => OPos.forall_append
    (s := F₁.shape) (t := F₂.shape) (P := fun p => (F₁.seq F₂).tie ρ p = ∅)
    (fun p => by
      show (F₁.seq F₂).tie ρ (OPos.left p) = ∅
      rw [seq_tie_left, h₁.noTie])
    (fun p => Finset.eq_empty_of_forall_notMem fun u hu => by
      obtain ⟨q, hq, h⟩ := (mem_seq_tie_right F₁ F₂ ρ p u).1 hu
      cases q with
      | inl q => exact h₂.noTie _ _ _ hq
      | inr q =>
        rcases h with h | ⟨p₁, _, h⟩
        · rw [h₁.srcAux] at h
          exact Finset.notMem_empty _ h
        · rw [h₁.noTie] at h
          exact Finset.notMem_empty _ h)
  copy := fun y τ => by rw [seq_imp, h₂.copy, h₁.copy]
  srcIdx := fun ρ p => by
    refine ⟨Finset.ext fun u => ?_, Finset.eq_empty_of_forall_notMem ?_⟩
    · rw [mem_seq_srcE]
      constructor
      · rintro ⟨q, hq, hu⟩
        rw [(h₂.srcIdx _ p).1, Finset.mem_singleton] at hq
        subst hq
        rwa [(h₁.srcIdx _ p).1] at hu
      · intro hu
        exact ⟨Sum.inl p,
          by rw [(h₂.srcIdx _ p).1]; exact Finset.mem_singleton_self _,
          by rwa [(h₁.srcIdx _ p).1]⟩
    · refine OPos.forall_append (s := F₁.shape) (t := F₂.shape) (fun u hu => ?_) (fun u hu => ?_)
      · obtain ⟨q, hq, hu⟩ := (left_mem_seq_srcO F₁ F₂ ρ _ u).1 hu
        rw [(h₂.srcIdx _ p).1, Finset.mem_singleton] at hq
        subst hq
        rw [(h₁.srcIdx _ p).2] at hu
        exact Finset.notMem_empty _ hu
      · have hu := (right_mem_seq_srcO F₁ F₂ ρ _ u).1 hu
        rw [(h₂.srcIdx _ p).2] at hu
        exact Finset.notMem_empty _ hu
  srcAux := fun ρ q => Finset.eq_empty_of_forall_notMem fun u hu => by
    obtain ⟨q', hq', hu⟩ := (mem_seq_srcE F₁ F₂ ρ _ u).1 hu
    cases q' with
    | inl q' => exact h₂.srcAux _ _ _ hq'
    | inr q' =>
      rw [h₁.srcAux] at hu
      exact Finset.notMem_empty _ hu

/-- Two steps in a row are a step. -/
theorem IdxStep.seq {F₁ : IOR X₁ (E0.prod Ea) X₂ (E0.prod Eb)}
    {F₂ : IOR X₂ (E0.prod Eb) X₃ (E0.prod Ec)} (h₁ : F₁.IdxStep) (h₂ : F₂.IdxStep) :
    (F₁.seq F₂).IdxStep where
  noIdx := fun ρ p hp => by
    rcases (mem_seq_extReads F₁ F₂ ρ _).1 hp with h | ⟨q, hq, hpq⟩
    · exact h₁.noIdx _ _ h
    · cases q with
      | inl q => exact h₂.noIdx _ _ hq
      | inr q => exact h₁.srcAux _ _ _ hpq
  noTie := fun ρ => OPos.forall_append
    (s := F₁.shape) (t := F₂.shape) (P := fun p => ∀ q, Sum.inl q ∉ (F₁.seq F₂).tie ρ p)
    (fun p q hq => by
      have hq : Sum.inl q ∈ (F₁.seq F₂).tie ρ (OPos.left p) := hq
      rw [seq_tie_left] at hq
      exact h₁.noTie _ _ _ hq)
    (fun p u hu => by
      obtain ⟨q, hq, h⟩ := (mem_seq_tie_right F₁ F₂ ρ p _).1 hu
      cases q with
      | inl q => exact h₂.noTie _ _ _ hq
      | inr q =>
        rcases h with h | ⟨p₁, _, h⟩
        · exact h₁.srcAux _ _ _ h
        · exact h₁.noTie _ _ _ h)
  copy := fun y τ => by rw [seq_imp, h₂.copy, h₁.copy]
  srcIdx := fun ρ p => by
    refine ⟨Finset.ext fun u => ?_, Finset.eq_empty_of_forall_notMem ?_⟩
    · rw [mem_seq_srcE]
      constructor
      · rintro ⟨q, hq, hu⟩
        rw [(h₂.srcIdx _ p).1, Finset.mem_singleton] at hq
        subst hq
        rwa [(h₁.srcIdx _ p).1] at hu
      · intro hu
        exact ⟨Sum.inl p,
          by rw [(h₂.srcIdx _ p).1]; exact Finset.mem_singleton_self _,
          by rwa [(h₁.srcIdx _ p).1]⟩
    · refine OPos.forall_append (s := F₁.shape) (t := F₂.shape) (fun u hu => ?_) (fun u hu => ?_)
      · obtain ⟨q, hq, hu⟩ := (left_mem_seq_srcO F₁ F₂ ρ _ u).1 hu
        rw [(h₂.srcIdx _ p).1, Finset.mem_singleton] at hq
        subst hq
        rw [(h₁.srcIdx _ p).2] at hu
        exact Finset.notMem_empty _ hu
      · have hu := (right_mem_seq_srcO F₁ F₂ ρ _ u).1 hu
        rw [(h₂.srcIdx _ p).2] at hu
        exact Finset.notMem_empty _ hu
  srcAux := fun ρ q p hp => by
    obtain ⟨q', hq', hu⟩ := (mem_seq_srcE F₁ F₂ ρ _ _).1 hp
    cases q' with
    | inl q' => exact h₂.srcAux _ _ _ hq'
    | inr q' => exact h₁.srcAux _ _ _ hu

/-- sources after a step that does nothing to the oracles -/
theorem post_id_srcE (R : IOR X₁ E₁ X₂ E₂) (f : X₂ → Option X₃) (ρ : Rho R.shape) (q : E₂.Pos) :
    (R.post f (ExtMap.id _)).srcE ρ q = R.srcE ρ q := by
  refine Finset.ext fun u => ?_
  unfold IOR.post
  simp only [ExtMap.id, Finset.mem_biUnion, Finset.mem_singleton, exists_eq_left]

theorem post_id_srcO (R : IOR X₁ E₁ X₂ E₂) (f : X₂ → Option X₃) (ρ : Rho R.shape) (q : E₂.Pos) :
    (R.post f (ExtMap.id _)).srcO ρ q = R.srcO ρ q := by
  refine Finset.ext fun u => ?_
  unfold IOR.post
  simp only [ExtMap.id, Finset.mem_biUnion, Finset.mem_singleton, exists_eq_left]

/-- A re-bracketing of the explicit part after a prefix or a step. -/
theorem IdxPrefix.post {R : IOR X₁ E0 X₂ (E0.prod Ea)} (h : R.IdxPrefix) (f : X₂ → Option X₃) :
    (R.post f (ExtMap.id _)).IdxPrefix :=
  ⟨h.noReads, h.noTie, h.copy,
    fun ρ p =>
      ⟨(post_id_srcE R f ρ _).trans (h.srcIdx ρ p).1,
        (post_id_srcO R f ρ _).trans (h.srcIdx ρ p).2⟩,
    fun ρ q => (post_id_srcE R f ρ _).trans (h.srcAux ρ q)⟩

theorem IdxStep.post {R : IOR X₁ (E0.prod Ea) X₂ (E0.prod Eb)}
    (h : R.IdxStep) (f : X₂ → Option X₃) :
    (R.post f (ExtMap.id _)).IdxStep :=
  ⟨h.noIdx, h.noTie, h.copy,
    fun ρ p =>
      ⟨(post_id_srcE R f ρ _).trans (h.srcIdx ρ p).1,
        (post_id_srcO R f ρ _).trans (h.srcIdx ρ p).2⟩,
    fun ρ q p hp => h.srcAux ρ q p (by rwa [post_id_srcE] at hp)⟩

/-- A re-bracketing of the explicit part before a step: still a step. -/
theorem IdxStep.pre {R : IOR X₂ (E0.prod Ea) X₃ (E0.prod Eb)} (h : R.IdxStep) (f : X₁ → Option X₂) :
    (R.pre f (ExtMap.id _)).IdxStep := by
  classical
  have eR : ∀ ρ, (R.pre f (ExtMap.id _)).extReads ρ = R.extReads ρ := fun ρ => by
    refine Finset.ext fun u => ?_
    unfold IOR.pre
    simp only [ExtMap.id, Finset.mem_biUnion, Finset.mem_singleton]
    exact ⟨fun ⟨a, ha, e⟩ => e ▸ ha, fun h => ⟨u, h, rfl⟩⟩
  have eS : ∀ ρ q, (R.pre f (ExtMap.id _)).srcE ρ q = R.srcE ρ q := fun ρ q => by
    refine Finset.ext fun u => ?_
    unfold IOR.pre
    simp only [ExtMap.id, Finset.mem_biUnion, Finset.mem_singleton]
    exact ⟨fun ⟨a, ha, e⟩ => e ▸ ha, fun h => ⟨u, h, rfl⟩⟩
  have eT : ∀ ρ p, (R.pre f (ExtMap.id _)).tie ρ p = R.tie ρ p := fun ρ p => by
    refine Finset.ext fun u => ?_
    unfold IOR.pre
    simp only [ExtMap.id, Finset.mem_biUnion, Finset.mem_singleton]
    exact ⟨fun ⟨a, ha, e⟩ => e ▸ ha, fun h => ⟨u, h, rfl⟩⟩
  exact ⟨fun ρ p hp => h.noIdx ρ p (by rwa [eR] at hp),
    fun ρ p q hq => h.noTie ρ p q (by rwa [eT] at hq),
    h.copy,
    fun ρ p => ⟨(eS ρ _).trans (h.srcIdx ρ p).1, (h.srcIdx ρ p).2⟩,
    fun ρ q p hp => h.srcAux ρ q p (by rwa [eS] at hp)⟩

/-- A re-bracketing of the explicit part before a prefix: still a prefix. -/
theorem IdxPrefix.pre {R : IOR X₂ E0 X₃ (E0.prod Eb)} (h : R.IdxPrefix) (f : X₁ → Option X₂) :
    (R.pre f (ExtMap.id _)).IdxPrefix := by
  classical
  have eR : ∀ ρ, (R.pre f (ExtMap.id _)).extReads ρ = R.extReads ρ := fun ρ => by
    refine Finset.ext fun u => ?_
    unfold IOR.pre
    simp only [ExtMap.id, Finset.mem_biUnion, Finset.mem_singleton]
    exact ⟨fun ⟨a, ha, e⟩ => e ▸ ha, fun h => ⟨u, h, rfl⟩⟩
  have eS : ∀ ρ q, (R.pre f (ExtMap.id _)).srcE ρ q = R.srcE ρ q := fun ρ q => by
    refine Finset.ext fun u => ?_
    unfold IOR.pre
    simp only [ExtMap.id, Finset.mem_biUnion, Finset.mem_singleton]
    exact ⟨fun ⟨a, ha, e⟩ => e ▸ ha, fun h => ⟨u, h, rfl⟩⟩
  have eT : ∀ ρ p, (R.pre f (ExtMap.id _)).tie ρ p = R.tie ρ p := fun ρ p => by
    refine Finset.ext fun u => ?_
    unfold IOR.pre
    simp only [ExtMap.id, Finset.mem_biUnion, Finset.mem_singleton]
    exact ⟨fun ⟨a, ha, e⟩ => e ▸ ha, fun h => ⟨u, h, rfl⟩⟩
  exact ⟨fun ρ => (eR ρ).trans (h.noReads ρ),
    fun ρ p => (eT ρ p).trans (h.noTie ρ p),
    h.copy,
    fun ρ p => ⟨(eS ρ _).trans (h.srcIdx ρ p).1, (h.srcIdx ρ p).2⟩,
    fun ρ q => (eS ρ _).trans (h.srcAux ρ q)⟩

/-- A block that only copies its oracles: it reads none, ties nothing, sends no oracle into the new
implicit instance. -/
structure OnlyCopies (R : IOR X E X' E) : Prop where
  noReads : ∀ ρ, R.extReads ρ = ∅
  noTie   : ∀ ρ p, R.tie ρ p = ∅
  copy    : ∀ y τ, R.imp y τ = y
  src     : ∀ ρ p, R.srcE ρ p = {p} ∧ R.srcO ρ p = ∅

theorem OnlyCopies.seq {R₁ : IOR X₁ E X₂ E} {R₂ : IOR X₂ E X₃ E}
    (h₁ : R₁.OnlyCopies) (h₂ : R₂.OnlyCopies) : (R₁.seq R₂).OnlyCopies where
  noReads := fun ρ => Finset.eq_empty_of_forall_notMem fun p hp => by
    rcases (mem_seq_extReads R₁ R₂ ρ p).1 hp with h | ⟨q, hq, _⟩
    · rw [h₁.noReads] at h
      exact Finset.notMem_empty _ h
    · rw [h₂.noReads] at hq
      exact Finset.notMem_empty _ hq
  noTie := fun ρ => OPos.forall_append
    (s := R₁.shape) (t := R₂.shape) (P := fun p => (R₁.seq R₂).tie ρ p = ∅)
    (fun p => by
      show (R₁.seq R₂).tie ρ (OPos.left p) = ∅
      rw [seq_tie_left, h₁.noTie])
    (fun p => Finset.eq_empty_of_forall_notMem fun u hu => by
      obtain ⟨q, hq, _⟩ := (mem_seq_tie_right R₁ R₂ ρ p u).1 hu
      rw [h₂.noTie] at hq
      exact Finset.notMem_empty _ hq)
  copy := fun y τ => by rw [seq_imp, h₂.copy, h₁.copy]
  src := fun ρ p => by
    refine ⟨Finset.ext fun u => ?_, Finset.eq_empty_of_forall_notMem ?_⟩
    · rw [mem_seq_srcE]
      constructor
      · rintro ⟨q, hq, hu⟩
        rw [(h₂.src _ p).1, Finset.mem_singleton] at hq
        subst hq
        rwa [(h₁.src _ q).1] at hu
      · intro hu
        exact ⟨p, by rw [(h₂.src _ p).1]; exact Finset.mem_singleton_self _,
          by rwa [(h₁.src _ p).1]⟩
    · refine OPos.forall_append (s := R₁.shape) (t := R₂.shape) (fun u hu => ?_) (fun u hu => ?_)
      · obtain ⟨q, _, hu⟩ := (left_mem_seq_srcO R₁ R₂ ρ _ u).1 hu
        rw [(h₁.src _ q).2] at hu
        exact Finset.notMem_empty _ hu
      · have hu := (right_mem_seq_srcO R₁ R₂ ρ _ u).1 hu
        rw [(h₂.src _ p).2] at hu
        exact Finset.notMem_empty _ hu

theorem OnlyCopies.draw (D : Type) [Fintype D] [Nonempty D] (nx : X → D → X') (E : ExtSpec) :
    (IOR.draw D nx E).OnlyCopies :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩⟩

/-- A block whose only oracle is the index, which it neither reads nor ties and only copies, beside
further oracles that are handed on: a step. -/
theorem IdxStep.keep {R : IOR X E0 X' E0} (hr : ∀ ρ, R.extReads ρ = ∅)
    (ht : ∀ ρ p, R.tie ρ p = ∅) (hc : ∀ y τ, R.imp y τ = y)
    (hs : ∀ ρ p, R.srcE ρ p = {p} ∧ R.srcO ρ p = ∅) (Z : Type) (F : ExtSpec) :
    (R.keep Z F).IdxStep where
  noIdx := fun ρ p hp => by
    have hp : Sum.inl p ∈ (R.extReads ρ).map Function.Embedding.inl := hp
    rw [hr] at hp
    exact Finset.notMem_empty _ hp
  noTie := fun ρ p q hq => by
    have hq : Sum.inl q ∈ (R.tie ρ p).map Function.Embedding.inl := hq
    rw [ht] at hq
    exact Finset.notMem_empty _ hq
  copy := fun y τ => hc y.1 τ
  srcIdx := fun ρ p => by
    refine ⟨?_, (hs ρ p).2⟩
    show (R.srcE ρ p).map Function.Embedding.inl = _
    rw [(hs ρ p).1]
    rfl
  srcAux := fun ρ q p hp => by
    have hp : (Sum.inl p : E0.Pos ⊕ F.Pos) ∈ ({Sum.inr q} : Finset (E0.Pos ⊕ F.Pos)) := hp
    exact absurd (Finset.mem_singleton.1 hp) (by simp)

/-- The verifier draws a value: a step. -/
theorem IdxStep.draw (D : Type) [Fintype D] [Nonempty D] (nx : X → D → X') :
    (IOR.draw D nx (E0.prod Ea)).IdxStep :=
  ⟨fun _ _ h => Finset.notMem_empty _ h,
    fun _ _ _ h => Finset.notMem_empty _ h,
    fun _ _ => rfl,
    fun _ _ => ⟨rfl, rfl⟩,
    fun _ q p hp => absurd (Finset.mem_singleton.1 hp) (by simp)⟩

/-! ## What is read off the explicit part is handed on -/

/-- Whenever the verifier outputs x', rc' x' = rc x. -/
def Passes {Rc : Type} (R : IOR X₁ E₁ X₂ E₂) (rc : X₁ → Rc) (rc' : X₂ → Rc) : Prop :=
  ∀ x y τ x', R.out x y τ = some x' → rc' x' = rc x

section
variable {Rc : Type}

theorem Passes.seq {R₁ : IOR X₁ E₁ X₂ E₂} {R₂ : IOR X₂ E₂ X₃ E₃} {r₁ : X₁ → Rc} {r₂ : X₂ → Rc}
    {r₃ : X₃ → Rc} (h₁ : R₁.Passes r₁ r₂) (h₂ : R₂.Passes r₂ r₃) : (R₁.seq R₂).Passes r₁ r₃ := by
  intro x y τ x' h
  obtain ⟨x₂, hx, hx'⟩ := Option.bind_eq_some_iff.1 ((seq_out R₁ R₂ x y τ).symm.trans h)
  exact (h₂ _ _ _ _ hx').trans (h₁ _ _ _ _ hx)

theorem Passes.keepX {R : IOR X₁ E₁ X₂ E₂} {r₁ : X₁ → Rc} {r₂ : X₂ → Rc}
    (h : R.Passes r₁ r₂) (Z : Type) :
    (R.keepX Z).Passes (fun a => r₁ a.1) (fun a => r₂ a.1) := by
  intro a y τ a' ha
  obtain ⟨xo, hx, rfl⟩ :=
    Option.map_eq_some_iff.1 (show (R.out a.1 y τ).map (fun xo => (xo, a.2)) = some a' from ha)
  exact h _ _ _ _ hx

theorem Passes.keepX_snd (R : IOR X₁ E₁ X₂ E₂) (r : Z → Rc) :
    (R.keepX Z).Passes (fun a => r a.2) (fun a => r a.2) := by
  intro a y τ a' ha
  obtain ⟨xo, _, rfl⟩ :=
    Option.map_eq_some_iff.1 (show (R.out a.1 y τ).map (fun xo => (xo, a.2)) = some a' from ha)
  rfl

theorem Passes.keepE {R : IOR X₁ E₁ X₂ E₂} {r₁ : X₁ → Rc} {r₂ : X₂ → Rc}
    (h : R.Passes r₁ r₂) (F : ExtSpec) : (R.keepE F).Passes r₁ r₂ :=
  fun x y τ x' hx => h x y.1 τ x' hx

theorem Passes.post {R : IOR X₁ E₁ X₂ E₂} {r₁ : X₁ → Rc} {r₂ : X₂ → Rc} {r₃ : X₃ → Rc}
    (h : R.Passes r₁ r₂) (f : X₂ → Option X₃) (g : ExtMap E₂ E₃)
    (hf : ∀ x x', f x = some x' → r₃ x' = r₂ x) : (R.post f g).Passes r₁ r₃ := by
  intro x y τ x' hx
  obtain ⟨x₂, h1, h2⟩ := Option.bind_eq_some_iff.1 (show (R.out x y τ).bind f = some x' from hx)
  exact (hf _ _ h2).trans (h _ _ _ _ h1)

theorem Passes.pre {R : IOR X₂ E₂ X₃ E₃} {r₁ : X₁ → Rc} {r₂ : X₂ → Rc} {r₃ : X₃ → Rc}
    (h : R.Passes r₂ r₃) (f : X₁ → Option X₂) (g : ExtMap E₁ E₂)
    (hf : ∀ x x', f x = some x' → r₂ x' = r₁ x) : (R.pre f g).Passes r₁ r₃ := by
  intro x y τ x' hx
  obtain ⟨x₂, h1, h2⟩ :=
    Option.bind_eq_some_iff.1 (show (f x).bind (fun x₁ => R.out x₁ (g.map y) τ) = some x' from hx)
  exact (h _ _ _ _ h2).trans (hf _ _ h1)

theorem Passes.draw (D : Type) [Fintype D] [Nonempty D] (nx : X → D → X') (E : ExtSpec) (r : X → Rc)
    (r' : X' → Rc) (h : ∀ x β, r' (nx x β) = r x) :
    (IOR.draw D nx E).Passes r r' := by
  intro x y τ x' hx
  rw [← Option.some.inj (show some (nx x (drawn τ)) = some x' from hx)]
  exact h _ _

end

/-! ## What is read off the witness is handed on -/

/-- The honest prover hands on what is read off its witness: on inputs in the relation, at verifier
messages that are not withheld. -/
def Honest.Hands {Pw W₁ W₂ : Type} {R : IOR X₁ E₁ X₂ E₂} (H : R.Honest W₁ W₂)
    (Ri : X₁ → E₁.Str → W₁ → Prop) (px : W₁ → Pw) (px' : W₂ → Pw) : Prop :=
  ∀ x y w c ρ, Ri x y w → ρ ∉ H.withheld w x → px' ((H.strat w x c).run ρ).2.2 = px w

section
variable {Pw W₁ W₂ W₃ Wz : Type}

theorem Honest.Hands.seq {R₁ : IOR X₁ E₁ X₂ E₂} {R₂ : IOR X₂ E₂ X₃ E₃}
    {H₁ : R₁.Honest W₁ W₂} {H₂ : R₂.Honest W₂ W₃} {Ra : X₁ → E₁.Str → W₁ → Prop}
    {Rb : X₂ → E₂.Str → W₂ → Prop} {p₁ : W₁ → Pw} {p₂ : W₂ → Pw} {p₃ : W₃ → Pw}
    (h₁ : H₁.Hands Ra p₁ p₂) (ha : H₁.Acc Ra Rb) (h₂ : H₂.Hands Rb p₂ p₃) :
    (H₁.seq H₂).Hands Ra p₁ p₃ := by
  intro x y w c ρ hR hρ
  obtain ⟨hρ₁, hρ₂⟩ := (Honest.not_mem_withheld_seq H₁ H₂ w x ρ).1 hρ
  rw [Honest.run_seq]
  exact (h₂ _ _ _ c.2 _ (ha x y w c.1 _ hR hρ₁).2 (hρ₂ c.1)).trans (h₁ x y w c.1 _ hR hρ₁)

theorem Honest.Hands.sub {R : IOR X₁ E₁ X₂ E₂} {H : R.Honest W₁ W₂}
    {Ri Ri' : X₁ → E₁.Str → W₁ → Prop} {p₁ : W₁ → Pw} {p₂ : W₂ → Pw}
    (h : H.Hands Ri p₁ p₂) (hs : ∀ x y w, Ri' x y w → Ri x y w) :
    H.Hands Ri' p₁ p₂ := fun x y w c ρ hR hρ => h x y w c ρ (hs x y w hR) hρ

theorem Honest.Hands.keepX {R : IOR X₁ E₁ X₂ E₂} {H : R.Honest W₁ W₂} {Ri : X₁ → E₁.Str → W₁ → Prop}
    {p₁ : W₁ → Pw} {p₂ : W₂ → Pw} (h : H.Hands Ri p₁ p₂) (Z : Type) :
    (H.keepX Z).Hands (fun a y w => Ri a.1 y w) p₁ p₂ := by
  intro a y w c ρ hR hρ
  show p₂ ((Strat.map (fun o : X₂ × W₂ => ((o.1, a.2), o.2)) (H.strat w a.1 c)).run ρ).2.2 = _
  rw [Strat.run_map]
  exact h a.1 y w c ρ hR hρ

theorem Honest.Hands.keepE {R : IOR X₁ E₁ X₂ E₂} {H : R.Honest W₁ W₂} {Ri : X₁ → E₁.Str → W₁ → Prop}
    {p₁ : W₁ → Pw} {p₂ : W₂ → Pw} (h : H.Hands Ri p₁ p₂) (F : ExtSpec) :
    (H.keepE F).Hands (fun x y w => Ri x y.1 w) p₁ p₂ :=
  fun x y w c ρ hR hρ => h x y.1 w c ρ hR hρ

theorem Honest.Hands.post {R : IOR X₁ E₁ X₂ E₂} {H : R.Honest W₁ W₂} {Ri : X₁ → E₁.Str → W₁ → Prop}
    {p₁ : W₁ → Pw} {p₂ : W₂ → Pw} {p₃ : W₃ → Pw} (h : H.Hands Ri p₁ p₂) (f : X₂ → Option X₃)
    (g : ExtMap E₂ E₃) (m : X₂ × W₂ → X₃ × W₃) (hm : ∀ a, p₃ (m a).2 = p₂ a.2) :
    (H.post f g m).Hands Ri p₁ p₃ := by
  intro x y w c ρ hR hρ
  show p₃ ((Strat.map m (H.strat w x c)).run ρ).2.2 = _
  rw [Strat.run_map]
  exact (hm _).trans (h x y w c ρ hR hρ)

theorem Honest.Hands.pre {R : IOR X₂ E₂ X₃ E₃} {H : R.Honest W₂ W₃} {Ri : X₂ → E₂.Str → W₂ → Prop}
    {Ri' : X₁ → E₁.Str → W₁ → Prop} {p₁ : W₁ → Pw} {p₂ : W₂ → Pw} {p₃ : W₃ → Pw}
    (h : H.Hands Ri p₂ p₃) (f : X₁ → Option X₂) (g : ExtMap E₁ E₂) (m : X₁ × W₁ → X₂ × W₂)
    (hR : ∀ x y w, Ri' x y w → Ri (m (x, w)).1 (g.map y) (m (x, w)).2)
    (hm : ∀ a, p₂ (m a).2 = p₁ a.2) : (H.pre f g m).Hands Ri' p₁ p₃ :=
  fun x y w c ρ hw hρ => (h _ _ _ c ρ (hR x y w hw) hρ).trans (hm (x, w))

/-- a further part of the witness is handed on -/
theorem Honest.Hands.carry_snd
    {R : IOR X₁ E₁ X₂ E₂} (H : R.Honest W₁ W₂) (Ri : X₁ → E₁.Str → W₁ × Wz → Prop) (p : Wz → Pw) :
    (H.carry Wz).Hands Ri (fun w => p w.2) (fun w => p w.2) := by
  intro x y w c ρ _ _
  show p ((Strat.map (fun o : X₂ × W₂ => (o.1, (o.2, w.2))) (H.strat w.1 x c)).run ρ).2.2.2 = _
  rw [Strat.run_map]

/-- the witness re-typed: what the re-typing itself puts back -/
theorem Honest.Hands.mapW {W₁' W₂' : Type} {R : IOR X₁ E₁ X₂ E₂} (H : R.Honest W₁ W₂)
    (fi : W₁' → W₁) (fo : W₁' → W₂ → W₂') (Ri : X₁ → E₁.Str → W₁' → Prop) (p₁ : W₁' → Pw)
    (p₂ : W₂' → Pw) (h : ∀ w o, p₂ (fo w o) = p₁ w) :
    (H.mapW fi fo).Hands Ri p₁ p₂ := by
  intro x y w c ρ _ _
  show p₂ ((Strat.map (fun o : X₂ × W₂ => (o.1, fo w o.2)) (H.strat (fi w) x c)).run ρ).2.2 = _
  rw [Strat.run_map]
  exact h _ _

/-- the witness re-typed, in general -/
theorem Honest.Hands.mapW' {W₁' W₂' : Type} {R : IOR X₁ E₁ X₂ E₂} {H : R.Honest W₁ W₂}
    {Ri : X₁ → E₁.Str → W₁ → Prop} {p₁ : W₁ → Pw} {p₂ : W₂ → Pw} (h : H.Hands Ri p₁ p₂)
    (fi : W₁' → W₁) (fo : W₁' → W₂ → W₂') (Ri' : X₁ → E₁.Str → W₁' → Prop) (p₂' : W₂' → Pw)
    (hR : ∀ x y w, Ri' x y w → Ri x y (fi w)) (hp : ∀ w o, p₂' (fo w o) = p₂ o) :
    (H.mapW fi fo).Hands Ri' (fun w => p₁ (fi w)) p₂' := by
  intro x y w c ρ hw hρ
  show p₂' ((Strat.map (fun o : X₂ × W₂ => (o.1, fo w o.2)) (H.strat (fi w) x c)).run ρ).2.2 = _
  rw [Strat.run_map]
  exact (hp _ _).trans (h x y (fi w) c ρ (hR x y w hw) hρ)

theorem Honest.Hands.draw (D : Type) [Fintype D] [Nonempty D] (nx : X → D → X') (E : ExtSpec)
    (W : Type) (Ri : X → E.Str → W → Prop) (p : W → Pw) :
    (Honest.draw D nx E W).Hands Ri p p :=
  fun _ _ _ _ _ _ _ => rfl

end
end IOR
end Iop
