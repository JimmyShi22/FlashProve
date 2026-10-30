-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/T3/ThreadsAtRing.lean: a value of ThreadsP at a prover is one at an equal prover, with the same invariants. So what is built at A.H serves at G.prover A.H, where the premise ring,
G.prover H = H, holds. A conditional lemma on this library's definitions.
-/
import Johnson.Desc.ProofFile.Honest.Law.OwedAtRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (FileDescription)

variable {Xi W₀ Rc Ky Tr X₀ X : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts} {w₀ : W₀} {rc : Rc} {x : Xi}
  {k : Coins Bk} {R : Ready W₀ Rc Xi Ky Tr X₀ X}

/-- **The same invariants at an equal prover.** -/
def ThreadsP.ofEq {P P' : Prover W₀ Rc Xi Ky Tr X₀ X} (e : P = P') (T : ThreadsP F Bk P w₀ rc x k R) :
    ThreadsP F Bk P' w₀ rc x k R :=
  e ▸ T

theorem ThreadsP.ofEq_I₁ {P P' : Prover W₀ Rc Xi Ky Tr X₀ X} (e : P = P')
    (T : ThreadsP F Bk P w₀ rc x k R) : (ThreadsP.ofEq e T).I₁ = T.I₁ := by
  subst e
  rfl

theorem ThreadsP.ofEq_I₂ {P P' : Prover W₀ Rc Xi Ky Tr X₀ X} (e : P = P')
    (T : ThreadsP F Bk P w₀ rc x k R) : (ThreadsP.ofEq e T).I₂ = T.I₂ := by
  subst e
  rfl

theorem ThreadsP.ofEq_I₃ {P P' : Prover W₀ Rc Xi Ky Tr X₀ X} (e : P = P')
    (T : ThreadsP F Bk P w₀ rc x k R) : (ThreadsP.ofEq e T).I₃ = T.I₃ := by
  subst e
  rfl

/-- **Under the premise ring**: what stands at H stands at G.prover H, in the form that RowDebtsP.threads takes. -/
theorem threadsP_at_ring {G : Sides F Bk W₀ Rc Ky Tr X₀ X} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    (ring : G.prover H = H) (T : ThreadsP F Bk H w₀ rc x k R) :
    ∃ T' : ThreadsP F Bk (G.prover H) w₀ rc x k R, T'.I₁ = T.I₁ ∧ T'.I₂ = T.I₂ ∧ T'.I₃ = T.I₃ :=
  ⟨ThreadsP.ofEq ring.symm T, ThreadsP.ofEq_I₁ _ T, ThreadsP.ofEq_I₂ _ T, ThreadsP.ofEq_I₃ _ T⟩

/-! ## OnAtRun at invariants by name -/

section Named
variable {G : Sides F Bk W₀ Rc Ky Tr X₀ X} {H : Prover W₀ Rc Xi Ky Tr X₀ X}

/-- **OnAtRun₁ at a family of invariants by name**: its text, with I for T.I₁. At a value T it is OnAtRun₁ T by rfl. -/
def OnAtRunAt₁ (G : Sides F Bk W₀ Rc Ky Tr X₀ X) (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc)
    (x : Xi) (k : Coins Bk) (I : Nat → Coins Bk → F.S₁ → Mid (Local W₀ Rc Xi Tr) X → Env → Prop)
    (ρ : Draws) (r : RunC F)
    (L : Lettered Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) : Prop :=
  ∀ σ, L.side F.first.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t, F.first.blocksInOrder = pre ++ σ.block :: t →
    ∀ m ca, InsideOf .own Bk 0 (G.prover H).first σ.block (I pre.length) (σ.roundsTo u.number) k m
      (envOf (H.storedWords w₀ rc) (fun _ _ => none)
        (r.run.played.1.take ((pre.flatMap (·.rounds)).length + σ.roundsTo u.number))) →
    m.seen = roundsOf (r.run.played.1.take ((pre.flatMap (·.rounds)).length + σ.roundsTo u.number)) →
    carriedAt Bk k 0 ⟨L.place, u.number⟩ u.part = .ok ca →
    r.called ⟨L.place, u.number⟩ = true →
    orRefused (midAtW F Bk (G.prover H) w₀ rc x k ρ ⟨L.place, u.number⟩) = .ok m →
    (laidOf F ρ (r.run.played.1.take ((pre.flatMap (·.rounds)).length + σ.roundsTo u.number)) [] []).front 0
        (storedShown (H.storedWords w₀ rc) (storedAsks F ρ)) =
      r.run.beforeAt (storedShown (H.storedWords w₀ rc) r.run.storedAsked) ⟨L.place, u.number⟩ →
    L.On u ca m ((laidOf F ρ
      (r.run.played.1.take ((pre.flatMap (·.rounds)).length + σ.roundsTo u.number)) [] []).front 0
        (storedShown (H.storedWords w₀ rc) (storedAsks F ρ)))

/-- **The same at the shared chain.** -/
def OnAtRunAt₂ (G : Sides F Bk W₀ Rc Ky Tr X₀ X) (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc)
    (x : Xi) (k : Coins Bk) (I : Nat → Coins Bk → F.S₂ → Mid (Common W₀ Rc Ky) X₀ → Env → Prop)
    (ρ : Draws) (r : RunC F)
    (L : Lettered Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky) : Prop :=
  ∀ σ, L.side F.shared.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t,
    F.shared.blocksInOrder = pre ++ σ.block :: t →
    ∀ m ca, InsideOf .shared Bk 1 (G.prover H).shared σ.block (I pre.length) (σ.roundsTo u.number)
      k m (envOf (H.storedWords w₀ rc) (fun _ _ => none)
        (r.run.played.2.1.take ((pre.flatMap (·.rounds)).length + σ.roundsTo u.number))) →
    m.seen =
      roundsOf (r.run.played.2.1.take ((pre.flatMap (·.rounds)).length + σ.roundsTo u.number)) →
    carriedAt Bk k 1 ⟨L.place, u.number⟩ u.part = .ok ca →
    r.called ⟨L.place, u.number⟩ = true →
    orRefused (midSharedAtW F Bk (G.prover H) w₀ rc x k ρ ⟨L.place, u.number⟩) = .ok m →
    (laidOf F ρ [] (r.run.played.2.1.take ((pre.flatMap (·.rounds)).length + σ.roundsTo u.number))
        []).front 1 (storedShown (H.storedWords w₀ rc) (storedAsks F ρ)) =
      r.run.beforeAt (storedShown (H.storedWords w₀ rc) r.run.storedAsked) ⟨L.place, u.number⟩ →
    L.On u ca m ((laidOf F ρ []
      (r.run.played.2.1.take ((pre.flatMap (·.rounds)).length + σ.roundsTo u.number)) []).front 1
        (storedShown (H.storedWords w₀ rc) (storedAsks F ρ)))

/-- **The same at the second chain.** -/
def OnAtRunAt₃ (G : Sides F Bk W₀ Rc Ky Tr X₀ X) (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc)
    (x : Xi) (k : Coins Bk) (I : Nat → Coins Bk → F.S₃ → Mid (Local W₀ Rc Xi Tr) X → Env → Prop)
    (ρ : Draws) (r : RunC F)
    (L : Lettered Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) : Prop :=
  ∀ σ, L.side F.second.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t,
    F.second.blocksInOrder = pre ++ σ.block :: t →
    ∀ m ca, InsideOf .own Bk 2 (G.prover H).second σ.block (I pre.length) (σ.roundsTo u.number) k m
      (envOf (H.storedWords w₀ rc) (taken₃ r.run.played.1 r.run.played.2.1)
        (r.run.played.2.2.take ((pre.flatMap (·.rounds)).length + σ.roundsTo u.number))) →
    m.seen = roundsOf r.run.played.1 ++ roundsOf r.run.played.2.1 ++
      roundsOf (r.run.played.2.2.take ((pre.flatMap (·.rounds)).length + σ.roundsTo u.number)) →
    carriedAt Bk k 2 ⟨L.place, u.number⟩ u.part = .ok ca →
    r.called ⟨L.place, u.number⟩ = true →
    orRefused (midAtW F Bk (G.prover H) w₀ rc x k ρ ⟨L.place, u.number⟩) = .ok m →
    (laidOf F ρ r.run.played.1 r.run.played.2.1
        (r.run.played.2.2.take ((pre.flatMap (·.rounds)).length + σ.roundsTo u.number))).front 2
        (storedShown (H.storedWords w₀ rc) (storedAsks F ρ)) =
      r.run.beforeAt (storedShown (H.storedWords w₀ rc) r.run.storedAsked) ⟨L.place, u.number⟩ →
    L.On u ca m ((laidOf F ρ r.run.played.1 r.run.played.2.1
      (r.run.played.2.2.take ((pre.flatMap (·.rounds)).length + σ.roundsTo u.number))).front 2
        (storedShown (H.storedWords w₀ rc) (storedAsks F ρ)))

theorem onAtRun₁_ofEq {P : Prover W₀ Rc Xi Ky Tr X₀ X} (e : P = G.prover H) (T : ThreadsP F Bk P w₀ rc x k R)
    {ρ : Draws} {r : RunC F} {L : Lettered Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    (h : OnAtRunAt₁ G H w₀ rc x k T.I₁ ρ r L) : OnAtRun₁ (G := G) (H := H) (ThreadsP.ofEq e T) ρ r L := by
  have a : OnAtRunAt₁ G H w₀ rc x k (ThreadsP.ofEq e T).I₁ ρ r L := by
    rw [ThreadsP.ofEq_I₁]
    exact h
  exact a

theorem onAtRun₂_ofEq {P : Prover W₀ Rc Xi Ky Tr X₀ X} (e : P = G.prover H) (T : ThreadsP F Bk P w₀ rc x k R)
    {ρ : Draws} {r : RunC F} {L : Lettered Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky}
    (h : OnAtRunAt₂ G H w₀ rc x k T.I₂ ρ r L) : OnAtRun₂ (G := G) (H := H) (ThreadsP.ofEq e T) ρ r L := by
  have a : OnAtRunAt₂ G H w₀ rc x k (ThreadsP.ofEq e T).I₂ ρ r L := by
    rw [ThreadsP.ofEq_I₂]
    exact h
  exact a

theorem onAtRun₃_ofEq {P : Prover W₀ Rc Xi Ky Tr X₀ X} (e : P = G.prover H) (T : ThreadsP F Bk P w₀ rc x k R)
    {ρ : Draws} {r : RunC F} {L : Lettered Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    (h : OnAtRunAt₃ G H w₀ rc x k T.I₃ ρ r L) : OnAtRun₃ (G := G) (H := H) (ThreadsP.ofEq e T) ρ r L := by
  have a : OnAtRunAt₃ G H w₀ rc x k (ThreadsP.ofEq e T).I₃ ρ r L := by
    rw [ThreadsP.ofEq_I₃]
    exact h
  exact a

/-- **The field threads of RowDebtsP, from its parts**: a value of ThreadsP at H, its invariants by name, and each list's On at those invariants, give the field at G.prover H. -/
theorem threads_of_named {Rel : W₀ → Rc → Xi → Prop} (ring : G.prover H = H)
    (I₁ : W₀ → Rc → Xi → (k : Coins Bk) → Ready W₀ Rc Xi Ky Tr X₀ X → Nat → Coins Bk → F.S₁ →
      Mid (Local W₀ Rc Xi Tr) X → Env → Prop)
    (I₂ : W₀ → Rc → Xi → (k : Coins Bk) → Ready W₀ Rc Xi Ky Tr X₀ X → Nat → Coins Bk → F.S₂ →
      Mid (Common W₀ Rc Ky) X₀ → Env → Prop)
    (I₃ : W₀ → Rc → Xi → (k : Coins Bk) → Ready W₀ Rc Xi Ky Tr X₀ X → Nat → Coins Bk → F.S₃ →
      Mid (Local W₀ Rc Xi Tr) X → Env → Prop)
    (named : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk H w₀ rc x k = .ok R →
      ∃ T : ThreadsP F Bk H w₀ rc x k R, T.I₁ = I₁ w₀ rc x k R ∧ T.I₂ = I₂ w₀ rc x k R ∧
        T.I₃ = I₃ w₀ rc x k R ∧ ∀ ρ r, ρ.due F = true → silentAt F H w₀ rc x ρ = none →
          runC F Bk H w₀ rc x k ρ = .ok r →
          (∀ L ∈ G.first, OnAtRunAt₁ G H w₀ rc x k (I₁ w₀ rc x k R) ρ r L) ∧
          (∀ L ∈ G.shared, OnAtRunAt₂ G H w₀ rc x k (I₂ w₀ rc x k R) ρ r L) ∧
          ∀ L ∈ G.second, OnAtRunAt₃ G H w₀ rc x k (I₃ w₀ rc x k R) ρ r L) :
    ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      ∃ T : ThreadsP F Bk (G.prover H) w₀ rc x k R, ∀ ρ r, ρ.due F = true →
        silentAt F (G.prover H) w₀ rc x ρ = none →
        runC F Bk (G.prover H) w₀ rc x k ρ = .ok r →
        (∀ L ∈ G.first, OnAtRun₁ (G := G) (H := H) T ρ r L) ∧
        (∀ L ∈ G.shared, OnAtRun₂ (G := G) (H := H) T ρ r L) ∧
        ∀ L ∈ G.second, OnAtRun₃ (G := G) (H := H) T ρ r L := by
  intro w₀ rc x h k R hR
  rw [ring] at hR
  obtain ⟨T, e₁, e₂, e₃, on⟩ := named w₀ rc x h k R hR
  refine ⟨ThreadsP.ofEq ring.symm T, fun ρ r hρ hs hr => ?_⟩
  rw [ring] at hs hr
  obtain ⟨o₁, o₂, o₃⟩ := on ρ r hρ hs hr
  exact ⟨fun L hL => onAtRun₁_ofEq ring.symm T (e₁ ▸ o₁ L hL),
    fun L hL => onAtRun₂_ofEq ring.symm T (e₂ ▸ o₂ L hL),
    fun L hL => onAtRun₃_ofEq ring.symm T (e₃ ▸ o₃ L hL)⟩

end Named

end ProofFile.Honest

#print axioms ProofFile.Honest.ThreadsP.ofEq
#print axioms ProofFile.Honest.ThreadsP.ofEq_I₁
#print axioms ProofFile.Honest.threadsP_at_ring
#print axioms ProofFile.Honest.onAtRun₁_ofEq
#print axioms ProofFile.Honest.onAtRun₂_ofEq
#print axioms ProofFile.Honest.onAtRun₃_ofEq
#print axioms ProofFile.Honest.threads_of_named
