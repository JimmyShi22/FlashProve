--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyShapeThirdStart.lean: THE KEY FILE's THIRD CHAIN's FIRST SHAPE, IN THE GOALS' SCOPE: where a
`Thread` over the first chain stands at that chain's last border and one over the shared chain at
that chain's last border, the description's own start of the third chain returns at the two states,
and what it returns has ONE WRITTEN SHAPE. A join: calls. Steps of the verifier's: NOTHING IS SHOWN
OF ANY PROVER.

  `shape19_of_thr`: at the first chain's border 19 the state's shape is `T19`
    (E2E/KeyShapeAtFull.lean).
  `len₂_sourced`: in scope the shared chain has twelve sub-protocols.
  **`shape₂_of_thr`**: at a border b of the shared chain, b at most 12, the state's shape is what
    the guards' run over the first b returns. **`shape12_of_thr`**: at 12 it is `V12`
    (E2E/KeyShapeSharedFull.lean). By the frame's `shape_at`: CALLED.
  **`start₃_of_shapes`**: at two states of these two shapes the description's start of the third
    chain returns, and the shape of what it returns is the written `X0`. By E2E/KeyShapeDoor.lean's
    `door_returns` and E2E/KeyShapeFirstEnd.lean's `door_at`: CALLED.
  **`start₃_of_thr`**: so at the two threads' last states.

Limits.
- That a `Thread` stands at either border is a premise; that one stands anywhere is shown nowhere
  here.
- The premises on the two threads: each one's list is its chain's; each begins at the description's
  start alone; at the shared chain: at an instance whose key's sizes fit.
- Nothing on the third chain's own sub-protocols.


-/
import E2E.KeyShapeSharedTies
import E2E.KeyShapeFullSourced

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.AtFiles.Full
open OnBytes OnBytes.Params AtPublicFiles.AtFiles AtPublicFiles.KeyShape
open ProofFile.Honest AtPublicFiles.KeyLink
open VerifiableInference.Desc.Own (keyFits)
open VerifiableInference.Desc.Key (FirstState Source LaterPlaces)
open _root_.Desc.K14 (St)

variable {Z : VerifierAndGoals.PublicFiles} {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}
  {V W Xh Pb : Type} {Bk : ProverCoinCounts}

/-- At the first chain's last border the state's shape is the run's last term. -/
theorem shape19_of_thr (hs : KeySourced Z X N P) (scope : VerifierAndGoals.InScope Z = true)
    (T₁ : Thread Bk (keyFileDescription X N P).S₁ (keyFileDescription X N P).Cl V W Xh Pb)
    (hbs : T₁.bs = (keyFileDescription X N P).first.blocksInOrder)
    (hbeg : ∀ k w h s₀, T₁.valid w → T₁.begun k w h s₀ → ∃ x, s₀ = (keyFileDescription X N P).start₁ x)
    {k : Coins Bk} {e₁ : (keyFileDescription X N P).S₁} {m : Mid W Xh} {E : Env} (h : Thr T₁ 19 k e₁ m E) :
    sh₁B (pubOf X) CF e₁ = T19 := by
  obtain ⟨-, -, -, hlen, hsh0, hrun, hyes, -⟩ := first_of_sourced hs scope fun _ _ _ _ => true
  obtain ⟨bw, hw, he, ha, -⟩ := public_first_sourced hs scope
  have h19 := shape_at T₁ (Z₁W (pubOf X) CF X.Y.D.1 X.Y.told.1 N fun _ _ _ _ => true) (a₀ := T0)
    (n := 19) (b := 19) (le_of_eq (by rw [hbs, hlen])) (Nat.le_refl _) hyes
    (fun k w h s₀ h1 h2 => by
      obtain ⟨x, rfl⟩ := hbeg k w h s₀ h1 h2
      exact (start₁_shape (cs := CF) (N := N) (X := X) (P := P) _ x).trans hsh0)
    (fun j => by
      rw [hbs]
      exact carries_whole₁ (pubOf X) CF X.Y.D.1 X.Y.told.1 N T₁.ft _ bw hw he ha j) h
  exact Except.ok.inj (h19.symm.trans hrun)

/-- In scope the shared chain has twelve sub-protocols. -/
theorem len₂_sourced (hs : KeySourced Z X N P) (scope : VerifierAndGoals.InScope Z = true) :
    (flat₂ X.chains P).length = 12 := by
  obtain ⟨layO, hQ⟩ := plan2_full
  obtain ⟨B⟩ := hQ.eight
  have h9 := pre_len₂ X.chains P (par_sourced hs scope) B
  obtain rfl := later_sourced hs scope
  rw [flat₂_cut, List.length_append, h9, omega_full]
  rfl

/-- **At a border of the shared chain the state's shape is what the guards' run returns there.** -/
theorem shape₂_of_thr (hs : KeySourced Z X N P) (scope : VerifierAndGoals.InScope Z = true)
    (v : Nat → St → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
    (T₂ : Thread Bk (keyFileDescription X N P).S₂ (keyFileDescription X N P).Cl V W Xh Pb)
    (hbs : T₂.bs = (keyFileDescription X N P).shared.blocksInOrder)
    (hbeg : ∀ k w h s₀, T₂.valid w → T₂.begun k w h s₀ →
      ∃ x, s₀ = (keyFileDescription X N P).start₂ x ∧ keyFits x.key QK.par.S.fold.index = true)
    {b : Nat} (hb : b ≤ 12) {k : Coins Bk} {e₂ : (keyFileDescription X N P).S₂} {m : Mid W Xh} {E : Env}
    (h : Thr T₂ b k e₂ m E) : (Z₂At X.chains P gK₂ v).run b V0 = .ok (sh₂ e₂) :=
  shape_at T₂ (Z₂At X.chains P gK₂ v) (a₀ := V0) (n := 12) (b := b)
    (le_of_eq (by rw [hbs]; exact (len₂_sourced hs scope).symm)) hb (yes₂_sourced hs scope v)
    (fun k w h s₀ h1 h2 => by
      obtain ⟨x, rfl, hk⟩ := hbeg k w h s₀ h1 h2
      exact first₂_shape hs scope x hk)
    (fun j => by
      rw [hbs]
      exact carries₂_sourced hs scope T₂.ft v j) h

/-- **At the shared chain's last border it is the run's last term.** -/
theorem shape12_of_thr (hs : KeySourced Z X N P) (scope : VerifierAndGoals.InScope Z = true)
    (T₂ : Thread Bk (keyFileDescription X N P).S₂ (keyFileDescription X N P).Cl V W Xh Pb)
    (hbs : T₂.bs = (keyFileDescription X N P).shared.blocksInOrder)
    (hbeg : ∀ k w h s₀, T₂.valid w → T₂.begun k w h s₀ →
      ∃ x, s₀ = (keyFileDescription X N P).start₂ x ∧ keyFits x.key QK.par.S.fold.index = true)
    {k : Coins Bk} {e₂ : (keyFileDescription X N P).S₂} {m : Mid W Xh} {E : Env}
    (h : Thr T₂ 12 k e₂ m E) : sh₂ e₂ = V12 :=
  Except.ok.inj ((shape₂_of_thr hs scope (fun _ _ _ _ => true) T₂ hbs hbeg (Nat.le_refl 12)
    h).symm.trans (run₂_sourced hs scope _))

/-- **AT TWO STATES OF THE TWO RUNS' LAST SHAPES THE THIRD CHAIN's START RETURNS, AND WHAT IT
RETURNS HAS THE WRITTEN SHAPE.** -/
theorem start₃_of_shapes (hs : KeySourced Z X N P) (scope : VerifierAndGoals.InScope Z = true)
    (x : (keyFileDescription X N P).XiPub) (e₁ : FirstState) (e₂ : St)
    (h1 : sh₁B (pubOf X) CF e₁ = T19) (h2 : sh₂ e₂ = V12) :
    ∃ s₃, (keyFileDescription X N P).start₃ x e₁ e₂ = .ok s₃ ∧
      X0 = some (sh₃ X.chains.made.sized.key.once.shape s₃) := by
  obtain ⟨-, hcs, hlin, -⟩ := first_of_sourced hs scope fun _ _ _ _ => true
  have h6 := six_sourced hs scope
  have hX : X0.isSome = true := door_full
  cases ht : doorS CF SF T19.1 T19.2.tidy T19.2.back.door (sharedOf V12) with
  | error w =>
    have q : X0 = none := by
      unfold X0
      rw [ht]
      rfl
    rw [q] at hX
    cases hX
  | ok t =>
    have q : X0 = some t := by
      unfold X0
      rw [ht]
      rfl
    have e := door_at (pubOf X) CF SF h6.lin e₁ (sharedSh e₂)
    have hb : sharedSh e₂ = sharedOf V12 := by
      rw [← h2]
      exact (sharedOf_eq e₂).symm
    rw [h1, hb, ht] at e
    have hS : X.chains.made.sized.key.once.shape = SF := hlin.symm.trans h6.lin
    obtain ⟨s₃, a, b⟩ := door_returns X N P x e₁ e₂ t (by
      rw [hcs, hS, hb]
      exact e.symm)
    exact ⟨s₃, a, by rw [q, b]⟩

/-- **So at the two threads' last states.** -/
theorem start₃_of_thr (hs : KeySourced Z X N P) (scope : VerifierAndGoals.InScope Z = true)
    (T₁ : Thread Bk (keyFileDescription X N P).S₁ (keyFileDescription X N P).Cl V W Xh Pb)
    (hbs₁ : T₁.bs = (keyFileDescription X N P).first.blocksInOrder)
    (hbeg₁ : ∀ k w h s₀, T₁.valid w → T₁.begun k w h s₀ → ∃ x, s₀ = (keyFileDescription X N P).start₁ x)
    (T₂ : Thread Bk (keyFileDescription X N P).S₂ (keyFileDescription X N P).Cl V W Xh Pb)
    (hbs₂ : T₂.bs = (keyFileDescription X N P).shared.blocksInOrder)
    (hbeg₂ : ∀ k w h s₀, T₂.valid w → T₂.begun k w h s₀ →
      ∃ x, s₀ = (keyFileDescription X N P).start₂ x ∧ keyFits x.key QK.par.S.fold.index = true)
    {k₁ k₂ : Coins Bk} {e₁ : (keyFileDescription X N P).S₁} {e₂ : (keyFileDescription X N P).S₂} {m₁ m₂ : Mid W Xh}
    {E₁ E₂ : Env} (a₁ : Thr T₁ 19 k₁ e₁ m₁ E₁) (a₂ : Thr T₂ 12 k₂ e₂ m₂ E₂)
    (x : (keyFileDescription X N P).XiPub) :
    ∃ s₃, (keyFileDescription X N P).start₃ x e₁ e₂ = .ok s₃ ∧
      X0 = some (sh₃ X.chains.made.sized.key.once.shape s₃) :=
  start₃_of_shapes hs scope x e₁ e₂ (shape19_of_thr hs scope T₁ hbs₁ hbeg₁ a₁)
    (shape12_of_thr hs scope T₂ hbs₂ hbeg₂ a₂)

end AtPublicFiles.AtFiles.Full

#print axioms AtPublicFiles.AtFiles.Full.shape19_of_thr
#print axioms AtPublicFiles.AtFiles.Full.len₂_sourced
#print axioms AtPublicFiles.AtFiles.Full.shape₂_of_thr
#print axioms AtPublicFiles.AtFiles.Full.shape12_of_thr
#print axioms AtPublicFiles.AtFiles.Full.start₃_of_shapes
#print axioms AtPublicFiles.AtFiles.Full.start₃_of_thr
