-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/TheCrossingCast.lean: whatever holds of the value of ThreadsP at a run holds of that
value at the return's own description.

A house that speaks of threadsAtRelation (TheCrossing.lean) states its sentence at the description by
name, h.description, and at the value TheThreadsHalf.threads, whose invariants are the three threads
by rfl. threadsP_at_of carries a sentence across the cast; threadsAtRelation_of does so at a run.
-/
import AtFullSide.Honest.TheCrossing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.Honest
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (matrixFilling tableCoins)
open AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm
open VerifierAndGoals (PublicFiles readFiles)

/-- **Every statement on a value crosses with it.** -/
theorem threadsP_at_of {Xi W₀ Rc Ky Tr X₀ X : Type} {F F' : VerifiableInference.Desc.FileDescription Xi}
    {Bk : ProverCoinCounts} {H H' : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ w₀' : W₀} {rc rc' : Rc} {x : Xi}
    {k k' : Coins Bk} {R : Ready W₀ Rc Xi Ky Tr X₀ X} (eF : F = F') (eH : H = H') (ew : w₀ = w₀')
    (er : rc = rc') (ek : k = k') {T : ThreadsP F Bk H w₀ rc x k R}
    {Q : ∀ (F₀ : VerifiableInference.Desc.FileDescription Xi) (H₀ : Prover W₀ Rc Xi Ky Tr X₀ X) (w : W₀)
      (r : Rc) (c : Coins Bk), ThreadsP F₀ Bk H₀ w r x c R → Prop}
    (hq : Q F H w₀ rc k T) : Q F' H' w₀' rc' k' (threadsP_at eF eH ew er ek T) := by
  subst eF eH ew er ek
  exact hq

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

variable {Z : PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} {h : HeadAtReturn Z A}
  {pp : Inst.Model.ScalesAndPolicy} {hr : readFiles Z = .ok pp}

/-- **A sentence at the run's value is a sentence at threadsAtRelation.** Q is stated over the
description, the prover, the input and the coins, so that a house states it once at each run. -/
theorem TheThreadsHalf.threadsAtRelation_of
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (O : TheThreadsHalf h hr)
    (G : Sides A.F A.B FullSizeMatrix IndexCommitterCoins OnBytes.TableKey Cells Unit Unit) (hP : G.prover A.H = A.H)
    {Rel : FullSizeMatrix → IndexCommitterCoins → ProofFile.Inst → Prop}
    (hRel : ∀ w₀ rc x, Rel w₀ rc x → ∃ n w, w.1 = w₀ ∧ tableCoins Z w.2.1 = rc ∧
      TiedRequest h hr n w x)
    (w₀ : FullSizeMatrix) (rc : IndexCommitterCoins) (x : ProofFile.Inst) (hx : Rel w₀ rc x) (k : Coins A.B)
    (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit)
    (hR : ProofFile.Honest.ready A.F A.B (G.prover A.H) w₀ rc x k = .ok R)
    {Q : ∀ (F₀ : VerifiableInference.Desc.FileDescription ProofFile.Inst)
      (H₀ : Prover FullSizeMatrix IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit) (w : FullSizeMatrix) (r : IndexCommitterCoins)
      (c : Coins A.B), ThreadsP F₀ A.B H₀ w r x c R → Prop}
    (hq : ∀ n w (c : CoinG A.B RunValue RunValue) (ht : TiedRequest h hr n w x)
      (hR' : ProofFile.Honest.ready h.description A.B A.H w.1 (tableCoins Z w.2.1) x (pursesOf c) = .ok R),
      Q h.description A.H w.1 (tableCoins Z w.2.1) (pursesOf c)
        (O.threads made ⟨n, w, x, c, R, ht, hR'⟩)) :
    Q A.F (G.prover A.H) w₀ rc k (O.threadsAtRelation made G hP hRel w₀ rc x hx k R hR) :=
  threadsP_at_of _ _ _ _ _ (hq _ _ _ _ _)

end AtFullSide.Honest

#print axioms AtFullSide.Honest.threadsP_at_of
#print axioms AtFullSide.Honest.TheThreadsHalf.threadsAtRelation_of
