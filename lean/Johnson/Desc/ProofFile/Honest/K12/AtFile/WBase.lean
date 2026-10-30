-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WBase.lean: the five statements at the last chain's proximity test at
the thread that the library lays, at the base prover: the job is the filling's, and `LetterAtW` is paid.

  `five_at_base`   at a return of the maker at `onlineProverPartsInUse`: there is the filling's job, and at every
                   thread of `lastThread` whose trees taken over are `takenLast`, from `StandAtW` and
                   the two letters under the stand and the step: `FiveAt` at number 2
  `five_at_base_rest`   the same from what stays open, at a thread whose tables and counts are
                   WTable.lean's terms: `StandRest`, `WidthsAt`, the rounds in front

Limits.
- Over TheFirstThread.lean (the lot of ProofFile's heads), at its `lastThread h first reads parts w`.
- The job's readers are the filling's (`I`, `randAt`): `saysAt` has a payer only where `reads` and `first`
  are the same terms. The statement leaves them free: the spender lays them.
- `StandAtW` holds what stays open (WTable.lean's head lists who owes each clause).
- NOT IN FRONT OF A LAW OVER COINS. AT THE FILLING, NOT READ THROUGH.
- That a stand is reached is not said; where none is, the five say nothing.
- Nothing on completeness of the whole chain, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WLastThread
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFilling
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open ProofFile.Honest.K12
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12.Seat (enterOwn leaveOwn)
open VerifiableInference.Desc.Third (S₃)
open ProofFile.Honest.K12.AtProof (idleT12)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts IndexReaders LastThreadParts lastThread
  lastWitness)
open ToldDesc (ownAt)
open AtFullSide.K12 (jobAtFill)

variable {W₀ : Type}

/-- **The five at the base prover, at the thread that the library lays.** The job's readers are the
filling's: `saysAt` has a payer only where `reads` and `first` are the same terms. -/
theorem five_at_base {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (h : HeadAtReturn files A) (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A) :
    ∃ M, jobAtFill A.Z h.places h.firstChain I S O A.G = some M ∧
      ∀ (first : FirstThreadParts A) (reads : IndexReaders W₀ IndexCommitterCoins) (parts : LastThreadParts A)
        (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
        (Said : ℕ → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop),
        parts.taken = takenLast →
        StandAtW h.description (lastThread h first reads parts w) Said 2 M →
        (∀ k s m E ds y cols s', ThrS (lastThread h first reads parts w) Said 2 k s m E →
          drawsFit ((ownAt h.places).retype : Block S₃ ProofFile.Cl).rounds ds = true →
          (lastThread h first reads parts w).Stepped ((ownAt h.places).retype : Block S₃ ProofFile.Cl) k s
            m E ds y cols s' →
          parts.rides 3 y.2.st.input s' ∧ parts.keeps ⟨3, none, 2, .K12⟩ s s') →
        ∀ fl : ℕ → S₃ → List Fmt.Drawn → Option String,
          FiveAt (lastThread h first reads parts w) Said fl 2 := by
  obtain ⟨M, hM, hp, ⟨f, hf⟩, hl, hd, -, hL⟩ := letter_at_filling (Wt := ProofFile.Honest.FirstThread.WtF) h.head I S O hA
  refine ⟨M, hM, ?_⟩
  intro first reads parts w Said ht St hnext fl
  have H₀ : LetterAtW h.description (lastThread h first reads parts w) 2 M enterOwn leaveOwn
      ((ownAt h.places).retype : Block S₃ ProofFile.Cl) idleT12 := by
    unfold lastThread
    rw [ht]
    exact hL h.sharedNumbers parts.meaning h.lastMeaning h.lastForm
      (fun s => OnBytes.Means.InOrder s.st) parts.ends (lastWitness h first reads) parts.table
      parts.fixed 0 h.description.t₁ h.description.t₂
      (ProofFile.Honest.ReadyInput h.description A.H) parts.rides
      (ProofFile.Honest.K14.kpSecond (ToldDesc.p14At A.Z) parts.keeps) w
  exact five_at_lastThread h first reads parts w Said M hp f hf hl hd H₀ St hnext fl

/-- **The same from what stays open**, where the thread's trees taken over, tables and counts are the
terms of WTable.lean: `StandRest`, `WidthsAt`, the rounds in front. The job's readers are the
filling's: `saysAt` has a payer only where `reads` and `first` are the same terms. -/
theorem five_at_base_rest {W₂ : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (h : HeadAtReturn files A) (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A) :
    ∃ M, jobAtFill A.Z h.places h.firstChain I S O A.G = some M ∧
      ∀ (first : FirstThreadParts A) (reads : IndexReaders W₀ IndexCommitterCoins) (parts : LastThreadParts A)
        (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
        (Said : ℕ → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
        (r₁ n₀ : ℕ) (toCommon : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → W₂)
        (tb₁ : Fmt.TreeSource → Coins A.B → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → List Fmt.Drawn →
          VerifiableInference.Desc.Place × Table)
        (tb₂ : Fmt.TreeSource → Coins A.B → W₂ → List Fmt.Drawn →
          VerifiableInference.Desc.Place × Table)
        (fx₁ fx₂ : Fmt.TreeSource → ℕ) (own₀ : Unit),
        parts.taken = takenLast →
        parts.table = lastTable r₁ toCommon tb₁ tb₂ (ownLast M.toRun.toTest own₀ n₀) →
        parts.fixed = lastFixed r₁ fx₁ fx₂ (fun τ => n₀ + seedRound M.toRun.toTest.p.nums.stages τ) →
        n₀ = (lastThread h first reads parts w).front →
        WidthsAt r₁ toCommon tb₁ tb₂ →
        StandRest (Zp := A.Z) (Np := h.places) (cF := h.firstChain)
          (lastThread h first reads parts w) Said M →
        (∀ k s m E ds y cols s', ThrS (lastThread h first reads parts w) Said 2 k s m E →
          drawsFit ((ownAt h.places).retype : Block S₃ ProofFile.Cl).rounds ds = true →
          (lastThread h first reads parts w).Stepped ((ownAt h.places).retype : Block S₃ ProofFile.Cl) k s
            m E ds y cols s' →
          parts.rides 3 y.2.st.input s' ∧ parts.keeps ⟨3, none, 2, .K12⟩ s s') →
        ∀ fl : ℕ → S₃ → List Fmt.Drawn → Option String,
          FiveAt (lastThread h first reads parts w) Said fl 2 := by
  obtain ⟨M, hM, key⟩ := five_at_filling (Wt := ProofFile.Honest.FirstThread.WtF) (W₂ := W₂) h.head I S O hA
  refine ⟨M, hM, ?_⟩
  intro first reads parts w Said r₁ n₀ toCommon tb₁ tb₂ fx₁ fx₂ own₀ ht htb hfx hn hW R hnext fl
  have eT : lastThread h first reads parts w = lastAt (Zp := A.Z) (Np := h.places)
      (cF := h.firstChain) A.H h.sharedNumbers parts.meaning h.lastMeaning h.lastForm
      (fun s => OnBytes.Means.InOrder s.st) parts.ends (lastWitness h first reads) r₁ n₀ toCommon tb₁
      tb₂ fx₁ fx₂ M.toRun.toTest own₀ 0 h.description.t₁ h.description.t₂
      (ProofFile.Honest.ReadyInput h.description A.H) parts.rides
      (ProofFile.Honest.K14.kpSecond (ToldDesc.p14At A.Z) parts.keeps) w := by
    unfold lastThread
    rw [ht, htb, hfx]
  rw [eT] at hn R hnext ⊢
  refine key h.sharedNumbers parts.meaning h.lastMeaning h.lastForm parts.ends
    (lastWitness h first reads) r₁ n₀ toCommon tb₁ tb₂ fx₁ fx₂ own₀ 0 h.description.t₁
    h.description.t₂ (ProofFile.Honest.ReadyInput h.description A.H) parts.rides
    (ProofFile.Honest.K14.kpSecond (ToldDesc.p14At A.Z) parts.keeps) w Said (fillZ_is _ _) hn hW R ?_ fl
  intro k s m E ds y cols s' u hd hS
  obtain ⟨hr, hk⟩ := hnext k s m E ds y cols s' u hd hS
  refine ⟨hr, fun q hq => ?_⟩
  have e : VerifiableInference.Desc.Last.lastPlaces[2]? = some ⟨3, none, 2, .K12⟩ := rfl
  obtain rfl := Option.some.inj (hq.symm.trans e)
  show (if (⟨3, none, 2, .K12⟩ : VerifiableInference.Desc.Place) = ⟨3, none, 0, .K14⟩ then _ else _)
  rw [if_neg (by decide)]
  exact hk

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.five_at_base
#print axioms ProofFile.Honest.K12.AtFile.five_at_base_rest
