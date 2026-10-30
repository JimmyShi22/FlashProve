--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyFormKept.lean: HOW A CLAUSE THAT WAS LAID INTO A THREAD's SENTENCE IS PAID, AND THE FIRST
PAYMENTS AT THE KEY FILE. E2E/KeyThreadsLaid.lean lays clauses on the verifier's state into the
three threads (`withForm`); that moves them into the debts at the members (`Owes`,
Johnson/Desc/ProofFile/Honest/Thread/File.lean). Here these debts are split.

General.
  `StepKeeps U Φ b`: the own step of the sub-protocol number b keeps Φ: from Φ at the border b and
    the step's acceptance, Φ at the border b + 1. ON THE VERIFIER's STEP ALONE: no prover, no coin.
  `plays_withForm`, `exchange_withForm`, `ridesPast_withForm`: three of the four debts at a member
    pass from U to `withForm U Φ`: their premise gets stronger, and what they conclude does not read
    Φ.
  `behind_withForm`: the fourth (`Behind`) passes where the step keeps Φ.
  **`owes_withForm`**: so `Owes (withForm U Φ)` from `Owes U` and `StepKeeps U Φ` at every member.
At the key file's description `keyFileDescription X N P`.
  `listed_kept₁`, `listed_kept₂`, `listed_kept₃`: "every member of every group is listed" is kept by
    every sub-protocol's own step: `desc_listed` (E2E/KeyListed.lean) through the library's
    `step_decide`.
  **`form₁_kept`, `form₂_kept`**: ALL of `Form₁` (`Form₂`) is kept at every sub-protocol but the
    chain's last two: its other clauses speak at the chain's last two borders alone.
  **`form₃_kept`**: all of `Form₃` is kept at the third chain's sub-protocol number 1.

Limits.
- PAID: `Listed` at every sub-protocol of the three chains; the whole form at every sub-protocol but
  these. NOT PAID: at the last two of the first and of the shared chain, and at numbers 0, 2 and 3
  of the third: there a clause that speaks at the border behind has to be GIVEN by the step: nothing
  here does that.
- That the clauses hold in front of a chain's first sub-protocol (`Enters₁`, `Enters₂`,
  `DoorBehind`) is not treated.
- `Owes U` at the base threads stays owed.
- "Keeps" speaks of a step that has accepted: nothing on whether a step accepts.

-/
import E2E.KeyThreadsLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.KeyLink
open ProofFile.Honest

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-- **The own step of the sub-protocol number b keeps Φ.** -/
def StepKeeps (U : Thread Bk S Cl V W X Pb) (Φ : Nat → S → Prop) (b : Nat) : Prop :=
  ∀ blk, U.bs[b]? = some blk → ∀ s rs cols s' n, Φ b s →
    blk.step U.ft s rs cols = .ok (s', n) → Φ (b + 1) s'

variable {U : Thread Bk S Cl V W X Pb} {Φ : Nat → S → Prop} {b : Nat}

theorem plays_withForm (h : Plays U b) : Plays (withForm U Φ) b :=
  fun blk hb k s m E ds l hT => h blk hb k s m E ds l (thr_of_withForm hT)

theorem exchange_withForm (h : Exchange U b) : Exchange (withForm U Φ) b :=
  fun blk hb k s m E ds y cols s' hT => h blk hb k s m E ds y cols s' (thr_of_withForm hT)

theorem ridesPast_withForm (h : RidesPast U b) : RidesPast (withForm U Φ) b :=
  fun k s m E s' ps i v hT => h k s m E s' ps i v (thr_of_withForm hT)

/-- `Behind` passes where the step keeps Φ. -/
theorem behind_withForm (h : Behind U b) (hK : StepKeeps U Φ b) : Behind (withForm U Φ) b :=
  fun blk hb k s m E ds y cols s' hT hd hS =>
    have a := h blk hb k s m E ds y cols s' (thr_of_withForm hT) hd hS
    ⟨⟨a.1.1, a.1.2, hK blk hb s _ cols s' _ (thr_withForm hT) hS.2⟩, a.2.1, a.2.2⟩

/-- **The debts at the members, with the clause laid in.** -/
theorem owes_withForm (h : Owes U) (hK : ∀ b, b < U.bs.length → StepKeeps U Φ b) :
    Owes (withForm U Φ) :=
  fun b hb => ⟨plays_withForm (h b hb).1, behind_withForm (h b hb).2.1 (hK b hb),
    exchange_withForm (h b hb).2.2.1, ridesPast_withForm (h b hb).2.2.2⟩

end AtPublicFiles.KeyLink

namespace AtPublicFiles.AtFiles
open ProofFile.Honest AtPublicFiles.KeyLink
open VerifiableInference.Desc.Key (FirstState)

variable {W₀ Rc Ky Tr X₀ Xh : Type} {Bk : ProverCoinCounts} (X : VerifiableInference.Desc.Key.Source)
  (N : H2U.PlaceNums) (P : VerifiableInference.Desc.Key.LaterPlaces) (q : KeyNums)
  (U₁ : Thread Bk (keyFileDescription X N P).S₁ (keyFileDescription X N P).Cl (Local W₀ Rc KeyInst Tr)
    (Local W₀ Rc KeyInst Tr) Xh KeyInst)
  (U₂ : Thread Bk (keyFileDescription X N P).S₂ (keyFileDescription X N P).Cl Empty (Common W₀ Rc Ky) X₀ Ky)
  (U₃ : Thread Bk (keyFileDescription X N P).S₃ (keyFileDescription X N P).Cl (Local W₀ Rc KeyInst Tr)
    (Local W₀ Rc KeyInst Tr) Xh KeyInst)

/-- **`Listed` is kept by every step of the first chain.** -/
theorem listed_kept₁ (hbs : U₁.bs = (keyFileDescription X N P).first.blocksInOrder) (b : Nat) :
    StepKeeps U₁ (fun _ s => Listed (show FirstState from s).d.st) b :=
  fun blk hb s rs cols s' n h0 hs => by
    obtain ⟨rs', gs', hd⟩ := VerifiableInference.Desc.ChainEnd.step_decide _ blk s s' rs cols n hs
    rw [hbs] at hb
    exact (desc_listed X N P).1 blk (List.mem_of_getElem? hb) s rs' gs' s' hd h0

/-- Of the shared chain. -/
theorem listed_kept₂ (hbs : U₂.bs = (keyFileDescription X N P).shared.blocksInOrder) (b : Nat) :
    StepKeeps U₂ (fun _ s => Listed (show _root_.Desc.K14.St from s).st) b :=
  fun blk hb s rs cols s' n h0 hs => by
    obtain ⟨rs', gs', hd⟩ := VerifiableInference.Desc.ChainEnd.step_decide _ blk s s' rs cols n hs
    rw [hbs] at hb
    exact (desc_listed X N P).2.1 blk (List.mem_of_getElem? hb) s rs' gs' s' hd h0

/-- Of the third chain. -/
theorem listed_kept₃ (hbs : U₃.bs = (keyFileDescription X N P).second.blocksInOrder) (b : Nat) :
    StepKeeps U₃ (fun _ s => Listed s.st) b :=
  fun blk hb s rs cols s' n h0 hs => by
    obtain ⟨rs', gs', hd⟩ := VerifiableInference.Desc.ChainEnd.step_decide _ blk s s' rs cols n hs
    rw [hbs] at hb
    exact (desc_listed X N P).2.2 blk (List.mem_of_getElem? hb) s rs' gs' s' hd h0

/-- **All of `Form₁` is kept at every sub-protocol of the first chain but the last two.** -/
theorem form₁_kept (hbs : U₁.bs = (keyFileDescription X N P).first.blocksInOrder) (b : Nat)
    (hb : b + 2 < (keyFileDescription X N P).first.blocksInOrder.length) : StepKeeps U₁ (Form₁ X N P q) b :=
  fun blk hk s rs cols s' n h0 hs =>
    ⟨listed_kept₁ X N P U₁ hbs b blk hk s rs cols s' n h0.1 hs, fun e => by omega,
      fun e => by omega⟩

/-- **All of `Form₂` at every sub-protocol of the shared chain but the last two.** -/
theorem form₂_kept (hbs : U₂.bs = (keyFileDescription X N P).shared.blocksInOrder) (b : Nat)
    (hb : b + 2 < (keyFileDescription X N P).shared.blocksInOrder.length) : StepKeeps U₂ (Form₂ X N P q) b :=
  fun blk hk s rs cols s' n h0 hs =>
    ⟨listed_kept₂ X N P U₂ hbs b blk hk s rs cols s' n h0.1 hs, fun e => by omega,
      fun e => by omega⟩

/-- **All of `Form₃` at the third chain's sub-protocol number 1.** -/
theorem form₃_kept (hbs : U₃.bs = (keyFileDescription X N P).second.blocksInOrder) :
    StepKeeps U₃ (Form₃ X N P q) 1 :=
  fun blk hk s rs cols s' n h0 hs =>
    ⟨listed_kept₃ X N P U₃ hbs 1 blk hk s rs cols s' n h0.1 hs, fun e => by omega,
      fun e => by omega, fun e => by omega, fun e => by
        have l : (keyFileDescription X N P).second.blocksInOrder.length = 4 := rfl
        omega⟩

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.KeyLink.plays_withForm
#print axioms AtPublicFiles.KeyLink.exchange_withForm
#print axioms AtPublicFiles.KeyLink.ridesPast_withForm
#print axioms AtPublicFiles.KeyLink.behind_withForm
#print axioms AtPublicFiles.KeyLink.owes_withForm
#print axioms AtPublicFiles.AtFiles.listed_kept₁
#print axioms AtPublicFiles.AtFiles.listed_kept₂
#print axioms AtPublicFiles.AtFiles.listed_kept₃
#print axioms AtPublicFiles.AtFiles.form₁_kept
#print axioms AtPublicFiles.AtFiles.form₂_kept
#print axioms AtPublicFiles.AtFiles.form₃_kept
