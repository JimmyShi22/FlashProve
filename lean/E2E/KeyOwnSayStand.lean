-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyOwnSayStand.lean: two pieces toward the clause `say` of `OwnAsks` at a stand of the last thread at border 2.

  `two_steps`: a stand at border 2 is the first member's yes from the chain's first state (the second leaves the state).
  `members_A2`: the own group's members at the written shape: a closed line that can say no.

What stays open. `say_stand`, the clause itself, is not here yet: it wants Omega's sample sentence at the letters Nm.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.KeyLastEvOwn
import E2E.KeyOwnSamples
import E2E.KeyOwnSay
import E2E.KeyOwnFront

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.KeyLastChain
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (TableKey Part Oracle Group)
open OnBytes.Means (Words Says tableSize RowOn layoutOf)
open OnBytes.Slice (GE rdE readE begun)
open VerifiableInference.Desc (Block Place Wit OpenedColumn Strs foldBlocks foldBlocks_cons_ok step_iff)
open VerifiableInference.Desc.Ground.Sh (stTidyB tidy_of stSh grpSh grp_get)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.K12 (T12)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open VerifiableInference.Desc.Third (S₃ batchLinearConstraintsSecondPart takenSources Border)
open VerifiableInference.Desc.Third.Law (RowsHold says_congr law_k14Second takenSources_same)
open VerifiableInference.Desc.Last (ItemL)
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces descriptionFromSource thirdPar valOf RowHolds ownTest
  rowHolds_iff_says_of_rowIn)
open _root_.Desc.K14 (St)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeyThread (KeyFill)
open AtPublicFiles.AtFiles (KeySourced ThirdShaped Sh₃ sh₃ SF)
open AtPublicFiles.AtFiles.Full (A0)
open Johnson.RunOne.KeyRows1 (plan₁)

/-- **The own group's members at the written shape.** -/
theorem members_A2 : (A2.1.st.groups[A2.2.own]?).map (·.members) = some [0, 9, A2.2.omega] := by decide +kernel

/-- **A stand at border 2 is the first member's yes.** -/
theorem two_steps {Xs : Source} {Nr : H2U.PlaceNums} {Pl : LaterPlaces} {Bk : ProverCoinCounts} {V W Y Pb : Type}
    {T₃ : Thread Bk (descriptionFromSource Xs Nr Pl).S₃ (descriptionFromSource Xs Nr Pl).Cl V W Y Pb} (hbs : T₃.bs = (descriptionFromSource Xs Nr Pl).second.blocksInOrder)
    {k : Coins Bk} {st : S₃} {m : Mid W Y} {E : Env} (hT : Thr T₃ 2 k st m E) :
    ∃ s₀ rs gs, T₃.begun k m.st.input (m.st.heard.take T₃.front) s₀ ∧
      (batchLinearConstraintsSecondPart (Cl := Unit) (thirdPar Xs.chains)).decide s₀ rs gs = .ok st := by
  obtain ⟨-, -, -, -, s₀, cols, hbeg, -, hf⟩ := hT.2.2.2.2.1
  obtain ⟨b₀, b₁, e, d₀, d₁⟩ : ∃ b₀ b₁, (descriptionFromSource Xs Nr Pl).second.blocksInOrder.take 2 = [b₀, b₁] ∧
      b₀.decide = (batchLinearConstraintsSecondPart (Cl := Unit) (thirdPar Xs.chains)).decide ∧
      b₁.decide = (takenSources (ownTest Pl) : Block S₃ Unit).decide := ⟨_, _, rfl, rfl, rfl⟩
  rw [hbs, e] at hf
  obtain ⟨-, s₁, _, hs₁, h₁⟩ := foldBlocks_cons_ok.1 hf
  obtain ⟨-, s₂, _, hs₂, h₂⟩ := foldBlocks_cons_ok.1 h₁
  have hy₁ := ((step_iff _ b₀ s₀ s₁ _ _ _).1 hs₁).2.1
  have hy₂ := ((step_iff _ b₁ s₁ s₂ _ _ _).1 hs₂).2.1
  rw [d₀] at hy₁
  rw [d₁] at hy₂
  have e₂ : s₂ = s₁ := takenSources_same _ s₁ s₂ _ _ hy₂
  have q : (Except.ok (s₂, _, _) : Except String (S₃ × List Fmt.RoundView × List OpenedColumn)) = .ok (st, [], []) := h₂
  have e₃ : s₂ = st := (Prod.mk.inj (Except.ok.inj q)).1
  have e₄ : s₁ = st := e₂.symm.trans e₃
  rw [e₄] at hy₁
  exact ⟨s₀, _, _, hbeg, hy₁⟩

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.members_A2
#print axioms AtPublicFiles.KeyLastChain.two_steps
