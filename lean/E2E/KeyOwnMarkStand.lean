-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyOwnMarkStand.lean: `OwnMark` at a stand of the last thread at border 2, at a letter that says `saidLast`, with no premise on the marks: the claims from
`claims_of_fold`, the samples from `lotSamplesDense`. `fits_door` is the hostile reader's probe of that theorem, taken as it stands
(a file not in this library). The reader's L2: `mark_at_two`'s premise `hstart`, for all letters ends, is not what `lotSamplesDense` pays; this file
speaks of the first state that the letter names.

  `fits_door`, `mark_door`: the marks at the state that the door names.
  `mark_stand`: at border 2.

Nothing on soundness, completeness, hiding or binding.
-/
import E2E.KeyOwnSayStand
import E2E.KeyFirstMarks
import E2E.LotSamplesDense
import Johnson.Desc.Third.Law.AtDoor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.KeyLastChain
open VerifiableInference.Desc (OpenedColumn)
open VerifiableInference.Desc.Ground.Sh (claimsAtB)
open VerifiableInference.Desc.Key (Source LaterPlaces descriptionFromSource Xi thirdPar)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Third.Law (ok_of_bind some_of_named start₃E_inv start₃_inv)
open AtPublicFiles.KeyLastThread (start_key handOf)
open AtPublicFiles.AtFiles (KeySourced ThirdShaped sh₃ SF)
open AtPublicFiles.AtFiles.Full (A0 public_first_sourced)
open ProofFile.Honest

/-- **The hostile reader's probe of `lotSamplesDense`.** -/
theorem fits_door {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
    (hs : KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true) (x : Xi)
    (r₁ r₂ : List Fmt.RoundView) (c₁ c₂ : List OpenedColumn) (e₁ : (descriptionFromSource Xs N Pl).S₁) (e₂ : (descriptionFromSource Xs N Pl).S₂)
    (v₀ : (descriptionFromSource Xs N Pl).S₃) (D : DoorAt (descriptionFromSource Xs N Pl) x r₁ r₂ c₁ c₂ e₁ e₂ v₀) :
    SamplesDense (v₀ : S₃).st ∧ ∀ b, (v₀ : S₃).loc.border = some b → SamplesDense b.shared.st := by
  have h1 := (AtPublicFiles.KeyLastChain.Lots.lotSamplesDense Xs N Pl hs scope x r₁ c₁).1 _ _ _ D.fold₁
  have h2 := (AtPublicFiles.KeyLastChain.Lots.lotSamplesDense Xs N Pl hs scope x r₂ c₂).2 _ _ _ D.fold₂
  have hst := D.start
  obtain ⟨l, _, hst⟩ := ok_of_bind hst
  obtain ⟨e, he, hst⟩ := ok_of_bind hst
  obtain ⟨f, hf, h3⟩ := start₃E_inv _ _ _ _ _ _ _ _ _ _ _ hst
  obtain ⟨_, _, rfl⟩ := start₃_inv _ _ _ _ h3
  have he' := some_of_named he
  have hfs : f.st = (e₁ : VerifiableInference.Desc.Key.FirstState).d.st := by
    unfold VerifiableInference.Desc.Third.firstOutFrom at hf
    split at hf
    · dsimp only at hf
      split at hf
      · split at hf
        · cases hf; rfl
        · cases hf
      · cases hf
    · cases hf
  have hes : e.st = (e₂ : _root_.Desc.K14.St).st := by
    unfold _root_.Desc.K14.ended at he'
    dsimp only at he'
    split at he'
    · cases he'; rfl
    · cases he'
  refine ⟨?_, ?_⟩
  · show SamplesDense f.st
    rw [hfs]; exact h1
  · intro b hb
    obtain rfl := Option.some.inj hb
    show SamplesDense e.st
    rw [hes]; exact h2

/-- **The marks at the state that the door names.** -/
theorem mark_door {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
    (hs : KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true) (x : Xi)
    (r₁ r₂ : List Fmt.RoundView) (c₁ c₂ : List OpenedColumn) (e₁ : (descriptionFromSource Xs N Pl).S₁) (e₂ : (descriptionFromSource Xs N Pl).S₂)
    (v₀ : (descriptionFromSource Xs N Pl).S₃) (D : DoorAt (descriptionFromSource Xs N Pl) x r₁ r₂ c₁ c₂ e₁ e₂ v₀) : OwnMark v₀ := by
  obtain ⟨s₁, s₂⟩ := fits_door hs scope x r₁ r₂ c₁ c₂ e₁ e₂ v₀ D
  obtain ⟨bw, hw, -, -, -⟩ := public_first_sourced hs scope
  obtain ⟨l, hl, hc⟩ := claims_of_fold _ Xs.Y.D.1 Xs.Y.told.1 N bw hw D.fold₁
  obtain ⟨h, o, hh, -, hst⟩ := (start_key Xs N Pl _ _ _ v₀).1 D.start
  have hh' : (e₁ : VerifiableInference.Desc.Key.FirstState).lin.map (handOf e₁) = some h := hh
  rw [hl] at hh'
  obtain rfl := Option.some.inj hh'
  obtain ⟨-, -, -, -, est, -, -, eown, -⟩ := K14.start_gives (thirdPar Xs.chains) _ o v₀ hst
  refine ⟨?_, s₁, s₂⟩
  rw [est, eown]
  exact hc

/-- **The marks at border 2.** -/
theorem mark_stand {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces} {Bk : ProverCoinCounts} {W₀ Rc Tr Y : Type}
    {T₃ : Thread Bk (descriptionFromSource Xs N Pl).S₃ (descriptionFromSource Xs N Pl).Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y Xi}
    {v : S₃ → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool}
    (hs : KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true) (hbs : T₃.bs = (descriptionFromSource Xs N Pl).second.blocksInOrder)
    (hZ : ThirdShaped T₃ v A0) (hfun : ∀ k w h s s', T₃.begun k w h s → T₃.begun k w h s' → s = s')
    {k : Coins Bk} {st : S₃} {m : Mid (Local W₀ Rc Xi Tr) Y} {E : Env} (hT : Thr T₃ 2 k st m E)
    (hS : saidLast (descriptionFromSource Xs N Pl) T₃ 2 k m) : OwnMark st := by
  obtain ⟨r₁, r₂, c₁, c₂, e₁, e₂, v₀, -, -, D, hb⟩ := hS (Nat.le_refl 2)
  obtain ⟨s₀, rs, gs, hbeg, hdec⟩ := two_steps hbs hT
  obtain rfl : s₀ = v₀ := hfun _ _ _ _ _ hbeg hb
  have hsh₀ : sh₃ SF s₀ = A0 := by
    have q := hZ.first _ _ _ _ hT.2.2.2.2.2.2 hbeg
    obtain ⟨-, -, hlin, -⟩ := AtPublicFiles.AtFiles.Full.first_of_sourced hs scope fun _ _ _ _ => true
    have hS' : Xs.chains.made.sized.key.once.shape = SF := hlin.symm.trans (AtPublicFiles.AtFiles.Full.six_sourced hs scope).lin
    have q' : sh₃ Xs.chains.made.sized.key.once.shape s₀ = A0 := q
    rw [hS'] at q'
    exact q'
  exact second_mark (Cl := Unit) _ s₀ st rs gs hdec (fresh_of_shape hsh₀) (mark_door hs scope _ _ _ _ _ _ _ _ D)

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.fits_door
#print axioms AtPublicFiles.KeyLastChain.mark_door
#print axioms AtPublicFiles.KeyLastChain.mark_stand
