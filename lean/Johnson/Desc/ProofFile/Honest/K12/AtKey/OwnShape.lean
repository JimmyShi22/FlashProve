-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/OwnShape.lean: the verifier's state in front of the key file's own
test has a shape that is a closed term. Steps of the verifier's: nothing is shown of any prover.

  `first_end_shape`   a fold over the whole first chain from the chain's start ends at the shape `T19`
  `shared_end_shape`  a fold over the whole shared chain from the chain's start, at a key that fits,
                      ends at the shape `V12`
  `start_shape`       so the last chain's start returns a state of the shape that `X0` holds
  `run_two`           the run on shapes over the last chain's first two blocks is `ZW`'s, in scope
  `stand_shape`       at a stand in front of the test the state has the shape of that run

Why it is so. Each chain's run on shapes returns at the written terms, and each block's accept carries its
shape: (B1), `carries_whole₁`, `carries₂_sourced`, `carries_all_in_scope`. The shape holds no field
element, so the term reads no run. The shapes `T19`, `V12` are evaluated at written public values: that
these are the public values of the files in scope is `first_of_sourced`, `run₂_sourced`.

By what. `shape_reach` (Thread/Shape.lean), `reach_of_fold`, `door_carries` (E2E/KeyShapeDoor.lean),
`door_at` (E2E/KeyShapeFirstEnd.lean), `first₂_shape`, `ownRounds_full`, `sized_sourced`.

Limits.
- In scope alone, at the full size.
- `shared_end_shape` and what stands on it ask that the key fits the sizes (`keyFits`): a premise.
- What a shape does not read (the values of rows, sample rows, tensors) is not said here.
- The folds are premises: a stand reaches them through `EndsAre` (K12/AtFile/WDoor.lean).
- Nothing on completeness, soundness or hiding.
-/
import E2E.KeyShapeFullSourced
import E2E.KeyShapeFirstEnd
import E2E.KeyShapeSharedTies
import E2E.KeyShapeOwn
import E2E.KeySources
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WDoor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtKey
open OnBytes OnBytes.Params
open VerifiableInference.Desc (Block OpenedColumn foldBlocks)
open VerifiableInference.Desc.Ground.Sh (coreSh stTidyB)
open VerifiableInference.Desc.Key (Source LaterPlaces Xi Claim FirstState ownTest)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Own (keyFits)
open Johnson.Desc.First.Walk.Tied (Reach reach_of_fold)
open _root_.Desc.K14 (St)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription Z₁W pubOf sh₁B sh₂ sh₃ Sh₃ sharedSh doorS
  door_carries door_at start₁_shape carries_whole₁ Z₂At flat₂ Z₃Own ZW SF CF carries_all_in_scope
  gSecond gSources sized_sourced ownRounds_full)
open AtPublicFiles.AtFiles.Full (T19 V0 V12 X0 gK₂ first_of_sourced public_first_sourced six_sourced
  carries₂_sourced run₂_sourced first₂_shape)
open H2K.Member (piKWFull)

variable {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {Nr : H2U.PlaceNums} {Pl : LaterPlaces}

/-- **A fold over the whole first chain ends at the written shape.** -/
theorem first_end_shape (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (x : (keyFileDescription Xs Nr Pl).XiPub) {e₁ : FirstState} {rs r : List Fmt.RoundView} {cols c : List OpenedColumn}
    (h : foldBlocks 0 (keyFileDescription Xs Nr Pl).first.blocksInOrder ((keyFileDescription Xs Nr Pl).start₁ x) rs cols =
      .ok (e₁, r, c)) : sh₁B (pubOf Xs) CF e₁ = T19 := by
  obtain ⟨-, -, -, hlen, hsh0, hrun, -, -⟩ := first_of_sourced hs scope fun _ _ _ _ => true
  obtain ⟨bw, hw, he, ha, -⟩ := public_first_sourced hs scope
  have ht : (keyFileDescription Xs Nr Pl).first.blocksInOrder.take 19 = (keyFileDescription Xs Nr Pl).first.blocksInOrder := by
    rw [← hlen]
    exact List.take_length
  have hr : Reach 0 (keyFileDescription Xs Nr Pl).first.blocksInOrder (fun _ : Unit => (keyFileDescription Xs Nr Pl).start₁ x) 19
      ((), e₁) :=
    reach_of_fold 19 (le_of_eq hlen.symm) e₁ rs r cols c (by
      rw [ht]
      exact h)
  have e := ProofFile.Honest.shape_reach (Z₁W (pubOf Xs) CF Xs.Y.D.1 Xs.Y.told.1 Nr fun _ _ _ _ => true)
    (fun j => carries_whole₁ (pubOf Xs) CF Xs.Y.D.1 Xs.Y.told.1 Nr 0 _ bw hw he ha j) hr T19 (by
      show (Z₁W (pubOf Xs) CF Xs.Y.D.1 Xs.Y.told.1 Nr fun _ _ _ _ => true).run 19
        ((Z₁W (pubOf Xs) CF Xs.Y.D.1 Xs.Y.told.1 Nr fun _ _ _ _ => true).sh
          ((keyFileDescription Xs Nr Pl).start₁ x)) = _
      rw [(start₁_shape (cs := CF) (N := Nr) (X := Xs) (P := Pl) _ x).trans hsh0]
      exact hrun)
  exact e.symm

/-- **A fold over the whole shared chain ends at the written shape.** -/
theorem shared_end_shape (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (x : (keyFileDescription Xs Nr Pl).XiPub) (hk : keyFits x.key AtPublicFiles.AtFiles.Full.QK.par.S.fold.index = true)
    {e₂ : St} {rs r : List Fmt.RoundView} {cols c : List OpenedColumn}
    (h : foldBlocks 0 (keyFileDescription Xs Nr Pl).shared.blocksInOrder ((keyFileDescription Xs Nr Pl).start₂ x) rs cols =
      .ok (e₂, r, c)) : AtPublicFiles.AtFiles.sh₂ e₂ = V12 := by
  have hlen := (AtPublicFiles.KeyThread.lengths scope hs.named).2.1
  have ht : (keyFileDescription Xs Nr Pl).shared.blocksInOrder.take 12 = (keyFileDescription Xs Nr Pl).shared.blocksInOrder := by
    rw [← hlen]
    exact List.take_length
  have hr : Reach 0 (flat₂ Xs.chains Pl) (fun _ : Unit => (keyFileDescription Xs Nr Pl).start₂ x) 12
      ((), e₂) :=
    reach_of_fold 12 (le_of_eq hlen.symm) e₂ rs r cols c (by
      show foldBlocks 0 ((keyFileDescription Xs Nr Pl).shared.blocksInOrder.take 12) _ _ _ = _
      rw [ht]
      exact h)
  have e := ProofFile.Honest.shape_reach (Z₂At Xs.chains Pl gK₂ fun _ _ _ _ => true)
    (carries₂_sourced hs scope 0 _) hr V12 (by
      show (Z₂At Xs.chains Pl gK₂ fun _ _ _ _ => true).run 12
        (sh₂ ((keyFileDescription Xs Nr Pl).start₂ x)) = _
      rw [first₂_shape hs scope x hk]
      exact run₂_sourced hs scope _)
  exact e.symm

/-- **The last chain's start returns a state of the shape that `X0` holds.** -/
theorem start_shape (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (x : (keyFileDescription Xs Nr Pl).XiPub) {e₁ : FirstState} {e₂ : St} {s₀ : S₃}
    (h₁ : sh₁B (pubOf Xs) CF e₁ = T19) (h₂ : AtPublicFiles.AtFiles.sh₂ e₂ = V12)
    (hb : (keyFileDescription Xs Nr Pl).start₃ x e₁ e₂ = .ok s₀) {A₀ : Sh₃} (hA : X0 = some A₀) :
    sh₃ SF s₀ = A₀ := by
  have hk := sized_sourced hs scope
  have hd : doorS CF SF T19.1 T19.2.tidy T19.2.back.door (AtPublicFiles.AtFiles.sharedOf V12) = .ok A₀ := by
    unfold X0 at hA
    cases hq : doorS CF SF T19.1 T19.2.tidy T19.2.back.door (AtPublicFiles.AtFiles.sharedOf V12) with
    | error e =>
      rw [hq] at hA
      cases hA
    | ok t =>
      rw [hq] at hA
      obtain rfl := Option.some.inj hA
      rfl
  rw [← h₁, ← h₂, AtPublicFiles.AtFiles.sharedOf_eq, AtPublicFiles.AtFiles.door_at (pubOf Xs) CF SF (six_sourced hs scope).lin e₁ _]
    at hd
  have e := door_carries Xs Nr Pl x e₁ e₂ A₀ s₀ hb (by
    rw [hk]
    exact hd)
  rw [hk] at e
  exact e.symm

/-- **In scope the run on shapes over the first two blocks is `ZW`'s.** -/
theorem run_two (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (vOwn : S₃ → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool) (a : Sh₃) :
    (Z₃Own Xs Pl vOwn).run 2 a = ZW.run 2 a := by
  have hk := sized_sourced hs scope
  show ((Except.ok a : Except String Sh₃).bind (gSecond Xs.chains.made.sized.key.once.shape)).bind
      (gSources (ownTest Pl).rounds) =
    ((Except.ok a : Except String Sh₃).bind (gSecond SF)).bind
      (gSources (H2K.Member.dsOf piKWFull))
  rw [hk, ownRounds_full hs scope]

/-- **At a stand in front of the test the state has the shape of the run.** -/
theorem stand_shape (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true) {ft : Nat}
    {s₀ st : S₃} {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    (hf : foldBlocks ft ((keyFileDescription Xs Nr Pl).second.blocksInOrder.take 2) s₀ rs cols = .ok (st, [], []))
    {A₀ A₂ : Sh₃} (h₀ : sh₃ SF s₀ = A₀) (h₂ : ZW.run 2 A₀ = .ok A₂) : sh₃ SF st = A₂ := by
  have hk := sized_sourced hs scope
  have hlen := (AtPublicFiles.KeyThread.lengths scope hs.named).2.2
  have hr : Reach ft (keyFileDescription Xs Nr Pl).second.blocksInOrder (fun _ : Unit => s₀) 2 ((), st) :=
    reach_of_fold 2 (Nat.le_trans (by decide : 2 ≤ 4) (le_of_eq hlen.symm)) st rs [] cols [] hf
  have e := ProofFile.Honest.shape_reach (Z₃Own Xs Pl fun _ _ _ => true)
    (fun j => carries_all_in_scope hs scope _ ft j) hr A₂ (by
      show (Z₃Own Xs Pl fun _ _ _ => true).run 2 (sh₃ Xs.chains.made.sized.key.once.shape s₀) = _
      rw [hk, h₀, run_two hs scope]
      exact h₂)
  have e' : A₂ = sh₃ Xs.chains.made.sized.key.once.shape st := e
  rw [hk] at e'
  exact e'.symm

end ProofFile.Honest.K12.AtKey

#print axioms ProofFile.Honest.K12.AtKey.first_end_shape
#print axioms ProofFile.Honest.K12.AtKey.shared_end_shape
#print axioms ProofFile.Honest.K12.AtKey.start_shape
#print axioms ProofFile.Honest.K12.AtKey.run_two
#print axioms ProofFile.Honest.K12.AtKey.stand_shape
