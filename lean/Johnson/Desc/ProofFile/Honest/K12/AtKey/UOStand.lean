-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/UOStand.lean: the key file's shared thread, walked through its two proximity
tests with the field `opened` told: from the start with the field at `some []`, at the second condition
`SaidField` (Honest/Thread/SaidField.lean) together with `WalkedFrom` (E2E/WalkedFrom.lean: the thread's own steps
reach this state from that start), and at the one letter `keepsKey` (UKeeps.lean), the invariant holds at
border 9, the half of the test on G_u plays, it holds at border 10, the half of the test on G_omega plays behind
its guard, and it holds at border 11.

  `letter_at_start`   the second condition at the start
  `letter_carried`    it is carried over every member
  `stand_eleven_at_key`   the statement
  `stand_twelve_at_key`   and behind the chain's last member: the invariant at border 12
  `stand_eleven_paid`, `stand_twelve_paid`   the invariant, the plays and the second condition with no premise left: at
                     the written key, at letters that say nothing, at SOME list that fits at each member; what
                     has been heard and what the two tests' yes says of the states are not in these two

By what. `stand_ten_at_key` (UStep.lean), `step_at_ten` (OStand.lean), `step_at_eleven` (OEnd.lean), `saidNext_every_member` (OLetter.lean),
`saidField_start`, `saidNext_and` (Honest/Thread/Said.lean), `saidNext_walked` (E2E/WalkedFrom.lean).

Limits.
- NOT IN FRONT OF A LAW OVER COINS (the rule: the head of Johnson/Bind/ForProver/FiveFieldsAt.lean): a statement at
  every coin; no measure is taken.
- A walk of the thread's steps, not a run of the frame: the first chain is not walked, and `WalkedFrom` binds the
  verifier's state and the tables afresh at each step.
- hPin: the meaning's item on the stored table holds everywhere: no real meaning meets that. The road spends it for
  the one open item at the start and for `CellsAlone` alone (`pair_nine`, E2E/KeyStandNine.lean).
- `stand_eleven_paid`: `VerifierAndGoals.storedPublicFiles` is three terms written in the library; `pubKey Z₀` is a made-up value; the parts
  beside the table, the index, the coins, the two sendings and the two halves say nothing.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.UStep
import Johnson.Desc.ProofFile.Honest.K12.AtKey.UKeeps
import Johnson.Desc.ProofFile.Honest.K12.AtKey.OEnd
import E2E.WalkedFrom

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.AtKey
open ProofFile.Honest ProofFile.Honest.K14 ProofFile.Honest.K12
open ProofFile.Honest.K12.AtFile (keepsU)
open OnBytes (TableKey)
open VerifiableInference.Desc (Place Grows)
open VerifiableInference.Desc.K1 (SmpStay)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source Xi)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeySharedThread (parKey plan_key)
open AtPublicFiles.KeyStandOne (inK)
open AtPublicFiles.KeyStandMember (keyOf)
open AtPublicFiles.KeyFiveFields (pubKey)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Honest (Eight)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.AtFiles.Full (PF par_sourced)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.HalvesAreJobs (pU pO)
open AtPublicFiles.TableFilled (ttF arm_U)
open AtPublicFiles.StandAtNine (K1 K2 TS)
open AtPublicFiles.KeyStandFull (idleNm idleMg idleTk idleRest idleNm_tenant)
open AtPublicFiles.KeyPartsIdle (fixedKeyParts idleWhere idle_quiet)
open AtPublicFiles.Stops (QuietHalf)
open Bind.ForProver (oodSh Seed)
open H2K.JointK (keyOmega)

variable {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (K₀ : KeyPub) (K' : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Vd : Common W₀ Rc TableKey → Prop)
  (f : W₀ → Weights) (g : Rc → ℕ → TableRand) (Z₀ : ProofFile.Pub)
  (w₀ : W₀) (rc : Rc) (x : Xi) (B : Eight (parKey Xs PF)) (own₀ : X₀)

/-- The second condition: the field holds the columns of the members in front, and the thread's own steps reach
this state from the start with the field at `some []`. -/
abbrev letterKey : ℕ → Coins (keyBook K₀) → ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀ → Prop :=
  fun b k m => SaidField (TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀) BaseNil b k m ∧
    WalkedFrom (TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀)
      (fun _ m₀ => m₀ = AtPublicFiles.KeyStandOne.startAt (keyOf (pubKey Z₀ Xs.chains) Xs PF (K2 Xs K' f g Z₀) f g)
        (some []) (inK w₀ rc x)) b k m

/-- **The second condition at the start**, with the field at `some []`. -/
theorem letter_at_start (k : Coins (keyBook K₀)) :
    letterKey Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Vd f g Z₀ w₀ rc x B own₀ 0 k
      (AtPublicFiles.KeyStandOne.startAt (keyOf (pubKey Z₀ Xs.chains) Xs PF (K2 Xs K' f g Z₀) f g) (some [])
        (inK w₀ rc x)) :=
  ⟨saidField_start _ rfl, .begun rfl⟩

/-- **The linear claim's five fields at the honest key's input.** -/
theorem fields_made_at_key {Z : VerifierAndGoals.PublicFiles} (hs : KeySourced Z Xs Nr PF) (scope : VerifierAndGoals.InScope Z = true)
    (sd : Seed (Bind.ForProver.shapeOf (pubKey Z₀ Xs.chains)) × ℕ)
    (hx : x = ⟨oodSh (Bind.ForProver.shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨f w₀, g rc, sd⟩⟩) :
    FiveFields (parKey Xs PF)
      (AtPublicFiles.KeySharedThread.lettersKey Xs Nr PF (AtPublicFiles.KeyLay.withTestsOnUAndOmega (K1 Xs K' f g Z₀) pU pO) ℓ Nm Mg₀
        (AtPublicFiles.KeyTreesKey.tbKey (parKey Xs PF) (K1 Xs K' f g Z₀).weights
      (AtPublicFiles.KeySharedThread.randKey (K1 Xs K' f g Z₀)) tk (ttF K₀ Xs (K1 Xs K' f g Z₀) B own₀)) rest keepsKey Vd (inK w₀ rc x)).valid
      (AtPublicFiles.KeySharedThread.lettersKey Xs Nr PF (AtPublicFiles.KeyLay.withTestsOnUAndOmega (K1 Xs K' f g Z₀) pU pO) ℓ Nm Mg₀
        (AtPublicFiles.KeyTreesKey.tbKey (parKey Xs PF) (K1 Xs K' f g Z₀).weights
      (AtPublicFiles.KeySharedThread.randKey (K1 Xs K' f g Z₀)) tk (ttF K₀ Xs (K1 Xs K' f g Z₀) B own₀)) rest keepsKey Vd (inK w₀ rc x)).stored
      (K1 Xs K' f g Z₀).weights (AtPublicFiles.KeySharedThread.randKey (K1 Xs K' f g Z₀)) := by
  subst hx
  have es := AtPublicFiles.AtFiles.sized_sourced hs scope
  have hfit : Bind.ForProver.rowsFit (Bind.ForProver.shapeOf (pubKey Z₀ Xs.chains))
      (Bind.ForProver.linOf (pubKey Z₀ Xs.chains)).kLo
      (Bind.ForProver.linOf (pubKey Z₀ Xs.chains)).matrixRows = true := by
    show Bind.ForProver.rowsFit
      (Bind.ForProver.shapeOfIndex Xs.chains.made.sized.key.once.shape.fold.index)
      Xs.chains.made.sized.key.once.shape.kLo Xs.chains.made.sized.key.once.shape.matrixRows = true
    rw [es]
    exact AtPublicFiles.KeyFiveFields.rows_full
  have ha : (Bind.ForProver.shapeOf (pubKey Z₀ Xs.chains)).a ≤ 32 := by
    show (Bind.ForProver.shapeOfIndex Xs.chains.made.sized.key.once.shape.fold.index).a ≤ 32
    rw [es]
    exact AtPublicFiles.KeyFiveFields.a_full
  exact AtPublicFiles.KeyFiveFields.five_made Xs Nr PF
    (keyOf (pubKey Z₀ Xs.chains) Xs PF (K2 Xs K' f g Z₀) f g) ℓ Nm Mg₀
    (AtPublicFiles.KeyTreesKey.tbKey (parKey Xs PF) (K1 Xs K' f g Z₀).weights
      (AtPublicFiles.KeySharedThread.randKey (K1 Xs K' f g Z₀)) tk (ttF K₀ Xs (K1 Xs K' f g Z₀) B own₀))
    rest keepsKey Vd f g Z₀ hfit ha rfl rfl (fun _ _ _ => rfl) w₀ rc sd

/-- **The second condition is carried over every member.** -/
theorem letter_carried {Z : VerifierAndGoals.PublicFiles} (hs : KeySourced Z Xs Nr PF) (scope : VerifierAndGoals.InScope Z = true)
    (hK₀ : fullPub = some K₀) (sd : Seed (Bind.ForProver.shapeOf (pubKey Z₀ Xs.chains)) × ℕ)
    (hx : x = ⟨oodSh (Bind.ForProver.shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨f w₀, g rc, sd⟩⟩)
    (hN : Function.Injective Nm.tenant) (b : ℕ) :
    SaidNext (TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀)
      (letterKey Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Vd f g Z₀ w₀ rc x B own₀) b :=
  saidNext_and _ _
    (saidNext_every_member K₀ hK₀ Xs Nr (K1 Xs K' f g Z₀) ℓ Nm Mg₀ tk rest keepsKey Vd _ B own₀ hs scope
      (fields_made_at_key Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Vd f g Z₀ w₀ rc x B own₀ hs scope sd hx) rfl rfl hN
      (no_stop_at_key K₀ Xs Nr (K1 Xs K' f g Z₀) ℓ Nm Mg₀ tk rest keepsKey Vd _ B _ rfl) b)
    (saidNext_walked _ _ b)

/-- **Through both proximity tests, with the field told.** At a key in scope, at the honest key's input, at every
coin and every list that fits at the eight members with rounds in front of border 11. -/
theorem stand_eleven_at_key {Z : VerifierAndGoals.PublicFiles} (hs : KeySourced Z Xs Nr PF)
    (scope : VerifierAndGoals.InScope Z = true) (hK₀ : fullPub = some K₀)
    (sd : Seed (Bind.ForProver.shapeOf (pubKey Z₀ Xs.chains)) × ℕ)
    (hx : x = ⟨oodSh (Bind.ForProver.shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨f w₀, g rc, sd⟩⟩)
    (hN : Function.Injective Nm.tenant) (hPin : ∀ v s y u, (Mg₀ v).pinT s y u)
    (hVd : Vd (inK w₀ rc x)) (qr : QuietHalf K'.rng) (qw : QuietHalf K'.own)
    (k : Coins (keyBook K₀)) (ds₁ ds₂ ds₄ ds₅ ds₇ ds₈ ds₉ ds₁₀ : List Fmt.Drawn)
    (hd₁ : ∀ blk, (TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀).bs[1]? = some blk →
      drawsFit blk.rounds ds₁ = true)
    (hd₂ : ∀ blk, (TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀).bs[2]? = some blk →
      drawsFit blk.rounds ds₂ = true)
    (hd₄ : ∀ blk, (TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀).bs[4]? = some blk →
      drawsFit blk.rounds ds₄ = true)
    (hd₅ : ∀ blk, (TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀).bs[5]? = some blk →
      drawsFit blk.rounds ds₅ = true)
    (hd₇ : ∀ blk, (TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀).bs[7]? = some blk →
      drawsFit blk.rounds ds₇ = true)
    (hd₈ : ∀ blk, (TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀).bs[8]? = some blk →
      drawsFit blk.rounds ds₈ = true)
    (hd₉ : drawsFit (H2K.JointK.keyGu PF).rounds ds₉ = true)
    (hd₁₀ : drawsFit (keyOmega (PF.O.getD PF.U)).rounds ds₁₀ = true) :
    ∃ (s s' s'' : St) (m : ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀) (E : Env)
      (y y' : List Played × ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀)
      (cols cols' : List VerifiableInference.Desc.OpenedColumn),
      ThrS (TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀)
          (letterKey Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Vd f g Z₀ w₀ rc x B own₀) 9 k s m E ∧
        (TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀).Moved (H2K.JointK.keyGu PF) k m E ds₉ y cols ∧
        ThrS (TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀)
          (letterKey Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Vd f g Z₀ w₀ rc x B own₀) 10 k s' (y.2.took cols)
          (E.add y.1) ∧
        (TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀).Moved (keyOmega (PF.O.getD PF.U)) k (y.2.took cols) (E.add y.1) ds₁₀ y' cols' ∧
        ThrS (TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀)
          (letterKey Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Vd f g Z₀ w₀ rc x B own₀) 11 k s'' (y'.2.took cols')
          ((E.add y.1).add y'.1) ∧
        (y'.2.took cols').st.heard = ds₁ ++ ds₂ ++ ds₄ ++ ds₅ ++ ds₇ ++ ds₈ ++ ds₉ ++ ds₁₀ ∧
        keepsU pU s s' ∧ Grows s'.st s''.st ∧ SmpStay s'.st s''.st := by
  have hC := letter_carried Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Vd f g Z₀ w₀ rc x B own₀ hs scope hK₀ sd hx hN
  obtain ⟨s, s', m, E, y, cols, u9, hMv, u10, hh, hy⟩ := stand_ten_at_key Xs Nr K₀ K' ℓ Nm Mg₀ tk rest
    keepsKey Vd f g Z₀ w₀ rc x B own₀ hs scope hK₀ sd hx hN hPin keepsKey_same
    (fun s s' h => (keepsKey_zero s s').1 h) keepsKey_nine hVd qr qw
    (letterKey Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Vd f g Z₀ w₀ rc x B own₀) (some []) k
    ds₁ ds₂ ds₄ ds₅ ds₇ ds₈ ds₉ hd₁ hd₂ hd₄ hd₅ hd₇ hd₈ hd₉
    (letter_at_start Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Vd f g Z₀ w₀ rc x B own₀ k) (fun b _ => hC b)
  obtain ⟨layO, hQ⟩ := plan_key hs scope
  obtain ⟨s'', y', cols', hMv', u11, hh', hG, hS⟩ := step_at_ten K₀ hK₀ Xs Nr (K1 Xs K' f g Z₀) ℓ Nm Mg₀ tk
    rest keepsKey Vd (inK w₀ rc x) B own₀ hs.named.plan (par_sourced hs scope) hQ rfl hQ.facts.two
    keepsKey_ten (letterKey Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Vd f g Z₀ w₀ rc x B own₀)
    (fun k s m E u => field_of_letter K₀ Xs Nr (K1 Xs K' f g Z₀) ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀
      k s m E ⟨u.1, u.2.1⟩) (hC 10)
    (no_stop_at_key K₀ Xs Nr (K1 Xs K' f g Z₀) ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B _ rfl)
    u10 ds₁₀ hd₁₀
  exact ⟨s, s', s'', m, E, y, y', cols, cols', u9, hMv, u10, hMv', u11, by rw [hh', hh], hy, hG, hS⟩

/-- **The whole shared chain, with the field told**: the invariant and the second condition hold at border 12, behind
the last of the chain's twelve members (`members_of_thread`, OField.lean), at every list that fits at the nine
members with rounds. The second condition says that the thread's own steps reach this state from the start. -/
theorem stand_twelve_at_key {Z : VerifierAndGoals.PublicFiles} (hs : KeySourced Z Xs Nr PF)
    (scope : VerifierAndGoals.InScope Z = true) (hK₀ : fullPub = some K₀)
    (sd : Seed (Bind.ForProver.shapeOf (pubKey Z₀ Xs.chains)) × ℕ)
    (hx : x = ⟨oodSh (Bind.ForProver.shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨f w₀, g rc, sd⟩⟩)
    (hN : Function.Injective Nm.tenant) (hPin : ∀ v s y u, (Mg₀ v).pinT s y u)
    (hVd : Vd (inK w₀ rc x)) (qr : QuietHalf K'.rng) (qw : QuietHalf K'.own)
    (k : Coins (keyBook K₀)) (ds₁ ds₂ ds₄ ds₅ ds₇ ds₈ ds₉ ds₁₀ ds₁₁ : List Fmt.Drawn)
    (hd₁ : ∀ blk, (TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀).bs[1]? = some blk →
      drawsFit blk.rounds ds₁ = true)
    (hd₂ : ∀ blk, (TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀).bs[2]? = some blk →
      drawsFit blk.rounds ds₂ = true)
    (hd₄ : ∀ blk, (TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀).bs[4]? = some blk →
      drawsFit blk.rounds ds₄ = true)
    (hd₅ : ∀ blk, (TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀).bs[5]? = some blk →
      drawsFit blk.rounds ds₅ = true)
    (hd₇ : ∀ blk, (TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀).bs[7]? = some blk →
      drawsFit blk.rounds ds₇ = true)
    (hd₈ : ∀ blk, (TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀).bs[8]? = some blk →
      drawsFit blk.rounds ds₈ = true)
    (hd₉ : drawsFit (H2K.JointK.keyGu PF).rounds ds₉ = true)
    (hd₁₀ : drawsFit (keyOmega (PF.O.getD PF.U)).rounds ds₁₀ = true)
    (hd₁₁ : drawsFit (H2K.JointK.keySharedEnd Xs.chains PF).rounds ds₁₁ = true) :
    ∃ (s : St) (m : ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀) (E : Env),
      ThrS (TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest keepsKey Vd f g Z₀ w₀ rc x B own₀)
          (letterKey Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Vd f g Z₀ w₀ rc x B own₀) 12 k s m E ∧
        m.st.heard = ds₁ ++ ds₂ ++ ds₄ ++ ds₅ ++ ds₇ ++ ds₈ ++ ds₉ ++ ds₁₀ ++ ds₁₁ := by
  obtain ⟨s, s', s'', m, E, y₉, y', cols₉, cols', _, _, _, _, u11, hh, _⟩ := stand_eleven_at_key Xs Nr K₀ K' ℓ Nm Mg₀
    tk rest Vd f g Z₀ w₀ rc x B own₀ hs scope hK₀ sd hx hN hPin hVd qr qw k ds₁ ds₂ ds₄ ds₅ ds₇ ds₈ ds₉ ds₁₀
    hd₁ hd₂ hd₄ hd₅ hd₇ hd₈ hd₉ hd₁₀
  obtain ⟨layO, hQ⟩ := plan_key hs scope
  have hk : VerifiableInference.Desc.Own.keyFits x.key AtPublicFiles.AtFiles.Full.QK.par.S.fold.index = true := by
    have h := (fields_made_at_key Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Vd f g Z₀ w₀ rc x B own₀ hs scope sd hx).key
      (inK w₀ rc x) ⟨rfl, hVd⟩
    have e : parKey Xs PF = AtPublicFiles.AtFiles.Full.QK := par_sourced hs scope
    rw [e] at h
    exact h
  obtain ⟨y, cols, -, u12, hh'⟩ := step_at_eleven K₀ Xs Nr (K1 Xs K' f g Z₀) ℓ Nm Mg₀ tk rest keepsKey Vd w₀ rc
    x B own₀ hs scope hk hQ.facts.two keepsKey_same (fun s s' h => (keepsKey_eleven s s').1 h)
    (letterKey Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Vd f g Z₀ w₀ rc x B own₀)
    (letter_carried Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Vd f g Z₀ w₀ rc x B own₀ hs scope hK₀ sd hx hN 11)
    (no_stop_at_key K₀ Xs Nr (K1 Xs K' f g Z₀) ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B _ rfl)
    u11 ds₁₁ hd₁₁
  exact ⟨s'', _, _, u12, by rw [hh', hh]⟩

/-- Some list of challenges fits the test on G_omega. By the kernel. -/
theorem fit_at_omega : drawsFit (keyOmega (PF.O.getD PF.U)).rounds
    ((keyOmega (PF.O.getD PF.U)).rounds.map AtPublicFiles.KeyStandMember.fitOf) = true := by
  decide +kernel

/-- **No premise left.** At the written key, at parts and letters that say nothing beside the two halves, at every
index, committer's coins, seed and book's coins, at some list that fits at each of the eight members with rounds:
the thread's steps go from the start, with the field at `some []`, through both proximity tests to border 11. -/
theorem stand_eleven_paid (Z₀ : ProofFile.Pub) :
    ∃ (Xs : Source) (Nr : H2U.PlaceNums) (K₀ : KeyPub), KeySourced VerifierAndGoals.storedPublicFiles Xs Nr PF ∧
      fullPub = some K₀ ∧ ∃ B : Eight (parKey Xs PF),
      ∀ (fc : VerifiableInference.Desc.K3.Face) (w₀ : Weights) (rc : ℕ → TableRand)
        (sd : Seed (Bind.ForProver.shapeOf (pubKey Z₀ Xs.chains)) × ℕ) (k : Coins (keyBook K₀)),
        let T := TS Xs Nr K₀ (fixedKeyParts (W₀ := Weights) (Rc := ℕ → TableRand) (X₀ := Unit) (X := Unit) (Wk := Unit) fc idleWhere
      ⟨fun _ _ => 0⟩ () () ())
            WitLens.words idleNm (fun _ => idleMg) idleTk idleRest keepsKey (fun _ => True) id id Z₀ w₀ rc
            ⟨oodSh (Bind.ForProver.shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨w₀, rc, sd⟩⟩ B ()
        let Said := letterKey Xs Nr K₀ (fixedKeyParts (W₀ := Weights) (Rc := ℕ → TableRand) (X₀ := Unit) (X := Unit) (Wk := Unit) fc idleWhere
      ⟨fun _ _ => 0⟩ () () ())
            WitLens.words idleNm (fun _ => idleMg) idleTk idleRest (fun _ => True) id id Z₀ w₀ rc
            ⟨oodSh (Bind.ForProver.shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨w₀, rc, sd⟩⟩ B ()
        ∃ (s s' s'' : St) (m : ProofFile.Honest.Mid (Common Weights (ℕ → TableRand) TableKey) Unit) (E : Env)
          (ds ds' : List Fmt.Drawn)
          (y y' : List Played × ProofFile.Honest.Mid (Common Weights (ℕ → TableRand) TableKey) Unit)
          (cols cols' : List VerifiableInference.Desc.OpenedColumn),
          ThrS T Said 9 k s m E ∧ T.Moved (H2K.JointK.keyGu PF) k m E ds y cols ∧
            ThrS T Said 10 k s' (y.2.took cols) (E.add y.1) ∧
            T.Moved (keyOmega (PF.O.getD PF.U)) k (y.2.took cols) (E.add y.1) ds' y' cols' ∧
            ThrS T Said 11 k s'' (y'.2.took cols') ((E.add y.1).add y'.1) := by
  obtain ⟨Xs, Nr, Pl, hs⟩ := AtPublicFiles.AtFiles.key_sourced VerifierAndGoals.storedPublicFiles AtFullSide.Top.theLive_zFull
  obtain ⟨K₀, hK₀⟩ := AtPublicFiles.KeyBook.full_made
  have hPl : Pl = PF := AtPublicFiles.AtFiles.Full.later_sourced hs VerifierAndGoals.inScope_full
  subst hPl
  obtain ⟨layO, hQ⟩ := plan_key hs VerifierAndGoals.inScope_full
  obtain ⟨B⟩ := hQ.eight
  refine ⟨Xs, Nr, K₀, hs, hK₀, B, fun fc w₀ rc sd k => ?_⟩
  intro T Said
  obtain ⟨qr, -, -, qw⟩ := idle_quiet (W₀ := Weights) (Rc := ℕ → TableRand) (X₀ := Unit)
    (X := Unit) (Wk := Unit) fc idleWhere ⟨fun _ _ => 0⟩ () () ()
  have pa : (K2 Xs (fixedKeyParts (W₀ := Weights) (Rc := ℕ → TableRand) (X₀ := Unit) (X := Unit) (Wk := Unit) fc idleWhere
      ⟨fun _ _ => 0⟩ () () ()) id id Z₀).onU.place =
      AtPublicFiles.KeyBook.foldedTestPlace := AtPublicFiles.KeyPlaysAt.place_on
  have pb : (K2 Xs (fixedKeyParts (W₀ := Weights) (Rc := ℕ → TableRand) (X₀ := Unit) (X := Unit) (Wk := Unit) fc idleWhere
      ⟨fun _ _ => 0⟩ () () ()) id id Z₀).onOmega.place =
      AtPublicFiles.KeyBook.omegaTestPlace := AtPublicFiles.HalvesAreJobs.place_omega
  obtain ⟨ds₁, ds₂, ds₄, ds₅, ds₇, ds₈, h₁, h₂, h₄, h₅, h₇, h₈⟩ := AtPublicFiles.KeyStandNineAt.lists_nine Xs Nr PF K₀
    (K2 Xs (fixedKeyParts (W₀ := Weights) (Rc := ℕ → TableRand) (X₀ := Unit) (X := Unit) (Wk := Unit) fc idleWhere
      ⟨fun _ _ => 0⟩ () () ()) id id Z₀) WitLens.words idleNm (fun _ => idleMg) idleTk _ idleRest
    keepsKey (fun _ => True) id id Z₀ w₀ rc _ hs VerifierAndGoals.inScope_full sd rfl pa pb
  obtain ⟨s, s', s'', m, E, y, y', cols, cols', u9, hM, u10, hM', u11, -⟩ := stand_eleven_at_key Xs Nr K₀
    (fixedKeyParts (W₀ := Weights) (Rc := ℕ → TableRand) (X₀ := Unit) (X := Unit) (Wk := Unit) fc idleWhere
      ⟨fun _ _ => 0⟩ () () ()) WitLens.words idleNm (fun _ => idleMg) idleTk idleRest
    (fun _ => True) id id Z₀ w₀ rc _ B () hs VerifierAndGoals.inScope_full hK₀ sd rfl
    idleNm_tenant (fun _ _ _ _ => trivial) trivial qr qw k ds₁ ds₂ ds₄ ds₅ ds₇ ds₈ _ _ h₁ h₂ h₄ h₅ h₇ h₈
    AtPublicFiles.KeyPlaysAt.fit_gu fit_at_omega
  exact ⟨s, s', s'', m, E, _, _, y, y', cols, cols', u9, hM, u10, hM', u11⟩

/-- Some list of challenges fits the chain's last member: its one round draws nothing. -/
theorem fit_at_end (c : OnBytes.Model.Verify.Chains) :
    drawsFit (H2K.JointK.keySharedEnd c PF).rounds
      ((H2K.JointK.keySharedEnd c PF).rounds.map AtPublicFiles.KeyStandMember.fitOf) = true := by
  have e : (H2K.JointK.keySharedEnd c PF).rounds = [VerifiableInference.Desc.ChainEnd.sealRound] := rfl
  rw [e]
  decide

/-- **The whole chain with no premise left.** At the written key, at parts and letters that say nothing beside the two
halves, at every index, committer's coins, seed and book's coins, at some list that fits at each of the nine
members with rounds: the invariant and the second condition hold at border 12. -/
theorem stand_twelve_paid (Z₀ : ProofFile.Pub) :
    ∃ (Xs : Source) (Nr : H2U.PlaceNums) (K₀ : KeyPub), KeySourced VerifierAndGoals.storedPublicFiles Xs Nr PF ∧
      fullPub = some K₀ ∧ ∃ B : Eight (parKey Xs PF),
      ∀ (fc : VerifiableInference.Desc.K3.Face) (w₀ : Weights) (rc : ℕ → TableRand)
        (sd : Seed (Bind.ForProver.shapeOf (pubKey Z₀ Xs.chains)) × ℕ) (k : Coins (keyBook K₀)),
        ∃ (s : St) (m : ProofFile.Honest.Mid (Common Weights (ℕ → TableRand) TableKey) Unit) (E : Env),
          ThrS (TS Xs Nr K₀ (fixedKeyParts (W₀ := Weights) (Rc := ℕ → TableRand) (X₀ := Unit) (X := Unit) (Wk := Unit) fc idleWhere
      ⟨fun _ _ => 0⟩ () () ())
              WitLens.words idleNm (fun _ => idleMg) idleTk idleRest keepsKey (fun _ => True) id id Z₀ w₀ rc
              ⟨oodSh (Bind.ForProver.shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨w₀, rc, sd⟩⟩ B ())
            (letterKey Xs Nr K₀ (fixedKeyParts (W₀ := Weights) (Rc := ℕ → TableRand) (X₀ := Unit) (X := Unit) (Wk := Unit) fc idleWhere
      ⟨fun _ _ => 0⟩ () () ())
              WitLens.words idleNm (fun _ => idleMg) idleTk idleRest (fun _ => True) id id Z₀ w₀ rc
              ⟨oodSh (Bind.ForProver.shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨w₀, rc, sd⟩⟩ B ()) 12 k s m E := by
  obtain ⟨Xs, Nr, Pl, hs⟩ := AtPublicFiles.AtFiles.key_sourced VerifierAndGoals.storedPublicFiles AtFullSide.Top.theLive_zFull
  obtain ⟨K₀, hK₀⟩ := AtPublicFiles.KeyBook.full_made
  have hPl : Pl = PF := AtPublicFiles.AtFiles.Full.later_sourced hs VerifierAndGoals.inScope_full
  subst hPl
  obtain ⟨layO, hQ⟩ := plan_key hs VerifierAndGoals.inScope_full
  obtain ⟨B⟩ := hQ.eight
  refine ⟨Xs, Nr, K₀, hs, hK₀, B, fun fc w₀ rc sd k => ?_⟩
  obtain ⟨qr, -, -, qw⟩ := idle_quiet (W₀ := Weights) (Rc := ℕ → TableRand) (X₀ := Unit)
    (X := Unit) (Wk := Unit) fc idleWhere ⟨fun _ _ => 0⟩ () () ()
  have pa : (K2 Xs (fixedKeyParts (W₀ := Weights) (Rc := ℕ → TableRand) (X₀ := Unit) (X := Unit) (Wk := Unit) fc idleWhere
      ⟨fun _ _ => 0⟩ () () ()) id id Z₀).onU.place =
      AtPublicFiles.KeyBook.foldedTestPlace := AtPublicFiles.KeyPlaysAt.place_on
  have pb : (K2 Xs (fixedKeyParts (W₀ := Weights) (Rc := ℕ → TableRand) (X₀ := Unit) (X := Unit) (Wk := Unit) fc idleWhere
      ⟨fun _ _ => 0⟩ () () ()) id id Z₀).onOmega.place =
      AtPublicFiles.KeyBook.omegaTestPlace := AtPublicFiles.HalvesAreJobs.place_omega
  obtain ⟨ds₁, ds₂, ds₄, ds₅, ds₇, ds₈, h₁, h₂, h₄, h₅, h₇, h₈⟩ := AtPublicFiles.KeyStandNineAt.lists_nine Xs Nr PF K₀
    (K2 Xs (fixedKeyParts (W₀ := Weights) (Rc := ℕ → TableRand) (X₀ := Unit) (X := Unit) (Wk := Unit) fc idleWhere
      ⟨fun _ _ => 0⟩ () () ()) id id Z₀) WitLens.words idleNm (fun _ => idleMg) idleTk _ idleRest
    keepsKey (fun _ => True) id id Z₀ w₀ rc _ hs VerifierAndGoals.inScope_full sd rfl pa pb
  obtain ⟨s, m, E, u, -⟩ := stand_twelve_at_key Xs Nr K₀
    (fixedKeyParts (W₀ := Weights) (Rc := ℕ → TableRand) (X₀ := Unit) (X := Unit) (Wk := Unit) fc idleWhere
      ⟨fun _ _ => 0⟩ () () ()) WitLens.words idleNm (fun _ => idleMg) idleTk idleRest
    (fun _ => True) id id Z₀ w₀ rc _ B () hs VerifierAndGoals.inScope_full hK₀ sd rfl
    idleNm_tenant (fun _ _ _ _ => trivial) trivial qr qw k ds₁ ds₂ ds₄ ds₅ ds₇ ds₈ _ _
    ((H2K.JointK.keySharedEnd Xs.chains PF).rounds.map AtPublicFiles.KeyStandMember.fitOf) h₁ h₂ h₄ h₅ h₇ h₈
    AtPublicFiles.KeyPlaysAt.fit_gu fit_at_omega (fit_at_end Xs.chains)
  exact ⟨s, m, E, u⟩

end ProofFile.Honest.K12.AtKey

end

#print axioms ProofFile.Honest.K12.AtKey.letter_at_start
#print axioms ProofFile.Honest.K12.AtKey.fields_made_at_key
#print axioms ProofFile.Honest.K12.AtKey.letter_carried
#print axioms ProofFile.Honest.K12.AtKey.stand_eleven_at_key
#print axioms ProofFile.Honest.K12.AtKey.stand_twelve_at_key
#print axioms ProofFile.Honest.K12.AtKey.fit_at_omega
#print axioms ProofFile.Honest.K12.AtKey.stand_eleven_paid
#print axioms ProofFile.Honest.K12.AtKey.fit_at_end
#print axioms ProofFile.Honest.K12.AtKey.stand_twelve_paid
