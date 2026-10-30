-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyStandWalked.lean: the stand at border 9 of the key's shared thread, with the start's field at `some []` and the
letter `WalkedFrom` (E2E/WalkedFrom.lean), at letters and at the written value.

Why. `stand_nine` (E2E/KeyStandNineAt.lean) is general in the letter `Said` and in the start's field. The frame's walk
begins at `some []`. This file lays both, so that the field is what a guarded half is handed, and lays the value.

Main names.
  `stand_nine_walked`: `stand_nine` at the start's field `some []` and the letter `WalkedFrom`: no premise on the letter.
  `stand_nine_at_value`: the same at the offline prover's senders at a description of the public files.
  `eight_at_letters`: the five statements at members 1 to 8, at these letters, with the five facts paid by `five_made`.
  `front_at_letters`: the same at member 0.

What stays open. As premises: `hN`, `hPin`: met at idle letters `Nm`, `Mg₀`; `hKp`, `hE`, `hV`, and the fit of the lists. The
seed `sd` is a letter: `validAt_of_tied` gives one at a tied input.

What its end is worth. A stand is a sentence of one run: `∃`. `SaysNine` holds at every stand (`items_at_nine`), but the
three `HasRow`, the two lengths and the list heard are said of this stand's own state alone. A debt over every state at
border 9 can't spend them without a uniqueness of the state.

No law over coins: the coins are letters.

Nothing on soundness, completeness, hiding or binding.

-/
import E2E.KeyStandNineAt
import E2E.KeyValueHolds
import E2E.WalkedFrom
import E2E.KeyEightFive

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.KeyStandWalked
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (TableKey)
open VerifiableInference.Desc (Place OpenedColumn)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source LaterPlaces Xi)
open _root_.Desc.K14 (St)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub foldedTestPlace omegaTestPlace)
open AtPublicFiles.KeySharedThread (threadKey parKey)
open AtPublicFiles.KeyAsksKey (tableKey)
open AtPublicFiles.KeyStandOne (startAt inK)
open AtPublicFiles.KeyStandNine (HasRow)
open AtPublicFiles.KeyStandNineAt (SaysNine stand_nine)
open AtPublicFiles.KeyStandMember (keyOf)
open AtPublicFiles.KeyFiveFields (pubKey)
open AtPublicFiles.KeyFile (KeyParts)
open Bind.ForProver (shapeOf oodSh Seed)

section Letters
variable {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K₀ : KeyPub) (K' : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (tt : Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop)
  (f : W₀ → Weights) (g : Rc → ℕ → TableRand) (Z₀ : ProofFile.Pub)
  (w₀ : W₀) (rc : Rc) (x : Xi)

/-- The shared thread at these letters. -/
abbrev threadAt :=
  threadKey Xs Nr Pl (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
    (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd (inK w₀ rc x)

/-- **The letter**: what the thread's steps reach from the walk's start. -/
abbrev walkedLetter :=
  WalkedFrom (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x)
    (fun _ m => m = startAt (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) (some []) (inK w₀ rc x))

/-- What the stand at border 9 says. -/
def NineEnd (k : Coins (keyBook K₀)) (ds₁ ds₂ ds₄ ds₅ ds₇ ds₈ : List Fmt.Drawn) : Prop :=
  ∃ (s : St) (m : Mid (Common W₀ Rc TableKey) X₀) (E : Env),
    ThrS (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x)
      (walkedLetter Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x) 9 k s m E ∧
    m.st.heard = ds₁ ++ ds₂ ++ ds₄ ++ ds₅ ++ ds₇ ++ ds₈ ∧
    SaysNine Xs Pl ℓ s ((threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x).wit k
      m.st.input m.st.heard) ∧
    HasRow (num .oU) s ∧ HasRow (num .oOmega) s ∧ HasRow (num .oSp) s ∧
    (_root_.Desc.K14.Law.rowsOn s s.loc.gU).length = (parKey Xs Pl).par.S.fold.index.answers +
      (parKey Xs Pl).par.S.fold.columns + 1 ∧
    (_root_.Desc.K14.Law.rowsOn s s.loc.gOmega).length = 1 ∧
    0 < (parKey Xs Pl).par.S.fold.index.answers ∧ 0 < (parKey Xs Pl).par.S.fold.columns

/-- **The stand at border 9 at the walk's start and the letter `WalkedFrom`.** -/
theorem stand_nine_walked {Z : VerifierAndGoals.PublicFiles} (hs : KeySourced Z Xs Nr Pl)
    (scope : VerifierAndGoals.InScope Z = true) (hK₀ : fullPub = some K₀)
    (sd : Seed (shapeOf (pubKey Z₀ Xs.chains)) × ℕ)
    (hx : x = ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨f w₀, g rc, sd⟩⟩)
    (hN : Function.Injective Nm.tenant) (hPin : ∀ v s y u, (Mg₀ v).pinT s y u)
    (hKp : ∀ b ∈ [0, 11], ∀ s, Kp b s s) (hE : ∀ s s', Kp 0 s s' → s' = s)
    (hV : Vd (inK w₀ rc x))
    (qr : AtPublicFiles.Stops.QuietHalf K'.rng) (qU : AtPublicFiles.Stops.QuietHalf K'.onU)
    (qO : AtPublicFiles.Stops.QuietHalf K'.onOmega) (qw : AtPublicFiles.Stops.QuietHalf K'.own)
    (pU : K'.onU.place = foldedTestPlace) (pO : K'.onOmega.place = omegaTestPlace)
    (k : Coins (keyBook K₀)) (ds₁ ds₂ ds₄ ds₅ ds₇ ds₈ : List Fmt.Drawn)
    (hd₁ : ∀ blk, (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x).bs[1]? = some blk →
      drawsFit blk.rounds ds₁ = true)
    (hd₂ : ∀ blk, (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x).bs[2]? = some blk →
      drawsFit blk.rounds ds₂ = true)
    (hd₄ : ∀ blk, (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x).bs[4]? = some blk →
      drawsFit blk.rounds ds₄ = true)
    (hd₅ : ∀ blk, (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x).bs[5]? = some blk →
      drawsFit blk.rounds ds₅ = true)
    (hd₇ : ∀ blk, (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x).bs[7]? = some blk →
      drawsFit blk.rounds ds₇ = true)
    (hd₈ : ∀ blk, (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x).bs[8]? = some blk →
      drawsFit blk.rounds ds₈ = true) :
    NineEnd Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x k ds₁ ds₂ ds₄ ds₅ ds₇ ds₈ :=
  stand_nine Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd
    (walkedLetter Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x) (some []) f g Z₀ w₀ rc x
    hs scope hK₀ sd hx hN hPin hKp hE hV qr qU qO qw pU pO k ds₁ ds₂ ds₄ ds₅ ds₇ ds₈ hd₁ hd₂ hd₄ hd₅
    hd₇ hd₈ (.begun rfl) fun b _ => saidNext_walked _ _ b

/-- **The five statements at members 1 to 8, at these letters, where the input's key is the committer's at the seed `sd`.** -/
theorem eight_at_letters {Z : VerifierAndGoals.PublicFiles} (hs : KeySourced Z Xs Nr Pl)
    (scope : VerifierAndGoals.InScope Z = true) (hK₀ : fullPub = some K₀)
    (sd : Seed (shapeOf (pubKey Z₀ Xs.chains)) × ℕ)
    (hx : x = ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨f w₀, g rc, sd⟩⟩)
    (hN : Function.Injective Nm.tenant)
    (pU : K'.onU.place = foldedTestPlace) (pO : K'.onOmega.place = omegaTestPlace)
    (Said : Nat → Coins (keyBook K₀) → Mid (Common W₀ Rc TableKey) X₀ → Prop)
    (fall : Nat → (VerifiableInference.Desc.Key.descriptionFromSource Xs Nr Pl).S₂ → List Fmt.Drawn → Option String)
    (b : Nat) (h1 : 1 ≤ b) (h8 : b ≤ 8) :
    PlaysS (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x) Said b ∧
      BehindS (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x) Said b ∧
      ExchangeS (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x) Said b ∧
      RidesPastS (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x) Said b ∧
      AcceptedS (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x) Said fall b := by
  subst hx
  have es := AtPublicFiles.AtFiles.sized_sourced hs scope
  have hfit : Bind.ForProver.rowsFit (shapeOf (pubKey Z₀ Xs.chains))
      (Bind.ForProver.linOf (pubKey Z₀ Xs.chains)).kLo
      (Bind.ForProver.linOf (pubKey Z₀ Xs.chains)).matrixRows = true := by
    show Bind.ForProver.rowsFit (Bind.ForProver.shapeOfIndex Xs.chains.made.sized.key.once.shape.fold.index)
      Xs.chains.made.sized.key.once.shape.kLo Xs.chains.made.sized.key.once.shape.matrixRows = true
    rw [es]
    exact AtPublicFiles.KeyFiveFields.rows_full
  have ha : (shapeOf (pubKey Z₀ Xs.chains)).a ≤ 32 := by
    show (Bind.ForProver.shapeOfIndex Xs.chains.made.sized.key.once.shape.fold.index).a ≤ 32
    rw [es]
    exact AtPublicFiles.KeyFiveFields.a_full
  have F := AtPublicFiles.KeyFiveFields.five_made Xs Nr Pl (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
    (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd f g Z₀ hfit ha rfl
    rfl (fun _ _ _ => rfl) w₀ rc sd
  have hap : [K14.place 1, K14.sendPlace 2, K14.place 4, K14.sendPlace 5, K14.place 7, K14.place 8,
      (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g).onU.place,
      (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g).onOmega.place].Nodup := by
    show [K14.place 1, K14.sendPlace 2, K14.place 4, K14.sendPlace 5, K14.place 7, K14.place 8,
      K'.onU.place, K'.onOmega.place].Nodup
    rw [pU, pO]
    decide
  exact AtPublicFiles.KeyEightFive.eight_five_sourced Xs Nr Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm
    Mg₀ tk tt rest Kp Vd _ Said fall hs scope hK₀ F rfl rfl hap hN b h1 h8

/-- **The five statements at member 0, the chain's front.** -/
theorem front_at_letters {Z : VerifierAndGoals.PublicFiles} (hs : KeySourced Z Xs Nr Pl)
    (scope : VerifierAndGoals.InScope Z = true) (hKp : ∀ b ∈ [0, 11], ∀ s, Kp b s s)
    (hE : ∀ s s', Kp 0 s s' → s' = s) (hC : ∀ v, AtPublicFiles.KeySharedQuiet.CellsAlone (Mg₀ v))
    (Said : Nat → Coins (keyBook K₀) → Mid (Common W₀ Rc TableKey) X₀ → Prop)
    (fall : Nat → (VerifiableInference.Desc.Key.descriptionFromSource Xs Nr Pl).S₂ → List Fmt.Drawn → Option String) :
    PlaysS (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x) Said 0 ∧
      BehindS (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x) Said 0 ∧
      ExchangeS (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x) Said 0 ∧
      RidesPastS (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x) Said 0 ∧
      AcceptedS (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x) Said fall 0 := by
  have hO := AtPublicFiles.KeySharedQuiet.over_key Xs Nr Pl (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
    (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd (inK w₀ rc x)
  exact ⟨playsS_of _ Said (AtPublicFiles.KeyThread.plays_quiet₂ scope hs.named _ hO.bs 0 (by decide)),
    behindS_of _ Said (AtPublicFiles.KeyThread.behind₂ Xs Nr Pl hs scope hO
      (AtPublicFiles.KeySharedQuiet.quiet_key Xs Nr Pl (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
        (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd
        (inK w₀ rc x) hKp) 0 (by decide)),
    exchangeS_of _ Said (AtPublicFiles.KeyThread.exchange_of_nil _
      (AtPublicFiles.KeySharedQuiet.owes_front Xs Nr Pl (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
        (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd
        (inK w₀ rc x))),
    ridesPastS_of _ Said (AtPublicFiles.KeySharedQuiet.ridesPast_front Xs Nr Pl
      (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
      (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd
      (inK w₀ rc x) hE hC),
    acceptedS_of _ Said (AtPublicFiles.AtFiles.accepted_front₂ Xs Nr Pl _ (fall := fall) hO.bs)⟩

end Letters

section Value
open AtPublicFiles.KeyValueHolds (quietHalf_test quietHalf_needs place_p12At)
open AtPublicFiles.KeyValues (WitK matrixEntryOf multiplicitiesGroups)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open ProofFile.Honest.Term (tableCoins)
open AtPublicFiles.AtFiles.HonestTerm (OfflineDescription offlineSenders offlineTestParametersOnU offlineTestOnOmega
  matrixReader)

variable {files : VerifierAndGoals.PublicFiles} (description : OfflineDescription)

/-- **The offline prover's senders with the four proximity tests.** -/
abbrev offlineValue : KeyParts FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles files).EncodingRandomness Unit Unit WitK :=
  AtPublicFiles.KeyLay.withTests (offlineSenders (files := files) description) description.source
    description.numbers description.later (offlineTestParametersOnU description.later)
    (offlineTestOnOmega description.later) (matrixEntryOf matrixReader) (multiplicitiesGroups description.source) 0

variable {P₁ Wt : Type} (K₀ : KeyPub) (ℓ : WitLens Wt) (Nm : NumbersS)
  (Mg₀ : Common FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles files).EncodingRandomness TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles files).EncodingRandomness TableKey →
    List Fmt.Drawn → Place × Table)
  (tt : Nat → Coins (keyBook K₀) → Common FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles files).EncodingRandomness TableKey →
    List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles files).EncodingRandomness TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles files).EncodingRandomness TableKey → Prop)
  (Z₀ : ProofFile.Pub) (w₀ : FullSizeMatrix) (rc : (AtPublicFiles.AtFiles.protocolAtFiles files).EncodingRandomness) (x : Xi)

/-- **The stand at border 9, at the written value.** -/
theorem stand_nine_at_value (hs : KeySourced files description.source description.numbers
      description.later) (scope : VerifierAndGoals.InScope files = true) (hK₀ : fullPub = some K₀)
    (sd : Seed (shapeOf (pubKey Z₀ description.source.chains)) × ℕ)
    (hx : x = ⟨oodSh (shapeOf (pubKey Z₀ description.source.chains))
      (pubKey Z₀ description.source.chains)
      ⟨AtPublicFiles.AtFiles.HonestTerm.matrixReader w₀, ProofFile.Honest.Term.tableCoins files rc, sd⟩⟩)
    (hN : Function.Injective Nm.tenant) (hPin : ∀ v s y u, (Mg₀ v).pinT s y u)
    (hKp : ∀ b ∈ [0, 11], ∀ s, Kp b s s) (hE : ∀ s s', Kp 0 s s' → s' = s)
    (hV : Vd (inK w₀ rc x))
    (k : Coins (keyBook K₀)) (ds₁ ds₂ ds₄ ds₅ ds₇ ds₈ : List Fmt.Drawn)
    (hd₁ : ∀ blk, (threadAt description.source description.numbers description.later K₀
      (offlineValue description) ℓ Nm Mg₀ tk tt rest Kp Vd matrixReader (tableCoins files) Z₀ w₀ rc
      x).bs[1]? = some blk → drawsFit blk.rounds ds₁ = true)
    (hd₂ : ∀ blk, (threadAt description.source description.numbers description.later K₀
      (offlineValue description) ℓ Nm Mg₀ tk tt rest Kp Vd matrixReader (tableCoins files) Z₀ w₀ rc
      x).bs[2]? = some blk → drawsFit blk.rounds ds₂ = true)
    (hd₄ : ∀ blk, (threadAt description.source description.numbers description.later K₀
      (offlineValue description) ℓ Nm Mg₀ tk tt rest Kp Vd matrixReader (tableCoins files) Z₀ w₀ rc
      x).bs[4]? = some blk → drawsFit blk.rounds ds₄ = true)
    (hd₅ : ∀ blk, (threadAt description.source description.numbers description.later K₀
      (offlineValue description) ℓ Nm Mg₀ tk tt rest Kp Vd matrixReader (tableCoins files) Z₀ w₀ rc
      x).bs[5]? = some blk → drawsFit blk.rounds ds₅ = true)
    (hd₇ : ∀ blk, (threadAt description.source description.numbers description.later K₀
      (offlineValue description) ℓ Nm Mg₀ tk tt rest Kp Vd matrixReader (tableCoins files) Z₀ w₀ rc
      x).bs[7]? = some blk → drawsFit blk.rounds ds₇ = true)
    (hd₈ : ∀ blk, (threadAt description.source description.numbers description.later K₀
      (offlineValue description) ℓ Nm Mg₀ tk tt rest Kp Vd matrixReader (tableCoins files) Z₀ w₀ rc
      x).bs[8]? = some blk → drawsFit blk.rounds ds₈ = true) :
    NineEnd description.source description.numbers description.later K₀ (offlineValue description) ℓ
      Nm Mg₀ tk tt rest Kp Vd matrixReader (tableCoins files) Z₀ w₀ rc x k ds₁ ds₂ ds₄ ds₅ ds₇ ds₈ :=
  stand_nine_walked description.source description.numbers description.later K₀
    (offlineValue description) ℓ Nm Mg₀ tk tt rest Kp Vd matrixReader (tableCoins files) Z₀ w₀ rc x hs
    scope hK₀ sd hx hN hPin hKp hE hV (quietHalf_test _) (quietHalf_test _)
    (quietHalf_needs (quietHalf_test _)) (quietHalf_needs (quietHalf_test _)) (place_p12At _ _)
    (place_p12At _ _) k ds₁ ds₂ ds₄ ds₅ ds₇ ds₈ hd₁ hd₂ hd₄ hd₅ hd₇ hd₈

end Value

end AtPublicFiles.KeyStandWalked

#print axioms AtPublicFiles.KeyStandWalked.stand_nine_walked
#print axioms AtPublicFiles.KeyStandWalked.stand_nine_at_value
#print axioms AtPublicFiles.KeyStandWalked.eight_at_letters
#print axioms AtPublicFiles.KeyStandWalked.front_at_letters
