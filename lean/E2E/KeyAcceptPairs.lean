--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyAcceptPairs.lean: E2E/KeyAccept.lean WITH THE DEBTS ASKED FROM THE PAIR OF A THREAD AND WHAT
IS SAID: the accept law of the key file's prover, at any description, any sides and any three
threads with any three letters, from
`debtsOne_of_pairs` (E2E/DebtsOfPairs.lean). One call more than that file. NOTHING IS CLAIMED OF ANY
PROVER.

  `AtRunS`: what is owed at one tied input and one coin, beside the debts at the members: `AtRun`
    with the letter at the two starts, at the states as `ChainProgress.start` lays them (the field `opened`
    is `some []`), and with the door and the end asked from the pairs (`DoorBehindS`, `DoorYesS`,
    `FinYesS`).
  **`accLaw_key_of_pairs`**: the accept law. Its conclusion is `accLaw_key_of_threads`' to the
    letter.

Limits. All limits of E2E/KeyAccept.lean and E2E/DebtsOfPairs.lean stand. CONDITIONAL THROUGHOUT.
The three letters are free: who lays them, and who pays `SaidNext`, is not said here.

-/
import E2E.DebtsOfPairs

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.KeyLink
open VerifiableInference.Desc (FileDescription)
open ProofFile.Honest

/-- **What is owed at one tied input and one coin**, beside the debts at the members, with the
letter at the two starts (at the states whose field `opened` is `some []`) and with the door and the
end asked from the pairs. A statement of premises: it is claimed of nothing. -/
def AtRunS {W₀ Rc Xi Ky Tr X₀ X Sd R₂ R₃ : Type} {Bk : ProverCoinCounts} (F : FileDescription Xi)
    (H : Prover W₀ Rc Xi Ky Tr X₀ X)
    (U₁ : Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (U₂ : Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (U₃ : Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (S₁ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (S₂ : Nat → Coins Bk → Mid (Common W₀ Rc Ky) X₀ → Prop)
    (S₃ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (w : W₀ × Rc × Sd) (x : Xi) (c : CoinOne Bk R₂ R₃) : Prop :=
  F.okStart x = true ∧
    ∃ R, ready F Bk H w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ = .ok R ∧ PlanServes H w.1 w.2.1 R ∧
      Enters₁ F H U₁ w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ R ∧
      Enters₂ F H U₂ w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ R ∧
      S₁ 0 ⟨c.2.1.1, c.1.1, c.2.1.2⟩ { R.start₁ H with opened := some [] } ∧
      S₂ 0 ⟨c.2.1.1, c.1.1, c.2.1.2⟩ { R.start₂ H with opened := some [] } ∧
      DoorBehindS F H U₁ U₂ U₃ S₁ S₂ S₃ x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ R ∧
      DoorYesS F U₁ U₂ S₁ S₂ x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ ∧
      FinYesS F U₁ U₂ U₃ S₁ S₂ S₃ x ⟨c.2.1.1, c.1.1, c.2.1.2⟩

end AtPublicFiles.KeyLink

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Cut AtPublicFiles.KeyLink
open OnBytes.Flat (Files relationsAndEncodingOfClaims RecFull Coding silK front₀ join₀)
open OnBytes.Slice (frS frZ DecR)
open _root_.Run.PQ (View XO)
open OnBytes.Maker (WholeD)
open _root_.Run (ckP)
open VerifiableInference.OnPublicFiles (threeProtocolsAtFullSize InnerCompilerInputAndAnalysisFieldsAtFullSize innerCompilerInputAtFullSize)
open VerifiableInference.Desc (FileDescription)
open VerifiableInference.Desc.Key (keyInstanceOfOutOfDomainSample)
open ProofFile.Honest (Prover KeyAndJoiningRoundMessages ProverCoinCounts Sides Thread Local Common Sits OwesS YesS SaidNext Coins Mid
  fallsBy Tied DataFits halvedAll sealPlain drawsAt)
open OnBytes.Prover (AccLaw)
open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms

variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → View → View → View → Bool}
  {runP : X × RecFull → View → View → View → Bool} {ds : List TypedOracleCompiler.Run.PQ.RD}
  {xs : List XO} {dec : RecFull × RecFull → View → Bool} {rK rP : RecFull} {depthReq : ℕ}
  {early : X → X} {salt K : ℕ}
  {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers}
  (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)
  (Fx : FileDescription KeyInst) {Ky Tr X₀ X' R₂ R₃ : Type} (B : ProverCoinCounts)
  (G : Sides Fx B (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
    ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) Ky Tr X₀ X')
  (H : Prover (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
    ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) KeyInst Ky Tr X₀ X')
  [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
  (J : R₂ → R₃ → KeyAndJoiningRoundMessages (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
    ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd)
    (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Seed KeyInst Ky (OnBytes.Maker.FrontMsg (List OnBytes.E))
    (Compile.Joined.JoinMsg (List OnBytes.E) ByteArray) ByteArray)
  (sh : Ky → Fx.S₂)
  (ext : (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I ×
    ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) ×
    (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Seed →
    (Iop.oneExternalString (2 ^ (DK.at frS.P.T.a).a) _root_.Run.PQ.SgX).Str)

/-- **THE ACCEPT LAW OF THE KEY FILE's PROVER, FROM THE DEBTS ON THE PAIRS.** -/
theorem accLaw_key_of_pairs
    {pubJ : R₂ → R₃ → KeyInst → OnBytes.Maker.FrontMsg (List OnBytes.E) ×
      Compile.Joined.JoinMsg (List OnBytes.E) ByteArray × ByteArray}
    {Rel : (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I →
      (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd → KeyInst → Prop}
    {U₁ : Thread B Fx.S₁ Fx.Cl
      (Local (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
        ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) KeyInst Tr)
      (Local (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
        ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) KeyInst Tr) X' KeyInst}
    {U₂ : Thread B Fx.S₂ Fx.Cl Empty
      (Common (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
        ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) Ky) X₀ Ky}
    {U₃ : Thread B Fx.S₃ Fx.Cl
      (Local (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
        ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) KeyInst Tr)
      (Local (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
        ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) KeyInst Tr) X' KeyInst}
    {S₁ : Nat → Coins B → Mid (Local (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
      ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) KeyInst Tr) X' → Prop}
    {S₂ : Nat → Coins B → Mid (Common (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
      ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) Ky) X₀ → Prop}
    {S₃ : Nat → Coins B → Mid (Local (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
      ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) KeyInst Tr) X' → Prop}
    (hFull : LPFFrame.FullAt (ckP .two) (DK.at frS.P.T.a)) (hCar : ∀ w, LPFFrame.Carries (ext w))
    (hD : DataFits Fx (DK.at frS.P.T.a)) (hp : Fx.planOk = true) (hq : sealPlain Fx = true)
    (hdue : ∀ ρ, (drawsAt (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty
      ρ).due Fx = true)
    (hrun : ∀ a v₁ v₂ v₃, Fx.run (keyInstanceOfOutOfDomainSample a) v₁ v₂ v₃ = true → runK a v₁ v₂ v₃ = true)
    (hsil : ∀ r2 r3 w a,
      Tied (DK.at frS.P.T.a) Fx (G.prover H) J ext pubJ sh Rel w (keyInstanceOfOutOfDomainSample a) →
      silK a ((J r2 r3).front w.1 w.2.1 w.2.2 (keyInstanceOfOutOfDomainSample a)) ((J r2 default).join w.1 w.2.1 w.2.2)
        ((J r2 r3).seam w.1 w.2.1 w.2.2 (keyInstanceOfOutOfDomainSample a)) = true)
    (h4 : halvedAll Fx (G.prover H) = true) (hS : Sits Fx (G.prover H) U₁ U₂ U₃)
    (o₁ : OwesS U₁ S₁) (o₂ : OwesS U₂ S₂) (o₃ : OwesS U₃ S₃) (n₁ : ∀ b, SaidNext U₁ S₁ b)
    (n₂ : ∀ b, SaidNext U₂ S₂ b) (n₃ : ∀ b, SaidNext U₃ S₃ b)
    (y₁ : YesS U₁ S₁ (fallsBy G.falls₁ Fx.first.blocksInOrder))
    (y₂ : YesS U₂ S₂ (fallsBy G.falls₂ Fx.shared.blocksInOrder))
    (y₃ : YesS U₃ S₃ (fallsBy G.falls₃ Fx.second.blocksInOrder))
    (hat : ∀ w x (c : CoinOne B R₂ R₃),
      Tied (DK.at frS.P.T.a) Fx (G.prover H) J ext pubJ sh Rel w x →
      AtRunS Fx (G.prover H) U₁ U₂ U₃ S₁ S₂ S₃ w x c) :
    ∀ w (a : RecFull) (c : CoinOne B R₂ R₃),
      Tied (DK.at frS.P.T.a) Fx (G.prover H) J ext pubJ sh Rel w (keyInstanceOfOutOfDomainSample a) →
      AccLaw (batTC (innerCompilerInputAtFullSize T).protocol (innerCompilerInputAtFullSize T).offlineRoundSplits) (wTC (innerCompilerInputAtFullSize T).queryLayout) a
        ((keyHonestAny A (relationsAndEncodingOfClaims A E) DK DP Fx runP ds xs dec rK rP depthReq early salt B
          (G.prover H) J sh ext runK P).ext w)
        ((keyHonestAny A (relationsAndEncodingOfClaims A E) DK DP Fx runP ds xs dec rK rP depthReq early salt B
          (G.prover H) J sh ext runK P).strat w a c)
        ((keyHonestAny A (relationsAndEncodingOfClaims A E) DK DP Fx runP ds xs dec rK rP depthReq early salt B
          (G.prover H) J sh ext runK P).withheld w a ∪
          fallOne (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty Fx B G H w
            (keyInstanceOfOutOfDomainSample a) c) :=
  accLaw_keyHonestAny T Fx B G H J sh ext hFull hCar hrun hsil
    (yesOne_of_debts (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty Fx silKey B
      G H J sh ext hp hq hD h4 hdue fun w x c ht => by
        obtain ⟨h0, R, hR, hP, a₁, a₂, e₁, e₂, a₃, door, fin⟩ := hat w x c ht
        exact debtsOne_of_pairs G H hS hp o₁ o₂ o₃ n₁ n₂ n₃ y₁ y₂ y₃ w x c h0 hR hP a₁ a₂ e₁ e₂ a₃
          door fin)

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.KeyLink.AtRunS
#print axioms AtPublicFiles.AtFiles.accLaw_key_of_pairs
