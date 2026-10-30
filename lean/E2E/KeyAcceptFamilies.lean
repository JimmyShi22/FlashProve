--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyAcceptFamilies.lean: E2E/KeyAcceptPairs.lean WITH THE THREE THREADS AND THE THREE LETTERS AS
FAMILIES IN THE PRIVATE INPUT AND THE INSTANCE. The accept law of the key file's prover, at any
description and any sides. The same calls as that file; no new proof. NOTHING IS CLAIMED OF ANY
PROVER.

Why. A thread whose sentences name the private input and the instance is another thread at each of
them. `debtsOne_of_pairs` (E2E/DebtsOfPairs.lean) is stated at one private input, one instance and
one coin, with the threads as letters: so a family goes in as it stands.

  `MembersS`: what is owed of three threads with their three letters at the members: that they sit;
    `OwesS`, `SaidNext` at every border and `YesS`, of each. The ten premises of
    `accLaw_key_of_pairs` on its threads, as one statement.
  **`accLaw_key_of_families`**: the accept law. `MembersS` and `AtRunS` are asked AT TIED INPUTS
    ALONE, of the family's member there; and `MembersS` only where the instance passes the
    description's test at the start (`okStart`), which is `AtRunS`' first clause: so whoever pays a
    debt at a member may spend it. Its conclusion is `accLaw_key_of_pairs`' to the letter.

Limits. All limits of E2E/KeyAcceptPairs.lean stand. CONDITIONAL THROUGHOUT. The families are free
letters: who lays them is not said here.

-/
import E2E.KeyAcceptPairs

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.KeyLink
open VerifiableInference.Desc (FileDescription)
open ProofFile.Honest

/-- **What is owed of three threads with their letters at the members.** A statement of premises: it
is claimed of nothing. -/
def MembersS {W₀ Rc Xi Ky Tr X₀ X : Type} {Bk : ProverCoinCounts} (F : FileDescription Xi)
    (G : Sides F Bk W₀ Rc Ky Tr X₀ X) (H₀ : Prover W₀ Rc Xi Ky Tr X₀ X)
    (U₁ : Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (U₂ : Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (U₃ : Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (S₁ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (S₂ : Nat → Coins Bk → Mid (Common W₀ Rc Ky) X₀ → Prop)
    (S₃ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) : Prop :=
  Sits F (G.prover H₀) U₁ U₂ U₃ ∧ OwesS U₁ S₁ ∧ OwesS U₂ S₂ ∧ OwesS U₃ S₃ ∧
    (∀ b, SaidNext U₁ S₁ b) ∧ (∀ b, SaidNext U₂ S₂ b) ∧ (∀ b, SaidNext U₃ S₃ b) ∧
    YesS U₁ S₁ (fallsBy G.falls₁ F.first.blocksInOrder) ∧ YesS U₂ S₂ (fallsBy G.falls₂ F.shared.blocksInOrder) ∧
    YesS U₃ S₃ (fallsBy G.falls₃ F.second.blocksInOrder)

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

/-- **THE ACCEPT LAW OF THE KEY FILE's PROVER, FROM THE DEBTS ON FAMILIES OF PAIRS**: the threads
and what is said may hang on the private input and the instance; all that is asked of them is asked
at tied inputs, the debts at the members only where the instance passes the test at the start. -/
theorem accLaw_key_of_families
    {pubJ : R₂ → R₃ → KeyInst → OnBytes.Maker.FrontMsg (List OnBytes.E) ×
      Compile.Joined.JoinMsg (List OnBytes.E) ByteArray × ByteArray}
    {Rel : (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I →
      (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd → KeyInst → Prop}
    {U₁ : ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I ×
      ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) ×
      (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Seed) → KeyInst →
      Thread B Fx.S₁ Fx.Cl
      (Local (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
        ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) KeyInst Tr)
      (Local (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
        ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) KeyInst Tr) X' KeyInst}
    {U₂ : ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I ×
      ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) ×
      (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Seed) → KeyInst →
      Thread B Fx.S₂ Fx.Cl Empty
      (Common (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
        ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) Ky) X₀ Ky}
    {U₃ : ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I ×
      ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) ×
      (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Seed) → KeyInst →
      Thread B Fx.S₃ Fx.Cl
      (Local (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
        ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) KeyInst Tr)
      (Local (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
        ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) KeyInst Tr) X' KeyInst}
    {S₁ : ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I ×
      ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) ×
      (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Seed) → KeyInst →
      Nat → Coins B → Mid (Local (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
      ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) KeyInst Tr) X' → Prop}
    {S₂ : ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I ×
      ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) ×
      (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Seed) → KeyInst →
      Nat → Coins B → Mid (Common (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
      ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) Ky) X₀ → Prop}
    {S₃ : ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I ×
      ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) ×
      (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Seed) → KeyInst →
      Nat → Coins B → Mid (Local (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
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
    (h4 : halvedAll Fx (G.prover H) = true)
    (hM : ∀ w x, Tied (DK.at frS.P.T.a) Fx (G.prover H) J ext pubJ sh Rel w x →
      Fx.okStart x = true →
      MembersS Fx G H (U₁ w x) (U₂ w x) (U₃ w x) (S₁ w x) (S₂ w x) (S₃ w x))
    (hat : ∀ w x (c : CoinOne B R₂ R₃),
      Tied (DK.at frS.P.T.a) Fx (G.prover H) J ext pubJ sh Rel w x →
      AtRunS Fx (G.prover H) (U₁ w x) (U₂ w x) (U₃ w x) (S₁ w x) (S₂ w x) (S₃ w x) w x c) :
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
        obtain ⟨hS, o₁, o₂, o₃, n₁, n₂, n₃, y₁, y₂, y₃⟩ := hM w x ht h0
        exact debtsOne_of_pairs G H hS hp o₁ o₂ o₃ n₁ n₂ n₃ y₁ y₂ y₃ w x c h0 hR hP a₁ a₂ e₁ e₂ a₃
          door fin)

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.accLaw_key_of_families
