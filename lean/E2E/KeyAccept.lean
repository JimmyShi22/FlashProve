--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyAccept.lean: THE ACCEPT LAW OF THE KEY FILE's HONEST PROVER, FROM THE DEBTS AS THEY ARE OWED
ON THREADS: the whole from the parts, in one statement. Three calls: `debtsOne_of_threads`
(E2E/DebtsOfThreads.lean), `yesOne_of_debts`, `accLaw_keyHonestAny` (E2E/KeyLink.lean). NOTHING IS
CLAIMED OF ANY PROVER.

  `AtRun …`: what is owed at one tied input and one coin, beside the debts at the members: the
    instance's first test accepts; the run can be made ready; the plan serves; the two first threads
    are entered; the second chain's start; the last test. A statement of premises.
  **`accLaw_key_of_threads`**: at any letters of the full size, for every private input w, OOD
    sample a and coin c with (w, the written key of a) tied: `OnBytes.Prover.AccLaw` at the compiled
    verifier's own key file's protocol and wiring, at the external string, the strategy and the
    abort set of `keyHonestAny`, outside the abort set and the set at which a fall speaks.
    ITS PREMISES, BY KIND.
    On the data and the table: `FullAt`, `Carries`, `DataFits`.
    On the description: its tests on the plan accept; its sealing rounds are plain; every list of
      challenges that typed verifier randomness gives is due; where its decision accepts at the
      written key, so does the object's decision on the key file.
    On the seam: the test on the three rounds without a challenge accepts its three values.
    On the prover of parts: every place with a round has a half.
    ON THREADS: three threads sit; `Owes` and `Yes` at every member of the three chains, at the
      rows' own lists of falls; `AtRun` at every tied input and coin.

Limits.
- CONDITIONAL THROUGHOUT: all limits of E2E/KeyLink.lean and E2E/DebtsOfThreads.lean stand. No
  premise on threads is shown of the key file's description or of any prover of parts.
- THE LISTS OF FALLS ARE FREE LETTERS. The law says something at a member only beside each fall's
  text and its measured share, at each fixed coin.
- THE FALL's SET HANGS ON THE PROVER's COIN. A bound on its measure at each fixed coin bounds the
  share over verifier randomness and coins together; it does not bound the set of verifier
  randomness at which SOME coin's run falls. So a statement of completeness takes the number as an
  error over verifier randomness and coins together; the fall is a second set, which reads the coin,
  beside the abort set, and is not folded into it: the form of `OnBytes.Prover.HonFit` (its accept
  laws outside the abort set and the fall at that coin; its measures at each fixed coin).
- Pointwise in the verifier randomness: no measure. No OOD seed is set aside.
- Nothing at public files: the letters are any letters of the full size.

-/
import E2E.DebtsOfThreads

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.KeyLink
open VerifiableInference.Desc (FileDescription)
open ProofFile.Honest

/-- **What is owed at one tied input and one coin**, beside the debts at the members. A statement of
premises: it is claimed of nothing. -/
def AtRun {W₀ Rc Xi Ky Tr X₀ X Sd R₂ R₃ : Type} {Bk : ProverCoinCounts} (F : FileDescription Xi)
    (H : Prover W₀ Rc Xi Ky Tr X₀ X)
    (U₁ : Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (U₂ : Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (U₃ : Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (w : W₀ × Rc × Sd) (x : Xi) (c : CoinOne Bk R₂ R₃) : Prop :=
  F.okStart x = true ∧
    ∃ R, ready F Bk H w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ = .ok R ∧ PlanServes H w.1 w.2.1 R ∧
      Enters₁ F H U₁ w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ R ∧
      Enters₂ F H U₂ w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ R ∧
      DoorBehind F H U₁ U₂ U₃ x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ R ∧
      DoorYes F U₁ U₂ x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ ∧ FinYes F U₁ U₂ U₃ x ⟨c.2.1.1, c.1.1, c.2.1.2⟩

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
open ProofFile.Honest (Prover KeyAndJoiningRoundMessages ProverCoinCounts Sides Thread Local Common Sits Owes Yes fallsBy Tied DataFits
  halvedAll sealPlain drawsAt)
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

/-- **THE ACCEPT LAW OF THE KEY FILE's PROVER, FROM THE DEBTS ON THREADS.** -/
theorem accLaw_key_of_threads
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
    (hFull : LPFFrame.FullAt (ckP .two) (DK.at frS.P.T.a)) (hCar : ∀ w, LPFFrame.Carries (ext w))
    (hD : DataFits Fx (DK.at frS.P.T.a)) (hp : Fx.planOk = true) (hq : sealPlain Fx = true)
    (hdue : ∀ ρ, (drawsAt (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty
      ρ).due Fx = true)
    (hrun : ∀ a v₁ v₂ v₃, Fx.run (keyInstanceOfOutOfDomainSample a) v₁ v₂ v₃ = true → runK a v₁ v₂ v₃ = true)
    (hsil : ∀ r2 r3 w a,
      Tied (DK.at frS.P.T.a) Fx (G.prover H) J ext pubJ sh Rel w (keyInstanceOfOutOfDomainSample a) →
      silK a ((J r2 r3).front w.1 w.2.1 w.2.2 (keyInstanceOfOutOfDomainSample a)) ((J r2 default).join w.1 w.2.1 w.2.2)
        ((J r2 r3).seam w.1 w.2.1 w.2.2 (keyInstanceOfOutOfDomainSample a)) = true)
    (h4 : halvedAll Fx (G.prover H) = true) (hS : Sits Fx (G.prover H) U₁ U₂ U₃) (o₁ : Owes U₁)
    (o₂ : Owes U₂) (o₃ : Owes U₃) (y₁ : Yes U₁ (fallsBy G.falls₁ Fx.first.blocksInOrder))
    (y₂ : Yes U₂ (fallsBy G.falls₂ Fx.shared.blocksInOrder))
    (y₃ : Yes U₃ (fallsBy G.falls₃ Fx.second.blocksInOrder))
    (hat : ∀ w x (c : CoinOne B R₂ R₃),
      Tied (DK.at frS.P.T.a) Fx (G.prover H) J ext pubJ sh Rel w x →
      AtRun Fx (G.prover H) U₁ U₂ U₃ w x c) :
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
        obtain ⟨h0, R, hR, hP, a₁, a₂, a₃, door, fin⟩ := hat w x c ht
        exact debtsOne_of_threads G H hS hp o₁ o₂ o₃ y₁ y₂ y₃ w x c h0 hR hP a₁ a₂ a₃ door fin)

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.accLaw_key_of_threads
