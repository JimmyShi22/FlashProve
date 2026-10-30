--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyAcceptLaid.lean: THE ACCEPT LAW OF THE KEY FILE's HONEST PROVER AT THE KEY FILE's OWN
DESCRIPTION, WITH THE THREADS AS LAID: `accLaw_key_of_threads` (E2E/KeyAccept.lean) at
`keyFileDescription X N P` and at the threads of E2E/KeyThreadsLaid.lean. What the adapters pay falls out of
the premises: so THE PREMISES THAT ARE LEFT ARE WHAT IS STILL OWED AT THE KEY FILE. By calls.
NOTHING
IS CLAIMED OF ANY PROVER.

  `sits_withForm`: threads with further clauses on the verifier's state sit where the threads
    without them sit: the tests on a thread's letters do not read these clauses.
  `second_length`: the third chain has four sub-protocols.
  `yes₁_laid`, `yes₂_laid`, `yes₃_laid`: `Yes` at a whole chain, from `Accepted` at the
    sub-protocols that have no adapter: all but the last of the first chain; all but the last of the
    shared chain; number 2 of the third chain (its proximity test).
  `AtRunLeft …`: what is owed at one tied input and coin: as `AtRun`, without the third chain's
    start's return and without the last test, which are paid.
  **`accLaw_key_laid`**: the accept law. ITS PREMISES ON THREADS: the base threads sit; no part of a
    prover stands at the two ends' places; `Owes` at the three threads AS LAID; `Accepted` at the
    sub-protocols named above; `AtRunLeft` at every tied input and coin.

Limits.
- CONDITIONAL THROUGHOUT: all limits of E2E/KeyAccept.lean and E2E/KeyThreadsLaid.lean stand.
- THE CLAUSES ARE MOVED, NOT PAID: `Owes`, `Enters₁`, `Enters₂` and `DoorBehind` are asked of the
  threads WITH the added clauses: each sub-protocol has to keep them, and the starts have to give
  them.
- THE FALL's SET HANGS ON THE PROVER's COIN. A bound on its measure at each fixed coin bounds the
  share over verifier randomness and coins together; it does not bound the set of verifier
  randomness at which SOME coin's run falls. So a statement of completeness takes the number as an
  error over verifier randomness and coins together; the fall is a second set, which reads the coin,
  beside the abort set, and is not folded into it: the form of `OnBytes.Prover.HonFit` (its accept
  laws outside the abort set and the fall at that coin; its measures at each fixed coin).
- The base threads, the numbers, the rows G with their falls, the prover of parts, the seam, the
  table and X, N, P are free letters. The premises that are not on threads are as in
  E2E/KeyAccept.lean.

-/
import E2E.KeyAccept
import E2E.KeyThreadsLaid

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.KeyLink
open VerifiableInference.Desc (FileDescription)
open ProofFile.Honest

/-- Threads with further clauses on the verifier's state sit where those without them sit. -/
theorem sits_withForm {W₀ Rc Xi Ky Tr X₀ X : Type} {Bk : ProverCoinCounts} {F : FileDescription Xi}
    {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    {U₁ : Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    {U₂ : Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky}
    {U₃ : Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    (Φ₁ : Nat → F.S₁ → Prop) (Φ₂ : Nat → F.S₂ → Prop) (Φ₃ : Nat → F.S₃ → Prop)
    (h : Sits F H U₁ U₂ U₃) : Sits F H (withForm U₁ Φ₁) (withForm U₂ Φ₂) (withForm U₃ Φ₃) :=
  ⟨h.one, h.two, h.three, h.fits⟩

/-- **What is owed at one tied input and one coin**, the third chain's start's return and the last
test apart. A statement of premises: it is claimed of nothing. -/
def AtRunLeft {W₀ Rc Xi Ky Tr X₀ X Sd R₂ R₃ : Type} {Bk : ProverCoinCounts} (F : FileDescription Xi)
    (H : Prover W₀ Rc Xi Ky Tr X₀ X)
    (U₁ : Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (U₂ : Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (U₃ : Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (w : W₀ × Rc × Sd) (x : Xi) (c : CoinOne Bk R₂ R₃) : Prop :=
  F.okStart x = true ∧
    ∃ R, ready F Bk H w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ = .ok R ∧ PlanServes H w.1 w.2.1 R ∧
      Enters₁ F H U₁ w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ R ∧
      Enters₂ F H U₂ w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ R ∧
      DoorBehind F H U₁ U₂ U₃ x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ R

end AtPublicFiles.KeyLink

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Cut AtPublicFiles.KeyLink
open OnBytes.Flat (Files relationsAndEncodingOfClaims RecFull Coding silK front₀ join₀)
open OnBytes.Slice (frS frZ DecR)
open _root_.Run.PQ (View XO)
open OnBytes.Maker (WholeD)
open _root_.Run (ckP)
open VerifiableInference.OnPublicFiles (threeProtocolsAtFullSize InnerCompilerInputAndAnalysisFieldsAtFullSize innerCompilerInputAtFullSize)
open VerifiableInference.Desc.Key (keyInstanceOfOutOfDomainSample)
open ProofFile.Honest (Prover KeyAndJoiningRoundMessages ProverCoinCounts Sides Thread Local Common Sits Owes Yes Accepted fallsBy Tied
  DataFits halvedAll sealPlain drawsAt)
open OnBytes.Prover (AccLaw)
open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms

section Chains
variable {W₀ Rc Ky Tr X₀ Xh : Type} {Bk : ProverCoinCounts} (X : VerifiableInference.Desc.Key.Source)
  (N : H2U.PlaceNums) (P : VerifiableInference.Desc.Key.LaterPlaces) (q : KeyNums)
  (U₁ : Thread Bk (keyFileDescription X N P).S₁ (keyFileDescription X N P).Cl (Local W₀ Rc KeyInst Tr)
    (Local W₀ Rc KeyInst Tr) Xh KeyInst)
  (U₂ : Thread Bk (keyFileDescription X N P).S₂ (keyFileDescription X N P).Cl Empty (Common W₀ Rc Ky) X₀ Ky)
  (U₃ : Thread Bk (keyFileDescription X N P).S₃ (keyFileDescription X N P).Cl (Local W₀ Rc KeyInst Tr)
    (Local W₀ Rc KeyInst Tr) Xh KeyInst)

/-- The third chain has four sub-protocols. -/
theorem second_length : (keyFileDescription X N P).second.blocksInOrder.length = 4 := rfl

/-- **`Yes` at the first chain**, from `Accepted` at all its sub-protocols but the last. -/
theorem yes₁_laid {fall : Nat → (keyFileDescription X N P).S₁ → List Fmt.Drawn → Option String}
    (hbs : U₁.bs = (keyFileDescription X N P).first.blocksInOrder)
    (hn : (U₁.hs.find? fun g => g.place == (keyFileDescription X N P).first.last.place) = none)
    (h : ∀ b, b + 1 < (keyFileDescription X N P).first.blocksInOrder.length →
      Accepted (withForm U₁ (Form₁ X N P q)) fall b) :
    Yes (withForm U₁ (Form₁ X N P q)) fall := by
  intro b hb
  have hb' : b < (keyFileDescription X N P).first.blocksInOrder.length := by
    have e : (withForm U₁ (Form₁ X N P q)).bs = (keyFileDescription X N P).first.blocksInOrder := hbs
    rw [e] at hb
    exact hb
  by_cases hl : b + 1 < (keyFileDescription X N P).first.blocksInOrder.length
  · exact h b hl
  · have e : b = (keyFileDescription X N P).first.blocksInOrder.length - 1 := by omega
    rw [e]
    exact seal_laid X N P q U₁ hbs hn

/-- **`Yes` at the shared chain**, from `Accepted` at all its sub-protocols but the last. -/
theorem yes₂_laid {fall : Nat → (keyFileDescription X N P).S₂ → List Fmt.Drawn → Option String}
    (hbs : U₂.bs = (keyFileDescription X N P).shared.blocksInOrder)
    (hn : (U₂.hs.find? fun g => g.place == (keyFileDescription X N P).shared.last.place) = none)
    (h : ∀ b, b + 1 < (keyFileDescription X N P).shared.blocksInOrder.length →
      Accepted (withForm U₂ (Form₂ X N P q)) fall b) :
    Yes (withForm U₂ (Form₂ X N P q)) fall := by
  intro b hb
  have hb' : b < (keyFileDescription X N P).shared.blocksInOrder.length := by
    have e : (withForm U₂ (Form₂ X N P q)).bs = (keyFileDescription X N P).shared.blocksInOrder := hbs
    rw [e] at hb
    exact hb
  by_cases hl : b + 1 < (keyFileDescription X N P).shared.blocksInOrder.length
  · exact h b hl
  · have e : b = (keyFileDescription X N P).shared.blocksInOrder.length - 1 := by omega
    rw [e]
    exact end₂_laid X N P q U₂ hbs hn

/-- **`Yes` at the third chain**, in scope, from `Accepted` at its proximity test, number 2. -/
theorem yes₃_laid {fall : Nat → (keyFileDescription X N P).S₃ → List Fmt.Drawn → Option String}
    (hbs : U₃.bs = (keyFileDescription X N P).second.blocksInOrder) (hp : (keyFileDescription X N P).planOk = true)
    {Z : VerifierAndGoals.PublicFiles} (hs : KeySourced Z X N P) (scope : VerifierAndGoals.InScope Z = true)
    (h : Accepted (withForm U₃ (Form₃ X N P q)) fall 2) :
    Yes (withForm U₃ (Form₃ X N P q)) fall := by
  intro b hb
  have hb' : b < 4 := by
    have e : (withForm U₃ (Form₃ X N P q)).bs = (keyFileDescription X N P).second.blocksInOrder := hbs
    rw [e, second_length] at hb
    exact hb
  rcases b with _ | _ | _ | _ | b
  · exact k14Second_laid X N P q U₃ hbs hp
  · exact takenSources_laid X N P q U₃ hbs hs scope
  · exact h
  · exact end₃_laid X N P q U₃ hbs
  · omega

end Chains

variable {Xq : Type} {A : (frS.toDecR frZ 402653181).Claims Xq} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → View → View → View → Bool}
  {runP : Xq × RecFull → View → View → View → Bool} {ds : List TypedOracleCompiler.Run.PQ.RD}
  {xs : List XO} {dec : RecFull × RecFull → View → Bool} {rK rP : RecFull} {depthReq : ℕ}
  {early : Xq → Xq} {salt K : ℕ}
  {Q : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers}
  (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K Q)
  (X : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
  (P : VerifiableInference.Desc.Key.LaterPlaces) (q : KeyNums) {Ky Tr X₀ X' R₂ R₃ : Type} (B : ProverCoinCounts)
  (G : Sides (keyFileDescription X N P) B (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
    ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) Ky Tr X₀ X')
  (H : Prover (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
    ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) KeyInst Ky Tr X₀ X')
  [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
  (J : R₂ → R₃ → KeyAndJoiningRoundMessages (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
    ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd)
    (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Seed KeyInst Ky (OnBytes.Maker.FrontMsg (List OnBytes.E))
    (Compile.Joined.JoinMsg (List OnBytes.E) ByteArray) ByteArray)
  (sh : Ky → (keyFileDescription X N P).S₂)
  (ext : (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I ×
    ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) ×
    (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Seed →
    (Iop.oneExternalString (2 ^ (DK.at frS.P.T.a).a) _root_.Run.PQ.SgX).Str)

/-- **THE ACCEPT LAW AT THE KEY FILE's OWN DESCRIPTION, WITH THE THREADS AS LAID: WHAT IS LEFT.** -/
theorem accLaw_key_laid
    {pubJ : R₂ → R₃ → KeyInst → OnBytes.Maker.FrontMsg (List OnBytes.E) ×
      Compile.Joined.JoinMsg (List OnBytes.E) ByteArray × ByteArray}
    {Rel : (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I →
      (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd → KeyInst → Prop}
    {U₁ : Thread B (keyFileDescription X N P).S₁ (keyFileDescription X N P).Cl
      (Local (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
        ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) KeyInst Tr)
      (Local (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
        ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) KeyInst Tr) X' KeyInst}
    {U₂ : Thread B (keyFileDescription X N P).S₂ (keyFileDescription X N P).Cl Empty
      (Common (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
        ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) Ky) X₀ Ky}
    {U₃ : Thread B (keyFileDescription X N P).S₃ (keyFileDescription X N P).Cl
      (Local (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
        ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) KeyInst Tr)
      (Local (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
        ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) KeyInst Tr) X' KeyInst}
    {Z : VerifierAndGoals.PublicFiles} (hs : KeySourced Z X N P) (scope : VerifierAndGoals.InScope Z = true)
    (hFull : LPFFrame.FullAt (ckP .two) (DK.at frS.P.T.a)) (hCar : ∀ w, LPFFrame.Carries (ext w))
    (hD : DataFits (keyFileDescription X N P) (DK.at frS.P.T.a)) (hq : sealPlain (keyFileDescription X N P) = true)
    (hdue : ∀ ρ, (drawsAt (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty
      ρ).due (keyFileDescription X N P) = true)
    (hrun : ∀ a v₁ v₂ v₃, (keyFileDescription X N P).run (keyInstanceOfOutOfDomainSample a) v₁ v₂ v₃ = true → runK a v₁ v₂ v₃ = true)
    (hsil : ∀ r2 r3 w a,
      Tied (DK.at frS.P.T.a) (keyFileDescription X N P) (G.prover H) J ext pubJ sh Rel w (keyInstanceOfOutOfDomainSample a) →
      silK a ((J r2 r3).front w.1 w.2.1 w.2.2 (keyInstanceOfOutOfDomainSample a)) ((J r2 default).join w.1 w.2.1 w.2.2)
        ((J r2 r3).seam w.1 w.2.1 w.2.2 (keyInstanceOfOutOfDomainSample a)) = true)
    (h4 : halvedAll (keyFileDescription X N P) (G.prover H) = true)
    (hS : Sits (keyFileDescription X N P) (G.prover H) U₁ U₂ U₃)
    (hn₁ : (U₁.hs.find? fun g => g.place == (keyFileDescription X N P).first.last.place) = none)
    (hn₂ : (U₂.hs.find? fun g => g.place == (keyFileDescription X N P).shared.last.place) = none)
    (o₁ : Owes (withForm U₁ (Form₁ X N P q))) (o₂ : Owes (withForm U₂ (Form₂ X N P q)))
    (o₃ : Owes (withForm U₃ (Form₃ X N P q)))
    (y₁ : ∀ b, b + 1 < (keyFileDescription X N P).first.blocksInOrder.length →
      Accepted (withForm U₁ (Form₁ X N P q)) (fallsBy G.falls₁ (keyFileDescription X N P).first.blocksInOrder) b)
    (y₂ : ∀ b, b + 1 < (keyFileDescription X N P).shared.blocksInOrder.length →
      Accepted (withForm U₂ (Form₂ X N P q)) (fallsBy G.falls₂ (keyFileDescription X N P).shared.blocksInOrder) b)
    (y₃ : Accepted (withForm U₃ (Form₃ X N P q)) (fallsBy G.falls₃ (keyFileDescription X N P).second.blocksInOrder) 2)
    (hat : ∀ w x (c : CoinOne B R₂ R₃),
      Tied (DK.at frS.P.T.a) (keyFileDescription X N P) (G.prover H) J ext pubJ sh Rel w x →
      AtRunLeft (keyFileDescription X N P) (G.prover H) (withForm U₁ (Form₁ X N P q))
        (withForm U₂ (Form₂ X N P q)) (withForm U₃ (Form₃ X N P q)) w x c) :
    ∀ w (a : RecFull) (c : CoinOne B R₂ R₃),
      Tied (DK.at frS.P.T.a) (keyFileDescription X N P) (G.prover H) J ext pubJ sh Rel w (keyInstanceOfOutOfDomainSample a) →
      AccLaw (batTC (innerCompilerInputAtFullSize T).protocol (innerCompilerInputAtFullSize T).offlineRoundSplits) (wTC (innerCompilerInputAtFullSize T).queryLayout) a
        ((keyHonestAny A (relationsAndEncodingOfClaims A E) DK DP (keyFileDescription X N P) runP ds xs dec rK rP depthReq early salt
          B (G.prover H) J sh ext runK Q).ext w)
        ((keyHonestAny A (relationsAndEncodingOfClaims A E) DK DP (keyFileDescription X N P) runP ds xs dec rK rP depthReq early salt
          B (G.prover H) J sh ext runK Q).strat w a c)
        ((keyHonestAny A (relationsAndEncodingOfClaims A E) DK DP (keyFileDescription X N P) runP ds xs dec rK rP depthReq early salt
          B (G.prover H) J sh ext runK Q).withheld w a ∪
          fallOne (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty
            (keyFileDescription X N P) B G H w (keyInstanceOfOutOfDomainSample a) c) :=
  accLaw_key_of_threads T (keyFileDescription X N P) B G H J sh ext hFull hCar hD hs.named.plan hq hdue hrun
    hsil h4 (sits_withForm _ _ _ hS) o₁ o₂ o₃ (yes₁_laid X N P q U₁ hS.one.2.2.2.1 hn₁ y₁)
    (yes₂_laid X N P q U₂ hS.two.2.2.2.1 hn₂ y₂)
    (yes₃_laid X N P q U₃ hS.three.2.2.2.1 hs.named.plan hs scope y₃) fun w x c ht => by
      obtain ⟨h0, R, hR, hP, a₁, a₂, a₃⟩ := hat w x c ht
      exact ⟨h0, R, hR, hP, a₁, a₂, a₃, door_laid X N P q U₁ U₂ hs.named.plan x _,
        fin_laid X N P q U₁ U₂ U₃ x _⟩

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.KeyLink.sits_withForm
#print axioms AtPublicFiles.AtFiles.second_length
#print axioms AtPublicFiles.AtFiles.yes₁_laid
#print axioms AtPublicFiles.AtFiles.yes₂_laid
#print axioms AtPublicFiles.AtFiles.yes₃_laid
#print axioms AtPublicFiles.AtFiles.accLaw_key_laid
