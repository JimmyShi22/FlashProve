--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyAcceptProver.lean: THE ACCEPT LAW OF THE KEY FILE's HONEST PROVER, WITH THE PROVER OF PARTS
`keyProver K` (E2E/KeyProver.lean) LAID IN: `accLaw_key_laid` (E2E/KeyAcceptLaid.lean) at the bare
rows of that prover (E2E/KeyLaid.lean) and at threads seated on it. What the tests with code pay
falls out of the premises. By calls. NOTHING IS CLAIMED OF WHAT THE PARTS SEND.

  `find_none_of_places`: no half stands at a place that is none of the halves' places.
  `no_half_seal₁`, `no_half_seal₂`: so none of `keyProver K`'s stands at either sealed chain's end.
  `accLaw_key_at`: `accLaw_key_laid` with a letter for the rows' prover: the step by which a prover
    that is equal to it is laid in.
  **`accLaw_keyProver`**: the accept law at `keyHonestAny … (keyProver K) …`, outside its abort set
    and the set at which a fall of three given lists speaks. PAID HERE: a half at every sub-protocol
    that sends (`halvedAll_key`) · the fifteen equations of `Sits` · no half at the two ends.
    LEFT, ON THE PROVER AND THE THREADS: the letters bear the sixteen places (`KeyParts.AtAll`) ·
    the tests with code on the base threads' other letters (`Thread.fits`, thrice) · `Owes` at the
    three threads as laid · `Accepted` at the sub-protocols without an adapter · `AtRunLeft` at
    every tied input and coin.
    LEFT, NOT ON THREADS: as in E2E/KeyAccept.lean, but for `halvedAll` and the test on the plan.

Limits.
- CONDITIONAL THROUGHOUT: all limits of E2E/KeyAcceptLaid.lean and E2E/KeyLaid.lean stand. THE
  CLAUSES LAID INTO THE THREADS ARE MOVED, NOT PAID.
- The book B is a free letter: no test on a book is among the premises of the accept law.
- The four proximity tests' halves, what the sendings' rows hold, the lookups' summands, the readers
  and the pile's filler are letters of `KeyParts`.
- THE LISTS OF FALLS ARE FREE LETTERS, and the fall's set hangs on the prover's coin: as in
  E2E/KeyLink.lean's limits.

-/
import E2E.KeyAcceptLaid
import E2E.KeyLaid

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.KeyLink
open VerifiableInference.Desc (Place)
open ProofFile.Honest

/-- No half stands at a place that is none of the halves' places. -/
theorem find_none_of_places {V W Y : Type} (hs : List (Placed V W Y)) (p : Place)
    (h : ((hs.map (·.place)).any (· == p)) = false) :
    (hs.find? fun g => g.place == p) = none := by
  rw [List.find?_eq_none]
  intro g hg hp
  have a : (hs.any fun g => g.place == p) = true := List.any_eq_true.2 ⟨g, hg, hp⟩
  rw [any_places, h] at a
  cases a

end AtPublicFiles.KeyLink

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Cut AtPublicFiles.KeyLink AtPublicFiles.KeyFile AtPublicFiles.KeyBook
open OnBytes.Flat (Files relationsAndEncodingOfClaims RecFull Coding silK front₀ join₀)
open OnBytes.Slice (frS frZ DecR)
open _root_.Run.PQ (View XO)
open OnBytes.Maker (WholeD)
open _root_.Run (ckP)
open VerifiableInference.OnPublicFiles (threeProtocolsAtFullSize InnerCompilerInputAndAnalysisFieldsAtFullSize innerCompilerInputAtFullSize)
open VerifiableInference.Desc.Key (keyInstanceOfOutOfDomainSample)
open ProofFile.Honest (Prover KeyAndJoiningRoundMessages ProverCoinCounts Sides Fall Thread Local Common Sits Owes Yes Accepted fallsBy Tied
  DataFits halvedAll sealPlain drawsAt)
open OnBytes.Prover (AccLaw)
open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms

section Ends
variable {W₀ Rc X₀ X' Wk : Type} (X : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
  (P : VerifiableInference.Desc.Key.LaterPlaces) (K : KeyParts W₀ Rc X₀ X' Wk) (hK : K.AtAll)
include hK

/-- No half of `keyProver K` stands at the first chain's end. -/
theorem no_half_seal₁ :
    ((keyProver K).first.find? fun g => g.place == (keyFileDescription X N P).first.last.place) = none :=
  find_none_of_places _ _ (by
    rw [first_places K hK.first]
    rfl)

/-- Nor at the shared chain's. -/
theorem no_half_seal₂ :
    ((keyProver K).shared.find? fun g => g.place == (keyFileDescription X N P).shared.last.place) = none :=
  find_none_of_places _ _ (by
    rw [keyProver_shared K hK.splits, hK.onU, hK.onOmega]
    rfl)

end Ends

variable {Xq : Type} {A : (frS.toDecR frZ 402653181).Claims Xq} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → View → View → View → Bool}
  {runP : Xq × RecFull → View → View → View → Bool} {ds : List TypedOracleCompiler.Run.PQ.RD}
  {xs : List XO} {dec : RecFull × RecFull → View → Bool} {rK rP : RecFull} {depthReq : ℕ}
  {early : Xq → Xq} {salt K' : ℕ}
  {Q : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers}
  (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K' Q)
  (X : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
  (P : VerifiableInference.Desc.Key.LaterPlaces) (q : KeyNums) {Ky Tr X₀ X' R₂ R₃ : Type} (B : ProverCoinCounts)
  [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]

/-- **`accLaw_key_laid`, with a letter Hp for the rows' prover.** -/
theorem accLaw_key_at
    (G : Sides (keyFileDescription X N P) B (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
      ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) Ky Tr X₀ X')
    (H Hp : Prover (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
      ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) KeyInst Ky Tr X₀ X')
    (e : G.prover H = Hp)
    (J : R₂ → R₃ → KeyAndJoiningRoundMessages (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
      ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd)
      (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Seed KeyInst Ky (OnBytes.Maker.FrontMsg (List OnBytes.E))
      (Compile.Joined.JoinMsg (List OnBytes.E) ByteArray) ByteArray)
    (sh : Ky → (keyFileDescription X N P).S₂)
    (ext : (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I ×
      ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) ×
      (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Seed →
      (Iop.oneExternalString (2 ^ (DK.at frS.P.T.a).a) _root_.Run.PQ.SgX).Str)
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
      Tied (DK.at frS.P.T.a) (keyFileDescription X N P) Hp J ext pubJ sh Rel w (keyInstanceOfOutOfDomainSample a) →
      silK a ((J r2 r3).front w.1 w.2.1 w.2.2 (keyInstanceOfOutOfDomainSample a)) ((J r2 default).join w.1 w.2.1 w.2.2)
        ((J r2 r3).seam w.1 w.2.1 w.2.2 (keyInstanceOfOutOfDomainSample a)) = true)
    (h4 : halvedAll (keyFileDescription X N P) Hp = true) (hS : Sits (keyFileDescription X N P) Hp U₁ U₂ U₃)
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
      Tied (DK.at frS.P.T.a) (keyFileDescription X N P) Hp J ext pubJ sh Rel w x →
      AtRunLeft (keyFileDescription X N P) Hp (withForm U₁ (Form₁ X N P q)) (withForm U₂ (Form₂ X N P q))
        (withForm U₃ (Form₃ X N P q)) w x c) :
    ∀ w (a : RecFull) (c : CoinOne B R₂ R₃),
      Tied (DK.at frS.P.T.a) (keyFileDescription X N P) Hp J ext pubJ sh Rel w (keyInstanceOfOutOfDomainSample a) →
      AccLaw (batTC (innerCompilerInputAtFullSize T).protocol (innerCompilerInputAtFullSize T).offlineRoundSplits) (wTC (innerCompilerInputAtFullSize T).queryLayout) a
        ((keyHonestAny A (relationsAndEncodingOfClaims A E) DK DP (keyFileDescription X N P) runP ds xs dec rK rP depthReq early salt
          B Hp J sh ext runK Q).ext w)
        ((keyHonestAny A (relationsAndEncodingOfClaims A E) DK DP (keyFileDescription X N P) runP ds xs dec rK rP depthReq early salt
          B Hp J sh ext runK Q).strat w a c)
        ((keyHonestAny A (relationsAndEncodingOfClaims A E) DK DP (keyFileDescription X N P) runP ds xs dec rK rP depthReq early salt
          B Hp J sh ext runK Q).withheld w a ∪
          fallOne (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty
            (keyFileDescription X N P) B G H w (keyInstanceOfOutOfDomainSample a) c) := by
  subst e
  exact accLaw_key_laid T X N P q B G H J sh ext hs scope hFull hCar hD hq hdue hrun hsil h4 hS hn₁
    hn₂ o₁ o₂ o₃ y₁ y₂ y₃ hat

/-- **THE ACCEPT LAW WITH `keyProver K` LAID IN: WHAT IS LEFT.** -/
theorem accLaw_keyProver {Wk : Type}
    (K : KeyParts (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
      ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) X₀ X' Wk) (hK : K.AtAll)
    (f₁ : List (Fall (keyFileDescription X N P).S₁)) (f₂ : List (Fall (keyFileDescription X N P).S₂))
    (f₃ : List (Fall (keyFileDescription X N P).S₃))
    (J : R₂ → R₃ → KeyAndJoiningRoundMessages (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
      ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd)
      (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Seed KeyInst OnBytes.TableKey
      (OnBytes.Maker.FrontMsg (List OnBytes.E))
      (Compile.Joined.JoinMsg (List OnBytes.E) ByteArray) ByteArray)
    (sh : OnBytes.TableKey → (keyFileDescription X N P).S₂)
    (ext : (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I ×
      ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) ×
      (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Seed →
      (Iop.oneExternalString (2 ^ (DK.at frS.P.T.a).a) _root_.Run.PQ.SgX).Str)
    {pubJ : R₂ → R₃ → KeyInst → OnBytes.Maker.FrontMsg (List OnBytes.E) ×
      Compile.Joined.JoinMsg (List OnBytes.E) ByteArray × ByteArray}
    {Rel : (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I →
      (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd → KeyInst → Prop}
    (V₁ : Thread B (keyFileDescription X N P).S₁ (keyFileDescription X N P).Cl
      (Local (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
        ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) KeyInst Unit)
      (Local (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
        ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) KeyInst Unit) X' KeyInst)
    (V₂ : Thread B (keyFileDescription X N P).S₂ (keyFileDescription X N P).Cl Empty
      (Common (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
        ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) OnBytes.TableKey) X₀
      OnBytes.TableKey)
    (V₃ : Thread B (keyFileDescription X N P).S₃ (keyFileDescription X N P).Cl
      (Local (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
        ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) KeyInst Unit)
      (Local (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
        ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) KeyInst Unit) X' KeyInst)
    {Z : VerifierAndGoals.PublicFiles} (hs : KeySourced Z X N P) (scope : VerifierAndGoals.InScope Z = true)
    (hFull : LPFFrame.FullAt (ckP .two) (DK.at frS.P.T.a)) (hCar : ∀ w, LPFFrame.Carries (ext w))
    (hD : DataFits (keyFileDescription X N P) (DK.at frS.P.T.a)) (hq : sealPlain (keyFileDescription X N P) = true)
    (hdue : ∀ ρ, (drawsAt (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty
      ρ).due (keyFileDescription X N P) = true)
    (hrun : ∀ a v₁ v₂ v₃, (keyFileDescription X N P).run (keyInstanceOfOutOfDomainSample a) v₁ v₂ v₃ = true → runK a v₁ v₂ v₃ = true)
    (hsil : ∀ r2 r3 w a,
      Tied (DK.at frS.P.T.a) (keyFileDescription X N P) (keyProver K) J ext pubJ sh Rel w (keyInstanceOfOutOfDomainSample a) →
      silK a ((J r2 r3).front w.1 w.2.1 w.2.2 (keyInstanceOfOutOfDomainSample a)) ((J r2 default).join w.1 w.2.1 w.2.2)
        ((J r2 r3).seam w.1 w.2.1 w.2.2 (keyInstanceOfOutOfDomainSample a)) = true)
    (t₁ : (seat₁ (keyFileDescription X N P) (keyProver K) V₁).fits (keyFileDescription X N P).first.blocksInOrder.length = true)
    (t₂ : (seat₂ (keyFileDescription X N P) (keyProver K) V₂).fits (keyFileDescription X N P).shared.blocksInOrder.length = true)
    (t₃ : (seat₃ (keyFileDescription X N P) (keyProver K) V₃).fits (keyFileDescription X N P).second.blocksInOrder.length = true)
    (o₁ : Owes (withForm (seat₁ (keyFileDescription X N P) (keyProver K) V₁) (Form₁ X N P q)))
    (o₂ : Owes (withForm (seat₂ (keyFileDescription X N P) (keyProver K) V₂) (Form₂ X N P q)))
    (o₃ : Owes (withForm (seat₃ (keyFileDescription X N P) (keyProver K) V₃) (Form₃ X N P q)))
    (y₁ : ∀ b, b + 1 < (keyFileDescription X N P).first.blocksInOrder.length →
      Accepted (withForm (seat₁ (keyFileDescription X N P) (keyProver K) V₁) (Form₁ X N P q))
        (fallsBy f₁ (keyFileDescription X N P).first.blocksInOrder) b)
    (y₂ : ∀ b, b + 1 < (keyFileDescription X N P).shared.blocksInOrder.length →
      Accepted (withForm (seat₂ (keyFileDescription X N P) (keyProver K) V₂) (Form₂ X N P q))
        (fallsBy f₂ (keyFileDescription X N P).shared.blocksInOrder) b)
    (y₃ : Accepted (withForm (seat₃ (keyFileDescription X N P) (keyProver K) V₃) (Form₃ X N P q))
      (fallsBy f₃ (keyFileDescription X N P).second.blocksInOrder) 2)
    (hat : ∀ w x (c : CoinOne B R₂ R₃),
      Tied (DK.at frS.P.T.a) (keyFileDescription X N P) (keyProver K) J ext pubJ sh Rel w x →
      AtRunLeft (keyFileDescription X N P) (keyProver K)
        (withForm (seat₁ (keyFileDescription X N P) (keyProver K) V₁) (Form₁ X N P q))
        (withForm (seat₂ (keyFileDescription X N P) (keyProver K) V₂) (Form₂ X N P q))
        (withForm (seat₃ (keyFileDescription X N P) (keyProver K) V₃) (Form₃ X N P q)) w x c) :
    ∀ w (a : RecFull) (c : CoinOne B R₂ R₃),
      Tied (DK.at frS.P.T.a) (keyFileDescription X N P) (keyProver K) J ext pubJ sh Rel w (keyInstanceOfOutOfDomainSample a) →
      AccLaw (batTC (innerCompilerInputAtFullSize T).protocol (innerCompilerInputAtFullSize T).offlineRoundSplits) (wTC (innerCompilerInputAtFullSize T).queryLayout) a
        ((keyHonestAny A (relationsAndEncodingOfClaims A E) DK DP (keyFileDescription X N P) runP ds xs dec rK rP depthReq early salt
          B (keyProver K) J sh ext runK Q).ext w)
        ((keyHonestAny A (relationsAndEncodingOfClaims A E) DK DP (keyFileDescription X N P) runP ds xs dec rK rP depthReq early salt
          B (keyProver K) J sh ext runK Q).strat w a c)
        ((keyHonestAny A (relationsAndEncodingOfClaims A E) DK DP (keyFileDescription X N P) runP ds xs dec rK rP depthReq early salt
          B (keyProver K) J sh ext runK Q).withheld w a ∪
          fallOne (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty
            (keyFileDescription X N P) B (bareSides (keyFileDescription X N P) B (keyProver K) f₁ f₂ f₃) (keyProver K) w
            (keyInstanceOfOutOfDomainSample a) c) :=
  accLaw_key_at T X N P q B (bareSides (keyFileDescription X N P) B (keyProver K) f₁ f₂ f₃) (keyProver K)
    (keyProver K) (bareSides_prover _ _ _ _ _ _) J sh ext hs scope hFull hCar hD hq hdue hrun hsil
    (halvedAll_key scope hs.named K hK) (sits_seated _ _ V₁ V₂ V₃ t₁ t₂ t₃)
    (no_half_seal₁ X N P K hK) (no_half_seal₂ X N P K hK) o₁ o₂ o₃ y₁ y₂ y₃ hat

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.KeyLink.find_none_of_places
#print axioms AtPublicFiles.AtFiles.no_half_seal₁
#print axioms AtPublicFiles.AtFiles.no_half_seal₂
#print axioms AtPublicFiles.AtFiles.accLaw_key_at
#print axioms AtPublicFiles.AtFiles.accLaw_keyProver
