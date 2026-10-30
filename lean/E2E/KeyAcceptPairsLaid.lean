-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyAcceptPairsLaid.lean: the accept law of the key file's honest prover, from the debts asked of the pairs
of a thread and a letter, with the prover of parts `keyProver K` laid in. By calls. It is a conditional.

Why. `accLaw_keyProver` (E2E/KeyAcceptProver.lean) asks `Owes` and `Accepted` of the threads alone. A thread
does not read the field `opened`, and a proximity test's half behind the guard errs where that field is none, so
those premises are asked at stands at which such a half does not play. `accLaw_key_of_families` (E2E/KeyAcceptFamilies.lean) asks the debts of the pairs,
and the thread and the letter may hang on the private input and the instance. This file lays `keyProver K` in it.

Main names.
  `accLaw_families_at`: `accLaw_key_of_families` with a letter for the rows' prover.
  `accLaw_keyProver_pairs`: the accept law at `keyHonestAny … (keyProver K) …`, outside its abort set and the
    set at which a fall of three given lists speaks.

What is paid here: the description's test on the plan (`KeyNamed.plan`); a half at every sub-protocol that sends
(`halvedAll_key`, under `K.AtAll`).

What stays open, as premises. On the files: `hFull`, `hCar`, `hD`, `hq`, `hdue`, `hrun`, `hsil`: for each the
name that pays it is at the head of E2E/KeyAcceptAtFiles.lean, where `hdue` hangs on the closed test `nzWritten`.
On the threads, `hM`: at tied inputs that pass the first test: that they sit; `OwesS`, `SaidNext` at every border
and `YesS`, of each of the three. At one run, `hat`: `AtRunS`. No thread and no letter is laid here, and no field
of `K` but its places is read.

Where `hM` or `hat` can't be met the law says nothing. Nothing here shows that they can be met.

The lists of falls are letters. `Tied` ties the private input to the instance at every coin, so each premise under
it stands at every value of the coins; no law over coins is stated here, and this is none: `AccLaw` speaks of one
input and one coin.

Nothing on soundness, completeness, hiding or binding.

-/
import E2E.KeyAcceptFamilies
import E2E.KeyLaid
import E2E.KeyPublic

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Cut AtPublicFiles.KeyLink AtPublicFiles.KeyFile
open OnBytes.Flat (Files relationsAndEncodingOfClaims RecFull Coding silK front₀ join₀)
open OnBytes.Slice (frS frZ DecR)
open _root_.Run.PQ (View XO)
open OnBytes.Maker (WholeD)
open _root_.Run (ckP)
open VerifiableInference.OnPublicFiles (threeProtocolsAtFullSize InnerCompilerInputAndAnalysisFieldsAtFullSize innerCompilerInputAtFullSize)
open VerifiableInference.Desc (FileDescription)
open VerifiableInference.Desc.Key (keyInstanceOfOutOfDomainSample)
open ProofFile.Honest (Prover KeyAndJoiningRoundMessages ProverCoinCounts Sides Fall Thread Local Common Coins Mid Tied DataFits halvedAll
  sealPlain drawsAt)
open OnBytes.Prover (AccLaw)
open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms

variable {Xq : Type} {A : (frS.toDecR frZ 402653181).Claims Xq} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → View → View → View → Bool}
  {runP : Xq × RecFull → View → View → View → Bool} {ds : List TypedOracleCompiler.Run.PQ.RD}
  {xs : List XO} {dec : RecFull × RecFull → View → Bool} {rK rP : RecFull} {depthReq : ℕ}
  {early : Xq → Xq} {salt K' : ℕ}
  {Q : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers}
  (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K' Q)
  {Ky Tr X₀ X' R₂ R₃ : Type} (B : ProverCoinCounts) [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]

/-- **`accLaw_key_of_families`, with a letter Hp for the rows' prover.** -/
theorem accLaw_families_at (Fx : FileDescription KeyInst)
    (G : Sides Fx B (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
      ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) Ky Tr X₀ X')
    (H Hp : Prover (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
      ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) KeyInst Ky Tr X₀ X')
    (e : G.prover H = Hp)
    (J : R₂ → R₃ → KeyAndJoiningRoundMessages (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
      ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd)
      (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Seed KeyInst Ky (OnBytes.Maker.FrontMsg (List OnBytes.E))
      (Compile.Joined.JoinMsg (List OnBytes.E) ByteArray) ByteArray)
    (sh : Ky → Fx.S₂)
    (ext : (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I ×
      ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) ×
      (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Seed →
      (Iop.oneExternalString (2 ^ (DK.at frS.P.T.a).a) _root_.Run.PQ.SgX).Str)
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
      Tied (DK.at frS.P.T.a) Fx Hp J ext pubJ sh Rel w (keyInstanceOfOutOfDomainSample a) →
      silK a ((J r2 r3).front w.1 w.2.1 w.2.2 (keyInstanceOfOutOfDomainSample a)) ((J r2 default).join w.1 w.2.1 w.2.2)
        ((J r2 r3).seam w.1 w.2.1 w.2.2 (keyInstanceOfOutOfDomainSample a)) = true)
    (h4 : halvedAll Fx Hp = true)
    (hM : ∀ w x, Tied (DK.at frS.P.T.a) Fx Hp J ext pubJ sh Rel w x → Fx.okStart x = true →
      MembersS Fx G H (U₁ w x) (U₂ w x) (U₃ w x) (S₁ w x) (S₂ w x) (S₃ w x))
    (hat : ∀ w x (c : CoinOne B R₂ R₃),
      Tied (DK.at frS.P.T.a) Fx Hp J ext pubJ sh Rel w x →
      AtRunS Fx Hp (U₁ w x) (U₂ w x) (U₃ w x) (S₁ w x) (S₂ w x) (S₃ w x) w x c) :
    ∀ w (a : RecFull) (c : CoinOne B R₂ R₃),
      Tied (DK.at frS.P.T.a) Fx Hp J ext pubJ sh Rel w (keyInstanceOfOutOfDomainSample a) →
      AccLaw (batTC (innerCompilerInputAtFullSize T).protocol (innerCompilerInputAtFullSize T).offlineRoundSplits) (wTC (innerCompilerInputAtFullSize T).queryLayout) a
        ((keyHonestAny A (relationsAndEncodingOfClaims A E) DK DP Fx runP ds xs dec rK rP depthReq early salt B Hp J sh ext
          runK Q).ext w)
        ((keyHonestAny A (relationsAndEncodingOfClaims A E) DK DP Fx runP ds xs dec rK rP depthReq early salt B Hp J sh ext
          runK Q).strat w a c)
        ((keyHonestAny A (relationsAndEncodingOfClaims A E) DK DP Fx runP ds xs dec rK rP depthReq early salt B Hp J sh ext
          runK Q).withheld w a ∪
          fallOne (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty Fx B G H w
            (keyInstanceOfOutOfDomainSample a) c) := by
  subst e
  exact accLaw_key_of_families T Fx B G H J sh ext hFull hCar hD hp hq hdue hrun hsil h4 hM hat

variable (X : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
  (P : VerifiableInference.Desc.Key.LaterPlaces)

/-- **The accept law from the pairs, with `keyProver K` laid in: what is left.** -/
theorem accLaw_keyProver_pairs {Wk : Type}
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
    {U₁ : ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I ×
      ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) ×
      (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Seed) → KeyInst →
      Thread B (keyFileDescription X N P).S₁ (keyFileDescription X N P).Cl
      (Local (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
        ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) KeyInst Unit)
      (Local (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
        ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) KeyInst Unit) X' KeyInst}
    {U₂ : ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I ×
      ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) ×
      (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Seed) → KeyInst →
      Thread B (keyFileDescription X N P).S₂ (keyFileDescription X N P).Cl Empty
      (Common (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
        ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) OnBytes.TableKey) X₀
      OnBytes.TableKey}
    {U₃ : ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I ×
      ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) ×
      (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Seed) → KeyInst →
      Thread B (keyFileDescription X N P).S₃ (keyFileDescription X N P).Cl
      (Local (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
        ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) KeyInst Unit)
      (Local (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
        ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) KeyInst Unit) X' KeyInst}
    {S₁ : ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I ×
      ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) ×
      (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Seed) → KeyInst →
      Nat → Coins B → Mid (Local (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
      ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) KeyInst Unit) X' → Prop}
    {S₂ : ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I ×
      ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) ×
      (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Seed) → KeyInst →
      Nat → Coins B → Mid (Common (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
      ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) OnBytes.TableKey) X₀ → Prop}
    {S₃ : ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I ×
      ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) ×
      (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Seed) → KeyInst →
      Nat → Coins B → Mid (Local (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
      ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) KeyInst Unit) X' → Prop}
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
    (hM : ∀ w x, Tied (DK.at frS.P.T.a) (keyFileDescription X N P) (keyProver K) J ext pubJ sh Rel w x →
      (keyFileDescription X N P).okStart x = true →
      MembersS (keyFileDescription X N P) (bareSides (keyFileDescription X N P) B (keyProver K) f₁ f₂ f₃) (keyProver K)
        (U₁ w x) (U₂ w x) (U₃ w x) (S₁ w x) (S₂ w x) (S₃ w x))
    (hat : ∀ w x (c : CoinOne B R₂ R₃),
      Tied (DK.at frS.P.T.a) (keyFileDescription X N P) (keyProver K) J ext pubJ sh Rel w x →
      AtRunS (keyFileDescription X N P) (keyProver K) (U₁ w x) (U₂ w x) (U₃ w x) (S₁ w x) (S₂ w x) (S₃ w x) w x
        c) :
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
  accLaw_families_at T B (keyFileDescription X N P) (bareSides (keyFileDescription X N P) B (keyProver K) f₁ f₂ f₃)
    (keyProver K) (keyProver K) (bareSides_prover _ _ _ _ _ _) J sh ext hFull hCar hD hs.named.plan hq
    hdue hrun hsil (halvedAll_key scope hs.named K hK) hM hat

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.accLaw_families_at
#print axioms AtPublicFiles.AtFiles.accLaw_keyProver_pairs
