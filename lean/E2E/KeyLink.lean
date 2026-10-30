--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyLink.lean: THE ACCEPT LAW OF THE KEY FILE's HONEST PROVER (`OnBytes.Prover.AccLaw`, the
clause
`accT` of `OnBytes.Prover.HonFit`), at the honest side made of `ProofFile.Honest.honestBatchProverOfFile` over the key
file's description, carried back along the map that writes the key (E2E/KeyHonest.lean), at the
compiled verifier's own protocol and wiring: FROM SENTENCES ON THE HONEST SIDE's OWN RUN. By calls.
NOTHING IS CLAIMED OF ANY PROVER.

Two theorems of other folders are called, as in E2E/BridgeLink.lean for one request's prover. Here
there is no request and no copy's number.
  `ProofFile.Honest.yes_at_stratC` (Johnson/Desc/ProofFile/Honest/Law/ThreadStratC.lean) ends at: the
    description's decision accepts the three views of the transcript that the honest strategy
    writes, at verifier randomness outside the abort set at which no fall speaks; and the three
    rounds without a challenge hold the seam's three values.
  `LPFFrame.frame_at_slotK` (Johnson/LPFFrame/Proofs.lean) takes: at all verifier randomness that
    passes the wire's tests, outside a set: the test on these three rounds and the key file's
    decision accept at the strategy's run; and gives `AccLaw` outside that set. It pays the nonces
    and the test bits; the reads under two premises, `FullAt` and `Carries`, which stay premises.

What is shown.
  `CoinOne`, `fallOne`: the honest side's coin; the set of verifier randomness at which a fall
    speaks along the honest run, at a private input, an instance and a coin.
  `no_fall_one`: outside that set no fall speaks at the views of the run.
  `YesOne …`: A HYPOTHESIS BY NAME, in the letters of the first theorem's end.
  `DebtsOne …`: what the first theorem asks beyond "tied", at one input and coin: a statement of
    premises.
  **`yesOne_of_debts`**: `YesOne` from `DebtsOne` at every tied input and coin, with `Tied`
    (Johnson/Desc/ProofFile/Honest/Law/Rule/Tied.lean) paying the two keys, the shared chain's first
    state and the table.
  **`accLaw_key_of_yes`**: the accept law at the compiled verifier's key file's protocol and wiring,
    at any letters of the full size, from `YesOne` and: `FullAt`; `Carries`; where the description's
    decision accepts at the written key, so does the object's decision on the key file; the test on
    the three rounds accepts the seam's three values.
  `accLaw_keyHonestAny`: the same, spelled at the fields of `keyHonestAny`: external string,
    strategy, abort set.

Limits.
- CONDITIONAL. `DebtsOne` is shown of no prover of parts: it holds the invariants of all members.
  "Tied" is a free letter in `accLaw_key_of_yes`: at a relation that nothing meets the theorem is
  idle.
- `YesOne` is asked at all verifier randomness outside the set, whether it passes the wire's tests
  or not: more than the theorem on the key file's letters spends.
- `DebtsOne` is asked at EVERY coin of a tied input: every purse and both run values.
- Pointwise in the verifier randomness: no measure.
- THE LISTS OF FALLS ARE FREE LETTERS (fields of the rows G). A fall that always speaks makes the
  law idle. At a member without a round, a fall whose test is "this member's own step rejects" makes
  "no fall speaks along the run" hold a part of the conclusion. So the law says something at a
  member only beside EACH FALL's TEXT AND ITS MEASURED SHARE, at each fixed coin: without the number
  it says nothing there.
- THE FALL's SET HANGS ON THE PROVER's COIN. A bound on its measure at each fixed coin bounds the
  share over verifier randomness and coins together; it does not bound the set of verifier
  randomness at which SOME coin's run falls. So a statement of completeness takes the number as an
  error over verifier randomness and coins together; the fall is a second set, which reads the coin,
  beside the abort set, and is not folded into it: the form of `OnBytes.Prover.HonFit` (its accept
  laws outside the abort set and the fall at that coin; its measures at each fixed coin).
- No OOD seed is set aside here: the fall's set is the true one, not the guarded one of
  E2E/KeyBridge.lean.
- `DebtsOne` has the text of `DebtsAt` (E2E/BridgeLink.lean): two names for one statement of
  premises.
- Nothing at public files: the letters are any letters of the full size.

-/
import E2E.KeyHonest
import Johnson.LPFFrame.Proofs
import Johnson.Desc.ProofFile.Honest.Law.ThreadStratC
import Johnson.Desc.ProofFile.Honest.Law.Rule.Tied

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.KeyLink
open Iop Prob
open OnBytes.Maker (WholeD chainsOf view₁ view₂ view₃)
open _root_.Run.PQ (CK SgX)
open ProofFile.Honest (honestBatchProverOfFile Prover KeyAndJoiningRoundMessages ProverCoinCounts Purse Sides fallAt drawsAt runC viewsFall ready
  PlanServes ThreadsC Tied DataFits halvedAll sealPlain yes_at_stratC)

/-- The honest side's coin: the shared chain's purse and the second chain's run value; the two other
purses and the third chain's run value. -/
abbrev CoinOne (B : ProverCoinCounts) (R₂ R₃ : Type) : Type :=
  (Purse B.shared × R₂) × ((Purse B.first × Purse B.second) × R₃)

section One
variable {Xi W₀ Rc Ky Tr X₀ X Sd TF TJ T3 R₂ R₃ : Type} (C : CK) (D : WholeD) (tF : TF) (tJ : TJ)
  (t3 : T3) (F : VerifiableInference.Desc.FileDescription Xi) (silent : Xi → TF → TJ → T3 → Bool)
  (B : ProverCoinCounts) (G : Sides F B W₀ Rc Ky Tr X₀ X) (H : Prover W₀ Rc Xi Ky Tr X₀ X) [Fintype R₂]
  [Nonempty R₂] [Fintype R₃] [Inhabited R₃] (J : R₂ → R₃ → KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky TF TJ T3)
  (sh : Ky → F.S₂) (ext : W₀ × Rc × Sd → (Iop.oneExternalString (2 ^ D.a) SgX).Str)

/-- **The fall's set at the prover's coin.** -/
def fallOne (w : W₀ × Rc × Sd) (x : Xi) (c : CoinOne B R₂ R₃) :
    Set (Rho (chainsOf C D tF tJ t3).sh) :=
  {ρ | (fallAt G H w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ (drawsAt C D tF tJ t3 ρ)).isSome = true}

omit [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃] in
/-- Outside the fall's set no fall speaks at the views of the run. -/
theorem no_fall_one (w : W₀ × Rc × Sd) (x : Xi) (c : CoinOne B R₂ R₃)
    (ρ : Rho (chainsOf C D tF tJ t3).sh) (h : ρ ∉ fallOne C D tF tJ t3 F B G H w x c) :
    ∀ r, runC F B (G.prover H) w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ (drawsAt C D tF tJ t3 ρ) =
      .ok r → viewsFall F G.falls₁ G.falls₂ G.falls₃ x r.run.views = none := by
  intro r hr
  have h' : ¬ (fallAt G H w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩
      (drawsAt C D tF tJ t3 ρ)).isSome = true := h
  unfold ProofFile.Honest.fallAt at h'
  rw [hr] at h'
  exact Option.not_isSome_iff_eq_none.1 h'

/-- **Hypothesis by name**: at tied inputs, at every coin, outside abort set and fall: the
description's decision accepts the three views of the honest run, and the three rounds without a
challenge hold the seam's three values. -/
def YesOne (TiedX : W₀ × Rc × Sd → Xi → Prop) : Prop :=
  ∀ w x (c : CoinOne B R₂ R₃), TiedX w x →
    ∀ ρ, ρ ∉ (honestBatchProverOfFile C D tF tJ t3 F silent B (G.prover H) J sh ext).one.withheld w x ∪
        fallOne C D tF tJ t3 F B G H w x c →
      F.run x
        (view₁ C D tF tJ t3 (ext w)
          (((honestBatchProverOfFile C D tF tJ t3 F silent B (G.prover H) J sh ext).one.strat w x c).run ρ).1)
        (view₂ C D tF tJ t3 (ext w)
          (((honestBatchProverOfFile C D tF tJ t3 F silent B (G.prover H) J sh ext).one.strat w x c).run ρ).1)
        (view₃ C D tF tJ t3 (ext w)
          (((honestBatchProverOfFile C D tF tJ t3 F silent B (G.prover H) J sh ext).one.strat w x c).run ρ).1) =
        true ∧
      ((chainsOf C D tF tJ t3).msgF
        (((honestBatchProverOfFile C D tF tJ t3 F silent B (G.prover H) J sh ext).one.strat w x c).run ρ).1).2 =
        (J c.1.2 c.2.2).front w.1 w.2.1 w.2.2 x ∧
      ((chainsOf C D tF tJ t3).msgJ
        (((honestBatchProverOfFile C D tF tJ t3 F silent B (G.prover H) J sh ext).one.strat w x c).run ρ).1).2 =
        (J c.1.2 default).join w.1 w.2.1 w.2.2 ∧
      ((chainsOf C D tF tJ t3).msg3
        (((honestBatchProverOfFile C D tF tJ t3 F silent B (G.prover H) J sh ext).one.strat w x c).run ρ).1).2 =
        (J c.1.2 c.2.2).seam w.1 w.2.1 w.2.2 x

/-- **What the theorem on the honest run asks beyond "tied"**, at one input and one coin: the
instance's first test accepts; the run can be made ready; the plan serves; the invariants of all
members, with the rows' own lists of falls. A statement of premises: it is claimed of nothing. -/
def DebtsOne (w : W₀ × Rc × Sd) (x : Xi) (c : CoinOne B R₂ R₃) : Prop :=
  F.okStart x = true ∧
    ∃ R, ready F B (G.prover H) w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ = .ok R ∧
      PlanServes (G.prover H) w.1 w.2.1 R ∧
      ∃ Thr : ThreadsC F B (G.prover H) w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ R,
        Thr.f₁ = G.falls₁ ∧ Thr.f₂ = G.falls₂ ∧ Thr.f₃ = G.falls₃

/-- **`YesOne` from the debts**, "tied" paying the two keys, the shared chain's first state and the
table. -/
theorem yesOne_of_debts (hp : F.planOk = true) (hq : sealPlain F = true) (hD : DataFits F D)
    (h4 : halvedAll F (G.prover H) = true) (hdue : ∀ ρ, (drawsAt C D tF tJ t3 ρ).due F = true)
    {pubJ : R₂ → R₃ → Xi → TF × TJ × T3} {Rel : W₀ → Rc → Xi → Prop}
    (hdebt : ∀ w x (c : CoinOne B R₂ R₃), Tied D F (G.prover H) J ext pubJ sh Rel w x →
      DebtsOne F B G H w x c) :
    YesOne C D tF tJ t3 F silent B G H J sh ext
      (fun w x => Tied D F (G.prover H) J ext pubJ sh Rel w x) := by
  intro w x c ht ρ hρ
  obtain ⟨h0, R, hR, hP, Thr, e1, e2, e3⟩ := hdebt w x c ht
  have hf := no_fall_one C D tF tJ t3 F B G H w x c ρ (fun a => hρ (Or.inr a))
  exact yes_at_stratC C D tF tJ t3 F silent B (G.prover H) J sh ext w x c (ext w) ρ hR hp hq hD h4
    h0 hP ht.key ht.start.symm ht.table (hdue ρ) (fun a => hρ (Or.inl a)) Thr
    (by rw [e1, e2, e3]; exact hf)

end One

end AtPublicFiles.KeyLink

/-! ## At the letters of the compiled verifier -/

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
open ProofFile.Honest (Prover KeyAndJoiningRoundMessages ProverCoinCounts Sides)
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

/-- **THE ACCEPT LAW OF THE KEY FILE's PROVER, at the compiled verifier's own protocol and wiring**,
from `YesOne`. -/
theorem accLaw_key_of_yes
    {TiedX : (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I ×
      ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) ×
      (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Seed → KeyInst → Prop}
    (hFull : LPFFrame.FullAt (ckP .two) (DK.at frS.P.T.a)) (hCar : ∀ w, LPFFrame.Carries (ext w))
    (hrun : ∀ a v₁ v₂ v₃, Fx.run (keyInstanceOfOutOfDomainSample a) v₁ v₂ v₃ = true → runK a v₁ v₂ v₃ = true)
    (hsil : ∀ r2 r3 w a, TiedX w (keyInstanceOfOutOfDomainSample a) →
      silK a ((J r2 r3).front w.1 w.2.1 w.2.2 (keyInstanceOfOutOfDomainSample a)) ((J r2 default).join w.1 w.2.1 w.2.2)
        ((J r2 r3).seam w.1 w.2.1 w.2.2 (keyInstanceOfOutOfDomainSample a)) = true)
    (hyes : YesOne (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty Fx silKey B G
      H J sh ext TiedX) :
    ∀ w (a : RecFull) (c : CoinOne B R₂ R₃), TiedX w (keyInstanceOfOutOfDomainSample a) →
      AccLaw (batTC (innerCompilerInputAtFullSize T).protocol (innerCompilerInputAtFullSize T).offlineRoundSplits) (wTC (innerCompilerInputAtFullSize T).queryLayout) a
        (ext w)
        ((offlineBatchProver A (relationsAndEncodingOfClaims A E) DK Fx rK B (G.prover H) J sh ext).one.strat w (keyInstanceOfOutOfDomainSample a) c)
        ((offlineBatchProver A (relationsAndEncodingOfClaims A E) DK Fx rK B (G.prover H) J sh ext).one.withheld w (keyInstanceOfOutOfDomainSample a) ∪
          fallOne (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty Fx B G H w
            (keyInstanceOfOutOfDomainSample a) c) := by
  intro w a c ht
  refine LPFFrame.frame_at_slotK T hFull a (ext w) (hCar w) _ _ (fun ρ _ hρ => ?_)
  obtain ⟨hy, m1, m2, m3⟩ := hyes w (keyInstanceOfOutOfDomainSample a) c ht ρ hρ
  exact ⟨(congr (congr (congrArg (silK a) m1) m2) m3).trans (hsil c.1.2 c.2.2 w a ht),
    hrun a _ _ _ hy⟩

/-- **The same, spelled at the fields of `keyHonestAny`**: its external string, its strategy and its
abort set are these, by unfolding. -/
theorem accLaw_keyHonestAny
    {TiedX : (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I ×
      ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) ×
      (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Seed → KeyInst → Prop}
    (hFull : LPFFrame.FullAt (ckP .two) (DK.at frS.P.T.a)) (hCar : ∀ w, LPFFrame.Carries (ext w))
    (hrun : ∀ a v₁ v₂ v₃, Fx.run (keyInstanceOfOutOfDomainSample a) v₁ v₂ v₃ = true → runK a v₁ v₂ v₃ = true)
    (hsil : ∀ r2 r3 w a, TiedX w (keyInstanceOfOutOfDomainSample a) →
      silK a ((J r2 r3).front w.1 w.2.1 w.2.2 (keyInstanceOfOutOfDomainSample a)) ((J r2 default).join w.1 w.2.1 w.2.2)
        ((J r2 r3).seam w.1 w.2.1 w.2.2 (keyInstanceOfOutOfDomainSample a)) = true)
    (hyes : YesOne (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty Fx silKey B G
      H J sh ext TiedX) :
    ∀ w (a : RecFull) (c : CoinOne B R₂ R₃), TiedX w (keyInstanceOfOutOfDomainSample a) →
      AccLaw (batTC (innerCompilerInputAtFullSize T).protocol (innerCompilerInputAtFullSize T).offlineRoundSplits) (wTC (innerCompilerInputAtFullSize T).queryLayout) a
        ((keyHonestAny A (relationsAndEncodingOfClaims A E) DK DP Fx runP ds xs dec rK rP depthReq early salt B
          (G.prover H) J sh ext runK P).ext w)
        ((keyHonestAny A (relationsAndEncodingOfClaims A E) DK DP Fx runP ds xs dec rK rP depthReq early salt B
          (G.prover H) J sh ext runK P).strat w a c)
        ((keyHonestAny A (relationsAndEncodingOfClaims A E) DK DP Fx runP ds xs dec rK rP depthReq early salt B
          (G.prover H) J sh ext runK P).withheld w a ∪
          fallOne (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty Fx B G H w
            (keyInstanceOfOutOfDomainSample a) c) :=
  accLaw_key_of_yes T Fx B G H J sh ext hFull hCar hrun hsil hyes

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.KeyLink.no_fall_one
#print axioms AtPublicFiles.KeyLink.yesOne_of_debts
#print axioms AtPublicFiles.AtFiles.accLaw_key_of_yes
#print axioms AtPublicFiles.AtFiles.accLaw_keyHonestAny
