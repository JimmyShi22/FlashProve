-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/Honest/StratLawAtTerm.lean: `StratLaw` (Johnson/Prover/Print/StratLaw.lean), the law that
the printer asks of a strategy's own run, at the provers of E2E/TheHonestProver.lean.

`StratLaw` holds of every strategy of the frame, with no hypothesis (`meets_stratLawC`,
Johnson/Desc/ProofFile/Honest/Law/MeetsStratLawC.lean): a side hands its message as `Said` items and
`Table`s, whose types hold words below the prime. The term's offline and online provers are the
frame's wherever the functions on the public files that they match on return. Of these,
`makerReturns` and `offlineDescriptionNamed` stand; `ReturnIsTheDescription` is a premise here, a
theorem at all public files (`returnIsTheDescription`, AtFullSide/K14/Sim/ReturnAtTerm.lean), and
public files in scope that the test takes are a premise.

Main names (namespace AtPublicFiles.AtFiles.HonestTerm).
  `offlineAt_stratLaw`   the offline prover at a description, at every private input, instance and
      coin: `StratLaw` at the run values `runValueBytes` of the coin's two run values.
  `onlineAt_stratLaw`    the online prover at a return of the maker, at every number, private input,
      instance and coin: the same.
  `proversAtReturn_stratLaw`   the law at `strats.T` and `strats.B` of the three provers written at
      a description and a return of the maker.
  `honestProvers_eq_atReturn`   at public files in scope that the verifier's test takes, under
      `ReturnIsTheDescription`: `honestProvers` is so written. By `makerReturns`,
      `offlineDescriptionNamed`, `onlineProver_eq`, `offlineProver_eq`
      (AtFullSide/Honest/HonestProverLaws.lean).
  `honestProvers_stratLaw`   under the same, the law at `honestProvers` itself, with two readers of
      run values on its own coins, each of which gives 32 bytes.

Limits. Nothing on acceptance. Nothing at public files where a description is not made or the maker
refuses: there the term's provers are the ones that send the fixed messages, and the seam's plain
part is empty, not of 32 bytes. The three premises hold at the stored files, each by a theorem of
its own: `inScope_full` (Johnson/Goal/Files/ScopeExample.lean), `theLive_zFull`
(AtFullSide/Top/LiveAtFull.lean), `returnIsTheDescription`. Nothing on the link's strategy. A run
value may be 32 zero bytes. `honestProvers` is not the value that the compiler reads: that is these
provers under a step that widens the stop set.
Terms: lean/GLOSSARY.md.

-/
import E2E.TheHonestProver
import AtFullSide.Honest.HonestProverLaws
import AtFullSide.Honest.RunValuesLaw
import E2E.KeyHonestLaw
import E2E.BridgeLawB

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles.HonestTerm
open Iop Prob Hiop AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed AtPublicFiles.Cut
open OnBytes (TableKey)
open OnBytes.Flat (RecFull front₀ join₀ relationsAndEncodingOfClaims)
open OnBytes.Slice (frS)
open _root_.Run (ckP)
open Johnson.Prover.Print (StratLaw)
open ProofFile.Honest (Purse)
open ProofFile.Honest.Term (OnlineReturn onlineMaker)
open VerifierAndGoals (PublicFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData)
open VerifiableInference.Desc (Chain)
open LPFD.Full (XF)

local instance (priority := high) : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) : Inhabited RunValue := ⟨fun _ => 0⟩

variable {files : PublicFiles}

/-- **The offline prover at a description meets `StratLaw`.** -/
theorem offlineAt_stratLaw (parts : Parts files) (description : OfflineDescription)
    (w : (Cz files).I × ((Cz files).Pad × (Cz files).Rnd) × (Cz files).Seed) (x : RecFull)
    (c : (Purse parts.book.shared × RunValue) ×
      ((Purse parts.book.first × Purse parts.book.second) × RunValue)) :
    StratLaw (ckP .two) ((dataAtFiles flashProveData files).DK.at frS.P.T.a)
      (front₀ (dataAtFiles flashProveData files).G.rec₀) (join₀ (dataAtFiles flashProveData files).G.rec₀) ByteArray.empty
      ((offlineProverWithEncodedTable files (keyFileDescription description.source description.numbers description.later) parts.book
        (parts.prover description) runValueBytes runValueBytes (offlineStart description)).strat
        w x c)
      (runValueBytes c.1.2) (runValueBytes c.2.2) :=
  keySeam_stratLaw (dataAtFiles flashProveData files).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData files).E)
    (dataAtFiles flashProveData files).DK (dataAtFiles flashProveData files).DP _ (dataAtFiles flashProveData files).runP
    PV.EntryFive.dsF PV.EntryFive.xsF (dataAtFiles flashProveData files).dec (dataAtFiles flashProveData files).G.rec₀
    (dataAtFiles flashProveData files).G.z₀.2 (LPFD.Full.sBG (dataAtFiles flashProveData files).G).logLeaves
    (dataAtFiles flashProveData files).G.early (LPFD.Full.saltG (dataAtFiles flashProveData files).G) parts.book
    (parts.prover description) runValueBytes runValueBytes (offlineStart description) _
    (dataAtFiles flashProveData files).runK (dataAtFiles flashProveData files).P w x c

/-- **The online prover at a return of the maker meets `StratLaw`.** -/
theorem onlineAt_stratLaw (returned : OnlineReturn files) (places : H2U.Places4)
    (firstChain : Chain P5J.TS ProofFile.Cl) (n : ℕ)
    (w : (Cz files).I × (protocolAtFiles files).EncodingRandomness × (protocolAtFiles files).OutOfDomainSeed) (a : XF × RecFull)
    (κ : CoinG returned.B RunValue RunValue) :
    StratLaw (ckP .two) ((dataAtFiles flashProveData files).DP.at frS.P.T.a)
      (front₀ (dataAtFiles flashProveData files).G.z₀.2) (join₀ (dataAtFiles flashProveData files).G.z₀.2) ByteArray.empty
      ((onlineProverAt returned places firstChain).strat n w a κ)
      (runValueBytes κ.1.2) (runValueBytes κ.2.2) :=
  famAtFiles_stratLaw files _ _ _ returned.B _ _ _ _ (dataAtFiles flashProveData files).P n w a κ

/-- **The three provers of the term, written at a description and a return of the maker.** -/
abbrev proversAtReturn (parts : Parts files) (description : OfflineDescription)
    (returned : OnlineReturn files) (places : H2U.Places4) (firstChain : Chain P5J.TS ProofFile.Cl) :
    OnBytes.Prover.ThreeProvers (protocolAtFiles files) :=
  proversOf
    (offlineProverWithEncodedTable files (keyFileDescription description.source description.numbers description.later) parts.book
      (parts.prover description) runValueBytes runValueBytes (offlineStart description))
    (linkProver files) (onlineProverAt returned places firstChain)

/-- **The law at the offline and the online strategy of the three provers**, at every index, table
randomness, out-of-domain seed, request, number and coins. -/
theorem proversAtReturn_stratLaw (parts : Parts files) (description : OfflineDescription)
    (returned : OnlineReturn files) (places : H2U.Places4) (firstChain : Chain P5J.TS ProofFile.Cl) :
    (∀ i r e₁ κ, StratLaw (ckP .two) ((dataAtFiles flashProveData files).DK.at frS.P.T.a)
      (front₀ (dataAtFiles flashProveData files).G.rec₀) (join₀ (dataAtFiles flashProveData files).G.rec₀) ByteArray.empty
      ((proversAtReturn parts description returned places firstChain).strats.T i r e₁ κ)
      (runValueBytes κ.1.1.2) (runValueBytes κ.1.2.2)) ∧
    ∀ i r e₂ x n κ, StratLaw (ckP .two) ((dataAtFiles flashProveData files).DP.at frS.P.T.a)
      (front₀ (dataAtFiles flashProveData files).G.z₀.2) (join₀ (dataAtFiles flashProveData files).G.z₀.2) ByteArray.empty
      ((proversAtReturn parts description returned places firstChain).strats.B i r e₂ x n κ)
      (runValueBytes κ.2.2.1.2) (runValueBytes κ.2.2.2.2) :=
  ⟨fun i r e₁ κ => offlineAt_stratLaw parts description (i, r, e₁)
      ((protocolAtFiles files).recOf i r e₁) κ.1,
    fun i r e₂ x n κ => onlineAt_stratLaw returned places firstChain n (i, r, e₂)
      (x, (protocolAtFiles files).recOf i r e₂) κ.2.2⟩

/-- **The honest provers are these**, at public files in scope that the verifier's test takes, under
`ReturnIsTheDescription`. -/
theorem honestProvers_eq_atReturn (parts : Parts files) (scope : VerifierAndGoals.InScope files = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    (returnIsDescription : ProofFile.Honest.Term.ReturnIsTheDescription files) :
    ∃ description returned places firstChain,
      honestProvers files parts =
        proversAtReturn parts description returned places firstChain := by
  obtain ⟨description, hd, -⟩ := offlineDescriptionNamed files live
  obtain ⟨returned, made⟩ := ProofFile.Honest.Term.makerReturns files scope live
  obtain ⟨places, firstChain, hp, hc, -⟩ := returnIsDescription scope live returned made
  refine ⟨description, returned, places, firstChain, ?_⟩
  unfold honestProvers
  rw [offlineProver_eq parts hd, onlineProver_eq made hp hc]

/-- **The law at the term itself**, under the same premises. The statement says that two readers of
run values on the provers' coins exist, of 32 bytes each; the proof takes `runValueBytes` of the
coin's two run values, at the coin of the prover that the term is at these public files. -/
theorem honestProvers_stratLaw (parts : Parts files) (scope : VerifierAndGoals.InScope files = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    (returnIsDescription : ProofFile.Honest.Term.ReturnIsTheDescription files) :
    ∃ (runsOffline : (honestProvers files parts).T.Coin → ByteArray × ByteArray)
      (runsOnline : (honestProvers files parts).B.Coin → ByteArray × ByteArray),
      (∀ κ, (runsOffline κ).1.size = 32 ∧ (runsOffline κ).2.size = 32) ∧
      (∀ κ, (runsOnline κ).1.size = 32 ∧ (runsOnline κ).2.size = 32) ∧
      (∀ w x κ, StratLaw (ckP .two) ((dataAtFiles flashProveData files).DK.at frS.P.T.a)
        (front₀ (dataAtFiles flashProveData files).G.rec₀) (join₀ (dataAtFiles flashProveData files).G.rec₀) ByteArray.empty
        ((honestProvers files parts).T.strat w x κ) (runsOffline κ).1 (runsOffline κ).2) ∧
      ∀ w a κ, StratLaw (ckP .two) ((dataAtFiles flashProveData files).DP.at frS.P.T.a)
        (front₀ (dataAtFiles flashProveData files).G.z₀.2) (join₀ (dataAtFiles flashProveData files).G.z₀.2) ByteArray.empty
        ((honestProvers files parts).B.strat w a κ) (runsOnline κ).1 (runsOnline κ).2 := by
  obtain ⟨description, returned, places, firstChain, h⟩ :=
    honestProvers_eq_atReturn parts scope live returnIsDescription
  rw [h]
  exact ⟨fun κ => (runValueBytes κ.1.2, runValueBytes κ.2.2),
    fun κ => (runValueBytes κ.1.2, runValueBytes κ.2.2),
    fun _ => ⟨runValueBytes_size _, runValueBytes_size _⟩,
    fun _ => ⟨runValueBytes_size _, runValueBytes_size _⟩,
    fun w x κ => offlineAt_stratLaw parts description w x κ,
    fun w a κ => onlineAt_stratLaw returned places firstChain w.2.2.2 (w.1, w.2.1, w.2.2.1) a κ⟩

end AtPublicFiles.AtFiles.HonestTerm

#print axioms AtPublicFiles.AtFiles.HonestTerm.honestProvers_stratLaw
#print axioms AtPublicFiles.AtFiles.HonestTerm.proversAtReturn_stratLaw
#print axioms AtPublicFiles.AtFiles.HonestTerm.honestProvers_eq_atReturn
#print axioms AtPublicFiles.AtFiles.HonestTerm.offlineAt_stratLaw
#print axioms AtPublicFiles.AtFiles.HonestTerm.onlineAt_stratLaw
