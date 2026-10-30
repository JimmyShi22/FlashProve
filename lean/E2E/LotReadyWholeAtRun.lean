-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotReadyWholeAtRun.lean: E2E/LotReadyWhole.lean with all sixteen sides paid, IN THE SHAPE IN
WHICH IT IS SPENT, and a shown case.

  LotReadyAtRunWhole      the second clause of AtRunS (E2E/KeyAcceptPairs.lean), its ∃ R with ready alone,
                          at the offline prover's own senders, at every input that is tied with
                          ok := AtPublicFiles.AtFiles.inRange and every coin, at the written book keyBook K₀: the
                          letters at which the socket offlineDebts_from_chains asks it
  LotReadyAtTermBookWhole the same at the term's own book offlineProverCoinCounts, at every ok that gives the range
  lotReadyShownWhole      A SHOWN CASE: at the written copy of the full-size public files ready returns,
                          at the prover's named index, a table's randomness of zeros, one instance and
                          the default coins

They are E2E/LotReadyAtRun.lean's and E2E/LotReadyShown.lean's statements with the premise LookupsStated
paid by lookupsStated_walked. TiedText (E2E/LotReadyAtRunCore.lean) is the body of TiedOffline
(E2E/OfflineAtParts.lean), which the socket spends, spelled out so that this file need not stand over that
one. That the two are one is not said here: tiedText_is (E2E/LotTiedIsTied.lean) says it, by unfolding, and
lotReadyAtTied there is the first statement at TiedOffline itself.
Premises: the test on the public files says yes; offlineDescription returns d; scope; fullPub = some K₀.
In the shown case none: there the test's yes is a theorem of the SIDE library
(AtFullSide.Top.theLive_zFull); storedPublicFiles is a value written in Lean, and no theorem ties it to a file on
a disk.
Limits. AtRunS's other clauses are not here. ready says that the rounds are prepared: no round has been
played, and nothing says that a move returns or that a verifier accepts. The written sizes alone.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.LotReadyWhole
import E2E.LotReadyAtRun
import E2E.LotReadyShown

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.OfflineRows.Lots
open ProofFile.Honest
open ProofFile.Honest.Term (matrixInput)
open VerifiableInference.Desc.Key (keyInstanceOfOutOfDomainSample)
open VerifiableInference.OnPublicFiles (recZeroFull)
open AtPublicFiles.KeyLink (CoinOne)
open AtPublicFiles.KeyFile (KeyInst keyProver)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.AtFiles (keyFileDescription FullSizeMatrix Cz protocolAtFiles)
open AtPublicFiles.AtFiles.HonestTerm (OfflineDescription offlineDescription offlineProverCoinCounts)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)

/-- **Ready returns in AtRunS's own shape, at the socket's letters.** -/
def LotReadyAtRunWhole : Prop :=
  ∀ {Z : PublicFiles} {d : OfflineDescription} {K₀ : KeyPub} {Q₂ Q₃ : Type} [Inhabited Q₃]
    (val₂ : Q₂ → ByteArray) (val₃ : Q₃ → ByteArray), protocolDataWellFormed (asDescriptionFiles Z) = true →
    offlineDescription Z = .ok d → InScope Z = true → fullPub = some K₀ →
    ∀ (w : FullSizeMatrix × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed) (x : KeyInst)
      (c : CoinOne (keyBook K₀) Q₂ Q₃),
      TiedText Z d.source d.numbers d.later val₂ val₃ (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) d)
        AtPublicFiles.AtFiles.inRange w x →
      ∃ R, ready (keyFileDescription d.source d.numbers d.later) (keyBook K₀)
        (keyProver (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) d)) w.1 w.2.1 x
        ⟨c.2.1.1, c.1.1, c.2.1.2⟩ = .ok R

theorem lotReadyAtRunWhole : LotReadyAtRunWhole :=
  fun val₂ val₃ live hd scope hK =>
    lotReadyAtRunCut val₂ val₃ live hd scope hK (lookupsStated_walked live hd scope hK)

/-- **The same at the term's own book.** -/
def LotReadyAtTermBookWhole : Prop :=
  ∀ {Z : PublicFiles} {d : OfflineDescription} {K₀ : KeyPub} {Q₂ Q₃ : Type} [Inhabited Q₃]
    (val₂ : Q₂ → ByteArray) (val₃ : Q₃ → ByteArray) (ok : FullSizeMatrix → Prop),
    (∀ M, ok M → matrixInput.inRange M = true) → protocolDataWellFormed (asDescriptionFiles Z) = true →
    offlineDescription Z = .ok d → InScope Z = true → fullPub = some K₀ →
    ∀ (w : FullSizeMatrix × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed) (x : KeyInst)
      (c : CoinOne offlineProverCoinCounts Q₂ Q₃),
      TiedText Z d.source d.numbers d.later val₂ val₃ (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) d)
        ok w x →
      ∃ R, ready (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts
        (keyProver (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) d)) w.1 w.2.1 x
        ⟨c.2.1.1, c.1.1, c.2.1.2⟩ = .ok R

theorem lotReadyAtTermBookWhole : LotReadyAtTermBookWhole :=
  fun val₂ val₃ ok hok live hd scope hK =>
    lotReadyAtTermBook val₂ val₃ ok hok live hd scope hK (lookupsStated_walked live hd scope hK)

/-- **A SHOWN CASE: at the written full-size files ready returns.** -/
theorem lotReadyShownWhole :
    ∃ (description : OfflineDescription) (K₀ : KeyPub),
      offlineDescription VerifierAndGoals.storedPublicFiles = .ok description ∧ fullPub = some K₀ ∧
        ∃ R, ready (keyFileDescription description.source description.numbers description.later) (keyBook K₀)
          (keyProver (AtPublicFiles.KeyStandWalked.offlineValue (files := VerifierAndGoals.storedPublicFiles) description))
          matrixInput.dummy (zeroTable : (protocolAtFiles VerifierAndGoals.storedPublicFiles).EncodingRandomness) (keyInstanceOfOutOfDomainSample recZeroFull) default = .ok R := by
  obtain ⟨d, K₀, hd, hK, h⟩ := lotReadyShown lotReadyReturns
  exact ⟨d, K₀, hd, hK,
    h (lookupsStated_walked AtFullSide.Top.theLive_zFull hd VerifierAndGoals.inScope_full hK)⟩

end AtPublicFiles.OfflineRows.Lots

#print axioms AtPublicFiles.OfflineRows.Lots.lotReadyAtRunWhole
#print axioms AtPublicFiles.OfflineRows.Lots.lotReadyAtTermBookWhole
#print axioms AtPublicFiles.OfflineRows.Lots.lotReadyShownWhole
