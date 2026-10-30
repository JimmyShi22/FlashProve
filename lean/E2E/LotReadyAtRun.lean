-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotReadyAtRun.lean: «ready returns» (lotReadyReturns, E2E/LotReadyDebts.lean) IN THE SHAPE IN WHICH IT IS SPENT:
the second clause of AtRunS (E2E/KeyAcceptPairs.lean) at the offline prover's own senders, at every tied input and every
coin; at the written book keyBook K₀, and at the term's own book offlineProverCoinCounts (E2E/KeyArgumentsAt.lean).

  LotReadyAtRun, lotReadyAtRun   at keyBook K₀, at every letter ok that gives the prover's range
  LotReadyAtRunCut, lotReadyAtRunCut   at ok := the object's cut (AtPublicFiles.AtFiles.inRange), by inRange_iff
                  (E2E/KeyRangeOne.lean)
  offlineBook_is  at the written sizes the term's book is the written book
  LotReadyAtTermBook, lotReadyAtTermBook   the same at offlineProverCoinCounts

Premises. The test on the public files says yes; offlineDescription returns the description; scope;
fullPub = some K₀; LookupsStated (not proved in this file: E2E/LotLookupsStated.lean). And on the letter ok: it gives the range.
Limits. As lotReadyReturns's. AtRunS's other eight clauses are not here. At ok := fun _ => True the clause is false at an index
out of range (no_ready_out, E2E/LotReadyAtRunCore.lean). Nothing on soundness, completeness, hiding or binding.
-/
import E2E.LotReadyAtRunCore
import E2E.LotReadyDebts
import E2E.KeyRangeOne

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.OfflineRows.Lots
open ProofFile.Honest
open ProofFile.Honest.Term (matrixInput)
open AtPublicFiles.KeyLink (CoinOne)
open AtPublicFiles.KeyFile (KeyInst keyProver)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.AtFiles (keyFileDescription FullSizeMatrix Cz)
open AtPublicFiles.AtFiles.HonestTerm (OfflineDescription offlineDescription offlineProverCoinCounts inRange_iff)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)

/-- **Ready returns in AtRunS's own shape**, at the written book. -/
def LotReadyAtRun : Prop :=
  ∀ {Z : PublicFiles} {d : OfflineDescription} {K₀ : KeyPub} {Q₂ Q₃ : Type} [Inhabited Q₃]
    (val₂ : Q₂ → ByteArray) (val₃ : Q₃ → ByteArray) (ok : FullSizeMatrix → Prop),
    (∀ M, ok M → matrixInput.inRange M = true) → protocolDataWellFormed (asDescriptionFiles Z) = true →
    offlineDescription Z = .ok d → InScope Z = true → fullPub = some K₀ →
    LookupsStated K₀ (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) d) →
    ∀ (w : FullSizeMatrix × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed) (x : KeyInst)
      (c : CoinOne (keyBook K₀) Q₂ Q₃),
      TiedText Z d.source d.numbers d.later val₂ val₃ (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) d) ok w x →
      ∃ R, ready (keyFileDescription d.source d.numbers d.later) (keyBook K₀)
        (keyProver (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) d)) w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ = .ok R

theorem lotReadyAtRun : LotReadyAtRun := by
  intro Z d K₀ Q₂ Q₃ _ val₂ val₃ ok hok live hd scope hK hL w x c t
  exact readyAtRun_of (keyBook K₀) hok
    (fun w₀ rc x k hin => lotReadyReturns live hd scope hK hL w₀ rc x k hin) w x c t

/-- **The same at the object's cut.** -/
def LotReadyAtRunCut : Prop :=
  ∀ {Z : PublicFiles} {d : OfflineDescription} {K₀ : KeyPub} {Q₂ Q₃ : Type} [Inhabited Q₃]
    (val₂ : Q₂ → ByteArray) (val₃ : Q₃ → ByteArray), protocolDataWellFormed (asDescriptionFiles Z) = true →
    offlineDescription Z = .ok d → InScope Z = true → fullPub = some K₀ →
    LookupsStated K₀ (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) d) →
    ∀ (w : FullSizeMatrix × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed) (x : KeyInst)
      (c : CoinOne (keyBook K₀) Q₂ Q₃),
      TiedText Z d.source d.numbers d.later val₂ val₃ (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) d)
        AtPublicFiles.AtFiles.inRange w x →
      ∃ R, ready (keyFileDescription d.source d.numbers d.later) (keyBook K₀)
        (keyProver (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) d)) w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ = .ok R

theorem lotReadyAtRunCut : LotReadyAtRunCut := fun val₂ val₃ =>
  lotReadyAtRun val₂ val₃ AtPublicFiles.AtFiles.inRange fun M h => (inRange_iff M).2 h

/-- At the written sizes the term's book is the written book. -/
theorem offlineBook_is {K₀ : KeyPub} (hK : fullPub = some K₀) : offlineProverCoinCounts = keyBook K₀ := by
  unfold offlineProverCoinCounts
  rw [hK]

/-- **The same at the term's own book.** -/
def LotReadyAtTermBook : Prop :=
  ∀ {Z : PublicFiles} {d : OfflineDescription} {K₀ : KeyPub} {Q₂ Q₃ : Type} [Inhabited Q₃]
    (val₂ : Q₂ → ByteArray) (val₃ : Q₃ → ByteArray) (ok : FullSizeMatrix → Prop),
    (∀ M, ok M → matrixInput.inRange M = true) → protocolDataWellFormed (asDescriptionFiles Z) = true →
    offlineDescription Z = .ok d → InScope Z = true → fullPub = some K₀ →
    LookupsStated K₀ (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) d) →
    ∀ (w : FullSizeMatrix × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed) (x : KeyInst)
      (c : CoinOne offlineProverCoinCounts Q₂ Q₃),
      TiedText Z d.source d.numbers d.later val₂ val₃ (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) d) ok w x →
      ∃ R, ready (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts
        (keyProver (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) d)) w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ = .ok R

theorem lotReadyAtTermBook : LotReadyAtTermBook := by
  intro Z d K₀ Q₂ Q₃ _ val₂ val₃ ok hok live hd scope hK hL w x
  rw [offlineBook_is hK]
  exact lotReadyAtRun val₂ val₃ ok hok live hd scope hK hL w x

end AtPublicFiles.OfflineRows.Lots

#print axioms AtPublicFiles.OfflineRows.Lots.lotReadyAtRun
#print axioms AtPublicFiles.OfflineRows.Lots.lotReadyAtRunCut
#print axioms AtPublicFiles.OfflineRows.Lots.offlineBook_is
#print axioms AtPublicFiles.OfflineRows.Lots.lotReadyAtTermBook
