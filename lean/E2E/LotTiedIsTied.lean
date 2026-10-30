-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotTiedIsTied.lean: THE READING BECOMES A THEOREM: TiedText (E2E/LotReadyAtRunCore.lean), at which
«ready returns» is stated in AtRunS's shape, IS TiedOffline (E2E/OfflineAtParts.lean), which the socket
spends: by unfolding. And so «ready returns» at TiedOffline itself.

  tiedText_is          TiedText … = TiedOffline …, at all letters: rfl
  LotReadyAtTied       THE STATEMENT: at every input that is tied (TiedOffline, ok := inRange) and every coin, at the
                       offline prover's own senders and the written book, ∃ R, ready … = .ok R
  inRange_of_tied      a tied input's matrix passes the test that ready reads

Premises of LotReadyAtTied: the test on the public files says yes; offlineDescription returns d; scope;
fullPub = some K₀.
Limits. Those of E2E/LotReadyWholeAtRun.lean. If TiedOffline's text turns, this file goes red: that is what it is for.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.OfflineAtParts
import E2E.LotReadyWholeAtRun

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.OfflineRows.Lots
open ProofFile.Honest
open ProofFile.Honest.Term (matrixInput)
open VerifiableInference.Desc.Key (Source LaterPlaces)
open AtPublicFiles.KeyLink (CoinOne)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.AtFiles (keyFileDescription FullSizeMatrix Cz TiedOffline)
open AtPublicFiles.AtFiles.HonestTerm (OfflineDescription offlineDescription inRange_iff)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)

section
variable (Z : PublicFiles) (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) {Q₂ Q₃ : Type}
  [Inhabited Q₃] (val₂ : Q₂ → ByteArray) (val₃ : Q₃ → ByteArray) {X₀ Xh Wk : Type} (K : KeyParts FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) X₀ Xh Wk)

/-- **The two are one.** -/
theorem tiedText_is (ok : FullSizeMatrix → Prop) (w : FullSizeMatrix × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed)
    (x : KeyInst) :
    TiedText Z X N P val₂ val₃ K ok w x = TiedOffline Z X N P val₂ val₃ K ok w x := rfl

end

/-- A tied input's matrix passes the test that ready reads. -/
theorem inRange_of_tied {Z : PublicFiles} {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces} {Q₂ Q₃ : Type}
    [Inhabited Q₃] {val₂ : Q₂ → ByteArray}
    {val₃ : Q₃ → ByteArray} {X₀ Xh Wk : Type} {K : KeyParts FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) X₀ Xh Wk}
    {w : FullSizeMatrix × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed} {x : KeyInst}
    (t : TiedOffline Z X N P val₂ val₃ K AtPublicFiles.AtFiles.inRange w x) :
    matrixInput.inRange w.1 = true :=
  (inRange_iff w.1).2 (ok_of_tied ((tiedText_is Z X N P val₂ val₃ K _ w x).symm ▸ t))

/-- **Ready returns at the socket's own «tied».** -/
def LotReadyAtTied : Prop :=
  ∀ {Z : PublicFiles} {d : OfflineDescription} {K₀ : KeyPub} {Q₂ Q₃ : Type} [Inhabited Q₃]
    (val₂ : Q₂ → ByteArray) (val₃ : Q₃ → ByteArray),
    protocolDataWellFormed (asDescriptionFiles Z) = true → offlineDescription Z = .ok d → InScope Z = true →
    fullPub = some K₀ →
    ∀ (w : FullSizeMatrix × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed) (x : KeyInst)
      (c : CoinOne (keyBook K₀) Q₂ Q₃),
      TiedOffline Z d.source d.numbers d.later val₂ val₃
        (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) d) AtPublicFiles.AtFiles.inRange w x →
      ∃ R, ready (keyFileDescription d.source d.numbers d.later) (keyBook K₀)
        (keyProver (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) d)) w.1 w.2.1 x
        ⟨c.2.1.1, c.1.1, c.2.1.2⟩ = .ok R

theorem lotReadyAtTied : LotReadyAtTied :=
  fun val₂ val₃ live hd scope hK w x c t =>
    lotReadyAtRunWhole val₂ val₃ live hd scope hK w x c
      ((tiedText_is _ _ _ _ val₂ val₃ _ _ w x).symm ▸ t)

end AtPublicFiles.OfflineRows.Lots

#print axioms AtPublicFiles.OfflineRows.Lots.tiedText_is
#print axioms AtPublicFiles.OfflineRows.Lots.inRange_of_tied
#print axioms AtPublicFiles.OfflineRows.Lots.lotReadyAtTied
