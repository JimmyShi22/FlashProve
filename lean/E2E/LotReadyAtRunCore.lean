-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotReadyAtRunCore.lean: where «ready returns» is spent: the second clause of AtRunS (E2E/KeyAcceptPairs.lean), which
the offline prover's accept law asks at every tied input and every coin. What «tied» gives on the index, and the
clause's own shape from «ready returns at every index in range».

  TiedText        the body of TiedOffline (E2E/OfflineAtParts.lean), spelled: the frame's Tied at the key's prover, the
                  seat's letters and the committer's relation at the letter ok
  ok_of_tied      a tied input's index has ok: the one thing that «tied» says of the index alone
  no_ready_out    A CONTROL: at an index out of the prover's range ready never returns, at any description, book,
                  prover, instance and coins
  readyAtRun_of   the clause's shape: where ok gives the range and ready returns at every index in range

Limits. ok is a letter: at ok := fun _ => True a tied input's index need not be in range, and by no_ready_out the
clause is then false there. ready says that the rounds are prepared, not that a move returns. Nothing on
soundness, completeness, hiding or binding.
-/
import E2E.KeyTied
import E2E.KeyAcceptPairs
import E2E.KeyProver

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.OfflineRows.Lots
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.KeyLink AtPublicFiles.Committed
open AtPublicFiles.KeyFile (KeyParts keyProver)
open OnBytes.Flat (relationsAndEncodingOfClaims)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (FileDescription)
open VerifiableInference.Desc.Key (Source LaterPlaces)
open ProofFile.Honest
open VerifierAndGoals (PublicFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData)

local instance (priority := high) padsAtRunCore : Nonempty PadZ := pads_nonempty frS 402653181

section
variable (Z : PublicFiles) (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) {Q₂ Q₃ : Type} [Inhabited Q₃]
  (val₂ : Q₂ → ByteArray) (val₃ : Q₃ → ByteArray) {X₀ Xh Wk : Type}
  (K : KeyParts FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) X₀ Xh Wk)

/-- **TiedOffline's body, spelled.** -/
abbrev TiedText (ok : FullSizeMatrix → Prop) (w : FullSizeMatrix × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed) (x : KeyInst) :
    Prop :=
  Tied ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) (keyFileDescription X N P) (keyProver K)
    (keySeam (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) val₂ val₃)
    (tableOf (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK)
    (pubAt val₂ val₃ keyAnswersTied 0) (keyFirst X N P) (relKeyZ Z ok) w x

variable {Z X N P val₂ val₃ K}

/-- **A tied input's index has ok.** -/
theorem ok_of_tied {ok : FullSizeMatrix → Prop} {w : FullSizeMatrix × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed} {x : KeyInst}
    (t : TiedText Z X N P val₂ val₃ K ok w x) : ok w.1 := by
  obtain ⟨_, _, h⟩ := (relKey_iff (AZ Z) PadZ (holdZ Z) ok w.1 w.2.1 x).1 t.rel
  exact h

end

section
variable {Xi W₀ Rc Ky Tr X₀ X : Type}

/-- **A control: out of the prover's range ready never returns.** -/
theorem no_ready_out (F : FileDescription Xi) (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) {w₀ : W₀}
    (h : H.inRange w₀ = false) (rc : Rc) (x : Xi) (k : Coins B) :
    ∀ R, ready F B H w₀ rc x k ≠ .ok R := by
  have e : ∃ r, readyTests F B H w₀ = .error r := by
    unfold readyTests
    split_ifs <;> first | exact ⟨_, rfl⟩ | simp_all
  obtain ⟨r, hr⟩ := e
  intro R hR
  unfold ready at hR
  rw [hr] at hR
  cases hR

end

section
variable {Z : PublicFiles} {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces} {Q₂ Q₃ : Type} [Inhabited Q₃]
  {val₂ : Q₂ → ByteArray} {val₃ : Q₃ → ByteArray} {X₀ Xh Wk : Type}
  {K : KeyParts FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) X₀ Xh Wk}

/-- **The clause's own shape.** -/
theorem readyAtRun_of (B : ProverCoinCounts) {ok : FullSizeMatrix → Prop}
    (hok : ∀ M, ok M → (keyProver K).inRange M = true)
    (hret : ∀ (w₀ : FullSizeMatrix) (rc : (Cz Z).Pad × (Cz Z).Rnd) (x : KeyInst) (k : Coins B),
      (keyProver K).inRange w₀ = true → ∃ R, ready (keyFileDescription X N P) B (keyProver K) w₀ rc x k = .ok R)
    (w : FullSizeMatrix × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed) (x : KeyInst) (c : CoinOne B Q₂ Q₃)
    (t : TiedText Z X N P val₂ val₃ K ok w x) :
    ∃ R, ready (keyFileDescription X N P) B (keyProver K) w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ = .ok R :=
  hret w.1 w.2.1 x _ (hok _ (ok_of_tied t))

end

end AtPublicFiles.OfflineRows.Lots

#print axioms AtPublicFiles.OfflineRows.Lots.ok_of_tied
#print axioms AtPublicFiles.OfflineRows.Lots.no_ready_out
#print axioms AtPublicFiles.OfflineRows.Lots.readyAtRun_of
