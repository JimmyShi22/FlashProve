-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3KeeperRides.lean: the kind "lookup" (K3): THE TABLE's OWN THREE PUBLIC
ITEMS (ledger, freeAbove, unheard: Johnson/Desc/First/FillKeeper.lean) RIDE OVER A YES OF THE LOOKUP
ON THE DIGITS: at the Bools of that layer, from the facts that a yes of the seated digits' piece
leaves (SameBut, DigLeft). With two bridges: that layer's ledgerB and freeAboveB n ARE the lookups'
own Bools. Statements and proofs.

Main names.
  ledgerB_is: First.ledgerB s = s.fork?.any K3.sizedB: by rfl. freeAboveB_is: First.freeAboveB n s =
    freeAboveAtB n s (K3CallsKeeps.lean).
  digLeft_ledgerB, digLeft_freeAboveB: the two ride from s to t under DigLeft s t (the second asks
    the first in front, for the ledger's sizes).
  sameBut_unheardB: the third is one value at both states under SameBut.
OBJECT. Bools on the verifier's state; no block's text.
USER. ledgerB_is, freeAboveB_is: K3CallsAt.lean, K3CallsAtR.lean, Johnson/Desc/Sound/MgAt/
K3RidesLed.lean, K3CallsOthers.lean · digLeft_ledgerB, digLeft_freeAboveB: MgAt/K3DigitsOthers.lean,
K3DigitsMaskSeat.lean · sameBut_unheardB: no file calls it.
LETTERS. s, t, n.
IS IT EMPTY? DigLeft, SameBut: had by theorem at a yes of the seated piece (k3_digits_seated_leaves,
k3_digits_seated_turns).
Compiled with the whole library.
(Where this and lean/THEOREM.md differ, the page holds.)
Limits. Of the three Bools alone. Which other items are open behind the block, and that they ride,
is not said.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.FillKeeper
import Johnson.Desc.First.Look.K3DigitsSeatedLeaves
import Johnson.Desc.First.Look.K3DigitsTies

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model

/-- The table's own Bool on the ledger is the lookups'. -/
theorem ledgerB_is (s : Desc.First.S) :
    Desc.First.ledgerB s = s.fork?.any Desc.K3.sizedB := rfl

/-- The table's own "free above, with n slots" is the lookups'. -/
theorem freeAboveB_is (n : ℕ) (s : Desc.First.S) :
    Desc.First.freeAboveB n s = freeAboveAtB n s := by
  unfold Desc.First.freeAboveB freeAboveAtB freeAboveB
  cases s.fork? with
  | none => rfl
  | some G => rfl

/-- **ledger rides.** -/
theorem digLeft_ledgerB {s t : Desc.First.S} (DL : DigLeft s t)
    (h : Desc.First.ledgerB s = true) : Desc.First.ledgerB t = true := by
  obtain ⟨F, Gk, hF, hG, -, hZ, -⟩ := DL
  rw [ledgerB_is, hF] at h
  have hS : OnBytes.PscRun.Sized F := sized_of_sizedB h
  obtain ⟨-, ⟨z1, z2, z3⟩, -⟩ := hZ hS
  rw [ledgerB_is, hG]
  show Desc.K3.sizedB Gk = true
  simp [Desc.K3.sizedB, z1, z2, z3]

/-- **freeAbove rides**, with the number of slots. -/
theorem digLeft_freeAboveB {s t : Desc.First.S} (DL : DigLeft s t)
    (hL : Desc.First.ledgerB s = true) (n : ℕ) (h : Desc.First.freeAboveB n s = true) :
    Desc.First.freeAboveB n t = true := by
  obtain ⟨F, Gk, hF, hG, -, hZ, -⟩ := DL
  rw [ledgerB_is, hF] at hL
  obtain ⟨hLat, -, hFree⟩ := hZ (sized_of_sizedB hL)
  rw [freeAboveB_is] at h ⊢
  unfold freeAboveAtB at h ⊢
  rw [Bool.and_eq_true] at h ⊢
  refine ⟨hFree h.1, ?_⟩
  have h2 := h.2
  rw [hF] at h2
  rw [hG]
  have e : F.ns = n := by simpa using h2
  show (Gk.ns == n) = true
  rw [hLat.ns, e]
  exact beq_self_eq_true n

/-- **unheard is one value at both states.** -/
theorem sameBut_unheardB {s t : Desc.First.S} (T : SameBut s t) :
    Desc.First.unheardB t = Desc.First.unheardB s := by
  unfold Desc.First.unheardB
  rw [T.out]

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.ledgerB_is
#print axioms VerifiableInference.OnPublicFiles.freeAboveB_is
#print axioms VerifiableInference.OnPublicFiles.digLeft_ledgerB
#print axioms VerifiableInference.OnPublicFiles.digLeft_freeAboveB
#print axioms VerifiableInference.OnPublicFiles.sameBut_unheardB
