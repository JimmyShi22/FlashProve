-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/OwedAtLetters.lean: the closing of a segment (K10): the kind's field of the first thread's debt
(`FirstOwed.k10`, Johnson/AtFull/Shape/Scope/OwesByKind.lean): `KindPaid` at the kind K10: at every number at which the written list of
places has a place of that kind, the sender plays and each item that the row owes is exchanged.

  **`kindTen_paid`**              the field, general in the numbers of the falls, the input and Said (which gives `SaidOk`)
  **`kindTen_paid_at_letters`**   the field at the first chain's named letters (AtFullSide/Honest/TheLettersFirst.lean): no premise on Said

By `kindTen_five_at_number` (AtFullSide/K10/FiveByNumber.lean), `paidAt_of_five`, and the closed fact that the written list has a
place of the kind K10 at the 25 closings' numbers alone (`writtenPlaces_kindTen_at_borders`, Honest/K10/Pay/KindTenPlaces.lean).

Limits. Premises: the head at the return and the maker's return at the base filling. This is the base prover, whose table
randomness has the type `IndexCommitterCoins`. The statements speak at the stands at which the thread's invariant and Said hold; that a run stands
there is not proved here.
-/
import AtFullSide.K10.FiveAtLetters
import Johnson.AtFull.Shape.Scope.OwesByKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K10
open VerifiableInference.Desc
open OnBytes.HonestTrace (Sz)
open OnBytes (TableKey)
open P5J (TS)
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (matrixInput)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open ProofFile.Honest.K1 (firstScriptAt)
open AtFullSide.Honest.TheLetters
open Johnson.AtFull.Shape.Scope (KindPaid paidAt_of_five)

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (h : HeadAtReturn files A)
  (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
    (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction Sz.ref openHonest) = .ok A)

include made in
/-- **The kind's field of the first thread's debt.** -/
theorem kindTen_paid (numbers : FallNumbers) (input : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells)
    (Said : Nat → Coins A.B → Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m) :
    KindPaid (firstLetters h ⟨firstScriptAt matrixInput Sz.ref openHonest A h.firstChain, numbers⟩ input) Said
      KindName.K10 := by
  intro b p hp hk
  have hb : b < P5J.At.ps.length := by
    rcases Nat.lt_or_ge b P5J.At.ps.length with hlt | hge
    · exact hlt
    · rw [List.getElem?_eq_none hge] at hp
      cases hp
  have hm := ProofFile.Honest.K10.writtenPlaces_kindTen_at_borders b hb (by rw [hp]; simp [hk])
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hm
  exact paidAt_of_five (fall := fun _ _ _ => none)
    (kindTen_five_at_number h made numbers input Said hSaid _ (List.mem_range.1 hl))

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

include made in
/-- **The field at the first chain's named letters.** -/
theorem kindTen_paid_at_letters (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit) :
    KindPaid (firstLetters h (first h) R.own) (said₁ h R) KindName.K10 :=
  kindTen_paid h made (numbers h) R.own (said₁ h R) (fun b k m hs => saidOk_of_walk _ b k m hs)

end AtFullSide.K10

#print axioms AtFullSide.K10.kindTen_paid
#print axioms AtFullSide.K10.kindTen_paid_at_letters
