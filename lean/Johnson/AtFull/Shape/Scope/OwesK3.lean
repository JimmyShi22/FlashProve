-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/OwesK3.lean: THE KIND K3's DEBT OF owesS_firstThread AT THE FIRST THREAD OF THE BASE MAKER, BY KIND: lookupPaysAllFiveAtTheFirstThreadAtTheFirstScript, at every number of that kind in the written list.

Limits. Every premise named here stays a premise. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.OwesByKind
import E2E.Lookup.LookupPaysAllFiveAtTheFirstScript
import Johnson.P5J.K09Len
import AtFullSide.K2.ClosingAtReturn

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Scope
open VerifiableInference.Desc (KindName)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open ProofFile ProofFile.Honest ProofFile.Honest.K3 ProofFile.Honest.K3.Term
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts firstThread firstLetters)
open ProofFile.Honest.K1 (PlaceIn)
open ProofFile.Honest.Term (baseMaker matrixInput)
open AtPublicFiles.AtFiles (FullSizeMatrix)

set_option maxRecDepth 1000000 in
/-- Every place of the kind K3 in the written list stands at one of the fifty numbers. A closed fact. -/
theorem writtenPlaces_K3_at_borders : ∀ j < P5J.At.ps.length,
    (P5J.At.ps[j]?).any (fun p => p.kind == KindName.K3) = true →
      j ∈ (List.range 25).flatMap (fun l => [borderOf l false, borderOf l true]) := by decide +kernel

theorem K3_at_border {b : Nat} {p : VerifiableInference.Desc.Place} (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K3) : ∃ l d, l < 25 ∧ b = borderOf l d := by
  have hb : b < P5J.At.ps.length := by
    by_contra c
    rw [List.getElem?_eq_none (Nat.le_of_not_lt c)] at hp
    cases hp
  have hm := writtenPlaces_K3_at_borders b hb (by rw [hp]; simp [hk])
  simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hm
  obtain ⟨l, hl, e | e⟩ := hm
  · exact ⟨l, false, hl, e⟩
  · exact ⟨l, true, hl, e⟩

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- **K3_paid.** Conditional on the head, the maker's return, the Script, Said → SaidOk and the closings
at zeros. -/
theorem K3_paid (made : baseMaker files = .ok A) (head : HeadAtReturn files A)
    (parts : FirstThreadParts A)
    (script : parts.script = ProofFile.Honest.K1.firstScriptAt matrixInput OnBytes.HonestTrace.Sz.ref
      openHonest A head.firstChain)
    (closings : ∀ place ∈ K2.switchPlaces A.Z A.G,
      K2.closingOk K2.freshTable ((K2.segmentsOf A.Z A.G).take place.link) place = true)
    (w : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells)
    (Said : Nat → Coins A.B → Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m) :
    KindPaid (firstLetters head parts w) Said KindName.K3 := by
  intro b p hp hk
  obtain ⟨l, d, hl, rfl⟩ := K3_at_border hp hk
  exact paidAt_of_five (L := firstLetters head parts w) (AtPublicFiles.Lookup.lookupPaysAllFiveAtTheFirstThreadAtTheFirstScript made head parts
    script closings w Said hSaid (fun _ _ _ => none) l hl d)

/-- **K3_paid at the first Script, on the head, the maker's return and Said → SaidOk alone.** -/
theorem K3_paid_at_script (made : baseMaker files = .ok A) (head : HeadAtReturn files A)
    (numbers : ProofFile.Honest.FirstThread.FallNumbers) (w : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells)
    (Said : Nat → Coins A.B → Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m) :
    KindPaid
      (firstLetters head
        ⟨ProofFile.Honest.K1.firstScriptAt matrixInput OnBytes.HonestTrace.Sz.ref openHonest A head.firstChain,
          numbers⟩ w)
      Said KindName.K3 :=
  K3_paid made head _ rfl (AtFullSide.K2.Term.closing_at_return head.head made) w Said hSaid

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.K3_paid
#print axioms Johnson.AtFull.Shape.Scope.K3_paid_at_script
