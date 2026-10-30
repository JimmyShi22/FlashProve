-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K8/AllAtBaseMaker.lean: the smallness test at each of its 25 members, at the named maker, in
one theorem each: what the member owes, and the member's whole form with a family on the state.

  k8_owes_baseMaker     PlaysS, BehindS, ExchangeS and RidesPastS at a member of the kind
  k8_fiveJ_baseMaker    FiveAtBorderJ there, at the run on shapes as the family, from the run's yes
                        and that the honest side fits the member
  k8_cells_at_input_baseMaker, k8_cells_small_baseMaker   the cells at an input that meets
                        ReadyInput, at the return of the named maker

A member of the kind is the draw alone: nothing is sent there and no value is tested. The kind's tests on
values stand at the batching and at the member behind it (BatchValuesBase.lean, BehindValuesFirst.lean).
This file does not say that the range proof is accepted.

Limits. In the first chain the member's yes and the family's next border come from the rule on the table
of steps, so k8_owes_baseMaker is what the kind itself owes at its draws; k8_fiveJ_baseMaker shows that
form with hB, the run on shapes (hyes) and FitsAt as its premises. That the thread stands at any border
at any run is not shown. That the maker returns and that a head stands at its return are premises. The
limits of AtFullSide/K8/ExchangeAtFill.lean stand, in its words: "Behind a yes at which the second stop
is silent. Equations on the Script. NOT IN FRONT OF A LAW OVER COINS. At the messages'
first sending alone." That the digits are right holds of the prover only with K1's PlaysS at the 25
digit sendings, at this Script.
Nothing is claimed on completeness, soundness or hiding. The honest prover's
text named here is E2E/TheHonestProver.lean. The prover of this file is the
one that baseMaker returns: the crossing to the online prover of that text is not made here.
-/
import AtFullSide.K8.AtBaseMaker
import AtFullSide.K8.NextAtDraw
import AtFullSide.K8.OneTextAtTrace
import Johnson.Desc.ProofFile.Honest.Thread.FiveAtBorder

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K8.Term
open OnBytes OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.Sound
open Inst.Model (Instance ppref)
open OnBytes.HonestTrace (Sz cellsC theTrace ServesAt)
open P5J (TS)
open ProofFile.Honest ProofFile.Honest.K1 ProofFile.Honest.K8 ProofFile.Honest.Term
open ProofFile.Honest.FirstThread
open AtPublicFiles.AtFiles
open Johnson.AtFull.Shape

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- **What a member of the kind owes, at the named maker.** -/
theorem k8_owes_baseMaker (hA : baseMaker files = .ok A) (hd : HeadAtReturn files A)
    (numbers : FallNumbers) (w : LocB FullSizeMatrix) (Said : Nat → Coins A.B → Mid (LocB FullSizeMatrix) Unit → Prop)
    (hOk : ∀ b k m, Said b k m → SaidOk b k m) {b : Nat} {pl : Place}
    (ha : P5J.At.ps[b]? = some pl) (hk : pl.kind = KindName.K8) :
    PlaysS (baseThread hd numbers w) Said b ∧ BehindS (baseThread hd numbers w) Said b ∧
      ExchangeS (baseThread hd numbers w) Said b ∧ RidesPastS (baseThread hd numbers w) Said b :=
  ⟨k8_playsS_baseMaker hA hd numbers w Said ha hk, k8_behindS_baseMaker hd numbers w Said ha hk,
    k8_exchangeS_baseMaker hA hd numbers w Said hOk ha hk,
    k8_ridesPastS_baseMaker hd numbers w Said ha hk⟩

/-- **The member's whole form, with the run on shapes as the family.** -/
theorem k8_fiveJ_baseMaker (hA : baseMaker files = .ok A) (hd : HeadAtReturn files A)
    (numbers : FallNumbers) (w : LocB FullSizeMatrix) (Said : Nat → Coins A.B → Mid (LocB FullSizeMatrix) Unit → Prop)
    (hOk : ∀ b k m, Said b k m → SaidOk b k m) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) = .ok Bs)
    (fall : Nat → TS → List Fmt.Drawn → Option String) (a₀ : ShA)
    (hyes : (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)).yes a₀ 358 = true)
    {b : Nat} {pl : Place} (ha : P5J.At.ps[b]? = some pl) (hk : pl.kind = KindName.K8)
    (hF : FitsAt (baseThread hd numbers w) b) :
    FiveAtBorderJ (baseThread hd numbers w) Said
      (shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) a₀) fall b := by
  obtain ⟨p, e, x, r⟩ := k8_owes_baseMaker hA hd numbers w Said hOk ha hk
  exact ⟨p, e, x, r, k8_acceptedJ hd.head hB _ rfl Said fall a₀ hyes ha hk hF,
    k8_nextJ hd.head hB _ rfl Said fall a₀ hyes ha hk⟩

/-- **The cells at an input that meets ReadyInput, at the named maker.** -/
theorem k8_cells_at_input_baseMaker (hA : baseMaker files = .ok A) (hd : HeadAtReturn files A)
    {v : LocB FullSizeMatrix} (hv : ReadyInput hd.description A.H v) :
    ∃ (i : Cm.Idx) (x : Instance ppref), ProofFile.instOf v.x = some x ∧ ServesAt A.Z.p.X i x ∧
      v.trace = cellsC A.Z.p.X (theTrace A.Z.p.X i x) ∧
      ∀ l, l < 25 → ∀ mu r c, cellsAtOf (id v.trace) (K3.matsOwn A.G.W l) mu r c =
        theTrace A.Z.p.X i x l mu r c :=
  cells_at_input hA (k8_readyLaws_baseMaker hA hd) hv

/-- **Those cells are small at every place.** -/
theorem k8_cells_small_baseMaker (hA : baseMaker files = .ok A) (hd : HeadAtReturn files A)
    {v : LocB FullSizeMatrix} (hv : ReadyInput hd.description A.H v)
    (p : VerifiableInference.Desc.First.K8.Par) (l : Nat) :
    VerifiableInference.Desc.First.K8.Honest.cellsSmall p
      (cellsAtOf (id v.trace) (K3.matsOwn A.G.W l)) = true :=
  cells_small_at_input (k8_readyLaws_baseMaker hA hd) hv p l

end AtFullSide.K8.Term

#print axioms AtFullSide.K8.Term.k8_owes_baseMaker
#print axioms AtFullSide.K8.Term.k8_fiveJ_baseMaker
#print axioms AtFullSide.K8.Term.k8_cells_at_input_baseMaker
#print axioms AtFullSide.K8.Term.k8_cells_small_baseMaker
