-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/CountsAtFour.lean: the row "TS.54", its other four: IN THE GOALS' SCOPE, AT
THE NUMBERS CLOSED OVER THE FIRST CHAIN's OWN SUB-PROTOCOLS, THE TWO COUNTS AT: the first segment's
opening (number 2 of the flat list) · the kind K13's batching (355) · W's commitment with K13's rows
behind it (356) · the chain's last sub-protocol (357). They are the fields trees and msgs of RowG,
RowM3, RowM4 (Johnson/Desc/K13/Law/AtTableFirst.lean, AtTable.lean, AtTableW.lean) and the binders
hNt, hNm of k13_law_top, to the letter. A joining of what lies. A law file; no running text imports
it.
  places_nodup_full: the written list of the 358 places has no place twice: a closed fact, by Lean's
      kernel: so the premise hn of Johnson/Desc/AtSeats/CountsAtFifty.lean is paid
  frames_tell_nothing: the segments' frames' sub-protocols declare no oracle
  at_first, at_355, at_356, at_357: what stands at the four numbers, and what it declares: by the
      theorems k1_first_of, back_of, back_numbers, seal_seated, hear_at_flat,
      flatIx_scope (files of Johnson/IMR/)
  counts_fifty: hear_K1's two binders once more, without hn
  counts_first, counts_355, counts_356, counts_357: the two counts there

PREMISES THAT STAY. hok (at the first opening and at 356): every sub-protocol of the flat list
passes its own test on its parameters. hps: the flat list's places are the written list (
places_scope, in scope). What is not claimed. That the composed meaning's P5J.At.N is the numbers so
closed. At 355 and 357 the sentence says only that nothing is declared there: it holds of every N
s links: no example. Nothing on the verifier's state. Nothing on soundness.

-/
import Johnson.Desc.AtSeats.CountsAtFifty
import Johnson.IMR.SealSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace HashBuild
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain FileDescription Place)
open VerifiableInference.Desc.First (S ModelPart Numbers blockPlaces flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull)
open VerifiableInference.Desc.K1 (layOf oracles planOkOwn gpOf firstPar firstSegmentOpening parW sendAtS)
open ProofFile (Cl)

set_option maxRecDepth 1000000 in
/-- **The written list of places has no place twice.** -/
theorem places_nodup_full : (flatPlacesOf linksFull true).Nodup := by decide +kernel

/-- The segments' frames' sub-protocols declare no oracle. -/
theorem frames_tell_nothing (Z : ProofFile.Pub) (fb : Block S Unit) (h : fb ∈ P1L20.blocksOf Z) :
    fb.oracles = [] := by
  unfold P1L20.blocksOf at h
  split at h
  · obtain ⟨f, -, hf⟩ := List.mem_flatMap.1 h
    unfold ProofFile.frameBlocks at hf
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl | rfl <;> rfl
  · obtain rfl := List.mem_singleton.1 h
    rfl

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The first segment's opening.** -/
theorem at_first (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hok : ∀ b ∈ c.blocksInOrder, b.planOk = true) :
    ∃ b : Block S Cl, c.blocksInOrder[2]? = some b ∧
      b.oracles.flatten = (oracles (firstPar Bs.G₀.first (gpOf Z))).flatten ∧
      planOkOwn (firstPar Bs.G₀.first (gpOf Z)) = true := by
  obtain ⟨Lk, b, e1, e2, h⟩ := IM.k1_first_of hS hR O
  have h5 := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (by omega) 0] at h5
  have hp := hok b (List.mem_of_getElem? h5)
  rcases h with h | ⟨fb, hfb, h⟩
  · rw [IM.alone_planOk h] at hp
    have hp1 : (planOkOwn (firstPar Bs.G₀.first (gpOf Z)) &&
        K1.firstPlanOk Bs.G₀.first (gpOf Z).samples) = true := (IM.retype_planOk _ hp).1
    exact ⟨b, h5, by rw [IM.alone_oracles h]; rfl, (Bool.and_eq_true_iff.1 hp1).1⟩
  · have ep : b.planOk =
        (((firstSegmentOpening Bs.G₀.first (gpOf Z) : Block S Unit).retype : Block S Cl).planOk &&
          (fb.retype : Block S Cl).planOk) := congrArg (·.planOk) h
    have eo : b.oracles = oracles (firstPar Bs.G₀.first (gpOf Z)) ++ fb.oracles :=
      congrArg (·.oracles) h
    rw [ep] at hp
    have hp0 := (IM.retype_planOk _ (Bool.and_eq_true_iff.1 hp).1).1
    have hp1 : (planOkOwn (firstPar Bs.G₀.first (gpOf Z)) &&
        K1.firstPlanOk Bs.G₀.first (gpOf Z).samples) = true := hp0
    refine ⟨b, h5, ?_, (Bool.and_eq_true_iff.1 hp1).1⟩
    rw [eo, frames_tell_nothing Z fb hfb, List.append_nil]

/-- **The kind K13's batching.** -/
theorem at_355 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∃ b : Block S Cl, c.blocksInOrder[355]? = some b ∧ b.oracles.flatten = [] := by
  obtain ⟨-, -, ⟨b, b', hb, -, rfl, hl⟩, -⟩ := IM.back_of O
  refine ⟨_, (IM.back_numbers hS hR O).1 2 b hb, ?_⟩
  show b.oracles.flatten = []
  rw [IM.alone_oracles hl]
  exact K1.told_atM3 (K13.whereOf Z)

/-- **W's commitment with the own group and (Eval) behind it.** -/
theorem at_356 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hok : ∀ b ∈ c.blocksInOrder, b.planOk = true) :
    ∃ (b : Block S Cl) (msg : Array OnBytes.OracleNotice), c.blocksInOrder[356]? = some b ∧
      OnBytes.linMessageW Z.first.lin = some msg ∧
      b.oracles.flatten = (oracles (parW Z.first (gpOf Z) 4 msg)).flatten ∧
      planOkOwn (parW Z.first (gpOf Z) 4 msg) = true := by
  obtain ⟨-, -, -, b, b', w, hb, -, hw, rfl, hl⟩ := IM.back_of O
  unfold K13.wBlock K1.wAt at hw
  obtain ⟨msg, hm, rfl⟩ := Option.map_eq_some_iff.1 hw
  have h5 := (IM.back_numbers hS hR O).1 3 b hb
  have hp := hok _ (List.mem_of_getElem? h5)
  have hp2 : (b.planOk && b.hasNoClaimsAndNothingAfter) = true := hp
  have hp3 := (Bool.and_eq_true_iff.1 hp2).1
  rw [IM.alone_planOk hl] at hp3
  have hp4 := (IM.retype_planOk _ hp3).1
  have hp5 : (planOkOwn (parW Z.first (gpOf Z) 4 msg) &&
      (K13.rowsB (Cl := Unit) K13.atS (K13.whereOf Z)).planOk) = true := hp4
  refine ⟨_, msg, h5, hm, ?_, (Bool.and_eq_true_iff.1 hp5).1⟩
  show b.oracles.flatten = _
  rw [IM.alone_oracles hl]
  exact K1.told_atM4 (K13.whereOf Z) _

/-- **The chain's last sub-protocol.** -/
theorem at_357 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∃ b : Block S Cl, c.blocksInOrder[357]? = some b ∧ b.oracles.flatten = [] := by
  obtain ⟨b', -, rfl, hl⟩ := IM.seal_seated O
  refine ⟨_, (IM.back_numbers hS hR O).2, ?_⟩
  show c.last.oracles.flatten = []
  rw [IM.alone_oracles hl]
  exact K1.told_chainEnd (Cl := Unit) (T := S) 1 5 true (K13.inFrontOf Z) First.endAsks

variable (N : Numbers) (s : OnBytes.Params.ReqShape) (links : List ModelPart)

/-- **hear_K1's two binders**, with "no place twice" paid. -/
theorem counts_fifty (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hok : ∀ b ∈ c.blocksInOrder, b.planOk = true)
    (hps : blockPlaces c.blocksInOrder = flatPlacesOf linksFull true) :
    (∀ l < 25, ∀ d : Bool,
      (N.atBlocks s links c.blocksInOrder).treesAt (flatPlacesOf linksFull true)[no50 l d + 1]? =
        (N.atBlocks s links c.blocksInOrder).treesAt (flatPlacesOf linksFull true)[no50 l d]? +
          (layOf (par50 Z Bs.G₀ l d)).shapes.size) ∧
    ∀ l < 25, ∀ d : Bool,
      (N.atBlocks s links c.blocksInOrder).msgsAt (flatPlacesOf linksFull true)[no50 l d + 1]? =
        (N.atBlocks s links c.blocksInOrder).msgsAt (flatPlacesOf linksFull true)[no50 l d]? +
          (par50 Z Bs.G₀ l d).sent.size :=
  ⟨trees_fifty N s links hS hR O hok hps places_nodup_full,
    msgs_fifty N s links hS hR O hok hps places_nodup_full⟩

/-- **RowG's trees and msgs**, at k = 2. -/
theorem counts_first (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hok : ∀ b ∈ c.blocksInOrder, b.planOk = true)
    (hps : blockPlaces c.blocksInOrder = flatPlacesOf linksFull true) :
    (N.atBlocks s links c.blocksInOrder).treesAt (flatPlacesOf linksFull true)[2 + 1]? =
        (N.atBlocks s links c.blocksInOrder).treesAt (flatPlacesOf linksFull true)[2]? +
          (layOf (firstPar Bs.G₀.first (gpOf Z))).shapes.size ∧
      (N.atBlocks s links c.blocksInOrder).msgsAt (flatPlacesOf linksFull true)[2 + 1]? =
        (N.atBlocks s links c.blocksInOrder).msgsAt (flatPlacesOf linksFull true)[2]? +
          (firstPar Bs.G₀.first (gpOf Z)).sent.size := by
  obtain ⟨b, hb, ho, hB⟩ := at_first hS hR O hok
  exact K1.counts_at_send N s links c.blocksInOrder _ hps places_nodup_full 2 b hb _ ho hB

/-- **RowM3's trees and msgs; k13_law_top's hNt and hNm.** -/
theorem counts_355 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hps : blockPlaces c.blocksInOrder = flatPlacesOf linksFull true) :
    (N.atBlocks s links c.blocksInOrder).treesAt (flatPlacesOf linksFull true)[355 + 1]? =
        (N.atBlocks s links c.blocksInOrder).treesAt (flatPlacesOf linksFull true)[355]? ∧
      (N.atBlocks s links c.blocksInOrder).msgsAt (flatPlacesOf linksFull true)[355 + 1]? =
        (N.atBlocks s links c.blocksInOrder).msgsAt (flatPlacesOf linksFull true)[355]? := by
  obtain ⟨b, hb, ho⟩ := at_355 hS hR O
  exact K1.counts_at_quiet N s links c.blocksInOrder _ hps places_nodup_full 355 b hb ho

/-- **RowM4's trees and msgs**, at k = 356. -/
theorem counts_356 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hok : ∀ b ∈ c.blocksInOrder, b.planOk = true)
    (hps : blockPlaces c.blocksInOrder = flatPlacesOf linksFull true) :
    ∃ msg, OnBytes.linMessageW Z.first.lin = some msg ∧
      (N.atBlocks s links c.blocksInOrder).treesAt (flatPlacesOf linksFull true)[356 + 1]? =
        (N.atBlocks s links c.blocksInOrder).treesAt (flatPlacesOf linksFull true)[356]? +
          (layOf (parW Z.first (gpOf Z) 4 msg)).shapes.size ∧
      (N.atBlocks s links c.blocksInOrder).msgsAt (flatPlacesOf linksFull true)[356 + 1]? =
        (N.atBlocks s links c.blocksInOrder).msgsAt (flatPlacesOf linksFull true)[356]? +
          (parW Z.first (gpOf Z) 4 msg).sent.size := by
  obtain ⟨b, msg, hb, hm, ho, hB⟩ := at_356 hS hR O hok
  exact ⟨msg, hm, K1.counts_at_send N s links c.blocksInOrder _ hps places_nodup_full 356 b hb _ ho hB⟩

/-- **At the chain's last sub-protocol.** -/
theorem counts_357 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hps : blockPlaces c.blocksInOrder = flatPlacesOf linksFull true) :
    (N.atBlocks s links c.blocksInOrder).treesAt (flatPlacesOf linksFull true)[357 + 1]? =
        (N.atBlocks s links c.blocksInOrder).treesAt (flatPlacesOf linksFull true)[357]? ∧
      (N.atBlocks s links c.blocksInOrder).msgsAt (flatPlacesOf linksFull true)[357 + 1]? =
        (N.atBlocks s links c.blocksInOrder).msgsAt (flatPlacesOf linksFull true)[357]? := by
  obtain ⟨b, hb, ho⟩ := at_357 hS hR O
  exact K1.counts_at_quiet N s links c.blocksInOrder _ hps places_nodup_full 357 b hb ho

end

end HashBuild

#print axioms HashBuild.places_nodup_full
#print axioms HashBuild.frames_tell_nothing
#print axioms HashBuild.at_first
#print axioms HashBuild.at_356
#print axioms HashBuild.counts_fifty
#print axioms HashBuild.counts_first
#print axioms HashBuild.counts_355
#print axioms HashBuild.counts_356
#print axioms HashBuild.counts_357
