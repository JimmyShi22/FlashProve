-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/CarryThrough.lean: the proofs of the five statements of
Johnson/FrontRoad/CarryThroughSpec.lean: the implication Spec.sessionStops_of_cellsOwn with four of
its five premises on rows and prover carried back to a prover at the index type Cm.Idx.
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What this file has (namespace OnBytes.FrontRoad).
  The steps   forget_bare, forget_bareRows: a row made by bareRow, and a list of such rows,
      forgotten to halves, is the half, and the list of halves, that it was made of.
  The five proofs   pins_of_elder, frame_free_of_elder, sessionStops_of_elder, bare_forgets,
      bare_rows_are_images.

How it fits. pins_of_elder: halves_through (Johnson/FrontRoad/ProverThrough.lean) carries
PinHalvesAt to the images; pin_first_iff, pin_iff and public_second
(Johnson/FrontRoad/PinPublic.lean) make the two pins of it. frame_free_of_elder: the halves keep the
rows' places (first_provG, Johnson/FrontRoad/SessionHid.lean), and the images keep the halves'.
sessionStops_of_elder is sessionStops_of_cellsOwn (Johnson/FrontRoad/CellsOwnAt.lean) at these, with
cellsOwn_through. All limits: the head of Johnson/FrontRoad/CarryThroughSpec.lean. Not one of the
release's goal statements.
-/
import Johnson.FrontRoad.CarryThroughSpec
import Johnson.FrontRoad.ProverThrough

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open AtPublicFiles.AtFiles AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed
open OnBytes (TableKey)
open OnBytes.Flat (RecFull)
open OnBytes.Params (Lines missedInTheChecks clog2)
open OnBytes.Maker (WholeD)
open OnBytes.Model.Verify (publicOf)
open OnBytes.HonestTrace (Tr cellsC matsOf cellsSmall_cellOf ServesAt theTrace meetsAll_theTrace
  servesAt_iff_in_scope TraceHinge)
open Inst.Model (Instance ppref)
open VerifiableInference.Desc (Block Place KindName)
open VerifiableInference.Desc.First.K8 (Par)
open ProofFile.Honest (Prover ProverCoinCounts Sides Ready Coins ready Placed Local Common Cells Lettered)
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (protocolDataWellFormed)
open P5J

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off within this namespace,
so that no statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

/- Among all that this file imports, the search for this instance runs out of its budget. It is a
proposition, so whichever proof is found, the statements below are the same. -/
local instance (priority := high) nonemptyPadZ_carryThrough : Nonempty PadZ :=
  pads_nonempty OnBytes.Slice.frS 402653181

/- The same of this one. -/
local instance (priority := high) nonemptyOfInhabited_carryThrough {α : Type} [Inhabited α] :
    Nonempty α := ⟨default⟩

/-! ## The steps -/

section
variable {Bk : ProverCoinCounts} {S Cl V W Y Pb : Type}

/-- A row made by bareRow, forgotten to a half, is the half that it was made of. -/
theorem forget_bare (g : Placed V W Y) :
    (⟨(bareRow g : Lettered Bk S Cl V W Y Pb).place,
      (bareRow g : Lettered Bk S Cl V W Y Pb).row.map (·.1)⟩ : Placed V W Y) = g := by
  cases g with
  | mk a ps =>
    show (⟨a, (ps.map fun p => (p, (ProofFile.Honest.quietSim ⟨a, 0⟩ 1 : ProofFile.Honest.Sim Pb))).map
      (·.1)⟩ : Placed V W Y) = ⟨a, ps⟩
    rw [List.map_map]
    congr 1
    exact List.map_id ps

/-- The same of a list of halves. -/
theorem forget_bareRows : ∀ hs : List (Placed V W Y),
    (hs.map fun g => (bareRow g : Lettered Bk S Cl V W Y Pb)).map
      (fun L => (⟨L.place, L.row.map (·.1)⟩ : Placed V W Y)) = hs
  | [] => rfl
  | g :: hs => by
    rw [List.map_cons, List.map_cons, forget_bareRows hs, forget_bare]

end

/-! ## The five -/

theorem pins_of_elder : Spec.pins_of_elder := by
  intro Z Zp Np cF Rc' Tr' X₀ Xh B G H' dflt rd d scope pp hr D r L hG₁ hG₃ cells' p₁ p₃
  refine ⟨?_, ?_⟩
  · rw [hG₁]
    exact (pin_first_iff Z Zp Np cF scope hr L cells' _).2
      (halves_through _ dflt rd _ cells' _ _ p₁)
  · rw [hG₃]
    exact (pin_iff _ cells' _ _).2
      ⟨public_second Zp Np cF, halves_through _ dflt rd _ cells' _ _ p₃⟩

theorem frame_free_of_elder : Spec.frame_free_of_elder := by
  intro Z Zp Np cF Rc' Tr' X₀ Xh B G H' dflt rd d hG₁ hn' L hL
  have hm : (⟨L.place, L.row.map (·.1)⟩ : Placed _ _ Xh) ∈
      (provG Z Zp Np cF B G (imageAt dflt rd d H')).first := by
    rw [first_provG]
    exact List.mem_map.2 ⟨L, hL, rfl⟩
  rw [hG₁] at hm
  obtain ⟨g, hg, e⟩ := List.mem_map.1 hm
  have e2 : g.place = L.place := congrArg (fun q : Placed _ _ Xh => q.place) e
  rw [← e2]
  exact hn' g hg

theorem sessionStops_of_elder : Spec.sessionStops_of_elder := by
  intro Z Zp Np cF R₂ R₃ _ _ _ _ run₂ run₃ Rc' Tr' X₀ Xh B G H' dflt rd d scope pp hr live D r L
    hG₁ hG₃ w₀ rc x₀ k₀ R hR hn' Yes cells' p₁ p₃ hT ok Gs
  obtain ⟨h₁, h₃⟩ := pins_of_elder Z Zp Np cF B G H' dflt rd d scope hr L hG₁ hG₃ cells' p₁ p₃
  exact sessionStops_of_cellsOwn Z Zp Np cF run₂ run₃ B G (imageAt dflt rd d H') scope hr live L hR
    (frame_free_of_elder Z Zp Np cF B G H' dflt rd d hG₁ hn') Yes (matsOf Zp.p.X) cells' h₁ h₃
    (cellsOwn_through Z Zp Np cF run₂ run₃ B G H' Yes dflt rd d cells' hT) ok Gs

theorem bare_forgets : Spec.bare_forgets := by
  intro Xi W₀ Rc Ky Tr' X₀ X F Bk H H₁
  exact ⟨forget_bareRows H.first, forget_bareRows H.shared, forget_bareRows H.second⟩

theorem bare_rows_are_images : Spec.bare_rows_are_images := by
  intro Z Zp Np cF Rc' Tr' X₀ Xh B H' dflt rd d
  refine ⟨?_, ?_⟩
  · rw [first_provG]
    exact forget_bareRows _
  · rw [second_provG]
    exact forget_bareRows _

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.nonemptyPadZ_carryThrough
#print axioms OnBytes.FrontRoad.nonemptyOfInhabited_carryThrough
#print axioms OnBytes.FrontRoad.forget_bare
#print axioms OnBytes.FrontRoad.forget_bareRows
#print axioms OnBytes.FrontRoad.pins_of_elder
#print axioms OnBytes.FrontRoad.frame_free_of_elder
#print axioms OnBytes.FrontRoad.sessionStops_of_elder
#print axioms OnBytes.FrontRoad.bare_forgets
#print axioms OnBytes.FrontRoad.bare_rows_are_images
