-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/KeyFkAtD.lean (OVER THE ONE STORED BUILD COMMON TO THIS PROJECT's FILES, and the form of the key file): THE KEY FILE's FRAME's MAKER's RING OVER THE MAKER WITHOUT BUILD-TIME CODE.
`Key.madeAt` | `Key.descAt` (Johnson/Desc/Key/Road.lean) are a key file's description from what the verifier program reads of the public files, the layout file and the digest.
Main names.
  `fkAtD Z cfg`: `publicOf Z.pol Z.KL (some Z.lay) >>= fun X₀ => descAt X₀ Z.lay cfg`.
  `fkAtD_made`: WHAT THE MAKER READ AT Z STAYS IN HAND: `fkAtD Z cfg = .ok F` gives X₀ with `publicOf … = .ok X₀`, the record m with `madeAt X₀ Z.lay cfg = .ok m`, the source X, the numbers N, the places P read off m, and F = `Key.descriptionFromSource X N P`.
  `FkInScopeD` | `FkAtZD`: the sets of descriptions that the frame's core reads, as before.
THE CORE TURNS NOWHERE: it reads a set of descriptions, a letter.
Limits. Definitions and one inversion. Nothing on soundness.

-/
import Johnson.Desc.Key.Road
import OnBytes.K.Served
import Ladder

set_option autoImplicit false

namespace LPFD
open VerifiableInference.Desc (FileDescription)
open VerifiableInference.Desc.Key (Xi Source LaterPlaces descriptionFromSource sourceOf rangesNumbers laterPlaces descriptionFromPlan madeAt descAt)

/-- **The key file's description at three public files and a digest.** -/
def fkAtD (Z : OnBytes.K.Pub) (cfg : ByteArray) : Except String (FileDescription Xi) :=
  (OnBytes.Model.Verify.publicOf Z.pol Z.KL (some Z.lay)).bind fun X₀ => descAt X₀ Z.lay cfg

/-- **What the maker read at Z stays in hand.** -/
theorem fkAtD_made (Z : OnBytes.K.Pub) (cfg : ByteArray) (F : FileDescription Xi) (h : fkAtD Z cfg = .ok F) :
    ∃ (X₀ : OnBytes.Model.Verify.Public) (m : Johnson.G.OfPlan.Made) (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces),
      OnBytes.Model.Verify.publicOf Z.pol Z.KL (some Z.lay) = .ok X₀ ∧ madeAt X₀ Z.lay cfg = .ok m ∧
        sourceOf m = .ok X ∧ rangesNumbers m = .ok N ∧ laterPlaces m = .ok P ∧ F = descriptionFromSource X N P := by
  unfold fkAtD at h
  cases hX : OnBytes.Model.Verify.publicOf Z.pol Z.KL (some Z.lay) with
  | error e =>
    rw [hX] at h
    cases h
  | ok X₀ =>
    rw [hX] at h
    have h' : (madeAt X₀ Z.lay cfg).bind (fun m => descriptionFromPlan m) = .ok F := h
    cases hm : madeAt X₀ Z.lay cfg with
    | error e =>
      rw [hm] at h'
      cases h'
    | ok m =>
      rw [hm] at h'
      have h'' : descriptionFromPlan m = .ok F := h'
      unfold descriptionFromPlan at h''
      split at h''
      · rename_i X N P hS hN hP
        injection h'' with e
        exact ⟨X₀, m, X, N, P, rfl, hm, hS, hN, hP, e.symm⟩
      all_goals cases h''

/-- **The key file's descriptions in the goals' scope.** -/
def FkInScopeD (F : FileDescription Xi) : Prop :=
  ∃ (Z : OnBytes.K.Pub) (cfg : ByteArray), VerifierAndGoals.InScope ⟨Z.pol, Z.lay, Z.KL⟩ = true ∧ cfg.size = 32 ∧ fkAtD Z cfg = .ok F

/-- The key file's descriptions at one Z. -/
def FkAtZD (Z : OnBytes.K.Pub) (F : FileDescription Xi) : Prop := ∃ cfg : ByteArray, cfg.size = 32 ∧ fkAtD Z cfg = .ok F

theorem fkInScopeD_of_atZ (Z : OnBytes.K.Pub) (hs : VerifierAndGoals.InScope ⟨Z.pol, Z.lay, Z.KL⟩ = true) (F : FileDescription Xi) (h : FkAtZD Z F) : FkInScopeD F :=
  let ⟨cfg, hc, hF⟩ := h
  ⟨Z, cfg, hs, hc, hF⟩

end LPFD

#print axioms LPFD.fkAtD
#print axioms LPFD.fkAtD_made
#print axioms LPFD.fkInScopeD_of_atZ
