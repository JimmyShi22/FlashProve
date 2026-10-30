--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/OuterLot.lean: AT THE PROOF FILE's SEAT: a sub-protocol of the seat's
lots of one of the six kinds K3, K4, K5, K6, K8, K11: EVERY ACCEPTING OF ITS DECISION IS Outer
(Johnson/Goal/Meaning/OuterSeated.lean): what goes on to the later chains, the state of the calls
over the links and the request's public words are as they were. One theorem, proved: at every o; no
premise on scope.



  outer_lot   beside quiet_lot (Johnson/IMR/QuietLot.lean), whose case split it follows arm by arm.
  link_lot   the like for SameLink (Johnson/Goal/Meaning/LinkSeated.lean): the open link's context
    is as it was, whole.

OBJECT: the lots' own sub-protocols of the six kinds. USER: none in Lean yet; meant: the ride of the
public items across our 101 numbers. LETTERS: Z, G, L: free.

What is not claimed. Anything on the seated form of these sub-protocols. No soundness.
-/
import Johnson.IMR.QuietLot
import Johnson.Goal.Meaning.OuterSeated
import Johnson.Goal.Meaning.LinkSeated

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open VerifiableInference.Desc (Block Place KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Whole Decides)
open Meaning.Out (Outer)
open Meaning.Lnk (SameLink)
open ProofFile (Cl)

/-- **A sub-protocol of the seat's lots of one of the six kinds: every accepting of its decision is
Outer.** -/
theorem outer_lot {Z : ProofFile.Pub} {G : ProofFile.Ground} {L : ProofFile.Lot} (hL : L ∈ ProofFile.onlineFirstChainBlockTables Z)
    {b' : Block S Cl} (hb : b' ∈ L.blocks G) (hk : quietMaker b'.place.kind = true) :
    Decides Outer b' := by
  have hc : ∀ {L' : ProofFile.Lot}, L = L' → (L'.own G = []) → b' ∈ L'.hearC G := by
    rintro L' rfl ho
    rcases blocks_mem hb with ⟨x, hx, -⟩ | h
    · rw [ho] at hx
      cases hx
    · exact h
  cases hkk : b'.place.kind <;> rw [hkk] at hk <;> (try exact absurd hk (by decide))
  · -- K3
    have h := hc (lot_of_kind hL hb (by rw [hkk]; rfl)) rfl
    exact (Meaning.Out.theStated_outer _ _ _ _ _ _ (k3Hear_mem h)).1
  · -- K4
    have h := hc (lot_of_kind hL hb (by rw [hkk]; rfl)) rfl
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 h
    exact (Meaning.Out.blockAtC_outer { x.2 with k3Runs := true }).1
  · -- K5
    have h := hc (lot_of_kind hL hb (by rw [hkk]; rfl)) rfl
    obtain ⟨l, Xl, b₀, -, -, e, rfl⟩ := k5OwnN_mem h
    exact (Meaning.Out.k5AtN_outer _ _ _ _ e).1
  · -- K6
    have h := hc (lot_of_kind hL hb (by rw [hkk]; rfl)) rfl
    have h' : b' ∈ ((P4.headBefore Z G).bind fun ms =>
        VerifiableInference.Desc.Kinds.Head.seatedClaims G.W (G.built.size - 1) ms).toList := h
    rw [Option.mem_toList] at h'
    obtain ⟨ms, -, hsc⟩ := Option.bind_eq_some_iff.1 h'
    exact (Meaning.Out.seatedClaims_outer hsc).1
  · -- K8
    have h := hc (lot_of_kind hL hb (by rw [hkk]; rfl)) rfl
    obtain ⟨l, Xl, -, rfl⟩ := k8Whole_mem h
    exact (Meaning.Out.k8Whole_outer _).1
  · -- K11
    have h := hc (lot_of_kind hL hb (by rw [hkk]; rfl)) rfl
    obtain rfl := List.mem_singleton.1 h
    exact (Meaning.Out.headMerge11_outer _).1

/-- **A sub-protocol of the seat's lots of one of the six kinds: every accepting of its decision
leaves the open link's context.** -/
theorem link_lot {Z : ProofFile.Pub} {G : ProofFile.Ground} {L : ProofFile.Lot} (hL : L ∈ ProofFile.onlineFirstChainBlockTables Z)
    {b' : Block S Cl} (hb : b' ∈ L.blocks G) (hk : quietMaker b'.place.kind = true) :
    Decides SameLink b' := by
  have hc : ∀ {L' : ProofFile.Lot}, L = L' → (L'.own G = []) → b' ∈ L'.hearC G := by
    rintro L' rfl ho
    rcases blocks_mem hb with ⟨x, hx, -⟩ | h
    · rw [ho] at hx
      cases hx
    · exact h
  cases hkk : b'.place.kind <;> rw [hkk] at hk <;> (try exact absurd hk (by decide))
  · -- K3
    have h := hc (lot_of_kind hL hb (by rw [hkk]; rfl)) rfl
    exact (Meaning.Lnk.theStated_lk _ _ _ _ _ _ (k3Hear_mem h)).1
  · -- K4
    have h := hc (lot_of_kind hL hb (by rw [hkk]; rfl)) rfl
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 h
    exact (Meaning.Lnk.blockAtC_lk { x.2 with k3Runs := true }).1
  · -- K5
    have h := hc (lot_of_kind hL hb (by rw [hkk]; rfl)) rfl
    obtain ⟨l, Xl, b₀, -, -, e, rfl⟩ := k5OwnN_mem h
    exact (Meaning.Lnk.k5AtN_lk _ _ _ _ e).1
  · -- K6
    have h := hc (lot_of_kind hL hb (by rw [hkk]; rfl)) rfl
    have h' : b' ∈ ((P4.headBefore Z G).bind fun ms =>
        VerifiableInference.Desc.Kinds.Head.seatedClaims G.W (G.built.size - 1) ms).toList := h
    rw [Option.mem_toList] at h'
    obtain ⟨ms, -, hsc⟩ := Option.bind_eq_some_iff.1 h'
    exact (Meaning.Lnk.seatedClaims_lk hsc).1
  · -- K8
    have h := hc (lot_of_kind hL hb (by rw [hkk]; rfl)) rfl
    obtain ⟨l, Xl, -, rfl⟩ := k8Whole_mem h
    exact (Meaning.Lnk.k8Whole_lk _).1
  · -- K11
    have h := hc (lot_of_kind hL hb (by rw [hkk]; rfl)) rfl
    obtain rfl := List.mem_singleton.1 h
    exact (Meaning.Lnk.headMerge11_lk _).1

end IM

#print axioms IM.outer_lot
#print axioms IM.link_lot
