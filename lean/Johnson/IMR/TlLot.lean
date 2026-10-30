--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
TlLot.lean: AT THE PROOF FILE's SEAT: a sub-protocol of the seat's lots of the
kind K5, K6 or K11, or of the kind K3 at a piece below 7 (the lookup on the calls): EVERY ACCEPTING
OF ITS DECISION LEAVES THE OPEN SEGMENT's PARAMETERS OF THE APPROXIMATE RANGE PROOF (SameTl,
Johnson/Goal/Meaning/TlSeated.lean). One theorem, proved: at every o; no premise on scope.



  tlMaker p   the place's kind is K5, K6 or K11, or K3 with p.piece < 7.
  tl_lot   beside quiet_lot (Johnson/IMR/QuietLot.lean), whose case split it follows.

OBJECT: the lots' own sub-protocols at such places. USER: none in Lean yet. LETTERS: Z, G, L: free.

What is not claimed. K3 at the digits' lookup and K8 (they write that structure). K4. No soundness.

-/
import Johnson.IMR.QuietLot
import Johnson.Goal.Meaning.TlSeated

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open VerifiableInference.Desc (Block Place KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Whole Decides)
open Meaning.Tl (SameTl)
open ProofFile (Cl)

def tlMaker (p : Place) : Bool :=
  (p.kind == .K3 && decide (p.piece < 7)) || p.kind == .K5 || p.kind == .K6 || p.kind == .K11

/-- **A sub-protocol of the seat's lots at such a place: every accepting of its decision leaves
them.** -/
theorem tl_lot {Z : ProofFile.Pub} {G : ProofFile.Ground} {L : ProofFile.Lot} (hL : L ∈ ProofFile.onlineFirstChainBlockTables Z)
    {b' : Block S Cl} (hb : b' ∈ L.blocks G) (hk : tlMaker b'.place = true) :
    Decides SameTl b' := by
  have hc : ∀ {L' : ProofFile.Lot}, L = L' → (L'.own G = []) → b' ∈ L'.hearC G := by
    rintro L' rfl ho
    rcases blocks_mem hb with ⟨x, hx, -⟩ | h
    · rw [ho] at hx
      cases hx
    · exact h
  unfold tlMaker at hk
  cases hkk : b'.place.kind <;> rw [hkk] at hk <;> (try (exfalso; simp at hk; done))
  · -- K3
    have h7 : b'.place.piece < 7 := by
      simp at hk
      exact hk
    have h := hc (lot_of_kind hL hb (by rw [hkk]; rfl)) rfl
    exact (Meaning.Tl.theStated_tl _ _ _ _ _ _ h7 (k3Hear_mem h)).1
  · -- K5
    have h := hc (lot_of_kind hL hb (by rw [hkk]; rfl)) rfl
    obtain ⟨l, Xl, b₀, -, -, e, rfl⟩ := k5OwnN_mem h
    exact (Meaning.Tl.k5AtN_tl _ _ _ _ e).1
  · -- K6
    have h := hc (lot_of_kind hL hb (by rw [hkk]; rfl)) rfl
    have h' : b' ∈ ((P4.headBefore Z G).bind fun ms =>
        VerifiableInference.Desc.Kinds.Head.seatedClaims G.W (G.built.size - 1) ms).toList := h
    rw [Option.mem_toList] at h'
    obtain ⟨ms, -, hsc⟩ := Option.bind_eq_some_iff.1 h'
    exact (Meaning.Tl.seatedClaims_tl hsc).1
  · -- K11
    have h := hc (lot_of_kind hL hb (by rw [hkk]; rfl)) rfl
    obtain rfl := List.mem_singleton.1 h
    exact (Meaning.Tl.headMerge11_tl _).1

end IM

#print axioms IM.tl_lot
