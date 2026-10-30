-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/QuietLot.lean: CUT OUT, TO THE LETTER, OF GrownQuiet.lean (a file of this project that is not in this library), so that it stands without Johnson/IMR/HandsDef.lean: quietMaker · quiet_lot.
Compiled with the whole library.
  quietMaker k      k is one of K3 · K4 · K5 · K6 · K8 · K11.
  quiet_lot         (no scope; every o) a sub-protocol (block) of the seat's lots of one of the six kinds: EVERY ACCEPTING OF ITS DECISION IS Quiet (Johnson/Goal/Meaning/RecQuiet.lean: the statement, the state's book and the count of roots stay; what the state holds of the layout and of the open link stays; where no count of rows waited none waits; a mark that stands stays).
CALLED: theStated_quiet · blockAtC_quiet · k5AtN_quiet · seatedClaims_quiet · k8Whole_quiet · headMerge11_quiet (Johnson/Goal/Meaning/RecSeated.lean). No soundness.
-/
import Johnson.IMR.K3Seat
import Johnson.IMR.K5Seat
import Johnson.IMR.K8Seat
import Johnson.Goal.Meaning.RecSeated

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open VerifiableInference.Desc (Block Place KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Whole Decides)
open Meaning.K2 (Quiet)
open ProofFile (Cl)

def quietMaker (k : KindName) : Bool :=
  k == .K3 || k == .K4 || k == .K5 || k == .K6 || k == .K8 || k == .K11

/-- **A block of the seat's lots of one of the six kinds: every yes of its decision is Quiet.** -/
theorem quiet_lot {Z : ProofFile.Pub} {G : ProofFile.Ground} {L : ProofFile.Lot} (hL : L ∈ ProofFile.onlineFirstChainBlockTables Z)
    {b' : Block S Cl} (hb : b' ∈ L.blocks G) (hk : quietMaker b'.place.kind = true) :
    Decides Quiet b' := by
  have hc : ∀ {L' : ProofFile.Lot}, L = L' → (L'.own G = []) → b' ∈ L'.hearC G := by
    rintro L' rfl ho
    rcases blocks_mem hb with ⟨x, hx, -⟩ | h
    · rw [ho] at hx
      cases hx
    · exact h
  cases hkk : b'.place.kind <;> rw [hkk] at hk <;> (try exact absurd hk (by decide))
  · -- K3
    have h := hc (lot_of_kind hL hb (by rw [hkk]; rfl)) rfl
    exact (Meaning.K2.theStated_quiet _ _ _ _ _ _ (k3Hear_mem h)).1
  · -- K4
    have h := hc (lot_of_kind hL hb (by rw [hkk]; rfl)) rfl
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 h
    exact (Meaning.K2.blockAtC_quiet { x.2 with k3Runs := true }).1
  · -- K5
    have h := hc (lot_of_kind hL hb (by rw [hkk]; rfl)) rfl
    obtain ⟨l, Xl, b₀, -, -, e, rfl⟩ := k5OwnN_mem h
    exact (Meaning.K2.k5AtN_quiet _ _ _ _ e).1
  · -- K6
    have h := hc (lot_of_kind hL hb (by rw [hkk]; rfl)) rfl
    have h' : b' ∈ ((P4.headBefore Z G).bind fun ms =>
        VerifiableInference.Desc.Kinds.Head.seatedClaims G.W (G.built.size - 1) ms).toList := h
    rw [Option.mem_toList] at h'
    obtain ⟨ms, -, hsc⟩ := Option.bind_eq_some_iff.1 h'
    exact (Meaning.K2.seatedClaims_quiet hsc).1
  · -- K8
    have h := hc (lot_of_kind hL hb (by rw [hkk]; rfl)) rfl
    obtain ⟨l, Xl, -, rfl⟩ := k8Whole_mem h
    exact (Meaning.K2.k8Whole_quiet _).1
  · -- K11
    have h := hc (lot_of_kind hL hb (by rw [hkk]; rfl)) rfl
    obtain rfl := List.mem_singleton.1 h
    exact (Meaning.K2.headMerge11_quiet _).1

end IM

#print axioms IM.quiet_lot
