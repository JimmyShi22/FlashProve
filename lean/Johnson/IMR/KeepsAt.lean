--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
KeepsAt.lean: AT THE PROOF FILE's SEAT: EVERY ACCEPTING STEP OF A SUB-PROTOCOL OF
ONE OF THE SIX KINDS K3, K4, K5, K6, K8, K11 LEAVES THE READERS keepsAt OF ITS PLACE:
the second premise of more_of_owed. Theorems, proved: at every o; no premise on
scope.



  k4_tl   each of the lots' own sub-protocols of the kind K4: every accepting decision leaves S.tl?:
    one call of its own authors' k4_lot_whole (Johnson/Road/K4/K4LotRest.lean), at the field
    Rest.tl.
  sameOn_lot   at the lot's own sub-protocol b': from quiet_lot, outer_lot,
    link_lot, tl_lot and, at the kind K4, k4_tl.
  sameOn_yes   at whatever sub-protocol b stands under b' (b.UnderR b': the seated form): for every
    accepting step.

OBJECT: the lots' own sub-protocols of the six kinds, and their seated forms. USER: none in Lean
yet; meant: more_of_owed's hK. LETTERS: Z, G, L, ft: free.

What is not claimed. Anything on the public items. No soundness.
-/
import Johnson.IMR.MadeOwed
import Johnson.IMR.OuterLot
import Johnson.IMR.TlLot
import Johnson.Road.K4.K4LotRest

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open VerifiableInference.Desc (Block Place KindName)
open VerifiableInference.Desc.First (S PubData SameOn)
open VerifiableInference.Desc.Keeps (Decides)
open Meaning.Ride (sameOn_keepsQ sameOn_keepsT)
open Meaning.Tl (SameTl)
open ProofFile (Cl)

/-- **K4's twelve leave the approximate range proof's parameters.** -/
theorem k4_tl {Z : ProofFile.Pub} {G : ProofFile.Ground} {b' : Block S Cl}
    (lot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G) (hk : b'.place.kind = .K4) :
    Decides SameTl b' :=
  fun s rs gs s' hd => ((OnBytes.Road.K4.k4_lot_whole lot hk).1 s rs gs s' hd).tl

/-- **At the lot's own sub-protocol.** -/
theorem sameOn_lot (D : PubData) {Z : ProofFile.Pub} {G : ProofFile.Ground} {L : ProofFile.Lot}
    (hL : L ∈ ProofFile.onlineFirstChainBlockTables Z)
    {b' : Block S Cl} (hb : b' ∈ L.blocks G) (hq : quietMaker b'.place.kind = true)
    {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hd : b'.decide s rs gs = .ok s') :
    SameOn D (keepsAt b'.place) s s' := by
  have q := quiet_lot hL hb hq s rs gs s' hd
  have o := outer_lot hL hb hq s rs gs s' hd
  have l := link_lot hL hb hq s rs gs s' hd
  unfold keepsAt
  split
  · exact sameOn_keepsQ D q o l
  · rename_i hn
    refine sameOn_keepsT D q o l ?_
    by_cases h : b'.place.kind = .K4
    · exact k4_tl ⟨L, hL, hb⟩ h s rs gs s' hd
    · refine tl_lot hL hb ?_ s rs gs s' hd
      unfold tlMaker
      unfold quietMaker at hq
      revert hn hq h
      cases b'.place.kind <;> simp

/-- **At the seated form: every accepting step.** -/
theorem sameOn_yes (D : PubData) {Z : ProofFile.Pub} {G : ProofFile.Ground} {L : ProofFile.Lot}
    (hL : L ∈ ProofFile.onlineFirstChainBlockTables Z)
    {b b' : Block S Cl} (hb : b' ∈ L.blocks G) (hq : quietMaker b'.place.kind = true)
    (hU : b.UnderR b') {ft : Nat} {s s' : S}
    (hy : Yes ft b s s') : SameOn D (keepsAt b'.place) s s' := by
  obtain ⟨rs, cols, n, e⟩ := hy.under hU
  obtain ⟨-, -, -, hd⟩ := VerifiableInference.Desc.step_inv ft b' s s' rs cols n e
  exact sameOn_lot D hL hb hq hd

end IM

#print axioms IM.k4_tl
#print axioms IM.sameOn_lot
#print axioms IM.sameOn_yes
