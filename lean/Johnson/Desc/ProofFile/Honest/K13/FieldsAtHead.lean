-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K13/FieldsAtHead.lean: kind K13, the members' batching: the hypotheses
of `k13_good_of_due` (Fields.lean of this folder) proved at the first chain's own flat list and at
the book of coins that the frame's maker returns, under the library's hypothesis h (`P5J.AtMgA`,
Johnson/P5J/MgAtAll.lean). Statements with their proofs. At the full size and at the hash
`OnBytes.secondHashFunction` alone.

  `m3_member_there`   the first chain's flat list has a sub-protocol number 355
  `k13_side_at`   `Side.seated` returns a side at the kind's place, and its sub-protocol is number
     355: it is at the kind's place (`m3_member_place`, FromThreadAt.lean of this folder), no two
     sub-protocols of the list are at one place (`nodupAtFull`,
     Johnson/Desc/K11/Exchange/NodupAtFull.lean), so the first one found there is that one
     (`find_at`, Honest/Thread/Rows.lean)
  `k13_good_at_head`   the term of `Good`, under h, at the book that `bookWhole`
     (Honest/BookWhole.lean) returns at the head's description. That sub-protocol has the kind's
     rounds and declares no oracle message (`m3_member_fields`, FromThreadAt.lean); the test on the
     shape accepts in the goals' scope (`shape_in_scope`, ExactShape.lean of this folder); what
     `bookWhole` returns passes the book's tests (`bookWhole_word`, Honest/AtPureLaw.lean) and has
     no coin for a sub-protocol without a round "SEND seed" or "FOLD epsilon" (`bookWhole_bare_at`,
     Honest/Small/BareOfBook.lean)

Limits.
  * That h can be met is not shown here: it holds at all public files in the goals' scope that are
    read and pass the library's test `protocolDataWellFormed` (`head_of_live`, Johnson/P5J/HeadOfLive.lean). That
    `bookWhole` returns under h is not shown here.
  * The lists of sendings and the list of merges at which `bookWhole` is called are free: the
    statement holds at whatever it returns. At A := False `Good` reads the book in `fresh` alone:
    that the book lends part 1 its block is not said here (`k13_lendRow_at_head`,
    AtFullSide/K13/LendRowAtHead.lean).
  * The term shows `fits`, `exact` and `fresh` alone: see the heads of Fields.lean and Exact.lean.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.K13.Fields
import Johnson.Desc.ProofFile.Honest.K13.FromThreadAt
import Johnson.Desc.ProofFile.Honest.K13.ExactShape
import Johnson.Desc.ProofFile.Honest.Thread.Rows
import Johnson.Desc.K11.Exchange.NodupAtFull
import Johnson.RunOne.Sound.KeyListsAtFK
import Johnson.Desc.ProofFile.Honest.Small.BareOfBook
import Johnson.Desc.ProofFile.Honest.AtPureLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (blockPlaces)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open Johnson.Desc.First.ForkMerge.Exchange (nodupAtFull)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {W₀ Rc Tr X Pb : Type}

include h in
/-- The first chain's flat list has a sub-protocol number 355. -/
theorem m3_member_there : ∃ blk, cF.blocksInOrder[355]? = some blk := by
  have e := P5J.At.places_paid h.scope h.reads h.laid
  cases hb : cF.blocksInOrder[355]? with
  | some blk => exact ⟨blk, rfl⟩
  | none =>
    have q : (blockPlaces cF.blocksInOrder)[355]? = none := by
      unfold blockPlaces
      rw [List.getElem?_map, hb]
      rfl
    rw [e, m3_place] at q
    cases q

/-- **`Side.seated` returns a side at the kind's place, and its sub-protocol is number 355 of the
first chain's flat list.** -/
theorem k13_side_at (weights : W₀ → Weights) (pile : PileOf ProofFile.Inst) (fs : List (Fall TS)) :
    ∃ σ : Side TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X Pb,
      Side.seated cF.blocksInOrder (k13Place h.𝔇.P13) (k13Pairs weights pile h.𝔇.P13) fs = some σ ∧
        cF.blocksInOrder[355]? = some σ.block := by
  obtain ⟨blk, hb⟩ := m3_member_there h
  have hf := find_at cF.blocksInOrder 355 blk (nodupAtFull _ _ _ _ _ _ _ h) hb
  have ea : k13Place h.𝔇.P13 = blk.place := (m3_member_place h hb).symm
  refine ⟨⟨blk, k13Pairs weights pile h.𝔇.P13, fallOf fs (k13Place h.𝔇.P13)⟩, ?_, hb⟩
  unfold Side.seated
  rw [ea, hf]
  rfl

/-- **`fits`, `exact` and `fresh` as one term of `Good`, at the first chain's own flat list and the
book that `bookWhole` returns at the head's description, under h alone.** A and B are False: `plays`
and `acc` show nothing. -/
theorem k13_good_at_head {Bk : ProverCoinCounts} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    (hW : bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) p0 p1 p2 M = .ok Bk)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (weights : W₀ → Weights) (pile : PileOf ProofFile.Inst)
    (φ : Face (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Pb) {fs : List (Fall TS)}
    {σ : Side TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X Pb}
    (hσ : Side.seated cF.blocksInOrder (k13Place h.𝔇.P13) (k13Pairs weights pile h.𝔇.P13) fs = some σ)
    (ord : List Place) (chain firstTree : Nat) :
    Good pre φ σ Bk ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False) k13On
      k13Bud := by
  obtain ⟨σ', h1, h2⟩ := k13_side_at (Rc := Rc) (Tr := Tr) (X := X) (Pb := Pb) h weights pile fs
  obtain rfl : σ = σ' := Option.some.inj (hσ.symm.trans h1)
  have hf := m3_member_fields h h2
  have hp := Johnson.RunOne.Sound.placesOk_of_planOk _ h.laid.planOk
  have hb : σ.block ∈ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder := List.mem_of_getElem? h2
  refine k13_good_of_due (F := P5J.F0T OnBytes.secondHashFunction Zp Np cF) pre weights pile h.𝔇.P13
    (shape_in_scope h.scope h.laid.pub) φ hσ hf.1 hf.2 (bookWhole_word hW) hp ?_ (fun j _ => ?_)
    ord chain firstTree
  · rw [← sideSeated_place hσ]
    exact List.mem_map.2 ⟨σ.block, hb, rfl⟩
  · rw [← sideSeated_place hσ]
    exact (bookWhole_bare_at hW hp hb (k13_no_send_seed hf.1) (k13_no_fold_epsilon hf.1) j).1

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.m3_member_there
#print axioms ProofFile.Honest.K13.k13_side_at
#print axioms ProofFile.Honest.K13.k13_good_at_head
