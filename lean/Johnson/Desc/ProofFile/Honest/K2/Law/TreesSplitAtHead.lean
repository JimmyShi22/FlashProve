-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/TreesSplitAtHead.lean: NUMBERS OF A PUBLIC PLAN: UNDER THE
LIBRARY's HEAD AND THE OPENING THE MEMBERS OF THE FIRST CHAIN's FLAT LIST THAT DECLARE A TREE ARE
78: THE SHARED SENDING's 52, THE SWITCHES' 25 AND ONE MORE, NUMBER 354. So the field trees of
`JoinFit` (Honest/Thread/JoinFit.lean, of other authors) follows from three limbs, one for each
sender; and the switches' limb holds wherever the list holds the kind's share. Definitions with
code; closed facts by Lean's kernel, one of them a control; statements with their proofs.

  `treeMembers`     the numbers of the blocks that tell a tree, off what the blocks tell
  `sharedNos`       the shared sending's 52 numbers: 2, each link's two, 356
  `treeMembersW` BY LEAN's KERNEL, at the written tellings and places: 78 members tell a tree; each
                    is one of `sharedNos`, or a switch's (`switchBorders placesW`,
                    SwitchBorders.lean of this folder), or 354. A CONTROL: without 354 the test says
                    no
  `mem_treeMembers`   a block that tells a tree has its number among `treeMembers`
  `trees_of_three`  THE SPLIT: h1 (the 52 stand in a list nos) · h2 (each switch's member's number
                    stands in a list tn) · h3 (354 stands in tn) ⊢ the field trees at nos ++ tn
  `share_trees_limb` h2 where a record holds the kind's share (`ShareIn`, Honest/K2/JoinShare.lean)

Limits. NUMBERS ALONE: no lot, coin, input or run occurs. h1 AND h3 ARE PREMISES: the shared
sending's and the third sender's to pay: shown here at no list. Whose member 354 is this file does
not say. The head and the opening are premises. The full size; the format's second hash function. Nothing on
any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.FlatSeatsAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.SwitchBorders
import Johnson.Desc.ProofFile.Honest.K2.JoinShare

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain Oracle)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2Ties (toldFull toldOf_of_cut)
open VerifiableInference.Desc.K2.Honest.Returns (tests_at_head)
open ProofFile.Honest.FirstThread (TreeLot Others)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

/-- The numbers of the blocks that tell a tree. -/
def treeMembers (told : List (List Oracle)) : List Nat :=
  (told.zipIdx.filter fun x => !x.1.isEmpty).map (·.2)

/-- The shared sending's 52 numbers. -/
def sharedNos : List Nat :=
  2 :: (List.range 25).flatMap (fun l =>
    [VerifiableInference.Desc.K1.noL l false, VerifiableInference.Desc.K1.noL l true]) ++ [356]

set_option maxRecDepth 1000000 in
/-- **At the written tellings and places**; a control that says no. -/
theorem treeMembersW :
    (treeMembers toldFull).length = 78 ∧ sharedNos.length = 52 ∧
      ((treeMembers toldFull).all fun b =>
        sharedNos.contains b || (switchBorders placesW).contains b || b == 354) = true ∧
      ((treeMembers toldFull).all fun b =>
        sharedNos.contains b || (switchBorders placesW).contains b) = false := by
  decide +kernel

/-- A block that tells a tree has its number among `treeMembers`. -/
theorem mem_treeMembers {told : List (List Oracle)} {b : Nat} {l : List Oracle}
    (hb : told[b]? = some l) (hl : l.length ≠ 0) : b ∈ treeMembers told := by
  unfold treeMembers
  refine List.mem_map.2 ⟨(l, b), List.mem_filter.2 ⟨List.mem_zipIdx_iff_getElem?.2 hb, ?_⟩, rfl⟩
  cases l with
  | nil => exact absurd rfl hl
  | cons _ _ => rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}

/-- h1 AND h3 ARE PREMISES. **THE FIELD trees OF `JoinFit` FROM THREE LIMBS.** -/
theorem trees_of_three (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {nos tn : List Nat} (h1 : ∀ b ∈ sharedNos, b ∈ nos)
    (h2 : ∀ p ∈ switchPlaces Zp Bs.G₀, borderNo cF.blocksInOrder p.place ∈ tn) (h3 : 354 ∈ tn) :
    ∀ b blk, cF.blocksInOrder[b]? = some blk → (blk.oracles.flatMap id).length ≠ 0 → b ∈ nos ++ tn := by
  intro b blk hb hl
  have e : (cF.blocksInOrder.map fun x => x.oracles.flatten) = toldFull :=
    toldOf_of_cut (tests_at_head h.toAtMg O).2.1
  have hb' : toldFull[b]? = some blk.oracles.flatten := by
    rw [← e, List.getElem?_map, hb]
    rfl
  rw [List.flatMap_id] at hl
  have t := List.all_eq_true.1 treeMembersW.2.2.1 b (mem_treeMembers hb' hl)
  rw [Bool.or_eq_true, Bool.or_eq_true] at t
  rcases t with (t | t) | t
  · exact List.mem_append.2 (Or.inl (h1 b (List.contains_iff_mem.1 t)))
  · have m : b ∈ switchBorders placesW := List.contains_iff_mem.1 t
    rw [← borders_at_head h O] at m
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 m
    exact List.mem_append.2 (Or.inr (h2 p hp))
  · rw [beq_iff_eq.1 t]
    exact List.mem_append.2 (Or.inr h3)

/-- **The switches' limb, where a record holds the kind's share.** -/
theorem share_trees_limb {W₀ Rc Xi Tr : Type} {Bk : ProverCoinCounts} {bs : List (Block S ProofFile.Cl)}
    {front : Nat} {Zq : ProofFile.Pub} {G : ProofFile.Ground} {Dt : RowDataOf Xi}
    {readers : Local W₀ Rc Xi Tr → Readers} {rest : Nat → TreeLot Bk (Local W₀ Rc Xi Tr)}
    {Ot : Others Bk (Local W₀ Rc Xi Tr)}
    (hin : ShareIn (switchShareAt Bk bs front Zq G Dt readers rest) Ot) :
    ∀ p ∈ switchPlaces Zq G, borderNo bs p.place ∈ Ot.tn :=
  fun p hp => hin.tn _ (List.mem_map.2 ⟨p, hp, rfl⟩)

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.treeMembers
#print axioms ProofFile.Honest.K2.Law.sharedNos
#print axioms ProofFile.Honest.K2.Law.treeMembersW
#print axioms ProofFile.Honest.K2.Law.mem_treeMembers
#print axioms ProofFile.Honest.K2.Law.trees_of_three
#print axioms ProofFile.Honest.K2.Law.share_trees_limb
