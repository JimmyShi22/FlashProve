-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/BookTrees.lean: where a code switch's yes finds the trees of the senders whose messages
it reads: the tree stands in the book behind the switch's sending, its number is its place, and its
shape is the one that the sender's plan lays. And two public facts on the written lists: the lengths
of the trees that hold a closed group's members. States five theorems; their proofs are owed.
-/
import Johnson.Desc.ProofFile.Honest.K2.SeatedL
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten
import Johnson.Desc.K1.Law.LaterOne
import Johnson.Desc.First.Close.Law.SeatsOfLink
import Johnson.Desc.First.Close.Law.MaskLaidFull
import Johnson.Top.H0.K2Hears.Whole
import Johnson.Desc.K2.Honest.Returns.SeatReached
import Johnson.P5J.MgAtAll
import Johnson.P5J.FourAtMg
import AtFullSide.K2.BookTreesA
import AtFullSide.K2.BookTreesB
import AtFullSide.K2.BookTreesC
import AtFullSide.K2.BookTreesE
import Johnson.Desc.ProofFile.Honest.K2.Law.SwitchNo
import Johnson.LPFE1R.RowPubAt
import Johnson.HB.LLHARD.LaidWritten
import Johnson.G.PackLit
import Johnson.Desc.Ok.PlanWritten.SizedLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K2
open OnBytes
open OnBytes.Slice (codeOf)
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 AtYes)
open VerifiableInference.Desc.First.Close (membersOf seatK10 maskTree maskShape)
open VerifiableInference.Desc.LinkJoin (loAt)
open VerifiableInference.Desc.K1 (parL noL firstPar gpOf)
open VerifiableInference.Desc.K13.Law (LFull)
open VerifiableInference.Desc.Sound (allOf EAll)
open OnBytes.Maker (WholeD)
open Johnson.G (codesFull2)
open VerifiableInference.PlanWritten (proofSizedFull)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest (treesTo)
open ProofFile.Honest.K2 (SwitchPlace switchPar switchPlaces)
open ProofFile.Honest.K2.Law (switchNo)

/-- **The senders that a code switch reads**: the opening at number 2, a later sender at its link,
a switch in front. P: the sender's plan. b: its number in the first chain. -/
def SenderAt (Zp : ProofFile.Pub) (Bs : ProofFile.PureBase) (P : VerifiableInference.Desc.K1.Par) (b : Nat) :
    Prop :=
  (P = firstPar Bs.G₀.first (gpOf Zp) ∧ b = 2) ∨
    (∃ l d, l < 25 ∧ P = parL Zp Bs.G₀ l d ∧ b = noL l d) ∨
    ∃ p₀ ∈ switchPlaces Zp Bs.G₀, P = switchPar p₀ ∧ b = switchNo p₀

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}
  {base : List (Block TS ProofFile.Cl)}

/-- **A sender's tree behind a yes of the code switch.** a: the state reached at the border nb. s₁:
the state at which the kind's decision stands: it has a's book. τ: a tree of the sender's plan. The
sender stands in front of the border. -/
theorem tree_at_yes (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {nb : Nat}
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch nb a) {s₁ t : TS} (hbk : s₁.book = a.1.2.book) {q : P2} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {x : _root_.Tw.K2.Front} {z : _root_.Tw.K2.Sent}
    {S3 : Statement} {Y : Array E} {rows : List OnBytes.Row} {G : Group} {cd : Code}
    (A : AtYes q s₁ t r₁ r₂ gs x z S3 Y rows G cd)
    {P : VerifiableInference.Desc.K1.Par} {b : Nat} (hP : SenderAt Zp Bs P b) (hb : b < nb)
    {τ : Nat}
    (hτ : τ < ((VerifiableInference.Desc.Own.treesMade P.codes P.sent).getD {}).shapes.size) :
    ∃ tr : Tree, z.book.trees[treesTo cF.blocksInOrder b + τ]? = some tr ∧
      tr.number = treesTo cF.blocksInOrder b + τ ∧
      tr.shape = ((VerifiableInference.Desc.Own.treesMade P.codes P.sent).getD {}).shapes.getD τ {} ∧
      LFull.shapes[treesTo cF.blocksInOrder b + τ]? = some tr.shape := by
  obtain ⟨h2, hroom, hshape⟩ := senderFits_says (sender_fits_at_head h.toAtMg O hP)
  obtain ⟨hsize, hall⟩ := book_at_reached h.toAtMg O (z := a.1.1) (s := a.1.2)
    (Johnson.Desc.First.Walk.Tied.rchAt_raw hr.1) (by omega)
  have e0 := ProofFile.Honest.K2.Law.treesTo_at_head h.toAtMg O b
  have e1 := ProofFile.Honest.K2.Law.treesTo_at_head h.toAtMg O (b + 1)
  have hadd : ∀ m d, treesTo cF.blocksInOrder m ≤ treesTo cF.blocksInOrder (m + d) := by
    intro m d
    unfold ProofFile.Honest.treesTo
    rw [List.take_add, List.flatMap_append, List.length_append]
    exact Nat.le_add_right _ _
  have hmono : treesTo cF.blocksInOrder (b + 1) ≤ treesTo cF.blocksInOrder nb := by
    have hm := hadd (b + 1) (nb - (b + 1))
    rwa [Nat.add_sub_cancel' (Nat.succ_le_of_lt hb)] at hm
  have hlt : treesTo cF.blocksInOrder b + τ < a.1.2.book.trees.size := by omega
  obtain ⟨T, hT⟩ : ∃ T, a.1.2.book.trees[treesTo cF.blocksInOrder b + τ]? = some T :=
    ⟨_, Array.getElem?_eq_getElem hlt⟩
  obtain ⟨hnum, hsh⟩ := hall _ T hT
  refine ⟨T, ?_, hnum, ?_, hsh⟩
  · rw [(sending_keeps_at_yes A).2 _ (by rw [hbk]; exact hlt), hbk]
    exact hT
  · rw [e0, hshape τ hτ] at hsh
    exact (Option.some.inj hsh).symm

/-- **What is public of a sender**: its plan passes its own test, it lays its trees at the written
codes, and its block in the first chain declares as many trees as the plan lays. -/
theorem sender_plan (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {P : VerifiableInference.Desc.K1.Par} {b : Nat} (hP : SenderAt Zp Bs P b) :
    VerifiableInference.Desc.K1.planOkOwn P = true ∧ P.codes = codesFull2 ∧
      ∃ blk : Block TS ProofFile.Cl, cF.blocksInOrder[b]? = some blk ∧
        (blk.oracles.flatMap id).length = P.trees.length := by
  exact sender_plan_at_head h.toAtMg O hP

/-- **An older message's seat behind a yes of the code switch** is the seat in the book in front. -/
theorem place_at_yes {s₁ t : TS} {q : P2} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {x : _root_.Tw.K2.Front} {z : _root_.Tw.K2.Sent}
    {S3 : Statement} {Y : Array E} {rows : List OnBytes.Row} {G : Group} {cd : Code}
    (A : AtYes q s₁ t r₁ r₂ gs x z S3 Y rows G cd) {o : Nat} (ho : o < s₁.book.place.size) :
    z.book.place[o]? = s₁.book.place[o]? := by
  exact (sending_keeps_at_yes A).1 o ho

set_option maxRecDepth 1000000 in
/-- **The trees of a closed group's members**, on the written lists: a member with main rows lies in
a tree of the length of the group's code, and a member with mask rows in a tree long enough for the
mask code. code, maskCode: the written request's. -/
theorem member_trees_written :
    ((List.range 25).all fun l => (membersOf (loAt l)).all fun i =>
      (((loAt l).get i).1.mainRows == 0 ||
        (LFull.shapes[(seatK10 (loAt l) P5T.psFull l i).1]?).any fun t =>
          t.logN == (codesFull2.base.getD proofSizedFull.request.code default).logN) &&
      (((loAt l).get i).1.maskRows == 0 ||
        (LFull.shapes[(seatK10 (loAt l) P5T.psFull l i).1]?).any fun t =>
          decide ((codeOf (codesFull2.mask.getD proofSizedFull.request.maskCode default)).a ≤
            t.logN))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **The tree of a link's fresh mask**, on the written lists: it is long enough for the mask code.
-/
theorem fresh_trees_written : ((List.range 25).all fun l =>
    decide ((codeOf (codesFull2.mask.getD proofSizedFull.request.maskCode default)).a ≤
      (maskShape l).logN)) = true := by
  decide +kernel

end AtFullSide.K2

#print axioms AtFullSide.K2.tree_at_yes
#print axioms AtFullSide.K2.place_at_yes
#print axioms AtFullSide.K2.sender_plan
#print axioms AtFullSide.K2.member_trees_written
#print axioms AtFullSide.K2.fresh_trees_written
