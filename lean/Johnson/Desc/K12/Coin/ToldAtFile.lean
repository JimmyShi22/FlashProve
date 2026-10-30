-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/ToldAtFile.lean: **WHAT A DESCRIPTION TELLS OF THE SHARED CHAIN's FIRST TREES
IS WHAT ITS TWO SENDING BLOCKS TELL**, by the flat lists. Statements and proofs.

`FileDescription.oracleAt` (Johnson/Desc/Msg.lean) reads the three chains' flat lists of blocks in a row.
ToldOfLay.lean speaks of one sending's own list (`Desc.K14.oraclesOf codes sent gs`). Here the two
are tied for the shared chain as `Desc.K14.chainOf` (Johnson/Desc/K14/Blocks.lean) makes it.
  `told_length`: a sending tells of as many trees as its layout has shapes.
  `told_of_chain`: where `withU P.S = some sU`: what the blocks of `chainOf c P tests last` tell, in
    a row, is: what "send o_u" tells; what "send o_omega" tells; what the tests tell; what the last
    block tells. The kind's other blocks tell of no tree.
  `oracleAt_mid`: a list lemma: where the shared chain tells pre ++ told ++ post, `oracleAt` at
    (the first chain's told trees) + pre.length + τ is told's entry τ.
  `oracleAt_u`, `oracleAt_omega`: so, for a description G whose shared chain tells what that chain
    tells: at lo + τ what "send o_u" tells of its tree τ; at lo + (the trees of "send o_u") + τ what
    "send o_omega" tells of its tree τ; lo: the number of trees of which the first chain tells.
  `seatIs_of_laid`: **`SeatIs` FROM "THE RECORD CARRIES THE LAYOUT"**: for message i of a sending
    with the layout lay, whose trees stand from the book's place base on: where the member's tree
    and part are lay's (m.t = base + lay.tree i, m.part = lay.part i), the book's tree there has the
    member's shape, that shape is lay's, and the description tells at lo + base + τ what the sending
    tells of τ: there is what the description tells of the tree number lo + m.t, `SeatIs` holds of
    it at the tenant lay.part i, and that tenant is message i's.
Limits. Nothing on soundness. THAT A DESCRIPTION's SHARED CHAIN TELLS WHAT `chainOf c P tests last`
TELLS IS A PREMISE (one equation between two lists of `Oracle`): shown here of no description. That
lo is the data's t₁ is another's (`Block.shaped`; a premise of `oraclesAre` too).

-/
import Johnson.Desc.K12.Coin.ToldOfLay
import Johnson.Desc.Own.TreesMean

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.LayTreesLaws
open VerifiableInference.Desc
open _root_.Desc.K14 (P14 St chainOf withU withOmega)

/-- A sending tells of as many trees as its layout has shapes. -/
theorem told_length (codes : Codes) (sent : Array OracleNotice) (gs : List (List Nat))
    (lay : TreeLay) (h : Own.treesMade codes sent = some lay) :
    (_root_.Desc.K14.oraclesOf codes sent gs).length = lay.shapes.size := by
  unfold _root_.Desc.K14.oraclesOf
  rw [h]
  simp

/-- **What the shared chain's blocks tell, in a row.** -/
theorem told_of_chain (c : Model.Verify.Chains) (P : P14) (tests : List (Block St Unit))
    (last : List (Block St Unit) → Block St Unit) (sU : Array OracleNotice)
    (hU : withU P.S = some sU) :
    oraclesOf (chainOf c P tests last).blocksInOrder =
      _root_.Desc.K14.oraclesOf P.codes sU [[0], []] ++
        (_root_.Desc.K14.oraclesOf P.codes (withOmega P.S) [[1], [1, 0]] ++
          (oraclesOf tests ++
            (last (_root_.Desc.K14.blocksOr P ++ tests)).oracles.flatMap id)) := by
  have hb : oraclesOf (_root_.Desc.K14.blocksOr P) =
      _root_.Desc.K14.oraclesOf P.codes sU [[0], []] ++
        _root_.Desc.K14.oraclesOf P.codes (withOmega P.S) [[1], [1, 0]] := by
    unfold _root_.Desc.K14.blocksOr _root_.Desc.K14.blocks
    simp [hU, oraclesOf, _root_.Desc.K14.sendAt, _root_.Desc.K14.parK1, K1.Par.sent]
  have hbare : ∀ l : List (Block St Unit),
      oraclesOf (l.map fun b => { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }) = oraclesOf l := by
    intro l
    unfold oraclesOf
    rw [List.flatMap_map]
  unfold chainOf Chain.blocksInOrder
  simp only [List.map_nil, List.flatMap_nil, List.append_nil]
  show oraclesOf (_ :: ((_root_.Desc.K14.blocksOr P ++ tests).map _ ++ [_])) = _
  unfold oraclesOf at hb hbare ⊢
  rw [List.flatMap_cons, List.flatMap_append, hbare, List.flatMap_append, hb]
  simp [_root_.Desc.K14.frontBlock, roundlessBlock]

/-- Where the shared chain tells pre ++ told ++ post. -/
theorem oracleAt_mid {Xi : Type} (G : FileDescription Xi) (pre told post : List Oracle)
    (h : oraclesOf G.shared.blocksInOrder = pre ++ (told ++ post)) (τ : Nat) (o : Oracle)
    (ho : told[τ]? = some o) :
    G.oracleAt ((oraclesOf G.first.blocksInOrder).length + pre.length + τ) = some o := by
  have hτ : τ < told.length := (List.getElem?_eq_some_iff.1 ho).1
  unfold FileDescription.oracleAt
  rw [List.append_assoc, List.getElem?_append_right (by omega), h,
    show (oraclesOf G.first.blocksInOrder).length + pre.length + τ - (oraclesOf G.first.blocksInOrder).length =
      pre.length + τ by omega,
    List.append_assoc, List.getElem?_append_right (by omega),
    show pre.length + τ - pre.length = τ by omega, List.append_assoc,
    List.getElem?_append_left hτ]
  exact ho

section
variable {Xi : Type} (G : FileDescription Xi) (c : Model.Verify.Chains) (P : P14)
  (tests : List (Block St Unit)) (last : List (Block St Unit) → Block St Unit)
  (sU : Array OracleNotice)

/-- **At the trees of "send o_u".** -/
theorem oracleAt_u (hG : oraclesOf G.shared.blocksInOrder = oraclesOf (chainOf c P tests last).blocksInOrder)
    (hU : withU P.S = some sU) (τ : Nat) (o : Oracle)
    (ho : (_root_.Desc.K14.oraclesOf P.codes sU [[0], []])[τ]? = some o) :
    G.oracleAt ((oraclesOf G.first.blocksInOrder).length + τ) = some o := by
  have h := oracleAt_mid G [] _ _ (by
    rw [hG, told_of_chain c P tests last sU hU]
    rfl) τ o ho
  simpa using h

/-- **At the trees of "send o_omega".** -/
theorem oracleAt_omega (hG : oraclesOf G.shared.blocksInOrder = oraclesOf (chainOf c P tests last).blocksInOrder)
    (hU : withU P.S = some sU) (layU : TreeLay) (hl : Own.treesMade P.codes sU = some layU)
    (τ : Nat) (o : Oracle)
    (ho : (_root_.Desc.K14.oraclesOf P.codes (withOmega P.S) [[1], [1, 0]])[τ]? = some o) :
    G.oracleAt ((oraclesOf G.first.blocksInOrder).length + layU.shapes.size + τ) = some o := by
  have h := oracleAt_mid G _ _ _ (by
    rw [hG, told_of_chain c P tests last sU hU]) τ o ho
  rw [told_length P.codes sU _ layU hl] at h
  exact h

end

/-- **`SeatIs` from "the record carries the layout".** -/
theorem seatIs_of_laid {Xi : Type} (G : FileDescription Xi) (codes : Codes) (sent : Array OracleNotice)
    (gs : List (List Nat)) (lay : TreeLay) (h : Own.treesMade codes sent = some lay)
    (hg : gs.length = sent.size) (lo base : Nat)
    (hO : ∀ τ o, (_root_.Desc.K14.oraclesOf codes sent gs)[τ]? = some o →
      G.oracleAt (lo + base + τ) = some o)
    (book : TreeBook) (m : H2K.First.Seat1) (i : Nat) (hi : i < sent.size)
    (hmt : m.t = base + lay.tree.getD i 0) (hmp : m.part = lay.part.getD i 0)
    (hsh : (book.trees[m.t]?).map (·.shape) = some m.tsh)
    (hts : m.tsh = lay.shapes.getD (lay.tree.getD i 0) default) :
    ∃ o, G.oracleAt (lo + m.t) = some o ∧
      SeatIs (fun z => lo + z) book m (lo + m.t) (lay.part.getD i 0) o ∧
      o.tenants[lay.part.getD i 0]? = some (tenantOf sent gs i) := by
  have hlt : lay.tree.getD i 0 < lay.shapes.size := (Own.treesMade_gives h).2.1 i hi
  have hT : lay.shapes[lay.tree.getD i 0]? = some m.tsh := by
    rw [hts]
    generalize lay.tree.getD i 0 = τ at hlt ⊢
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt]
    rfl
  obtain ⟨o, ho, hS⟩ := told_shape codes sent gs lay h hg _ _ hT
  refine ⟨o, ?_, ⟨rfl, hsh, hmp, hS.main, hS.mask, hS.log⟩,
    told_tenant codes sent gs lay h hg i hi o ho⟩
  rw [hmt, ← Nat.add_assoc]
  exact hO _ o ho

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.told_of_chain
#print axioms VerifiableInference.Desc.K12.Coin.oracleAt_mid
#print axioms VerifiableInference.Desc.K12.Coin.oracleAt_u
#print axioms VerifiableInference.Desc.K12.Coin.oracleAt_omega
#print axioms VerifiableInference.Desc.K12.Coin.seatIs_of_laid
