-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Second/K08/BlocksInMsg.lean: BlocksInOfLayout.lean's law IN K8's FILES' OWN WORD: it
    ends in BlockInMsg (Johnson/Desc/First/K8/LawBlockIn.lean), in the letters of the second half of
    CellsIn: «∀ b ∈ a.blocks, BlockInMsg cs (l.get i).1 (s.st.rowBits o .main) (s.st.placeBits o
    .main) b». Statements and proofs: each is one call and the structure's three fields.

  blockInMsg_at_statement  St.codes.lengthsOk · reqLayoutOk St.codes s layout · reqArray layout
      born name = some a · St.oracles[o]? = some x · hsh (x has the shape of the message that first
      held the array) ⊢ ∀ b ∈ a.blocks, BlockInMsg St.codes x.shape (St.rowBits o .main)
      (St.placeBits o .main) b.
  blockInMsg_at_member     the same with the codes and the member's shape as letters cs and sh,
      under St.codes = cs and sh = x.shape: the caller lays sh := (l.get i).1.
  blockInMsg_at_pub        with the shape, the layout and the codes those of the plain road's
      public part Z: lengthsOk and reqLayoutOk are paid (pub_lengthsOk · pub_layoutOk): left:
      St.codes = Z.first.codes · the array · the oracle message · hsh · sh = x.shape.
Limits. BlocksInOfLayout.lean's. TOOLS: no reached state of a verifier stands in them. They speak of
    EVERY array that the layout has: K8's files' three fields that ask CellsIn (by report:
    K8LeftC.atFold · HereOwes.atFold · K8Fill.here) ask it
    (Johnson/P1K8R/ConstAt.lean · FillAt.lean · OwesAt.lean),
    at the early arrays alone, which is less.
    FOUR PREMISES ARE OWED AT THE SEAT, BY NOBODY: hcs · hx · hmem ·
    hsh; and «the open link's layout is Z.first's» is the caller's. So the clause on CellsIn stays
    open. No soundness is claimed.

-/
import Johnson.Second.K08.BlocksInOfLayout
import Johnson.Desc.First.K8.LawBlockIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Second.K08
open OnBytes OnBytes.Model OnBytes.Params
open VerifiableInference.Desc.First.K8 (BlockInMsg)


theorem blockInMsg_at_statement (St : Statement) (s : ReqShape) (layout : ReqLayout)
    (hlen : St.codes.lengthsOk = true) (h : reqLayoutOk St.codes s layout = true) (born : ℕ)
    (name : String) (a : ReqArray) (ha : OnBytes.reqArray layout born name = some a) (o : ℕ)
    (x : Oracle) (hx : St.oracles[o]? = some x)
    (hsh : ∀ (L : ReqLink) (msg : ReqMessage), s.link[born]? = some L →
      L.messages[a.message]? = some msg → x.shape = msg.shape) :
    ∀ b ∈ a.blocks,
      BlockInMsg St.codes x.shape (St.rowBits o .main) (St.placeBits o .main) b := fun b hb =>
  have t := blocksIn_at_statement St s layout hlen h born name a ha o x hx hsh b hb
  ⟨t.1, t.2.1, t.2.2⟩


theorem blockInMsg_at_member (cs : Codes) (sh : OracleShape) (St : Statement) (s : ReqShape)
    (layout : ReqLayout) (hcs : St.codes = cs) (hlen : cs.lengthsOk = true)
    (h : reqLayoutOk cs s layout = true) (born : ℕ) (name : String) (a : ReqArray)
    (ha : OnBytes.reqArray layout born name = some a) (o : ℕ) (x : Oracle)
    (hx : St.oracles[o]? = some x) (hmem : sh = x.shape)
    (hsh : ∀ (L : ReqLink) (msg : ReqMessage), s.link[born]? = some L →
      L.messages[a.message]? = some msg → x.shape = msg.shape) :
    ∀ b ∈ a.blocks, BlockInMsg cs sh (St.rowBits o .main) (St.placeBits o .main) b := by
  subst hcs
  subst hmem
  exact blockInMsg_at_statement St s layout hlen h born name a ha o x hx hsh


theorem blockInMsg_at_pub {ol : ProofFile.SecondHashFunctionArgument} {pol ly KL : ByteArray} {Z : ProofFile.Pub}
    (hZ : ProofFile.pureRoad.pub ol pol ly KL = .ok Z) (sh : OracleShape) (St : Statement)
    (hcs : St.codes = Z.first.codes) (born : ℕ) (name : String) (a : ReqArray)
    (ha : OnBytes.reqArray Z.first.layout born name = some a) (o : ℕ) (x : Oracle)
    (hx : St.oracles[o]? = some x) (hmem : sh = x.shape)
    (hsh : ∀ (L : ReqLink) (msg : ReqMessage), Z.first.shape.link[born]? = some L →
      L.messages[a.message]? = some msg → x.shape = msg.shape) :
    ∀ b ∈ a.blocks,
      BlockInMsg Z.first.codes sh (St.rowBits o .main) (St.placeBits o .main) b :=
  blockInMsg_at_member Z.first.codes sh St Z.first.shape Z.first.layout hcs (pub_lengthsOk hZ)
    (Meaning.K2.pub_layoutOk hZ) born name a ha o x hx hmem hsh

end Second.K08

#print axioms Second.K08.blockInMsg_at_statement
#print axioms Second.K08.blockInMsg_at_member
#print axioms Second.K08.blockInMsg_at_pub
