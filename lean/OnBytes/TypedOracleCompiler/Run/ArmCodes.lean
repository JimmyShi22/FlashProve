-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/ArmCodes.lean: the strings of the encoding `implArmD`
(OnBytes/TypedOracleCompiler/Run/ArmDirect.lean) at the link's chain queries, at leaves and at vertices.

OnBytes/TypedOracleCompiler/Run/RowsG.lean goes from strings to values for every page: if a typed query's string is
the bits of the format's string of a call, the family's answer there is what the format's hash gives
at that call. So what is wanted of an encoding is its strings. Here they are said for `implArmD`,
as equations with the strings of the codes of which it is made. No page over the first interface
enters.

Main definition: `pageArmD`, the page of which `implArmD` is the encoding (`implArmD_eq`, by
unfolding).
Main theorems.
 `armD_code_first`   a first query at which f0 writes s has the string s at its last block.
 `armD_code_round`   a later query that is read as q1 has, at block j, the string that the given
                     code of later queries writes at (q1, j).
 `armD_code_leaf`    a leaf query that is read as q1 has the string that the given code of leaves
                     writes at q1.
 `armD_code_node`    a vertex has the string of the library's code of vertices.
 `armD_code_q0`, `armD_code_q1`: the seeds' two queries have the strings of
                     OnBytes/TypedOracleCompiler/Run/SeedPoints.lean's `fbSeeds_q0`, `fbSeeds_q1`.

Not claimed. Where the codes do not write, nothing is said of the string. No pair of maps and no
code is given. Nothing on soundness.


-/
import OnBytes.TypedOracleCompiler.Run.ArmDirect

set_option autoImplicit false

namespace TypedOracleCompiler.Run.ArmDirect
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open TypedOracleCompiler.Run.Apart TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.SeedPage
open TypedOracleCompiler.Run.SeedPoints TypedOracleCompiler.Run.LinkAlong TypedOracleCompiler.Run.LinkOf
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

variable {I1 X1 I2 X2 : Type} {L1 : BatchProtocolWithLeafBody I1 X1} (L2 : BatchProtocolWithLeafBody I2 X2)
  (p0 p1 : PlainPart (shapeOf L2 .test) (annOf L2 .test))
  (isP0 isP1 : PlainPart (shapeOf L2 .test) (annOf L2 .test) → Bool) (cfgL : List (Dig 256)) (sh : Bits)
  (hp0 : ∀ p, isP0 p = true ↔ p = p0) (hp1 : ∀ p, isP1 p = true ↔ p = p1) (rest : ByteArray)
  (K : ℕ) (l : ℕ) (hlt : l < 2 ^ 48) (hne : l ≠ _root_.Fmt.recordLabel)
  (f0 : PCode (FbIn 256 L2 .link)) (h0 : ∀ q s, f0.put q = some s → Is160 l s)
  (F : FbPair L1 L2) (pR : PCode (FbIn 256 L1 .link × Fin (K + 1)))
  (hR : ∀ x s, pR.put x = some s → Is162 l s) (G : LeafPair L1 L2) (V : Leaves L1)
  (cfg : ByteArray) (hcfg : cfg.size = 32) (back : StrCode (AllPts 256 K L2))

/-- The page of which `implArmD` is the encoding. -/
def pageArmD : Page L2 K :=
  pageS L2 p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K (linkD L2 K l hlt hne f0 h0 F pR hR)
    (leavesAlong G V) cfg hcfg back

/-- `implArmD` is that page's encoding. -/
theorem implArmD_eq :
    implArmD L2 p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K l hlt hne f0 h0 F pR hR G V cfg hcfg back =
      implG (pageArmD L2 p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K l hlt hne f0 h0 F pR hR G V cfg hcfg
        back) := rfl

/-- **The link's first query.** -/
theorem armD_code_first (q2 : FbIn 256 L2 .link) (hq : q2.round = 0) (s : List Bool)
    (hs : f0.put q2 = some s) :
    (implG (pageArmD L2 p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K l hlt hne f0 h0 F pR hR G V cfg hcfg
      back)).code (.fb .link) q2 (Fin.last K) = s :=
  implG_fb _ .link q2 _ s (linkOf_first l hlt hne f0 h0 (roundsAlong F pR)
    (roundsAlong_is l F pR hR) q2 hq s hs)

/-- **A later query of the link.** -/
theorem armD_code_round (q2 : FbIn 256 L2 .link) (hq : q2.round ≠ 0) (q1 : FbIn 256 L1 .link)
    (h : F.sel q2 = some q1) (j : Fin (K + 1)) (s : List Bool) (hs : pR.put (q1, j) = some s) :
    (implG (pageArmD L2 p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K l hlt hne f0 h0 F pR hR G V cfg hcfg
      back)).code (.fb .link) q2 j = s :=
  implG_fb _ .link q2 j s ((linkOf_round l hlt hne f0 h0 (roundsAlong F pR)
    (roundsAlong_is l F pR hR) q2 hq j).trans ((roundsAlong_put F pR q2 q1 h j).trans hs))

/-- **A leaf query.** -/
theorem armD_code_leaf (q2 : LeafIn L2) (q1 : LeafIn L1) (h : G.sel q2 = some q1) (s : List Bool)
    (hs : V.lf.put q1 = some s) (j : Fin 1) :
    (implG (pageArmD L2 p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K l hlt hne f0 h0 F pR hR G V cfg hcfg
      back)).code .leaf q2 j = s :=
  implG_leaf _ q2 s ((leavesAlong_put G V q2 q1 h).trans hs) j

/-- **A vertex.** -/
theorem armD_code_node (q : Bits × Bits) (s : List Bool) (hs : (pNode cfg).put q = some s)
    (j : Fin 1) :
    (implG (pageArmD L2 p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K l hlt hne f0 h0 F pR hR G V cfg hcfg
      back)).code .node q j = s :=
  implG_node _ q s hs j

/-- **The first query of a seed**, at the block of the chain value. -/
theorem armD_code_q0 (cm : Dig 256) (hr : rest.size < 2 ^ 32) :
    (implG (pageArmD L2 p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K l hlt hne f0 h0 F pR hR G V cfg hcfg
      back)).code (.fb .test) (q0 L2 .test p0 cfgL sh cm) (Fin.last K) =
      bytesToBits (_root_.Fmt.oStr 0 160 0 _root_.Fmt.recordLabel _root_.Fmt.zero32
        (_root_.Fmt.firstBytes _root_.Fmt.zero32 (digToBytes cm ++ rest) ByteArray.empty none)) :=
  implG_fb _ .test _ _ _ (fbSeeds_q0 L2 .test p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K cm hr)

/-- **The second query of a seed**, at every block. -/
theorem armD_code_q1 (hK : K < 2 ^ 48) (v : Bits) (hv : v.length = 256) (j : Fin (K + 1)) :
    (implG (pageArmD L2 p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K l hlt hne f0 h0 F pR hR G V cfg hcfg
      back)).code (.fb .test) (q1 L2 .test p1 v) j =
      bytesToBits (_root_.Fmt.oStr (UInt8.ofNat (blockNo 0 K j % 2)) 162 _root_.Fmt.recordLabel 1
        (bitsToBytes v) (ByteArray.empty ++ _root_.Fmt.tail .seeds 0 0 (blockNo 0 K j / 2))) :=
  implG_fb _ .test _ _ _ (fbSeeds_q1 L2 .test p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K hK v hv j)

end TypedOracleCompiler.Run.ArmDirect
