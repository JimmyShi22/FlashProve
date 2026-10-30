-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/ArmDirect.lean: one encoding over a second interface. The link's first query is
written directly. A later query of the link, and a leaf query, has the string that a code over a
first interface writes at the query as which it is read. At a query where these codes write, and
where a page over the first interface has the same string, the encoding reads out of every oracle
what that page's encoding reads. Elsewhere nothing is said.

The link's first query is not carried from the first interface. A code f0 over the second interface
writes it (OnBytes/TypedOracleCompiler/Run/LinkFirstAns.lean has one
for a first query that holds two roots and both tables' answers as digests in its list). So nothing
is asked of how a first query over the first interface would be carried.

Main definition: `implArmD`.
Main theorems.
 `armD_first`  a first query q2 at which f0 writes s, and a query q1 over L1 at whose last block a
               page C1 has the string s: one chain value, out of every oracle.
 `armD_round`  a later query that is read as q1, where the given code writes at all blocks of q1 and
               C1 has these strings: one whole answer.
 `armD_leaf`, `armD_node`: a leaf query; a vertex.
 `armD_q0`, `armD_q1`: the seeds' two queries are read as in OnBytes/TypedOracleCompiler/Run/SeedPage.lean.

This is the encoding that is meant for the entry's arm.

Not claimed. No pair of maps, no code and no page over L1 is given: they are letters. So is `back`,
a one-to-one code of ALL typed points over L2 with a parser: the encoding is one to one through it,
and none is given at any interface here. At a typed point where the partial codes do not write, the
string is `back`'s behind the escape: no string of the programs, and not the first page's. That a
verifier over L2 asks these queries alone. Nothing on soundness.


-/
import OnBytes.TypedOracleCompiler.Run.LinkOf

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

/-- The link's chain queries over L2: the first directly, the later ones carried. -/
def linkD : LinkCode L2 K :=
  linkOf l hlt hne f0 h0 (roundsAlong F pR) (roundsAlong_is l F pR hR)

/-- **The encoding over L2.** -/
def implArmD : OracleCoding (typedOracleFamily 256 K L2) 256 :=
  implS L2 p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K (linkD L2 K l hlt hne f0 h0 F pR hR)
    (leavesAlong G V) cfg hcfg back

/-- **The link's first query: the chain value.** -/
theorem armD_first (C1 : Page L1 K) (q2 : FbIn 256 L2 .link) (hq : q2.round = 0) (s : List Bool)
    (hs : f0.put q2 = some s) (q1 : FbIn 256 L1 .link)
    (h1 : (implG C1).code (.fb .link) q1 (Fin.last K) = s) (g : Fam (rom 256)) :
    (readBlocks (implArmD L2 p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K l hlt hne f0 h0 F pR hR G V cfg
        hcfg back) g (.fb .link) q2 : (Fin K → Dig 256) × Dig 256).2 =
      (readBlocks (implG C1) g (.fb .link) q1 : (Fin K → Dig 256) × Dig 256).2 :=
  fb_read_tail C1 _ .link q1 q2 (by
    rw [h1]
    exact implG_fb _ .link q2 _ s (linkOf_first l hlt hne f0 h0 (roundsAlong F pR)
      (roundsAlong_is l F pR hR) q2 hq s hs)) g

/-- **A later query of the link: the whole answer.** -/
theorem armD_round (C1 : Page L1 K) (q2 : FbIn 256 L2 .link) (hq : q2.round ≠ 0)
    (q1 : FbIn 256 L1 .link) (h : F.sel q2 = some q1) (s : Fin (K + 1) → List Bool)
    (hs : ∀ j, pR.put (q1, j) = some (s j))
    (h1 : ∀ j, (implG C1).code (.fb .link) q1 j = s j) (g : Fam (rom 256)) :
    (readBlocks (implArmD L2 p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K l hlt hne f0 h0 F pR hR G V cfg
        hcfg back) g (.fb .link) q2 : (Fin K → Dig 256) × Dig 256) =
      readBlocks (implG C1) g (.fb .link) q1 :=
  fb_read C1 _ .link q1 q2 (fun j => by
    rw [h1 j]
    exact implG_fb _ .link q2 j (s j) ((linkOf_round l hlt hne f0 h0 (roundsAlong F pR)
      (roundsAlong_is l F pR hR) q2 hq j).trans ((roundsAlong_put F pR q2 q1 h j).trans (hs j)))) g

/-- **A leaf query.** -/
theorem armD_leaf (C1 : Page L1 K) (q2 : LeafIn L2) (q1 : LeafIn L1) (h : G.sel q2 = some q1)
    (s : List Bool) (hs : V.lf.put q1 = some s) (h1 : (implG C1).code .leaf q1 (0 : Fin 1) = s)
    (g : Fam (rom 256)) :
    (readBlocks (implArmD L2 p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K l hlt hne f0 h0 F pR hR G V cfg
        hcfg back) g .leaf q2 : Dig 256) = readBlocks (implG C1) g .leaf q1 :=
  leaf_read C1 _ q1 q2 (by
    rw [h1]
    exact implG_leaf _ q2 s ((leavesAlong_put G V q2 q1 h).trans hs) 0) g

/-- **A vertex.** -/
theorem armD_node (C1 : Page L1 K) (q : Bits × Bits) (s : List Bool)
    (hs : (pNode cfg).put q = some s) (h1 : (implG C1).code .node q (0 : Fin 1) = s)
    (g : Fam (rom 256)) :
    (readBlocks (implArmD L2 p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K l hlt hne f0 h0 F pR hR G V cfg
        hcfg back) g .node q : Dig 256) = readBlocks (implG C1) g .node q :=
  node_read C1 _ q (by
    rw [h1]
    exact implG_node _ q s hs 0) g

/-- **The first query of a seed.** -/
theorem armD_q0 (cm : Dig 256) (hr : rest.size < 2 ^ 32) :
    (readBlocks (implArmD L2 p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K l hlt hne f0 h0 F pR hR G V cfg
        hcfg back) oBits (.fb .test) (q0 L2 .test p0 cfgL sh cm) : (Fin K → Dig 256) × Dig 256).2 =
      bytesToDig (_root_.Fmt.oracle (_root_.Fmt.oStr 0 160 0 _root_.Fmt.recordLabel
        _root_.Fmt.zero32
        (_root_.Fmt.firstBytes _root_.Fmt.zero32 (digToBytes cm ++ rest) ByteArray.empty none))) :=
  implS_q0 L2 p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K _ _ cfg hcfg back cm hr

/-- **The second query of a seed.** -/
theorem armD_q1 (hK : K < 2 ^ 48) (v : Bits) (hv : v.length = 256) (k : Fin K) :
    (readBlocks (implArmD L2 p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K l hlt hne f0 h0 F pR hR G V cfg
        hcfg back) oBits (.fb .test) (q1 L2 .test p1 v) : (Fin K → Dig 256) × Dig 256).1 k =
      bytesToDig (_root_.Fmt.oracle (_root_.Fmt.oStr (UInt8.ofNat ((k.val + 1) % 2)) 162
        _root_.Fmt.recordLabel 1 (bitsToBytes v)
        (ByteArray.empty ++ _root_.Fmt.tail .seeds 0 0 ((k.val + 1) / 2)))) :=
  implS_q1 L2 p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K _ _ cfg hcfg back hK v hv k

end TypedOracleCompiler.Run.ArmDirect
