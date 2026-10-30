-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/ArmLaws.lean: the laws at vertices and at leaves of the family of typed oracles that
the encoding `implArmD` (OnBytes/TypedOracleCompiler/Run/ArmDirect.lean) reads out of one oracle.

The clause "every walk from a leaf reaches its root" of the lax verifier's yes
(OnBytes/TypedOracleCompiler/Slice/EntryWhole.lean: `assembleS_walks`, `ownOkE_of_read`, `stoOkE_of_read`) looks at
the family of typed oracles in three places: the law at vertices (`NodeLaw`,
OnBytes/TypedOracleCompiler/Run/WholePaths.lean), the answer at a leaf of a tree of the chain's own, and the answer
at a leaf of a stored table. Here the three are shown, first for the family that any page's encoding
reads out of ANY oracle g on bit strings (`RowsG.famG C g`), from equations on that encoding's
strings, against the format's hash made of the same g (`RowsG.hOfG g`); then for `implArmD`. The
interface is a variable. The code of leaves is `leafCode` of OnBytes/TypedOracleCompiler/Run/KeyLeaves.lean (over
an interface whose bodies are bit strings), carried along a map of leaf queries.

Main theorems.
 `al_node`, `al_own`, `al_sto`   the three laws at any page C, from: a vertex has the string of the
                 format's call 166; a leaf query that `sel` reads as q1 has the string that the
                 code of leaves writes at q1.
 `nodeLaw_armD`   `NodeLaw` with the format's call 166 under the page's digest.
 `ownLeaf_armD`   the hypothesis `hleaf` of `ownOkE_of_read`, to the letter, at a form s and a way
                 e2 of writing a leaf's body over L2. Asked: G reads the body `e2 s x sym` as the
                 format's spelling of that leaf, and keeps the salt; s is of no stored tree; its
                 label's first word is below 2^48; 2^depth + 2^depth ≤ 2^64; the run value has 32
                 bytes; the code of leaves is made for a file's salt of sB bytes.
 `stoLeaf_armD`   the hypothesis `hleaf` of `stoOkE_of_read`, to the letter. Asked: G reads the body
                 `embE2 y` as the body `embX` of the stored symbol y, and keeps the salt; s is
                 stored, of the tree 0, of a width below 2^24; 2^depth + 2^depth ≤ 2^64; sB / 8 is
                 below 2^8; the digest has 32 bytes.

Not claimed. No pair of maps G, no e2 and no embE2 is given, and what is asked of them is shown of
none. Where the codes do not write, nothing is said. No domain of the format's hash is asked: these
are equations at every g. Nothing on the chain's queries. Nothing on soundness.


-/
import OnBytes.TypedOracleCompiler.Run.ArmCodes
import OnBytes.TypedOracleCompiler.Run.RowsE3
import OnBytes.TypedOracleCompiler.Run.Node178
import OnBytes.TypedOracleCompiler.Run.WholePaths
import OnBytes.TypedOracleCompiler.Slice.Batch3SRead

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Run.ArmLaws
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.Apart TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.SeedPage
open TypedOracleCompiler.Run.SeedPoints TypedOracleCompiler.Run.LinkAlong TypedOracleCompiler.Run.LinkOf
open TypedOracleCompiler.Run.ArmDirect TypedOracleCompiler.Run.RowsG TypedOracleCompiler.Run.RowsE3 TypedOracleCompiler.Strings
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run
open _root_.Run.PQ (SgX)

/-! ## At any page -/

section
variable {I X I0 X0 : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ} (C : Page L K) (g : Fam (rom 256))

/-- **The law at vertices**, if a vertex on two strings of 256 bits has the string of the format's
call 166 under cfg. -/
theorem al_node (cfg : ByteArray)
    (hc : ∀ a b : Bits, a.length = 256 → b.length = 256 →
      (implG C).code .node (a, b) (0 : Fin 1) =
        bytesToBits (_root_.Fmt.oStr 0 166 0 0 cfg (bitsToBytes a ++ bitsToBytes b))) :
    NodeLaw (famG C g) (fun a b => hOfG g 166 0 0 cfg (a ++ b)) where
  node := fun a b ha hb =>
    node_of_code C g (a, b) 166 0 0 cfg (bitsToBytes a ++ bitsToBytes b) (by decide) (hc a b ha hb)
  size := fun a b => _root_.Run.PQ.size_HO32 _ (size_oB g) 166 0 0 cfg (a ++ b) (by decide)

variable (L0 : _root_.Iop.BatchProtocol I0 X0) (nb : ℕ) (cfgV : ByteArray)
  (sel : LeafIn L → Option (LeafIn (strung L0)))
  (hcode : ∀ q2 q1 s, sel q2 = some q1 → (KeyLeaves.leafCode L0 nb cfgV).put q1 = some s →
    (implG C).code .leaf q2 (0 : Fin 1) = s)
include hcode

/-- **The law at a leaf of a tree of the chain's own.** -/
theorem al_own (sB : ℕ) (hn : nb = 8 * sB) (e2 : Enc1 (Body L)) (s : _root_.Fmt.Shape)
    (h1 : s.stored = false) (hp : _root_.Fmt.leafPlace s.tree s.W (sB / 8) < 2 ^ 48)
    (ha : 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64) (run : ByteArray) (hrun : run.size = 32)
    (hsel : ∀ (x : Fin (2 ^ s.a)) (sym : Fin s.W → UInt64) (z : Bits),
      sel ⟨e2 s x sym, z⟩ = some ⟨spell2 164 (_root_.Fmt.leafPlace s.tree s.W (sB / 8),
        2 ^ s.a + x.val, _root_.Fmt.colBytes (List.ofFn sym) ++
          _root_.Fmt.zeroBytes (_root_.Fmt.fillLen s.W sB)), z⟩) :
    ∀ (x : Fin (2 ^ s.a)) (sym : Fin s.W → UInt64) (salt : ByteArray), salt.size = sB →
      (famG C g .leaf (⟨e2 s x sym, leafSalt run salt⟩ : LeafIn L) : Dig 256) =
        bytesToDig (leafAtH (hOfG g) s run x.val (List.ofFn sym) salt) := by
  intro x sym salt hs
  have hi : 2 ^ s.a + x.val < 2 ^ 64 := by
    have := x.isLt
    omega
  have hw := leafCode_at L0 nb sB hn cfgV _ 164 _ _ _
    (ok2_spell 164 _ _ (_root_.Fmt.colBytes (List.ofFn sym) ++
      _root_.Fmt.zeroBytes (_root_.Fmt.fillLen s.W sB)) (Or.inl rfl) hp hi)
    (rd2_spell 164 _ _ _ (by decide) hp hi) run salt hrun hs
    (leafOK2_own _ cfgV _ (spell2_take 164 _).2)
  have hv := leaf_of_code C g (⟨e2 s x sym, leafSalt run salt⟩ : LeafIn L) 164 _ _ run _ (by decide)
    (hcode _ _ _ (hsel x sym (leafSalt run salt)) hw)
  rw [hv]
  unfold leafAtH _root_.Fmt.leafBytes
  rw [h1, List.length_ofFn, hs]
  rfl

/-- **The law at a leaf of a stored table.** -/
theorem al_sto (sB : ℕ) (c : StrCode (ℕ × List UInt64)) (hn : nb = 8 * sB) (embE2 : SgX → Body L)
    (s : _root_.Fmt.Shape) (h1 : s.stored = true) (h2 : s.tree = 0) (hW : s.W < 2 ^ 24)
    (ha : 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64) (h8 : sB / 8 < 2 ^ 8) (hcV : cfgV.size = 32)
    (hsel : ∀ (y : SgX) (z : Bits), sel ⟨embE2 y, z⟩ = some ⟨embX s.a sB c y, z⟩) :
    ∀ (x : ℕ) (col : List UInt64) (salt : ByteArray), x < 2 ^ s.a → col.length = s.W →
      salt.size = sB →
      (famG C g .leaf (⟨embE2 (x, col), leafSalt cfgV salt⟩ : LeafIn L) : Dig 256) =
        bytesToDig (leafAtH (hOfG g) s cfgV x col salt) := by
  intro x col salt hx hcl hs
  have hk := storedOK_of s.a sB x col hx ha (by rw [hcl]; exact hW) h8
  have hw := leafCode_at L0 nb sB hn cfgV _ _ _ _ _ (ok2_rd2_embX s.a sB c (x, col) hk).1
    (ok2_rd2_embX s.a sB c (x, col) hk).2 cfgV salt hcV hs (leafOK2_cfg L0 cfgV salt hcV _)
  have hv := leaf_of_code C g (⟨embE2 (x, col), leafSalt cfgV salt⟩ : LeafIn L) 174 _ _ cfgV _
    (by decide) (hcode _ _ _ (hsel (x, col) (leafSalt cfgV salt)) hw)
  rw [hv]
  unfold leafAtH _root_.Fmt.leafBytes
  rw [h1, h2, hs]
  rfl

end

/-! ## At `implArmD` -/

section
variable {I0 X0 I2 X2 : Type} (L0 : _root_.Iop.BatchProtocol I0 X0) (L2 : BatchProtocolWithLeafBody I2 X2)
  (p0 p1 : PlainPart (shapeOf L2 .test) (annOf L2 .test))
  (isP0 isP1 : PlainPart (shapeOf L2 .test) (annOf L2 .test) → Bool) (cfgL : List (Dig 256)) (sh : Bits)
  (hp0 : ∀ p, isP0 p = true ↔ p = p0) (hp1 : ∀ p, isP1 p = true ↔ p = p1) (rest : ByteArray)
  (K : ℕ) (l : ℕ) (hlt : l < 2 ^ 48) (hne : l ≠ _root_.Fmt.recordLabel)
  (f0 : PCode (FbIn 256 L2 .link)) (h0 : ∀ q s, f0.put q = some s → Is160 l s)
  (F : FbPair (strung L0) L2) (pR : PCode (FbIn 256 (strung L0) .link × Fin (K + 1)))
  (hR : ∀ x s, pR.put x = some s → Is162 l s) (G : LeafPair (strung L0) L2) (nb : ℕ)
  (cfgV cfg : ByteArray) (hcfg : cfg.size = 32) (back : StrCode (AllPts 256 K L2))
  (g : Fam (rom 256))

/-- **The law at vertices.** -/
theorem nodeLaw_armD :
    NodeLaw (famG (pageArmD L2 p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K l hlt hne f0 h0 F pR hR G
      (KeyLeaves.leavesAt L0 nb cfgV) cfg hcfg back) g)
      (fun a b => hOfG g 166 0 0 cfg (a ++ b)) :=
  al_node _ g cfg fun a b ha hb =>
    armD_code_node L2 p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K l hlt hne f0 h0 F pR hR G
      (KeyLeaves.leavesAt L0 nb cfgV) cfg hcfg back (a, b) _
      (by rw [← pNodeAt_166]; exact pNodeAt_put 166 cfg a b ha hb) 0

/-- **`ownOkE_of_read`'s `hleaf`.** -/
theorem ownLeaf_armD (sB : ℕ) (hn : nb = 8 * sB) (e2 : Enc1 (Body L2)) (s : _root_.Fmt.Shape)
    (h1 : s.stored = false) (hp : _root_.Fmt.leafPlace s.tree s.W (sB / 8) < 2 ^ 48)
    (ha : 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64) (run : ByteArray) (hrun : run.size = 32)
    (hsel : ∀ (x : Fin (2 ^ s.a)) (sym : Fin s.W → UInt64) (z : Bits),
      G.sel ⟨e2 s x sym, z⟩ = some ⟨spell2 164 (_root_.Fmt.leafPlace s.tree s.W (sB / 8),
        2 ^ s.a + x.val, _root_.Fmt.colBytes (List.ofFn sym) ++
          _root_.Fmt.zeroBytes (_root_.Fmt.fillLen s.W sB)), z⟩) :
    ∀ (x : Fin (2 ^ s.a)) (sym : Fin s.W → UInt64) (salt : ByteArray), salt.size = sB →
      (famG (pageArmD L2 p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K l hlt hne f0 h0 F pR hR G
      (KeyLeaves.leavesAt L0 nb cfgV) cfg hcfg back) g .leaf
          (⟨e2 s x sym, leafSalt run salt⟩ : LeafIn L2) : Dig 256) =
        bytesToDig (leafAtH (hOfG g) s run x.val (List.ofFn sym) salt) :=
  al_own _ g L0 nb cfgV G.sel (fun q2 q1 z h hs =>
    armD_code_leaf L2 p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K l hlt hne f0 h0 F pR hR G
      (KeyLeaves.leavesAt L0 nb cfgV) cfg hcfg back q2 q1 h z hs 0)
    sB hn e2 s h1 hp ha run hrun hsel

/-- **`stoOkE_of_read`'s `hleaf`.** -/
theorem stoLeaf_armD (sB : ℕ) (c : StrCode (ℕ × List UInt64)) (hn : nb = 8 * sB)
    (embE2 : SgX → Body L2) (s : _root_.Fmt.Shape) (h1 : s.stored = true) (h2 : s.tree = 0)
    (hW : s.W < 2 ^ 24) (ha : 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64) (h8 : sB / 8 < 2 ^ 8)
    (hcV : cfgV.size = 32)
    (hsel : ∀ (y : SgX) (z : Bits), G.sel ⟨embE2 y, z⟩ = some ⟨embX s.a sB c y, z⟩) :
    ∀ (x : ℕ) (col : List UInt64) (salt : ByteArray), x < 2 ^ s.a → col.length = s.W →
      salt.size = sB →
      (famG (pageArmD L2 p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K l hlt hne f0 h0 F pR hR G
      (KeyLeaves.leavesAt L0 nb cfgV) cfg hcfg back) g .leaf
          (⟨embE2 (x, col), leafSalt cfgV salt⟩ : LeafIn L2) : Dig 256) =
        bytesToDig (leafAtH (hOfG g) s cfgV x col salt) :=
  al_sto _ g L0 nb cfgV G.sel (fun q2 q1 z h hs =>
    armD_code_leaf L2 p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K l hlt hne f0 h0 F pR hR G
      (KeyLeaves.leavesAt L0 nb cfgV) cfg hcfg back q2 q1 h z hs 0)
    sB c hn embE2 s h1 h2 hW ha h8 hcV hsel

end

end TypedOracleCompiler.Run.ArmLaws
