-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/ArmWalksAt.lean: what the lax verifier's clause on the walks asks at an entry's
typed string, at the family of typed oracles that the encoding `implArmD` reads out of one oracle.

OnBytes/TypedOracleCompiler/Slice/ArmWalks.lean joins what `assembleS_walks` asks into one statement `Walks`, with
the family's three laws as hypotheses (`walks_at`). OnBytes/TypedOracleCompiler/Run/ArmLaws.lean shows these three
laws of the family that the page `pageArmD` (OnBytes/TypedOracleCompiler/Run/ArmCodes.lean) reads out of any oracle
g on bit strings. Here the two are put together: what stays a hypothesis does not look at the
family. For proofs only; the program does not import this file.

Main name.
 `walks_armD`: `Walks D (famG (pageArmD …) g) embS embE2 cms o`, for every oracle g, with the hash
   `hOfG g` made of the same oracle, and every number K of blocks. The page's digest, and the digest
   of its code of leaves, are the description's `D.base.cfg`.

What is asked.
 Of the bodies over the second interface: the chain's own symbols are written by one way e2, lifted
   (`hemb`); the map of leaf queries G reads `e2 s x sym` as the format's spelling of that leaf, and
   `embE2 y` as the line's body of the stored symbol y, and keeps the salt (`hselO`, `hselS`).
 Of what was read, opening by opening: the format's reader of an opening said yes (`ReadAs`); forms
   and roots under Fm and Rt; widths; the salts have sB bytes; the stored tables' depth and outer
   roots; bounds on forms; the run value has 32 bytes.
 Of the hash: its answers have the format's lengths (`hz`).

What is not claimed. None of these hypotheses at any file, description or pair of maps. Nothing on
the chain's queries. Nothing on soundness.


-/
import OnBytes.TypedOracleCompiler.Run.ArmLaws
import OnBytes.TypedOracleCompiler.Slice.ArmWalks

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice.ArmWalks
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.Apart TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.SeedPage
open TypedOracleCompiler.Run.SeedPoints TypedOracleCompiler.Run.LinkAlong TypedOracleCompiler.Run.LinkOf
open TypedOracleCompiler.Run.ArmDirect TypedOracleCompiler.Run.RowsG TypedOracleCompiler.Run.RowsE3 TypedOracleCompiler.Strings
open TypedOracleCompiler.Run.ArmLaws
open TypedOracleCompiler.Run.PQ (XD SOf)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run
open _root_.Run.PQ (SgX)

variable {I0 X0 I2 X2 : Type} (L0 : _root_.Iop.BatchProtocol I0 X0) (L2 : BatchProtocolWithLeafBody I2 X2) (D : XD)
  (p0 p1 : PlainPart (shapeOf L2 .test) (annOf L2 .test))
  (isP0 isP1 : PlainPart (shapeOf L2 .test) (annOf L2 .test) → Bool) (cfgL : List (Dig 256)) (sh : Bits)
  (hp0 : ∀ p, isP0 p = true ↔ p = p0) (hp1 : ∀ p, isP1 p = true ↔ p = p1) (rest : ByteArray)
  (l : ℕ) (hlt : l < 2 ^ 48) (hne : l ≠ _root_.Fmt.recordLabel)
  (f0 : PCode (FbIn 256 L2 .link)) (h0 : ∀ q s, f0.put q = some s → Is160 l s)
  (K : ℕ) (F : FbPair (strung L0) L2) (pR : PCode (FbIn 256 (strung L0) .link × Fin (K + 1)))
  (hR : ∀ x s, pR.put x = some s → Is162 l s) (G : LeafPair (strung L0) L2) (nb : ℕ)
  (hcfg : D.base.cfg.size = 32) (back : StrCode (AllPts 256 K L2)) (g : Fam (rom 256))

/-- The clause on the walks at `implArmD`'s family: only what is free of the family stays a
hypothesis. -/
theorem walks_armD (hz : ∀ n t i s b, ByteArray.size (hOfG g n t i s b) = _root_.Fmt.dlen n)
    {embS : (p : OPos (_root_.Run.Twin.up (SOf D.C D.ds))) →
      OSym (_root_.Run.Twin.up (SOf D.C D.ds)) p → Body L2}
    {e2 : Enc1 (Body L2)} (hemb : ∀ q a, embS (.inr q) a = embLS D.C (liftT e2) D.ds q a)
    {Fm : ℕ → _root_.Fmt.Shape → Prop} {Rt : ℕ → Dig 256 → Prop} (hF : FormsOn Fm 0 D.ds)
    {o : _root_.Fmt.ChainOut} (hRt : RtsL Rt D.C 0 D.ds (PQ.rtSL D.C D.ds o.rounds.toList))
    {embE2 : SgX → Body L2} {cms : List (Dig 256)} (sB : ℕ) (hn : nb = 8 * sB)
    (c : StrCode (ℕ × List UInt64)) (h8 : sB / 8 < 2 ^ 8)
    (rdO : ∀ run, o.run = some run → ∀ op ∈ (opsOf 1 o).filter (fun op => !op.sh.stored),
      ReadAs (hOfG g) D.base.cfg run op)
    (hform : ∀ op ∈ (opsOf 1 o).filter (fun op => !op.sh.stored),
      ∀ n s, Fm n s → s.tree = op.sh.tree → s = op.sh)
    (hroot : ∀ op ∈ (opsOf 1 o).filter (fun op => !op.sh.stored),
      ∀ n s c, Fm n s → s.tree = op.sh.tree → Rt n c → c = bytesToDig op.out.root)
    (hsO : ∀ op ∈ (opsOf 1 o).filter (fun op => !op.sh.stored), ∀ sl ∈ op.out.salts, sl.size = sB)
    (hrun : ∀ run, o.run = some run → run.size = 32)
    (hbO : ∀ op ∈ (opsOf 1 o).filter (fun op => !op.sh.stored),
      _root_.Fmt.leafPlace op.sh.tree op.sh.W (sB / 8) < 2 ^ 48 ∧
        2 ^ op.sh.a + 2 ^ op.sh.a ≤ 2 ^ 64)
    (hselO : ∀ (s : _root_.Fmt.Shape) (x : Fin (2 ^ s.a)) (sym : Fin s.W → UInt64) (z : Bits),
      G.sel ⟨e2 s x sym, z⟩ = some ⟨spell2 164 (_root_.Fmt.leafPlace s.tree s.W (sB / 8),
        2 ^ s.a + x.val, _root_.Fmt.colBytes (List.ofFn sym) ++
          _root_.Fmt.zeroBytes (_root_.Fmt.fillLen s.W sB)), z⟩)
    (rdS : ∀ op ∈ (opsOf 1 o).filter (fun op => op.sh.stored),
      ReadAs (hOfG g) D.base.cfg D.base.cfg op)
    (hd : ∀ op ∈ (opsOf 1 o).filter (fun op => op.sh.stored), op.sh.a = D.a)
    (hr : ∀ op ∈ (opsOf 1 o).filter (fun op => op.sh.stored),
      cms.getD (whichOf D op) default = bytesToDig op.out.root)
    (hcS : ∀ op ∈ (opsOf 1 o).filter (fun op => op.sh.stored),
      ∀ c ∈ op.out.cols, c.length = op.sh.W)
    (hsS : ∀ op ∈ (opsOf 1 o).filter (fun op => op.sh.stored), ∀ sl ∈ op.out.salts, sl.size = sB)
    (hbS : ∀ op ∈ (opsOf 1 o).filter (fun op => op.sh.stored),
      op.sh.tree = 0 ∧ op.sh.W < 2 ^ 24 ∧ 2 ^ op.sh.a + 2 ^ op.sh.a ≤ 2 ^ 64)
    (hselS : ∀ (y : SgX) (z : Bits), G.sel ⟨embE2 y, z⟩ = some ⟨embX D.a sB c y, z⟩) :
    Walks D (famG (pageArmD L2 p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K l hlt hne f0 h0 F pR
      hR G (KeyLeaves.leavesAt L0 nb D.base.cfg) D.base.cfg hcfg back) g) embS embE2 cms o :=
  walks_at (h := hOfG g) hz
    (nodeLaw_armD L0 L2 p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K l hlt hne f0 h0 F pR hR G nb
      D.base.cfg D.base.cfg hcfg back g)
    hemb hF hRt sB rdO hform hroot hsO
    (fun run hr' op hop =>
      ownLeaf_armD L0 L2 p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K l hlt hne f0 h0 F pR hR G nb
        D.base.cfg D.base.cfg hcfg back g sB hn e2 op.sh
        (by simpa using (List.mem_filter.1 hop).2) (hbO op hop).1 (hbO op hop).2 run
        (hrun run hr') (hselO op.sh))
    rdS hd hr hcS hsS
    (fun op hop =>
      stoLeaf_armD L0 L2 p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K l hlt hne f0 h0 F pR hR G nb
        D.base.cfg D.base.cfg hcfg back g sB c hn embE2 op.sh
        (List.mem_filter.1 hop).2 (hbS op hop).1 (hbS op hop).2.1 (hbS op hop).2.2 h8 hcfg
        (by rw [hd op hop]; exact hselS))

end TypedOracleCompiler.Slice.ArmWalks
