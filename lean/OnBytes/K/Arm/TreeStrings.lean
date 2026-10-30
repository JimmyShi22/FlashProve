-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
`OnBytes/K/Arm/TreeStrings.lean`: the library's encoding of typed hash queries spells the two kinds
of query that make up a stored table's hash tree exactly as the file format does.

States. m is the encoding `implL2` with `KeyLeaves.leavesAt`: the one through which `wordOf`
(Johnson/Top/OnFilesArmsCD.lean) reads.
`implL2_vertex`: m spells a query at an inner node as the bits of `Fmt.oStr 0 166 0 0 cfg (u ++ v)`.
`implL2_stored_leaf`: m spells a query at a bottom node (one column of a stored table) as the bits
of `Fmt.oStr 0 174 ..` with the column's bytes, the fill and the salt.
`vertexW_asks`, `leafW_asks`, `vertexW_code`, `leafW_code`: the format's routines `Fmt.vertexW` and
`Fmt.leafW`, run over one oracle, each make one query, at these strings.
`implL2_dec_vertex`, `implL2_dec_stored_leaf`: m reads these strings back as these typed queries.
Under. Eight hypotheses by name: hn (nb = 8 k), hy (`storedOK a k y`: ranges), h0 (the salt has k
bytes), hb (bd reads the typed query's body b as the column's string), hu, hv (256 bits each), hl,
hr (32 bytes each); beside the seven that m itself takes as arguments.
Does not show.
  1. Anything about the queries that a check makes: they are in no list of queries of the soundness
     game.
  2. That a file's check calls only these two routines for such a tree, at this cfg and k: that is
     read off the engine's text, not proved.
  3. Anything on the bottom nodes of the trees of a single run (hash-call tag 164).
  4. What `extEnc` returns over a list of queries: see TreeWord.lean.
  5. More than one salt length k and one 32-byte prefix cfg: at others m uses an escape code.
  6. As which typed query m reads the format's string at another salt length or prefix.
  7. Anything at a fixed depth a: it is a free variable; whoever reads a body does so at one depth.
  8. Anything on soundness.
  9. Anything about a program: the file is for proofs only, and no program imports it.
Notes in full, with every limit at length, stand at the end of this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Arm.AgreeArm
import OnBytes.K.Arm.LeafWrites
import OnBytes.Maker.Page.LeafTakenAt
import Rom.ExitDown

set_option autoImplicit false

namespace OnBytes.K.Arm
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.PageOf TypedOracleCompiler.Run.SeedPage
open TypedOracleCompiler.Run.EntryFb TypedOracleCompiler.Slice.EntryFill
open TypedOracleCompiler.Run.LinkAlong TypedOracleCompiler.Run.LinkAlongM
open TypedOracleCompiler.Slice.ArmRead TypedOracleCompiler.Slice.ArmLinkCode
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD)
open OnBytes.Slice (seedEntry)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

variable {lg s : ℕ} (D : XD) (d₁ : Sd1 lg s) (cfg : ByteArray) (hcfg : cfg.size = 32)
  (pd : Dig 256) (rest1 : ByteArray) (nb : ℕ)
  {I2 X2 : Type} (L2 : BatchProtocolWithLeafBody I2 X2)
  (pbF : PlainPart (shapeOf L2 .link) (annOf L2 .link) ≃
    PlainPart (shapeOf (Ls D d₁) .link) (annOf (Ls D d₁) .link))
  (bd : L2.Bd ≃ (Ls D d₁).Bd)
  (p0 p1 : PlainPart (shapeOf L2 .test) (annOf L2 .test))
  (isP0 isP1 : PlainPart (shapeOf L2 .test) (annOf L2 .test) → Bool) (cfgL : List (Dig 256)) (sh : Bits)
  (hp0 : ∀ p, isP0 p = true ↔ p = p0) (hp1 : ∀ p, isP1 p = true ↔ p = p1) (rest : ByteArray)
  (isPL : PlainPart (shapeOf L2 .link) (annOf L2 .link) → Bool)
  (hpL : ∀ p, isPL p = true ↔
    p = pbF.symm (p0E D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s)))
  {An : Type} (cA : An → List (Dig 256)) (tr : An → List T3) (hinj : Function.Injective cA)
  (hlen : ∀ a a', (cA a).length = (cA a').length) (htr : Function.Injective tr)
  (K : ℕ) (back : StrCode (AllPts 256 K L2))

/-- The encoding, for short. -/
local notation "mE" =>
  implL2 D d₁ cfg hcfg pd rest1 (KeyLeaves.leavesAt (L0 D d₁) nb cfg) L2 pbF bd p0 p1 isP0 isP1 cfgL
    sh hp0 hp1 rest isPL hpL cA tr hinj hlen htr K back

/-- The page of which it is the encoding. -/
local notation "pE" =>
  pageL2 D d₁ cfg hcfg pd rest1 (KeyLeaves.leavesAt (L0 D d₁) nb cfg) L2 pbF bd p0 p1 isP0 isP1 cfgL
    sh hp0 hp1 rest isPL hpL cA tr hinj hlen htr K back

/-- **A vertex query's string is the format's.** -/
theorem implL2_vertex (u v : Bits) (hu : u.length = 256) (hv : v.length = 256)
    (j : Fin ((mE).blocks .node)) :
    (mE).code .node (u, v) j =
      bytesToBits (_root_.Fmt.oStr 0 166 0 0 cfg (bitsToBytes u ++ bitsToBytes v)) :=
  totalG_real pE (.inr (.inl (u, v))) _ (_root_.Run.pNode_put cfg u v hu hv)

/-- **The string of a leaf query at a stored table's symbol is the format's.** -/
theorem implL2_stored_leaf (k : ℕ) (hn : nb = 8 * k) (a : ℕ) (y : ℕ × List UInt64)
    (hy : TypedOracleCompiler.Run.storedOK a k y) (s0 : ByteArray) (h0 : s0.size = k) (b : L2.Bd)
    (hb : bd b = TypedOracleCompiler.Run.storedStr a k y)
    (j : Fin ((mE).blocks .leaf)) :
    (mE).code .leaf ⟨b, bytesToBits cfg ++ bytesToBits s0⟩ j =
      bytesToBits (_root_.Fmt.oStr 0 174 (_root_.Fmt.leafPlace 0 y.2.length (k / 8)) (2 ^ a + y.1)
        cfg (_root_.Fmt.colBytes y.2 ++ _root_.Fmt.zeroBytes (_root_.Fmt.fillLen y.2.length k) ++
          s0)) := by
  obtain ⟨t, ht⟩ := leafCode_sto (L0 D d₁) nb cfg k hn a y hy s0 hcfg h0
  obtain ⟨c, -, e⟩ := KeyLeaves.leafCode_str (L0 D d₁) nb cfg k hn _ t ht
  have hc := OnBytes.Maker.Page.leafCall_stored a k y hy cfg s0 hcfg
  rw [OnBytes.Flat.embStored_fit a k y hy] at hc
  have e2 := OnBytes.Maker.Page.agrees_leavesAt (L0 D d₁) nb k hn cfg
    ⟨TypedOracleCompiler.Run.storedStr a k y, bytesToBits cfg ++ bytesToBits s0⟩ t ht _ hc
  have e3 : t = bytesToBits (bitsToBytes t) := by
    rw [e, bitsToBytes_bytesToBits]
  rw [e2] at e3
  have hp : (pE).real.put
      (.inl ⟨b, bytesToBits cfg ++ bytesToBits s0⟩) = some t :=
    (leavesAlong_put (leafM (Ls D d₁) L2 bd) (KeyLeaves.leavesAt (L0 D d₁) nb cfg)
      ⟨b, bytesToBits cfg ++ bytesToBits s0⟩
      ⟨TypedOracleCompiler.Run.storedStr a k y, bytesToBits cfg ++ bytesToBits s0⟩
      (by show some _ = some _; rw [hb])).trans ht
  exact (totalG_real _ _ t hp).trans e3

/-- The format's routine for a vertex, at the hash that asks the one oracle. -/
theorem vertexW_asks (l r : ByteArray) :
    _root_.Fmt.vertexW (_root_.Fmt.HM askB) cfg l r =
      askB (_root_.Fmt.oStr 0 166 0 0 cfg (l ++ r)) :=
  rfl

/-- The format's routine for a leaf of a stored table's tree, at that hash. -/
theorem leafW_asks (a x : ℕ) (col : List UInt64) (s0 : ByteArray) :
    _root_.Fmt.leafW (_root_.Fmt.HM askB) (_root_.Fmt.leafNo true) 0 a x cfg col s0 =
      askB (_root_.Fmt.oStr 0 174 (_root_.Fmt.leafPlace 0 col.length (s0.size / 8)) (2 ^ a + x) cfg
        (_root_.Fmt.colBytes col ++ _root_.Fmt.zeroBytes (_root_.Fmt.fillLen col.length s0.size) ++
          s0)) :=
  rfl

/-- **The format's routine for a vertex asks the encoding's string of the typed vertex query.** -/
theorem vertexW_code (l r : ByteArray) (hl : l.size = 32) (hr : r.size = 32)
    (j : Fin ((mE).blocks .node)) :
    _root_.Fmt.vertexW (_root_.Fmt.HM askB) cfg l r =
      .query ((mE).code .node (bytesToBits l, bytesToBits r) j) fun d => .pure (digToBytes d) := by
  rw [implL2_vertex D d₁ cfg hcfg pd rest1 nb L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest isPL
    hpL cA tr hinj hlen htr K back _ _ (by rw [length_bytesToBits, hl])
    (by rw [length_bytesToBits, hr]) j, bitsToBytes_bytesToBits, bitsToBytes_bytesToBits]
  rfl

/-- **The format's routine for a stored leaf asks the encoding's string of the typed leaf
query.** -/
theorem leafW_code (k : ℕ) (hn : nb = 8 * k) (a : ℕ) (y : ℕ × List UInt64)
    (hy : TypedOracleCompiler.Run.storedOK a k y) (s0 : ByteArray) (h0 : s0.size = k) (b : L2.Bd)
    (hb : bd b = TypedOracleCompiler.Run.storedStr a k y)
    (j : Fin ((mE).blocks .leaf)) :
    _root_.Fmt.leafW (_root_.Fmt.HM askB) (_root_.Fmt.leafNo true) 0 a y.1 cfg y.2 s0 =
      .query ((mE).code .leaf ⟨b, bytesToBits cfg ++ bytesToBits s0⟩ j)
        fun d => .pure (digToBytes d) := by
  rw [implL2_stored_leaf D d₁ cfg hcfg pd rest1 nb L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest
    isPL hpL cA tr hinj hlen htr K back k hn a y hy s0 h0 b hb j, leafW_asks, h0]
  rfl

/-- The encoding reads the format's string of a vertex back as the typed query. -/
theorem implL2_dec_vertex (u v : Bits) (hu : u.length = 256) (hv : v.length = 256)
    (j : Fin ((mE).blocks .node)) :
    (mE).dec
        (bytesToBits (_root_.Fmt.oStr 0 166 0 0 cfg (bitsToBytes u ++ bitsToBytes v))) =
      ⟨OracleName.node, (u, v), j⟩ := by
  rw [← implL2_vertex D d₁ cfg hcfg pd rest1 nb L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest isPL
    hpL cA tr hinj hlen htr K back u v hu hv j]
  exact OracleCoding.dec_code mE OracleName.node (u, v) j

/-- **The encoding reads the format's string of a stored leaf back as the typed query.** -/
theorem implL2_dec_stored_leaf (k : ℕ) (hn : nb = 8 * k) (a : ℕ) (y : ℕ × List UInt64)
    (hy : TypedOracleCompiler.Run.storedOK a k y) (s0 : ByteArray) (h0 : s0.size = k) (b : L2.Bd)
    (hb : bd b = TypedOracleCompiler.Run.storedStr a k y)
    (j : Fin ((mE).blocks .leaf)) :
    (mE).dec
        (bytesToBits (_root_.Fmt.oStr 0 174 (_root_.Fmt.leafPlace 0 y.2.length (k / 8))
          (2 ^ a + y.1) cfg (_root_.Fmt.colBytes y.2 ++
            _root_.Fmt.zeroBytes (_root_.Fmt.fillLen y.2.length k) ++ s0))) =
      ⟨OracleName.leaf, ⟨b, bytesToBits cfg ++ bytesToBits s0⟩, j⟩ := by
  rw [← implL2_stored_leaf D d₁ cfg hcfg pd rest1 nb L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest
    isPL hpL cA tr hinj hlen htr K back k hn a y hy s0 h0 b hb j]
  exact OracleCoding.dec_code mE OracleName.leaf ⟨b, bytesToBits cfg ++ bytesToBits s0⟩ j

end OnBytes.K.Arm

/-
Notes in full (other files' comments call these notes "the head of" this file).

OnBytes/K/Arm/TreeStrings.lean: the entry file's arm's encoding (`implL2`,
OnBytes/TypedOracleCompiler/Slice/ArmRead.lean) writes a typed query at a vertex, and at a leaf of a stored table's
tree, as THE FORMAT's OWN STRING of that vertex's and that leaf's hash call; so what the format's
routines ask for such a tree are that encoding's strings, and the encoding reads them back as these
typed queries. Statements and proofs.

Why. The word under a root is read off a log of strings through one encoding (`extEnc` over
`singleTr`; Johnson/Top/Pub/). A committer that hashes a stored table's tree by the format's own
routines leaves these strings in its log, the log off which the word is read. (A check asks the same
strings at the opened columns; its queries stand in no log of the game.) Whether the encoding reads
these strings as the tree's typed queries is a question on strings: here it is answered for the two
kinds of query of which a tree is made.

m stands for `implL2 D d₁ cfg hcfg pd rest1 (KeyLeaves.leavesAt (L0 D d₁) nb cfg) L2 .. K back`: the
encoding with the code of leaf queries over strings of bits. The arm's own coding is that by
abbreviation (`mAtP`, Johnson/Top/Pub/ArmOther.lean), at `cfg := (entryXD G c).base.cfg`, which is c
(`entryXD_cfg`, OnBytes/TypedOracleCompiler/Slice/EntryDesc.lean).

Main theorems.
  `implL2_vertex`: at two strings of 256 bits: `m.code .node (u, v) j` is the bits of
    `Fmt.oStr 0 166 0 0 cfg (u ++ v)`.
  `implL2_stored_leaf`: at a body that bd reads as the string of a stored table's symbol y
    (`storedStr a k y`, OnBytes/TypedOracleCompiler/Run/Tag174.lean) and the typed salt "cfg, then s0":
    `m.code .leaf .. j` is the bits of `Fmt.oStr 0 174 (leafPlace 0 W (k / 8)) (2 ^ a + x) cfg
    (the column's bytes, the fill, s0)`.
  `vertexW_asks`, `leafW_asks`: the format's routines `Fmt.vertexW` and `Fmt.leafW` under 174
    (Fmt/Rules7.lean), at the hash that asks the one oracle (`Fmt.HM Run.askB`), are one query at
    these strings. By unfolding.
  `vertexW_code`, `leafW_code`: so they are one query at m's strings.
  `implL2_dec_vertex`, `implL2_dec_stored_leaf`: m reads the format's strings back as these typed
    queries (`OracleCoding.dec`, Rom/ExitDown.lean: the term that `singleTr` calls).
The first two are the library's laws on a page's encoding (`totalG_real`,
OnBytes/TypedOracleCompiler/Run/PageG.lean) at what the page's two partial codes write (`Run.pNode_put`;
`leafCode_sto`, `leafCode_str`, `agrees_leavesAt`, `leafCall_stored`).
What is asked, by name: hn : nb = 8 k; hy : `storedOK a k y` (the position, the width and the place
are in range); h0 : s0 has k bytes; hb : how bd reads the body; hu, hv: 256 bits.

What is not claimed. That a check of a file calls these two routines alone for a stored tree, at
this cfg and at salts of k bytes: that is a reading of the engine's text
(OnBytes/ChecksWithHashAsArgument/M/Chain/EngineM.lean). The leaves of a run's own trees (number 164). What `extEnc`
returns over any log (OnBytes/K/Arm/TreeWord.lean). ONE length k of salts and ONE start cfg: at
another the code of leaves writes nothing, and m's string is the total code's behind an escape; as
which typed point m reads the FORMAT's string at another length or start is said nowhere. The depth
a is a letter here; whoever reads a body back as a symbol does so at one depth. Nothing on
soundness. For proofs only; the program does not import this file.

Terms: lean/GLOSSARY.md.

-/
