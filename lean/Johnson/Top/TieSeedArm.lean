-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/TieSeedArm.lean: the two seeds' fields of `EntryPart` (OnBytes/K/Parts.lean) at the
shape of an `ArmIn` (Johnson/Top/TieArm.lean) whose coding and seeds' wire are written.

Main names:
  `s0At W S0 cfg sh`: the seeds' wire S0 with the typed pieces of a table's name at a digest cfg of
    the public files and a shape sh of the tables: cfg as the one digest behind the root, and sh's
    six words as bits (OnBytes/TypedOracleCompiler/Run/SeedVals.lean).
  `armOf`: the `ArmIn` with: Sd := `sdTest W (s0At W S0 cfg sh) p0 p1` (the tag of Test;
    Johnson/Top/TieSeedSpelt.lean); m := `implArmD` (OnBytes/TypedOracleCompiler/Run/ArmDirect.lean) over the
    carrier, at the wire's own number of digests W.K, at the same plain parts p0, p1 and the same
    typed pieces of a name, and at the bytes `restOf sh cfg` behind the root in a table's name. The
    link's codes and the leaves' code in m, which statements are served and how a table is read as
    a record are letters.
  `seedsOK_arm`: `SeedsOK` (Johnson/Top/TieSeedHoles.lean) at these terms.
  `RecIsProgram`: what is asked of Served and recOf: where the program says yes on a served
    statement, both tables are read as records, and each record's seed is `toSeed` of what the
    program's own `recordSeeds` returns, in the field f, at the table's name under sh and cfg.
    It is shown of `recOfArm` and `servedArm` (OnBytes/K/ArmLetters.lean) in
    Johnson/Top/TieSeedRec.lean (`recIsProgram_arm`); here it is a hypothesis.
  `seed0_arm`, `seed1_arm`: the two fields at `(armOf …).shape`, to the letter.

Asked: (wire) S0's seed is `toSeed` of the program's own draws on the digests, in f, at sh; (room)
W.K digests are enough; cfg has 32 bytes; W.K is below 2 ^ 48; `RecIsProgram`.

Limits: the field `link` is not spoken of. Nothing on how seeds are distributed; nothing on
soundness (index binding included), opening-form binding, no two openings, correctness of extraction
or whatever else names a committer or a prover.

-/
import Johnson.Top.TieArm
import Johnson.Top.TieSeedHoles
import Johnson.Top.TieSeedSpelt
import OnBytes.TypedOracleCompiler.Run.SeedVals

set_option autoImplicit false

noncomputable section

namespace OnBytes.K

open _root_.Compile TypedOracleCompiler.Iop Rom TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (bytesToDig digToBytes bitsToBytes)
open _root_.Run (oBits PCode)
open TypedOracleCompiler.Run.Apart TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.SeedPage
open TypedOracleCompiler.Run.LinkAlong TypedOracleCompiler.Run.ArmDirect

variable {I X : Type} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
  (W : QueryLayout 256 (typedOracleCarrier L Bd aT aL)) (S0 : OutOfDomainSampleQueryLayout 256 W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig 256)) (f : Fmt.Fld) (cfgP : ByteArray) (sh : Params.IndexShape)
  (toSeed : List (List E × E) → L.OutOfDomainSeed) (Served : UserStm → Prop)
  (recOf : UserStm → Params.TableName → Option L.Rec) {I1 X1 : Type} {L1 : BatchProtocolWithLeafBody I1 X1}
  (p0 p1 : PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) .test) (annOf (typedOracleCarrier L Bd aT aL) .test))
  (isP0 isP1 : PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) .test) (annOf (typedOracleCarrier L Bd aT aL) .test) → Bool)
  (hp0 : ∀ p, isP0 p = true ↔ p = p0) (hp1 : ∀ p, isP1 p = true ↔ p = p1)
  (l : ℕ) (hlt : l < 2 ^ 48) (hne : l ≠ Fmt.recordLabel)
  (f0 : PCode (FbIn 256 (typedOracleCarrier L Bd aT aL) .link))
  (h0 : ∀ q s, f0.put q = some s → Is160 l s) (F : FbPair L1 (typedOracleCarrier L Bd aT aL))
  (pR : PCode (FbIn 256 L1 .link × Fin (W.K + 1))) (hR : ∀ x s, pR.put x = some s → Is162 l s)
  (G : LeafPair L1 (typedOracleCarrier L Bd aT aL)) (V : Leaves L1) (cfg : ByteArray) (hcfg : cfg.size = 32)
  (back : StrCode (AllPts 256 W.K (typedOracleCarrier L Bd aT aL)))

/-- The seeds' wire with the typed pieces of a table's name at a digest and a shape. -/
def s0At : OutOfDomainSampleQueryLayout 256 W.K L Bd aT aL :=
  { S0 with
    cfg := TypedOracleCompiler.Run.SeedVals.cfgL cfgP
    shape := TypedOracleCompiler.Run.SeedVals.shapeBits sh.code.logN sh.code.ell sh.code.r sh.v sh.answers
      sh.saltBytes }

/-- The bytes behind the root in a table's name are fewer than 2 ^ 32, if the digest has 32 bytes.
-/
theorem rest_small (hc : cfgP.size = 32) : (restOf sh cfgP).size < 2 ^ 32 :=
  TypedOracleCompiler.Run.SeedVals.rest_small cfgP hc _ _ _ _ _ _

/-- The arm's input with a written coding, seeds' wire, test of "served" and reading of a table. -/
def armOf : ArmIn where
  I := I
  X := X
  L := L
  Bd := Bd
  aT := aT
  aL := aL
  W := W
  Sd := sdTest W (s0At W S0 cfgP sh) p0 p1
  cA := cA
  m := implArmD (typedOracleCarrier L Bd aT aL) p0 p1 isP0 isP1 (s0At W S0 cfgP sh).cfg
    (s0At W S0 cfgP sh).shape hp0 hp1 (restOf sh cfgP) W.K l hlt hne f0 h0 F pR hR G V cfg hcfg back
  Served := Served
  recOf := recOf

/-- What is asked of "served" and of the reading of a table: where the program says yes on a served
statement, both tables are read, and each record's seed is the typed form of what the program's own
`recordSeeds` returns at the name made of the table's root, cfgP and sh. cfgP and sh are fixed
letters: that name is the name under which the program of that run draws only where "served" pins
the run's three public files to files whose digest is cfgP and whose tables have the shape sh. -/
def RecIsProgram {Sd An : Type} (f : Fmt.Fld) (cfgP : ByteArray) (sh : Params.IndexShape)
    (toSeed : List (List E × E) → Sd) (Served : UserStm → Prop)
    (recOf : UserStm → Params.TableName → Option (Sd × An)) : Prop :=
  ∀ Fl o id table further, PortYesAt Fl id table further → Served (stmOf Fl o) →
    ∃ (l0 l1 : List (List E × E)) (c cj : Sd × An),
      recordSeeds f (Key.nameOf sh cfgP table) sh.cubeBits sh.answers = some l0 ∧
      recordSeeds f (Key.nameOf sh cfgP further) sh.cubeBits sh.answers = some l1 ∧
      recOf (stmOf Fl o) table = some c ∧ recOf (stmOf Fl o) further = some cj ∧
      c.1 = toSeed l0 ∧ cj.1 = toSeed l1

variable (wire : ∀ a, S0.seed a = toSeed (seedsOfDigs f sh.cubeBits sh.answers a))
  (room : nBlocks sh.cubeBits sh.answers ≤ W.K) (hc : cfgP.size = 32) (hK : W.K < 2 ^ 48)
  (hrec : RecIsProgram f cfgP sh toSeed Served recOf)

include wire room hc hK in
/-- What `seed_program` asks, at the written terms. -/
theorem seedsOK_arm :
    SeedsOK W (sdTest W (s0At W S0 cfgP sh) p0 p1)
      (readBlocks (implArmD (typedOracleCarrier L Bd aT aL) p0 p1 isP0 isP1 (s0At W S0 cfgP sh).cfg
        (s0At W S0 cfgP sh).shape hp0 hp1 (restOf sh cfgP) W.K l hlt hne f0 h0 F pR hR G V cfg
        hcfg back) oBits) f cfgP sh toSeed :=
  ⟨spelt_arm W (s0At W S0 cfgP sh) p0 p1 isP0 isP1 hp0 hp1 _ l hlt hne f0 h0 F pR hR G V cfg hcfg
    back (rest_small cfgP sh hc) hK, wire, room⟩

include wire room hc hK hrec in
/-- **`EntryPart.seed0`** at the shape of `armOf`. -/
theorem seed0_arm :
    ∀ Fl o id table further, o.id = some id → o.bits = 128 → PortYesAt Fl id table further →
      (armOf W S0 cA cfgP sh Served recOf p0 p1 isP0 isP1 hp0 hp1 l hlt hne f0 h0 F pR hR G V cfg
        hcfg back).shape.Served (stmOf Fl o) →
      ∃ c, (armOf W S0 cA cfgP sh Served recOf p0 p1 isP0 isP1 hp0 hp1 l hlt hne f0 h0 F pR hR G V
          cfg hcfg back).shape.recOf (stmOf Fl o) table = some c ∧
        (armOf W S0 cA cfgP sh Served recOf p0 p1 isP0 isP1 hp0 hp1 l hlt hne f0 h0 F pR hR G V cfg
          hcfg back).shape.seed0 (stmOf Fl o) (bytesToDig table.root) c = true :=
  fun Fl o id table further _ _ hp hs => by
    obtain ⟨l0, l1, c, cj, e0, -, r0, -, s0, -⟩ := hrec Fl o id table further hp hs
    obtain ⟨p, -, -, -, -, h0', -, -, -⟩ := port_recs Fl o id table further hp
    refine ⟨c, r0, ?_⟩
    show (outOfDomainSeedIs W (sdTest W (s0At W S0 cfgP sh) p0 p1) (bytesToDig table.root) c.1).det _ = true
    rw [s0]
    exact seed_program (seedsOK_arm W S0 f cfgP sh toSeed p0 p1 isP0 isP1 hp0 hp1 l hlt hne f0 h0 F
      pR hR G V cfg hcfg back wire room hc hK) table h0' hc l0 e0

include wire room hc hK hrec in
/-- **`EntryPart.seed1`** at the same shape. -/
theorem seed1_arm :
    ∀ Fl o id table further, o.id = some id → o.bits = 128 → PortYesAt Fl id table further →
      (armOf W S0 cA cfgP sh Served recOf p0 p1 isP0 isP1 hp0 hp1 l hlt hne f0 h0 F pR hR G V cfg
        hcfg back).shape.Served (stmOf Fl o) →
      ∃ c, (armOf W S0 cA cfgP sh Served recOf p0 p1 isP0 isP1 hp0 hp1 l hlt hne f0 h0 F pR hR G V
          cfg hcfg back).shape.recOf (stmOf Fl o) further = some c ∧
        (armOf W S0 cA cfgP sh Served recOf p0 p1 isP0 isP1 hp0 hp1 l hlt hne f0 h0 F pR hR G V cfg
          hcfg back).shape.seed1 (stmOf Fl o) (bytesToDig further.root) c = true :=
  fun Fl o id table further _ _ hp hs => by
    obtain ⟨l0, l1, c, cj, -, e1, -, r1, -, s1⟩ := hrec Fl o id table further hp hs
    obtain ⟨p, -, -, -, -, -, h1', -, -⟩ := port_recs Fl o id table further hp
    refine ⟨cj, r1, ?_⟩
    show (outOfDomainSeedIs W (sdTest W (s0At W S0 cfgP sh) p0 p1) (bytesToDig further.root) cj.1).det _ =
      true
    rw [s1]
    exact seed_program (seedsOK_arm W S0 f cfgP sh toSeed p0 p1 isP0 isP1 hp0 hp1 l hlt hne f0 h0 F
      pR hR G V cfg hcfg back wire room hc hK) further h1' hc l1 e1

end OnBytes.K
