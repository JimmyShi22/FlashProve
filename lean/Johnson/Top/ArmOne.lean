-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/ArmOne.lean: the input of the entry's arm with one digest and one record's wire, so that
the tie of the seeds' tests and the arm's bound speak of the same terms.

Johnson/Top/TieSeedSizes.lean shows the two seeds' fields of `EntryPart` at `(armFull …).shape`.
Johnson/Flat/ArmSibClosed.lean bounds the chance that `armL` says yes while what it promises fails.
The two were not in the same letters. `armFull` has two digests as two letters (cfgP, in the tables'
names; cfg, in the leaves' code of the coding), five letters of the record's wire that `armOf`
overwrites, and a free code of the answers. The bound is at `sdAtFull` at any tag, typed pieces and
plain parts, and at the code `cAAtFull`.

Main names (Small for Full at the small example).
 `digest_size`        the digest of a description's three public files has 32 bytes.
 `oneSd_full`         what `armOf` lays as the seeds' data over `sdAtFull … t cfgD shape pl0 pl1 …`
                      is `sdAtFull … .test (cfgL cfgP) (shapeBits …) p0 p1 …`: by definition.
 `armFullAt`          `armFull` at one Z : Pub: Z.digest in both places, the record's wire laid at
                      once at these values, the answers' code `cAAtFull T`.
 `armFullAt_W`, `armFullAt_Sd`, `armFullAt_cA`   its wire, seeds' data and answers' code are those
                      of the bound: by definition.
 `seed0_fullAt`, `seed1_fullAt`   the two fields at `(armFullAt …).shape`; the digest's size is
                      paid.
 `lax_closed_fullAt`  the bound `atFull_lax_closed`, stated in the fields of `armFullAt …`: its W,
                      Sd, cA and m.

Asked, in the two fields: hF : K + 1 < 2 ^ 48 and `RecIsProgram` at Z.digest. In the bound:
`BCHKS46At GF GE`; T's decoder and collisions are the configuration's; K is at least the
description's number of blocks; `wB.ext.OK`; the maker's bound. In both: hE, and the laws of the
coding's letters that `armOf` takes.

Limits: those of the two files. The bound is over a random function and the two fields are at Lean's
BLAKE2b: they are composed nowhere here. wT and wB are letters: no value of them is written. Nothing
on the field `link`.


-/
import Johnson.Top.TieSeedSizes
import OnBytes.K.ArmLetters

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.K
open _root_.Compile TypedOracleCompiler.Iop Rom TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open Hiop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (bytesToDig PCode ckP)
open TypedOracleCompiler.Run.Apart TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.SeedPage
open TypedOracleCompiler.Run.LinkAlong TypedOracleCompiler.Run.ArmDirect
open TypedOracleCompiler.Run.SeedVals (cfgL shapeBits)
open OnBytes.Slice OnBytes.Flat Cb Cb.Ood
open OnBytes.RunA (RestR LrG)
open TypedOracleCompiler.Run.PQ (SOf)
open OnBytes.Tie (recordGround smallRecordGround)
open TypedOracleCompiler.Slice (seedOfC entryXD)

/-- The digest of a description's three public files has 32 bytes. -/
theorem digest_size (Z : Pub) : Z.digest.size = 32 := Params.configurationDigest_size _

section Full
variable {X X' RI : Type} [Fintype RI] [Nonempty RI] {A : (frS.toDecR frZ 402653181).Claims X}
  {R : (frS.toDecR frZ 402653181).RelationsAndEncoding A}
  (T : RestR (DecR.configurationOfStoredTable A R).I X' RI (Fin 1 → (Fin 29 → GE) × NZ)
    ((Fin frS.P.v → Bool) × Fin 1 → GE) frS.P.T.a linkSibFull)
  (K : ℕ) (hE : (seedBS recLg recS).b ≤ K + 1) (hF : K + 1 < 2 ^ 48) {aT : RoundSplits T.test.shape}
  (wT : ProtocolQueryLayout 256 (K + 1) (batTC (LrG T) aT))
  (wB : ProtocolQueryLayout 256 (K + 1) T.bat) (depthReq depthReqT salt : ℕ)
  (embT : (p : OPos T.test.shape) → OSym T.test.shape p → List Bool)
  (prjT : (p : OPos T.test.shape) → List Bool → Option (OSym T.test.shape p))
  (embB : (p : OPos T.bat.loc.shape) → OSym T.bat.loc.shape p → List Bool)
  (prjB : (p : OPos T.bat.loc.shape) → List Bool → Option (OSym T.bat.loc.shape p))
  (code : (LrG T).Rec → List (Dig 256)) (num : ℕ → Plains T.bat.loc.shape → Bool)
  (dS : DecidableEq (Fin 1 → (Fin 29 → GE) × NZ))

/-- **One record's wire, at any wire W and any shape of the tables.** What `armOf` lays as the
seeds' data over `sdAtFull` at any tag, typed pieces and plain parts is `sdAtFull` at the tag of
Test, the typed pieces of a table's name at cfgP and sh, and the plain parts p0, p1. -/
theorem oneSd_full (Bd : Type)
    (W : QueryLayout 256 (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))))
    (t : Tag) (cfgD : List (Dig 256)) (shape : Bits)
    (pl0 pl1 : PlainPart (shapeOf (typedOracleCarrier (LrG T) Bd aT
               (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) t)
      (annOf (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) t))
    (h : (seedBS recLg recS).b ≤ W.K) (cfgP : ByteArray) (sh : Params.IndexShape)
    (p0 p1 : PlainPart (shapeOf (typedOracleCarrier (LrG T) Bd aT
               (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) .test)
      (annOf (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) .test)) :
    sdTest W (s0At W (sdAtFull T Bd aT W t cfgD shape pl0 pl1 code num h dS) cfgP sh) p0 p1 =
      sdAtFull T Bd aT W .test (cfgL cfgP)
        (shapeBits sh.code.logN sh.code.ell sh.code.r sh.v sh.answers sh.saltBytes) p0 p1 code num
        h dS := rfl

variable (Z : Pub) (Served : UserStm → Prop)
  (recOf : UserStm → Params.TableName → Option (LrG T).Rec) {I1 X1 : Type} {L1 : BatchProtocolWithLeafBody I1 X1}
  (p0 p1 : PlainPart (shapeOf (typedOracleCarrier (LrG T) (List Bool) aT
             (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) .test)
    (annOf (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull)))
      .test))
  (isP0 isP1 : PlainPart (shapeOf (typedOracleCarrier (LrG T) (List Bool) aT
             (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) .test)
    (annOf (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull)))
      .test) → Bool)
  (hp0 : ∀ p, isP0 p = true ↔ p = p0) (hp1 : ∀ p, isP1 p = true ↔ p = p1)
  (l : ℕ) (hlt : l < 2 ^ 48) (hne : l ≠ Fmt.recordLabel)
  (f0 : PCode (FbIn 256 (typedOracleCarrier (LrG T) (List Bool) aT
    (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) .link))
  (h0 : ∀ q s, f0.put q = some s → Is160 l s)
  (F : FbPair L1 (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))))
  (pR : PCode (FbIn 256 L1 .link ×
    Fin ((wFull T K wT wB depthReq depthReqT salt embT prjT embB prjB).K + 1)))
  (hR : ∀ x s, pR.put x = some s → Is162 l s)
  (G : LeafPair L1 (typedOracleCarrier (LrG T) (List Bool) aT
    (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))))
  (V : Leaves L1)
  (back : StrCode (AllPts 256 (wFull T K wT wB depthReq depthReqT salt embT prjT embB prjB).K
    (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull)))))

/-- **The arm's input at one description's public files Z.** `armFull` with the digest of Z's three
files in both places where a digest stands (the tables' names; the leaves' code of the coding), the
record's wire laid at once at what `armOf` lays over it, and the answers' code of the arm's bound.
-/
abbrev armFullAt : ArmIn :=
  armFull T K hE wT wB depthReq depthReqT salt embT prjT embB prjB .test (cfgL Z.digest)
    (shapeBits recordGround.q.link.table.code.logN recordGround.q.link.table.code.ell
      recordGround.q.link.table.code.r recordGround.q.link.table.v
      recordGround.q.link.table.answers recordGround.q.link.table.saltBytes)
    p0 p1 code num dS (cAAtFull T) Z.digest Served recOf p0 p1 isP0 isP1 hp0 hp1 l hlt hne f0 h0 F
    pR hR G V Z.digest (digest_size Z) back

local notation "theArm" => armFullAt T K hE wT wB depthReq depthReqT salt embT prjT embB prjB code
  num dS Z Served recOf p0 p1 isP0 isP1 hp0 hp1 l hlt hne f0 h0 F pR hR G V back

/-- Its wire is the written wire with K + 1 blocks. -/
theorem armFullAt_W :
    (theArm).W = wAtFull T K wT wB depthReq depthReqT salt embT prjT embB prjB := rfl

/-- Its seeds' data are the record's wire of the arm's bound, at the tag of Test, the typed pieces
of a table's name at Z's digest and the ground's shape, and the plain parts p0, p1. -/
theorem armFullAt_Sd : (theArm).Sd =
    sdAtFull T (List Bool) aT (wAtFull T K wT wB depthReq depthReqT salt embT prjT embB prjB) .test
      (cfgL Z.digest)
      (shapeBits recordGround.q.link.table.code.logN recordGround.q.link.table.code.ell
        recordGround.q.link.table.code.r recordGround.q.link.table.v
        recordGround.q.link.table.answers recordGround.q.link.table.saltBytes)
      p0 p1 code num hE dS := rfl

set_option maxRecDepth 20000 in
/-- Its answers' code is that of the arm's bound. -/
theorem armFullAt_cA : (theArm).cA = cAAtFull T := rfl

variable (hrec : RecIsProgram recordGround.q.given.plan.field Z.digest recordGround.q.link.table
    (seedOfC recLg recS : List (List E × E) → (LrG T).OutOfDomainSeed) Served recOf)

include hF hrec in
/-- `EntryPart.seed0` at `armFullAt`: the digest's size is paid. -/
theorem seed0_fullAt :
    ∀ Fl o id table further, o.id = some id → o.bits = 128 → PortYesAt Fl id table further →
      (theArm).shape.Served (stmOf Fl o) →
      ∃ r, (theArm).shape.recOf (stmOf Fl o) table = some r ∧
        (theArm).shape.seed0 (stmOf Fl o) (bytesToDig table.root) r = true :=
  seed0_full T K hE hF wT wB depthReq depthReqT salt embT prjT embB prjB _ _ _ _ _ code num dS _ _
    Served recOf p0 p1 isP0 isP1 hp0 hp1 l hlt hne f0 h0 F pR hR G V _ _ back (digest_size Z) hrec

include hF hrec in
/-- `EntryPart.seed1` at `armFullAt`. -/
theorem seed1_fullAt :
    ∀ Fl o id table further, o.id = some id → o.bits = 128 → PortYesAt Fl id table further →
      (theArm).shape.Served (stmOf Fl o) →
      ∃ r, (theArm).shape.recOf (stmOf Fl o) further = some r ∧
        (theArm).shape.seed1 (stmOf Fl o) (bytesToDig further.root) r = true :=
  seed1_full T K hE hF wT wB depthReq depthReqT salt embT prjT embB prjB _ _ _ _ _ code num dS _ _
    Served recOf p0 p1 isP0 isP1 hp0 hp1 l hlt hne f0 h0 F pR hR G V _ _ back (digest_size Z) hrec

variable (hd : T.dcd = (DecR.configurationOfStoredTable A R).D) (hc : T.coll = (DecR.configurationOfStoredTable A R).coll)
  (hK : frD.K ≤ K) (hB : wB.ext.OK)

include hd hc hK hB in
set_option maxRecDepth 20000 in
/-- **The arm's bound in the letters of `armFullAt`**: `atFull_lax_closed`
(Johnson/Flat/ArmSibClosed.lean) at this input's own wire, seeds' data, answers' code and coding. -/
theorem lax_closed_fullAt (hA : BCHKS46At GF GE)
    (Mk : OComp (rom 256) (OutLA 256 (theArm).L (theArm).aL)) (tq : ℕ) (hq : Mk.QueryBound tq) :
    Rom.Pr (Mk.withTrace.bind fun o =>
        ((armL (theArm).W (theArm).Sd (theArm).cA o.1).overOne (theArm).m).bind fun b =>
          OComp.pure (o, b))
        (fun g => {x | x.2 = true ∧
          ¬ LinkHolds (theArm).W (logOne (theArm).W (armL (theArm).W (theArm).Sd (theArm).cA)
              (theArm).m
              (readBlocks (theArm).m g) x.1)
            x.1.1.1 x.1.1.2.1 x.1.1.2.2.1 x.1.1.2.2.2.1}) ≤
      (((tq + tVL (theArm).W) * (1 + 4) : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 128 +
        2 * (((tq + tVL (theArm).W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 :=
  atFull_lax_closed T K wT wB depthReq depthReqT salt embT prjT embB prjB hd hc hK hB .test _ _
    p0 p1 code num hE dS hA (theArm).m Mk tq hq

end Full

section Small
variable {X X' RI : Type} [Fintype RI] [Nonempty RI] {A : (srS.toDecR srZ 524285).Claims X}
  {R : (srS.toDecR srZ 524285).RelationsAndEncoding A}
  (T : RestR (DecR.configurationOfStoredTable A R).I X' RI (Fin 1 → (Fin 19 → GE) × NZ)
    ((Fin srS.P.v → Bool) × Fin 1 → GE) srS.P.T.a linkSibSmall)
  (K : ℕ) (hE : (seedBS 19 1).b ≤ K + 1) (hF : K + 1 < 2 ^ 48) {aT : RoundSplits T.test.shape}
  (wT : ProtocolQueryLayout 256 (K + 1) (batTC (LrG T) aT))
  (wB : ProtocolQueryLayout 256 (K + 1) T.bat) (depthReq depthReqT salt : ℕ)
  (embT : (p : OPos T.test.shape) → OSym T.test.shape p → List Bool)
  (prjT : (p : OPos T.test.shape) → List Bool → Option (OSym T.test.shape p))
  (embB : (p : OPos T.bat.loc.shape) → OSym T.bat.loc.shape p → List Bool)
  (prjB : (p : OPos T.bat.loc.shape) → List Bool → Option (OSym T.bat.loc.shape p))
  (code : (LrG T).Rec → List (Dig 256)) (num : ℕ → Plains T.bat.loc.shape → Bool)
  (dS : DecidableEq (Fin 1 → (Fin 19 → GE) × NZ))

/-- **One record's wire, at any wire W and any shape of the tables.** What `armOf` lays as the
seeds' data over `sdAtSmall` at any tag, typed pieces and plain parts is `sdAtSmall` at the tag of
Test, the typed pieces of a table's name at cfgP and sh, and the plain parts p0, p1. -/
theorem oneSd_small (Bd : Type)
    (W : QueryLayout 256 (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))))
    (t : Tag) (cfgD : List (Dig 256)) (shape : Bits)
    (pl0 pl1 : PlainPart (shapeOf (typedOracleCarrier (LrG T) Bd aT
               (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) t)
      (annOf (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) t))
    (h : (seedBS 19 1).b ≤ W.K) (cfgP : ByteArray) (sh : Params.IndexShape)
    (p0 p1 : PlainPart (shapeOf (typedOracleCarrier (LrG T) Bd aT
               (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) .test)
      (annOf (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) .test)) :
    sdTest W (s0At W (sdAtSmall T Bd aT W t cfgD shape pl0 pl1 code num h dS) cfgP sh) p0 p1 =
      sdAtSmall T Bd aT W .test (cfgL cfgP)
        (shapeBits sh.code.logN sh.code.ell sh.code.r sh.v sh.answers sh.saltBytes) p0 p1 code num
        h dS := rfl

variable (Z : Pub) (Served : UserStm → Prop)
  (recOf : UserStm → Params.TableName → Option (LrG T).Rec) {I1 X1 : Type} {L1 : BatchProtocolWithLeafBody I1 X1}
  (p0 p1 : PlainPart (shapeOf (typedOracleCarrier (LrG T) (List Bool) aT
             (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) .test)
    (annOf (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall)))
      .test))
  (isP0 isP1 : PlainPart (shapeOf (typedOracleCarrier (LrG T) (List Bool) aT
             (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) .test)
    (annOf (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall)))
      .test) → Bool)
  (hp0 : ∀ p, isP0 p = true ↔ p = p0) (hp1 : ∀ p, isP1 p = true ↔ p = p1)
  (l : ℕ) (hlt : l < 2 ^ 48) (hne : l ≠ Fmt.recordLabel)
  (f0 : PCode (FbIn 256 (typedOracleCarrier (LrG T) (List Bool) aT
    (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) .link))
  (h0 : ∀ q s, f0.put q = some s → Is160 l s)
  (F : FbPair L1 (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))))
  (pR : PCode (FbIn 256 L1 .link ×
    Fin ((wSmall T K wT wB depthReq depthReqT salt embT prjT embB prjB).K + 1)))
  (hR : ∀ x s, pR.put x = some s → Is162 l s)
  (G : LeafPair L1 (typedOracleCarrier (LrG T) (List Bool) aT
    (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))))
  (V : Leaves L1)
  (back : StrCode (AllPts 256 (wSmall T K wT wB depthReq depthReqT salt embT prjT embB prjB).K
    (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall)))))

/-- **The arm's input at one description's public files Z.** `armSmall` with the digest of Z's three
files in both places where a digest stands (the tables' names; the leaves' code of the coding), the
record's wire laid at once at what `armOf` lays over it, and the answers' code of the arm's bound.
-/
abbrev armSmallAt : ArmIn :=
  armSmall T K hE wT wB depthReq depthReqT salt embT prjT embB prjB .test (cfgL Z.digest)
    (shapeBits smallRecordGround.q.link.table.code.logN smallRecordGround.q.link.table.code.ell
      smallRecordGround.q.link.table.code.r smallRecordGround.q.link.table.v
      smallRecordGround.q.link.table.answers smallRecordGround.q.link.table.saltBytes)
    p0 p1 code num dS (cAAtSmall T) Z.digest Served recOf p0 p1 isP0 isP1 hp0 hp1 l hlt hne f0 h0 F
    pR hR G V Z.digest (digest_size Z) back

local notation "theArm" => armSmallAt T K hE wT wB depthReq depthReqT salt embT prjT embB prjB code
  num dS Z Served recOf p0 p1 isP0 isP1 hp0 hp1 l hlt hne f0 h0 F pR hR G V back

/-- Its wire is the written wire with K + 1 blocks. -/
theorem armSmallAt_W :
    (theArm).W = wAtSmall T K wT wB depthReq depthReqT salt embT prjT embB prjB := rfl

/-- Its seeds' data are the record's wire of the arm's bound, at the tag of Test, the typed pieces
of a table's name at Z's digest and the ground's shape, and the plain parts p0, p1. -/
theorem armSmallAt_Sd : (theArm).Sd =
    sdAtSmall T (List Bool) aT (wAtSmall T K wT wB depthReq depthReqT salt embT prjT embB prjB)
      .test (cfgL Z.digest)
      (shapeBits smallRecordGround.q.link.table.code.logN smallRecordGround.q.link.table.code.ell
        smallRecordGround.q.link.table.code.r smallRecordGround.q.link.table.v
        smallRecordGround.q.link.table.answers smallRecordGround.q.link.table.saltBytes)
      p0 p1 code num hE dS := rfl

set_option maxRecDepth 20000 in
/-- Its answers' code is that of the arm's bound. -/
theorem armSmallAt_cA : (theArm).cA = cAAtSmall T := rfl

variable (hrec : RecIsProgram smallRecordGround.q.given.plan.field Z.digest
    smallRecordGround.q.link.table (seedOfC 19 1 : List (List E × E) → (LrG T).OutOfDomainSeed) Served recOf)

include hF hrec in
/-- `EntryPart.seed0` at `armSmallAt`: the digest's size is paid. -/
theorem seed0_smallAt :
    ∀ Fl o id table further, o.id = some id → o.bits = 128 → PortYesAt Fl id table further →
      (theArm).shape.Served (stmOf Fl o) →
      ∃ r, (theArm).shape.recOf (stmOf Fl o) table = some r ∧
        (theArm).shape.seed0 (stmOf Fl o) (bytesToDig table.root) r = true :=
  seed0_small T K hE hF wT wB depthReq depthReqT salt embT prjT embB prjB _ _ _ _ _ code num dS _ _
    Served recOf p0 p1 isP0 isP1 hp0 hp1 l hlt hne f0 h0 F pR hR G V _ _ back (digest_size Z) hrec

include hF hrec in
/-- `EntryPart.seed1` at `armSmallAt`. -/
theorem seed1_smallAt :
    ∀ Fl o id table further, o.id = some id → o.bits = 128 → PortYesAt Fl id table further →
      (theArm).shape.Served (stmOf Fl o) →
      ∃ r, (theArm).shape.recOf (stmOf Fl o) further = some r ∧
        (theArm).shape.seed1 (stmOf Fl o) (bytesToDig further.root) r = true :=
  seed1_small T K hE hF wT wB depthReq depthReqT salt embT prjT embB prjB _ _ _ _ _ code num dS _ _
    Served recOf p0 p1 isP0 isP1 hp0 hp1 l hlt hne f0 h0 F pR hR G V _ _ back (digest_size Z) hrec

variable (hd : T.dcd = (DecR.configurationOfStoredTable A R).D) (hc : T.coll = (DecR.configurationOfStoredTable A R).coll)
  (hK : srD.K ≤ K) (hB : wB.ext.OK)

include hd hc hK hB in
set_option maxRecDepth 20000 in
/-- **The arm's bound in the letters of `armSmallAt`**: `atSmall_lax_closed`
(Johnson/Flat/ArmSibClosed.lean) at this input's own wire, seeds' data, answers' code and coding. -/
theorem lax_closed_smallAt (hA : BCHKS46At GF GE)
    (Mk : OComp (rom 256) (OutLA 256 (theArm).L (theArm).aL)) (tq : ℕ) (hq : Mk.QueryBound tq) :
    Rom.Pr (Mk.withTrace.bind fun o =>
        ((armL (theArm).W (theArm).Sd (theArm).cA o.1).overOne (theArm).m).bind fun b =>
          OComp.pure (o, b))
        (fun g => {x | x.2 = true ∧
          ¬ LinkHolds (theArm).W (logOne (theArm).W (armL (theArm).W (theArm).Sd (theArm).cA)
              (theArm).m
              (readBlocks (theArm).m g) x.1)
            x.1.1.1 x.1.1.2.1 x.1.1.2.2.1 x.1.1.2.2.2.1}) ≤
      (((tq + tVL (theArm).W) * (1 + 4) : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 128 +
        2 * (((tq + tVL (theArm).W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 :=
  atSmall_lax_closed T K wT wB depthReq depthReqT salt embT prjT embB prjB hd hc hK hB .test _ _
    p0 p1 code num hE dS hA (theArm).m Mk tq hq

end Small

end OnBytes.K
