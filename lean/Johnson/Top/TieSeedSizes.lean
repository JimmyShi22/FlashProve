-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/TieSeedSizes.lean: the two seeds' fields of `EntryPart` (OnBytes/K/Parts.lean) at the
entry's arm, at the full size and at the small example, with what is asked of the wires paid.

Johnson/Top/TieSeedArm.lean shows the two fields at `(armOf …).shape` under five premises: `wire`,
`room`, the digest of the public files has 32 bytes, W.K < 2 ^ 48, and `RecIsProgram`. Here W is the
written wire of Johnson/Flat/ArmSibClosed.lean (`wAtFull`, `wAtSmall`) with K + 1 blocks, and S0 is
the record's wire of Johnson/Flat/ArmSibAt.lean over it. K is a letter: K + 1 blocks are enough for
the seeds' sampler (hE), and K + 1 < 2 ^ 48 (hF). Then `wire` and `room` are theorems
(Johnson/Flat/ArmSeeds.lean). At K := the number of blocks of the entry's description at the ground
hE and hF are theorems too (`enough_full`, `few_full`, `enough_small`, `few_small` there); a
greater K, as one wire for several files needs, is served as well.

Main names (Small for Full at the small example).
 `wFull`, `sFull`, `armFull`   the wire, the record's wire, the arm's input.
 `seed0_full`, `seed1_full`   the two fields at `(armFull …).shape`.

Asked: hE, hF; the digest has 32 bytes; `RecIsProgram` at the ground's field and table's shape, with
`seedOfC` at the size's numbers. Beside these, `armOf` takes seven laws of the coding's letters as
arguments (hp0, hp1, hlt, hne, h0, hR, hcfg), as in Johnson/Top/TieSeedArm.lean.

Five letters of `sFull` and `sSmall` are idle here (t, cfgD, shape, pl0, pl1): `armOf` lays the
tag of Test, the typed pieces of a table's name at cfgP and the plain parts p0, p1 over them; of the
record's wire its seed, its code, `num` and the test of equality alone are kept. cfgD is not the
digest of the public files: that is cfgP.

Limits: those of Johnson/Top/TieSeedArm.lean. The coding in `armOf` has the link's codes and the
leaves' code as letters. The field `link` is not spoken of. Nothing on soundness.


-/
import Johnson.Top.TieSeedArm
import Johnson.Flat.ArmSibClosed
import Johnson.Flat.ArmSeeds

set_option autoImplicit false

noncomputable section

namespace OnBytes.K
open _root_.Compile TypedOracleCompiler.Iop Rom TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open Hiop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (bytesToDig PCode ckP)
open TypedOracleCompiler.Run.Apart TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.SeedPage
open TypedOracleCompiler.Run.LinkAlong TypedOracleCompiler.Run.ArmDirect
open OnBytes.Slice OnBytes.Flat Cb Cb.Ood
open OnBytes.RunA (RestR LrG)
open TypedOracleCompiler.Run.PQ (SOf)
open OnBytes.Tie (recordGround smallRecordGround)
open TypedOracleCompiler.Slice (seedOfC entryXD)

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

/-- The written wire with K + 1 blocks. -/
abbrev wFull : QueryLayout 256 (typedOracleCarrier (LrG T) (List Bool) aT
          (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) :=
  wAtFull T K wT wB depthReq depthReqT salt embT prjT embB prjB

variable (t : Tag) (cfgD : List (Dig 256)) (shape : Bits)
  (pl0 pl1 : PlainPart (shapeOf (typedOracleCarrier (LrG T) (List Bool) aT
             (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) t)
    (annOf (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) t))
  (code : (LrG T).Rec → List (Dig 256)) (num : ℕ → Plains T.bat.loc.shape → Bool)
  (dS : DecidableEq (Fin 1 → (Fin 29 → GE) × NZ))

/-- The record's wire over it. -/
abbrev sFull : OutOfDomainSampleQueryLayout 256 (wFull T K wT wB depthReq depthReqT salt embT prjT embB prjB).K
    (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull)) :=
  sdAtFull T (List Bool) aT (wFull T K wT wB depthReq depthReqT salt embT prjT embB prjB) t
    cfgD shape pl0 pl1 code num hE dS

variable (cA : (LrG T).OutOfDomainAnswer → List (Dig 256)) (cfgP : ByteArray) (Served : UserStm → Prop)
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
  (V : Leaves L1) (cfg : ByteArray) (hcfg : cfg.size = 32)
  (back : StrCode (AllPts 256 (wFull T K wT wB depthReq depthReqT salt embT prjT embB prjB).K
    (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull)))))

/-- The arm's input at this size: `armOf` at the written wire and the record's wire over it. -/
abbrev armFull : ArmIn :=
  armOf (wFull T K wT wB depthReq depthReqT salt embT prjT embB prjB)
    (sFull T K hE wT wB depthReq depthReqT salt embT prjT embB prjB t cfgD shape pl0 pl1 code num
      dS) cA cfgP recordGround.q.link.table Served recOf p0 p1 isP0 isP1 hp0 hp1 l hlt hne f0 h0 F
      pR hR G V
    cfg hcfg back

variable (hc : cfgP.size = 32)
  (hrec : RecIsProgram recordGround.q.given.plan.field cfgP recordGround.q.link.table
    (seedOfC recLg recS : List (List E × E) → (LrG T).OutOfDomainSeed) Served recOf)

include hF hc hrec in
/-- **`EntryPart.seed0` at this size**: of the five premises of `seed0_arm` three are paid. -/
theorem seed0_full :
    ∀ Fl o id table further, o.id = some id → o.bits = 128 → PortYesAt Fl id table further →
      (armFull T K hE wT wB depthReq depthReqT salt embT prjT embB prjB t cfgD shape pl0 pl1 code
        num dS cA cfgP Served recOf p0 p1 isP0 isP1 hp0 hp1 l hlt hne f0 h0 F pR hR G V cfg hcfg
        back).shape.Served (stmOf Fl o) →
      ∃ r, (armFull T K hE wT wB depthReq depthReqT salt embT prjT embB prjB t cfgD shape pl0 pl1
          code num dS cA cfgP Served recOf p0 p1 isP0 isP1 hp0 hp1 l hlt hne f0 h0 F pR hR G V cfg
          hcfg
          back).shape.recOf (stmOf Fl o) table = some r ∧
        (armFull T K hE wT wB depthReq depthReqT salt embT prjT embB prjB t cfgD shape pl0 pl1
          code num dS cA cfgP Served recOf p0 p1 isP0 isP1 hp0 hp1 l hlt hne f0 h0 F pR hR G V cfg
          hcfg
          back).shape.seed0 (stmOf Fl o) (bytesToDig table.root) r = true :=
  seed0_arm _ _ cA recordGround.q.given.plan.field cfgP recordGround.q.link.table (seedOfC recLg
      recS) Served
    recOf p0 p1 isP0 isP1 hp0 hp1 l hlt hne f0 h0 F pR hR G V cfg hcfg back
    (wire_atFull T (List Bool) aT _ t cfgD shape pl0 pl1 code num hE dS)
    (room_atFull T (List Bool) aT _ hE) hc hF hrec

include hF hc hrec in
/-- **`EntryPart.seed1` at this size.** -/
theorem seed1_full :
    ∀ Fl o id table further, o.id = some id → o.bits = 128 → PortYesAt Fl id table further →
      (armFull T K hE wT wB depthReq depthReqT salt embT prjT embB prjB t cfgD shape pl0 pl1 code
        num dS cA cfgP Served recOf p0 p1 isP0 isP1 hp0 hp1 l hlt hne f0 h0 F pR hR G V cfg hcfg
        back).shape.Served (stmOf Fl o) →
      ∃ r, (armFull T K hE wT wB depthReq depthReqT salt embT prjT embB prjB t cfgD shape pl0 pl1
          code num dS cA cfgP Served recOf p0 p1 isP0 isP1 hp0 hp1 l hlt hne f0 h0 F pR hR G V cfg
          hcfg
          back).shape.recOf (stmOf Fl o) further = some r ∧
        (armFull T K hE wT wB depthReq depthReqT salt embT prjT embB prjB t cfgD shape pl0 pl1
          code num dS cA cfgP Served recOf p0 p1 isP0 isP1 hp0 hp1 l hlt hne f0 h0 F pR hR G V cfg
          hcfg
          back).shape.seed1 (stmOf Fl o) (bytesToDig further.root) r = true :=
  seed1_arm _ _ cA recordGround.q.given.plan.field cfgP recordGround.q.link.table (seedOfC recLg
      recS) Served
    recOf p0 p1 isP0 isP1 hp0 hp1 l hlt hne f0 h0 F pR hR G V cfg hcfg back
    (wire_atFull T (List Bool) aT _ t cfgD shape pl0 pl1 code num hE dS)
    (room_atFull T (List Bool) aT _ hE) hc hF hrec

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

/-- The written wire with K + 1 blocks. -/
abbrev wSmall : QueryLayout 256 (typedOracleCarrier (LrG T) (List Bool) aT
          (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) :=
  wAtSmall T K wT wB depthReq depthReqT salt embT prjT embB prjB

variable (t : Tag) (cfgD : List (Dig 256)) (shape : Bits)
  (pl0 pl1 : PlainPart (shapeOf (typedOracleCarrier (LrG T) (List Bool) aT
             (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) t)
    (annOf (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) t))
  (code : (LrG T).Rec → List (Dig 256)) (num : ℕ → Plains T.bat.loc.shape → Bool)
  (dS : DecidableEq (Fin 1 → (Fin 19 → GE) × NZ))

/-- The record's wire over it. -/
abbrev sSmall : OutOfDomainSampleQueryLayout 256 (wSmall T K wT wB depthReq depthReqT salt embT prjT embB prjB).K
    (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall)) :=
  sdAtSmall T (List Bool) aT (wSmall T K wT wB depthReq depthReqT salt embT prjT embB prjB) t
    cfgD shape pl0 pl1 code num hE dS

variable (cA : (LrG T).OutOfDomainAnswer → List (Dig 256)) (cfgP : ByteArray) (Served : UserStm → Prop)
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
  (V : Leaves L1) (cfg : ByteArray) (hcfg : cfg.size = 32)
  (back : StrCode (AllPts 256 (wSmall T K wT wB depthReq depthReqT salt embT prjT embB prjB).K
    (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall)))))

/-- The arm's input at this size: `armOf` at the written wire and the record's wire over it. -/
abbrev armSmall : ArmIn :=
  armOf (wSmall T K wT wB depthReq depthReqT salt embT prjT embB prjB)
    (sSmall T K hE wT wB depthReq depthReqT salt embT prjT embB prjB t cfgD shape pl0 pl1 code num
      dS) cA cfgP smallRecordGround.q.link.table Served recOf p0 p1 isP0 isP1 hp0 hp1 l hlt hne f0
      h0 F pR hR G V
    cfg hcfg back

variable (hc : cfgP.size = 32)
  (hrec : RecIsProgram smallRecordGround.q.given.plan.field cfgP smallRecordGround.q.link.table
    (seedOfC 19 1 : List (List E × E) → (LrG T).OutOfDomainSeed) Served recOf)

include hF hc hrec in
/-- **`EntryPart.seed0` at this size**: of the five premises of `seed0_arm` three are paid. -/
theorem seed0_small :
    ∀ Fl o id table further, o.id = some id → o.bits = 128 → PortYesAt Fl id table further →
      (armSmall T K hE wT wB depthReq depthReqT salt embT prjT embB prjB t cfgD shape pl0 pl1 code
        num dS cA cfgP Served recOf p0 p1 isP0 isP1 hp0 hp1 l hlt hne f0 h0 F pR hR G V cfg hcfg
        back).shape.Served (stmOf Fl o) →
      ∃ r, (armSmall T K hE wT wB depthReq depthReqT salt embT prjT embB prjB t cfgD shape pl0 pl1
          code num dS cA cfgP Served recOf p0 p1 isP0 isP1 hp0 hp1 l hlt hne f0 h0 F pR hR G V cfg
          hcfg
          back).shape.recOf (stmOf Fl o) table = some r ∧
        (armSmall T K hE wT wB depthReq depthReqT salt embT prjT embB prjB t cfgD shape pl0 pl1
          code num dS cA cfgP Served recOf p0 p1 isP0 isP1 hp0 hp1 l hlt hne f0 h0 F pR hR G V cfg
          hcfg
          back).shape.seed0 (stmOf Fl o) (bytesToDig table.root) r = true :=
  seed0_arm _ _ cA smallRecordGround.q.given.plan.field cfgP smallRecordGround.q.link.table (seedOfC
      19 1) Served
    recOf p0 p1 isP0 isP1 hp0 hp1 l hlt hne f0 h0 F pR hR G V cfg hcfg back
    (wire_atSmall T (List Bool) aT _ t cfgD shape pl0 pl1 code num hE dS)
    (room_atSmall T (List Bool) aT _ hE) hc hF hrec

include hF hc hrec in
/-- **`EntryPart.seed1` at this size.** -/
theorem seed1_small :
    ∀ Fl o id table further, o.id = some id → o.bits = 128 → PortYesAt Fl id table further →
      (armSmall T K hE wT wB depthReq depthReqT salt embT prjT embB prjB t cfgD shape pl0 pl1 code
        num dS cA cfgP Served recOf p0 p1 isP0 isP1 hp0 hp1 l hlt hne f0 h0 F pR hR G V cfg hcfg
        back).shape.Served (stmOf Fl o) →
      ∃ r, (armSmall T K hE wT wB depthReq depthReqT salt embT prjT embB prjB t cfgD shape pl0 pl1
          code num dS cA cfgP Served recOf p0 p1 isP0 isP1 hp0 hp1 l hlt hne f0 h0 F pR hR G V cfg
          hcfg
          back).shape.recOf (stmOf Fl o) further = some r ∧
        (armSmall T K hE wT wB depthReq depthReqT salt embT prjT embB prjB t cfgD shape pl0 pl1
          code num dS cA cfgP Served recOf p0 p1 isP0 isP1 hp0 hp1 l hlt hne f0 h0 F pR hR G V cfg
          hcfg
          back).shape.seed1 (stmOf Fl o) (bytesToDig further.root) r = true :=
  seed1_arm _ _ cA smallRecordGround.q.given.plan.field cfgP smallRecordGround.q.link.table (seedOfC
      19 1) Served
    recOf p0 p1 isP0 isP1 hp0 hp1 l hlt hne f0 h0 F pR hR G V cfg hcfg back
    (wire_atSmall T (List Bool) aT _ t cfgD shape pl0 pl1 code num hE dS)
    (room_atSmall T (List Bool) aT _ hE) hc hF hrec

end Small

end OnBytes.K
