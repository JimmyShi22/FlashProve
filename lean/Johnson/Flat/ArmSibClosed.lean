-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ArmSibClosed.lean: the bound on the entry's arm with the lax Link
(`atFull_arm_hash`, `atSmall_arm_hash`, Johnson/Flat/ArmSibAt.lean) at the written wire of
Johnson/EntryRec/OklaSib.lean and at the arm `armL` itself.

Two hypotheses of the bound are paid: the wire is lawful (`okla_sibFull`, `okla_sibSmall`), and
`armL` is an arm (`isArm_armL`, Johnson/TypedOracleCompiler/RecCompile/LinkAnsPr.lean).

Main names (Small for Full at the small example):
  `wAtFull`: the wire `wireOf2` at `LrG T`: Link's part is `wSib`, the bodies are `bodiesSib`,
    Link's depth of requests is 0.
  `atFull_lax_closed`: for every coding m and every maker with at most tq queries to one random
    function: the chance that `armL`, asking that function through m, says yes while what it
    promises fails is at most (tq + tVL W) * 5 * 2^-128 + 2 * ((tq + tVL W) * 5 + 1)^2 / 2^256.

Hypotheses left: `BCHKS46At GF GE`; T's decoder and collisions are the configuration's; K is at
least the description's number of blocks; the session's part of the wire has a lawful wire of
external strings (`wB.ext.OK`); K + 1 blocks are enough for the seeds' sampler; the maker's bound.

T holds honest provers of its three protocols, as the object's type asks: data, of which nothing is
asked and which no statement here reads; they are no hypothesis on soundness.

Limits: the bound is over a random function; nothing is said of a fixed one. Nothing on an honest
prover.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.ArmSibAt
import Johnson.EntryRec.OklaSib

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob Hiop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.Slice OnBytes.Flat Cb Cb.Ood
open OnBytes.RunA (RestR LrG wSib bodiesSib okla_sibFull okla_sibSmall)
open TypedOracleCompiler.Run.PQ (SOf)
open _root_.Run (ckP chalP)

section
variable {X X' RI : Type} [Fintype RI] [Nonempty RI] {A : (frS.toDecR frZ 402653181).Claims X}
  {R : (frS.toDecR frZ 402653181).RelationsAndEncoding A}
  (T : RestR (DecR.configurationOfStoredTable A R).I X' RI (Fin 1 → (Fin 29 → GE) × NZ)
    ((Fin frS.P.v → Bool) × Fin 1 → GE) frS.P.T.a linkSibFull)
  (K : ℕ) {aT : RoundSplits T.test.shape} (wT : ProtocolQueryLayout 256 (K + 1) (batTC (LrG T) aT))
  (wB : ProtocolQueryLayout 256 (K + 1) T.bat) (depthReq depthReqT salt : ℕ)
  (embT : (p : OPos T.test.shape) → OSym T.test.shape p → List Bool)
  (prjT : (p : OPos T.test.shape) → List Bool → Option (OSym T.test.shape p))
  (embB : (p : OPos T.bat.loc.shape) → OSym T.bat.loc.shape p → List Bool)
  (prjB : (p : OPos T.bat.loc.shape) → List Bool → Option (OSym T.bat.loc.shape p))

/-- The wire: Link's part is the written link's own; Link's depth of requests is 0. -/
abbrev wAtFull : QueryLayout 256 (typedOracleCarrier (LrG T) (List Bool) aT
          (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) :=
  wireOf2 (L := LrG T) (aT := aT) (aL := _root_.Run.Twin.allLo (SOf (ckP .two) dsFull)) (K + 1) wT
    (wSib T K (chalP .two K)) wB frS.P.T.a depthReq depthReqT 0
    (bodiesSib T salt embT prjT embB prjB)

variable (hd : T.dcd = (DecR.configurationOfStoredTable A R).D) (hc : T.coll = (DecR.configurationOfStoredTable A R).coll)
  (hK : frD.K ≤ K) (hB : wB.ext.OK) (t : Tag) (cfg : List (Dig 256)) (shape : Bits)
  (pl0 pl1 : PlainPart (shapeOf (typedOracleCarrier (LrG T) (List Bool) aT
             (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) t)
    (annOf (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) t))
  (code : (LrG T).Rec → List (Dig 256)) (num : ℕ → Plains T.bat.loc.shape → Bool)
  (h : (seedBS recLg recS).b ≤ K + 1) (dS : DecidableEq (Fin 1 → (Fin 29 → GE) × NZ))

include hd hc hK hB in
set_option maxRecDepth 20000 in
/-- The entry's arm with the lax Link, at the written wire, is sound against every maker over one
hash function, the arm itself asking that function: at 2^-128 a query. This is said under the
hypotheses that stand in the statement itself, which this comment does not list; it is no claim that
they hold. -/
theorem atFull_lax_closed (hA : BCHKS46At GF GE)
    (m : OracleCoding (typedOracleFamily 256 (K + 1) (typedOracleCarrier (LrG T) (List Bool) aT
                           (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull)))) 256)
    (Mk : OComp (rom 256) (OutLA 256 (LrG T) (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))))
    (tq : ℕ) (hq : Mk.QueryBound tq) :
    Rom.Pr (Mk.withTrace.bind fun o =>
        ((armL (wAtFull T K wT wB depthReq depthReqT salt embT prjT embB prjB)
          (sdAtFull T (List Bool) aT
            (wAtFull T K wT wB depthReq depthReqT salt embT prjT embB prjB) t cfg shape pl0 pl1
            code num h dS) (cAAtFull T) o.1).overOne m).bind fun b => OComp.pure (o, b))
        (fun g => {x | x.2 = true ∧
          ¬ LinkHolds (wAtFull T K wT wB depthReq depthReqT salt embT prjT embB prjB)
            (logOne (wAtFull T K wT wB depthReq depthReqT salt embT prjT embB prjB)
              (armL (wAtFull T K wT wB depthReq depthReqT salt embT prjT embB prjB)
                (sdAtFull T (List Bool) aT
                  (wAtFull T K wT wB depthReq depthReqT salt embT prjT embB prjB) t cfg shape
                  pl0 pl1 code num h dS) (cAAtFull T)) m (readBlocks m g) x.1)
            x.1.1.1 x.1.1.2.1 x.1.1.2.2.1 x.1.1.2.2.2.1}) ≤
      (((tq + tVL (wAtFull T K wT wB depthReq depthReqT salt embT prjT embB prjB)) * (1 + 4) :
          ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 128 +
        2 * (((tq + tVL (wAtFull T K wT wB depthReq depthReqT salt embT prjT embB prjB)) *
          (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 :=
  atFull_arm_hash T hd hc (List Bool) aT
    (wAtFull T K wT wB depthReq depthReqT salt embT prjT embB prjB) t cfg shape pl0 pl1 code num
    h dS hA (okla_sibFull K T hK wT wB hB depthReq depthReqT 0 salt embT prjT embB prjB)
    (isArm_armL ..) m Mk tq hq

end

section
variable {X X' RI : Type} [Fintype RI] [Nonempty RI] {A : (srS.toDecR srZ 524285).Claims X}
  {R : (srS.toDecR srZ 524285).RelationsAndEncoding A}
  (T : RestR (DecR.configurationOfStoredTable A R).I X' RI (Fin 1 → (Fin 19 → GE) × NZ)
    ((Fin srS.P.v → Bool) × Fin 1 → GE) srS.P.T.a linkSibSmall)
  (K : ℕ) {aT : RoundSplits T.test.shape} (wT : ProtocolQueryLayout 256 (K + 1) (batTC (LrG T) aT))
  (wB : ProtocolQueryLayout 256 (K + 1) T.bat) (depthReq depthReqT salt : ℕ)
  (embT : (p : OPos T.test.shape) → OSym T.test.shape p → List Bool)
  (prjT : (p : OPos T.test.shape) → List Bool → Option (OSym T.test.shape p))
  (embB : (p : OPos T.bat.loc.shape) → OSym T.bat.loc.shape p → List Bool)
  (prjB : (p : OPos T.bat.loc.shape) → List Bool → Option (OSym T.bat.loc.shape p))

/-- The wire: Link's part is the written link's own; Link's depth of requests is 0. -/
abbrev wAtSmall : QueryLayout 256 (typedOracleCarrier (LrG T) (List Bool) aT
          (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) :=
  wireOf2 (L := LrG T) (aT := aT) (aL := _root_.Run.Twin.allLo (SOf (ckP .two) dsSmall)) (K + 1) wT
    (wSib T K (chalP .two K)) wB srS.P.T.a depthReq depthReqT 0
    (bodiesSib T salt embT prjT embB prjB)

variable (hd : T.dcd = (DecR.configurationOfStoredTable A R).D) (hc : T.coll = (DecR.configurationOfStoredTable A R).coll)
  (hK : srD.K ≤ K) (hB : wB.ext.OK) (t : Tag) (cfg : List (Dig 256)) (shape : Bits)
  (pl0 pl1 : PlainPart (shapeOf (typedOracleCarrier (LrG T) (List Bool) aT
             (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) t)
    (annOf (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) t))
  (code : (LrG T).Rec → List (Dig 256)) (num : ℕ → Plains T.bat.loc.shape → Bool)
  (h : (seedBS 19 1).b ≤ K + 1) (dS : DecidableEq (Fin 1 → (Fin 19 → GE) × NZ))

include hd hc hK hB in
set_option maxRecDepth 20000 in
/-- The entry's arm with the lax Link, at the written wire, is sound against every maker over one
hash function, the arm itself asking that function: at 2^-128 a query. This is said under the
hypotheses that stand in the statement itself, which this comment does not list; it is no claim that
they hold. -/
theorem atSmall_lax_closed (hA : BCHKS46At GF GE)
    (m : OracleCoding (typedOracleFamily 256 (K + 1) (typedOracleCarrier (LrG T) (List Bool) aT
                           (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall)))) 256)
    (Mk : OComp (rom 256) (OutLA 256 (LrG T) (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))))
    (tq : ℕ) (hq : Mk.QueryBound tq) :
    Rom.Pr (Mk.withTrace.bind fun o =>
        ((armL (wAtSmall T K wT wB depthReq depthReqT salt embT prjT embB prjB)
          (sdAtSmall T (List Bool) aT
            (wAtSmall T K wT wB depthReq depthReqT salt embT prjT embB prjB) t cfg shape pl0 pl1
            code num h dS) (cAAtSmall T) o.1).overOne m).bind fun b => OComp.pure (o, b))
        (fun g => {x | x.2 = true ∧
          ¬ LinkHolds (wAtSmall T K wT wB depthReq depthReqT salt embT prjT embB prjB)
            (logOne (wAtSmall T K wT wB depthReq depthReqT salt embT prjT embB prjB)
              (armL (wAtSmall T K wT wB depthReq depthReqT salt embT prjT embB prjB)
                (sdAtSmall T (List Bool) aT
                  (wAtSmall T K wT wB depthReq depthReqT salt embT prjT embB prjB) t cfg shape
                  pl0 pl1 code num h dS) (cAAtSmall T)) m (readBlocks m g) x.1)
            x.1.1.1 x.1.1.2.1 x.1.1.2.2.1 x.1.1.2.2.2.1}) ≤
      (((tq + tVL (wAtSmall T K wT wB depthReq depthReqT salt embT prjT embB prjB)) * (1 + 4) :
          ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 128 +
        2 * (((tq + tVL (wAtSmall T K wT wB depthReq depthReqT salt embT prjT embB prjB)) *
          (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 :=
  atSmall_arm_hash T hd hc (List Bool) aT
    (wAtSmall T K wT wB depthReq depthReqT salt embT prjT embB prjB) t cfg shape pl0 pl1 code num
    h dS hA (okla_sibSmall K T hK wT wB hB depthReq depthReqT 0 salt embT prjT embB prjB)
    (isArm_armL ..) m Mk tq hq

end

end TypedOracleCompiler.Compile.Batch.Cms
