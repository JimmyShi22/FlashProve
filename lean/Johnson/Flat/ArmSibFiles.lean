-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ArmSibFiles.lean: the bound on the entry's arm with the lax Link at the written wire
(`atFull_lax_closed`, `atSmall_lax_closed`, Johnson/Flat/ArmSibClosed.lean), at the written rest of
the object (`restSibFull`, `restSibSmall`, Johnson/Flat/RestSib.lean) and at the description's own
number of blocks.

Main names (Small, sr for Full, fr at the small example):
  `frD_K`: the library's description of the entry's chain has 140 blocks (small: 99).
  `fr_seed_fits`: one block more is enough for the seeds' sampler.
  `sibFull_closed`: the bound at T := `restSibFull A R F P hL`: the two equations on T's decoder and
    collisions hold by definition.
  `sibFull_closed_at`: the same at K := 140 (small: 99): the two conditions on K are paid.

Hypotheses left in `sibFull_closed_at`: `BCHKS46At GF GE`; the session's part of the wire has a
lawful wire of external strings (`wB.ext.OK`); the maker's bound.

F, the files' description, is any. P and hL, honest provers, are fields that the object's type asks
for: data, of which nothing is asked and which no statement here reads; they are no hypothesis on
soundness.

Limits: the bound is over a random function; nothing is said of a fixed one. Nothing on an honest
prover.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.ArmSibClosed
import Johnson.Flat.RestSib
import OnBytes.Params.EntryBlocksRecord
import OnBytes.Slice.SeedBias

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob Hiop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.Slice OnBytes.Flat Cb Cb.Ood
open OnBytes.RunA (RestR LrG)
open TypedOracleCompiler.Run.PQ (SOf)
open _root_.Run (ckP)

/-- The library's description of the entry's chain has 140 blocks. -/
theorem frD_K : frD.K = 140 := OnBytes.Params.record_kOf ByteArray.empty

/-- 140 + 1 blocks are enough for the seeds' sampler. -/
theorem fr_seed_fits : (seedBS recLg recS).b ≤ 140 + 1 := by
  rw [seedBS_b_full]
  norm_num

section
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (F : Files (DecR.configurationOfStoredTable A R)) (P : F.Provers)
  (hL : Honest linkSibFull ((DecR.configurationOfStoredTable A R).I ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 29 → GE) × NZ)) ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 29 → GE) × NZ))))

section
variable (K : ℕ)
  {aT : RoundSplits (restSibFull A R F P hL).test.shape}
  (wT : ProtocolQueryLayout 256 (K + 1) (batTC (LrG (restSibFull A R F P hL)) aT))
  (wB : ProtocolQueryLayout 256 (K + 1) (restSibFull A R F P hL).bat) (depthReq depthReqT salt : ℕ)
  (embT : (p : OPos (restSibFull A R F P hL).test.shape) →
    OSym (restSibFull A R F P hL).test.shape p → List Bool)
  (prjT : (p : OPos (restSibFull A R F P hL).test.shape) → List Bool →
    Option (OSym (restSibFull A R F P hL).test.shape p))
  (embB : (p : OPos (restSibFull A R F P hL).bat.loc.shape) →
    OSym (restSibFull A R F P hL).bat.loc.shape p → List Bool)
  (prjB : (p : OPos (restSibFull A R F P hL).bat.loc.shape) → List Bool →
    Option (OSym (restSibFull A R F P hL).bat.loc.shape p))
  (hB : wB.ext.OK) (t : Tag) (cfg : List (Dig 256)) (shape : Bits)
  (pl0 pl1 : PlainPart (shapeOf (typedOracleCarrier (LrG (restSibFull A R F P hL)) (List Bool) aT
             (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) t)
    (annOf (typedOracleCarrier (LrG (restSibFull A R F P hL)) (List Bool) aT
      (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) t))
  (code : (LrG (restSibFull A R F P hL)).Rec → List (Dig 256))
  (num : ℕ → Plains (restSibFull A R F P hL).bat.loc.shape → Bool)
  (dS : DecidableEq (Fin 1 → (Fin 29 → GE) × NZ))
  (hK : frD.K ≤ K) (h : (seedBS recLg recS).b ≤ K + 1)

include hK hB in
set_option maxRecDepth 20000 in
/-- The bound at the written rest of the object, any number of blocks. -/
theorem sibFull_closed (hA : BCHKS46At GF GE)
    (m : OracleCoding (typedOracleFamily 256 (K + 1) (typedOracleCarrier (LrG (restSibFull A R F P hL)) (List Bool) aT
                           (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull)))) 256)
    (Mk : OComp (rom 256) (OutLA 256 (LrG (restSibFull A R F P hL))
      (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))))
    (tq : ℕ) (hq : Mk.QueryBound tq) :
    Rom.Pr (Mk.withTrace.bind fun o =>
        ((armL (wAtFull (restSibFull A R F P hL) K wT wB depthReq depthReqT salt embT prjT embB
            prjB)
          (sdAtFull (restSibFull A R F P hL) (List Bool) aT
            (wAtFull (restSibFull A R F P hL) K wT wB depthReq depthReqT salt embT prjT embB prjB)
            t cfg shape pl0 pl1 code num h dS) (cAAtFull (restSibFull A R F P hL)) o.1).overOne
                m).bind
          fun b => OComp.pure (o, b))
        (fun g => {x | x.2 = true ∧
          ¬ LinkHolds (wAtFull (restSibFull A R F P hL) K wT wB depthReq depthReqT salt embT prjT
              embB prjB)
            (logOne (wAtFull (restSibFull A R F P hL) K wT wB depthReq depthReqT salt embT prjT embB
                prjB)
              (armL (wAtFull (restSibFull A R F P hL) K wT wB depthReq depthReqT salt embT prjT embB
                  prjB)
                (sdAtFull (restSibFull A R F P hL) (List Bool) aT
                  (wAtFull (restSibFull A R F P hL) K wT wB depthReq depthReqT salt embT prjT embB
                      prjB)
                  t cfg shape pl0 pl1 code num h dS) (cAAtFull (restSibFull A R F P hL))) m
              (readBlocks m g) x.1)
            x.1.1.1 x.1.1.2.1 x.1.1.2.2.1 x.1.1.2.2.2.1}) ≤
      (((tq + tVL (wAtFull (restSibFull A R F P hL) K wT wB depthReq depthReqT salt embT prjT embB
          prjB)) *
          (1 + 4) : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 128 +
        2 * (((tq + tVL (wAtFull (restSibFull A R F P hL) K wT wB depthReq depthReqT salt embT prjT
            embB prjB)) *
          (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 :=
  atFull_lax_closed (restSibFull A R F P hL) K wT wB depthReq depthReqT salt embT prjT embB prjB
    (restSibFull_dcd A R F P hL) (restSibFull_coll A R F P hL) hK hB t cfg shape pl0 pl1 code
    num h dS hA m Mk tq hq

end

section
variable
  {aT : RoundSplits (restSibFull A R F P hL).test.shape}
  (wT : ProtocolQueryLayout 256 (140 + 1) (batTC (LrG (restSibFull A R F P hL)) aT))
  (wB : ProtocolQueryLayout 256 (140 + 1) (restSibFull A R F P hL).bat) (depthReq depthReqT salt : ℕ)
  (embT : (p : OPos (restSibFull A R F P hL).test.shape) →
    OSym (restSibFull A R F P hL).test.shape p → List Bool)
  (prjT : (p : OPos (restSibFull A R F P hL).test.shape) → List Bool →
    Option (OSym (restSibFull A R F P hL).test.shape p))
  (embB : (p : OPos (restSibFull A R F P hL).bat.loc.shape) →
    OSym (restSibFull A R F P hL).bat.loc.shape p → List Bool)
  (prjB : (p : OPos (restSibFull A R F P hL).bat.loc.shape) → List Bool →
    Option (OSym (restSibFull A R F P hL).bat.loc.shape p))
  (hB : wB.ext.OK) (t : Tag) (cfg : List (Dig 256)) (shape : Bits)
  (pl0 pl1 : PlainPart (shapeOf (typedOracleCarrier (LrG (restSibFull A R F P hL)) (List Bool) aT
             (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) t)
    (annOf (typedOracleCarrier (LrG (restSibFull A R F P hL)) (List Bool) aT
      (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) t))
  (code : (LrG (restSibFull A R F P hL)).Rec → List (Dig 256))
  (num : ℕ → Plains (restSibFull A R F P hL).bat.loc.shape → Bool)
  (dS : DecidableEq (Fin 1 → (Fin 29 → GE) × NZ))

include hB in
set_option maxRecDepth 20000 in
/-- The bound at the written rest of the object and the description's own number of blocks. -/
theorem sibFull_closed_at (hA : BCHKS46At GF GE)
    (m : OracleCoding (typedOracleFamily 256 (140 + 1) (typedOracleCarrier (LrG (restSibFull A R F P hL)) (List Bool) aT
                           (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull)))) 256)
    (Mk : OComp (rom 256) (OutLA 256 (LrG (restSibFull A R F P hL))
      (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))))
    (tq : ℕ) (hq : Mk.QueryBound tq) :
    Rom.Pr (Mk.withTrace.bind fun o =>
        ((armL (wAtFull (restSibFull A R F P hL) 140 wT wB depthReq depthReqT salt embT prjT embB
            prjB)
          (sdAtFull (restSibFull A R F P hL) (List Bool) aT
            (wAtFull (restSibFull A R F P hL) 140 wT wB depthReq depthReqT salt embT prjT embB prjB)
            t cfg shape pl0 pl1 code num fr_seed_fits dS) (cAAtFull (restSibFull A R F P hL))
                o.1).overOne m).bind
          fun b => OComp.pure (o, b))
        (fun g => {x | x.2 = true ∧
          ¬ LinkHolds (wAtFull (restSibFull A R F P hL) 140 wT wB depthReq depthReqT salt embT prjT
              embB prjB)
            (logOne (wAtFull (restSibFull A R F P hL) 140 wT wB depthReq depthReqT salt embT prjT
                embB prjB)
              (armL (wAtFull (restSibFull A R F P hL) 140 wT wB depthReq depthReqT salt embT prjT
                  embB prjB)
                (sdAtFull (restSibFull A R F P hL) (List Bool) aT
                  (wAtFull (restSibFull A R F P hL) 140 wT wB depthReq depthReqT salt embT prjT embB
                      prjB)
                  t cfg shape pl0 pl1 code num fr_seed_fits dS) (cAAtFull (restSibFull A R F P hL)))
                      m
              (readBlocks m g) x.1)
            x.1.1.1 x.1.1.2.1 x.1.1.2.2.1 x.1.1.2.2.2.1}) ≤
      (((tq + tVL (wAtFull (restSibFull A R F P hL) 140 wT wB depthReq depthReqT salt embT prjT embB
          prjB)) *
          (1 + 4) : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 128 +
        2 * (((tq + tVL (wAtFull (restSibFull A R F P hL) 140 wT wB depthReq depthReqT salt embT
            prjT embB prjB)) *
          (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 :=
  sibFull_closed A R F P hL 140 wT wB depthReq depthReqT salt embT prjT embB prjB hB t cfg shape
    pl0 pl1 code num dS (le_of_eq frD_K) fr_seed_fits hA m Mk tq hq

end

end

/-- The library's description of the entry's chain has 99 blocks. -/
theorem srD_K : srD.K = 99 := OnBytes.Params.small_record_kOf ByteArray.empty

/-- 99 + 1 blocks are enough for the seeds' sampler. -/
theorem sr_seed_fits : (seedBS 19 1).b ≤ 99 + 1 := by
  rw [sr_seed_blocks]
  norm_num

section
variable {X : Type} (A : (srS.toDecR srZ 524285).Claims X)
  (R : (srS.toDecR srZ 524285).RelationsAndEncoding A) (F : Files (DecR.configurationOfStoredTable A R)) (P : F.Provers)
  (hL : Honest linkSibSmall ((DecR.configurationOfStoredTable A R).I ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 19 → GE) × NZ)) ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 19 → GE) × NZ))))

section
variable (K : ℕ)
  {aT : RoundSplits (restSibSmall A R F P hL).test.shape}
  (wT : ProtocolQueryLayout 256 (K + 1) (batTC (LrG (restSibSmall A R F P hL)) aT))
  (wB : ProtocolQueryLayout 256 (K + 1) (restSibSmall A R F P hL).bat) (depthReq depthReqT salt : ℕ)
  (embT : (p : OPos (restSibSmall A R F P hL).test.shape) →
    OSym (restSibSmall A R F P hL).test.shape p → List Bool)
  (prjT : (p : OPos (restSibSmall A R F P hL).test.shape) → List Bool →
    Option (OSym (restSibSmall A R F P hL).test.shape p))
  (embB : (p : OPos (restSibSmall A R F P hL).bat.loc.shape) →
    OSym (restSibSmall A R F P hL).bat.loc.shape p → List Bool)
  (prjB : (p : OPos (restSibSmall A R F P hL).bat.loc.shape) → List Bool →
    Option (OSym (restSibSmall A R F P hL).bat.loc.shape p))
  (hB : wB.ext.OK) (t : Tag) (cfg : List (Dig 256)) (shape : Bits)
  (pl0 pl1 : PlainPart (shapeOf (typedOracleCarrier (LrG (restSibSmall A R F P hL)) (List Bool) aT
             (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) t)
    (annOf (typedOracleCarrier (LrG (restSibSmall A R F P hL)) (List Bool) aT
      (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) t))
  (code : (LrG (restSibSmall A R F P hL)).Rec → List (Dig 256))
  (num : ℕ → Plains (restSibSmall A R F P hL).bat.loc.shape → Bool)
  (dS : DecidableEq (Fin 1 → (Fin 19 → GE) × NZ))
  (hK : srD.K ≤ K) (h : (seedBS 19 1).b ≤ K + 1)

include hK hB in
set_option maxRecDepth 20000 in
/-- The bound at the written rest of the object, any number of blocks. -/
theorem sibSmall_closed (hA : BCHKS46At GF GE)
    (m : OracleCoding (typedOracleFamily 256 (K + 1) (typedOracleCarrier (LrG (restSibSmall A R F P hL)) (List Bool) aT
                           (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall)))) 256)
    (Mk : OComp (rom 256) (OutLA 256 (LrG (restSibSmall A R F P hL))
      (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))))
    (tq : ℕ) (hq : Mk.QueryBound tq) :
    Rom.Pr (Mk.withTrace.bind fun o =>
        ((armL (wAtSmall (restSibSmall A R F P hL) K wT wB depthReq depthReqT salt embT prjT embB
            prjB)
          (sdAtSmall (restSibSmall A R F P hL) (List Bool) aT
            (wAtSmall (restSibSmall A R F P hL) K wT wB depthReq depthReqT salt embT prjT embB prjB)
            t cfg shape pl0 pl1 code num h dS) (cAAtSmall (restSibSmall A R F P hL)) o.1).overOne
                m).bind
          fun b => OComp.pure (o, b))
        (fun g => {x | x.2 = true ∧
          ¬ LinkHolds (wAtSmall (restSibSmall A R F P hL) K wT wB depthReq depthReqT salt embT prjT
              embB prjB)
            (logOne (wAtSmall (restSibSmall A R F P hL) K wT wB depthReq depthReqT salt embT prjT
                embB prjB)
              (armL (wAtSmall (restSibSmall A R F P hL) K wT wB depthReq depthReqT salt embT prjT
                  embB prjB)
                (sdAtSmall (restSibSmall A R F P hL) (List Bool) aT
                  (wAtSmall (restSibSmall A R F P hL) K wT wB depthReq depthReqT salt embT prjT embB
                      prjB)
                  t cfg shape pl0 pl1 code num h dS) (cAAtSmall (restSibSmall A R F P hL))) m
              (readBlocks m g) x.1)
            x.1.1.1 x.1.1.2.1 x.1.1.2.2.1 x.1.1.2.2.2.1}) ≤
      (((tq + tVL (wAtSmall (restSibSmall A R F P hL) K wT wB depthReq depthReqT salt embT prjT embB
          prjB)) *
          (1 + 4) : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 128 +
        2 * (((tq + tVL (wAtSmall (restSibSmall A R F P hL) K wT wB depthReq depthReqT salt embT
            prjT embB prjB)) *
          (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 :=
  atSmall_lax_closed (restSibSmall A R F P hL) K wT wB depthReq depthReqT salt embT prjT embB prjB
    (restSibSmall_dcd A R F P hL) (restSibSmall_coll A R F P hL) hK hB t cfg shape pl0 pl1 code
    num h dS hA m Mk tq hq

end

section
variable
  {aT : RoundSplits (restSibSmall A R F P hL).test.shape}
  (wT : ProtocolQueryLayout 256 (99 + 1) (batTC (LrG (restSibSmall A R F P hL)) aT))
  (wB : ProtocolQueryLayout 256 (99 + 1) (restSibSmall A R F P hL).bat) (depthReq depthReqT salt : ℕ)
  (embT : (p : OPos (restSibSmall A R F P hL).test.shape) →
    OSym (restSibSmall A R F P hL).test.shape p → List Bool)
  (prjT : (p : OPos (restSibSmall A R F P hL).test.shape) → List Bool →
    Option (OSym (restSibSmall A R F P hL).test.shape p))
  (embB : (p : OPos (restSibSmall A R F P hL).bat.loc.shape) →
    OSym (restSibSmall A R F P hL).bat.loc.shape p → List Bool)
  (prjB : (p : OPos (restSibSmall A R F P hL).bat.loc.shape) → List Bool →
    Option (OSym (restSibSmall A R F P hL).bat.loc.shape p))
  (hB : wB.ext.OK) (t : Tag) (cfg : List (Dig 256)) (shape : Bits)
  (pl0 pl1 : PlainPart (shapeOf (typedOracleCarrier (LrG (restSibSmall A R F P hL)) (List Bool) aT
             (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) t)
    (annOf (typedOracleCarrier (LrG (restSibSmall A R F P hL)) (List Bool) aT
      (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) t))
  (code : (LrG (restSibSmall A R F P hL)).Rec → List (Dig 256))
  (num : ℕ → Plains (restSibSmall A R F P hL).bat.loc.shape → Bool)
  (dS : DecidableEq (Fin 1 → (Fin 19 → GE) × NZ))

include hB in
set_option maxRecDepth 20000 in
/-- The bound at the written rest of the object and the description's own number of blocks. -/
theorem sibSmall_closed_at (hA : BCHKS46At GF GE)
    (m : OracleCoding (typedOracleFamily 256 (99 + 1) (typedOracleCarrier (LrG (restSibSmall A R F P hL)) (List Bool) aT
                           (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall)))) 256)
    (Mk : OComp (rom 256) (OutLA 256 (LrG (restSibSmall A R F P hL))
      (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))))
    (tq : ℕ) (hq : Mk.QueryBound tq) :
    Rom.Pr (Mk.withTrace.bind fun o =>
        ((armL (wAtSmall (restSibSmall A R F P hL) 99 wT wB depthReq depthReqT salt embT prjT embB
            prjB)
          (sdAtSmall (restSibSmall A R F P hL) (List Bool) aT
            (wAtSmall (restSibSmall A R F P hL) 99 wT wB depthReq depthReqT salt embT prjT embB
                prjB)
            t cfg shape pl0 pl1 code num sr_seed_fits dS) (cAAtSmall (restSibSmall A R F P hL))
                o.1).overOne m).bind
          fun b => OComp.pure (o, b))
        (fun g => {x | x.2 = true ∧
          ¬ LinkHolds (wAtSmall (restSibSmall A R F P hL) 99 wT wB depthReq depthReqT salt embT prjT
              embB prjB)
            (logOne (wAtSmall (restSibSmall A R F P hL) 99 wT wB depthReq depthReqT salt embT prjT
                embB prjB)
              (armL (wAtSmall (restSibSmall A R F P hL) 99 wT wB depthReq depthReqT salt embT prjT
                  embB prjB)
                (sdAtSmall (restSibSmall A R F P hL) (List Bool) aT
                  (wAtSmall (restSibSmall A R F P hL) 99 wT wB depthReq depthReqT salt embT prjT
                      embB prjB)
                  t cfg shape pl0 pl1 code num sr_seed_fits dS) (cAAtSmall (restSibSmall A R F P
                      hL))) m
              (readBlocks m g) x.1)
            x.1.1.1 x.1.1.2.1 x.1.1.2.2.1 x.1.1.2.2.2.1}) ≤
      (((tq + tVL (wAtSmall (restSibSmall A R F P hL) 99 wT wB depthReq depthReqT salt embT prjT
          embB prjB)) *
          (1 + 4) : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 128 +
        2 * (((tq + tVL (wAtSmall (restSibSmall A R F P hL) 99 wT wB depthReq depthReqT salt embT
            prjT embB prjB)) *
          (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 :=
  sibSmall_closed A R F P hL 99 wT wB depthReq depthReqT salt embT prjT embB prjB hB t cfg shape
    pl0 pl1 code num dS (le_of_eq srD_K) sr_seed_fits hA m Mk tq hq

end

end

end TypedOracleCompiler.Compile.Batch.Cms
