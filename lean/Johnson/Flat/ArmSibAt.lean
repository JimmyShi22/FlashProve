-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ArmSibAt.lean: the entry's arm with the lax Link is sound at the object with records
`LrG T` (Johnson/EntryRec/Defs.lean) whose link is `linkSibFull` | `linkSibSmall`
(OnBytes/Flat/LinkSibAt.lean), with the written link's own marks on the link's rounds
(`Run.Twin.allLo`).

T holds all that an object with records holds beside its word length, its symbols and its link. Two
things are asked of it: its decoder and its collisions are those of the configuration of a stored
table with a record (`DecR.configurationOfStoredTable A R`, OnBytes/Slice/ConfOf.lean). All its other fields are letters.

Main names (Small for Full at the small example):
  `atFull_sound`: the link of `LrG T` is sound for "the first table's decoder finds nothing, or the
    copy collides at its seed, or both decoders find the same", in the object's own letters, with
    counts below 2^-128, one a round, proof of work counted: Johnson/Flat/EntryArm.lean's head.
  `sdAtFull`, `sdAtFull_law`: the record's wire, and the seed's law at 2^-128.
  `cAAtFull`, `ansOK_atFull`: the answers' code `codeA` and its two laws.
  `atFull_arm_one`: for every arm V, every coding m and every maker with at most tq queries to one
    random function: the chance that the arm says yes while what it promises fails is at most
    (tq + tVL W) * 5 * 2^-128 + 2 * ((tq + tVL W) * 5 + 1)^2 / 2^256.
  `atFull_arm_hash`: the same with the arm itself asking that function.

Hypotheses: `BCHKS46At GF GE`; the two equations on T; the wire is lawful (`OKLA W`); V is an arm
(`IsArm`); the wire has blocks enough for the seeds' sampler.

T holds honest provers of its three protocols, as the object's type asks: data, of which nothing is
asked and which no statement here reads; they are no hypothesis on soundness.

Limits: nothing on an honest prover; that a lawful wire exists is not shown here. A count bounds one
round's error, not the chance of a false proof; that the work in it is worth its bits is not shown.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Flat.EntryArm
import Johnson.EntryRec.Defs
import OnBytes.Flat.LinkSibAt

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

/-- Where all rounds have the written link's own marks, the errors of the rounds count as they are.
-/
theorem below_allLo (S : List _root_.Run.Twin.RS) (N : ℕ) (ε : Err (_root_.Run.Twin.up S))
    (κ : ℝ≥0∞) (hb : Err.Below ε κ) :
    Err.Below (Err.timesShared N (_root_.Run.Twin.allLo S) ε) κ := by
  rw [_root_.Run.Twin.allLo_eq, timesShared_allLocal]
  exact hb

section
variable {X X' RI : Type} [Fintype RI] [Nonempty RI] {A : (frS.toDecR frZ 402653181).Claims X}
  {R : (frS.toDecR frZ 402653181).RelationsAndEncoding A}
  (T : RestR (DecR.configurationOfStoredTable A R).I X' RI (Fin 1 → (Fin 29 → GE) × NZ)
    ((Fin frS.P.v → Bool) × Fin 1 → GE) frS.P.T.a linkSibFull)
  (hd : T.dcd = (DecR.configurationOfStoredTable A R).D) (hc : T.coll = (DecR.configurationOfStoredTable A R).coll)
  (Bd : Type) (aT : RoundSplits T.test.shape)
  (W : QueryLayout 256 (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))))
  (t : Tag) (cfg : List (Dig 256)) (shape : Bits)
  (pl0 pl1 : PlainPart (shapeOf (typedOracleCarrier (LrG T) Bd aT
             (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) t)
    (annOf (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) t))
  (code : (LrG T).Rec → List (Dig 256)) (num : ℕ → Plains T.bat.loc.shape → Bool)
  (h : (seedBS recLg recS).b ≤ W.K) (dS : DecidableEq (Fin 1 → (Fin 29 → GE) × NZ))

/-- The record's wire at `LrG T`: the seed is the written draw from the digests. -/
def sdAtFull : OutOfDomainSampleQueryLayout 256 W.K (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull)) :=
  sdE (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull)) t cfg shape pl0 pl1
    (recSeedK recT recLg recS W.K h) code num dS

/-- The code of a record's answers there. -/
abbrev cAAtFull : (LrG T).OutOfDomainAnswer → List (Dig 256) := codeA (v := frS.P.v) (s := 1)

/-- No two tables of answers are written alike, and all with one number of digests. -/
theorem ansOK_atFull : AnsOK (cAAtFull T) :=
  ⟨codeA_inj, fun a a' => (codeA_length a).trans (codeA_length a').symm⟩

include hd hc in
/-- The link of `LrG T` is sound in the object's own letters, with each round's count below 2^-128;
at six rounds 32 of these bits are proof of work, which is not shown to be worth its bits. This is
said under the hypotheses that stand in the statement; it is no claim that they hold. -/
theorem atFull_sound (hA : BCHKS46At GF GE) :
    ∃ ε : Err (LrG T).link.shape,
      (LrG T).link.Sound
        (fun rr y => (LrG T).decodeIndex y.1 rr.1 = none ∨ (LrG T).hasCollisionAt y.2 rr.2.1 ∨
          (LrG T).decodeIndex y.2 rr.2 = (LrG T).decodeIndex y.1 rr.1) ε ∧
        Err.Below ε (((2 : ℝ≥0∞)⁻¹) ^ 128) := by
  obtain ⟨ε, hs, hb⟩ := linkSibFull_sound hA A R
  refine ⟨ε, ?_, hb⟩
  show linkSibFull.Sound (fun rr y => T.dcd y.1 rr.1 = none ∨ T.coll y.2 rr.2.1 ∨
    T.dcd y.2 rr.2 = T.dcd y.1 rr.1) ε
  rw [hd, hc]
  exact hs

include hc in
/-- The seed's law at `LrG T`. -/
theorem sdAtFull_law :
    (sdAtFull T Bd aT W t cfg shape pl0 pl1 code num h dS).Law (((2 : ℝ≥0∞)⁻¹) ^ 128) :=
  sdE_law _ _ _ _ _ _ _ _ _ _ _ _ _ _ fun y => by
    show pr _ {a | T.coll y (recSeedK recT recLg recS W.K h a)} ≤ _
    rw [hc]
    exact entryFull_seedLawK A R W.K h y

include hd hc in
set_option maxRecDepth 20000 in
/-- The entry's arm at `LrG T` is sound against every maker over one hash function, under the
hypothesis on codes: at 2^-128 a query, proof of work counted, which is not shown to be worth its
bits. This is said under the hypotheses in the statement; it is no claim that they hold. -/
theorem atFull_arm_one (hA : BCHKS46At GF GE) (hW : OKLA W)
    {V : OutLA 256 (LrG T) (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull)) →
      TypedOracleComputation 256 W.K (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) Bool}
    (hV : IsArm W (sdAtFull T Bd aT W t cfg shape pl0 pl1 code num h dS) (cAAtFull T) V)
    (m : OracleCoding (typedOracleFamily 256 W.K
              (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull)))) 256)
    (Mk : OComp (rom 256) (OutLA 256 (LrG T) (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))))
    (tq : ℕ) (hq : Mk.QueryBound tq) :
    Rom.Pr Mk.withTrace
        (fun g => {o | (runA W V (readBlocks m g) o.1).1 = true ∧
          ¬ LinkHolds W (logOne W V m (readBlocks m g) o) o.1.1 o.1.2.1 o.1.2.2.1 o.1.2.2.2.1}) ≤
      (((tq + tVL W) * (1 + 4) : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 128 +
        2 * (((tq + tVL W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 := by
  obtain ⟨ε, hs, hb⟩ := atFull_sound T hd hc hA
  exact arm_pr_one (L := LrG T) (εL := ε) hs linkSibFull_local
    (by rw [_root_.Run.Twin.allLo_eq]; exact _root_.Iop.BatchOne.BAnn.allLocal_coherent _) hW
    (ansOK_atFull T) (sdAtFull_law T hc Bd aT W t cfg shape pl0 pl1 code num h dS)
    (below_allLo _ _ _ _ hb) hV m Mk tq hq

include hd hc in
set_option maxRecDepth 20000 in
/-- The same with the arm itself asking that function. -/
theorem atFull_arm_hash (hA : BCHKS46At GF GE) (hW : OKLA W)
    {V : OutLA 256 (LrG T) (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull)) →
      TypedOracleComputation 256 W.K (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) Bool}
    (hV : IsArm W (sdAtFull T Bd aT W t cfg shape pl0 pl1 code num h dS) (cAAtFull T) V)
    (m : OracleCoding (typedOracleFamily 256 W.K
              (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull)))) 256)
    (Mk : OComp (rom 256) (OutLA 256 (LrG T) (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))))
    (tq : ℕ) (hq : Mk.QueryBound tq) :
    Rom.Pr (Mk.withTrace.bind fun o => ((V o.1).overOne m).bind fun b => OComp.pure (o, b))
        (fun g => {x | x.2 = true ∧
          ¬ LinkHolds W (logOne W V m (readBlocks m g) x.1) x.1.1.1 x.1.1.2.1 x.1.1.2.2.1
            x.1.1.2.2.2.1}) ≤
      (((tq + tVL W) * (1 + 4) : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 128 +
        2 * (((tq + tVL W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 := by
  obtain ⟨ε, hs, hb⟩ := atFull_sound T hd hc hA
  exact arm_pr_hash (L := LrG T) (εL := ε) hs linkSibFull_local
    (by rw [_root_.Run.Twin.allLo_eq]; exact _root_.Iop.BatchOne.BAnn.allLocal_coherent _) hW
    (ansOK_atFull T) (sdAtFull_law T hc Bd aT W t cfg shape pl0 pl1 code num h dS)
    (below_allLo _ _ _ _ hb) hV m Mk tq hq

end

section
variable {X X' RI : Type} [Fintype RI] [Nonempty RI] {A : (srS.toDecR srZ 524285).Claims X}
  {R : (srS.toDecR srZ 524285).RelationsAndEncoding A}
  (T : RestR (DecR.configurationOfStoredTable A R).I X' RI (Fin 1 → (Fin 19 → GE) × NZ)
    ((Fin srS.P.v → Bool) × Fin 1 → GE) srS.P.T.a linkSibSmall)
  (hd : T.dcd = (DecR.configurationOfStoredTable A R).D) (hc : T.coll = (DecR.configurationOfStoredTable A R).coll)
  (Bd : Type) (aT : RoundSplits T.test.shape)
  (W : QueryLayout 256 (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))))
  (t : Tag) (cfg : List (Dig 256)) (shape : Bits)
  (pl0 pl1 : PlainPart (shapeOf (typedOracleCarrier (LrG T) Bd aT
             (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) t)
    (annOf (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) t))
  (code : (LrG T).Rec → List (Dig 256)) (num : ℕ → Plains T.bat.loc.shape → Bool)
  (h : (seedBS 19 1).b ≤ W.K) (dS : DecidableEq (Fin 1 → (Fin 19 → GE) × NZ))

/-- The record's wire at `LrG T`: the seed is the written draw from the digests. -/
def sdAtSmall : OutOfDomainSampleQueryLayout 256 W.K (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall)) :=
  sdE (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall)) t cfg shape pl0 pl1
    (recSeedK srT 19 1 W.K h) code num dS

/-- The code of a record's answers there. -/
abbrev cAAtSmall : (LrG T).OutOfDomainAnswer → List (Dig 256) := codeA (v := srS.P.v) (s := 1)

/-- No two tables of answers are written alike, and all with one number of digests. -/
theorem ansOK_atSmall : AnsOK (cAAtSmall T) :=
  ⟨codeA_inj, fun a a' => (codeA_length a).trans (codeA_length a').symm⟩

include hd hc in
/-- The link of `LrG T` is sound in the object's own letters, with each round's count below 2^-128;
at four rounds 32 of these bits are proof of work, which is not shown to be worth its bits. This is
said under the hypotheses that stand in the statement; it is no claim that they hold. -/
theorem atSmall_sound (hA : BCHKS46At GF GE) :
    ∃ ε : Err (LrG T).link.shape,
      (LrG T).link.Sound
        (fun rr y => (LrG T).decodeIndex y.1 rr.1 = none ∨ (LrG T).hasCollisionAt y.2 rr.2.1 ∨
          (LrG T).decodeIndex y.2 rr.2 = (LrG T).decodeIndex y.1 rr.1) ε ∧
        Err.Below ε (((2 : ℝ≥0∞)⁻¹) ^ 128) := by
  obtain ⟨ε, hs, hb⟩ := linkSibSmall_sound hA A R
  refine ⟨ε, ?_, hb⟩
  show linkSibSmall.Sound (fun rr y => T.dcd y.1 rr.1 = none ∨ T.coll y.2 rr.2.1 ∨
    T.dcd y.2 rr.2 = T.dcd y.1 rr.1) ε
  rw [hd, hc]
  exact hs

include hc in
/-- The seed's law at `LrG T`. -/
theorem sdAtSmall_law :
    (sdAtSmall T Bd aT W t cfg shape pl0 pl1 code num h dS).Law (((2 : ℝ≥0∞)⁻¹) ^ 128) :=
  sdE_law _ _ _ _ _ _ _ _ _ _ _ _ _ _ fun y => by
    show pr _ {a | T.coll y (recSeedK srT 19 1 W.K h a)} ≤ _
    rw [hc]
    exact entrySmall_seedLawK A R W.K h y

include hd hc in
set_option maxRecDepth 20000 in
/-- The entry's arm at `LrG T` is sound against every maker over one hash function, under the
hypothesis on codes: at 2^-128 a query, proof of work counted, which is not shown to be worth its
bits. This is said under the hypotheses in the statement; it is no claim that they hold. -/
theorem atSmall_arm_one (hA : BCHKS46At GF GE) (hW : OKLA W)
    {V : OutLA 256 (LrG T) (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall)) →
      TypedOracleComputation 256 W.K (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) Bool}
    (hV : IsArm W (sdAtSmall T Bd aT W t cfg shape pl0 pl1 code num h dS) (cAAtSmall T) V)
    (m : OracleCoding (typedOracleFamily 256 W.K
              (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall)))) 256)
    (Mk : OComp (rom 256) (OutLA 256 (LrG T) (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))))
    (tq : ℕ) (hq : Mk.QueryBound tq) :
    Rom.Pr Mk.withTrace
        (fun g => {o | (runA W V (readBlocks m g) o.1).1 = true ∧
          ¬ LinkHolds W (logOne W V m (readBlocks m g) o) o.1.1 o.1.2.1 o.1.2.2.1 o.1.2.2.2.1}) ≤
      (((tq + tVL W) * (1 + 4) : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 128 +
        2 * (((tq + tVL W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 := by
  obtain ⟨ε, hs, hb⟩ := atSmall_sound T hd hc hA
  exact arm_pr_one (L := LrG T) (εL := ε) hs linkSibSmall_local
    (by rw [_root_.Run.Twin.allLo_eq]; exact _root_.Iop.BatchOne.BAnn.allLocal_coherent _) hW
    (ansOK_atSmall T) (sdAtSmall_law T hc Bd aT W t cfg shape pl0 pl1 code num h dS)
    (below_allLo _ _ _ _ hb) hV m Mk tq hq

include hd hc in
set_option maxRecDepth 20000 in
/-- The same with the arm itself asking that function. -/
theorem atSmall_arm_hash (hA : BCHKS46At GF GE) (hW : OKLA W)
    {V : OutLA 256 (LrG T) (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall)) →
      TypedOracleComputation 256 W.K (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) Bool}
    (hV : IsArm W (sdAtSmall T Bd aT W t cfg shape pl0 pl1 code num h dS) (cAAtSmall T) V)
    (m : OracleCoding (typedOracleFamily 256 W.K
              (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall)))) 256)
    (Mk : OComp (rom 256) (OutLA 256 (LrG T) (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))))
    (tq : ℕ) (hq : Mk.QueryBound tq) :
    Rom.Pr (Mk.withTrace.bind fun o => ((V o.1).overOne m).bind fun b => OComp.pure (o, b))
        (fun g => {x | x.2 = true ∧
          ¬ LinkHolds W (logOne W V m (readBlocks m g) x.1) x.1.1.1 x.1.1.2.1 x.1.1.2.2.1
            x.1.1.2.2.2.1}) ≤
      (((tq + tVL W) * (1 + 4) : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 128 +
        2 * (((tq + tVL W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 := by
  obtain ⟨ε, hs, hb⟩ := atSmall_sound T hd hc hA
  exact arm_pr_hash (L := LrG T) (εL := ε) hs linkSibSmall_local
    (by rw [_root_.Run.Twin.allLo_eq]; exact _root_.Iop.BatchOne.BAnn.allLocal_coherent _) hW
    (ansOK_atSmall T) (sdAtSmall_law T hc Bd aT W t cfg shape pl0 pl1 code num h dS)
    (below_allLo _ _ _ _ hb) hV m Mk tq hq

end

end TypedOracleCompiler.Compile.Batch.Cms
