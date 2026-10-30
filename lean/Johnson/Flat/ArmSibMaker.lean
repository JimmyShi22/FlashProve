-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ArmSibMaker.lean: the bound on the entry's arm with the lax Link, at the object whose
link is `linkSibFull` | `linkSibSmall`, with the event said on the maker's own log of strings
(`arm_pr_maker`, Johnson/TypedOracleCompiler/RecCompile/LinkAnsMaker.lean), and with no hypothesis left on the wire.

Main names (Small, sr for Full, fr at the small example):
  `oneExt wB z`, `oneExt_ok`: a session's wire with the library's wire of one external string
    (`WireE.one`) in the place of its own, wB's own depth and its word on pruned paths kept; it is
    lawful. z: the symbol where nothing is fixed.
  `atFull_arm_maker`: the bound at `LrG T`, any lawful wire, any arm whose first queries are the two
    seeds' (`HeadSeeds`).
  `sibFull_maker`: the bound at T := `restSibFull A R F P hL`, 140 + 1 blocks (small: 99 + 1), the
    wire `wAtFull` with `oneExt wB z` for the session's part, and the arm `armL`: the maker runs,
    then the arm, both asking one random function; the chance that the arm says yes while what it
    promises fails on the one-block entries of the maker's log of strings is at most
    (tq + tVL W) * 5 * 2^-128 + 2 * ((tq + tVL W) * 5 + 1)^2 / 2^256.
  `sibFull_price`: the same with the bound `tVL W` on the arm's typed queries as a number
    (Johnson/Flat/ArmSibCount.lean): tVL W = 13545 (small: 7975).

Hypotheses left in `sibFull_maker` and `sibFull_price`: `BCHKS46At GF GE`; a coding m (see Limits);
the maker asks at most tq queries.

F, the files' description, is any. P and hL, honest provers, are fields that the object's type asks
for: data, of which nothing is asked and which no statement here reads; they are no hypothesis on
soundness. The other letters (Test's and the session's wires, depths, the length of salts, four
maps, the tag, the name's parts, the plain parts, the record's code, `num`, the test of equality of
seeds) are free.

Limits: the bound is over a random function; nothing is said of a fixed one. That the programs are
wired as the written wire says is not shown here. Nothing on an honest prover.
A theorem of its own on the entry file's arm: no instance of a description of the whole verifier.
A wiring for the arm alone: 140 + 1 blocks (small: 99 + 1) are the entry's own number and one; that
this number serves the key file's and the proof file's rounds is not shown; wT and wB, the wire
records of these two files' protocols, are letters. The bound is composed here with no statement on
the program. What the arm promises (`LinkHolds`) has the way out "the first table's decoder finds
nothing": the entry file alone settles nothing on an index. Link's compiled verifier runs without
the test of the strict format.
The coding m is a letter with laws inside its type: `Rom.OracleCoding` asks that it be one to one and onto
all bit strings. It counts as a hypothesis. No coding is given here, and that one exists at this
object is not shown here: where the typed queries are uncountable (X and F are any) there is none,
and the theorems say nothing.
m, the wire and the seeds' data (the tag, the name's parts `cfg` and `shape`, the plain parts) are
fixed BEFORE the function is drawn: each may be any value, but a fixed one. The coding and the
seeds' data that the programs are meant to have hold two digests that are themselves values of the
hash function (the head of Johnson/Top/TieArmSib.lean): an experiment in which these digests are the
drawn function's own values is not covered by the theorems as stated.
The 2^-128 of a round counts proof of work: at six rounds of the full size and four of the small one
32 of the 128 bits are test bits (the heads of OnBytes/Slice/FullRecNum.lean and
OnBytes/Slice/SmallRecNum.lean). That work is worth its bits is not shown.
The claims A, the rest R and the type X of instances are letters. The decoder in `LinkHolds` reads
through A: "finds nothing" also covers a first table that decodes to a matrix which A calls out of
range; at an A whose range holds of nothing that way out is always open.
13545 (small: 7975) is the value of `tVL W`, an upper bound on the arm's TYPED queries at the
written wire (Johnson/Flat/ArmSibCount.lean), not the number of queries of a run.
That `armL` ever says yes at this wire is not shown: if it never did, the bound would hold for free.
The limits in the heads of the files named above hold here too, but for those that a sentence above
lifts.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.ArmSibFiles
import Johnson.TypedOracleCompiler.RecCompile.LinkAnsMaker
import Johnson.Flat.ArmSibCount

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob Hiop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.Slice OnBytes.Flat Cb Cb.Ood
open OnBytes.RunA (RestR LrG okla_sibFull okla_sibSmall)
open TypedOracleCompiler.Run.PQ (SOf)
open _root_.Run (ckP)
open _root_.Run.PQ (SgX)

/-- A session's wire with the library's wire of one external string in the place of its own. -/
def oneExt {a K : ℕ} {Y : Type} {Q : BatchInteractiveOracleProof Y (oneExternalString (2 ^ a) SgX)} (wB : ProtocolQueryLayout 256 K Q)
    (z : SgX) : ProtocolQueryLayout 256 K Q :=
  ⟨wB.sh, { WireE.one (2 ^ a) SgX z with pr := wB.ext.pr, depth := wB.ext.depth }, wB.decO,
    wB.nOpen, wB.maxDepth⟩

/-- Its wire of external strings is lawful. -/
theorem oneExt_ok {a K : ℕ} {Y : Type} {Q : BatchInteractiveOracleProof Y (oneExternalString (2 ^ a) SgX)}
    (wB : ProtocolQueryLayout 256 K Q) (z : SgX) : (oneExt wB z).ext.OK :=
  ⟨(WireE.one_ok _ _ z).nodup, (WireE.one_ok _ _ z).complete, (WireE.one_ok _ _ z).build_rd⟩

section
variable {X X' RI : Type} [Fintype RI] [Nonempty RI] {A : (frS.toDecR frZ 402653181).Claims X}
  {R : (frS.toDecR frZ 402653181).RelationsAndEncoding A}
  (T : RestR (DecR.configurationOfStoredTable A R).I X' RI (Fin 1 → (Fin 29 → GE) × NZ)
    ((Fin frS.P.v → Bool) × Fin 1 → GE) frS.P.T.a linkSibFull)
  (hd : T.dcd = (DecR.configurationOfStoredTable A R).D) (hc : T.coll = (DecR.configurationOfStoredTable A R).coll)
  (Bd : Type) (aT : RoundSplits T.test.shape)
  (W : QueryLayout 256 (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))))
  (t : Tag) (cfg : List (Dig 256)) (shape : Bits)
  (pl0 pl1 : PlainPart (shapeOf (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) t)
    (annOf (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) t))
  (code : (LrG T).Rec → List (Dig 256)) (num : ℕ → Plains T.bat.loc.shape → Bool)
  (h : (seedBS recLg recS).b ≤ W.K) (dS : DecidableEq (Fin 1 → (Fin 29 → GE) × NZ))

include hd hc in
set_option maxRecDepth 20000 in
/-- The entry's arm at `LrG T`: the maker runs, then the arm, both asking one random function; the
chance that the arm says yes while what it promises fails on the maker's own log of strings. -/
theorem atFull_arm_maker (hA : BCHKS46At GF GE) (hW : OKLA W)
    {V : OutLA 256 (LrG T) (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull)) →
      TypedOracleComputation 256 W.K (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) Bool}
    (hV : IsArm W (sdAtFull T Bd aT W t cfg shape pl0 pl1 code num h dS) (cAAtFull T) V)
    (hH : HeadSeeds W (sdAtFull T Bd aT W t cfg shape pl0 pl1 code num h dS) V)
    (m : OracleCoding (typedOracleFamily 256 W.K (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two)
                                       dsFull)))) 256)
    (Mk : OComp (rom 256) (OutLA 256 (LrG T) (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))))
    (tq : ℕ) (hq : Mk.QueryBound tq) :
    Rom.Pr (Mk.withTrace.bind fun o => ((V o.1).overOne m).bind fun b => OComp.pure (o, b))
        (fun _ => {x | x.2 = true ∧
          ¬ LinkHolds W (singleTr m x.1.2) x.1.1.1 x.1.1.2.1 x.1.1.2.2.1 x.1.1.2.2.2.1}) ≤
      (((tq + tVL W) * (1 + 4) : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 128 +
        2 * (((tq + tVL W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 := by
  obtain ⟨ε, hs, hb⟩ := atFull_sound T hd hc hA
  exact arm_pr_maker (L := LrG T) (εL := ε) hs linkSibFull_local
    (by rw [_root_.Run.Twin.allLo_eq]; exact _root_.Iop.BatchOne.BAnn.allLocal_coherent _) hW
    (ansOK_atFull T) (sdAtFull_law T hc Bd aT W t cfg shape pl0 pl1 code num h dS)
    (below_allLo _ _ _ _ hb) hV hH (by norm_num) m Mk tq hq

end

section
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (F : Files (DecR.configurationOfStoredTable A R)) (P : F.Provers)
  (hL : Honest linkSibFull ((DecR.configurationOfStoredTable A R).I ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 29 → GE) × NZ)) ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 29 → GE) × NZ))))
  {aT : RoundSplits (restSibFull A R F P hL).test.shape}
  (wT : ProtocolQueryLayout 256 (140 + 1) (batTC (LrG (restSibFull A R F P hL)) aT))
  (wB : ProtocolQueryLayout 256 (140 + 1) (restSibFull A R F P hL).bat) (z : SgX) (depthReq depthReqT salt : ℕ)
  (embT : (p : OPos (restSibFull A R F P hL).test.shape) → OSym (restSibFull A R F P hL).test.shape
      p → List Bool)
  (prjT : (p : OPos (restSibFull A R F P hL).test.shape) → List Bool → Option (OSym (restSibFull A R
      F P hL).test.shape p))
  (embB : (p : OPos (restSibFull A R F P hL).bat.loc.shape) → OSym (restSibFull A R F P
      hL).bat.loc.shape p → List Bool)
  (prjB : (p : OPos (restSibFull A R F P hL).bat.loc.shape) → List Bool → Option (OSym (restSibFull
      A R F P hL).bat.loc.shape p))
  (t : Tag) (cfg : List (Dig 256)) (shape : Bits)
  (pl0 pl1 : PlainPart (shapeOf (typedOracleCarrier (LrG (restSibFull A R F P hL)) (List Bool) aT
             (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) t)
    (annOf (typedOracleCarrier (LrG (restSibFull A R F P hL)) (List Bool) aT (_root_.Run.Twin.allLo (SOf (ckP
                  .two) dsFull))) t))
  (code : (LrG (restSibFull A R F P hL)).Rec → List (Dig 256))
  (num : ℕ → Plains (restSibFull A R F P hL).bat.loc.shape → Bool)
  (dS : DecidableEq (Fin 1 → (Fin 29 → GE) × NZ))

set_option maxRecDepth 20000 in
/-- The bound at the written object, the written wire and `armL`, on the maker's own log of
strings. Left: the hypothesis on codes, a coding m and the maker's bound. -/
theorem sibFull_maker (hA : BCHKS46At GF GE)
    (m : OracleCoding (typedOracleFamily 256 (140 + 1) (typedOracleCarrier (LrG (restSibFull A R F P hL)) (List Bool) aT
                             (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull)))) 256)
    (Mk : OComp (rom 256) (OutLA 256 (LrG (restSibFull A R F P hL)) (_root_.Run.Twin.allLo (SOf (ckP
        .two) dsFull))))
    (tq : ℕ) (hq : Mk.QueryBound tq) :
    Rom.Pr (Mk.withTrace.bind fun o =>
        ((armL (wAtFull (restSibFull A R F P hL) 140 wT (oneExt wB z) depthReq depthReqT salt embT
            prjT embB prjB)
          (sdAtFull (restSibFull A R F P hL) (List Bool) aT (wAtFull (restSibFull A R F P hL) 140 wT
              (oneExt wB z) depthReq depthReqT salt embT prjT embB prjB) t cfg shape pl0 pl1 code
          num fr_seed_fits dS)
          (cAAtFull (restSibFull A R F P hL)) o.1).overOne m).bind fun b => OComp.pure (o, b))
        (fun _ => {x | x.2 = true ∧
          ¬ LinkHolds (wAtFull (restSibFull A R F P hL) 140 wT (oneExt wB z) depthReq depthReqT salt
              embT prjT embB prjB)
            (singleTr m x.1.2) x.1.1.1 x.1.1.2.1 x.1.1.2.2.1 x.1.1.2.2.2.1}) ≤
      (((tq + tVL (wAtFull (restSibFull A R F P hL) 140 wT (oneExt wB z) depthReq depthReqT salt
          embT prjT embB prjB)) * (1 + 4) : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 128 +
        2 * (((tq + tVL (wAtFull (restSibFull A R F P hL) 140 wT (oneExt wB z) depthReq depthReqT
            salt embT prjT embB prjB)) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 :=
  atFull_arm_maker (restSibFull A R F P hL) (restSibFull_dcd A R F P hL) (restSibFull_coll A R F P
      hL)
    (List Bool) aT (wAtFull (restSibFull A R F P hL) 140 wT (oneExt wB z) depthReq depthReqT salt
        embT prjT embB prjB) t cfg shape pl0 pl1 code num fr_seed_fits dS hA
    (okla_sibFull 140 (restSibFull A R F P hL) (le_of_eq frD_K) wT (oneExt wB z) (oneExt_ok wB z)
        depthReq
      depthReqT 0 salt embT prjT embB prjB)
    (isArm_armL ..) (headSeeds_armL _ _) m Mk tq hq

set_option maxRecDepth 20000 in
/-- The same with the bound `tVL W` on the arm's typed queries as a number. -/
theorem sibFull_price (hA : BCHKS46At GF GE)
    (m : OracleCoding (typedOracleFamily 256 (140 + 1) (typedOracleCarrier (LrG (restSibFull A R F P hL)) (List Bool) aT
                             (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull)))) 256)
    (Mk : OComp (rom 256) (OutLA 256 (LrG (restSibFull A R F P hL)) (_root_.Run.Twin.allLo (SOf (ckP
        .two) dsFull))))
    (tq : ℕ) (hq : Mk.QueryBound tq) :
    Rom.Pr (Mk.withTrace.bind fun o =>
        ((armL (wAtFull (restSibFull A R F P hL) 140 wT (oneExt wB z) depthReq depthReqT salt embT
            prjT embB prjB)
          (sdAtFull (restSibFull A R F P hL) (List Bool) aT (wAtFull (restSibFull A R F P hL) 140 wT
              (oneExt wB z) depthReq depthReqT salt embT prjT embB prjB) t cfg shape pl0 pl1 code
          num fr_seed_fits dS)
          (cAAtFull (restSibFull A R F P hL)) o.1).overOne m).bind fun b => OComp.pure (o, b))
        (fun _ => {x | x.2 = true ∧
          ¬ LinkHolds (wAtFull (restSibFull A R F P hL) 140 wT (oneExt wB z) depthReq depthReqT salt
              embT prjT embB prjB)
            (singleTr m x.1.2) x.1.1.1 x.1.1.2.1 x.1.1.2.2.1 x.1.1.2.2.2.1}) ≤
      (((tq + 13545) * (1 + 4) : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 128 +
        2 * (((tq + 13545) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 := by
  have h := sibFull_maker A R F P hL wT wB z depthReq depthReqT salt embT prjT embB prjB t cfg
    shape pl0 pl1 code num dS hA m Mk tq hq
  rw [tVL_atFull] at h
  exact h

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
  (pl0 pl1 : PlainPart (shapeOf (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall)))
             t)
    (annOf (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) t))
  (code : (LrG T).Rec → List (Dig 256)) (num : ℕ → Plains T.bat.loc.shape → Bool)
  (h : (seedBS 19 1).b ≤ W.K) (dS : DecidableEq (Fin 1 → (Fin 19 → GE) × NZ))

include hd hc in
set_option maxRecDepth 20000 in
/-- The entry's arm at `LrG T`: the maker runs, then the arm, both asking one random function; the
chance that the arm says yes while what it promises fails on the maker's own log of strings. -/
theorem atSmall_arm_maker (hA : BCHKS46At GF GE) (hW : OKLA W)
    {V : OutLA 256 (LrG T) (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall)) →
      TypedOracleComputation 256 W.K (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) Bool}
    (hV : IsArm W (sdAtSmall T Bd aT W t cfg shape pl0 pl1 code num h dS) (cAAtSmall T) V)
    (hH : HeadSeeds W (sdAtSmall T Bd aT W t cfg shape pl0 pl1 code num h dS) V)
    (m : OracleCoding (typedOracleFamily 256 W.K (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two)
                                       dsSmall)))) 256)
    (Mk : OComp (rom 256) (OutLA 256 (LrG T) (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))))
    (tq : ℕ) (hq : Mk.QueryBound tq) :
    Rom.Pr (Mk.withTrace.bind fun o => ((V o.1).overOne m).bind fun b => OComp.pure (o, b))
        (fun _ => {x | x.2 = true ∧
          ¬ LinkHolds W (singleTr m x.1.2) x.1.1.1 x.1.1.2.1 x.1.1.2.2.1 x.1.1.2.2.2.1}) ≤
      (((tq + tVL W) * (1 + 4) : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 128 +
        2 * (((tq + tVL W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 := by
  obtain ⟨ε, hs, hb⟩ := atSmall_sound T hd hc hA
  exact arm_pr_maker (L := LrG T) (εL := ε) hs linkSibSmall_local
    (by rw [_root_.Run.Twin.allLo_eq]; exact _root_.Iop.BatchOne.BAnn.allLocal_coherent _) hW
    (ansOK_atSmall T) (sdAtSmall_law T hc Bd aT W t cfg shape pl0 pl1 code num h dS)
    (below_allLo _ _ _ _ hb) hV hH (by norm_num) m Mk tq hq

end

section
variable {X : Type} (A : (srS.toDecR srZ 524285).Claims X)
  (R : (srS.toDecR srZ 524285).RelationsAndEncoding A) (F : Files (DecR.configurationOfStoredTable A R)) (P : F.Provers)
  (hL : Honest linkSibSmall ((DecR.configurationOfStoredTable A R).I ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 19 → GE) × NZ)) ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 19 → GE) × NZ))))
  {aT : RoundSplits (restSibSmall A R F P hL).test.shape}
  (wT : ProtocolQueryLayout 256 (99 + 1) (batTC (LrG (restSibSmall A R F P hL)) aT))
  (wB : ProtocolQueryLayout 256 (99 + 1) (restSibSmall A R F P hL).bat) (z : SgX) (depthReq depthReqT salt : ℕ)
  (embT : (p : OPos (restSibSmall A R F P hL).test.shape) → OSym (restSibSmall A R F P
      hL).test.shape p → List Bool)
  (prjT : (p : OPos (restSibSmall A R F P hL).test.shape) → List Bool → Option (OSym (restSibSmall A
      R F P hL).test.shape p))
  (embB : (p : OPos (restSibSmall A R F P hL).bat.loc.shape) → OSym (restSibSmall A R F P
      hL).bat.loc.shape p → List Bool)
  (prjB : (p : OPos (restSibSmall A R F P hL).bat.loc.shape) → List Bool → Option (OSym
      (restSibSmall A R F P hL).bat.loc.shape p))
  (t : Tag) (cfg : List (Dig 256)) (shape : Bits)
  (pl0 pl1 : PlainPart (shapeOf (typedOracleCarrier (LrG (restSibSmall A R F P hL)) (List Bool) aT
             (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) t)
    (annOf (typedOracleCarrier (LrG (restSibSmall A R F P hL)) (List Bool) aT (_root_.Run.Twin.allLo (SOf (ckP
                  .two) dsSmall))) t))
  (code : (LrG (restSibSmall A R F P hL)).Rec → List (Dig 256))
  (num : ℕ → Plains (restSibSmall A R F P hL).bat.loc.shape → Bool)
  (dS : DecidableEq (Fin 1 → (Fin 19 → GE) × NZ))

set_option maxRecDepth 20000 in
/-- The bound at the written object, the written wire and `armL`, on the maker's own log of
strings. Left: the hypothesis on codes, a coding m and the maker's bound. -/
theorem sibSmall_maker (hA : BCHKS46At GF GE)
    (m : OracleCoding (typedOracleFamily 256 (99 + 1) (typedOracleCarrier (LrG (restSibSmall A R F P hL)) (List Bool) aT
                             (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall)))) 256)
    (Mk : OComp (rom 256) (OutLA 256 (LrG (restSibSmall A R F P hL)) (_root_.Run.Twin.allLo (SOf
        (ckP .two) dsSmall))))
    (tq : ℕ) (hq : Mk.QueryBound tq) :
    Rom.Pr (Mk.withTrace.bind fun o =>
        ((armL (wAtSmall (restSibSmall A R F P hL) 99 wT (oneExt wB z) depthReq depthReqT salt embT
            prjT embB prjB)
          (sdAtSmall (restSibSmall A R F P hL) (List Bool) aT (wAtSmall (restSibSmall A R F P hL) 99
              wT (oneExt wB z) depthReq depthReqT salt embT prjT embB prjB) t cfg shape pl0 pl1 code
          num sr_seed_fits dS)
          (cAAtSmall (restSibSmall A R F P hL)) o.1).overOne m).bind fun b => OComp.pure (o, b))
        (fun _ => {x | x.2 = true ∧
          ¬ LinkHolds (wAtSmall (restSibSmall A R F P hL) 99 wT (oneExt wB z) depthReq depthReqT
              salt embT prjT embB prjB)
            (singleTr m x.1.2) x.1.1.1 x.1.1.2.1 x.1.1.2.2.1 x.1.1.2.2.2.1}) ≤
      (((tq + tVL (wAtSmall (restSibSmall A R F P hL) 99 wT (oneExt wB z) depthReq depthReqT salt
          embT prjT embB prjB)) * (1 + 4) : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 128 +
        2 * (((tq + tVL (wAtSmall (restSibSmall A R F P hL) 99 wT (oneExt wB z) depthReq depthReqT
            salt embT prjT embB prjB)) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 :=
  atSmall_arm_maker (restSibSmall A R F P hL) (restSibSmall_dcd A R F P hL) (restSibSmall_coll A R F
      P hL)
    (List Bool) aT (wAtSmall (restSibSmall A R F P hL) 99 wT (oneExt wB z) depthReq depthReqT salt
        embT prjT embB prjB) t cfg shape pl0 pl1 code num sr_seed_fits dS hA
    (okla_sibSmall 99 (restSibSmall A R F P hL) (le_of_eq srD_K) wT (oneExt wB z) (oneExt_ok wB z)
        depthReq
      depthReqT 0 salt embT prjT embB prjB)
    (isArm_armL ..) (headSeeds_armL _ _) m Mk tq hq

set_option maxRecDepth 20000 in
/-- The same with the bound `tVL W` on the arm's typed queries as a number. -/
theorem sibSmall_price (hA : BCHKS46At GF GE)
    (m : OracleCoding (typedOracleFamily 256 (99 + 1) (typedOracleCarrier (LrG (restSibSmall A R F P hL)) (List Bool) aT
                             (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall)))) 256)
    (Mk : OComp (rom 256) (OutLA 256 (LrG (restSibSmall A R F P hL)) (_root_.Run.Twin.allLo (SOf
        (ckP .two) dsSmall))))
    (tq : ℕ) (hq : Mk.QueryBound tq) :
    Rom.Pr (Mk.withTrace.bind fun o =>
        ((armL (wAtSmall (restSibSmall A R F P hL) 99 wT (oneExt wB z) depthReq depthReqT salt embT
            prjT embB prjB)
          (sdAtSmall (restSibSmall A R F P hL) (List Bool) aT (wAtSmall (restSibSmall A R F P hL) 99
              wT (oneExt wB z) depthReq depthReqT salt embT prjT embB prjB) t cfg shape pl0 pl1 code
          num sr_seed_fits dS)
          (cAAtSmall (restSibSmall A R F P hL)) o.1).overOne m).bind fun b => OComp.pure (o, b))
        (fun _ => {x | x.2 = true ∧
          ¬ LinkHolds (wAtSmall (restSibSmall A R F P hL) 99 wT (oneExt wB z) depthReq depthReqT
              salt embT prjT embB prjB)
            (singleTr m x.1.2) x.1.1.1 x.1.1.2.1 x.1.1.2.2.1 x.1.1.2.2.2.1}) ≤
      (((tq + 7975) * (1 + 4) : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 128 +
        2 * (((tq + 7975) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 := by
  have h := sibSmall_maker A R F P hL wT wB z depthReq depthReqT salt embT prjT embB prjB t cfg
    shape pl0 pl1 code num dS hA m Mk tq hq
  rw [tVL_atSmall] at h
  exact h

end

end TypedOracleCompiler.Compile.Batch.Cms
