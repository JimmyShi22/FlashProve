-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ArmSibPublic.lean: the entry's arm at the written link (`LrG T`,
Johnson/Flat/ArmSibAt.lean) where the two public digests are themselves answers of the one hash
function, with the code of the answers as it stands in the other theorems at that object.

`arm_pr_pub2` (Johnson/TypedOracleCompiler/RecCompile/LinkAnsPublic.lean) at `LrG T`, any wire with the laws `OKLA`,
the written draw of a seed, the written code of the answers and the arm with the lax Link. The
configuration's digest stands in the record's wire (`cfgOf c`); the parameters' digest stands in no
typed query: the coding, which is a family over the two digests, spells it. So the arm at (c, p) is
the arm of Johnson/Flat/ArmSibMaker.lean at the record's wire with `cfgOf c`.

  `armAtFullPub`, `armAtSmallPub`
  `atFull_arm_pub2`, `atSmall_arm_pub2`

Here the parameters' digest is not laid in front of each record's answers in the typed first query
of Link.

Limits: those in the heads of LinkAnsPublic.lean and Johnson/Flat/ArmSibMaker.lean. The two public
strings, `cfgOf`, the way m in which the coding is made of the two digests, and W are letters fixed
before the function is drawn. The theorem on codes is a hypothesis. The bound is an average over the
two digests of bounds against makers that may hang on them.
  * No yes is shown: the bound would hold of an arm that refuses everything.
  * No such family of codings is built, and that one exists is not shown. That a family of codings
    can write p into the string of Link's first query is not shown.
  * One maker: the theorems in two stages at this object still fix the digests.
  * By the byte format the run's value, a call on the parameters' digest and 32 bytes of the proof
    string, also stands in the arm's calls. It is no public digest, and the typed arm makes no such
    call. How a coding carries it is the coding's matter.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.ArmSibAt
import Johnson.TypedOracleCompiler.RecCompile.LinkAnsPublicArm

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

section
variable {X X' RI : Type} [Fintype RI] [Nonempty RI] {A : (frS.toDecR frZ 402653181).Claims X}
  {R : (frS.toDecR frZ 402653181).RelationsAndEncoding A}
  (T : RestR (DecR.configurationOfStoredTable A R).I X' RI (Fin 1 → (Fin 29 → GE) × NZ)
    ((Fin frS.P.v → Bool) × Fin 1 → GE) frS.P.T.a linkSibFull)
  (hd : T.dcd = (DecR.configurationOfStoredTable A R).D) (hc : T.coll = (DecR.configurationOfStoredTable A R).coll)
  (Bd : Type) (aT : RoundSplits T.test.shape)
  (W : QueryLayout 256 (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))))
  (t : Tag) (cfgOf : Dig 256 → List (Dig 256)) (shape : Bits)
  (pl0 pl1 : PlainPart (shapeOf (typedOracleCarrier (LrG T) Bd aT
             (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) t)
    (annOf (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) t))
  (code : (LrG T).Rec → List (Dig 256)) (num : ℕ → Plains T.bat.loc.shape → Bool)
  (h : (seedBS recLg recS).b ≤ W.K) (dS : DecidableEq (Fin 1 → (Fin 29 → GE) × NZ))

/-- The arm with the lax Link at `LrG T`, made of the two public digests d = (c, p): c stands in the
rest of a table's name (`cfgOf c`), so in the first seed query. The code of the answers does not
hang on d: where p stands in a string is the coding's matter. -/
def armAtFullPub (d : Dig 256 × Dig 256) :
    OutLA 256 (LrG T) (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull)) →
      TypedOracleComputation 256 W.K (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) Bool :=
  armL W (sdAtFull T Bd aT W t (cfgOf d.1) shape pl0 pl1 code num h dS) (cAAtFull T)

include hd hc in
set_option maxRecDepth 20000 in
/-- The entry's arm with the lax Link at `LrG T` and any wire with the laws `OKLA`, where the
configuration's digest c and the parameters' digest p are answers of the one hash function: c at the
public string s0, p at the public string s1 c. The maker runs; then the arm asks the function for c
and p itself and runs at them, through the coding at (c, p). It accepts, and what it promises fails
on the one-block entries, under that coding, of the maker's log of strings, with probability at most
n 2^-128 + 2 (n + 1)² / 2^256 at n = 5 (tq + tVL W). Hypotheses: the theorem on codes; `OKLA W`; the
bound on the maker's calls; of the family m of codings and the two strings: under every coding of
the family (at every d) s0 and every s1 c (at every c) code points of the spare oracle; s1 c is
never s0. From `variable` lines: T decodes and collides as the configuration's object (hd, hc); the
seed's number of blocks is at most W.K (h). -/
theorem atFull_arm_pub2 (hA : BCHKS46At GF GE) (hW : OKLA W)
    (m : Dig 256 × Dig 256 → OracleCoding (typedOracleFamily 256 W.K
              (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull)))) 256)
    (s0 : List Bool) (s1 : Dig 256 → List Bool) (h0 : ∀ d, IsOther (m d) s0)
    (h1 : ∀ d c, IsOther (m d) (s1 c)) (hne : ∀ c, s1 c ≠ s0)
    (Mk : OComp (rom 256) (OutLA 256 (LrG T) (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))))
    (tq : ℕ) (hq : Mk.QueryBound tq) :
    Rom.Pr (expPub (armAtFullPub T Bd aT W t cfgOf shape pl0 pl1 code num h dS) m
        (pub2 s0 s1) Mk)
        (fun _ => {x | x.2.2 = true ∧
          ¬ LinkHolds W (singleTr (m x.2.1) x.1.2) x.1.1.1 x.1.1.2.1 x.1.1.2.2.1 x.1.1.2.2.2.1}) ≤
      (((tq + tVL W) * (1 + 4) : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 128 +
        2 * (((tq + tVL W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 := by
  obtain ⟨ε, hs, hb⟩ := atFull_sound T hd hc hA
  have hPt : ∀ d s, Pt2 s0 s1 s → IsOther (m d) s := by
    rintro d s (rfl | ⟨c, rfl⟩)
    · exact h0 d
    · exact h1 d c
  exact arm_pr_pub2 (L := LrG T) (εL := ε)
    (S := fun d => sdAtFull T Bd aT W t (cfgOf d.1) shape pl0 pl1 code num h dS)
    (cA := fun _ => cAAtFull T)
    (V := armAtFullPub T Bd aT W t cfgOf shape pl0 pl1 code num h dS)
    hs linkSibFull_local
    (by rw [_root_.Run.Twin.allLo_eq]; exact _root_.Iop.BatchOne.BAnn.allLocal_coherent _) hW
    (fun _ => ansOK_atFull T)
    (fun d => sdAtFull_law T hc Bd aT W t (cfgOf d.1) shape pl0 pl1 code num h dS)
    (below_allLo _ _ _ _ hb) (fun _ => isArm_armL _ _ _) (fun _ => headSeeds_armL _ _)
    (by norm_num) m s0 s1 (fun d s hs' => isOther_tree (m d) s (hPt d s hs'))
    (fun d _ => OComp.AsksIn.mono (fun _ s hn hs' => hn (hPt d s hs')) (hno_armL (m d) _ _ _))
    hne Mk tq hq

end

section
variable {X X' RI : Type} [Fintype RI] [Nonempty RI] {A : (srS.toDecR srZ 524285).Claims X}
  {R : (srS.toDecR srZ 524285).RelationsAndEncoding A}
  (T : RestR (DecR.configurationOfStoredTable A R).I X' RI (Fin 1 → (Fin 19 → GE) × NZ)
    ((Fin srS.P.v → Bool) × Fin 1 → GE) srS.P.T.a linkSibSmall)
  (hd : T.dcd = (DecR.configurationOfStoredTable A R).D) (hc : T.coll = (DecR.configurationOfStoredTable A R).coll)
  (Bd : Type) (aT : RoundSplits T.test.shape)
  (W : QueryLayout 256 (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))))
  (t : Tag) (cfgOf : Dig 256 → List (Dig 256)) (shape : Bits)
  (pl0 pl1 : PlainPart (shapeOf (typedOracleCarrier (LrG T) Bd aT
             (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) t)
    (annOf (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) t))
  (code : (LrG T).Rec → List (Dig 256)) (num : ℕ → Plains T.bat.loc.shape → Bool)
  (h : (seedBS 19 1).b ≤ W.K) (dS : DecidableEq (Fin 1 → (Fin 19 → GE) × NZ))

/-- The arm with the lax Link at `LrG T`, made of the two public digests d = (c, p): c stands in the
rest of a table's name (`cfgOf c`), so in the first seed query. The code of the answers does not
hang on d: where p stands in a string is the coding's matter. -/
def armAtSmallPub (d : Dig 256 × Dig 256) :
    OutLA 256 (LrG T) (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall)) →
      TypedOracleComputation 256 W.K (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) Bool :=
  armL W (sdAtSmall T Bd aT W t (cfgOf d.1) shape pl0 pl1 code num h dS) (cAAtSmall T)

include hd hc in
set_option maxRecDepth 20000 in
/-- The entry's arm with the lax Link at `LrG T` and any wire with the laws `OKLA`, where the
configuration's digest c and the parameters' digest p are answers of the one hash function: c at the
public string s0, p at the public string s1 c. The maker runs; then the arm asks the function for c
and p itself and runs at them, through the coding at (c, p). It accepts, and what it promises fails
on the one-block entries, under that coding, of the maker's log of strings, with probability at most
n 2^-128 + 2 (n + 1)² / 2^256 at n = 5 (tq + tVL W). Hypotheses: the theorem on codes; `OKLA W`; the
bound on the maker's calls; of the family m of codings and the two strings: under every coding of
the family (at every d) s0 and every s1 c (at every c) code points of the spare oracle; s1 c is
never s0. From `variable` lines: T decodes and collides as the configuration's object (hd, hc); the
seed's number of blocks is at most W.K (h). -/
theorem atSmall_arm_pub2 (hA : BCHKS46At GF GE) (hW : OKLA W)
    (m : Dig 256 × Dig 256 → OracleCoding (typedOracleFamily 256 W.K
              (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall)))) 256)
    (s0 : List Bool) (s1 : Dig 256 → List Bool) (h0 : ∀ d, IsOther (m d) s0)
    (h1 : ∀ d c, IsOther (m d) (s1 c)) (hne : ∀ c, s1 c ≠ s0)
    (Mk : OComp (rom 256) (OutLA 256 (LrG T) (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))))
    (tq : ℕ) (hq : Mk.QueryBound tq) :
    Rom.Pr (expPub (armAtSmallPub T Bd aT W t cfgOf shape pl0 pl1 code num h dS) m
        (pub2 s0 s1) Mk)
        (fun _ => {x | x.2.2 = true ∧
          ¬ LinkHolds W (singleTr (m x.2.1) x.1.2) x.1.1.1 x.1.1.2.1 x.1.1.2.2.1 x.1.1.2.2.2.1}) ≤
      (((tq + tVL W) * (1 + 4) : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 128 +
        2 * (((tq + tVL W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 := by
  obtain ⟨ε, hs, hb⟩ := atSmall_sound T hd hc hA
  have hPt : ∀ d s, Pt2 s0 s1 s → IsOther (m d) s := by
    rintro d s (rfl | ⟨c, rfl⟩)
    · exact h0 d
    · exact h1 d c
  exact arm_pr_pub2 (L := LrG T) (εL := ε)
    (S := fun d => sdAtSmall T Bd aT W t (cfgOf d.1) shape pl0 pl1 code num h dS)
    (cA := fun _ => cAAtSmall T)
    (V := armAtSmallPub T Bd aT W t cfgOf shape pl0 pl1 code num h dS)
    hs linkSibSmall_local
    (by rw [_root_.Run.Twin.allLo_eq]; exact _root_.Iop.BatchOne.BAnn.allLocal_coherent _) hW
    (fun _ => ansOK_atSmall T)
    (fun d => sdAtSmall_law T hc Bd aT W t (cfgOf d.1) shape pl0 pl1 code num h dS)
    (below_allLo _ _ _ _ hb) (fun _ => isArm_armL _ _ _) (fun _ => headSeeds_armL _ _)
    (by norm_num) m s0 s1 (fun d s hs' => isOther_tree (m d) s (hPt d s hs'))
    (fun d _ => OComp.AsksIn.mono (fun _ s hn hs' => hn (hPt d s hs')) (hno_armL (m d) _ _ _))
    hne Mk tq hq

end

end TypedOracleCompiler.Compile.Batch.Cms
