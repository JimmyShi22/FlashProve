-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ArmSibCount.lean: the number of typed queries of the entry's arm at the written wire of
the written link (`wAtFull`, `wAtSmall`, Johnson/Flat/ArmSibClosed.lean), as a number.

The bounds of Johnson/Flat/ArmSibClosed.lean are said at n = 5 (tq + tVL W), where `tVL W` bounds
the typed queries of the entry's arm: four for the two seeds; one for each round of Link and one
more; a leaf and a path for each opening; a leaf and a path in the request tree.

  `tVL_wSib`      `tVL` at a wiring whose Link's part is `wSib` (Johnson/EntryRec/OklaSib.lean), as
                  a
                  function of the rounds' data, of the openings of the stored tables, of the depth
                  of the tables' code and of the depth of Link's request tree
  `sibF_len`, `sibF_nOpen`, `sibF_stored`, `sibF_max`; `sibS_…`   the four numbers at each size, by
                  evaluation in Lean's kernel
  `tVL_atFull`    tVL (wAtFull …) = 13545
  `tVL_atSmall`   tVL (wAtSmall …) = 7975

They are the numbers of Johnson/Flat/EntryCount.lean at a request tree with one leaf.

Limits: a count of typed queries as the bound `tVL` counts them (every opening at the greatest
depth), not of calls to the hash function, and not of what a run asks.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.ArmSibClosed

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob Hiop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.Slice OnBytes.Flat Cb Cb.Ood
open OnBytes.RunA (RestR LrG wSib bodiesSib)
open TypedOracleCompiler.Run.PQ (SOf)
open _root_.Run (ckP chalP)
open _root_.Run.PQ (CK XO View SgX)

section
variable {I X RI Seed Ans : Type} [Fintype RI] [Nonempty RI] [Fintype Seed] [Nonempty Seed] {a : ℕ}
  {C : CK} {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List XO}
  {dec : (Seed × Ans) × (Seed × Ans) → View → Bool}
  (T : RestR I X RI Seed Ans a (linkProtocolOfRoundData C ds a xs dec))
  (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

/-- The bound on the arm's typed queries at a wiring whose Link's part is the written link's own,
with the four numbers named. -/
theorem tVL_wSib {aT : RoundSplits T.test.shape} (wT : ProtocolQueryLayout 256 (K + 1) (batTC (LrG T) aT))
    (wB : ProtocolQueryLayout 256 (K + 1) T.bat) (depthReq depthReqT depthReqL : ℕ)
    (b : Bodies (LrG T) (List Bool)) {n1 n2 n3 n4 : ℕ}
    (h1 : (linkProtocolOfRoundData C ds a xs dec).shape.length = n1) (h2 : TypedOracleCompiler.Run.PQ.nOpen ds = n2)
    (h3 : (xs.map (·.count)).sum = n3) (h4 : max (TypedOracleCompiler.Run.PQ.maxDepth ds) a = n4) :
    tVL (wireOf2 (L := LrG T) (aT := aT) (aL := _root_.Run.Twin.allLo (SOf C ds)) (K + 1) wT
        (wSib T K chal) wB a depthReq depthReqT depthReqL b) =
      4 + ((n1 + 1) + ((n2 + n3) * (n4 + 1) + (depthReqL + 1))) := by
  rw [← h1, ← h2, ← h3, ← h4]
  rfl

end

/-- The rounds of the written link at the full size, the round in front among them. -/
theorem sibF_len : linkSibFull.shape.length = 42 := by decide +kernel

/-- The openings of the chain's own trees, at the full size. -/
theorem sibF_nOpen : TypedOracleCompiler.Run.PQ.nOpen dsFull = 285 := by decide +kernel

/-- The openings of the stored tables, at the full size. -/
theorem sibF_stored : (frD.xs.map (·.count)).sum = 124 := by decide +kernel

/-- The greatest depth, of the chain's own trees and of the tables' code, at the full size. -/
theorem sibF_max : max (TypedOracleCompiler.Run.PQ.maxDepth dsFull) frS.P.T.a = 32 := by decide +kernel

/-- The rounds of the written link at the small example, the round in front among them. -/
theorem sibS_len : linkSibSmall.shape.length = 25 := by decide +kernel

/-- The openings of the chain's own trees, at the small example. -/
theorem sibS_nOpen : TypedOracleCompiler.Run.PQ.nOpen dsSmall = 229 := by decide +kernel

/-- The openings of the stored tables, at the small example. -/
theorem sibS_stored : (srD.xs.map (·.count)).sum = 102 := by decide +kernel

/-- The greatest depth, of the chain's own trees and of the tables' code, at the small example. -/
theorem sibS_max : max (TypedOracleCompiler.Run.PQ.maxDepth dsSmall) srS.P.T.a = 23 := by decide +kernel

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

set_option maxRecDepth 20000 in
/-- The bound `tVL` at the written link of the full size is 13545. The entry's arm asks no more
typed queries (`isArm_armL`: the field `det`). -/
theorem tVL_atFull :
    tVL (wAtFull T K wT wB depthReq depthReqT salt embT prjT embB prjB) = 13545 :=
  (tVL_wSib T K (chalP .two K) wT wB depthReq depthReqT 0 (bodiesSib T salt embT prjT embB prjB)
    sibF_len sibF_nOpen sibF_stored sibF_max).trans (by norm_num)

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

set_option maxRecDepth 20000 in
/-- The bound `tVL` at the written link of the small example is 7975. The entry's arm asks no more
typed queries (`isArm_armL`: the field `det`). -/
theorem tVL_atSmall :
    tVL (wAtSmall T K wT wB depthReq depthReqT salt embT prjT embB prjB) = 7975 :=
  (tVL_wSib T K (chalP .two K) wT wB depthReq depthReqT 0 (bodiesSib T salt embT prjT embB prjB)
    sibS_len sibS_nOpen sibS_stored sibS_max).trans (by norm_num)

end

end TypedOracleCompiler.Compile.Batch.Cms
