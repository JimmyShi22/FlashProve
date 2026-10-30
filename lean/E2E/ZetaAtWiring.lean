-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ZetaAtWiring.lean: ten numbers of the full-size wiring (`wireOfFullD`,
Johnson/Flat/Dec/WiresAtSizes.lean): its four tree depths, the leaves of its three protocols' trees,
and the three protocols' numbers of rounds.

Summary. These numbers enter the bound on `zetaW`. Here each is expressed through the three files'
rounds' data, which are arbitrary; E2E/ZetaNumbers.lean evaluates them.

Main results.
  `lv_fullD`: `lv` (E2E/ZetaWires.lean) of the key file's, the link's and the proof file's wiring is
    `leavesW DK`, `leavesR ds` and `leavesW DP`.
  `depths_fullD`: the tree over an encoded index has the depth of the tables' code; the request
    trees have the depths that the wiring is given, the link's 0.
  `rounds_fullD`: the three protocols have `roundsW DK`, 1 + the link's rounds, and `roundsW DP`
    rounds (by the library's `length_sh`, Johnson/Top/Pub/CountsTop.lean).

Terms: E2E/HidingTerms.lean.

Limits. Nothing is evaluated. No security property is stated.

Definitions and helper lemmas.
  `roundsW D`, `leavesW D`: a whole file's rounds (three chains and three rounds between them) and
    the leaves of all its trees.
  `uL_length`: a list of the link's rounds' data gives as many rounds.


-/
import E2E.ZetaWires
import Johnson.Flat.Dec.WiresAtSizes
import Johnson.Top.Pub.CountsTop

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.ZetaAt
open TypedOracleCompiler.Iop TypedOracleCompiler.Joined OnBytes.Maker
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.Flat (RecFull)
open OnBytes.Slice (frS frZ)
open _root_.Run.PQ (CK View XO Dn)
open _root_.Run (ckP chalP)
open VerifiableInference.OnPublicFiles (threeProtocolsAtFullSize wireOfFullD)
open TypedOracleCompiler.Compile.Batch.Cms (batTC batLC wTC wLC wBC)

/-- The rounds of a whole file: three chains, the front round, the joining round, the seam. -/
def roundsW (D : WholeD) : ℕ := 1 + (D.ds₁.length + (1 + (D.ds₂.length + (1 + D.ds₃.length))))

/-- The leaves of all trees that a whole file sends. -/
def leavesW (D : WholeD) : ℕ := leavesT D.ds₁ + (leavesT D.ds₂ + leavesT D.ds₃)

theorem uL_length (C : CK) : ∀ ds : List TypedOracleCompiler.Run.PQ.RD,
    (TypedOracleCompiler.Run.PQ.uL C ds).length = ds.length
  | [] => rfl
  | _ :: ds => congrArg (· + 1) (uL_length C ds)

section
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (DK DP : WholeD)
  (runK : RecFull → View → View → View → Bool) (runP : X × RecFull → View → View → View → Bool)
  (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List XO) (dec : RecFull × RecFull → View → Bool)
  (rK rP : RecFull) (depthReq : ℕ) (early : X → X) (salt : ℕ)
  (P : (threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).Provers)
  (K depthReqT : ℕ)

local notation "Ff" => threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt
local notation "Lo" => OnBytes.Flat.Files.withProvers Ff P
local notation "Ww" =>
  wireOfFullD A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT

include A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT

/-- **The four depths of the wiring.** -/
theorem depths_fullD : (Ww).depth = frS.P.T.a ∧ (Ww).depthReq = depthReq ∧
    (Ww).depthReqT = depthReqT ∧ (Ww).depthReqL = 0 := ⟨rfl, rfl, rfl, rfl⟩

/-- **The leaves of the three wirings**, as computable functions of the rounds' data. -/
theorem lv_fullD : lv (Lo).offline.shape (Ff).annT (wTC Ww).sh = leavesW DK ∧
    lv (Lo).link.shape (Ff).annL (wLC Ww).sh = leavesR ds ∧
    lv (Lo).onlineBatch.loc.shape (Lo).onlineBatch.ann (wBC Ww).sh = leavesW DP :=
  ⟨lv_wqWhole (ckP .two) K (chalP .two K) (DK.at frS.P.T.a) (OnBytes.Flat.front₀ rK)
      (OnBytes.Flat.join₀ rK) ByteArray.empty OnBytes.Flat.silK runK,
    lv_wqW (ckP .two) K (chalP .two K) ds frS.P.T.a xs dec,
    lv_wqWhole (ckP .two) K (chalP .two K) (DP.at frS.P.T.a) (OnBytes.Flat.front₀ rP)
      (OnBytes.Flat.join₀ rP) ByteArray.empty OnBytes.Flat.silP runP⟩

omit K depthReqT in
/-- **The rounds of the three protocols.** -/
theorem rounds_fullD : (Lo).offline.shape.length = roundsW DK ∧
    (Lo).link.shape.length = 1 + ds.length ∧ (Lo).onlineBatch.loc.shape.length = roundsW DP := by
  refine ⟨?_, ?_, ?_⟩
  · exact OnBytes.K.Arm.length_sh (ckP .two) (DK.at frS.P.T.a) (OnBytes.Flat.front₀ rK)
      (OnBytes.Flat.join₀ rK) ByteArray.empty
  · show (_ :: TypedOracleCompiler.Run.PQ.uL (ckP .two) ds).length = _
    rw [List.length_cons, uL_length]
    omega
  · exact OnBytes.K.Arm.length_sh (ckP .two) (DP.at frS.P.T.a) (OnBytes.Flat.front₀ rP)
      (OnBytes.Flat.join₀ rP) ByteArray.empty

end

end AtPublicFiles.ZetaAt

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.ZetaAt.depths_fullD
#print axioms AtPublicFiles.ZetaAt.lv_fullD
#print axioms AtPublicFiles.ZetaAt.rounds_fullD
#print axioms AtPublicFiles.ZetaAt.uL_length
