-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Dec/CountAtFrame.lean: the compiled verifier's own count of typed queries (`tVC`) at the
wiring of the frame whose entry file's rounds' data, stored openings and decision are letters too
(`wireOfFullD`, `wireOfSmallD`, Johnson/Flat/Dec/WiresAtSizes.lean), as a plain function of the three
files' data. THE SIBLING OF Johnson/Flat/CountAtFrame.lean, whose two sections on the sizes are turned
here; its closed error `epsFrame` and the two laws on it are general in the wiring and are
called as they lie.

  `cntEntry ds xs a`: the entry file's arm's count less the four queries for two seeds: one for each
    round and one more; a leaf and a path for each opening, each at the greatest depth; a leaf in a
    request tree with one leaf. `cntEntry_dsFull`, `cntEntry_dsSmall`: at the written rounds: 13541 | 7971.
  `cntFrameFullD DK DP ds xs depthReq depthReqT`; `tVC_wireOfFullD`: tVC at that wiring is that number. No
    premise: K, the salt, the three decisions and the records are not read. (Small alike.)
  `cntFrameFullD_landed`: at the written rounds it is `cntFrameFull`.

Limits: those of the sibling's head. NO COUNT IS EVALUATED at any data of a key file or a proof file.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.CountAtFrame
import Johnson.Flat.Dec.WiresAtSizes

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.K.Arm (cntWhole length_sh)

/-- The entry file's arm's count, less the four queries for the two seeds, as a function of its
rounds' data, its stored openings and the depth of the tables' code. -/
def cntEntry (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List _root_.Run.PQ.XO) (a : ℕ) : ℕ :=
  ((ds.length + 1) + 1) +
    ((TypedOracleCompiler.Run.PQ.nOpen ds + (xs.map (·.count)).sum) *
      (max (TypedOracleCompiler.Run.PQ.maxDepth ds) a + 1) + (0 + 1))

/-- The rounds behind the round in front are as many as the data. -/
theorem length_uL (C : _root_.Run.PQ.CK) : ∀ ds : List TypedOracleCompiler.Run.PQ.RD,
    (TypedOracleCompiler.Run.PQ.uL C ds).length = ds.length
  | [] => rfl
  | _ :: ds => congrArg (· + 1) (length_uL C ds)

/-- The link's rounds: the round in front, and one for each entry of the data. -/
theorem length_linkW {Y : Type} (C : _root_.Run.PQ.CK) (ds : List TypedOracleCompiler.Run.PQ.RD) (a : ℕ)
    (xs : List _root_.Run.PQ.XO) (dec : Y → PQ.View → Bool) :
    (linkProtocolOfRoundData C ds a xs dec).shape.length = ds.length + 1 :=
  congrArg (· + 1) (length_uL C ds)

/-- At the written rounds of the full size. -/
theorem cntEntry_dsFull : cntEntry dsFull frD.xs frS.P.T.a = 13541 := by
  have h1 : dsFull.length + 1 = 42 := (length_linkW _ _ _ _ _).symm.trans sibF_len
  unfold cntEntry
  rw [h1, sibF_nOpen, sibF_stored, sibF_max]

/-- At the written rounds of the small size. -/
theorem cntEntry_dsSmall : cntEntry dsSmall srD.xs srS.P.T.a = 7971 := by
  have h1 : dsSmall.length + 1 = 25 := (length_linkW _ _ _ _ _).symm.trans sibS_len
  unfold cntEntry
  rw [h1, sibS_nOpen, sibS_stored, sibS_max]

/-- The count at the full size, as a function of the three files' data and the two depths. -/
def cntFrameFullD (DK DP : WholeD) (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List _root_.Run.PQ.XO)
    (depthReq depthReqT : ℕ) : ℕ :=
  cntWhole (DK.at frS.P.T.a) depthReqT + cntEntry ds xs frS.P.T.a +
    cntWhole (DP.at frS.P.T.a) depthReq

/-- The count at the small size. -/
def cntFrameSmallD (DK DP : WholeD) (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List _root_.Run.PQ.XO)
    (depthReq depthReqT : ℕ) : ℕ :=
  cntWhole (DK.at srS.P.T.a) depthReqT + cntEntry ds xs srS.P.T.a +
    cntWhole (DP.at srS.P.T.a) depthReq

/-- At the written rounds they are the sibling's. -/
theorem cntFrameFullD_landed (DK DP : WholeD) (depthReq depthReqT : ℕ) :
    cntFrameFullD DK DP dsFull frD.xs depthReq depthReqT =
      cntFrameFull DK DP depthReq depthReqT := by
  unfold cntFrameFullD cntFrameFull
  rw [cntEntry_dsFull]

theorem cntFrameSmallD_landed (DK DP : WholeD) (depthReq depthReqT : ℕ) :
    cntFrameSmallD DK DP dsSmall srD.xs depthReq depthReqT =
      cntFrameSmall DK DP depthReq depthReqT := by
  unfold cntFrameSmallD cntFrameSmall
  rw [cntEntry_dsSmall]

/-! ## The full size -/

section
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (DK DP : WholeD)
  (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List _root_.Run.PQ.XO)
  (dec : RecFull × RecFull → PQ.View → Bool) (rK rP : RecFull) (depthReq : ℕ)
  (early : X → X) (salt : ℕ)
  (P : (threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).Provers) (K depthReqT : ℕ)

/-- The key file's arm's count at the frame's wiring, at every data and decision. -/
theorem tVT_wireOfFullD :
    tVT (wireOfFullD A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT) =
      cntWhole (DK.at frS.P.T.a) depthReqT := by
  show 2 + (((chainsOf (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK)
    ByteArray.empty).sh.length + 1) + (nOpenW (DK.at frS.P.T.a) *
      (maxDepthW (DK.at frS.P.T.a) + 1) + (depthReqT + 1))) = _
  rw [length_sh]
  rfl

/-- The entry file's arm's count there: four, and a plain function of its rounds' data and stored
openings. The decision is not read. -/
theorem tVL_wireOfFullD :
    tVL (wireOfFullD A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT) =
      4 + cntEntry ds xs frS.P.T.a := by
  rw [wireOfFull_eq_sibD]
  haveI : Nonempty (Fin 1 → (Fin 29 → GE) × OnBytes.Slice.NZ) :=
    ⟨fun _ => (fun _ => 0, ⟨1, one_ne_zero⟩)⟩
  exact (tVL_wSib (restOfFullD A R DK DP runK runP ds xs dec rK rP depthReq early salt P) K (chalP .two K) _ _
    depthReq depthReqT 0 _ (length_linkW _ _ _ _ _) rfl rfl rfl)

/-- The proof file's arm's count there, at every data and decision. -/
theorem tVB_wireOfFullD :
    tVB (wireOfFullD A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT) =
      cntWhole (DP.at frS.P.T.a) depthReq := by
  show 2 + (((chainsOf (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP)
    ByteArray.empty).sh.length + 1) + (nOpenW (DP.at frS.P.T.a) *
      (maxDepthW (DP.at frS.P.T.a) + 1) + (depthReq + 1))) = _
  rw [length_sh]
  rfl

/-- **The compiled verifier's own count of typed queries at the frame's wiring is a plain function
of the two whole files' data and the two depths.** No premise. -/
theorem tVC_wireOfFullD :
    tVC (wireOfFullD A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT) =
      cntFrameFullD DK DP ds xs depthReq depthReqT := by
  have h := tVC_add_four (wireOfFullD A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT)
  rw [tVT_wireOfFullD, tVL_wireOfFullD, tVB_wireOfFullD] at h
  unfold cntFrameFullD
  omega

end

/-! ## The small size -/

section
variable {X : Type} (A : (srS.toDecR srZ 524285).Claims X)
  (R : (srS.toDecR srZ 524285).RelationsAndEncoding A) (DK DP : WholeD)
  (runK : RecSmall → PQ.View → PQ.View → PQ.View → Bool)
  (runP : X × RecSmall → PQ.View → PQ.View → PQ.View → Bool)
  (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List _root_.Run.PQ.XO)
  (dec : RecSmall × RecSmall → PQ.View → Bool) (rK rP : RecSmall) (depthReq : ℕ)
  (early : X → X) (salt : ℕ)
  (P : (threeProtocolsAtSmallSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).Provers) (K depthReqT : ℕ)

/-- The key file's arm's count at the frame's wiring, at every data and decision. -/
theorem tVT_wireOfSmallD :
    tVT (wireOfSmallD A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT) =
      cntWhole (DK.at srS.P.T.a) depthReqT := by
  show 2 + (((chainsOf (ckP .two) (DK.at srS.P.T.a) (front₀ rK) (join₀ rK)
    ByteArray.empty).sh.length + 1) + (nOpenW (DK.at srS.P.T.a) *
      (maxDepthW (DK.at srS.P.T.a) + 1) + (depthReqT + 1))) = _
  rw [length_sh]
  rfl

/-- The entry file's arm's count there: four, and a plain function of its rounds' data and stored
openings. The decision is not read. -/
theorem tVL_wireOfSmallD :
    tVL (wireOfSmallD A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT) =
      4 + cntEntry ds xs srS.P.T.a := by
  rw [wireOfSmall_eq_sibD]
  haveI : Nonempty (Fin 1 → (Fin 19 → GE) × OnBytes.Slice.NZ) :=
    ⟨fun _ => (fun _ => 0, ⟨1, one_ne_zero⟩)⟩
  exact (tVL_wSib (restOfSmallD A R DK DP runK runP ds xs dec rK rP depthReq early salt P) K (chalP .two K) _ _
    depthReq depthReqT 0 _ (length_linkW _ _ _ _ _) rfl rfl rfl)

/-- The proof file's arm's count there, at every data and decision. -/
theorem tVB_wireOfSmallD :
    tVB (wireOfSmallD A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT) =
      cntWhole (DP.at srS.P.T.a) depthReq := by
  show 2 + (((chainsOf (ckP .two) (DP.at srS.P.T.a) (front₀ rP) (join₀ rP)
    ByteArray.empty).sh.length + 1) + (nOpenW (DP.at srS.P.T.a) *
      (maxDepthW (DP.at srS.P.T.a) + 1) + (depthReq + 1))) = _
  rw [length_sh]
  rfl

/-- **The compiled verifier's own count of typed queries at the frame's wiring is a plain function
of the two whole files' data and the two depths.** No premise. -/
theorem tVC_wireOfSmallD :
    tVC (wireOfSmallD A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT) =
      cntFrameSmallD DK DP ds xs depthReq depthReqT := by
  have h := tVC_add_four (wireOfSmallD A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT)
  rw [tVT_wireOfSmallD, tVL_wireOfSmallD, tVB_wireOfSmallD] at h
  unfold cntFrameSmallD
  omega

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.cntEntry_dsFull
#print axioms VerifiableInference.OnPublicFiles.cntFrameFullD_landed
#print axioms VerifiableInference.OnPublicFiles.tVC_wireOfFullD
#print axioms VerifiableInference.OnPublicFiles.tVC_wireOfSmallD
