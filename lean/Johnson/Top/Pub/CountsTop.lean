-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Pub/CountsTop.lean: the three arms' own counts of typed queries at the one wiring of the
three files (`topWFull`, `topWSmall`, Johnson/Top/ArmTopFull.lean, ArmTopSmall.lean): the entry
file's arm's as a number; the key file's and the proof file's as plain functions of the written
data G; and one test on G under which all three are small beside 2^64.

Why. The errors of the three arms' bounds are said at n = a small multiple of "the committer's and
the prover's queries and the arm's own count" (`tVT`, `tVL`, `tVB`,
Johnson/TypedOracleCompiler/RecCompile/KeyAns.lean, LinkOnly.lean, ProofAns.lean). A figure for such an error takes
a bound on that count as a premise. Here the premise comes down to a test on G that has code: Lean's
compiler takes it.

Main names (the same with Small).
  `cntWhole D dep`: the count of the arm of a file of three chains with the data D and a request
    tree of the depth dep: two for the seed; one for each round and one more; a leaf and a path for
    each opening, each at the greatest depth; a leaf and a path in the request tree.
  `length_sh`: a file has three rounds and one for each entry of its three lists.
  `tVL_topFull`: tVL W = 13545, at every A, E, G, P (`tVL_topSmall`: 7975): the entry file's wire
    record does not read G; by `tVL_wSib` and the four evaluations of
    Johnson/Flat/ArmSibCount.lean, at a request tree with one leaf.
  `cntKeyFull G`, `cntProofFull G`; `tVT_topFull`: tVT W = cntKeyFull G; `tVB_topFull`:
    tVB W = cntProofFull G: by unfolding and `length_sh`.
  `countsFullB G`: the test: both are at most 2^62.
  `counts_topFull_64`: where the test says yes and t is at most 2^63: t + 1 + tVT W, t + 1 + tVL W
    and t + tVB W are at most 2^64.

Limits. Arithmetic on definitions: no bound of an arm, no probability, nothing on soundness. G IS A
LETTER, AND THE TEST IS EVALUATED AT NO G HERE: no figure for `cntKeyFull` or `cntProofFull` is
given. At data made of public files the test's value hangs on these files. Where the makers' test on
a file's dry run fails, that file's data are three empty lists (Johnson/Flat/WireAt.lean) and its
count is small for nothing. The counts are bounds as `tVQB` counts (every opening at the greatest
depth), in typed queries: not calls of the hash function, and not what a run asks. The thresholds
2^62, 2^63 and 2^64 are a choice.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.ArmTopFull
import Johnson.Top.ArmTopSmall
import Johnson.Flat.ArmSibCount
import Johnson.TypedOracleCompiler.RecCompile.KeyAns
import Johnson.TypedOracleCompiler.RecCompile.ProofAns
import OnBytes.Maker.WholeLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 20000

noncomputable section

namespace OnBytes.K.Arm
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Compile.Batch.Cms OnBytes.K.Left OnBytes.Flat OnBytes.RunA OnBytes.Slice
open OnBytes.Tie Hiop Cb Cb.Ood
open OnBytes.K OnBytes.Maker
open VerifiableInference.OnPublicFiles
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run
open _root_.Run.PQ (CK)
open _root_.Compile.Joined (plainRound)

/-- The bound on the typed queries of the arm of a file of three chains, as a function of the
file's data D and the depth of its request tree: two for the seed; one for each round and one more;
a leaf and a path for each opening, each at the greatest depth; a leaf and a path in the request
tree. -/
def cntWhole (D : WholeD) (dep : ℕ) : ℕ :=
  2 + ((1 + (D.ds₁.length + (1 + (D.ds₂.length + (1 + D.ds₃.length)))) + 1) +
    (nOpenW D * (maxDepthW D + 1) + (dep + 1)))

/-- The number of rounds of a file: the front, the joining round, the seam, and one for each entry
of the three lists. -/
theorem length_sh (C : CK) (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3) :
    (chainsOf C D tF tJ t3).sh.length =
      1 + (D.ds₁.length + (1 + (D.ds₂.length + (1 + D.ds₃.length)))) := by
  show (plainRound TF tF :: (uLT C D.ds₁ ++ plainRound TJ tJ :: (uLT C D.ds₂ ++
    plainRound T3 t3 :: uLT C D.ds₃))).length = _
  simp only [List.length_cons, List.length_append, length_uLT]
  omega

section Full
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X) (E : Coding A) (G : FilesParameters X RecFull)
  (P : (threeProtocolsFromDryRunAtFullSize A (Flat.relationsAndEncodingOfClaims A E) G).Provers)

/-- The key file's arm's count at the full size, as a function of G's data. -/
def cntKeyFull : ℕ := cntWhole ((dataKFull G).at frS.P.T.a) G.k.oneTime.binding.logLeaves

/-- The proof file's arm's count at the full size, as a function of G's data. -/
def cntProofFull : ℕ := cntWhole ((dataPFull G).at frS.P.T.a) G.depthReq

/-- **The entry file's arm's count at the one wiring is a number**, at every A, E, G, P. -/
theorem tVL_topFull : tVL (topWFull A E G P) = 13545 := by
  have h := tVL_wSib (restFullAt A E G P) (KFullAt G) (chalP .two (KFullAt G))
    (aT := (threeProtocolsFromDryRunAtFullSize A (Flat.relationsAndEncodingOfClaims A E) G).annT) (topWTFull G) (topWBFull G) G.depthReq
    G.k.oneTime.binding.logLeaves 0
    (bodiesSib (restFullAt A E G P) topSaltFull (topEmbTFull A E G P) (topPrjTFull A E G P)
      (topEmbBFull A E G P) (topPrjBFull A E G P))
    sibF_len sibF_nOpen sibF_stored sibF_max
  exact h

/-- **The key file's arm's count at the one wiring is `cntKeyFull G`.** -/
theorem tVT_topFull : tVT (topWFull A E G P) = cntKeyFull G := by
  show 2 + (((chainsOf (ckP .two) ((dataKFull G).at frS.P.T.a) (front₀ G.rec₀) (join₀ G.rec₀)
    ByteArray.empty).sh.length + 1) + (nOpenW ((dataKFull G).at frS.P.T.a) *
      (maxDepthW ((dataKFull G).at frS.P.T.a) + 1) + (G.k.oneTime.binding.logLeaves + 1))) = _
  rw [length_sh]
  rfl

/-- **The proof file's arm's count at the one wiring is `cntProofFull G`.** -/
theorem tVB_topFull : tVB (topWFull A E G P) = cntProofFull G := by
  show 2 + (((chainsOf (ckP .two) ((dataPFull G).at frS.P.T.a) (front₀ G.z₀.2) (join₀ G.z₀.2)
    ByteArray.empty).sh.length + 1) + (nOpenW ((dataPFull G).at frS.P.T.a) *
      (maxDepthW ((dataPFull G).at frS.P.T.a) + 1) + (G.depthReq + 1))) = _
  rw [length_sh]
  rfl

/-- One test on G's data: the two counts are at most 2^62. -/
def countsFullB : Bool := decide (cntKeyFull G ≤ 2 ^ 62) && decide (cntProofFull G ≤ 2 ^ 62)

/-- **Where the test says yes, and t is at most 2^63: the three sums are at most 2^64.** -/
theorem counts_topFull_64 (h : countsFullB G = true) {t : ℕ} (ht : t ≤ 2 ^ 63) :
    t + 1 + tVT (topWFull A E G P) ≤ 2 ^ 64 ∧ t + 1 + tVL (topWFull A E G P) ≤ 2 ^ 64 ∧
      t + tVB (topWFull A E G P) ≤ 2 ^ 64 := by
  unfold countsFullB at h
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
  rw [tVT_topFull, tVL_topFull, tVB_topFull]
  have e62 : (2 : ℕ) ^ 64 = 4 * 2 ^ 62 := by norm_num
  have e63 : (2 : ℕ) ^ 63 = 2 * 2 ^ 62 := by norm_num
  have big : 13545 + 1 ≤ (2 : ℕ) ^ 62 := by norm_num
  omega

end Full

section Small
variable {X : Type} (A : (srS.toDecR srZ 524285).Claims X) (E : Coding A) (G : FilesParameters X RecSmall)
  (P : (threeProtocolsFromDryRunAtSmallSize A (Flat.relationsAndEncodingOfClaims A E) G).Provers)

/-- The key file's arm's count at the small size, as a function of G's data. -/
def cntKeySmall : ℕ := cntWhole ((dataKSmall G).at srS.P.T.a) G.k.oneTime.binding.logLeaves

/-- The proof file's arm's count at the small size, as a function of G's data. -/
def cntProofSmall : ℕ := cntWhole ((dataPSmall G).at srS.P.T.a) G.depthReq

/-- **The entry file's arm's count at the one wiring is a number**, at every A, E, G, P. -/
theorem tVL_topSmall : tVL (topWSmall A E G P) = 7975 := by
  have h := tVL_wSib (restSmallAt A E G P) (KSmallAt G) (chalP .two (KSmallAt G))
    (aT := (threeProtocolsFromDryRunAtSmallSize A (Flat.relationsAndEncodingOfClaims A E) G).annT) (topWTSmall G) (topWBSmall G) G.depthReq
    G.k.oneTime.binding.logLeaves 0
    (bodiesSib (restSmallAt A E G P) topSaltSmall (topEmbTSmall A E G P) (topPrjTSmall A E G P)
      (topEmbBSmall A E G P) (topPrjBSmall A E G P))
    sibS_len sibS_nOpen sibS_stored sibS_max
  exact h

/-- **The key file's arm's count at the one wiring is `cntKeySmall G`.** -/
theorem tVT_topSmall : tVT (topWSmall A E G P) = cntKeySmall G := by
  show 2 + (((chainsOf (ckP .two) ((dataKSmall G).at srS.P.T.a) (front₀ G.rec₀) (join₀ G.rec₀)
    ByteArray.empty).sh.length + 1) + (nOpenW ((dataKSmall G).at srS.P.T.a) *
      (maxDepthW ((dataKSmall G).at srS.P.T.a) + 1) + (G.k.oneTime.binding.logLeaves + 1))) = _
  rw [length_sh]
  rfl

/-- **The proof file's arm's count at the one wiring is `cntProofSmall G`.** -/
theorem tVB_topSmall : tVB (topWSmall A E G P) = cntProofSmall G := by
  show 2 + (((chainsOf (ckP .two) ((dataPSmall G).at srS.P.T.a) (front₀ G.z₀.2) (join₀ G.z₀.2)
    ByteArray.empty).sh.length + 1) + (nOpenW ((dataPSmall G).at srS.P.T.a) *
      (maxDepthW ((dataPSmall G).at srS.P.T.a) + 1) + (G.depthReq + 1))) = _
  rw [length_sh]
  rfl

/-- One test on G's data: the two counts are at most 2^62. -/
def countsSmallB : Bool := decide (cntKeySmall G ≤ 2 ^ 62) && decide (cntProofSmall G ≤ 2 ^ 62)

/-- **Where the test says yes, and t is at most 2^63: the three sums are at most 2^64.** -/
theorem counts_topSmall_64 (h : countsSmallB G = true) {t : ℕ} (ht : t ≤ 2 ^ 63) :
    t + 1 + tVT (topWSmall A E G P) ≤ 2 ^ 64 ∧ t + 1 + tVL (topWSmall A E G P) ≤ 2 ^ 64 ∧
      t + tVB (topWSmall A E G P) ≤ 2 ^ 64 := by
  unfold countsSmallB at h
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
  rw [tVT_topSmall, tVL_topSmall, tVB_topSmall]
  have e62 : (2 : ℕ) ^ 64 = 4 * 2 ^ 62 := by norm_num
  have e63 : (2 : ℕ) ^ 63 = 2 * 2 ^ 62 := by norm_num
  have big : 7975 + 1 ≤ (2 : ℕ) ^ 62 := by norm_num
  omega

end Small

end OnBytes.K.Arm

#print axioms OnBytes.K.Arm.tVL_topFull
#print axioms OnBytes.K.Arm.tVT_topFull
#print axioms OnBytes.K.Arm.tVB_topFull
#print axioms OnBytes.K.Arm.counts_topFull_64
#print axioms OnBytes.K.Arm.tVL_topSmall
#print axioms OnBytes.K.Arm.tVT_topSmall
#print axioms OnBytes.K.Arm.tVB_topSmall
#print axioms OnBytes.K.Arm.counts_topSmall_64
