-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/WholeKey/Main.lean: INDEX PRIVACY OF THE SCHEME WITH THE WHOLE KEY PUBLISHED: THE THEOREM.
The statement Spec.wholeKeyPrivacy (Johnson/WholeKey/Statement.lean) is proved here, from its three
parts, each of which is a theorem of its own file.

A general theorem, with corollaries that cost a line each. This file states no goal of the release.

WHAT IT IS. For ANY object with out-of-domain (OOD) samples, any wires, any honest sides of its
three interactive protocols, under the premises PremW (Johnson/WholeKey/Premises.lean): at every
index of the range ok, the scheme argW (Johnson/WholeKey/Defs.lean), whose committer publishes THE
WHOLE KEY, has index privacy in the form of ZKCP/Gen.lean, in which the environment that picks the
instances sees the adversary's whole view and may decline, at one request a proof, with the
simulator NAMED (simWholeKey, Johnson/WholeKey/Wrap.lean) and the error WRITTEN OUT (zetaW,
Johnson/WholeKey/Zeta.lean).

WHAT IT IS NOT. It is a CONDITIONAL theorem at LETTERS, over TYPED ORACLES, of Lean terms that are
tied to no program. How far its premises are shown at the protocol of the release: the docstring of
wholeKeyPrivacy, below. Elsewhere they are shown to hold together at two toys alone. The head of
Johnson/WholeKey/Statement.lean says what the statement leans on, WHAT MUST GO WITH ANY QUOTE OF IT,
and what it does not say; all of that holds of the theorem, but for the one line "this file does not
prove it".

THE THREE PARTS (wholeKeyPrivacy_of_parts, Johnson/WholeKey/Assembly.lean, has the chain and the
  prices). LateSide.realToLate    (Johnson/LateSide/Whole.lean)    the real experiment against a
                         plain challenger that lays its secret-holding hash queries late: ζ's term
                         HASH.
  LateWorld.lateToWrap   (Johnson/LateWorld/Whole.lean)   that challenger against the reduction
                         around the real game of the interactive protocols: TAIL and SEEDS.
  LateWorld.premLate     (Johnson/LateWorld/PremOf.lean)  the premises of that step, from PremW.
Called inside the assembly: the real game against the simulated game, PARTS and STOPS (gameAtW,
Johnson/WrapLaws/AtKit.lean); the frame for one index (frameAt, Compile/PrivFrame/Top.lean).

Main names (namespace OnBytes.WholeKey).
  wholeKeyPrivacy           THE THEOREM.
  wholeKeyPrivacy_all       where the range is all indices: the library's
                            ZKCP.Gen.HasIndexPrivacyWith.
  wholeKeyPrivacy_overOne   over one hash function (ZKCP.privacyOn_overOne, ZKCP/OnRange.lean): the
                            same ζ. It takes ONE LETTER MORE: m : Rom.OracleCoding, a way to lay the typed
                            oracles over one hash function. This file has no closed value of it;
                            at an input r it is r.oracleCoding.
  wholeKeyPrivacy_strong    one request a call, in the form of ZKCP/Defs.lean:
                            ZKCP.StrongPrivacyOn. The same letter m.
  wholeKeyPrivacy_withId    with the digest of a code of the key laid in front of the key: ζ at one
                            query more. The same letter m.
  privacy_wholeOne, privacy_wholeId   the last two AT AN INPUT r of Johnson/Top/InnerCompiledVerifier.lean: the
                            schemes wholeOne r a.side and wholeId r a.side
                            (Johnson/WholeKey/AtInput.lean). THE ROAD ABOVE ENDS HERE: the step to
                            a key that is the commitment ID alone (wrapFront) has no theorem, and
                            nothing stands at the library's innerSystem.
  zeta_pad_le, zeta_pad_half, zeta_pad2_le, zeta_pad2_half   THE NUMBERS AT THE TWO TOYS: ζ + ζ is
                            at most 60/256 (about 0.23) and at most about 0.50, so below 1. THAT IS
                            WHERE THE STATEMENT BEGINS TO SPEAK; IT IS NOT "HIDES"
                            (Johnson/WholeKey/Half.lean); the second toy shows little.
  private_pad, private_pad2   THE THEOREM APPLIED: at the two toys (Johnson/WholeKey/Member.lean,
                            Johnson/WholeKey/Member2.lean): the conclusion, which compares THE REAL
                            EXPERIMENT WITH THE IDEAL ONE at each index of the range, and ζ + ζ < 1
                            at the named numbers of queries and requests. Two real experiments
                            against each other: real_pad, real_pad2 (Johnson/WholeKey/Half.lean).
Completeness, index binding, index privacy and the honest side's work at one term:
Johnson/WholeKey/Bundle.lean.

Terms: lean/GLOSSARY.md.

-/
import Johnson.WholeKey.Assembly
import Johnson.LateSide.Whole
import Johnson.LateWorld.Whole
import Johnson.LateWorld.PremOf
import Johnson.WholeKey.AtInputProof
import Johnson.WholeKey.Member
import Johnson.WholeKey.Member2

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.WholeKey
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- **Conditional theorem on index privacy of the hashed argument with the whole key published.** If
the 20 conditions of `PremW` hold. With the link proof's honest prover written in Lean all 20 are
proved at one fixed public-files digest, at which `verify` is not proved ever to be called
(`premW_laid`, E2E/LinkLaidPrivacy.lean). That is for Lean's form of the release's protocol, at
public files in scope, within bounds on copies, requests per copy and the sampled bits of a leaf's
salt. This is not the whole protocol: the key file's and the request's provers are placeholders that
send fixed messages. -/
theorem wholeKeyPrivacy : Spec.wholeKeyPrivacy :=
  wholeKeyPrivacy_of_parts LateSide.realToLate LateWorld.lateToWrap LateWorld.premLate

section Letters
variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (p : Params) (a : AtRecs lam L Bd aT aL)
  (Sm : Sims L) (ok : I → Prop) (Gs : L.OutOfDomainSeed → Prop) (Ryes : I → X → Prop) (c : CoinNums Bd)
  (u : NumsW) (i₀ : I)

/-- Where the range is all indices: the library's property. -/
theorem wholeKeyPrivacy_all (R : ZKCP.Gen.RelPair I X Unit Unit)
    (hR : ∀ i x w, R.yes i x w → Ryes i x)
    (hP : PremW W S cA p a Sm (fun _ => True) Gs Ryes c u) :
    ZKCP.Gen.HasIndexPrivacyWith R (argW W S cA r₀ p a.side) 1
      (simWholeKey W S cA r₀ a.side Sm i₀ u.s1 Gs Unit) (zetaW W S p a c u) :=
  privacyAll_of_wholeKeyPrivacy wholeKeyPrivacy I X lam L Bd aT aL W S cA r₀ p a Sm Gs Ryes c u R i₀
    hR hP

/-- **Over one hash function**: the same error. -/
theorem wholeKeyPrivacy_overOne {lam' : ℕ} (m : Rom.OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam')
    (R : ZKCP.Gen.RelPair I X Unit Unit) (hR : ∀ i x w, R.yes i x w → Ryes i x)
    (hP : PremW W S cA p a Sm ok Gs Ryes c u) :
    ZKCP.Gen.PrivacyOn R (Rom.schemeOverOneHashFunction m (argW W S cA r₀ p a.side)) 1
      (Rom.simOne m (simWholeKey W S cA r₀ a.side Sm i₀ u.s1 Gs Unit)) (zetaW W S p a c u) ok :=
  ZKCP.privacyOn_overOne m R _ 1 _ _ ok
    (wholeKeyPrivacy I X lam L Bd aT aL W S cA r₀ p a Sm ok Gs Ryes c u R i₀ hR hP)

/-- **One request a call, in the form of ZKCP/Defs.lean.** -/
theorem wholeKeyPrivacy_strong {lam' : ℕ} (m : Rom.OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam')
    (R : ZKCP.IndexedRelation I X Unit Unit) (hR : ∀ i x w, R.rel i x w → Ryes i x)
    (hP : PremW W S cA p a Sm ok Gs Ryes c u) :
    ZKCP.StrongPrivacyOn R
      (ZKCP.SpecialAny.oneOf (Rom.schemeOverOneHashFunction m (argW W S cA r₀ p a.side)))
      (ZKCP.Special.simOf (Rom.simOne m (simWholeKey W S cA r₀ a.side Sm i₀ u.s1 Gs Unit)))
      (zetaW W S p a c u) ok :=
  ZKCP.strongPrivacyOn_of_gen R (ZKCP.SpecialAny.agrees_oneOf _) _ _ ok
    (wholeKeyPrivacy_overOne W S cA r₀ p a Sm ok Gs Ryes c u i₀ m (ZKCP.Special.toPair R) hR hP)

/-- **With the digest of a code of the key laid in front of the key**: the error at one query more.
-/
theorem wholeKeyPrivacy_withId {lam' : ℕ} (m : Rom.OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam')
    (R : ZKCP.IndexedRelation I X Unit Unit) (hR : ∀ i x w, R.rel i x w → Ryes i x)
    (hP : PremW W S cA p a Sm ok Gs Ryes c u) (code : FullKey lam L aT aL → Option ZKCP.Str) :
    ZKCP.StrongPrivacyOn R
      (withId (ZKCP.SpecialAny.oneOf (Rom.schemeOverOneHashFunction m (argW W S cA r₀ p a.side))) code)
      ((wrapId (W := Unit) code).sim
        (ZKCP.Special.simOf (Rom.simOne m (simWholeKey W S cA r₀ a.side Sm i₀ u.s1 Gs Unit))) id)
      (fun t N => zetaW W S p a c u (t + 1) N) ok :=
  privacyOn_withId R _ _ _ code ok
    (wholeKeyPrivacy_strong W S cA r₀ p a Sm ok Gs Ryes c u i₀ m R hR hP)

end Letters

/-! ## At an input -/

section Input
open VerifiableInference.OnPublicFiles
variable (r : InnerCompilerInput) (a : AtRecs 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits) (Sm : Sims r.protocol) (ok : r.Index → Prop)
  (Gs : r.protocol.OutOfDomainSeed → Prop) (Ryes : r.Index → r.Instance → Prop) (c : CoinNums r.LeafBody) (u : NumsW) (i₀ : r.Index)

/-- **At an input r of Johnson/Top/InnerCompiledVerifier.lean, over its own way to one hash function** (r.oracleCoding),
one request a call: the scheme wholeOne r a.side (Johnson/WholeKey/AtInput.lean). -/
theorem privacy_wholeOne (R : ZKCP.IndexedRelation r.Index r.Instance Unit Unit)
    (hR : ∀ i x w, R.rel i x w → Ryes i x)
    (hP : PremW r.queryLayout r.seedQueries r.answerCode r.compilerParameters a Sm ok Gs Ryes c u) :
    ZKCP.StrongPrivacyOn R (wholeOne r a.side)
      (ZKCP.Special.simOf
        (Rom.simOne r.oracleCoding (simWholeKey r.queryLayout r.seedQueries r.answerCode r.fixedSample a.side Sm i₀ u.s1 Gs Unit)))
      (zetaW r.queryLayout r.seedQueries r.compilerParameters a c u) ok :=
  wholeKeyPrivacy_strong r.queryLayout r.seedQueries r.answerCode r.fixedSample r.compilerParameters a Sm ok Gs Ryes c u i₀ r.oracleCoding R hR hP

/-- **The scheme whose published key begins with the commitment ID** (wholeId r a.side): the error
at one query more. -/
theorem privacy_wholeId (R : ZKCP.IndexedRelation r.Index r.Instance Unit Unit)
    (hR : ∀ i x w, R.rel i x w → Ryes i x)
    (hP : PremW r.queryLayout r.seedQueries r.answerCode r.compilerParameters a Sm ok Gs Ryes c u) :
    ZKCP.StrongPrivacyOn R (wholeId r a.side)
      ((wrapId (W := Unit) fun k => r.keyCode (lowKey k)).sim
        (ZKCP.Special.simOf
          (Rom.simOne r.oracleCoding (simWholeKey r.queryLayout r.seedQueries r.answerCode r.fixedSample a.side Sm i₀ u.s1 Gs Unit))) id)
      (fun t N => zetaW r.queryLayout r.seedQueries r.compilerParameters a c u (t + 1) N) ok :=
  wholeKeyPrivacy_withId r.queryLayout r.seedQueries r.answerCode r.fixedSample r.compilerParameters a Sm ok Gs Ryes c u i₀ r.oracleCoding R hR hP
    fun k => r.keyCode (lowKey k)

end Input

/-! ## The theorem applied -/

theorem zeta_pad_le :
    zetaW Member.WP Member.SP Member.pP Member.atP Member.cnP Member.nuP 1 1 ≤ 30 / 256 := by
  have hT : Prob.pOver (Member.atP.M + 1) Member.nuP.s1 1 = 0 := by
    show Prob.pOver 1 1 1 = 0
    unfold Prob.pOver
    rw [Prob.binTail_eq_sum_Icc]
    simp
  have hz : zetaW Member.WP Member.SP Member.pP Member.atP Member.cnP Member.nuP 1 1 =
      Rom.costTotal (S := typedOracleFamily 8 Member.WP.K Member.CP) (eW Member.WP Member.SP Member.atP 1)
        (mW Member.WP Member.atP 1) (bitsW (lam := 8) Member.pP Member.cnP)
        (osW Member.WP Member.atP) 1 := by
    unfold zetaW
    rw [hT]
    show (0 : ℝ≥0∞) + (0 + ((0 + 1 : ℕ) : ℝ≥0∞) * 0 + ((1 : ℕ) : ℝ≥0∞) * 0) +
      (0 + ((0 + 1 : ℕ) : ℝ≥0∞) * 0 + ((1 : ℕ) : ℝ≥0∞) * 0) + ((0 + 2 : ℕ) : ℝ≥0∞) * 0 + _ = _
    simp
  rw [hz]
  exact Member.hash_pad

/-- **At the first toy ζ + ζ < 1**, at one query and one request (at most 60/256). -/
theorem zeta_pad_half :
    zetaW Member.WP Member.SP Member.pP Member.atP Member.cnP Member.nuP 1 1 +
      zetaW Member.WP Member.SP Member.pP Member.atP Member.cnP Member.nuP 1 1 < 1 := by
  refine lt_of_le_of_lt (add_le_add zeta_pad_le zeta_pad_le) ?_
  rw [ENNReal.div_add_div_same]
  refine ENNReal.div_lt_of_lt_mul ?_
  norm_num

/-- **At the first toy**: for every pair of relations, index privacy (the real experiment against
the ideal one) at both indices; at one query and one request ζ + ζ < 1. -/
theorem private_pad (R : ZKCP.Gen.RelPair Bool Unit Unit Unit) (r₀ : Hiop.Seeded.pad.Rec)
    (i₀ : Bool) :
    ZKCP.Gen.PrivacyOn R (argW Member.WP Member.SP Member.cAP r₀ Member.pP Member.atP.side) 1
        (simWholeKey Member.WP Member.SP Member.cAP r₀ Member.atP.side Member.smP i₀ Member.nuP.s1
          (fun _ => True) Unit)
        (zetaW Member.WP Member.SP Member.pP Member.atP Member.cnP Member.nuP) (fun _ => True) ∧
      zetaW Member.WP Member.SP Member.pP Member.atP Member.cnP Member.nuP 1 1 +
        zetaW Member.WP Member.SP Member.pP Member.atP Member.cnP Member.nuP 1 1 < 1 :=
  ⟨wholeKeyPrivacy _ _ _ _ _ _ _ _ _ _ r₀ _ _ _ _ _ (fun i x => ∃ w, R.yes i x w) _ _ R i₀
      (fun _ _ w h => ⟨w, h⟩) (Member.premW_pad _), zeta_pad_half⟩

theorem zeta_pad2_le :
    zetaW Member2.W2 Member2.S2 Member2.p2 Member2.at2 Member2.cn2 Member2.nu2 1 3 ≤
      1073741824 / 4294967296 + 204 / 4294967296 := by
  have hz : zetaW Member2.W2 Member2.S2 Member2.p2 Member2.at2 Member2.cn2 Member2.nu2 1 3 =
      Prob.pOver (Member2.at2.M + 1) Member2.nu2.s1 3 +
        Rom.costTotal (S := typedOracleFamily 32 Member2.W2.K Member2.C2)
          (eW Member2.W2 Member2.S2 Member2.at2 3) (mW Member2.W2 Member2.at2 3)
          (bitsW (lam := 32) Member2.p2 Member2.cn2) (osW Member2.W2 Member2.at2) 1 := by
    unfold zetaW
    show Prob.pOver (Member2.at2.M + 1) Member2.nu2.s1 3 +
      (0 + ((1 + 1 : ℕ) : ℝ≥0∞) * 0 + ((3 : ℕ) : ℝ≥0∞) * 0) +
      (0 + ((1 + 1 : ℕ) : ℝ≥0∞) * 0 + ((3 : ℕ) : ℝ≥0∞) * 0) + ((1 + 2 : ℕ) : ℝ≥0∞) * 0 + _ = _
    simp
  rw [hz]
  exact add_le_add Member2.tail_pad2 Member2.hash_pad2

/-- **At the second toy ζ + ζ < 1**, at one query and three requests (at most about 0.50). -/
theorem zeta_pad2_half :
    zetaW Member2.W2 Member2.S2 Member2.p2 Member2.at2 Member2.cn2 Member2.nu2 1 3 +
      zetaW Member2.W2 Member2.S2 Member2.p2 Member2.at2 Member2.cn2 Member2.nu2 1 3 < 1 := by
  refine lt_of_le_of_lt (add_le_add zeta_pad2_le zeta_pad2_le) ?_
  simp only [ENNReal.div_add_div_same]
  refine ENNReal.div_lt_of_lt_mul ?_
  norm_num

/-- **At the second toy**: for every pair of relations, index privacy (the real experiment against
the ideal one) at the two indices in range; at one query and three requests ζ + ζ < 1. -/
theorem private_pad2 (R : ZKCP.Gen.RelPair (Option Bool) Unit Unit Unit)
    (r₀ : Hiop.Seeded.Two.pad2.Rec) (i₀ : Option Bool) :
    ZKCP.Gen.PrivacyOn R (argW Member2.W2 Member2.S2 Member2.cA2 r₀ Member2.p2 Member2.at2.side) 1
        (simWholeKey Member2.W2 Member2.S2 Member2.cA2 r₀ Member2.at2.side Member2.sm2 i₀
          Member2.nu2.s1 (fun _ => True) Unit)
        (zetaW Member2.W2 Member2.S2 Member2.p2 Member2.at2 Member2.cn2 Member2.nu2)
        Member2.ok2 ∧
      zetaW Member2.W2 Member2.S2 Member2.p2 Member2.at2 Member2.cn2 Member2.nu2 1 3 +
        zetaW Member2.W2 Member2.S2 Member2.p2 Member2.at2 Member2.cn2 Member2.nu2 1 3 < 1 :=
  ⟨wholeKeyPrivacy _ _ _ _ _ _ _ _ _ _ r₀ _ _ _ _ _ (fun i x => ∃ w, R.yes i x w) _ _ R i₀
      (fun _ _ w h => ⟨w, h⟩) (Member2.premW_pad2 _), zeta_pad2_half⟩

end OnBytes.WholeKey

#print axioms OnBytes.WholeKey.wholeKeyPrivacy
#print axioms OnBytes.WholeKey.wholeKeyPrivacy_all
#print axioms OnBytes.WholeKey.wholeKeyPrivacy_overOne
#print axioms OnBytes.WholeKey.wholeKeyPrivacy_strong
#print axioms OnBytes.WholeKey.wholeKeyPrivacy_withId
#print axioms OnBytes.WholeKey.zeta_pad_half
#print axioms OnBytes.WholeKey.zeta_pad2_half
#print axioms OnBytes.WholeKey.privacy_wholeOne
#print axioms OnBytes.WholeKey.privacy_wholeId
#print axioms OnBytes.WholeKey.private_pad
#print axioms OnBytes.WholeKey.private_pad2
