-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/OpensCommitOverTypedOracles.lean: WITH THE HONEST COMMITTER `committerOverTypedOracles`
(Johnson/TypedOracleCompiler/RecCompile/CommitOverTypedOracles.lean), TIED TO NO PROGRAM: whoever opens a key (root, record) of
the second form's scheme, by running that committer again, opens it to what the library's extractor
decodes from that key and its maker's log, but for a probability that is written out; and the
committer's count of queries to the hash function. AT LETTERS: any object with records, wire, wire
of the record and coding.

Main names. `committerQueryCount`, `queryBound_committerOverTypedOracles_one`: the committer's queries to one hash function under
a coding m; `committerQueryCount_eq`: that count is 2 · 2 ^ depth + 2 (K + 1) under every coding, where lam is not
0. `cost_committerLeafHashes`, `cost_pairUpCommitterNodes`, `cost_committerTreeLevels`, `cost_committerOverTypedOracles`: the count at any weights
of the oracles, by the library's count that carries a property of the result along (`OComp.CA`,
Compile/CostPost.lean: the levels' count is bounded only at lists of the right length, and a plain
bound would have to hold at every list). `opens_committerOverTypedOracles`: index binding of the scheme with
openings in place of proofs (ZKCP/WithOpenings.lean). `VerifiableInference.OnPublicFiles.openingByCommitterMatchesExtractor r β`:
that sentence at an input r of Johnson/Top/InnerCompiledVerifier.lean; `opens_committerOverTypedOracles` gives it where r's
committer is `committerOverTypedOracles`, under its own premises at r's letters: the wire's laws and hdec
(`openingByCommitterMatchesExtractor_withCommitterOverTypedOracles`, Johnson/Top/BindsAtInnerSystem.lean).

How: `binding_of_badW` (Johnson/TypedOracleCompiler/RecCompile/OpensTwoStage.lean) at no public reading, fed by
`good_committerOverTypedOracles` and the count over one hash function; then `Rom.binding_withOpenings_rom` (the same
file). The count: `OComp.CA.cost`, then `overOneN_all`, `queryBound_overOneN`, `cnt_all`
(Rom/OverOneN.lean).

Kin in the library. `committerQueryCount_eq` proves the K + 1 blocks of the seed's oracle at any lam but 0.
`binding_withOpenings` with `traceOpens_argBKE` (Compile/Batch/WithOpenings.lean) is the like of
`opens_committerOverTypedOracles` at the compiler's first form, over typed oracles. hdec is, to the letter, the
field `dec_enc` of `HolographicProtocol.WiredR` (Hiop/RecInterface.lean).

Limits.
- THE BOUND IS A TERM IN THE WIRE: `committerQueryCount W S m` is 2 · 2 ^ depth + 2 (K + 1). At a huge wire the
  statement says nothing.
- hdec (the decoder gives every index back from its honest encoding and record) IS A PREMISE. At an
  index type that holds a member that the decoder never gives it is false. Beside `noneColl`, one of
  the sixteen hypotheses of Johnson/Top/InnerCompiledVerifier.lean, it forces that no honest word has a
  collision at any seed.
- ONE CODING, FIXED BEFORE THE HASH FUNCTION IS DRAWN. A scheme whose coding or wire of the record
  hangs on digests that are themselves answers of the hash function is not covered.
- The verifier is idle in this statement: nothing says that it accepts anything under such a key.
  Nothing on soundness or completeness. Not claimed: anything on hiding.
- No program's committer or commitment is spoken of.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.CommitOverTypedOracles
import Johnson.TypedOracleCompiler.RecCompile.OpensTwoStage
import Johnson.Top.InnerCompiledVerifier
import Compile.CostPost
import Rom.CutKit

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob ZKCP
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)

/-- The committer's count of queries to one hash function under the coding m. -/
def committerQueryCount (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) : ℕ :=
  2 ^ W.depth * m.blocks OracleName.leaf + 2 ^ W.depth * m.blocks OracleName.node + 2 * m.blocks (OracleName.fb S.t)

/-! ### The counts -/

section Count
variable (w : OracleName → ℕ)

/-- The leaves: one query an input, and as many answers. -/
theorem cost_committerLeafHashes : ∀ xs : List (LeafIn (typedOracleCarrier L Bd aT aL)),
    OComp.CA (fun o _ => w o) (committerLeafHashes W xs) (xs.length * w OracleName.leaf)
      fun out => out.length = xs.length
  | [] => rfl
  | x :: xs => by
      show OComp.CA (fun o _ => w o)
        ((OComp.ask (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) OracleName.leaf x).bind fun u =>
          (committerLeafHashes W xs).bind fun us => .pure ((show Dig lam from u) :: us)) _ _
      have h1 : OComp.CA (fun o _ => w o)
          (OComp.ask (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) OracleName.leaf x) (w OracleName.leaf)
          fun _ => True :=
        ⟨0, Nat.le_refl _, fun _ => trivial⟩
      refine OComp.CA.bind' h1 (m' := xs.length * w OracleName.leaf) (fun u _ => ?_) ?_
      · exact OComp.CA.map (cost_committerLeafHashes xs) _ fun us hus => congrArg (· + 1) hus
      · rw [List.length_cons, Nat.succ_mul]
        omega

/-- One step from 2 n digests: n queries, n digests. -/
theorem cost_pairUpCommitterNodes : ∀ (n : ℕ) (l : List (Dig lam)), l.length = 2 * n →
    OComp.CA (fun o _ => w o) (pairUp (committerNodeHash W) l) (n * w OracleName.node) fun l' => l'.length = n
  | 0, [], _ => rfl
  | 0, _ :: _, hl => by simp at hl
  | n + 1, [], hl => by simp at hl
  | n + 1, [_], hl => by
      simp only [List.length_singleton] at hl
      omega
  | n + 1, a :: b :: t, hl => by
      show OComp.CA (fun o _ => w o) ((committerNodeHash W a b).bind fun c =>
        (pairUp (committerNodeHash W) t).bind fun r => OComp.pure (c :: r)) _ _
      have ht : t.length = 2 * n := by
        simp only [List.length_cons] at hl
        omega
      have h1 : OComp.CA (fun o _ => w o) (committerNodeHash W a b) (w OracleName.node) fun _ => True :=
        ⟨0, Nat.le_refl _, fun _ => trivial⟩
      refine OComp.CA.bind' h1 (m' := n * w OracleName.node) (fun c _ => ?_) ?_
      · exact OComp.CA.map (cost_pairUpCommitterNodes n t ht) _ fun r hr => congrArg (· + 1) hr
      · rw [Nat.succ_mul]
        omega

/-- The levels over 2 ^ d digests: at most 2 ^ d queries. -/
theorem cost_committerTreeLevels : ∀ (d : ℕ) (l : List (Dig lam)), l.length = 2 ^ d →
    OComp.CA (fun o _ => w o) (levelsM (committerNodeHash W) d l) (2 ^ d * w OracleName.node) fun _ => True
  | 0, _, _ => trivial
  | d + 1, l, hl => by
      show OComp.CA (fun o _ => w o) ((pairUp (committerNodeHash W) l).bind fun u =>
        (levelsM (committerNodeHash W) d u).bind fun r => OComp.pure (l :: r)) _ _
      refine OComp.CA.bind' (cost_pairUpCommitterNodes W w (2 ^ d) l (by rw [hl, pow_succ, Nat.mul_comm]))
        (m' := 2 ^ d * w OracleName.node) (fun u hu => ?_) ?_
      · exact OComp.CA.map (cost_committerTreeLevels d u hu) _ fun _ _ => trivial
      · rw [pow_succ, Nat.mul_comm (2 ^ d) 2, Nat.mul_assoc, Nat.two_mul]

/-- The committer, at any weights of the oracles. -/
theorem cost_committerOverTypedOracles (ri : Enum L.EncodingRandomness) (sl : Enum (ℕ → Bits)) (b₀ : Bd) (i : I) :
    (committerOverTypedOracles W S ri sl b₀ i).CostBoundAt (fun o _ => w o)
      (2 ^ W.depth * w OracleName.leaf + 2 ^ W.depth * w OracleName.node + 2 * w (OracleName.fb S.t)) := by
  intro a c
  have hT : OComp.CA (fun o _ => w o) (committerTreeRoot W b₀ (L.encodeIndex i (ri.e a)) (sl.e c))
      (2 ^ W.depth * w OracleName.leaf + 2 ^ W.depth * w OracleName.node) fun _ => True := by
    unfold committerTreeRoot
    have h0 := cost_committerLeafHashes W w
      ((List.range (2 ^ W.depth)).map (committerLeafInput W b₀ (L.encodeIndex i (ri.e a)) (sl.e c)))
    rw [List.length_map, List.length_range] at h0
    refine OComp.CA.bind' h0 (m' := 2 ^ W.depth * w OracleName.node) (fun l hl => ?_) (Nat.le_refl _)
    exact OComp.CA.map (cost_committerTreeLevels W w W.depth l hl) _ fun _ _ => trivial
  refine OComp.CA.cost (P := fun _ => True) (OComp.CA.bind' hT (m' := 2 * w (OracleName.fb S.t))
    (fun root _ => ?_) (Nat.le_refl _))
  refine ⟨w (OracleName.fb S.t), ?_, fun a0 => ⟨0, Nat.le_refl _, fun a1 => trivial⟩⟩
  show w (OracleName.fb S.t) + w (OracleName.fb S.t) ≤ 2 * w (OracleName.fb S.t)
  omega

end Count

/-- **Over one hash function, under the coding m, it asks at most `committerQueryCount W S m` queries**: each
typed query weighed by the number of blocks of its answer. -/
theorem queryBound_committerOverTypedOracles_one (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    (ri : Enum L.EncodingRandomness) (sl : Enum (ℕ → Bits)) (b₀ : Bd) (i : I) :
    ((committerOverTypedOracles W S ri sl b₀ i).overOne m).QueryBound (committerQueryCount W S m) := by
  have h := cost_committerOverTypedOracles W S m.blocks ri sl b₀ i
  have e : Need.num (m := m) (fun _ _ _ => true) = fun o _ => m.blocks o :=
    funext fun _ => funext fun _ => cnt_all _
  rw [← overOneN_all]
  exact queryBound_overOneN m _ _ _ (e ▸ h)

/-- **The count over one hash function does not hang on the coding**: where lam is not 0, under
every coding a leaf and a node are one block and an answer of the seed's oracle is K + 1 blocks, by
counting. -/
theorem committerQueryCount_eq (hlam : 0 < lam) (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) :
    committerQueryCount W S m = 2 * 2 ^ W.depth + 2 * (W.K + 1) := by
  have hf : m.blocks (OracleName.fb S.t) = W.K + 1 :=
    Rom.blocks_eq_of_equiv hlam ((m.rng (OracleName.fb S.t)).symm.trans
      ((Equiv.prodComm (Fin W.K → Dig lam) (Dig lam)).trans (Fin.consEquiv fun _ => Dig lam)))
  unfold committerQueryCount
  rw [blocks_leaf hlam m, blocks_node hlam m, hf]
  omega

/-- **WITH THE COMMITTER `committerOverTypedOracles`: whoever opens a key, by running that committer again, opens it
to what the library's extractor gives at that key and its maker's log, but for
2 (tC + (tO + committerQueryCount) + 1)² / 2^lam.** At any scheme A with that committer: of its prover and its
verifier nothing is asked, and neither is run. hdec can hold only at a type of indices all of whose
members the decoder gives. -/
theorem opens_committerOverTypedOracles (hlam : 0 < lam) (hW : W.OKG)
    (hdec : ∀ i r s, L.decodeIndex (L.encodeIndex i r) (L.recOf i r s) = some i)
    (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (ri : Enum L.EncodingRandomness) (sl : Enum (ℕ → Bits))
    (b₀ : Bd)
    (A : Gen.Arg (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) I X Unit (KeyRoot lam L)
      (I × L.EncodingRandomness × (ℕ → Bits)) (OfflineLinkOnlineProof lam L aT aL))
    (hC : A.C = committerOverTypedOracles W S ri sl b₀) :
    HasIndexBindingWith (openingRelation I) (SpecialAny.oneOf (schemeOverOneHashFunction m A)).withOpenings
      (Special.extOf (extractorOverOneHashFunction m (indexExtractorAtRootAndOutOfDomainSample W))).withOpenings
      fun tC tO => 2 * ((tC + (tO + committerQueryCount W S m) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  refine Rom.binding_withOpenings_rom _ _ _
    (binding_of_badW (W := W) hlam (fun _ : Unit => m) (fun _ => False) (fun _ _ h => h.elim)
      (OComp.pure ()) trivial trivial trivial (schemeOverOneHashFunction m A) (extractorOverOneHashFunction m (indexExtractorAtRootAndOutOfDomainSample W))
      (fun k => k.cm) (committerQueryCount W S m) (fun i => ?_) ?_)
  · show ((A.C i).overOne m).QueryBound _
    rw [hC]
    exact queryBound_committerOverTypedOracles_one W S m ri sl b₀ i
  · intro g key i n trC trP trV _ hrun hM he
    have hrun : RunsIn trV ((((A.C i).overOne m).withCoins n).bind fun keys =>
        OComp.pure keys.1) key := hrun
    rw [hC] at hrun
    obtain ⟨o, ho, h2⟩ := (runsIn_bind_iff _ _ _).1 hrun
    obtain rfl := runsIn_pure_iff.1 h2
    exact good_committerOverTypedOracles W S hlam hW hdec m ri sl b₀ i n ho hM he

end TypedOracleCompiler.Compile.Batch.Cms

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms

/-- Whoever opens a key of the input's scheme, by running its committer again, opens it to what the
library's extractor gives at that key and its maker's log, but for β. -/
def openingByCommitterMatchesExtractor (r : InnerCompilerInput) (β : ℕ → ℕ → ℝ≥0∞) : Prop :=
  HasIndexBindingWith (openingRelation r.Index)
    (SpecialAny.oneOf (schemeOverOneHashFunction r.oracleCoding (schemeOverTypedOracles r))).withOpenings
    (Special.extOf (extractorOverOneHashFunction r.oracleCoding (indexExtractorAtRootAndOutOfDomainSample r.queryLayout))).withOpenings β

end VerifiableInference.OnPublicFiles

#print axioms TypedOracleCompiler.Compile.Batch.Cms.cost_committerLeafHashes
#print axioms TypedOracleCompiler.Compile.Batch.Cms.cost_pairUpCommitterNodes
#print axioms TypedOracleCompiler.Compile.Batch.Cms.cost_committerTreeLevels
#print axioms TypedOracleCompiler.Compile.Batch.Cms.cost_committerOverTypedOracles
#print axioms TypedOracleCompiler.Compile.Batch.Cms.queryBound_committerOverTypedOracles_one
#print axioms TypedOracleCompiler.Compile.Batch.Cms.committerQueryCount_eq
#print axioms TypedOracleCompiler.Compile.Batch.Cms.opens_committerOverTypedOracles
