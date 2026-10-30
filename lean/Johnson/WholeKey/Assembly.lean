-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/WholeKey/Assembly.lean: THE STATEMENT OF INDEX PRIVACY for the scheme with the whole key
published (Spec.wholeKeyPrivacy, Johnson/WholeKey/Statement.lean) FOLLOWS FROM THREE STATEMENTS,
each typed here or in its own file, none of them proved here.

A general theorem with its proof, from hypotheses that are named propositions. This file states no
goal of the release. IT DOES NOT PROVE Spec.wholeKeyPrivacy: it shows that the parts fit. (The three
hypotheses are theorems of their own files; Johnson/WholeKey/Main.lean puts them in.)

THE CHAIN, at one index i of the range, for an adversary whose first move is the setup.
    the real experiment of argW at i
      → [Spec.realToLate: HYPOTHESIS]   a plain challenger that runs the scheme's own programs at i
          and lays its secret-holding hash queries late (lateW, Johnson/LateWorld/Defs.lean).
          Price: ζ's term HASH.
      → [Spec.lateToWrap: HYPOTHESIS; its premises by Spec.premLate: HYPOTHESIS]   the reduction
          (wrapW, Johnson/WholeKey/Wrap.lean) around the REAL game of the interactive protocols at
          i. Price: ζ's terms TAIL and SEEDS.
      → [gameAtW: PROVED, Johnson/WrapLaws/AtKit.lean; the reduction's calls are allowed: admW,
          PROVED, Johnson/WrapLaws/Adm.lean]   the reduction around the SIMULATED game at i₀.
          Price: ζ's terms PARTS and STOPS.
      = the ideal experiment of simWholeKey   [frameAt: PROVED, Compile/PrivFrame/Top.lean; the
          reduction never answers a query in two ways: consW, PROVED, Johnson/WrapLaws/Cons.lean].
The prices add up to zetaW to the letter.

  Spec.realToLate   under PremW: real experiment and lateW are within
                    Rom.costTotal (eW …) (mW …) (bitsW …) (osW …) t.
  Spec.premLate     PremW gives the premises of Spec.lateToWrap.
  wholeKeyPrivacy_of_parts   Spec.realToLate → Spec.lateToWrap → Spec.premLate →
  Spec.wholeKeyPrivacy.

Terms: lean/GLOSSARY.md.

-/
import Johnson.WholeKey.Statement
import Johnson.LateWorld.SpecWrap
import Johnson.WrapLaws.Adm
import Johnson.WrapLaws.Cons
import Johnson.WrapLaws.AtKit
import Compile.PrivFrame.Top

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.WholeKey
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover
open _root_.Compile.GlueB (GCall GIn GAdm realW)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- **From the real experiment to the plain challenger that lays late**, under the premises of the
statement of index privacy, at ζ's hash term. A theorem's type; not proved here. -/
def Spec.realToLate : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
    (aL : RoundSplits L.link.shape) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (p : Params) (a : AtRecs lam L Bd aT aL)
    (Sm : Sims L) (ok : I → Prop) (Gs : L.OutOfDomainSeed → Prop) (Ryes : I → X → Prop) (c : CoinNums Bd)
    (u : NumsW),
    PremW W S cA p a Sm ok Gs Ryes c u →
    ∀ (i : I) (α : Type) (okb : ZKCP.Gen.Batch X Unit → Prop)
      (k : GIn (FullKey lam L aT aL) (RequestProof lam L) →
        Adv (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (GCall X Unit)
          (GIn (FullKey lam L aT aL) (RequestProof lam L)) α) (t n : ℕ),
      (Adv.call .setup k).TotalBound t (n + 1) → GAdm okb (.call .setup k) false n →
      tv ((interact (realW (argW W S cA r₀ p a.side) i) (.call .setup k)
            (none, Table.empty _)).map Prod.fst)
          ((interact (LateWorld.lateW W S cA r₀ a.side i) (.call .setup k)
            (none, Table.empty _)).map Prod.fst) ≤
        Rom.costTotal (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (eW W S a n) (mW W a n)
          (bitsW (lam := lam) p c) (osW W a) t

/-- The premises of the statement of index privacy give those of the step from the plain challenger
to the reduction. A theorem's type; not proved here. -/
def Spec.premLate : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
    (aL : RoundSplits L.link.shape) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (cA : L.OutOfDomainAnswer → List (Dig lam)) (p : Params) (a : AtRecs lam L Bd aT aL) (Sm : Sims L)
    (ok : I → Prop) (Gs : L.OutOfDomainSeed → Prop) (Ryes : I → X → Prop) (c : CoinNums Bd) (u : NumsW),
    PremW W S cA p a Sm ok Gs Ryes c u → LateWorld.PremLate W S cA a ok Gs u.δ

/-- **THE PARTS FIT**: the statement of index privacy from the three statements. -/
theorem wholeKeyPrivacy_of_parts (h1 : Spec.realToLate) (h2 : LateWorld.Spec.lateToWrap)
    (h3 : Spec.premLate) : Spec.wholeKeyPrivacy := by
  intro I X lam L Bd aT aL W S cA r₀ p a Sm ok Gs Ryes c u R i₀ hR hP i hi Z hZ
  letI : Inhabited (FullKey lam L aT aL) := ⟨⟨default, r₀, none, []⟩⟩
  letI : Inhabited (RequestProof lam L) := ⟨⟨0, 0, none⟩⟩
  have len1 : ∀ b : ZKCP.Gen.Batch X Unit, ZKCP.Gen.ValidBatch R 1 i b.pairs → b.length ≤ 1 := by
    intro b hb
    have := hb.1
    simpa [ZKCP.Gen.Batch.pairs] using this
  have key := PrivFrame.frameAt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) I X Unit Unit
    (FullKey lam L aT aL) (Isk lam L Bd aT aL) (RequestProof lam L) _ _ R (argW W S cA r₀ p a.side) 1
    (wrapW W S cA r₀ a.side) (Table.empty _, none) i
    (Hiop.Seeded.gameReal L (kitW W r₀ a.side) (WrapLaws.recsG a) i (boundsW a.side u.s1) Gs _)
    (none, Table.empty _)
    (Hiop.Seeded.gameSim L (kitW W r₀ a.side) (simsG a.side Sm) i₀ (boundsW a.side u.s1) Gs _)
    (none, Table.empty _)
    (fun _ E _ n => E.CallsOK (Hiop.Seeded.okCall (Ryes i)) ∧ Hiop.Seeded.SessLe E n)
    (fun t n => Rom.costTotal (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (eW W S a n) (mW W a n)
        (bitsW (lam := lam) p c) (osW W a) t +
      (Prob.pOver (a.M + 1) u.s1 n + ((a.M + 2 : ℕ) : ℝ≥0∞) * u.δ))
    (fun _ n => (u.zT + ((a.M + 1 : ℕ) : ℝ≥0∞) * u.zL + (n : ℝ≥0∞) * u.zO) +
      (u.hT + ((a.M + 1 : ℕ) : ℝ≥0∞) * u.hL + (n : ℝ≥0∞) * u.hO))
    (fun α k t n hT hA =>
      le_trans (tv_triangle _
        ((interact (LateWorld.lateW W S cA r₀ a.side i) (.call .setup k)
          (none, Table.empty _)).map Prod.fst) _)
        (add_le_add
          (h1 I X lam L Bd aT aL W S cA r₀ p a Sm ok Gs Ryes c u hP i α _ k t n hT hA)
          (h2 I X lam L Bd aT aL W S cA r₀ a ok Gs u.δ u.s1 i
            (h3 I X lam L Bd aT aL W S cA p a Sm ok Gs Ryes c u hP) hi α _ k n len1 hA)))
    (fun α k _ n _ hA =>
      WrapLaws.admW I X Unit Unit lam L Bd aT aL W S cA r₀ a.side R Ryes 1 hR i α _ false n _ hA)
    (fun α E _ n hE =>
      WrapLaws.gameAtW I X lam L Bd aT aL W S cA r₀ p a Sm ok Gs Ryes c u hP i hi i₀ n α E hE.1
        hE.2)
    (WrapLaws.consW I X lam L Bd aT aL W S cA r₀ a.side _) Z hZ
  have e : (fun t n => Rom.costTotal (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (eW W S a n)
        (mW W a n) (bitsW (lam := lam) p c) (osW W a) t +
        (Prob.pOver (a.M + 1) u.s1 n + ((a.M + 2 : ℕ) : ℝ≥0∞) * u.δ) +
      ((u.zT + ((a.M + 1 : ℕ) : ℝ≥0∞) * u.zL + (n : ℝ≥0∞) * u.zO) +
        (u.hT + ((a.M + 1 : ℕ) : ℝ≥0∞) * u.hL + (n : ℝ≥0∞) * u.hO))) = zetaW W S p a c u := by
    funext t n
    unfold zetaW
    ring
  rw [e] at key
  exact key

end OnBytes.WholeKey

#print axioms OnBytes.WholeKey.wholeKeyPrivacy_of_parts
