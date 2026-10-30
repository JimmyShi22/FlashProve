-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LateSide/Whole.lean: FROM THE REAL EXPERIMENT OF THE SCHEME WITH THE WHOLE KEY PUBLISHED TO
THE PLAIN CHALLENGER THAT LAYS LATE, UNDER THE PREMISES OF THE STATEMENT OF INDEX PRIVACY, at the
hash term of its written error: the proof of Spec.realToLate (Johnson/WholeKey/Assembly.lean).
Theorems with their proofs.

Lemmas of one step of a proof. This file states no goal of the release.

  back_of_nonces, cls_eq_nonceOf, shW_eq_wiresOf, ghostOK_prem   the premises on nonces, in the
               words of Johnson/GhostSide/.
  fitAll_prem  all premises on the letters (FitAll, Johnson/LateSide/Good.lean) at the written
               letters of the token side (tokAt, Johnson/TokenSide2/AtPrem.lean). Of the premises of
               the statement it spends coins, wires, plain, backT, backL, backB, and no other.
  hop_prem, late_prem   the two halves at the letters of the statement.
  realToLate_of   THE THEOREM, from Spec.sessLate. It calls: the real experiment is mode R of the
               token challenger (real_twinW, Johnson/HopSide/Proof.lean, at sameStep_prem); the hop
               (real_to_modeI, Compile/DeferRun/Hop.lean) at the counts of the written error
               (withinZetaT, Johnson/TokenRules/Closed.lean); mode I is the plain challenger that
               lays late (lateTwin, Johnson/LateSide/Assembly.lean, at lateStep_of, setupLate,
               lateDraws).
  realToLate   the same with Spec.sessLate laid in (sessLate, Johnson/LateSide2/Sess.lean).

Limits. The bound is a formula in the counts (Rom.costTotal, Rom/SpecHopCost.lean); no number is
evaluated here, so whether it is small at given letters is not said. n counts all batches of the
adversary, those of which nothing is shown and empty ones too. At a batch of two or more requests
both sides give fixed proofs (the scheme's own text: one request a proof).
Sources. The statement is Spec.realToLate (Johnson/WholeKey/Assembly.lean). The library files whose
forms its two halves follow are named in the heads of Johnson/HopSide/Spec.lean and
Johnson/LateSide/Spec.lean.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LateSide.Setup
import Johnson.LateSide.Assembly
import Johnson.LateSide2.Sess
import Johnson.LateSide2.ExtIn
import Johnson.TokenSide2.Closed
import Johnson.TokenSide2.LateDraws
import Johnson.TokenRules.Closed
import Johnson.WholeKey.Assembly

set_option autoImplicit false

noncomputable section

namespace OnBytes.LateSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey OnBytes.TokenSide OnBytes.GhostSide OnBytes.TokenRules
open OnBytes.HopSide OnBytes.LateWorld
open _root_.Compile.GlueB (GCall GIn GAdm realW)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout Marks

/-! ## The premises on nonces, in the words of Johnson/GhostSide/ -/

section Words
variable {lam : ℕ}

theorem back_of_nonces {K : ℕ} : ∀ {s : Shape} {A : RoundSplits s} {Ws : RoundsQueryLayout lam K s A} {cap : ℕ → ℕ}
    {i : ℕ}, NoncesBack s A Ws cap i → Back s A Ws cap i
  | [], _, _, _, _, _ => trivial
  | _ :: _, (a, _), (w, _), cap, i, h => by
    refine ⟨?_, back_of_nonces h.2⟩
    have h1 := h.1
    revert h1
    cases a.kind <;> exact id

theorem cls_eq_nonceOf {K : ℕ} : ∀ (s : Shape) (A : RoundSplits s) (Ws : RoundsQueryLayout lam K s A) (z : PlainPart s A),
    clsPB s A Ws z = nonceOf s A Ws z
  | [], _, _, z => nomatch z
  | _ :: _, (_, _), (_, _), .inl (.inl _) => rfl
  | _ :: _, (_, _), (_, _), .inl (.inr _) => rfl
  | _ :: s, (_, A), (_, Ws), .inr z => cls_eq_nonceOf s A Ws z

theorem shW_eq_wiresOf {I X : Type} {L : BatchProtocolWithLeafBody I X} (W : QueryLayout lam L) (t : Tag) :
    shW W t = wiresOf W t := by
  cases t <;> rfl

end Words

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}
variable {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL}
  {cA : L.OutOfDomainAnswer → List (Dig lam)} {p : Params} {a : AtRecs lam L Bd aT aL} {Sm : Sims L}
  {ok : I → Prop} {Gs : L.OutOfDomainSeed → Prop} {Ryes : I → X → Prop} {c : CoinNums Bd} {u : NumsW}

theorem ghostOK_prem (hP : PremW W S cA p a Sm ok Gs Ryes c u) :
    GhostOK W S a.side.capT a.side.capL a.side.capB where
  seed0 := by rw [cls_eq_nonceOf, shW_eq_wiresOf]; exact hP.plain.1
  seed1 := by rw [cls_eq_nonceOf, shW_eq_wiresOf]; exact hP.plain.2
  backT := back_of_nonces hP.backT
  backL := back_of_nonces hP.backL
  backB := back_of_nonces hP.backB

theorem fitAll_prem (hP : PremW W S cA p a Sm ok Gs Ryes c u) :
    FitAll W S a.side (tokAt W p a c) c.ℓ (min p.sFS lam) :=
  ⟨tokFit_tokAt hP.coins hP.wires, ghostOK_prem hP, lensOK_tokAt W p a c, extIn_of_oka hP.wires⟩

variable (r₀ : L.Rec) (i : I) {α : Type} (okb : ZKCP.Gen.Batch X Unit → Prop)
  (A : Adv (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (GCall X Unit)
    (GIn (FullKey lam L aT aL) (RequestProof lam L)) α) (t n : ℕ)

/-- The hop, at the letters of the statement: the real experiment against mode I of the token
challenger, at the counts of the written error. -/
theorem hop_prem (hP : PremW W S cA p a Sm ok Gs Ryes c u) (hT : A.TotalBound t (n + 1))
    (hA : GAdm okb A false n) :
    tv ((interact (realW (argW W S cA r₀ p a.side) i) A (none, Table.empty _)).map Prod.fst)
        ((interact (((challT W S cA r₀ a.side (tokAt W p a c) i).world true).pre (ghost W)) A
          (none, DSt.init _)).map Prod.fst) ≤
      Rom.costTotal (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (eW W S a n) (mW W a n)
        (bitsW (lam := lam) p c) (osW W a) t := by
  have hG := ghostOK_prem hP
  have hR := (routedTwin I X lam L Bd aT aL W S cA r₀ a.side (tokAt W p a c) hG).2.2 i
  have h1 := real_twinW p (sameStep_prem r₀ hP) hR okb A n hA
  have h2 := withinZetaT I X lam L Bd aT aL W S cA r₀ p a c (tokAt W p a c) i true α okb
    (A.via (ghost W)) n (lensOK_tokAt W p a c) rfl rfl rfl
    (DeferRun.gAdm_via okb (ghost W) A false n hA)
  exact DeferRun.real_to_modeI (challT W S cA r₀ a.side (tokAt W p a c) i) none
    (ghostPerm _ _ _ _ W) _ _ _ _ (realW (argW W S cA r₀ p a.side) i) (none, Table.empty _) A t
    (n + 1) hT h1 h2

/-- Mode I of the token challenger is the plain challenger that lays late, at the letters of the
statement. -/
theorem late_prem (hSess : Spec.sessLate) (hP : PremW W S cA p a Sm ok Gs Ryes c u)
    (hA : GAdm okb A false n) :
    (interact (((challT W S cA r₀ a.side (tokAt W p a c) i).world true).pre (ghost W)) A
        (none, DSt.init _)).map Prod.fst =
      (interact (lateW W S cA r₀ a.side i) A (none, Table.empty _)).map Prod.fst :=
  lateTwin I X lam L Bd aT aL W S cA r₀ a.side (tokAt W p a c) i _ α okb A n
    (lateStep_of setupLate hSess lateDraws cA r₀ a.side (tokAt W p a c) c.ℓ (min p.sFS lam) i
      (fitAll_prem hP)) hA

omit r₀ i okb A t n in
/-- **From the real experiment to the plain challenger that lays late**, from the statement on a
session. -/
theorem realToLate_of (hSess : Spec.sessLate) : WholeKey.Spec.realToLate := by
  intro I X lam L Bd aT aL W S cA r₀ p a Sm ok Gs Ryes c u hP i α okb k t n hT hA
  rw [← late_prem r₀ i okb (.call .setup k) n hSess hP hA]
  exact hop_prem r₀ i okb (.call .setup k) t n hP hT hA

/-- **From the real experiment to the plain challenger that lays late**, under the premises of the
statement of index privacy, at the hash term of its written error. -/
theorem realToLate : WholeKey.Spec.realToLate := realToLate_of sessLate

end OnBytes.LateSide

#print axioms OnBytes.LateSide.hop_prem
#print axioms OnBytes.LateSide.late_prem
#print axioms OnBytes.LateSide.realToLate
