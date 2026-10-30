-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/StringsAllLinks.lean: all M + 1 link proofs in the key are produced, except with a probability
that a union bound gives.

Summary. E2E/StringsShown.lean covers one link proof, the one at the place that the prover samples.
This file covers all M + 1 link proofs in the key, by a union bound over the places (a place is the
number of a copy in the key's list): first for arbitrary parameters and any three provers that never
abort, then for the placeholder provers at the verifier's parameters. The main limit: it says that
the proofs are produced, not that the verifier accepts them.

Main results.
  `full_law`: for any three provers that never abort, under `LawFit` and `WiresFit`: run the
    committer and then the prover of one request, with their coins. `FullTo (M + 1)` holds, except
    with probability at most (M + 2) · `alphaAll W capT capL capB 0 0 0 0 0`.
  `fullAt_description` (`FullAt r`): at the verifier's parameters at Z, for each fixed c and m, for
    public files Z in scope: for the placeholder provers (`silentAtC`) with at least 2 ^ 40 tries in
    every search, `FullTo (M + 1)` holds, except with probability at most (M + 2) · 71 · 2 ^ -256.

How. The committer does not read the prover's coins. So "the link proof at place j is produced"
follows, pointwise in the oracle functions, outside the bad event of the prover of a whole request,
taken for the committer's coins together with prover's coins whose place is j. `allY_law` bounds
that event's probability. The events of the places are added up.

Terms: E2E/HidingTerms.lean.

Limits.
- All limits of E2E/StringsShown.lean and E2E/StringsAtInput.lean hold, except "one link proof":
  nothing on acceptance · one commitment and one request, fixed before the oracles are sampled.
- What a produced proof opens of the committed tables is not stated here: see E2E/StringsHold.lean
  for any provers, and E2E/StringsHoldAtInput.lean, E2E/StringsHoldLink.lean and
  E2E/StringsHoldClosed.lean at these parameters. On a proof's plain messages, and on the openings
  of the prover's own oracle messages, these files say nothing.
- The factor is crude: each place is charged the failures of all three protocols, where the link's
  alone would do.

Definitions and helper lemmas.
  `leaf_proveAt`: the place that a proof names is the place that the prover's coins hold.
  `LinkAt j k`: the key's link proof at place j is produced.
  `link_of_not_ev`: pointwise. `link_fixed`: for fixed coins, at one place. `links_fixed`: for fixed
    coins, at the first n places: at most n times the bound.
  `FullTo n y`: `Strings y`, and the link proofs at the first n places are produced.
  `full_fixed`: `full_law` for fixed coins. `fullAt_of`: `FullAt r` for arbitrary r, from `Tries r`,
    `LawFit` and `WiresFit`.


-/
import E2E.StringsAtInput

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.Shown
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

section Letters
variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

/-- The key's link proof at place j is produced. -/
def LinkAt (j : ℕ) (k : FullKey lam L aT aL) : Prop :=
  ∃ l, k.links[j]? = some l ∧ l.2.2.isSome = true

/-- `Strings`, and the link proofs at the first n places are produced. -/
def FullTo (n : ℕ) (y : FullKey lam L aT aL × RequestProof lam L) : Prop :=
  Strings y ∧ ∀ j, j < n → LinkAt j y.1

variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (h : HonestSide lam L Bd aT aL)

/-- The place that a proof names is the place that the prover's coins hold. -/
theorem leaf_proveAt (g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) (isk : Isk lam L Bd aT aL)
    (x : X) (d : DrawP lam L Bd aT aL h.KB) :
    ((proveAt W cA r₀ h isk x d).det g).leaf = d.j := by
  unfold proveAt
  split
  · rfl
  · simp only [OComp.det_bind]
    rfl

/-- **Pointwise, at one place.** -/
theorem link_of_not_ev (g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) (hW : WiresFit W cA)
    (hs : NeverStops h.st) (i : I) (x : X) (c : DrawC lam L Bd aT aL h.KT h.KL)
    (e : DrawCopy lam L Bd aT aL h.KL) (d : DrawP lam L Bd aT aL h.KB)
    (hj : c.copies[d.j]? = some e)
    (hn : (allY W S cA r₀ h.b₀ h.st.joint h.capT h.capL h.capB (i, c.r, cutS (2 ^ W.depth) c.s) x
      (drawOf W h c e d)).det g ∉ EvY (noBads L)) :
    LinkAt d.j ((commitAt W S cA h i c).det g).1 := by
  obtain ⟨l, hl, hl'⟩ := (strings_of_not_ev W S cA r₀ h g hW hs i x c e d hj hn).2.1
  have hl₂ : ((commitAt W S cA h i c).det g).1.links[((proveAt W cA r₀ h
      ((commitAt W S cA h i c).det g).2 x d).det g).leaf]? = some l := hl
  rw [leaf_proveAt] at hl₂
  exact ⟨l, hl₂, hl'⟩

variable (hL : LawFit W S h.capT h.capL h.capB) (hW : WiresFit W cA) (hs : NeverStops h.st)
  (i : I) (x : X) (c : DrawC lam L Bd aT aL h.KT h.KL) (dP : DrawP lam L Bd aT aL h.KB)
include hL hW hs

/-- **For fixed coins, at one place.** -/
theorem link_fixed (j : ℕ) (hj : j < c.copies.length) :
    PrFrom (Table.empty _) ((commitAt W S cA h i c).bind fun key =>
      (proveAt W cA r₀ h key.2 x dP).bind fun π => .pure (key.1, π))
      {y | ¬ LinkAt j y.1} ≤ alphaAll W h.capT h.capL h.capB 0 0 0 0 0 := by
  have he : c.copies[j]? = some c.copies[j] := List.getElem?_eq_getElem hj
  refine (PrFrom_le_of_det (E' := EvY (noBads L)) ?_
    (noCoin_allY W S cA r₀ h.b₀ h.st.joint h.capT h.capL h.capB (i, c.r, cutS (2 ^ W.depth) c.s) x
      (drawOf W h c c.copies[j] ⟨j, dP.κ, dP.co⟩)) _ fun g hg => ?_).trans
    (allY_law cA r₀ h.b₀ h.st.joint h.capT h.capL h.capB (freshAll_empty W S) hL
      (i, c.r, cutS (2 ^ W.depth) c.s) x (drawOf W h c c.copies[j] ⟨j, dP.κ, dP.co⟩) _
      (setsSmall_none W S))
  · exact (noCoin_commitAt W S cA h i c).bind fun key =>
      (noCoin_proveAt W cA r₀ h key.2 x dP).bind fun _ => trivial
  · by_contra hn
    have hy := link_of_not_ev W S cA r₀ h g hW hs i x c c.copies[j] ⟨j, dP.κ, dP.co⟩ he hn
    have hg' : ¬ LinkAt j (Prod.fst (OComp.det g _)) := hg
    simp only [OComp.det_bind] at hg'
    exact hg' hy

/-- **For fixed coins, at the first n places.** -/
theorem links_fixed : ∀ n : ℕ, n ≤ c.copies.length →
    PrFrom (Table.empty _) ((commitAt W S cA h i c).bind fun key =>
      (proveAt W cA r₀ h key.2 x dP).bind fun π => .pure (key.1, π))
      {y | ∃ j, j < n ∧ ¬ LinkAt j y.1} ≤ (n : ℝ≥0∞) * alphaAll W h.capT h.capL h.capB 0 0 0 0 0
  | 0, _ => by
    have e : {y : FullKey lam L aT aL × RequestProof lam L | ∃ j, j < 0 ∧ ¬ LinkAt j y.1} = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun _ a => a.elim fun _ b => absurd b.1 (Nat.not_lt_zero _)
    rw [e, PrFrom_eq_lazy, pr_empty]
    exact zero_le _
  | n + 1, hn => by
    refine (PrFrom_mono _ _ (F := {y | ∃ j, j < n ∧ ¬ LinkAt j y.1} ∪ {y | ¬ LinkAt n y.1})
      fun y a => ?_).trans ((PrFrom_union_le _ _ _ _).trans ?_)
    · obtain ⟨j, hj, hb⟩ := a
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hlt | rfl
      · exact Or.inl ⟨j, hlt, hb⟩
      · exact Or.inr hb
    · rw [Nat.cast_succ, add_mul, one_mul]
      exact add_le_add (links_fixed n (Nat.le_of_succ_le hn))
        (link_fixed W S cA r₀ h hL hW hs i x c dP n hn)

/-- **For fixed coins: all of it.** -/
theorem full_fixed (hj : dP.j < c.copies.length) :
    PrFrom (Table.empty _) ((commitAt W S cA h i c).bind fun key =>
      (proveAt W cA r₀ h key.2 x dP).bind fun π => .pure (key.1, π))
      {y | ¬ FullTo c.copies.length y} ≤
        ((c.copies.length + 1 : ℕ) : ℝ≥0∞) * alphaAll W h.capT h.capL h.capB 0 0 0 0 0 := by
  refine (PrFrom_mono _ _
    (F := {y | ∃ j, j < c.copies.length ∧ ¬ LinkAt j y.1} ∪ {y | ¬ Strings y})
    fun y a => ?_).trans ((PrFrom_union_le _ _ _ _).trans ?_)
  · by_cases hS : Strings y
    · refine Or.inl ?_
      by_contra hb
      exact a ⟨hS, fun j hj' => by
        by_contra hl
        exact hb ⟨j, hj', hl⟩⟩
    · exact Or.inr hS
  · rw [Nat.cast_succ, add_mul, one_mul]
    exact add_le_add (links_fixed W S cA r₀ h hL hW hs i x c dP _ (Nat.le_refl _))
      (strings_fixed W S cA r₀ h hL hW hs i x c dP hj)

omit c dP in
/-- **The bound, for all M + 1 link proofs.** -/
theorem full_law :
    PrFrom (Table.empty _) ((commitW W S cA h i).bind fun key =>
      (coinsP W h).bind fun d => (proveAt W cA r₀ h key.2 x d).bind fun π => .pure (key.1, π))
      {y | ¬ FullTo (h.M + 1) y} ≤
        ((h.M + 2 : ℕ) : ℝ≥0∞) * alphaAll W h.capT h.capL h.capB 0 0 0 0 0 := by
  show PrFrom _ (((coinsC W h).bind fun d => commitAt W S cA h i d).bind fun key =>
    (coinsP W h).bind fun d => (proveAt W cA r₀ h key.2 x d).bind fun π => .pure (key.1, π)) _ ≤ _
  simp only [OComp.bind_assoc]
  refine PrFrom_coins_le _ _ _ (fun c hc => ?_) _ (onlyCoins_coinsC W h)
  refine PrFrom_bind_coins_le _ (commitAt W S cA h i c) _ _ (fun dP hdP => ?_) _
    (onlyCoins_coinsP W h)
  have e := full_fixed W S cA r₀ h hL hW hs i x c dP (by rw [hc.2.2.1]; exact hdP.1)
  rw [hc.2.2.1] at e
  exact e

end Letters

open VerifiableInference.OnPublicFiles (InnerCompilerInput)
open AtPublicFiles.Premises (silentAtC)
open AtPublicFiles.ZetaAt (Tries alpha_of_tries tries_built)
open VerifierAndGoals (PublicFiles InScope)
open FlashProve (flashProveData)

/-- With at least 2 ^ 40 tries in every search, `FullTo (M + 1)` fails with probability at most
(M + 2) · 71 · 2 ^ -256. -/
def FullAt (r : InnerCompilerInput) : Prop :=
  ∀ (capT capL capB : ℕ → ℕ), (∀ i, 2 ^ 40 ≤ capT i + 1) → (∀ i, 2 ^ 40 ≤ capL i + 1) →
    (∀ i, 2 ^ 40 ≤ capB i + 1) → ∀ (b : r.LeafBody) (M ℓ ℓr : ℕ) (i : r.Index) (x : r.Instance),
      PrFrom (Table.empty _) (runOf r (silentAtC r b M ℓ ℓr capT capL capB).side i x)
        {y | ¬ FullTo (M + 1) y} ≤ ((M + 2 : ℕ) : ℝ≥0∞) * (71 * (2⁻¹ : ℝ≥0∞) ^ 256)

theorem fullAt_of (r : InnerCompilerInput) (ht : Tries r)
    (hL : ∀ capT capL capB, LawFit r.queryLayout r.seedQueries capT capL capB) (hW : WiresFit r.queryLayout r.answerCode) : FullAt r :=
  fun capT capL capB h1 h2 h3 b M ℓ ℓr i x =>
    (full_law r.queryLayout r.seedQueries r.answerCode r.fixedSample (silentAtC r b M ℓ ℓr capT capL capB).side (hL capT capL capB) hW
      (neverStops_silent r.protocol _) i x).trans
      (mul_le_mul' le_rfl (alpha_of_tries r ht capT capL capB h1 h2 h3))

/-- **At the verifier's parameters at Z**, for each fixed c and m, for public files Z in scope. -/
theorem fullAt_description (Z : PublicFiles) (scope : InScope Z = true) :
    ∀ (c : VerifiableInference.Digest) (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More),
      FullAt ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m) :=
  VerifierAndGoals.ofBuilt
    (Q := fun D => ∀ (c : VerifiableInference.Digest) (m : D.More), FullAt (D.input Z c m))
    fun c m => fullAt_of _ (tries_built Z scope c m) (fits_built Z c m).1 (fits_built Z c m).2

end AtPublicFiles.Shown

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.Shown.leaf_proveAt
#print axioms AtPublicFiles.Shown.link_of_not_ev
#print axioms AtPublicFiles.Shown.link_fixed
#print axioms AtPublicFiles.Shown.links_fixed
#print axioms AtPublicFiles.Shown.full_fixed
#print axioms AtPublicFiles.Shown.full_law
#print axioms AtPublicFiles.Shown.fullAt_of
#print axioms AtPublicFiles.Shown.fullAt_description
