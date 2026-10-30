-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/StringsShown.lean: for any three provers that never abort, the hashed scheme's proofs are
produced, except with the probability that a proof-of-work search runs out.

Summary. In the hashed scheme (`argW`, Johnson/WholeKey/Defs.lean) a prover searches for a nonce in
every round that has a proof-of-work test. Where a search runs out, no proof is produced. This file
bounds the probability of that, for arbitrary parameters and any three provers that never abort.
E2E/StringsInGameOne.lean and E2E/StringsInGame.lean use it to bound the probability that a view in
the experiment of index privacy lacks a proof. The main limit: it says that a proof is produced, not
that the verifier accepts it.

Main result.
  `strings_law`: for any three provers that never abort, under `LawFit` and `WiresFit`: run the
    committer and then the prover of one request, with their coins. The first table's proof, the
    link proof at the place that the proof names and the session's proof are produced (`Strings`),
    except with probability at most `alphaAll W capT capL capB 0 0 0 0 0`: the sum of the three
    protocols' `capFail` (Johnson/Prover/Law/Defs.lean).

How. As `fixed_law` and `complete_argW` in Johnson/WholeKey/Complete.lean, with the verifier taken
out. Fix all coins. Under fixed oracle functions the three proofs are what three runs of the prover
of a whole request return (`allY`, Johnson/Prover/All/Defs.lean). Outside that prover's bad event
for five empty sets, no search has run out and no run lacks a format; the provers never abort; so
each of the three proofs is produced. `allY_law` bounds the event's probability, starting from the
empty table of oracle answers. A bound for all values of the coins is a bound on average.

Terms: E2E/HidingTerms.lean.

Limits.
- No verifier runs here, and no premise on acceptance is asked for.
- One link proof: the one at the place that the prover samples, not all M + 1. For all of them see
  E2E/StringsAllLinks.lean.
- One commitment and one request, both fixed before the oracles are sampled, and nobody asks a query
  first. For the session's proof that covers a fixed instance only.
- `LawFit` and `WiresFit` (Johnson/Prover/All/Law.lean, Johnson/Prover/All/Yes.lean) are premises
  here.
- The bound is an expression in the parameters. What `capFail` is for given search limits and
  proof-of-work tests is not stated here: see E2E/ZetaTriesAtInput.lean.
- Structured oracles, keys and proofs: no hash function and no bytes.

Definitions and helper lemmas.
  `noBads`, `setsSmall_none`: the five empty sets; their measures are 0.
  `NeverStops st`: the three conditions for an abort are false for all arguments.
  `Strings y`: for a key and a proof: the first table's proof in the key, the link proof at the
    place that the proof names, and the session's proof are produced.
  `strings_of_not_ev`: pointwise in the oracle functions, outside the event. `strings_fixed`: for
    fixed coins.


-/
import Johnson.WholeKey.Complete

set_option autoImplicit false

noncomputable section

namespace AtPublicFiles.Shown
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

/-- The five empty sets. -/
def noBads (L : HolographicProtocol I X) : Bads L := ⟨∅, ∅, fun _ => ∅, fun _ _ => ∅, fun _ => ∅⟩

/-- Their measures are 0. -/
theorem setsSmall_none (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) :
    SetsSmall W S (noBads L) 0 0 0 0 0 :=
  ⟨le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h => h),
    le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h => h),
    fun _ => le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h => h),
    fun _ _ => le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h => h),
    fun _ => le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h => h)⟩

/-- The three conditions for an abort are false for all arguments. -/
structure NeverStops {KT KL KB : Type} (st : Plays L KT KL KB) : Prop where
  T : ∀ i r e ρ, st.stopT i r e ρ = false
  Lk : ∀ i a b ρ, st.stopL i a b ρ = false
  B : ∀ i r e x n ρ, st.stopB i r e x n ρ = false

/-- **The three proofs are produced**: the first table's proof in the key, the link proof at the
place that the proof names, the session's proof. -/
def Strings (y : FullKey lam L aT aL × RequestProof lam L) : Prop :=
  y.1.piT.isSome = true ∧ (∃ l, y.1.links[y.2.leaf]? = some l ∧ l.2.2.isSome = true) ∧
    y.2.piB.isSome = true

variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (h : HonestSide lam L Bd aT aL)

/-- **Pointwise: outside the event for the five empty sets the three proofs are produced.** -/
theorem strings_of_not_ev (g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) (hW : WiresFit W cA)
    (hs : NeverStops h.st) (i : I) (x : X) (c : DrawC lam L Bd aT aL h.KT h.KL)
    (e : DrawCopy lam L Bd aT aL h.KL) (dP : DrawP lam L Bd aT aL h.KB)
    (hj : c.copies[dP.j]? = some e)
    (hn : (allY W S cA r₀ h.b₀ h.st.joint h.capT h.capL h.capB (i, c.r, cutS (2 ^ W.depth) c.s) x
      (drawOf W h c e dP)).det g ∉ EvY (noBads L)) :
    Strings (((commitAt W S cA h i c).det g).1,
      (proveAt W cA r₀ h ((commitAt W S cA h i c).det g).2 x dP).det g) := by
  obtain ⟨π, e₁, e₂, τT, τL, τB, hx, -, -, -, -, -⟩ :=
    ok_of_not_ev W S cA r₀ h.b₀ h.st.joint h.capT h.capL h.capB g hW
      (i, c.r, cutS (2 ^ W.depth) c.s) x (drawOf W h c e dP) (noBads L) hn
  rw [det_allX, det_allY_parts W S cA r₀ h g i c.r c.s x _ e.s rfl] at hx
  obtain ⟨a, b, c', ha, hb, hc, -⟩ := three_eq_ok hx
  have ft : ((commitAt W S cA h i c).det g).2.copies[dP.j]? = some (tabG W S h g i e.r e.s) := by
    rw [det_commitAt]
    show (c.copies.map fun e => tabG W S h g i e.r e.s)[dP.j]? = _
    rw [List.getElem?_map, hj]
    rfl
  have fl : ((commitAt W S cA h i c).det g).1.links[dP.j]? =
      some ((linkO W cA h i (tabG W S h g i c.r c.s) (tabG W S h g i e.r e.s) e).det g) := by
    rw [det_commitAt]
    show (c.copies.map fun e =>
      (linkO W cA h i (tabG W S h g i c.r c.s) (tabG W S h g i e.r e.s) e).det g)[dP.j]? = _
    rw [List.getElem?_map, hj]
    rfl
  have pT : ((commitAt W S cA h i c).det g).1.piT = some a.1 := by
    rw [det_commitAt]
    exact (congrArg (shown (h.st.stopT i c.r (tabG W S h g i c.r c.s).seed)) ha).trans
      (shown_ok (hs.T _ _ _ _))
  have pL : (linkO W cA h i (tabG W S h g i c.r c.s) (tabG W S h g i e.r e.s) e).det g =
      ((tabG W S h g i e.r e.s).tree.root, L.recOf i e.r (tabG W S h g i e.r e.s).seed,
        some b.1) := by
    rw [det_linkO]
    exact congrArg (fun z => ((tabG W S h g i e.r e.s).tree.root,
      L.recOf i e.r (tabG W S h g i e.r e.s).seed, z))
      ((congrArg (shown (h.st.stopL i (c.r, (tabG W S h g i c.r c.s).seed)
        (e.r, (tabG W S h g i e.r e.s).seed))) hb).trans (shown_ok (hs.Lk _ _ _ _)))
  have pB : shown (h.st.stopB i e.r (tabG W S h g i e.r e.s).seed x (h.nm dP.j))
      ((proveBA W cA r₀ (fun _ => (tabG W S h g i e.r e.s).tree)
        (h.dressB (h.rvB dP.κ) dP.co) h.capB
        (tabG W S h g i e.r e.s).tree.root x (L.recOf i e.r (tabG W S h g i e.r e.s).seed)
        (L.encodeIndex i e.r) (h.st.B i e.r (tabG W S h g i e.r e.s).seed x (h.nm dP.j) dP.κ)).det g) =
      some c'.1 :=
    (congrArg (shown (h.st.stopB i e.r (tabG W S h g i e.r e.s).seed x (h.nm dP.j))) hc).trans
      (shown_ok (hs.B _ _ _ _ _ _))
  have hi : ((commitAt W S cA h i c).det g).2.i = i := by
    rw [det_commitAt]
  rw [det_proveAt W cA r₀ h g _ x dP _ ft, hi]
  refine ⟨?_, ⟨_, fl, ?_⟩, ?_⟩
  · show ((commitAt W S cA h i c).det g).1.piT.isSome = true
    rw [pT]
    rfl
  · rw [pL]
    rfl
  · exact (congrArg Option.isSome pB).trans rfl

/-- **For fixed coins.** -/
theorem strings_fixed (hL : LawFit W S h.capT h.capL h.capB) (hW : WiresFit W cA)
    (hs : NeverStops h.st) (i : I) (x : X) (c : DrawC lam L Bd aT aL h.KT h.KL)
    (dP : DrawP lam L Bd aT aL h.KB) (hj : dP.j < c.copies.length) :
    PrFrom (Table.empty _) ((commitAt W S cA h i c).bind fun key =>
      (proveAt W cA r₀ h key.2 x dP).bind fun π => .pure (key.1, π))
      {y | ¬ Strings y} ≤ alphaAll W h.capT h.capL h.capB 0 0 0 0 0 := by
  have he : c.copies[dP.j]? = some c.copies[dP.j] := List.getElem?_eq_getElem hj
  refine (PrFrom_le_of_det (E' := EvY (noBads L)) ?_
    (noCoin_allY W S cA r₀ h.b₀ h.st.joint h.capT h.capL h.capB (i, c.r, cutS (2 ^ W.depth) c.s) x
      (drawOf W h c c.copies[dP.j] dP)) _ fun g hg => ?_).trans
    (allY_law cA r₀ h.b₀ h.st.joint h.capT h.capL h.capB (freshAll_empty W S) hL
      (i, c.r, cutS (2 ^ W.depth) c.s) x (drawOf W h c c.copies[dP.j] dP) _ (setsSmall_none W S))
  · exact (noCoin_commitAt W S cA h i c).bind fun key =>
      (noCoin_proveAt W cA r₀ h key.2 x dP).bind fun _ => trivial
  · by_contra hn
    have hy := strings_of_not_ev W S cA r₀ h g hW hs i x c c.copies[dP.j] dP he hn
    have hg' : ¬ Strings (OComp.det g _) := hg
    simp only [OComp.det_bind] at hg'
    exact hg' hy

/-- **The bound: the committer, then the prover of one request, with their coins.** -/
theorem strings_law (hL : LawFit W S h.capT h.capL h.capB) (hW : WiresFit W cA)
    (hs : NeverStops h.st) (i : I) (x : X) :
    PrFrom (Table.empty _) ((commitW W S cA h i).bind fun key =>
      (coinsP W h).bind fun d => (proveAt W cA r₀ h key.2 x d).bind fun π => .pure (key.1, π))
      {y | ¬ Strings y} ≤ alphaAll W h.capT h.capL h.capB 0 0 0 0 0 := by
  show PrFrom _ (((coinsC W h).bind fun d => commitAt W S cA h i d).bind fun key =>
    (coinsP W h).bind fun d => (proveAt W cA r₀ h key.2 x d).bind fun π => .pure (key.1, π)) _ ≤ _
  simp only [OComp.bind_assoc]
  refine PrFrom_coins_le _ _ _ (fun c hc => ?_) _ (onlyCoins_coinsC W h)
  refine PrFrom_bind_coins_le _ (commitAt W S cA h i c) _ _ (fun dP hdP => ?_) _
    (onlyCoins_coinsP W h)
  exact strings_fixed W S cA r₀ h hL hW hs i x c dP (by rw [hc.2.2.1]; exact hdP.1)

end AtPublicFiles.Shown

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.Shown.setsSmall_none
#print axioms AtPublicFiles.Shown.strings_of_not_ev
#print axioms AtPublicFiles.Shown.strings_fixed
#print axioms AtPublicFiles.Shown.strings_law
