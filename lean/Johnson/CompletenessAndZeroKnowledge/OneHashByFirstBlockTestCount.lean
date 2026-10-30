-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/CompletenessAndZeroKnowledge/OneHashByFirstBlockTestCount.lean: THE HASH QUERIES OF THE COMMITTER AND THE PROVER OF argW AT THE THIRD
EXIT (overOneF): a failed try of a search costs one, a whole answer K + 1, a tree query one. chainF
(Johnson/Prover/Law/CountF.lean) is the chain's count; commitC and proveC are commitN and proveN
(Johnson/WholeKey/Work.lean) with it. The fine count at the first exit is Johnson/CompletenessAndZeroKnowledge/FineCount.lean.

budgetC is what a system asks that runs the committer, and then the committer again and the prover,
with a public reading of q₀ queries and one query for a commitment ID. copies_within_two_pow_48 is an
inequality between numbers only: at the numerals that it takes for the three chains and a table, 2 ^ 48
holds budgetC exactly up to 81 copies. That these numerals are those of any system is not said here.
Upper bounds on every path. Nothing here is a goal.
-/
import Johnson.Prover.All.CountF
import Johnson.CompletenessAndZeroKnowledge.FineCount

set_option autoImplicit false

noncomputable section

namespace OnBytes.WholeKey
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}
variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (h : HonestSide lam L Bd aT aL)

/-- One link run, at the third exit. -/
def linkC : ℕ := chainF L.link.shape aL (wLC W).sh h.capL 0 W.depthReqL + 0

/-- **The committer's hash queries at the third exit.** -/
def commitC : ℕ :=
  tabW W + ((h.M + 1) * tabW W +
    (chainF L.offline.shape aT (wTC W).sh h.capT 0 W.depthReqT + ((h.M + 1) * linkC W h + 0)))

/-- **The prover's hash queries at the third exit.** -/
def proveC : ℕ := chainF L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh h.capB 0 W.depthReq + 0

variable {W S cA r₀ h} {hK : 0 < W.K} {pass : Pass lam (typedOracleCarrier L Bd aT aL)}

theorem costC_tabO (H : PassFits W S hK pass) (b₀ : Bd) (i : I) (r : L.EncodingRandomness) (s : ℕ → Bits) :
    (tabO W S b₀ i r s).CostBoundR (costP hK pass) (tabW W) := by
  show (tabO W S b₀ i r s).CostBoundR (costP hK pass) (2 * 2 ^ W.depth + (2 * (W.K + 1) + 0))
  exact OComp.CostBoundR.bind (fun _ => OComp.CostBoundR.bind (t := 0) (by intro _; trivial)
    (costBound_seedsO H _)) (costBound_committerTreeKeptByProver b₀ hK pass _ _)

theorem costC_tabsO (H : PassFits W S hK pass) (i : I) :
    ∀ ds : List (DrawCopy lam L Bd aT aL h.KL),
      (tabsO W S h i ds).CostBoundR (costP hK pass) (ds.length * tabW W)
  | [] => trivial
  | d :: ds => by
    have e : (d :: ds).length * tabW W = tabW W + (ds.length * tabW W + 0) := by
      rw [List.length_cons, Nat.succ_mul]
      omega
    rw [e]
    exact OComp.CostBoundR.bind (fun _ =>
      OComp.CostBoundR.bind (by intro _; trivial) (costC_tabsO H i ds))
      (costC_tabO H h.b₀ i d.r _)

theorem costC_linkO (H : PassFits W S hK pass) (i : I) (t₁ t₂ : TabK lam L Bd aT aL)
    (d : DrawCopy lam L Bd aT aL h.KL) (hd : d.co.path.length = W.depthReqL) :
    (linkO W cA h i t₁ t₂ d).CostBoundR (costP hK pass) (linkC W h) := by
  have q := costBound_proveX hK pass Tag.link (batLC L aL) (wLC W) W.embL id (fun _ => none)
    (cmsLA cA t₁.tree.root t₂.tree.root (L.recOf i t₁.r t₁.seed).2 (L.recOf i t₂.r t₂.seed).2)
    (L.recOf i t₁.r t₁.seed, L.recOf i t₂.r t₂.seed) (L.encodeIndex i t₁.r, L.encodeIndex i t₂.r)
    (fun k => if k = 0 then t₁.tree else t₂.tree)
    (h.st.Lk i (t₁.r, t₁.seed) (t₂.r, t₂.seed) d.κ) (h.dressL (h.rvL d.κ) d.co) h.capL H.testsL
  have e : (h.dressL (h.rvL d.κ) d.co).path.length = W.depthReqL := hd
  rw [e] at q
  exact OComp.CostBoundR.bind (by intro _; trivial) q

theorem costC_linksO (H : PassFits W S hK pass) (i : I) (t₁ : TabK lam L Bd aT aL) :
    ∀ l : List (DrawCopy lam L Bd aT aL h.KL × TabK lam L Bd aT aL),
      (∀ a ∈ l, a.1.co.path.length = W.depthReqL) →
      (linksO W cA h i t₁ l).CostBoundR (costP hK pass) (l.length * linkC W h)
  | [], _ => trivial
  | a :: l, hl => by
    have e : (a :: l).length * linkC W h = linkC W h + (l.length * linkC W h + 0) := by
      rw [List.length_cons, Nat.succ_mul]
      omega
    rw [e]
    exact OComp.CostBoundR.bind (fun _ => OComp.CostBoundR.bind (by intro _; trivial)
      (costC_linksO H i t₁ l fun b hb => hl b (List.mem_cons_of_mem _ hb)))
      (costC_linkO H i t₁ a.2 a.1 (hl a (List.mem_cons_self ..)))

theorem costC_commitAt (H : PassFits W S hK pass) (i : I) (d : DrawC lam L Bd aT aL h.KT h.KL)
    (hd : FitC W h d) : (commitAt W S cA h i d).CostBoundR (costP hK pass) (commitC W h) := by
  refine OComp.CostBoundR.bind (fun t₁ => ?_) (costC_tabO H h.b₀ i d.r _)
  have q2 := costC_tabsO (h := h) H i d.copies
  rw [hd.2.1] at q2
  refine OComp.CostBoundR.bind (fun ts => ?_) q2
  have q3 := costBound_proveX hK pass Tag.test (batTC L aT) (wTC W) W.embT id (fun _ => none)
    (cmsTA cA t₁.tree.root (L.recOf i t₁.r t₁.seed).2) (L.recOf i t₁.r t₁.seed) (L.encodeIndex i t₁.r)
    (fun _ => t₁.tree) (h.st.T i t₁.r t₁.seed d.κ) (h.dressT (h.rvT d.κ) d.co) h.capT H.testsT
  have e3 : (h.dressT (h.rvT d.κ) d.co).path.length = W.depthReqT := hd.1
  rw [e3] at q3
  refine OComp.CostBoundR.bind (fun a => ?_) q3
  have q4 := costC_linksO (cA := cA) (h := h) H i t₁ (d.copies.zip ts) fun b hb =>
    hd.2.2 b.1 (List.of_mem_zip (a := b.1) (b := b.2) hb).1
  have hlen : (d.copies.zip ts).length * linkC W h ≤ (h.M + 1) * linkC W h := by
    refine Nat.mul_le_mul_right _ ?_
    rw [List.length_zip, hd.2.1]
    exact Nat.min_le_left _ _
  exact OComp.CostBoundR.bind (by intro _; trivial) (q4.mono hlen)

theorem costC_commitW (H : PassFits W S hK pass) (hp : PathsFit W h) (i : I) :
    (commitW W S cA h i).CostBoundR (costP hK pass) (commitC W h) :=
  costR_bindOut (fun d hd => costC_commitAt H i d hd) _ (queryBound_coinsC W h)
    (allOut_coinsC W h hp)

theorem costC_proveAt (H : PassFits W S hK pass) (isk : Isk lam L Bd aT aL) (x : X)
    (d : DrawP lam L Bd aT aL h.KB) (hd : d.co.path.length = W.depthReq) :
    (proveAt W cA r₀ h isk x d).CostBoundR (costP hK pass) (proveC W h) := by
  unfold proveAt
  cases isk.copies[d.j]? with
  | none => trivial
  | some t =>
    have q := costBound_proveX hK pass Tag.onl L.onlineBatch (wBC W) W.embB id (xinBA r₀)
      (cmsBA cA t.tree.root (L.recOf isk.i t.r t.seed).2) (x, L.recOf isk.i t.r t.seed)
      (L.encodeIndex isk.i t.r) (fun _ => t.tree) (h.st.B isk.i t.r t.seed x (h.nm d.j) d.κ)
      (h.dressB (h.rvB d.κ) d.co) h.capB H.testsB
    have e : (h.dressB (h.rvB d.κ) d.co).path.length = W.depthReq := hd
    rw [e] at q
    exact OComp.CostBoundR.bind (by intro _; trivial) q

theorem costC_proveW (H : PassFits W S hK pass) (hp : PathsFit W h)
    (isk : Isk lam L Bd aT aL) :
    ∀ b : List (X × Unit), (proveW W cA r₀ h isk b).CostBoundR (costP hK pass) (proveC W h)
  | [] => trivial
  | [(x, _)] =>
    costR_bindOut (P := fun d : DrawP lam L Bd aT aL h.KB => d.co.path.length = W.depthReq)
      (fun d hd => (OComp.CostBoundR.bind (t := 0) (by intro _; trivial)
        (costC_proveAt H isk x d hd)).mono (by omega)) _
      (fun _ _ _ => trivial) (fun _ _ e => hp.B e)
  | _ :: _ :: _ => trivial

/-- **THE COMMITTER AT THE THIRD EXIT ASKS AT MOST commitC HASH QUERIES, ON EVERY PATH.** -/
theorem hashCalls_commitW (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (F : FirstIs hK m)
    (H : PassFits W S hK pass) (hp : PathsFit W h) (i : I) :
    ((commitW W S cA h i).overOneF m (moreP pass)).QueryBound (commitC W h) := by
  refine queryBound_overOneF m (moreP pass) _ _ ?_
  have e : costF m (moreP pass) = costP hK pass := by
    funext o q r
    exact costF_eq_costP hK pass m F o q r
  rw [e]
  exact costC_commitW H hp i

/-- **THE PROVER AT THE THIRD EXIT ASKS AT MOST proveC HASH QUERIES, ON EVERY PATH.** -/
theorem hashCalls_proveW (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (F : FirstIs hK m)
    (H : PassFits W S hK pass) (hp : PathsFit W h) (isk : Isk lam L Bd aT aL)
    (b : List (X × Unit)) :
    ((proveW W cA r₀ h isk b).overOneF m (moreP pass)).QueryBound (proveC W h) := by
  refine queryBound_overOneF m (moreP pass) _ _ ?_
  have e : costF m (moreP pass) = costP hK pass := by
    funext o q r
    exact costF_eq_costP hK pass m F o q r
  rw [e]
  exact costC_proveW H hp isk b

/-- The committer's count by its parts. -/
theorem commitC_eq : commitC W h = (h.M + 2) * tabW W +
    chainF L.offline.shape aT (wTC W).sh h.capT 0 W.depthReqT + (h.M + 1) * linkC W h := by
  unfold commitC
  ring

end OnBytes.WholeKey

namespace OnBytes.WholeKey

/-- The committer, then the committer again and the prover, with a public reading of q₀ queries and
one query for a commitment ID; M + 1 copies, tab a table, off the key's run, lnk a link, on a
session. -/
def budgetC (q₀ M tab off lnk on : ℕ) : ℕ :=
  2 * (q₀ + ((M + 2) * tab + off + (M + 1) * lnk) + 1) + on

/-- **At these numerals 2 ^ 48 bears exactly up to 81 copies.** -/
theorem copies_within_two_pow_48 (M : ℕ) :
    budgetC 8 M 8589982768 5223661230411 1649307525166 177887278538 ≤ 2 ^ 48 ↔ M + 1 ≤ 81 := by
  unfold budgetC
  omega

end OnBytes.WholeKey

#print axioms OnBytes.WholeKey.hashCalls_commitW
#print axioms OnBytes.WholeKey.hashCalls_proveW
#print axioms OnBytes.WholeKey.commitC_eq
#print axioms OnBytes.WholeKey.copies_within_two_pow_48
