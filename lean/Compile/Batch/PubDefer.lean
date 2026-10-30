-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/PubDefer.lean: deferred programming for the challenger of the compiled scheme that
publishes a function of the key at the setup (`VCBP`, Compile/Batch/PubChall.lean) (words of this
library: lean/GLOSSARY.md).

  `stepP`   under the hypotheses of its statement: every step of the challenger keeps the invariant
            and makes at most the queries counted for its kind of call
  `withinVCBP`   under the hypotheses of its statement: every run against the challenger stays
                 within the rules and the counts, in both modes. The counts are those of one setup
                 and n batches, and the oracles with marked queries are the ten (`Disc.osB`) and the
                 ghost names `fbw t k`, k < maxMoreB W (`osBG`)
  `hopDeferBPOf`   the hop of deferred programming, generic in its bound, under the hypotheses of
                   its statement: whatever one passage to fresh answers costs at the counts of the
                   scheme (`HopB`, Compile/Batch/SpecHop.lean), mode R and mode I of the challenger
                   differ by at most that
Among the hypotheses of all three: `Spec.safeCB`, `Spec.safePB` and L.maxBatchSize = 2 ^ W.depthReq. The modes
R and I are those of Rom/Defer.lean.

The invariant `WorldB.Inv` and the two lemmas on the committer's and the prover's programs
(`WorldB.setup`, `WorldB.session`; Compile/Batch/WithinVCB.lean) are used as they are: the published
value is computed from the program's output without a coin, a query or a token, and the invariant
does not depend on replies.

After Compile/Batch/WithinVCB.lean; here its lemmas are applied to the challenger `VCBP`.
-/
import Compile.Batch.WithinVCB
import Compile.Batch.PubReal
import Compile.Batch.SpecHop

noncomputable section

namespace Compile.Batch.Disc
open Iop Rom Prob
open scoped ENNReal
open Compile.GlueB (GCall GAdm)
open Compile.Life2 (virt run_bind run_fresh0)
open Compile.Life2.Many (view run_virt frame_virt)
open Compile.Life2.WorldsX (dummy gap)
open Compile.Disc (Rules nEv TreeTok)
open VirtO

variable {I X V : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
  (pw : IVK lam L → WKey lam L → V) (i : I)

/-- Under the hypotheses below: every step of the challenger keeps the invariant and makes at most
the queries counted for its kind of call. -/
theorem stepP (hC : Spec.safeCB) (hP : Spec.safePB) (hN : L.maxBatchSize = 2 ^ W.depthReq)
    (m : Bool) (s : Option (IskH lam L × ℕ)) (d : DSt (spec lam W.K L))
    (c : GCall X Unit) (hI : WorldB.Inv W p s d) :
    ∀ y ∈ (((VCBP W WP p pw i).step s c).run m d).support,
      WorldB.Inv W p y.1.2 y.2 ∧
      ∀ o,
        y.2.nPlain o ≤ d.nPlain o + callCostB (eCB W p) ePB c o ∧
        nEv y.2 o ≤ nEv d o + callCostB (mCB W p) (mPB W) c o := by
  have triv : ∀ (a : BInP V lam L)
          (y : (BInP V lam L × Option (IskH lam L × ℕ)) × DSt (spec lam W.K L)),
        y ∈ ((Step.pure (a, s) : St lam W.K L (BInP V lam L × Option (IskH lam L × ℕ))).run
            m d).support →
        WorldB.Inv W p y.1.2 y.2 ∧
        ∀ o,
          y.2.nPlain o ≤ d.nPlain o + callCostB (eCB W p) ePB c o ∧
          nEv y.2 o ≤ nEv d o + callCostB (mCB W p) (mPB W) c o := by
    intro a y hy
    simp only [Step.run, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨hI, fun o => ⟨Nat.le_add_right _ _, Nat.le_add_right _ _⟩⟩
  intro y hy
  rcases c with _ | b
  · rcases s with _ | k
    · rw [HopRP.VCBP_setup W WP p pw i, run_bind, PMF.mem_support_bind_iff] at hy
      obtain ⟨z, hz, hy⟩ := hy
      rw [run_fresh0] at hy
      simp only [Step.run, PMF.support_pure, Set.mem_singleton_iff] at hy
      subst hy
      exact WorldB.setup (i := i) hC m d hI z hz
    · exact triv _ y hy
  · rcases s with _ | ⟨k, N₀⟩
    · exact triv _ y hy
    · by_cases hb : hasOwn b = true
      · rw [HopRP.VCBP_own W WP p pw i k N₀ b hb, run_fresh0,
          run_bind, PMF.mem_support_bind_iff] at hy
        obtain ⟨z, hz, hy⟩ := hy
        simp only [Step.run, PMF.support_pure, Set.mem_singleton_iff] at hy
        subst hy
        exact WorldB.session hP hN m k N₀ _ _ d hI z hz
      · rw [HopRP.VCBP_none W WP p pw i k N₀ b (by simpa using hb)] at hy
        exact triv _ y hy

/-- Under the hypotheses below: every run against the challenger stays within the rules and the
counts, in both modes. -/
theorem withinVCBP (hC : Spec.safeCB) (hP : Spec.safePB)
    (hN : L.maxBatchSize = 2 ^ W.depthReq) (ok : ZKCP.Gen.Batch X Unit → Prop) {α : Type}
    (A : Adv (spec lam W.K L) (GCall X Unit) (BInP V lam L) α) (n : ℕ)
    (m : Bool) (hA : GAdm ok A false n) :
    ∀ x ∈ (interact ((VCBP W WP p pw i).world m) A (none, DSt.init _)).support,
      x.2.2.Within (eAllB W p n) (mAllB W p n) (rulesB W.K L lam p).bits (osBG (maxMoreB W)) := by
  intro x hx
  have htab : ∀ (s : Option (IskH lam L × ℕ))
          (d : DSt (spec lam W.K L)) (T : Table (spec lam W.K L)),
        WorldB.Inv W p s d → WorldB.Inv W p s { d with table := T } := by
    intro s d T h
    rcases s with _ | ⟨k, N₀⟩
    · exact TidyO.table h T
    · exact ⟨h.1.table T, WorldB.iskOK_of h.2.1 fun ts _ hc => ⟨hc.lt, hc.tail, hc.others⟩,
        ⟨h.2.2.1.len, h.2.2.1.tails, h.2.2.1.low, h.2.2.1.high⟩, h.2.2.2⟩
  obtain ⟨hI, hc⟩ := within_interactB (VCBP W WP p pw i) m (WorldB.Inv W p) (eCB W p) (mCB W p) ePB
    (mPB W) htab (stepP W WP p pw i hC hP hN m) ok A false n none (DSt.init _) hA TidyO.init x hx
  have ht : TidyO (rulesB W.K L lam p) x.2.2 := by
    rcases hs : x.2.1 with _ | ⟨k, N₀⟩
    · rw [hs] at hI; exact hI
    · rw [hs] at hI; exact hI.1
  refine withinO' _ _ _ _ _ _ ht (fun o ho => zeroBG I X lam L W p n o ho) (fun o => ?_) fun o => ?_
  · have := (hc o).1
    simpa [eAllB, DSt.init] using this
  · have := (hc o).2
    simpa [mAllB, DSt.init, nEv] using this

/-- The hop of deferred programming, generic in its bound, under the hypotheses below: whatever one
passage to fresh answers costs at the counts of the scheme (`HopB`, Compile/Batch/SpecHop.lean),
mode R and mode I of the challenger differ by at most that. -/
theorem hopDeferBPOf {h : ℕ → ℕ → ℝ≥0∞} (hh : HopB W p h) (hC : Spec.safeCB) (hP : Spec.safePB)
    (hN : L.maxBatchSize = 2 ^ W.depthReq) (ok : ZKCP.Gen.Batch X Unit → Prop) {α : Type}
    (A : Adv (spec lam W.K L) (GCall X Unit) (BInP V lam L) α) (t n : ℕ)
    (hB : A.TotalBound t (n + 1)) (hA : GAdm ok A false n) :
    tv ((interact ((VCBP W WP p pw i).world false) A (none, DSt.init _)).map Prod.fst)
        ((interact ((VCBP W WP p pw i).world true) A (none, DSt.init _)).map Prod.fst) ≤ h t n :=
  hh n _ _ _ _ (VCBP W WP p pw i) none A t (n + 1) hB
    (withinVCBP W WP p pw i hC hP hN ok A n true hA)


end Compile.Batch.Disc
