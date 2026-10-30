-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/Defer2Main.lean: the compiler theorem from one bound on the total variation distance of two
experiments. The compiler theorem with tests, links in the verification key, free empty slots
(Compile/Batch/PubProgMainBGr.lean: `mainBatchKEGrWithBOf`) with the inequality at the one door
(`HopDoor`) as its premise, in the place of a bound for all challengers (`HopU`); so also at the
sharper price `costU2` (CompileK/Defer2Door.lean): `mainBatchKE2`; each under the hypotheses of its
statement.

A definition (`HopDoor`), the analogues, with that premise, of the five theorems of
Compile/Batch/PubProgMainBGr.lean between `HopU` and the compiler theorem (the same names, with a
D), and three corollaries. The proofs are those of the five, but for one line of one proof
(`realToWrBPUTOfD`: `HopDoor` is applied where `realToWrBPUTOf` applies `PubG.hopUOf`). Nothing
assumed beyond the hypotheses of the statements, in the random-oracle model, on Lean's three axioms.
In this file the door, or the hop, is the step from mode R to mode I; the inequality at the door is
`HopDoor`; its price, or the hop's bound, is h.

Main names:
  `HopDoor W WP p B h`: for every published function pw, index, admissible adversary with t queries,
    n batches of at most B requests: mode R of the challenger with the prover with free empty slots
    is within h t n of mode I of the challenger with the base prover.
  `hopDoor_of_hopU`: under `hN`, `HopU W p B h` gives it (`PubG.hopUOf`): so the five analogues say
    no less than the five with `HopU`.
  `realToWrBPUTOfD`, `closePubUTOfD`, `privacyPubGrWithUOfD`, `privacyKEGrWithBOfD`,
    `mainBatchKEGrWithBOfD`: the five.
  `mainBatchKE2`: under the hypotheses of its statement: Gen.IsZKCPArgWith .. (argBKE W WP p) B ..
    (alphaBG W M) (epsB W M) (zetaBGen L p M (costU2 W p B)): the same scheme, extractor, simulator,
    α, ε; ζ with the vertices at 2 λ.

Limits: `costU2` is a formula in the counts, not evaluated.







`zetaT` (Cond/ObjBounds.lean) has `hashTerms2` (its summands `muB2`, `hashSqBG2`).
-/
import CompileK.Defer2Door

set_option autoImplicit false

namespace Compile.Batch
open Iop Rom Prob ZKCP Compile.GenMap Compile.GenPub
open Compile.GlueB (GCall SCall GAdm asW realW simOf viaCP Close)
open Compile.BatchLife (LifeOutB LifeInB LifeB LifeAdmB Sims simWorldB lifeStarBWith)
open Compile.Disc (nEv)
open scoped ENNReal

variable {I X V : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- The inequality at the door; the head's row `HopDoor` tells it. -/
def HopDoor (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (B : ℕ) (h : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∀ (V : Type) (pw : IVK lam L → WKey lam L → V) (i : I) (ok : Gen.Batch X Unit → Prop),
    (∀ b, ok b → b.pairs.length ≤ B) →
    ∀ (α : Type) (A : Adv (spec lam W.K L) (GCall X Unit) (BInP V lam L) α) (t n : ℕ),
      A.TotalBound t (n + 1) → GAdm ok A false n →
      tv ((interact ((VCBPG W WP p pw (PpU W WP p) i).world false)
            A (none, DSt.init _)).map Prod.fst)
          ((interact ((VCBPG W WP p pw (Pp W WP p) i).world true) A (none, DSt.init _)).map
            Prod.fst) ≤ h t n

theorem hopDoor_of_hopU {W : QueryLayout lam L} (WP : WireBP L) {p : Params} {B : ℕ} {h : ℕ → ℕ → ℝ≥0∞}
    (hN : L.maxBatchSize = 2 ^ W.depthReq) (hh : HopU W p B h) : HopDoor W WP p B h :=
  fun _ pw i ok hok _ A t n hT hA => PubG.hopUOf W WP p pw i hN B hh ok hok A t n hT hA

theorem hopDoor2 (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
    (B : ℕ) (hN : L.maxBatchSize = 2 ^ W.depthReq) :
    HopDoor W WP p B (Disc.costU2 W p B) :=
  fun V pw i ok hok α A t n hT hA => Disc.hopU2 I X V lam L W WP p pw i hN B ok hok α A t n hT hA

/-- From the real experiment of the token form to the wrapped lifetime game. -/
theorem realToWrBPUTOfD (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
    (pw : IVK lam L → WKey lam L → V) (Vf : V → X → Prf lam L → TypedOracleComputation lam W.K L Bool) (i : I)
    (hL : L.Wired) (hC : L.onlineBatch.ann.Coherent) (hF : L.onlineBatch.ann.Fmt) (hW : W.OKG) (hG : GrFitPB W)
    (hWP : WP.OK) (B : ℕ) (hB : B ≤ L.maxBatchSize) {h : ℕ → ℕ → ℝ≥0∞} (hh : HopDoor W WP p B h)
    (ok : Gen.Batch X Unit → Prop) (hok : ∀ b, ok b → b.pairs.length ≤ B) {α : Type}
    (A : Adv (spec lam W.K L) (GCall X Unit) (BInP V lam L) α) (t n : ℕ)
    (hT : A.TotalBound t (n + 1)) (hA : GAdm ok A false n) :
    tv ((interact (realW (argBPGT W WP p pw (PpU W WP p) Vf) i)
          A (none, Table.empty _)).map Prod.fst)
        ((interact (asW Unit (WrBP W p pw (LifeB _ L p.leaves i))) A
            (iniBP W p pw _ (none, Table.empty _))).map Prod.fst) ≤
      p.leaves * binTail n p.leaves p.s1 + h t n := by
  rw [real_eq_modeRPG ok (maskPpU W WP p) Vf A n hA,
    ← lumpBP W WP p pw i (eqSetupB eqProveB) (eqBatchB eqProveB) hL hC hF hW hG hWP A
      (allCalls_of_gAdmP ok (fun b hb => (hok b hb).trans hB) A false n hA)]
  have h1 : tv ((interact ((VCBPG W WP p pw (PpU W WP p) i).world false)
          A (none, DSt.init _)).map Prod.fst)
        ((interact ((VCBP W WP p pw i).world true) A (none, DSt.init _)).map Prod.fst) ≤ h t n :=
    hh V pw i ok hok α A t n hT hA
  rw [hopLateBP W WP p pw i lateCpB latePpB hL hC hW hG A fun x hx =>
      (Disc.withinVCBP W WP p pw i Disc.safeCB Disc.safePB hW.slots ok A n true hA x hx).1] at h1
  refine (tv_triangle _
    ((interact (chalLBP W WP p pw i).world A (none, LSt.init _)).map Prod.fst) _).trans ?_
  exact (add_le_add h1 (overrunBP W WP p pw i ok A n hA)).trans (le_of_eq (add_comm _ _))

/-- Closeness for the token form, for batches of at most B requests. (not all hypotheses are named
here: see the statement below) -/
theorem closePubUTOfD (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
    (pw : IVK lam L → WKey lam L → V) (Vf : V → X → Prf lam L → TypedOracleComputation lam W.K L Bool)
    (Ryes Rno : I → X → Prop) (M : LH.Nums) (h : L.PropsNoAcc Ryes Rno M) (hW : W.OKG)
    (hG : GrFitPB W) (hWP : WP.OK) (hF : L.onlineBatch.ann.Fmt) (hBu : Budget p M) (Sm : Sims L)
    (hS : Sm.Good Ryes M.zT M.zL M.zO) (i₀ : I) (B : ℕ) (hB : B ≤ L.maxBatchSize)
    {hb : ℕ → ℕ → ℝ≥0∞} (hh : HopDoor W WP p B hb) :
    Close (relPair Ryes Rno h.sub) (argBPGT W WP p pw (PpU W WP p) Vf) B
      (asW Unit (WrBP W p pw (simWorldB _ L p.leaves Sm i₀)))
      (iniBP W p pw _ (none, Table.empty _)) (zetaBGen L p M hb) := by
  intro i α A t n hA hP
  refine le_trans
    (tv_triangle _
      ((interact (asW Unit (WrBP W p pw (LifeB _ L p.leaves i))) A
        (iniBP W p pw _ (none, Table.empty _))).map Prod.fst) _)
    (add_le_add
      (realToWrBPUTOfD W WP p pw Vf i h.wired h.cohB hF hW hG hWP B hB hh _
        (fun b hb => hb.1) A t n hA hP) ?_)
  have hBeq : ∀ (G : LifeWB W) (s : G.σ),
      (interact (asW Unit (WrBP W p pw G)) A (iniBP W p pw G s)).map Prod.fst =
        (interact G ((wrapGP W p pw (fun sT ls => CpW W p sT (ls.take (p.M + 1))) (PpW W p)).adv
              A (none, LSt.init _)) s).map Prod.fst :=
    fun G s =>
      interact_adv (wrapGP W p pw (fun sT ls => CpW W p sT (ls.take (p.M + 1))) (PpW W p)) G A _ s
  rw [hBeq, hBeq]
  exact lifeStarBWith _ I X L Ryes M p.leaves p.s1 h.wired h.reads Sm hS hBu.1 hBu.2 i i₀ α _ n
    (lifeAdmB_wrapGP W p pw _ _ (Ryes i) A n
      (gAdm_mono (fun b hb => ⟨hb.1.trans hB, hb.2⟩) A false n hP))

/-- Index privacy for batches of at most B requests, with the simulator `simBPGr`. (not all
hypotheses are named here: see the statement below) -/
theorem privacyPubGrWithUOfD [Inhabited V] (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
    (pw : IVK lam L → WKey lam L → V) (Vf : V → X → Prf lam L → TypedOracleComputation lam W.K L Bool)
    (Ryes Rno : I → X → Prop) (M : LH.Nums) (h : L.PropsNoAcc Ryes Rno M) (hW : W.OKG)
    (hG : GrFitPB W) (hWP : WP.OK) (hF : L.onlineBatch.ann.Fmt) (hBu : Budget p M) (Sm : Sims L)
    (hS : Sm.Good Ryes M.zT M.zL M.zO) (i₀ : I) (B : ℕ) (hB : B ≤ L.maxBatchSize)
    {hb : ℕ → ℕ → ℝ≥0∞} (hh : HopDoor W WP p B hb) :
    Gen.HasIndexPrivacyWith (relPair Ryes Rno h.sub) (argBPG W WP p pw (PpU W WP p) Vf) B
      (simBPGr W p pw Sm i₀) (zetaBGen L p M hb) := by
  refine GlueB.gluePrivacyWith _ _ _ _ Unit _ _ _ _ _ _
    ((WrBP W p pw (simWorldB _ L p.leaves Sm i₀)).pre (ghost W))
    (iniBP W p pw _ (none, Table.empty _)) _
    (Rom.viaConsistent _ _ _ _ _ (ghostPerm I X lam L W) _ (consistent_wrapBP _)) ?_
  rw [argBPG_via W WP p pw (PpU W WP p) Vf hW (routedF_PpU W WP p hW)]
  exact GlueB.closeVia _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ghostPerm I X lam L W)
    (closePubUTOfD W WP p pw Vf Ryes Rno M h hW hG hWP hF hBu Sm hS i₀ B hB hh)

/-- the same (`simBKGr`) for the scheme with the links in the verification key -/
theorem privacyKEGrWithBOfD (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (Ryes Rno : I → X → Prop)
    (M : LH.Nums) (h : L.PropsNoAcc Ryes Rno M) (hW : W.OKG) (hG : GrFitPB W) (hWP : WP.OK)
    (hF : L.onlineBatch.ann.Fmt) (hBu : Budget p M) (Sm : Sims L) (hS : Sm.Good Ryes M.zT M.zL M.zO)
    (i₀ : I) (B : ℕ) (hB : B ≤ L.maxBatchSize) {hb : ℕ → ℕ → ℝ≥0∞} (hh : HopDoor W WP p B hb) :
    Gen.HasIndexPrivacyWith (relPair Ryes Rno h.sub) (argBKE W WP p) B
      (simBKGr W p Sm i₀) (zetaBGen L p M hb) :=
  GenMap.privacyWith (via_KE W WP p)
    _ (privacyPubGrWithUOfD W WP p _ _ Ryes Rno M h hW hG hWP hF hBu Sm hS i₀ B hB hh)

/-- The compiler theorem with tests, links in the verification key, free empty slots, for batches of
at most B ≤ maxBatchSize requests, generic in the hop's bound hb. (not all hypotheses are named here: see the
statement below) -/
theorem mainBatchKEGrWithBOfD (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
    (Ryes Rno : I → X → Prop) (M : LH.Nums) (h : L.PropsNoAcc Ryes Rno M) (hW : W.OKG)
    (hG : GrFitB W Ryes) (hWP : WP.OK) (hF : L.onlineBatch.ann.Fmt) (hBu : Budget p M)
    (Sm : Sims L) (hS : Sm.Good Ryes M.zT M.zL M.zO) (i₀ : I) (B : ℕ) (hB : B ≤ L.maxBatchSize)
    {hb : ℕ → ℕ → ℝ≥0∞} (hh : HopDoor W WP p B hb) :
    Gen.IsZKCPArgWith (relPair Ryes Rno h.sub) (argBKE W WP p) B (extractorBK W) (simBKGr W p Sm i₀)
      (alphaBG W M) (epsB W M) (zetaBGen L p M hb) :=
  ⟨fun i b hb' =>
      completeKE_of W WP p _ _ (completeBatchUGr I X lam L W WP p Ryes Rno M h hW hG hWP hF)
        i b ⟨hb'.1.trans hB, hb'.2⟩,
    bindingKEGr W WP p Ryes Rno M h hW,
    privacyKEGrWithBOfD W WP p Ryes Rno M h hW hG.toP hWP hF hBu Sm hS i₀ B hB hh⟩


/-- The compiler theorem at the sharper price `costU2`. -/
theorem mainBatchKE2 (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (Ryes Rno : I → X → Prop)
    (M : LH.Nums) (h : L.PropsNoAcc Ryes Rno M) (hW : W.OKG) (hG : GrFitB W Ryes) (hWP : WP.OK)
    (hF : L.onlineBatch.ann.Fmt) (hBu : Budget p M) (Sm : Sims L) (hS : Sm.Good Ryes M.zT M.zL M.zO)
    (i₀ : I) (B : ℕ) (hB : B ≤ L.maxBatchSize) :
    Gen.IsZKCPArgWith (relPair Ryes Rno h.sub) (argBKE W WP p) B (extractorBK W) (simBKGr W p Sm i₀)
      (alphaBG W M) (epsB W M) (zetaBGen L p M (Disc.costU2 W p B)) :=
  mainBatchKEGrWithBOfD W WP p Ryes Rno M h hW hG hWP hF hBu Sm hS i₀ B
    hB (hopDoor2 W WP p B hW.slots)

end Compile.Batch
