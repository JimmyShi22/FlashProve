-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/PubProgMainBGr.lean: index privacy for the prover with no query for an empty slot
(`PpU`, Compile/Batch/StarU.lean), when rounds may have proof-of-work bits: a batch is counted by
its requests, not by its slots. Generic in what one passage to fresh answers costs (words of this
library: lean/GLOSSARY.md).

For every B ≤ N (N: the slots of a batch) and batches of at most B requests. The experiments with
`PpU` join those with `Pp` in mode I (Compile/Batch/PubProgModeI.lean; the modes: Rom/Defer.lean);
the lemma on deferred programming is applied to the runs with `PpU`. That they keep the rules comes
from the runs of `Pp` (`PubG.within₂`); how many marked queries they make is counted on `PpU` itself
(Compile/Batch/CountU.lean, Compile/Batch/CountURun.lean: mAllU W p B n
(Compile/Batch/PriceUB.lean), every attempt counted: the ghost name `fbw t k` has the count cTry k
of B slots).

  `HopU W p B h`  h t n bounds one passage to fresh answers for every challenger whose runs in mode
                  I obey the rules and keep the counts of one setup and n batches of at most B
                  requests (eAllB, mAllU W p B, the lengths of rulesB, the oracles osBG), against t
                  queries in all (Rom/SpecHopCost.lean). By definition HopBAt W p (mAllU W p B) h
                  (Compile/Batch/SpecHop.lean), of which `HopB` is the case mAllB W p.
  `HopU.anti`, `hopU_of_hopB`  A bound for more requests serves fewer; the bounds of the scheme that
                               hashes every slot (HopB W p h) serve batches of at most B ≤ N
                               requests.
  `hopU_names`, `hopU_total`  `HopU`'s two instances at its counts: `Rom.costNames`,
                              `Rom.costTotal`.
  `PubG.hopUOf`  Mode R of the challenger with `PpU` is within h t n of mode I of the challenger
                 with `Pp`, for admissible adversaries (`GAdm`) with at most t queries and n
                 batches, each of at most B requests, if L.maxBatchSize = 2 ^ W.depthReq and `HopU W p B h`.
  `realToWrBPUTOf`  From the real experiment of the token form `argBPGT`
                    (Compile/Batch/PubProg.lean) to the reduction around the lifetime game (`WrBP`,
                    Compile/Batch/PubWr.lean): the overrun term + h t n.
  `closePubUTOf`, `privacyPubGrWithUOf`  Closeness; index privacy of the scheme argBPG .. (PpU ..)
                                         for batches of at most B requests, with the simulator
                                         `simBPGr` and ζ = zetaBGen L p M h.
  `privacyKEGrWithBOf`, `mainBatchKEGrWithBOf`  The same for the scheme `argBKE` with the Links in
                                                the verification key; the three properties for
                                                batches of at most B requests. Among the hypotheses
                                                of the last five: `L.PropsNoAcc` (or its parts),
                                                `W.OKG`, `GrFitPB W` (for the last:
                                                `GrFitB W Ryes`), `WP.OK`, `Fmt`, B ≤ N,
                                                `HopU W p B h`; from `closePubUTOf` on also
                                                `Budget p M` and good simulators.

Notation:
  `Ryes`, `Rno`: I → X → Prop; `relPair Ryes Rno sub`: the `Gen.RelPair` made of the two
    (Compile/Spec.lean)
  `M`: an `LH.Nums`: all numbers of the interface (Iop/InteractiveOracleProof.lean), `M.zT`, `M.zL`, `M.zO` among
    them; not `p.M`: the number of copies is `p.M` + 1 (`Params`, Compile/Star.lean)
  `Sm`: a `Sims L` (Compile/Batch/SpecLife.lean)
  `t`, `n`: in `A.TotalBound t (n + 1)`: at most t queries in all and at most n + 1 calls, on every
    path (Rom/World.lean); `Budget p M`: Compile/Spec.lean
  in the names: `..With..`: as in `IsZKCPArgWith` (ZKCP/Gen.lean); `argBPGT`: the token form of
    `argBPG`; `PpU`: no query for an empty slot

Limits: no explicit bound with proof-of-work bits is given here. The setup's share of the counts
does not shrink, nor does the count at the node oracle of request trees (`mPU` at `rnode` has N, not
B). The terms of the simulated sessions still count N slots a batch (n N zO). n counts batches.
-/
import Compile.Batch.MainKEGr
import Compile.Batch.CompleteUMainG
import Compile.Batch.CountURun
import Compile.Batch.PriceUB
import Compile.Batch.PubProgMainGr

noncomputable section

namespace Compile.Batch
open Iop Rom Prob ZKCP Compile.GenMap Compile.GenPub
open Compile.GlueB (GCall SCall GAdm asW realW simOf viaCP Close)
open Compile.BatchLife (LifeOutB LifeInB LifeB LifeAdmB Sims simWorldB lifeStarBWith)
open Compile.Disc (nEv)
open scoped ENNReal

variable {I X V : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- an adversary that is admissible for ok is admissible for every weaker condition -/
theorem gAdm_mono {S : OSpec} {X Wn IVK Pf α : Type} {ok ok' : Gen.Batch X Wn → Prop}
    (h : ∀ b, ok b → ok' b) (A : Adv S (GCall X Wn) (GlueB.GIn IVK Pf) α) :
    ∀ (f : Bool) (n : ℕ), GAdm ok A f n → GAdm ok' A f n := by
  induction A with
  | halt a => exact fun _ _ _ => trivial
  | sample m k ih => exact fun f n hA r => ih r f n (hA r)
  | query o q k ih => exact fun f n hA r => ih r f n (hA r)
  | call c k ih =>
    intro f n hA
    rcases c with _ | b
    · exact ⟨hA.1, fun a => ih a true n (hA.2 a)⟩
    · cases n with
      | zero => exact hA.elim
      | succ n => exact ⟨hA.1, h b hA.2.1, fun a => ih a f n (hA.2.2 a)⟩

/-- What one passage to fresh answers costs at the counts of one setup and n batches of at most B
requests. -/
def HopU (W : QueryLayout lam L) (p : Params) (B : ℕ) (h : ℕ → ℕ → ℝ≥0∞) : Prop :=
  HopBAt W p (mAllU W p B) h

theorem HopU.mono {W : QueryLayout lam L} {p : Params} {B : ℕ} {h h' : ℕ → ℕ → ℝ≥0∞}
    (hh : HopU W p B h) (hle : ∀ t n, h t n ≤ h' t n) : HopU W p B h' :=
  HopBAt.mono hh hle

/-- for each attempt number k: fewer slots, fewer attempts counted -/
theorem cTry_mono {K : ℕ} (k : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (Ws : RoundsQueryLayout lam K s A) {a b : ℕ},
      a ≤ b → cTry k a s A Ws ≤ cTry k b s A Ws
  | [], _, _, _, _, _ => le_rfl
  | _ :: s, (_, A), (_, Ws), _, _, h =>
    Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_right _ h) _) (cTry_mono k s A Ws h)

/-- fewer requests, fewer marked queries, oracle by oracle -/
theorem mPU_mono (W : QueryLayout lam L) {a b : ℕ} (h : a ≤ b) (o : OracleName) : mPU W a o ≤ mPU W b o := by
  cases o with
  | leaf => exact cTrees_mono _ _ _ h
  | node => exact cTrees_mono _ _ _ h
  | rleaf => exact Nat.mul_le_mul_left _ h
  | rnode => exact le_rfl
  | fb t' =>
    show (if t' = Tag.onl then (a + 1) * L.onlineBatch.loc.shape.length else 0) ≤
      (if t' = Tag.onl then (b + 1) * L.onlineBatch.loc.shape.length else 0)
    split
    · exact Nat.mul_le_mul_right _ (Nat.succ_le_succ h)
    · exact le_rfl
  | fbw t' k =>
    show (if t' = Tag.onl then cTry k a L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh else 0) ≤
      (if t' = Tag.onl then cTry k b L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh else 0)
    split
    · exact cTry_mono k _ _ _ h
    · exact le_rfl
  | g t' =>
    show (if t' = Tag.onl then Disc.joins L.onlineBatch.loc.shape L.onlineBatch.ann * a else 0) ≤
      (if t' = Tag.onl then Disc.joins L.onlineBatch.loc.shape L.onlineBatch.ann * b else 0)
    split
    · exact Nat.mul_le_mul_left _ h
    · exact le_rfl
  | ann => exact le_rfl
  | other => exact le_rfl

theorem mAllU_mono (W : QueryLayout lam L) (p : Params) {a b : ℕ} (h : a ≤ b) (n : ℕ) (o : OracleName) :
    mAllU W p a n o ≤ mAllU W p b n o :=
  Nat.add_le_add_left (Nat.mul_le_mul_left _ (mPU_mono W h o)) _

/-- with all slots full the counts by requests are those of the scheme that hashes every slot -/
theorem mAllU_N (W : QueryLayout lam L) (p : Params) (n : ℕ) : mAllU W p L.maxBatchSize n = Disc.mAllB W p n := by
  funext o
  show Disc.mCB W p o + n * mPU W L.maxBatchSize o = Disc.mCB W p o + n * Disc.mPB W o
  rw [mPU_N]

/-- A bound for more requests serves fewer. -/
theorem HopU.anti {W : QueryLayout lam L} {p : Params} {B B' : ℕ} {h : ℕ → ℕ → ℝ≥0∞}
    (hB : B ≤ B') (hh : HopU W p B' h) : HopU W p B h :=
  HopBAt.anti (fun n o => mAllU_mono W p hB n o) hh

/-- The bounds of the scheme that hashes every slot serve batches of at most B ≤ N requests too. -/
theorem hopU_of_hopB {W : QueryLayout lam L} {p : Params} {B : ℕ} {h : ℕ → ℕ → ℝ≥0∞}
    (hB : B ≤ L.maxBatchSize) (hh : HopB W p h) : HopU W p B h :=
  HopBAt.anti (fun n o => (mAllU_mono W p hB n o).trans (le_of_eq (congrFun (mAllU_N W p n) o))) hh

/-- the library's bound with the whole number of queries at every oracle, at these counts -/
theorem hopU_names (W : QueryLayout lam L) (p : Params) (B : ℕ) :
    HopU W p B fun t n =>
      Rom.costNames (S := spec lam W.K L) (Disc.eAllB W p n) (mAllU W p B n)
          (Disc.rulesB W.K L lam p).bits (Disc.osBG (maxMoreB W)) t :=
  fun _ => Rom.hopCost_names (S := spec lam W.K L) _ _ _ _

/-- the library's bound for one total number of queries, at these counts -/
theorem hopU_total (W : QueryLayout lam L) (p : Params) (B : ℕ) :
    HopU W p B fun t n =>
      Rom.costTotal (S := spec lam W.K L) (Disc.eAllB W p n) (mAllU W p B n)
          (Disc.rulesB W.K L lam p).bits (Disc.osBG (maxMoreB W)) t :=
  fun _ => Rom.hopCost_total (S := spec lam W.K L) _ _ _ _


/-- without ghost names the set is that of the ten oracles -/
theorem osBG_zero : Disc.osBG 0 = Disc.osB := by
  unfold Disc.osBG
  simp

/-- Under the hypotheses below: mode R of the challenger with `PpU` is within one passage, at its
own counts, of mode I of the challenger with `Pp`. -/
theorem PubG.hopUOf (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (pw : IVK lam L → WKey lam L → V)
    (i : I) (hN : L.maxBatchSize = 2 ^ W.depthReq) (B : ℕ) {h : ℕ → ℕ → ℝ≥0∞} (hh : HopU W p B h)
    (ok : Gen.Batch X Unit → Prop) (hok : ∀ b, ok b → b.pairs.length ≤ B) {α : Type}
    (A : Adv (spec lam W.K L) (GCall X Unit) (BInP V lam L) α) (t n : ℕ)
    (hT : A.TotalBound t (n + 1)) (hA : GAdm ok A false n) :
    tv ((interact ((VCBPG W WP p pw (PpU W WP p) i).world false) A (none, DSt.init _)).map Prod.fst)
        ((interact ((VCBPG W WP p pw (Pp W WP p) i).world true) A (none, DSt.init _)).map
          Prod.fst) ≤ h t n := by
  rw [Cpl.map_eq _ _
      ((PubG.modeI_cpl W WP p pw i (safeFPp W WP p hN) (skipFPpU W WP p) A).mono fun _ _ h => h.1)]
  refine hh n _ _ _ _ (VCBPG W WP p pw (PpU W WP p) i) none A t (n + 1) hT fun x hx => ?_
  obtain ⟨h1, h2, -, h4⟩ :=
    PubG.within₂ W WP p pw i (safeFPp W WP p hN) (skipFPpU W WP p) ok A n hA x hx
  exact ⟨h1, h2, countRunU W WP p pw i hN ok hok A n true hA x hx, h4⟩

/-- From the real experiment of the token form `argBPGT` to the reduction around the lifetime game.
-/
theorem realToWrBPUTOf (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
    (pw : IVK lam L → WKey lam L → V) (Vf : V → X → Prf lam L → TypedOracleComputation lam W.K L Bool) (i : I)
    (hL : L.Wired) (hC : L.onlineBatch.ann.Coherent) (hF : L.onlineBatch.ann.Fmt) (hW : W.OKG) (hG : GrFitPB W)
    (hWP : WP.OK) (B : ℕ) (hB : B ≤ L.maxBatchSize) {h : ℕ → ℕ → ℝ≥0∞} (hh : HopU W p B h)
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
    PubG.hopUOf W WP p pw i hW.slots B hh ok hok A t n hT hA
  rw [hopLateBP W WP p pw i lateCpB latePpB hL hC hW hG A fun x hx =>
      (Disc.withinVCBP W WP p pw i Disc.safeCB Disc.safePB hW.slots ok A n true hA x hx).1] at h1
  refine (tv_triangle _
    ((interact (chalLBP W WP p pw i).world A (none, LSt.init _)).map Prod.fst) _).trans ?_
  exact (add_le_add h1 (overrunBP W WP p pw i ok A n hA)).trans (le_of_eq (add_comm _ _))

/-- Closeness for the token form `argBPGT`, for batches of at most B requests. -/
theorem closePubUTOf (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
    (pw : IVK lam L → WKey lam L → V) (Vf : V → X → Prf lam L → TypedOracleComputation lam W.K L Bool)
    (Ryes Rno : I → X → Prop) (M : LH.Nums) (h : L.PropsNoAcc Ryes Rno M) (hW : W.OKG)
    (hG : GrFitPB W) (hWP : WP.OK) (hF : L.onlineBatch.ann.Fmt) (hBu : Budget p M) (Sm : Sims L)
    (hS : Sm.Good Ryes M.zT M.zL M.zO) (i₀ : I) (B : ℕ) (hB : B ≤ L.maxBatchSize)
    {hb : ℕ → ℕ → ℝ≥0∞} (hh : HopU W p B hb) :
    Close (relPair Ryes Rno h.sub) (argBPGT W WP p pw (PpU W WP p) Vf) B
      (asW Unit (WrBP W p pw (simWorldB _ L p.leaves Sm i₀)))
      (iniBP W p pw _ (none, Table.empty _)) (zetaBGen L p M hb) := by
  intro i α A t n hA hP
  refine le_trans
    (tv_triangle _
      ((interact (asW Unit (WrBP W p pw (LifeB _ L p.leaves i))) A
        (iniBP W p pw _ (none, Table.empty _))).map Prod.fst) _)
    (add_le_add
      (realToWrBPUTOf W WP p pw Vf i h.wired h.cohB hF hW hG hWP B hB hh _
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

/-- Index privacy for batches of at most B requests, with the simulator `simBPGr`. -/
theorem privacyPubGrWithUOf [Inhabited V] (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
    (pw : IVK lam L → WKey lam L → V) (Vf : V → X → Prf lam L → TypedOracleComputation lam W.K L Bool)
    (Ryes Rno : I → X → Prop) (M : LH.Nums) (h : L.PropsNoAcc Ryes Rno M) (hW : W.OKG)
    (hG : GrFitPB W) (hWP : WP.OK) (hF : L.onlineBatch.ann.Fmt) (hBu : Budget p M) (Sm : Sims L)
    (hS : Sm.Good Ryes M.zT M.zL M.zO) (i₀ : I) (B : ℕ) (hB : B ≤ L.maxBatchSize)
    {hb : ℕ → ℕ → ℝ≥0∞} (hh : HopU W p B hb) :
    Gen.HasIndexPrivacyWith (relPair Ryes Rno h.sub) (argBPG W WP p pw (PpU W WP p) Vf) B
      (simBPGr W p pw Sm i₀) (zetaBGen L p M hb) := by
  refine GlueB.gluePrivacyWith _ _ _ _ Unit _ _ _ _ _ _
    ((WrBP W p pw (simWorldB _ L p.leaves Sm i₀)).pre (ghost W))
    (iniBP W p pw _ (none, Table.empty _)) _
    (Rom.viaConsistent _ _ _ _ _ (ghostPerm I X lam L W) _ (consistent_wrapBP _)) ?_
  rw [argBPG_via W WP p pw (PpU W WP p) Vf hW (routedF_PpU W WP p hW)]
  exact GlueB.closeVia _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ghostPerm I X lam L W)
    (closePubUTOf W WP p pw Vf Ryes Rno M h hW hG hWP hF hBu Sm hS i₀ B hB hh)

/-- the same as `privacyPubGrWithUOf` for the scheme with the Links in the verification key -/
theorem privacyKEGrWithBOf (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (Ryes Rno : I → X → Prop)
    (M : LH.Nums) (h : L.PropsNoAcc Ryes Rno M) (hW : W.OKG) (hG : GrFitPB W) (hWP : WP.OK)
    (hF : L.onlineBatch.ann.Fmt) (hBu : Budget p M) (Sm : Sims L) (hS : Sm.Good Ryes M.zT M.zL M.zO)
    (i₀ : I) (B : ℕ) (hB : B ≤ L.maxBatchSize) {hb : ℕ → ℕ → ℝ≥0∞} (hh : HopU W p B hb) :
    Gen.HasIndexPrivacyWith (relPair Ryes Rno h.sub) (argBKE W WP p) B
      (simBKGr W p Sm i₀) (zetaBGen L p M hb) :=
  GenMap.privacyWith (via_KE W WP p)
    _ (privacyPubGrWithUOf W WP p _ _ Ryes Rno M h hW hG hWP hF hBu Sm hS i₀ B hB hh)

/-- The compiler theorem with proof-of-work bits, Links in the verification key, no query for an
empty slot, for batches of at most B ≤ N requests, generic in the hop's bound. It concludes
`Gen.IsZKCPArgWith` (ZKCP/Gen.lean; its fields: `completeness`, `indexBinding`, `indexPrivacy`) of
`argBKE W WP p`, for the relations `relPair Ryes Rno h.sub` and the bound B, with `extractorBK W`,
`simBKGr W p Sm i₀` and the errors `alphaBG W M`, `epsB W M`, `zetaBGen L p M hb`. (not all
hypotheses are named here: see the statement below) -/
theorem mainBatchKEGrWithBOf (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
    (Ryes Rno : I → X → Prop) (M : LH.Nums) (h : L.PropsNoAcc Ryes Rno M) (hW : W.OKG)
    (hG : GrFitB W Ryes) (hWP : WP.OK) (hF : L.onlineBatch.ann.Fmt) (hBu : Budget p M)
    (Sm : Sims L) (hS : Sm.Good Ryes M.zT M.zL M.zO) (i₀ : I) (B : ℕ) (hB : B ≤ L.maxBatchSize)
    {hb : ℕ → ℕ → ℝ≥0∞} (hh : HopU W p B hb) :
    Gen.IsZKCPArgWith (relPair Ryes Rno h.sub) (argBKE W WP p) B (extractorBK W) (simBKGr W p Sm i₀)
      (alphaBG W M) (epsB W M) (zetaBGen L p M hb) :=
  ⟨fun i b hb' =>
      completeKE_of W WP p _ _ (completeBatchUGr I X lam L W WP p Ryes Rno M h hW hG hWP hF)
        i b ⟨hb'.1.trans hB, hb'.2⟩,
    bindingKEGr W WP p Ryes Rno M h hW,
    privacyKEGrWithBOf W WP p Ryes Rno M h hW hG.toP hWP hF hBu Sm hS i₀ B hB hh⟩

end Compile.Batch
