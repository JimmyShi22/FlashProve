-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/PubLump.lean: the last game hop for batches, with a function of the key published at
the setup: the challenger that rejects a batch on a copy which has served s1 batches (`chalLSBP`,
Compile/Batch/PubChall.lean) is, under the hypotheses of `lumpBP` and in the distribution of the
output, the wrapped lifetime experiment (`WrBP`, Compile/Batch/PubWr.lean: the reduction of that
file, the "wrapper", around the lifetime experiment) (words of this library: lean/GLOSSARY.md).
  `lumpBP`    `chalLSBP.world` = `asW (WrBP (LifeB i))` in the distribution of the output, for an
              adversary all of whose batches have at most maxBatchSize requests; among the hypotheses:
              `Spec.eqSetupB` and `Spec.eqBatchB` (Compile/Batch/SpecEq.lean; proved in
              Compile/Batch/EqSetup.lean, Compile/Batch/EqBatch.lean from `Spec.eqProveB`, which
              Compile/Batch/EqProve.lean proves). The rounds may have proof-of-work bits (`W.OKG`,
              `GrFitPB W`)
Why the setup goes through: `Spec.eqSetupB` is, under its hypotheses, an equality of the joint
distributions of (ivk, index, `keyOf` of the key, encoding randomness of the copies, state of the
experiment). On the left the published value is pw ivk (keyOf isk), on the right pw ivk key with the
wrapper's own key: the same function of the same components.
Notation:
  "lump" in the names: `interact_lump_adm` (Compile/Batch/Lump.lean): a map Φ of states that
    commutes with all answers and with all allowed calls, on an invariant that these preserve,
    preserves the distribution of output and state, from a state that has the invariant, for an
    adversary that makes allowed calls only; here Φ is `PhiBP`
  `w`: an `LW W`, that is `LSt (spec lam W.K L)` (Compile/Batch/Lump.lean); `N₀`, `t₀`: number N₀ of
    tokens of the setup, number t₀ of tokens so far (`LeafGame.sess`, Compile/Batch/OverrunGen.lean)
  the hypotheses' names: `L.Wired`, `RoundSplits.Coherent` (Iop/Batch.lean), `RoundSplits.Fmt`
    (Iop/BatchFmt.lean), `W.OKG` (Iop/BatchWire.lean), `GrFitPB` (Compile/Batch/SpecFit.lean),
    `WP.OK` (Iop/BatchWireP.lean)
-/
import Compile.Batch.Lump
import Compile.Batch.PubWr

noncomputable section

namespace Compile.Batch
open Iop Rom Prob
open Compile.GlueB (GCall SCall GAdm asW ownPf)
open Compile.BatchLife (LifeOutB LifeInB BRet LifeB linksGB placeB bsess vec)
open Compile.Lifetime (Sess sess)
open Compile.DefC (virtL)

open LTools

variable {I X V : Type} {lam : ℕ} {L : BatchProtocol I X}

/-! ## The replies of the challenger that rejects, written out -/

section RepliesLS

variable (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (pw : IVK lam L → WKey lam L → V) (i : I)

theorem reply_setup_LSBP (w : LW W) :
    (chalLSBP W WP p pw i).world.reply (none, w) .setup =
      ((CpL W WP p i).run w).map fun y =>
        (.inl (pw y.1.1 (keyOf y.1.2)),
          (some (y.1.2, y.2.vals.length, fun _ => 0), dummy y.2)) := by
  rw [lreply_of_step (C := chalLSBP W WP p pw i) (s := none) (c := .setup)
        (Q := (CpL W WP p i).bind fun o =>
            LStep.fresh 0 fun t =>
              LStep.pure (.inl (pw o.1 (keyOf o.2)), some (o.2, t, fun _ => 0)))
        rfl w,
    DefC.run_bind, PMF.map_bind]
  simp only [lrun_fresh0]
  simp only [LStep.run, PMF.pure_map]
  rfl

theorem step_none_LSBP (k : IskH lam L) (N₀ : ℕ) (c : ℕ → ℕ)
    (b : ZKCP.Gen.Batch X Unit) (h : hasOwn b = false) :
    (chalLSBP W WP p pw i).step (some (k, N₀, c)) (.batch b) =
      LStep.pure (.inr [], some (k, N₀, c)) := by
  show (if hasOwn b then _ else _) = _
  rw [h]
  rfl

theorem reply_own_LSBP (k : IskH lam L) (N₀ : ℕ) (c : ℕ → ℕ) (w : LW W)
    (b : ZKCP.Gen.Batch X Unit) (h : hasOwn b = true) :
    (chalLSBP W WP p pw i).world.reply (some (k, N₀, c), w) (.batch b) =
      (PMF.uniformOfFintype (Fin (p.M + 1))).bind fun j =>
          if c j.val < p.s1 then
            ((virtL N₀ (w.vals.length + 1 - N₀) (PpLJ W WP p k (ownFlag b) (reqs b) j)).run
                (dummy w)).map fun z =>
              (replyOfP V b z.1, (some (k, N₀, Function.update c j.val (c j.val + 1)), z.2))
          else PMF.pure (.inr [], (some (k, N₀, c), dummy w)) := by
  have hstep : (chalLSBP W WP p pw i).step (some (k, N₀, c)) (.batch b) = LStep.fresh 0 fun t₀ => LStep.sample p.M fun j =>
      if c j.val < p.s1 then
        (virtL N₀ (t₀ + 1 - N₀) (PpLJ W WP p k (ownFlag b) (reqs b) j)).bind fun πs =>
          LStep.pure (replyOfP V b πs, some (k, N₀, Function.update c j.val (c j.val + 1)))
      else LStep.pure (.inr [], some (k, N₀, c)) := by
    show (if hasOwn b then _ else _) = _
    rw [h, if_pos rfl]
  refine (lreply_of_step hstep w).trans ((congrArg (PMF.map _) (lrun_fresh0 _ w)).trans ?_)
  refine (PMF.map_bind _ _ _).trans (congrArg _ (funext fun j => ?_))
  by_cases hj : c j.val < p.s1
  · simp only [if_pos hj]
    refine (congrArg (PMF.map _) (DefC.run_bind _ _ _)).trans ((PMF.map_bind _ _ _).trans ?_)
    simp only [LStep.run, PMF.pure_map]
    rfl
  · simp only [if_neg hj]
    exact PMF.pure_map _ _

end RepliesLS

/-! ## The replies of the wrapped experiment, written out -/

section RepliesWr

variable {W : QueryLayout lam L} {p : Params} (pw : IVK lam L → WKey lam L → V)
variable (cpW : Sess L.offline → List (Sess L.link) → Lp lam W.K L (IVK lam L × WKey lam L))
  (ppW : WKey lam L → List X → ℕ → BRet L → Lp lam W.K L (List (Prf lam L)))
  (G : World (spec lam W.K L) (LifeOutB X) (LifeInB L))

/-- how a run of a program of the wrapper becomes a move of the wrapped experiment -/
abbrev flatBP {β : Type} (x : (β × WτB W) × G.σ) : β × (WτB W × G.σ) := (x.1.1, (x.1.2, x.2))

theorem interact_repSetupB_inlP
    (w : LW W) (s : WτB W) (sT : Sess L.offline) (ls : List (Sess L.link)) (g : G.σ) :
    (interact G (repSetupBP W pw cpW w s (.inl (sT, ls))) g).map (flatBP G) =
      ((cpW sT ls).run w).map fun y =>
        (.inl (pw y.1.1 y.1.2), ((some (y.1.2, y.2.vals.length, fun _ => 0), dummy y.2), g)) := by
  rw [repSetupBP, interact_bind, interact_toAdv, DefC.run_bind, PMF.bind_map, PMF.map_bind]
  simp only [lrun_fresh0]
  simp only [LStep.run, PMF.bind_bind, PMF.pure_bind, Function.comp_def, interact, PMF.pure_map]
  rfl

theorem interact_repBatch_someP (key : WKey lam L) (N₀ : ℕ) (c : ℕ → ℕ) (xs : List X) (t₀ : ℕ)
    (j : Fin (p.M + 1)) (w : LW W) (ret : BRet L) (g : G.σ) :
    (interact G (repBatchP W p ppW V key N₀ c xs t₀ j w (.inr (some ret))) g).map (flatBP G) =
      ((virtL N₀ (t₀ + 1 - N₀) (ppW key xs j.val ret)).run w).map fun z =>
          (.inr z.1, ((some (key, N₀, Function.update c j.val (c j.val + 1)), z.2), g)) := by
  rw [repBatchP, interact_bind, interact_toAdv, PMF.bind_map, PMF.map_bind]
  simp only [Function.comp_def, interact, PMF.pure_map]
  rfl

theorem interact_repBatch_noneP (key : WKey lam L) (N₀ : ℕ) (c : ℕ → ℕ) (xs : List X) (t₀ : ℕ)
    (j : Fin (p.M + 1)) (w : LW W) (g : G.σ) :
    (interact G (repBatchP W p ppW V key N₀ c xs t₀ j w (.inr none)) g).map (flatBP G) =
      PMF.pure (.inr (xs.map fun _ => ⟨j.val, default, none, none⟩),
          ((some (key, N₀, Function.update c j.val (c j.val + 1)), w), g)) :=
  PMF.pure_map _ _

theorem reply_wrapG_setupP (w : LW W) (g : G.σ) :
    ((wrapGP W p pw cpW ppW).world G).reply ((none, w), g) .setup =
      (G.reply g (.inl ())).bind fun pr =>
        (interact G (repSetupBP W pw cpW w (none, w) pr.1) pr.2).map (flatBP G) := by
  show (interact G (.call (.inl ()) (repSetupBP W pw cpW w (none, w))) g).map _ = _
  simp only [interact, PMF.map_bind]
  rfl

theorem reply_wrapG_haltP {s : WτB W} {c : GCall X Unit} {a : BInP V lam L}
    (h : (wrapGP W p pw cpW ppW).rep s c = .halt (a, s)) (g : G.σ) :
    ((wrapGP W p pw cpW ppW).world G).reply (s, g) c = PMF.pure (a, (s, g)) := by
  show (interact G ((wrapGP W p pw cpW ppW).rep s c) g).map _ = _
  rw [h]
  exact PMF.pure_map _ _

theorem rep_wrapG_noneP (key : WKey lam L) (N₀ : ℕ) (c : ℕ → ℕ) (w : LW W)
    (b : ZKCP.Gen.Batch X Unit) (h : b.ownX.isEmpty = true) :
    (wrapGP W p pw cpW ppW).rep (some (key, N₀, c), w) (.batch b) =
      .halt (.inr [], (some (key, N₀, c), w)) := by
  show (if b.ownX.isEmpty then _ else _) = _
  rw [h, if_pos rfl]
  rfl

theorem reply_wrapG_ownP (key : WKey lam L) (N₀ : ℕ) (c : ℕ → ℕ) (w : LW W) (g : G.σ)
    (b : ZKCP.Gen.Batch X Unit) (h : b.ownX.isEmpty = false) :
    ((wrapGP W p pw cpW ppW).world G).reply ((some (key, N₀, c), w), g) (.batch b) =
      (PMF.uniformOfFintype (Fin (p.M + 1))).bind fun j =>
          if c j.val < p.s1 then
            (G.reply g (.inr (j.val, b.ownX))).bind fun pr =>
              (interact G (repBatchP W p ppW V key N₀ c b.ownX w.vals.length j (dummy w) pr.1)
                pr.2).map (flatBP G)
          else PMF.pure (.inr [], ((some (key, N₀, c), dummy w), g)) := by
  have hrep : (wrapGP W p pw cpW ppW).rep (some (key, N₀, c), w) (.batch b) =
      ((LStep.fresh 0 fun t₀ =>
          LStep.sample p.M fun j => LStep.pure (t₀, j) : Lp lam W.K L (ℕ × Fin (p.M + 1))).toAdv
        w).bind fun y =>
          if c y.1.2.val < p.s1 then
            .call (.inr (y.1.2.val, b.ownX)) (repBatchP W p ppW V key N₀ c b.ownX y.1.1 y.1.2 y.2)
          else .halt (.inr [], (some (key, N₀, c), y.2)) := by
    show (if b.ownX.isEmpty then _ else _) = _
    rw [h]
    rfl
  have e : ((wrapGP W p pw cpW ppW).world G).reply ((some (key, N₀, c), w), g) (.batch b)
      = (interact G (((LStep.fresh 0 fun t₀ => LStep.sample p.M fun j => LStep.pure (t₀, j) :
          Lp lam W.K L (ℕ × Fin (p.M + 1))).toAdv w).bind fun y =>
            (if c y.1.2.val < p.s1 then
              .call (.inr (y.1.2.val, b.ownX)) (repBatchP W p ppW V key N₀ c b.ownX y.1.1 y.1.2 y.2)
            else .halt (.inr [], (some (key, N₀, c), y.2)) : Adv (spec lam W.K L) (LifeOutB X) (LifeInB L) (BInP V lam L × WτB W))) g).map (flatBP G) :=
    congrArg (fun Q : Adv (spec lam W.K L) (LifeOutB X) (LifeInB L) (BInP V lam L × WτB W) =>
      (interact G Q g).map (flatBP G)) hrep
  rw [e, interact_bind, interact_toAdv, lrun_fresh0, PMF.bind_map, PMF.map_bind]
  simp only [LStep.run, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
  refine congrArg _ (funext fun j => ?_)
  by_cases hj : c j.val < p.s1
  · simp only [if_pos hj, interact, PMF.map_bind]
  · simp only [if_neg hj, interact, PMF.pure_map]

end RepliesWr

/-! ## Batches and their own requests -/

theorem replyOfP_const (b : ZKCP.Gen.Batch X Unit) (π₀ : Prf lam L) :
    replyOfP V b ((reqs b).map fun _ => π₀) = .inr (b.ownX.map fun _ => π₀) :=
  congrArg (toP V) (replyOf_const b π₀)

/-! ## The last game hop -/

section Lump

variable (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (pw : IVK lam L → WKey lam L → V) (i : I)

/-- the wrapped experiment, taking the calls of the real experiment -/
abbrev TheWrGP : World (spec lam W.K L) (GCall X Unit) (BInP V lam L) :=
  (wrapGP W p pw (fun sT ls => CpW W p sT (ls.take (p.M + 1))) (PpW W p)).world (TheLifeB W p i)

theorem asW_WrBP : asW Unit (WrBP W p pw (TheLifeB W p i)) = TheWrGP W p pw i := rfl

/-- From the states of the challenger that rejects to those of the wrapped lifetime experiment: the
wrapper holds the trees and Link's proof strings, the experiment the encoding randomness of the
copies. The index and the randomness of the first encoding are forgotten. -/
def PhiBP (s : (chalLSBP W WP p pw i).world.σ) : (TheWrGP W p pw i).σ :=
  ((s.1.map fun z => (keyOf z.1, z.2.1, z.2.2), s.2),
    (s.1.map fun z => z.1.leaves.map fun lf => lf.node.r, Table.empty _))

/-- the setup (hypotheses below) -/
theorem lumpB_setupP (hS : Spec.eqSetupB) (hL : L.Wired) (hW : W.OKG) (hG : GrFitPB W)
    (hWP : WP.OK) (w : LW W) :
    ((chalLSBP W WP p pw i).world.reply (none, w) .setup).map (Prod.map id (PhiBP W WP p pw i)) =
      (TheWrGP W p pw i).reply ((none, w), (none, Table.empty _)) .setup := by
  have hR : (TheWrGP W p pw i).reply ((none, w), (none, Table.empty _)) .setup
      = (unif L.EncodingRandomness).bind fun r₀ => (sess L.honestOfflineProver (i, r₀) ()).bind fun sT =>
          (linksGB (fun r r' => sess L.honestLinkProver (i, r, r') ()) r₀ (p.M + 1)).bind fun ls =>
            ((CpW W p sT (ls.map Prod.snd)).run w).map fun y =>
              (.inl (pw y.1.1 y.1.2),
                ((some (y.1.2, y.2.vals.length, fun _ => 0), dummy y.2),
                  (some (ls.map Prod.fst), Table.empty _))) := by
    rw [reply_wrapG_setupP, reply_LifeB_setup]
    refine (PMF.bind_bind _ _ _).trans
      (congrArg _
        (funext fun r₀ =>
          (PMF.bind_bind _ _ _).trans
            (congrArg _
              (funext fun sT =>
                (PMF.bind_map _ _ _).trans (bind_congr_support _ fun ls hls => ?_)))))
    show (interact (TheLifeB W p i)
          (repSetupBP W pw (fun sT ls => CpW W p sT (ls.take (p.M + 1))) w
            (none, w) (.inl (sT, ls.map Prod.snd)))
          (some (ls.map Prod.fst), Table.empty _)).map
        (flatBP (TheLifeB W p i)) = _
    rw [interact_repSetupB_inlP,
      List.take_of_length_le (by rw [List.length_map, length_linksGB _ r₀ _ ls hls])]
    rfl
  rw [hR]
  refine (congrArg (PMF.map _) (reply_setup_LSBP W WP p pw i w)).trans
    ((PMF.map_comp _ _ _).trans ?_)
  have h1 := congrArg
    (fun μ =>
      μ.map fun a : (IVK lam L × I × WKey lam L × List L.EncodingRandomness) × LW W =>
        ((.inl (pw a.1.1 a.1.2.2.1),
          ((some (a.1.2.2.1, a.2.vals.length, fun _ => 0), dummy a.2),
            (some a.1.2.2.2, Table.empty _))) :
          BInP V lam L × (WτB W × (Option (List L.EncodingRandomness) × Table (spec lam W.K L)))))
    (hS I X lam L W WP p i w hL hW hG hWP)
  simp only [PMF.map_comp, PMF.map_bind] at h1
  exact h1

/-- a batch with an own request -/
theorem lumpB_ownP (hE : Spec.eqBatchB) (hL : L.Wired) (hC : L.onlineBatch.ann.Coherent)
    (hF : L.onlineBatch.ann.Fmt) (hW : W.OKG) (hG : GrFitPB W) (hWP : WP.OK) (k : IskH lam L)
    (hk : k.i = i) (N₀ : ℕ) (c : ℕ → ℕ) (w : LW W) (b : ZKCP.Gen.Batch X Unit)
    (hb : hasOwn b = true) (hlen : b.pairs.length ≤ L.maxBatchSize) :
    ((chalLSBP W WP p pw i).world.reply (some (k, N₀, c), w) (.batch b)).map
        (Prod.map id (PhiBP W WP p pw i)) =
      (TheWrGP W p pw i).reply
        ((some (keyOf k, N₀, c), w), (some (k.leaves.map fun lf => lf.node.r), Table.empty _))
        (.batch b) := by
  rw [reply_wrapG_ownP _ _ _ _ _ _ _ _ _ b (by rw [isEmpty_ownX, hb]; rfl)]
  refine (congrArg (PMF.map _) (reply_own_LSBP W WP p pw i k N₀ c w b hb)).trans
    ((PMF.map_bind _ _ _).trans (congrArg _ (funext fun j => ?_)))
  by_cases hj : c j.val < p.s1
  · simp only [if_pos hj]
    cases hl : k.leaves[j.val]? with
    | none =>
      have h1 : (k.leaves.map fun lf => lf.node.r)[j.val]? = none := by
        rw [List.getElem?_map, hl]; rfl
      rw [reply_LifeB_none W p i _ _ _ _ h1, run_PpLJ_none W WP p _ _ k _ _ j hl]
      refine Eq.trans ?_ (PMF.pure_bind _ _).symm
      refine (PMF.map_comp _ _ _).trans ((PMF.pure_map _ _).trans ?_)
      refine Eq.trans ?_
        (interact_repBatch_noneP (PpW W p) (TheLifeB W p i) (keyOf k)
          N₀ c b.ownX w.vals.length j (dummy w) _).symm
      show PMF.pure (replyOfP V b ((reqs b).map fun _ => ⟨j.val, default, none, none⟩), _) = _
      rw [replyOfP_const]
      rfl
    | some lf =>
      have h1 : (k.leaves.map fun lf => lf.node.r)[j.val]? = some lf.node.r := by
        rw [List.getElem?_map, hl]; rfl
      have h2 := hE I X lam L W WP p N₀ (w.vals.length + 1 - N₀) k b j lf (dummy w)
        hL hC hF hW hG hWP hl hb hlen
      rw [hk] at h2
      rw [reply_LifeB_some W p i _ _ _ _ _ h1]
      refine Eq.trans ?_ (PMF.bind_map _ _ _).symm
      refine (PMF.map_comp _ _ _).trans ?_
      have h3 := congrArg (fun μ => μ.map fun a : BIn lam L × LW W =>
        ((toP V a.1, ((some (keyOf k, N₀, Function.update c j.val (c j.val + 1)), a.2),
          (some (k.leaves.map fun lf => lf.node.r), Table.empty _))) :
          BInP V lam L × (WτB W × (Option (List L.EncodingRandomness) × Table (spec lam W.K L))))) h2
      simp only [PMF.map_comp, PMF.map_bind] at h3
      refine Eq.trans h3 (congrArg _ (funext fun ret => ?_))
      show _ = (interact (TheLifeB W p i)
            (repBatchP W p (PpW W p) V (keyOf k) N₀ c b.ownX w.vals.length j
              (dummy w) (.inr (some ret)))
            (some (k.leaves.map fun lf => lf.node.r), Table.empty _)).map
          (flatBP (TheLifeB W p i))
      rw [interact_repBatch_someP]
      rfl
  · simp only [if_neg hj]
    exact PMF.pure_map _ _

end Lump

section Final

variable (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (pw : IVK lam L → WKey lam L → V) (i : I)

/-- An admissible adversary whose batches have at most maxBatchSize requests makes such calls only. -/
theorem allCalls_of_gAdmP {S : OSpec} {α : Type} (ok : ZKCP.Gen.Batch X Unit → Prop)
    (hok : ∀ b, ok b → b.pairs.length ≤ L.maxBatchSize) (A : Adv S (GCall X Unit) (BInP V lam L) α) :
    ∀ (b : Bool) (n : ℕ), GAdm ok A b n → AllCalls (okcB L) A := by
  induction A with
  | halt a => exact fun _ _ _ => trivial
  | sample m k ih => exact fun b n h r => ih r b n (h r)
  | query o q k ih => exact fun b n h r => ih r b n (h r)
  | call m k ih =>
    intro b n h
    rcases m with _ | bt
    · simp only [GAdm] at h
      exact ⟨trivial, fun a => ih a true n (h.2 a)⟩
    · cases n with
      | zero => exact h.elim
      | succ n =>
        simp only [GAdm] at h
        exact ⟨hok bt h.2.1, fun a => ih a b n (h.2.2 a)⟩

theorem lumpB_pureP (so : Option (IskH lam L × ℕ × (ℕ → ℕ))) (w : LW W) (c : GCall X Unit)
    (h₁ : (chalLSBP W WP p pw i).step so c = LStep.pure (.inr [], so))
    (h₂ : (wrapGP W p pw (fun sT ls => CpW W p sT (ls.take (p.M + 1))) (PpW W p)).rep
        (so.map fun z => (keyOf z.1, z.2.1, z.2.2), w) c =
      .halt (.inr [], (so.map fun z => (keyOf z.1, z.2.1, z.2.2), w))) :
    ((chalLSBP W WP p pw i).world.reply (so, w) c).map (Prod.map id (PhiBP W WP p pw i)) =
      (TheWrGP W p pw i).reply (PhiBP W WP p pw i (so, w)) c :=
  ((congrArg (PMF.map _) (lreply_pure h₁ w)).trans (PMF.pure_map _ _)).trans
    (reply_wrapG_haltP _ _ _ _ h₂ _).symm

theorem lumpB_answerP (so : Option (IskH lam L × ℕ × (ℕ → ℕ))) (w : LW W)
    (o : OracleName) (q : domOf lam L o) :
    ((chalLSBP W WP p pw i).world.answer (so, w) o q).map (Prod.map id (PhiBP W WP p pw i)) =
      (TheWrGP W p pw i).answer (PhiBP W WP p pw i (so, w)) o q := by
  have h := answer_wrapBP (p := p) (pw := pw) (cpW := fun sT ls => CpW W p sT (ls.take (p.M + 1)))
    (ppW := PpW W p) (TheLifeB W p i) (so.map fun z => (keyOf z.1, z.2.1, z.2.2), w)
    (so.map fun z => z.1.leaves.map fun lf => lf.node.r, Table.empty _) o q
  exact (PMF.map_comp _ _ _).trans h.symm

/-- Under the hypotheses below: the challenger that rejects a batch on a copy which has served s1
batches is, in the distribution of the output, the wrapped lifetime experiment, for an adversary all
of whose batches have at most maxBatchSize requests. -/
theorem lumpBP (hS : Spec.eqSetupB) (hE : Spec.eqBatchB) (hL : L.Wired) (hC : L.onlineBatch.ann.Coherent)
    (hF : L.onlineBatch.ann.Fmt) (hW : W.OKG) (hG : GrFitPB W) (hWP : WP.OK) {α : Type}
    (A : Adv (spec lam W.K L) (GCall X Unit) (BInP V lam L) α) (hA : AllCalls (okcB L) A) :
    (interact (chalLSBP W WP p pw i).world A (none, LSt.init _)).map Prod.fst =
      (interact (asW Unit (WrBP W p pw (LifeB _ L p.leaves i))) A
          (iniBP W p pw _ (none, Table.empty _))).map Prod.fst := by
  have h := interact_lump_adm (chalLSBP W WP p pw i).world (TheWrGP W p pw i)
    (PhiBP W WP p pw i) (fun s => ∀ z, s.1 = some z → z.1.i = i) (okcB L) ?_ ?_ ?_ ?_ A hA
    (none, LSt.init _) (fun z hz => absurd hz (by simp))
  · have h2 := congrArg (PMF.map Prod.fst) h
    rw [PMF.map_comp] at h2
    exact h2
  · rintro ⟨so, w⟩ o q -
    exact lumpB_answerP W WP p pw i so w o q
  · rintro ⟨so, w⟩ m hI hm
    rcases m with _ | b
    · cases so with
      | none => exact lumpB_setupP W WP p pw i hS hL hW hG hWP w
      | some z => exact lumpB_pureP W WP p pw i (some z) w .setup rfl rfl
    · cases so with
      | none => exact lumpB_pureP W WP p pw i none w (.batch b) rfl rfl
      | some z =>
        obtain ⟨k, N₀, c⟩ := z
        cases hb : hasOwn b
        · exact lumpB_pureP W WP p pw i (some (k, N₀, c)) w (.batch b)
            (step_none_LSBP W WP p pw i k N₀ c b hb)
            (rep_wrapG_noneP _ _ _ _ _ _ _ b (by rw [isEmpty_ownX, hb]; rfl))
        · exact lumpB_ownP W WP p pw i hE hL hC hF hW hG hWP k (hI _ rfl) N₀ c w b hb hm
  · rintro ⟨so, w⟩ o q hI x hx
    obtain ⟨a, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hx
    exact hI
  · rintro ⟨so, w⟩ m hI - x hx
    rcases m with _ | b
    · cases so with
      | none =>
        rw [reply_setup_LSBP] at hx
        obtain ⟨y, hy, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hx
        intro z hz
        have hz' : (y.1.2, y.2.vals.length, fun _ => 0) = z := Option.some.inj hz
        rw [← hz']
        exact index_of_mem_run_CpL W WP p i w y hy
      | some z =>
        rw [lreply_pure (C := chalLSBP W WP p pw i) (s := some z) (c := .setup)
            (a := .inr []) rfl] at hx
        rw [(PMF.mem_support_pure_iff _ _).1 hx]
        exact hI
    · cases so with
      | none =>
        rw [lreply_pure (C := chalLSBP W WP p pw i) (s := none) (c := .batch b)
            (a := .inr []) rfl] at hx
        rw [(PMF.mem_support_pure_iff _ _).1 hx]
        exact hI
      | some z =>
        obtain ⟨k, N₀, c⟩ := z
        have hk : k.i = i := hI _ rfl
        cases hb : hasOwn b
        · rw [lreply_pure (step_none_LSBP W WP p pw i k N₀ c b hb)] at hx
          rw [(PMF.mem_support_pure_iff _ _).1 hx]
          exact hI
        · rw [reply_own_LSBP W WP p pw i k N₀ c w b hb] at hx
          obtain ⟨j, -, hx⟩ := (PMF.mem_support_bind_iff _ _ _).1 hx
          by_cases hj : c j.val < p.s1
          · rw [if_pos hj] at hx
            obtain ⟨u, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hx
            intro z hz
            rw [← Option.some.inj hz]
            exact hk
          · rw [if_neg hj] at hx
            rw [(PMF.mem_support_pure_iff _ _).1 hx]
            exact hI

end Final

end Compile.Batch
