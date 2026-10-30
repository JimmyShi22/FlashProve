-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LateWorld/Steps.lean: AFTER A GOOD SETUP, THE REDUCTION AROUND THE GAME's REAL SIDE IS THE
HONEST SIDE THAT LAYS LATE AND COUNTS: a map of states that commutes with oracle queries and with
batches, under an invariant that these moves keep.

This file states no goal of the release: one step of the proof of Spec.lateToWrap
(Johnson/LateWorld/SpecWrap.lean).

The two challengers: wrapG, the reduction wrapW (Johnson/WholeKey/Wrap.lean) around the real game
(Hiop/Seeded/Game.lean) at the letters of the statement, with the calls of the real experiment; and
lateC (Johnson/LateWorld/Count.lean).

The map of states (toC). The reduction keeps each copy's tree with fillings for bodies, and its
out-of-domain sample; the game keeps each table's encoding randomness and seed, and counts. The
honest side's key is read off both: the tree with the bodies of the encoded index put in (realTree,
Johnson/LateWorld/SpecTables.lean). The counter of the place j is the game's count of sessions on
the table number j + 1. What else the game keeps is forgotten.

The invariant (InvG): the setup has been made and no table was refused; there are M + 1 copies, and
the game has at least as many further tables; each copy's out-of-domain sample is that of the index
at the game's randomness and seed.

A batch of one own request: both draw the prover's coins. The reduction does not use the strategy's
coins; the game draws its own, uniformly, which is the law of the enumeration's draw. Then the
session lemma (Spec.session, Johnson/LateWorld/SpecSession.lean) at the session's letters.

Main names (namespace OnBytes.LateWorld).
  gameG, wrapG     the two worlds' letters. StH, StGm, StWG: their states' types.
  realCopies, toC, InvG   (realCopies_get: the copy at a place.)
  repG, runG, repW, ansW   the two worlds' moves, with the states' types written out (runG_bind,
                   runG_halt, runG_call, runG_lazy, runG_defer, runG_pass2A, repW_batch, repW_setup:
                   unfoldings).
  game_sess, game_sess_no   the game's reply to a call for a session, served and refused.
  sess_branch      the session lemma at the session's letters (dec_iff, coVB, coVB_eq beside it).
  sessA', proveStepA_one, sessA_served, sessA_refused   the reduction's batch of one request,
    unfolded.
The step itself is in Johnson/LateWorld/Batch.lean.

Limits. It says nothing of the setup. The map of states, the invariant and the moves named anew are
devices of the proof and stand in no statement on the scheme. proveStepA_one holds by unfolding: it
follows the text of proveStepA (Johnson/WholeKey/Wrap.lean) to the letter.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LateWorld.Count
import Johnson.LateWorld.Session
import Johnson.LateWorld.SpecWrap
import Johnson.LateWorld.SpecTables
import Compile.DeferRun.Lump

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.LateWorld
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey OnBytes.Dry OnBytes.WrapLaws
open _root_.Compile.GlueB (GCall GIn GAdm asW)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (a : AtRecs lam L Bd aT aL) (Gs : L.OutOfDomainSeed → Prop)
  (s1 : ℕ) (i : I)

/-! ## The letters -/

/-- The real game at the letters of the statement. -/
abbrev gameG : World (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))
    (Hiop.Seeded.GOut L (kitW W r₀ a.side).form) (Hiop.Seeded.GIn L (kitW W r₀ a.side).form) :=
  Hiop.Seeded.gameReal L (kitW W r₀ a.side) (recsG a) i (boundsW a.side s1) Gs _

/-- The reduction around it, with the calls of the real experiment. -/
abbrev wrapG : World (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (GCall X Unit)
    (GIn (FullKey lam L aT aL) (RequestProof lam L)) :=
  asW Unit ((wrapW W S cA r₀ a.side).world (gameG W r₀ a Gs s1 i))

/-- The state of the game's host: the number of further tables; each table's (randomness, seed). -/
abbrev StH (L : HolographicProtocol I X) : Type := ℕ × (ℕ → L.EncodingRandomness × L.OutOfDomainSeed)

/-- The state of the game: what has been made and asked, with the host's state; its own table of
answers, which nobody asks. -/
abbrev StGm (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) : Type :=
  Option (ℕ × Hiop.UsedR × StH L) × Tb W

/-- The state of wrapG. -/
abbrev StWG (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) : Type := StG W × StGm W

/-! ## The map of states and the invariant -/

/-- The honest side's copies, off the reduction's and the game's (randomness, seed), from the table
number e on. -/
def realCopies (fn : ℕ → L.EncodingRandomness × L.OutOfDomainSeed) :
    ℕ → List (TabW lam L Bd aT aL) → List (TabK lam L Bd aT aL)
  | _, [] => []
  | e, t :: ts =>
      ⟨(fn e).1, realTree W a.b₀ (L.encodeIndex i (fn e).1) t.tree, (fn e).2⟩ :: realCopies fn (e + 1) ts

theorem realCopies_get (fn : ℕ → L.EncodingRandomness × L.OutOfDomainSeed) : ∀ (e : ℕ) (ts : List (TabW lam L Bd aT aL))
    (j : ℕ), (realCopies W a i fn e ts)[j]? = (ts[j]?).map fun t =>
      ⟨(fn (e + j)).1, realTree W a.b₀ (L.encodeIndex i (fn (e + j)).1) t.tree, (fn (e + j)).2⟩
  | _, [], _ => by simp [realCopies]
  | e, t :: ts, 0 => by simp [realCopies]
  | e, t :: ts, j + 1 => by
    rw [realCopies, List.getElem?_cons_succ, List.getElem?_cons_succ,
      realCopies_get fn (e + 1) ts j, show e + 1 + j = e + (j + 1) by omega]

/-- **The map of states.** -/
def toC (s : StWG W) : StC W a.side :=
  match s.1.2, s.2.1 with
  | some ts, some (_, u, st) =>
      ((some ⟨i, realCopies W a i st.2 1 ts⟩, s.1.1), fun j => u.sess (j.val + 1))
  | _, _ => ((none, s.1.1), fun _ => 0)

/-- **The invariant.** -/
def InvG (s : StWG W) : Prop :=
  ∃ (T : Tb W) (ts : List (TabW lam L Bd aT aL)) (c : ℕ) (u : Hiop.UsedR) (st : StH L) (Tg : Tb W),
    s = ((T, some ts), (some (c, u, st), Tg)) ∧ ts.length = a.M + 1 ∧ ts.length ≤ c ∧
      ∀ e t, ts[e]? = some t → t.ood = L.recOf i (st.2 (e + 1)).1 (st.2 (e + 1)).2

/-! ## The two worlds' moves, at the states' own types

The state of a world is a field of a structure, which the tactics do not see through. The moves are
named here once more, with the states' types written out; each is the world's own move by
definition. -/

/-- The game's reply. -/
def repG (g : StGm W) (m : Hiop.Seeded.GOut L (kitW W r₀ a.side).form) :
    PMF (Hiop.Seeded.GIn L (kitW W r₀ a.side).form × StGm W) :=
  (gameG W r₀ a Gs s1 i).reply g m

/-- The run of one of the reduction's programs against the game. -/
def runG {α : Type} (A : AdvG W r₀ a.side α) (g : StGm W) : PMF (α × StGm W) :=
  interact (gameG W r₀ a Gs s1 i) A g

/-- The reply of the reduction around the game. -/
def repW (s : StWG W) (c : GCall X Unit) :
    PMF (GIn (FullKey lam L aT aL) (RequestProof lam L) × StWG W) :=
  (wrapG W S cA r₀ a Gs s1 i).reply s c

/-- Its answer to an oracle query. -/
def ansW (s : StWG W) (o : TypedOracleCompiler.Compile.Batch.OracleName)
    (q : (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)).Dom o) :
    PMF ((typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)).Rng o × StWG W) :=
  (wrapG W S cA r₀ a Gs s1 i).answer s o q

theorem runG_bind {α β : Type} (A : AdvG W r₀ a.side α) (f : α → AdvG W r₀ a.side β)
    (g : StGm W) :
    runG W r₀ a Gs s1 i (A.bind f) g =
      (runG W r₀ a Gs s1 i A g).bind fun x => runG W r₀ a Gs s1 i (f x.1) x.2 :=
  interact_bind (gameG W r₀ a Gs s1 i) A f g

theorem runG_halt {α : Type} (x : α) (g : StGm W) :
    runG W r₀ a Gs s1 i (.halt x) g = PMF.pure (x, g) := rfl

theorem runG_call {α : Type} (m : Hiop.Seeded.GOut L (kitW W r₀ a.side).form)
    (k : Hiop.Seeded.GIn L (kitW W r₀ a.side).form → AdvG W r₀ a.side α) (g : StGm W) :
    runG W r₀ a Gs s1 i (.call m k) g =
      (repG W r₀ a Gs s1 i g m).bind fun p => runG W r₀ a Gs s1 i (k p.1) p.2 := rfl

theorem runG_lazy {α : Type} (c : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) α) (T : Tb W) (g : StGm W) :
    runG W r₀ a Gs s1 i (c.runLazyA T) g = (c.runLazy T).map fun y => (y, g) :=
  interact_runLazyA (gameG W r₀ a Gs s1 i) c T g

theorem runG_defer {α : Type} (mk : Mark (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)))
    (c : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) α) (T : Tb W)
    (lg : Trace (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) (g : StGm W) :
    runG W r₀ a Gs s1 i (c.runDeferA mk T lg) g = (c.runDefer mk T lg).map fun y => (y, g) :=
  interact_runDeferA (gameG W r₀ a Gs s1 i) mk c T lg g

theorem runG_pass2A (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam W.K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body (typedOracleCarrier L Bd aT aL))
    (embP : PlainPart Q.loc.shape Q.ann →
      PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) t) (annOf (typedOracleCarrier L Bd aT aL) t))
    (xin : Y → Option L.XC) (cms : List (Dig lam)) (x : Y)
    (xt : ℕ → TreeK lam (typedOracleCarrier L Bd aT aL)) (cap : ℕ → ℕ)
    (embE : E.Sym → Body (typedOracleCarrier L Bd aT aL)) (v : Option (DView Q.loc))
    (co : Coins lam (typedOracleCarrier L Bd aT aL)) (Rc : Record (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)))
    (T : Tb W) (g : StGm W) :
    runG W r₀ a Gs s1 i (pass2A t Q wq embS embP xin cms x xt cap embE v co Rc T) g =
      (pass2 t Q wq embS embP xin cms x xt cap embE v co Rc T).map fun y => (y, g) :=
  interact_pass2A (gameG W r₀ a Gs s1 i) t Q wq embS embP xin cms x xt cap embE v co Rc T g

theorem repW_batch (s : StWG W) (b : ZKCP.Gen.Batch X Unit) :
    repW W S cA r₀ a Gs s1 i s (.batch b) =
      (runG W r₀ a Gs s1 i (proveStepA W cA r₀ a.side s.1 b.ownX) s.2).map fun z =>
        (z.1.1, (z.1.2, z.2)) := rfl

theorem repW_setup (s : StWG W) :
    repW W S cA r₀ a Gs s1 i s .setup =
      (runG W r₀ a Gs s1 i (setupA W S cA r₀ a.side s.1.1) s.2).map fun z =>
        (z.1.1, (z.1.2, z.2)) := rfl

/-! ## The game's reply to a call for a session -/

theorem game_sess (c : ℕ) (u : Hiop.UsedR) (st : StH L) (Tg : Tb W) (e : ℕ) (x : X) (he : e ≤ c)
    (hu : u.sess e < (boundsW a.side s1).sess e) :
    repG W r₀ a Gs s1 i (some (c, u, st), Tg) (.sess e x ()) =
      (Hiop.Seeded.runAt ((recsG a).B e)
        ((kitW W r₀ a.side).μB e (x, L.recOf i (st.2 e).1 (st.2 e).2)) (kitW W r₀ a.side).ρB
        (i, (st.2 e).1, (st.2 e).2) (x, L.recOf i (st.2 e).1 (st.2 e).2)).map fun v =>
        (.sess x v, (some (c, { u with sess := Hiop.bump u.sess e }, st), Tg)) := by
  show (Hiop.Seeded.gameReply (Hiop.Seeded.realLawsG L (kitW W r₀ a.side) (recsG a) i).host
    (boundsW a.side s1) Gs (some (c, u, st)) (.sess e x ())).map (fun p => (p.1, (p.2, Tg))) = _
  simp only [Hiop.Seeded.gameReply]
  rw [if_pos ⟨he, hu, le_rfl⟩]
  have e1 : (Hiop.Seeded.realLawsG L (kitW W r₀ a.side) (recsG a) i).host.session st e x () =
      (Hiop.Seeded.runAt ((recsG a).B e)
        ((kitW W r₀ a.side).μB e (x, L.recOf i (st.2 e).1 (st.2 e).2)) (kitW W r₀ a.side).ρB
        (i, (st.2 e).1, (st.2 e).2) (x, L.recOf i (st.2 e).1 (st.2 e).2)).map fun v => (v, st) :=
    rfl
  rw [e1]
  exact (PMF.map_comp _ _ _).trans ((PMF.map_comp _ _ _).trans rfl)

theorem game_sess_no (c : ℕ) (u : Hiop.UsedR) (st : StH L) (Tg : Tb W) (e : ℕ) (x : X)
    (hu : ¬ u.sess e < (boundsW a.side s1).sess e) :
    repG W r₀ a Gs s1 i (some (c, u, st), Tg) (.sess e x ()) =
      PMF.pure (.none, (some (c, u, st), Tg)) := by
  show (Hiop.Seeded.gameReply (Hiop.Seeded.realLawsG L (kitW W r₀ a.side) (recsG a) i).host
    (boundsW a.side s1) Gs (some (c, u, st)) (.sess e x ())).map (fun p => (p.1, (p.2, Tg))) = _
  simp only [Hiop.Seeded.gameReply]
  rw [if_neg fun h => hu h.2.1, PMF.pure_map]
  rfl

/-! ## The session lemma at the session's letters -/

/-- from "decide p = true", at whatever instance, to p and back -/
theorem dec_iff {p : Prop} {d : Decidable p} : @decide p d = true ↔ p := @decide_eq_true_iff p d

/-- The coins that the reduction's second pass of a session is handed: with the public starts that
the view's plain parts give; as they were drawn, if there is no view. -/
def coVB (co : Coins lam (typedOracleCarrier L Bd aT aL)) :
    Option (Plains L.onlineBatch.loc.shape) → Coins lam (typedOracleCarrier L Bd aT aL)
  | some pl => a.side.dressB (a.side.pvB pl) co
  | none => co

variable {W S cA a Gs}

/-- **A session of the game, then the reduction's second pass, is the honest session laid late**, on
the copy at the place j of the key's list, whose table the reduction keeps as t and whose
(randomness, seed) the game keeps as (r, sd). -/
theorem sess_branch {ok : I → Prop} {δ : ℝ≥0∞} (hP : PremLate W S cA a ok Gs δ) (hi : ok i)
    (t : TabW lam L Bd aT aL) (r : L.EncodingRandomness)
    (sd : L.OutOfDomainSeed) (j : ℕ) (x : X) (co : Coins lam (typedOracleCarrier L Bd aT aL))
    (hco : co.path.length = W.depthReq) (T : Tb W) :
    ((Hiop.Seeded.runAt ((recsG a).B (j + 1))
        ((kitW W r₀ a.side).μB (j + 1) (x, L.recOf i r sd)) (kitW W r₀ a.side).ρB (i, r, sd)
        (x, L.recOf i r sd)).bind fun v =>
      pass2 Tag.onl L.onlineBatch (wBC W) W.embB id (xinBA r₀) (cmsBA cA t.tree.root (L.recOf i r sd).2)
        (x, L.recOf i r sd) (fun _ => t.tree) a.side.capB W.embE v.2
        (coVB a co (v.2.map DView.plains)) v.1.2 T) =
      (unif a.Hs.B.Coin).bind fun κ =>
        lateBA W cA r₀ (fun _ => realTree W a.b₀ (L.encodeIndex i r) t.tree)
          (a.side.dressB (a.side.rvB κ) co) a.side.capB t.tree.root x (L.recOf i r sd) (L.encodeIndex i r)
          (a.side.st.stopB i r sd x (a.nm j)) (a.side.st.B i r sd x (a.nm j) κ) T := by
  have hext : (sessionAt a.Hs (a.nm j)).ext (i, r, sd) = L.encodeIndex i r := hP.ext.B i r sd (a.nm j)
  have hTab : TabAgree L.onlineBatch (wBC W) W.embE ((sessionAt a.Hs (a.nm j)).ext (i, r, sd))
      (fun _ => realTree W a.b₀ (L.encodeIndex i r) t.tree) (fun _ => t.tree) := by
    rw [hext]
    refine ⟨fun _ => rfl, fun _ _ => rfl, fun p => ?_⟩
    show (committerLeafInput W a.b₀ (L.encodeIndex i r) (fun j => (t.tree.inp j).salt) (W.B.ext.leaf p)).body = _
    rw [(hP.wires.base.extB p).2]
    exact dif_pos p.isLt
  have h := session Tag.onl L.onlineBatch (wBC W) W.embB id (xinBA r₀) []
    (cmsBA cA t.tree.root (L.recOf i r sd).2) (x, L.recOf i r sd)
    (fun _ => realTree W a.b₀ (L.encodeIndex i r) t.tree) (fun _ => t.tree) a.side.capB W.embE
    (sessionAt a.Hs (a.nm j)) (i, r, sd) (a.side.st.stopB i r sd x (a.nm j))
    (blank a.b₀ W.depthReq) (fun κ => a.side.dressB (a.side.rvB κ) co) (coVB a co)
    hP.wires.B.ext (hP.freeB (x, L.recOf i r sd)) (fun _ => dec_iff)
    (fun κ ρ hρ =>
      congrArg (fun v => a.side.dressB v co) (hP.runVals.B i r sd (a.nm j) x κ ρ hi hρ))
    (fun _ => ⟨rfl, rfl, rfl⟩) (fun _ => (List.length_replicate ..).trans hco.symm) hTab T
  rw [hext] at h
  exact h.symm

/-! ## The reduction's batch of one request, unfolded -/

variable (W cA)

/-- What the reduction does behind the prover's coins, by whether it keeps a copy at the drawn
place: the text of proveStepA (Johnson/WholeKey/Wrap.lean). -/
def sessA' (h : HonestSide lam L Bd aT aL) (w : StG W) (x : X)
    (o : DrawP lam L Bd aT aL h.KB × Tb W) : Option (TabW lam L Bd aT aL) →
    AdvG W r₀ h (GIn (FullKey lam L aT aL) (RequestProof lam L) × StG W)
  | none => .halt (.inr [⟨o.1.j, h.nm o.1.j, none⟩], (o.2, w.2))
  | some t =>
    .call (.sess (o.1.j + 1) x ()) fun rp =>
      (match rp with
        | .sess _ u =>
            pass2A Tag.onl L.onlineBatch (wBC W) W.embB id (xinBA r₀) (cmsBA cA t.tree.root t.ood.2)
              (x, t.ood) (fun _ => t.tree) h.capB W.embE u.2
              (match u.2 with
                | some d => h.dressB (h.pvB d.plains) o.1.co
                | none => o.1.co) u.1.2 o.2
        | _ => .halt (none, o.2)).bind fun o' =>
      .halt (.inr [⟨o.1.j, h.nm o.1.j, o'.1⟩], (o'.2, w.2))

theorem proveStepA_one (h : HonestSide lam L Bd aT aL) (w : StG W) (x : X) :
    proveStepA W cA r₀ h w [x] = ((coinsP W h).runLazyA w.1).bind fun o =>
      sessA' W cA r₀ h w x o (w.2.bind fun ts => ts[o.1.j]?) := rfl

variable {W cA}

/-- the coins of the second pass, in the reduction's text and in coVB -/
theorem coVB_eq (co : Coins lam (typedOracleCarrier L Bd aT aL)) (v : Option (DView L.onlineBatch.loc)) :
    (match v with
      | some d => a.side.dressB (a.side.pvB d.plains) co
      | none => co) = coVB a co (v.map DView.plains) := by
  cases v <;> rfl

/-- Served: the game's run, then the second pass. -/
theorem sessA_served (T : Tb W) (ts : List (TabW lam L Bd aT aL)) (c : ℕ) (u : Hiop.UsedR)
    (st : StH L) (Tg : Tb W) (x : X) (d : DrawP lam L Bd aT aL a.side.KB)
    (t : TabW lam L Bd aT aL) (he : d.j + 1 ≤ c)
    (hu : u.sess (d.j + 1) < (boundsW a.side s1).sess (d.j + 1)) :
    runG W r₀ a Gs s1 i (sessA' W cA r₀ a.side (T, some ts) x (d, T) (some t))
        (some (c, u, st), Tg) =
      (Hiop.Seeded.runAt ((recsG a).B (d.j + 1))
        ((kitW W r₀ a.side).μB (d.j + 1)
          (x, L.recOf i (st.2 (d.j + 1)).1 (st.2 (d.j + 1)).2)) (kitW W r₀ a.side).ρB
        (i, (st.2 (d.j + 1)).1, (st.2 (d.j + 1)).2)
        (x, L.recOf i (st.2 (d.j + 1)).1 (st.2 (d.j + 1)).2)).bind fun v =>
        (pass2 Tag.onl L.onlineBatch (wBC W) W.embB id (xinBA r₀) (cmsBA cA t.tree.root t.ood.2) (x, t.ood)
          (fun _ => t.tree) a.side.capB W.embE v.2 (coVB a d.co (v.2.map DView.plains)) v.1.2
          T).map fun o' =>
          ((.inr [⟨d.j, a.side.nm d.j, o'.1⟩], (o'.2, some ts)),
            (some (c, { u with sess := Hiop.bump u.sess (d.j + 1) }, st), Tg)) := by
  rw [sessA', runG_call, game_sess W r₀ a Gs s1 i c u st Tg (d.j + 1) x he hu, PMF.bind_map]
  refine congrArg _ (funext fun v => ?_)
  show runG W r₀ a Gs s1 i
    ((pass2A Tag.onl L.onlineBatch (wBC W) W.embB id (xinBA r₀) (cmsBA cA t.tree.root t.ood.2) (x, t.ood)
      (fun _ => t.tree) a.side.capB W.embE v.2
      (match v.2 with
        | some d' => a.side.dressB (a.side.pvB d'.plains) d.co
        | none => d.co) v.1.2 T).bind fun o' =>
      .halt ((Sum.inr [(⟨d.j, a.side.nm d.j, o'.1⟩ : RequestProof lam L)] :
        GIn (FullKey lam L aT aL) (RequestProof lam L)), ((o'.2, some ts) : StG W))) _ = _
  rw [runG_bind, runG_pass2A, PMF.bind_map, coVB_eq]
  rfl

/-- Refused: no string, and nothing is done. -/
theorem sessA_refused (T : Tb W) (ts : List (TabW lam L Bd aT aL)) (c : ℕ) (u : Hiop.UsedR)
    (st : StH L) (Tg : Tb W) (x : X) (d : DrawP lam L Bd aT aL a.side.KB)
    (t : TabW lam L Bd aT aL)
    (hu : ¬ u.sess (d.j + 1) < (boundsW a.side s1).sess (d.j + 1)) :
    runG W r₀ a Gs s1 i (sessA' W cA r₀ a.side (T, some ts) x (d, T) (some t))
        (some (c, u, st), Tg) =
      PMF.pure ((.inr [⟨d.j, a.side.nm d.j, none⟩], (T, some ts)), (some (c, u, st), Tg)) := by
  rw [sessA', runG_call, game_sess_no W r₀ a Gs s1 i c u st Tg (d.j + 1) x hu, PMF.pure_bind]
  rfl

end OnBytes.LateWorld

#print axioms OnBytes.LateWorld.sess_branch
#print axioms OnBytes.LateWorld.sessA_served
#print axioms OnBytes.LateWorld.sessA_refused
