-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LateWorld/SetupGame.lean: THE REDUCTION's SETUP AGAINST THE REAL GAME, WHERE THE GAME
SERVES: the proofs of the five statements of Johnson/LateWorld/SpecSetupW.lean, and the game's
replies to the calls of the setup. Theorems with their proofs.

Lemmas of one step of a proof. This file states no goal of the release.

The game's replies (game_fresh, game_link) are read off the game's text
(gameReply, Hiop/Seeded/Game.lean) where its test says "served". They follow the pattern of
game_sess (Johnson/LateWorld/Steps.lean).

linksW: one induction on the copies. At each copy: the game's run of the link (game_link), then the
reduction's second pass; together they are the honest link laid late, with uniform coins of the
strategy (linkBranch, Johnson/LateWorld/Branches.lean); and a uniform draw is a draw through an
enumeration that lists each member once (bind_enum, Johnson/LateWorld/Batch.lean).

Main names (namespace OnBytes.LateWorld).
  game_fresh, game_link   the game's replies to the calls for a further table and for a link.
  gameTabsGood, stAfterKeeps, stAfterCopies, stAfterOod, linksW   THE THEOREMS.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LateWorld.SpecSetupW
import Johnson.LateWorld.Branches
import Johnson.LateWorld.Batch

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.LateWorld
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey OnBytes.WrapLaws
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (r₀ : L.Rec) (a : AtRecs lam L Bd aT aL)
  (Gs : L.OutOfDomainSeed → Prop) (s1 : ℕ) (i : I)

/-! ## The game's replies -/

/-- A further table. -/
theorem game_fresh (c : ℕ) (u : Hiop.UsedR) (st : StH L) (Tg : Tb W) (s : L.OutOfDomainSeed) (hs : Gs s)
    (hc : c < a.M + 1) :
    repG W r₀ a Gs s1 i (some (c, u, st), Tg) (.table s) =
      (unif L.EncodingRandomness).map fun r =>
        (.ood (L.recOf i r s), (some (c + 1, u, push st (r, s)), Tg)) := by
  show (Hiop.Seeded.gameReply (Hiop.Seeded.realLawsG L (kitW W r₀ a.side) (recsG a) i).host
    (boundsW a.side s1) Gs (some (c, u, st)) (.table s)).map (fun p => (p.1, (p.2, Tg))) = _
  simp only [Hiop.Seeded.gameReply]
  rw [if_pos ⟨hs, hc⟩]
  have e1 : (Hiop.Seeded.realLawsG L (kitW W r₀ a.side) (recsG a) i).host.fresh st s =
      (unif L.EncodingRandomness).map fun r => (L.recOf i r s, push st (r, s)) := rfl
  rw [e1]
  exact (PMF.map_comp _ _ _).trans ((PMF.map_comp _ _ _).trans rfl)

/-- The link from the first table to the table number e. -/
theorem game_link (c : ℕ) (u : Hiop.UsedR) (st : StH L) (Tg : Tb W) (e : ℕ) (h1 : 1 ≤ e)
    (he : e ≤ c) (hu : u.links e < (boundsW a.side s1).links e) :
    repG W r₀ a Gs s1 i (some (c, u, st), Tg) (.link e) =
      (Hiop.Seeded.runAt ((recsG a).Lk e)
        ((kitW W r₀ a.side).μL e
          (L.recOf i (st.2 0).1 (st.2 0).2, L.recOf i (st.2 e).1 (st.2 e).2))
        (kitW W r₀ a.side).ρL (i, st.2 0, st.2 e)
        (L.recOf i (st.2 0).1 (st.2 0).2, L.recOf i (st.2 e).1 (st.2 e).2)).map fun v =>
        (.link v, (some (c, { u with links := Hiop.bump u.links e }, st), Tg)) := by
  show (Hiop.Seeded.gameReply (Hiop.Seeded.realLawsG L (kitW W r₀ a.side) (recsG a) i).host
    (boundsW a.side s1) Gs (some (c, u, st)) (.link e)).map (fun p => (p.1, (p.2, Tg))) = _
  simp only [Hiop.Seeded.gameReply]
  rw [if_pos ⟨h1, he, hu⟩]
  have e1 : (Hiop.Seeded.realLawsG L (kitW W r₀ a.side) (recsG a) i).host.link st e =
      (Hiop.Seeded.runAt ((recsG a).Lk e)
        ((kitW W r₀ a.side).μL e
          (L.recOf i (st.2 0).1 (st.2 0).2, L.recOf i (st.2 e).1 (st.2 e).2))
        (kitW W r₀ a.side).ρL (i, st.2 0, st.2 e)
        (L.recOf i (st.2 0).1 (st.2 0).2, L.recOf i (st.2 e).1 (st.2 e).2)).map fun v => (v, st) :=
    rfl
  rw [e1]
  exact (PMF.map_comp _ _ _).trans ((PMF.map_comp _ _ _).trans rfl)

/-! ## The copies' tables -/

/-- **Where all seeds lie in Gs and there is room, the game refuses no table.** -/
theorem gameTabsGood : Spec.gameTabsGood := by
  intro I X lam L Bd aT aL W r₀ a Gs s1 i os
  induction os with
  | nil =>
    intro c u st Tg _ _
    show PMF.pure _ = (PMF.pure []).map _
    rw [PMF.pure_map]
    rfl
  | cons o os ih =>
    intro c u st Tg hG hc
    have hc' : c + (os.length + 1) ≤ a.M + 1 := hc
    show (repG W r₀ a Gs s1 i (some (c, u, st), Tg) (.table o.2)).bind _ =
      ((unif L.EncodingRandomness).bind fun r => (drawU L os.length).map fun rs => r :: rs).map _
    rw [game_fresh W r₀ a Gs s1 i c u st Tg o.2 (hG o (List.mem_cons_self ..)) (by omega),
      PMF.bind_map, PMF.map_bind]
    refine congrArg _ (funext fun r => ?_)
    show (gameTabs W r₀ a Gs s1 i os (some (c + 1, u, push st (r, o.2)), Tg)).map _ = _
    rw [ih (c + 1) u (push st (r, o.2)) Tg (fun x hx => hG x (List.mem_cons_of_mem _ hx))
      (by omega), PMF.map_comp, PMF.map_comp]
    refine congrArg (fun f => PMF.map f (drawU L os.length)) (funext fun rs => ?_)
    show (some ((⟨o.1, L.recOf i r o.2⟩ : TabW lam L Bd aT aL) :: mkTs i rs os),
        ((some (c + 1 + os.length, u, stAfter (push st (r, o.2)) rs os), Tg) : StGm W)) =
      (some (mkTs i (r :: rs) (o :: os)),
        ((some (c + (os.length + 1), u, stAfter st (r :: rs) (o :: os)), Tg) : StGm W))
    rw [show c + 1 + os.length = c + (os.length + 1) by omega]
    rfl

/-- The earlier tables are kept. -/
theorem stAfterKeeps : Spec.stAfterKeeps := by
  intro I X lam L Bd aT aL rs
  induction rs with
  | nil => exact fun _ _ _ _ => rfl
  | cons r rs ih =>
    intro os st e he
    cases os with
    | nil => rfl
    | cons o os =>
      show (stAfter (push st (r, o.2)) rs os).2 e = st.2 e
      rw [ih os (push st (r, o.2)) e (Nat.le_succ_of_le he)]
      exact Function.update_of_ne (by omega) _ _

/-- The honest side's copies, read off the reduction's tables and the host's state. -/
theorem stAfterCopies : Spec.stAfterCopies := by
  intro I X lam L Bd aT aL W a i rs
  induction rs with
  | nil => exact fun _ _ => rfl
  | cons r rs ih =>
    intro os st
    cases os with
    | nil => rfl
    | cons o os =>
      have hk : (stAfter (push st (r, o.2)) rs os).2 (st.1 + 1) = (r, o.2) := by
        rw [stAfterKeeps I X lam L Bd aT aL rs os (push st (r, o.2)) (st.1 + 1) (Nat.le_refl _)]
        exact Function.update_self _ _ _
      show (⟨((stAfter (push st (r, o.2)) rs os).2 (st.1 + 1)).1,
          realTree W a.b₀ (L.encodeIndex i ((stAfter (push st (r, o.2)) rs os).2 (st.1 + 1)).1) o.1,
          ((stAfter (push st (r, o.2)) rs os).2 (st.1 + 1)).2⟩ : TabK lam L Bd aT aL) ::
          realCopies W a i (stAfter (push st (r, o.2)) rs os).2 (st.1 + 1 + 1) (mkTs i rs os) =
        ⟨r, realTree W a.b₀ (L.encodeIndex i r) o.1, o.2⟩ :: realTabs W a.b₀ i rs os
      rw [hk]
      exact congrArg (_ :: ·) (ih os (push st (r, o.2)))

/-- The reduction's out-of-domain samples are the index's at the host's (randomness, seed). -/
theorem stAfterOod : Spec.stAfterOod := by
  intro I X lam L Bd aT aL i rs
  induction rs with
  | nil =>
    intro os st e t h
    simp [mkTs] at h
  | cons r rs ih =>
    intro os st e t h
    cases os with
    | nil => simp [mkTs] at h
    | cons o os =>
      cases e with
      | zero =>
        obtain rfl : (⟨o.1, L.recOf i r o.2⟩ : TabW lam L Bd aT aL) = t := by
          simpa [mkTs] using h
        have hk : (stAfter (push st (r, o.2)) rs os).2 (st.1 + 1) = (r, o.2) := by
          rw [stAfterKeeps I X lam L Bd aT aL rs os (push st (r, o.2)) (st.1 + 1) (Nat.le_refl _)]
          exact Function.update_self _ _ _
        show L.recOf i r o.2 = L.recOf i ((stAfter (push st (r, o.2)) rs os).2 (st.1 + 1 + 0)).1
          ((stAfter (push st (r, o.2)) rs os).2 (st.1 + 1 + 0)).2
        rw [Nat.add_zero, hk]
      | succ e =>
        have h' : (mkTs i rs os)[e]? = some t := by simpa [mkTs] using h
        have := ih os (push st (r, o.2)) e t h'
        show t.ood = L.recOf i ((stAfter (push st (r, o.2)) rs os).2 (st.1 + 1 + (e + 1))).1
          ((stAfter (push st (r, o.2)) rs os).2 (st.1 + 1 + (e + 1))).2
        rw [show st.1 + 1 + (e + 1) = st.1 + 1 + 1 + e by omega]
        exact this

/-! ## The links -/

/-- the coins of the second pass, in the reduction's text and in coVL -/
theorem coVL_eq (co : Coins lam (typedOracleCarrier L Bd aT aL)) (v : Option (DView L.link)) :
    (match v with
      | some d => a.side.dressL (a.side.pvL d.plains) co
      | none => co) = coVL a co (v.map DView.plains) := by
  cases v <;> rfl

/-- **The links against the game are the honest links laid late.** -/
theorem linksW : Spec.linksW := by
  intro I X lam L Bd aT aL W S cA r₀ a ok Gs δ s1 i hP hi t₁ c st Tg l
  induction l with
  | nil =>
    intro e u T _ _ _ _ _
    show PMF.pure _ = (PMF.pure _).map _
    rw [PMF.pure_map]
    rfl
  | cons x l ih =>
    intro e u T h1 hec hu ht₁ hx
    have hec' : e + (l.length + 1) ≤ c + 1 := hec
    obtain ⟨hx0, hco⟩ := hx 0 x rfl
    rw [Nat.add_zero] at hx0
    have hu0 : u.links e < (boundsW a.side s1).links e := by
      have := hu 0 (Nat.succ_pos _)
      rw [Nat.add_zero] at this
      rw [this]
      show 0 < if e = 0 then 0 else 1
      rw [if_neg (by omega)]
      exact Nat.one_pos
    -- the later links, by the induction
    have IH := fun T' => ih (e + 1) { u with links := Hiop.bump u.links e } T' (by omega) (by omega)
      (fun k hk => by
        show Hiop.bump u.links e (e + 1 + k) = 0
        unfold Hiop.bump
        rw [Function.update_of_ne (by omega), show e + 1 + k = e + (k + 1) by omega]
        exact hu (k + 1) (Nat.succ_lt_succ hk)) ht₁
      (fun k y hy => by
        have := hx (k + 1) y (by simpa using hy)
        rwa [show e + (k + 1) = e + 1 + k by omega] at this)
    -- this link
    have hB := linkBranch I X lam L Bd aT aL W S cA r₀ a ok Gs δ i hP hi e t₁ x.2 (st.2 0) (st.2 e)
      x.1.co hco T
    rw [linksA, runG_call, game_link W r₀ a Gs s1 i c u st Tg e h1 (by omega) hu0, PMF.bind_map]
    have step : ∀ v : (kitW W r₀ a.side).AL × Option (DView L.link), runG W r₀ a Gs s1 i
        ((pass2A Tag.link (batLC L aL) (wLC W) W.embL id (fun _ => none)
          (cmsLA cA t₁.tree.root x.2.tree.root t₁.ood.2 x.2.ood.2) (t₁.ood, x.2.ood)
          (fun k => if k = 0 then t₁.tree else x.2.tree) a.side.capL W.embE v.2
          (match v.2 with
            | some d => a.side.dressL (a.side.pvL d.plains) x.1.co
            | none => x.1.co) v.1.2 T).bind fun o =>
        (linksA W cA r₀ a.side t₁ (e + 1) l o.2).bind fun o' =>
          .halt ((x.2.tree.root, x.2.ood, o.1) :: o'.1, o'.2))
        (some (c, { u with links := Hiop.bump u.links e }, st), Tg) =
        (pass2 Tag.link (batLC L aL) (wLC W) W.embL id (fun _ => none)
          (cmsLA cA t₁.tree.root x.2.tree.root (L.recOf i (st.2 0).1 (st.2 0).2).2
            (L.recOf i (st.2 e).1 (st.2 e).2).2)
          (L.recOf i (st.2 0).1 (st.2 0).2, L.recOf i (st.2 e).1 (st.2 e).2)
          (fun k => if k = 0 then t₁.tree else x.2.tree) a.side.capL W.embE v.2
          (coVL a x.1.co (v.2.map DView.plains)) v.1.2 T).bind fun o =>
        (linksM W cA a.side i
          ⟨(st.2 0).1, realTree W a.b₀ (L.encodeIndex i (st.2 0).1) t₁.tree, (st.2 0).2⟩
          ((l.map fun y => y.1.co).zip (realCopies W a i st.2 (e + 1) (l.map fun y => y.2)))
          o.2).map fun o' =>
          (((x.2.tree.root, L.recOf i (st.2 e).1 (st.2 e).2, o.1) :: o'.1, o'.2),
            ((some (c, linksUsed { u with links := Hiop.bump u.links e } (e + 1) l.length, st),
              Tg) : StGm W)) := by
      intro v
      rw [runG_bind, runG_pass2A, PMF.bind_map, coVL_eq, ht₁, hx0]
      refine congrArg _ (funext fun o => ?_)
      show runG W r₀ a Gs s1 i ((linksA W cA r₀ a.side t₁ (e + 1) l o.2).bind fun o' =>
        .halt ((x.2.tree.root, L.recOf i (st.2 e).1 (st.2 e).2, o.1) :: o'.1, o'.2)) _ = _
      rw [runG_bind, IH o.2, PMF.bind_map]
      rfl
    refine Eq.trans (congrArg _ (funext fun v => step v)) ?_
    rw [← PMF.bind_bind, hB, ← bind_enum (β := a.Hs.Lk.Coin) a.kL hP.kL]
    show _ = ((linkM W cA a.side i _ _ x.1.co T).bind fun o => (linksM W cA a.side i _ _ o.2).bind
      fun o' => PMF.pure _).map _
    rw [PMF.map_bind]
    refine congrArg _ (funext fun o => ?_)
    rw [PMF.map_bind]
    simp only [PMF.pure_map]
    rfl

end OnBytes.LateWorld

#print axioms OnBytes.LateWorld.gameTabsGood
#print axioms OnBytes.LateWorld.stAfterKeeps
#print axioms OnBytes.LateWorld.stAfterCopies
#print axioms OnBytes.LateWorld.stAfterOod
#print axioms OnBytes.LateWorld.linksW
