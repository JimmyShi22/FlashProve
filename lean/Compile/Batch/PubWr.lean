-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/PubWr.lean: the reduction for batches, which publishes a function of its key at the
setup, and what holds of it around every challenger ("wrapper", `Wrap`, in Lean names; words of this
library: lean/GLOSSARY.md).

Compile/Batch/Wr.lean has the reduction's state (`WτB`) and general lemmas on admissible adversaries
of the lifetime game (Compile/Batch/SpecLifeStar.lean), which are used as they are; the reduction
itself is defined here. At the setup it makes the trees and the proof strings of
Test and of all Links from what the lifetime game returns, keeps for each copy its tree and the
proof string of its Link as its key (`WKey`), and replies with pw ivk key, for an arbitrary function
pw.

  `wrapBP`, `wrapGP`, `asW_wrapBP`  The reduction, for given programs cpW (setup) and ppW (batch);
                                    the same with the calls of the real experiment.
  `lifeAdmB_wrapGP`  An admissible adversary (batches of at most L.maxBatchSize requests, all allowed) against
                     the reduction is an admissible adversary of the lifetime game.
  `consistent_wrapBP`  The reduction never answers a repeated query differently, around every
                       challenger.
  `theWrapBP`, `WrBP`, `iniBP`  The reduction with the programs of Compile/Batch/Mirror.lean.
-/
import Compile.Batch.Wr
import Compile.Batch.PubChall

noncomputable section

namespace Compile.Batch
open Iop Rom Prob
open Compile.GlueB (GCall SCall GAdm asW)
open Compile.BatchLife (LifeOutB LifeInB BRet LifeAdmB)
open Compile.Lifetime (Sess)
open Compile.DefC (virtL)
open Compile.Life2 (advBind_assoc)

variable {I X V : Type} {lam : ℕ} {L : BatchProtocol I X}

variable (W : QueryLayout lam L) (p : Params) (pw : IVK lam L → WKey lam L → V)
  (cpW : Sess L.offline → List (Sess L.link) → Lp lam W.K L (IVK lam L × WKey lam L))
  (ppW : WKey lam L → List X → ℕ → BRet L → Lp lam W.K L (List (Prf lam L)))

/-- the setup, after the game's answer: the reply is pw of ivk and of the key that the reduction has
just made -/
def repSetupBP (w : LSt (spec lam W.K L)) (s : WτB W) :
    LifeInB L → Adv (spec lam W.K L) (LifeOutB X) (LifeInB L) (BInP V lam L × WτB W)
  | .inl (sT, ls) =>
      (((cpW sT ls).bind fun o => LStep.fresh 0 fun t => LStep.pure (o, t)).toAdv w).bind fun y =>
        .halt (.inl (pw y.1.1.1 y.1.1.2), (some (y.1.1.2, y.1.2, fun _ => 0), y.2))
  | .inr _ => .halt (.inr [], s)

/-- a batch on copy j, after the game's answer -/
def repBatchP (V : Type) (key : WKey lam L) (N₀ : ℕ) (c : ℕ → ℕ) (xs : List X) (t₀ : ℕ)
    (j : Fin (p.M + 1)) (w : LSt (spec lam W.K L)) :
    LifeInB L → Adv (spec lam W.K L) (LifeOutB X) (LifeInB L) (BInP V lam L × WτB W)
  | .inr (some ret) =>
      ((virtL N₀ (t₀ + 1 - N₀) (ppW key xs j.val ret)).toAdv w).bind fun z =>
        .halt (.inr z.1, (some (key, N₀, Function.update c j.val (c j.val + 1)), z.2))
  | _ =>
    .halt (.inr (xs.map fun _ => ⟨j.val, default, none, none⟩),
        (some (key, N₀, Function.update c j.val (c j.val + 1)), w))

/-- The reduction. Its state (`WτB`, Compile/Batch/Wr.lean): the key, the number of the setup's
tokens, the number of batches of each copy (none as long as there is no key); and the state `LSt`.
An oracle query is answered by the step `LStep.plain o q`. A "setup" in a state without a key calls
the game (`.inl ()`) and goes on with `repSetupBP`; one in a state with a key, a "prove" in a state
without one and a "prove" of no instance get the reply `.inr []`. Else a copy j among p.M + 1 is
sampled: if it has served fewer than p.s1 batches, the game is called on (j, xs) and `repBatchP`
goes on; else the reply is `.inr []`. -/
def wrapBP : Wrap (spec lam W.K L) (SCall X) (BInP V lam L) (LifeOutB X) (LifeInB L) where
  τ := WτB W
  ans := fun s o q =>
    ((LStep.plain o q LStep.pure : Lp lam W.K L _).toAdv s.2).bind fun y => .halt (y.1, (s.1, y.2))
  rep := fun s c => match c, s.1 with
    | .setup, none => .call (.inl ()) (repSetupBP W pw cpW s.2 s)
    | .setup, some _ => .halt (.inr [], s)
    | .prove _, none => .halt (.inr [], s)
    | .prove xs, some (key, N₀, c) =>
        if xs.isEmpty then .halt (.inr [], s)
        else
          ((LStep.fresh 0 fun t₀ =>
                LStep.sample p.M fun j =>
                  LStep.pure (t₀, j) : Lp lam W.K L (ℕ × Fin (p.M + 1))).toAdv
              s.2).bind fun y =>
            if c y.1.2.val < p.s1 then
              .call (.inr (y.1.2.val, xs)) (repBatchP W p ppW V key N₀ c xs y.1.1 y.1.2 y.2)
            else .halt (.inr [], (some (key, N₀, c), y.2))

/-- the reduction with the calls of the real experiment: of a batch it is told the own instances -/
def wrapGP : Wrap (spec lam W.K L) (GCall X Unit) (BInP V lam L) (LifeOutB X) (LifeInB L) where
  τ := WτB W
  ans := (wrapBP W p pw cpW ppW).ans
  rep := fun s c => (wrapBP W p pw cpW ppW).rep s (GlueB.forget c)

theorem asW_wrapBP (G : World (spec lam W.K L) (LifeOutB X) (LifeInB L)) :
    asW Unit ((wrapBP W p pw cpW ppW).world G) = (wrapGP W p pw cpW ppW).world G := rfl

/-! ## Admissibility -/

/-- Under the hypotheses below: the reduction makes an admissible adversary of the lifetime game. c
is the game's count of the batches of each copy, which is the reduction's own. -/
theorem lifeAdmB_substP (ok : X → Prop) {α : Type}
    (A : Adv (spec lam W.K L) (GCall X Unit) (BInP V lam L) α) :
    ∀ (s : WτB W) (c : ℕ → ℕ) (b : Bool) (n : ℕ),
      GAdm (fun b => b.pairs.length ≤ L.maxBatchSize ∧ ∀ xw ∈ b.pairs, ok xw.1) A b n →
      (∀ key N₀ c', s.1 = some (key, N₀, c') → b = true ∧ c' = c) → (b = false → c = fun _ => 0) →
      LifeAdmB ok p.s1 ((wrapGP W p pw cpW ppW).subst A s) c b n := by
  induction A with
  | halt a => exact fun _ _ _ _ _ _ _ => trivial
  | sample m k ih => exact fun s c b n h hs hc r => ih r s c b n (h r) hs hc
  | query o q k ih =>
    intro s c b n h hs hc
    simp only [Wrap.subst, wrapGP, wrapBP, advBind_assoc]
    exact lifeAdmB_bind_quiet ok p.s1 _ (toAdv_quiet _ _) _ c b n fun y =>
      ih y.1 (s.1, y.2) c b n (h y.1) hs hc
  | call m k ih =>
    intro s c b n h hs hc
    obtain ⟨so, w⟩ := s
    rcases m with _ | bt
    · simp only [GAdm] at h
      obtain ⟨rfl, h⟩ := h
      cases so with
      | some kk => exact absurd (hs kk.1 kk.2.1 kk.2.2 rfl).1 (by simp)
      | none =>
        simp only [Wrap.subst, wrapGP, wrapBP, GlueB.forget, Adv.bind, LifeAdmB]
        refine ⟨trivial, fun a => ?_⟩
        rcases a with ⟨sT, ls⟩ | a
        · simp only [repSetupBP, advBind_assoc]
          refine lifeAdmB_bind_quiet ok p.s1 _ (toAdv_quiet _ _) _ c true n fun y => ?_
          refine ih _ _ c true n (h _) (fun key N₀ c' he => ⟨rfl, ?_⟩)
            (fun hb => absurd hb (by simp))
          simp only [Option.some.injEq, Prod.mk.injEq] at he
          rw [← he.2.2, hc rfl]
        · exact ih _ _ c true n (h _) (fun key N₀ c' he => absurd he (by simp))
            (fun hb => absurd hb (by simp))
    · cases n with
      | zero => exact h.elim
      | succ n =>
        simp only [GAdm] at h
        obtain ⟨rfl, hx, h⟩ := h
        cases so with
        | none => exact lifeAdmB_succ ok p.s1 _ c true n (ih _ _ c true n (h _) hs hc)
        | some kk =>
          obtain ⟨key, N₀, c'⟩ := kk
          obtain ⟨-, rfl⟩ := hs key N₀ c' rfl
          have hsame : ∀ (π : BInP V lam L) (w' : LSt (spec lam W.K L)),
              LifeAdmB ok p.s1 ((wrapGP W p pw cpW ppW).subst (k π) (some (key, N₀, c'), w'))
                c' true (n + 1) := fun π w' =>
            lifeAdmB_succ ok p.s1 _ c' true n (ih π _ c' true n (h π) (fun key' N' c'' he => ⟨rfl, by
              simp only [Option.some.injEq, Prod.mk.injEq] at he
              exact he.2.2.symm⟩) (fun hb => absurd hb (by simp)))
          simp only [Wrap.subst, wrapGP, wrapBP, GlueB.forget]
          by_cases he : bt.ownX.isEmpty = true
          · simp only [he, if_true]
            exact hsame _ _
          · simp only [he, Bool.false_eq_true, if_false, advBind_assoc]
            refine lifeAdmB_bind_quiet ok p.s1 _ (toAdv_quiet _ _) _ c' true (n + 1) fun y => ?_
            by_cases hj : c' y.1.2.val < p.s1
            · simp only [if_pos hj, Adv.bind, LifeAdmB]
              refine ⟨trivial, hj, (length_ownX_le bt).trans hx.1, fun x hxm => ?_, fun a => ?_⟩
              · obtain ⟨xw, hxw, rfl⟩ := mem_pairs_of_mem_ownX hxm
                exact hx.2 xw hxw
              · have hrest : ∀ (π : BInP V lam L) (w' : LSt (spec lam W.K L)),
                    LifeAdmB ok p.s1 ((wrapGP W p pw cpW ppW).subst (k π)
                      (some (key, N₀, Function.update c' y.1.2.val (c' y.1.2.val + 1)), w'))
                      (Function.update c' y.1.2.val (c' y.1.2.val + 1)) true n := fun π w' =>
                  ih π _ _ true n (h π) (fun key' N' c'' he => ⟨rfl, by
                    simp only [Option.some.injEq, Prod.mk.injEq] at he
                    exact he.2.2.symm⟩) (fun hb => absurd hb (by simp))
                rcases a with a | _ | ret
                · exact hrest _ _
                · exact hrest _ _
                · simp only [repBatchP, advBind_assoc]
                  exact lifeAdmB_bind_quiet ok p.s1 _ (toAdv_quiet _ _)
                    _ _ true n fun z => hrest _ _
            · simp only [if_neg hj]
              exact hsame _ _

theorem lifeAdmB_wrapGP (ok : X → Prop) {α : Type}
    (A : Adv (spec lam W.K L) (GCall X Unit) (BInP V lam L) α) (n : ℕ)
    (h : GAdm (fun b => b.pairs.length ≤ L.maxBatchSize ∧ ∀ xw ∈ b.pairs, ok xw.1) A false n) :
    LifeAdmB ok p.s1 ((wrapGP W p pw cpW ppW).adv A (none, LSt.init _)) (fun _ => 0) false n :=
  lifeAdmB_bind_halt ok p.s1 _ _ _ _ _
    (lifeAdmB_substP W p pw cpW ppW ok A _ _ false n h
      (fun _ _ _ he => absurd he (by simp)) fun _ => rfl)

/-! ## The reduction is consistent, around every challenger -/

section Consistent

variable {W p pw cpW ppW}
variable (G : World (spec lam W.K L) (LifeOutB X) (LifeInB L))

theorem answer_wrapBP (s : WτB W) (g : G.σ) (o : OracleName) (q : domOf lam L o) :
    ((wrapBP W p pw cpW ppW).world G).answer (s, g) o q =
      (lazyAnswer (S := spec lam W.K L) s.2.table o q).map fun a =>
        (a.1, ((s.1, { s.2 with table := a.2 }), g)) := by
  show (interact G
      (((LStep.plain (S := spec lam W.K L) o q LStep.pure : Lp lam W.K L _).toAdv s.2).bind
        fun y => .halt (y.1, (s.1, y.2))) g).map _ = _
  rw [interact_bind, interact_toAdv]
  simp only [LStep.run, PMF.map_bind, PMF.bind_bind, PMF.pure_bind, interact, PMF.pure_map]
  rfl

/-- whatever the challenger behind it does, the program ends with a table that contains T -/
def KeepsBP {β : Type} (T : Table (spec lam W.K L))
    (P : Adv (spec lam W.K L) (LifeOutB X) (LifeInB L) (β × WτB W)) : Prop :=
  ∀ (G : World (spec lam W.K L) (LifeOutB X) (LifeInB L)) (g : G.σ),
    ∀ z ∈ (interact G P g).support, T.Sub z.1.2.2.table

theorem keepsBP_halt {β : Type} {T : Table (spec lam W.K L)} (a : β)
    (st : WτB W) (h : T.Sub st.2.table) : KeepsBP T (.halt (a, st)) := by
  intro G g z hz
  simp only [interact, PMF.support_pure, Set.mem_singleton_iff] at hz
  rw [hz]
  exact h

theorem keepsBP_call {β : Type} {T : Table (spec lam W.K L)} (m : LifeOutB X)
    (k : LifeInB L → Adv (spec lam W.K L) (LifeOutB X) (LifeInB L) (β × WτB W))
    (h : ∀ a, KeepsBP T (k a)) : KeepsBP T (.call m k) := by
  intro G g z hz
  simp only [interact, PMF.mem_support_bind_iff] at hz
  obtain ⟨y, -, hz⟩ := hz
  exact h y.1 G y.2 z hz

theorem keepsBP_toAdv_bind {β γ : Type} {T : Table (spec lam W.K L)} (Q : Lp lam W.K L γ)
    (w : LSt (spec lam W.K L))
    (f : γ × LSt (spec lam W.K L) → Adv (spec lam W.K L) (LifeOutB X) (LifeInB L) (β × WτB W))
    (hw : T.Sub w.table) (h : ∀ y, T.Sub y.2.table → KeepsBP T (f y)) :
    KeepsBP T ((Q.toAdv w).bind f) := by
  intro G g z hz
  rw [interact_bind, interact_toAdv, PMF.bind_map] at hz
  obtain ⟨y, hy, hz⟩ := (PMF.mem_support_bind_iff _ _ _).1 hz
  exact h y (hw.trans (run_table_mono Q w y hy)) G g z hz

theorem keepsBP_rep (s : WτB W) (c : SCall X) :
    KeepsBP s.2.table ((wrapBP W p pw cpW ppW).rep s c) := by
  obtain ⟨so, w⟩ := s
  have hr := Table.Sub.refl w.table
  rcases c with _ | xs
  · cases so with
    | some kk => exact keepsBP_halt _ _ hr
    | none =>
      refine keepsBP_call _ _ fun a => ?_
      rcases a with ⟨sT, ls⟩ | a
      · exact keepsBP_toAdv_bind _ _ _ hr fun y hy => keepsBP_halt _ _ hy
      · exact keepsBP_halt _ _ hr
  · cases so with
    | none => exact keepsBP_halt _ _ hr
    | some kk =>
      obtain ⟨key, N₀, c'⟩ := kk
      simp only [wrapBP]
      by_cases he : xs.isEmpty = true
      · simp only [he, if_true]
        exact keepsBP_halt _ _ hr
      · simp only [he, Bool.false_eq_true, if_false]
        refine keepsBP_toAdv_bind _ _ _ hr fun y hy => ?_
        by_cases hj : c' y.1.2.val < p.s1
        · simp only [if_pos hj]
          refine keepsBP_call _ _ fun a => ?_
          rcases a with a | _ | ret
          · exact keepsBP_halt _ _ hy
          · exact keepsBP_halt _ _ hy
          · exact keepsBP_toAdv_bind _ _ _ hy fun z hz => keepsBP_halt _ _ hz
        · simp only [if_neg hj]
          exact keepsBP_halt _ _ hy

/-- The reduction never answers a repeated query differently. -/
theorem consistent_wrapBP : ((wrapBP W p pw cpW ppW).world G).Consistent := by
  refine ⟨fun s => s.1.2.table, ?_, ?_, ?_⟩
  · rintro ⟨s, g⟩ o q r hr x hx
    rw [answer_wrapBP, lazyAnswer_of_some hr, PMF.pure_map] at hx
    rw [(PMF.mem_support_pure_iff _ _).1 hx]
  · rintro ⟨s, g⟩ o q x hx
    rw [answer_wrapBP] at hx
    cases hT : s.2.table o q with
    | some r =>
      rw [lazyAnswer_of_some hT, PMF.pure_map] at hx
      rw [(PMF.mem_support_pure_iff _ _).1 hx]
      exact ⟨hT, fun _ _ _ h => h⟩
    | none =>
      rw [lazyAnswer_of_none hT, PMF.map_comp] at hx
      obtain ⟨r, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hx
      exact ⟨Table.set_apply_same _ _ _ _, Table.sub_set hT r⟩
  · rintro ⟨s, g⟩ m x hx
    obtain ⟨z, hz, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hx
    exact keepsBP_rep s m G g z hz

end Consistent

/-! ## The reduction with its programs -/

/-- the reduction with its programs (Compile/Batch/Mirror.lean) -/
def theWrapBP : Wrap (spec lam W.K L) (SCall X) (BInP V lam L) (LifeOutB X) (LifeInB L) :=
  wrapBP W p pw (fun sT ls => CpW W p sT (ls.take (p.M + 1))) (PpW W p)

/-- The reduction around a challenger G. -/
def WrBP :
    World (spec lam W.K L) (LifeOutB X) (LifeInB L) →
    World (spec lam W.K L) (SCall X) (BInP V lam L) :=
  fun G => (theWrapBP W p pw).world G

/-- Its initial state. -/
def iniBP : (G : World (spec lam W.K L) (LifeOutB X) (LifeInB L)) → G.σ → (WrBP W p pw G).σ :=
  fun _ g => ((none, LSt.init _), g)

end Compile.Batch
