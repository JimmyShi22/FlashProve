-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Step1_defc_Gen.lean: generic lemmas on adversaries, wrappers and challengers; used in
Compile/Step1_life2_Wr.lean and Compile/Batch/.

  `Adv.bind`                     Adversaries as programs.
  `Wrap`, `Wrap.world`, `Wrap.subst`
                                 A wrapper whose moves are programs over the inner challenger; an
                                 adversary against the wrapped challenger is an adversary against
                                 the inner one (`interact_subst`).
  `interact_lump`                A map of states that commutes with all moves keeps the law of the
                                 output.
-/
import Rom.Forget
import Prob.Tv
noncomputable section -- Lean tags what it cannot compile

open scoped ENNReal
open Prob

namespace Rom

variable {S : OSpec} {Out In Out' In' α β : Type}

/-! ### Adversaries as programs -/

def Adv.bind : Adv S Out In α → (α → Adv S Out In β) → Adv S Out In β
  | .halt a, f => f a
  | .sample n k, f => .sample n fun r => (k r).bind f
  | .query o q k, f => .query o q fun r => (k r).bind f
  | .call m k, f => .call m fun a => (k a).bind f

theorem interact_bind (W : World S Out In) (A : Adv S Out In α) (f : α → Adv S Out In β) :
    ∀ s, interact W (A.bind f) s = (interact W A s).bind fun x => interact W (f x.1) x.2 := by
  induction A with
  | halt a => intro s; simp only [Adv.bind, interact, PMF.pure_bind]
  | sample n k ih => intro s; simp only [Adv.bind, interact, ih, PMF.bind_bind]
  | query o q k ih => intro s; simp only [Adv.bind, interact, ih, PMF.bind_bind]
  | call m k ih => intro s; simp only [Adv.bind, interact, ih, PMF.bind_bind]

theorem uniform_map_equiv {γ δ : Type} [Fintype γ] [Nonempty γ] [Fintype δ]
    [Nonempty δ] (e : γ ≃ δ) :
    (PMF.uniformOfFintype γ).map e = PMF.uniformOfFintype δ := by
  ext d
  rw [PMF.map_apply, tsum_eq_single (e.symm d)]
  · simp [PMF.uniformOfFintype_apply, Fintype.card_congr e]
  · intro c hc
    have : d ≠ e c := fun h => hc (by rw [h, Equiv.symm_apply_apply])
    simp [this]

/-! ### Wrappers -/

/-- A wrapper: a private state, and for each move of the outer adversary a program over the inner
challenger. -/
structure Wrap (S : OSpec) (Out In Out' In' : Type) where
  τ : Type
  ans : τ → (o : S.ι) → S.Dom o → Adv S Out' In' (S.Rng o × τ)
  rep : τ → Out → Adv S Out' In' (In × τ)

/-- the wrapped challenger -/
def Wrap.world (Wp : Wrap S Out In Out' In') (G : World S Out' In') :
    World S Out In where
  σ := Wp.τ × G.σ
  answer s o q := (interact G (Wp.ans s.1 o q) s.2).map fun x => (x.1.1, (x.1.2, x.2))
  reply s m := (interact G (Wp.rep s.1 m) s.2).map fun x => (x.1.1, (x.1.2, x.2))

/-- the outer adversary with the wrapper inside: an adversary against the inner challenger -/
def Wrap.subst (Wp : Wrap S Out In Out' In') : Adv S Out In α → Wp.τ → Adv S Out' In' (α × Wp.τ)
  | .halt a, w => .halt (a, w)
  | .sample n k, w => .sample n fun r => Wp.subst (k r) w
  | .query o q k, w => (Wp.ans w o q).bind fun x => Wp.subst (k x.1) x.2
  | .call m k, w => (Wp.rep w m).bind fun x => Wp.subst (k x.1) x.2

theorem interact_subst (Wp : Wrap S Out In Out' In') (G : World S Out' In') (A : Adv S Out In α) :
    ∀ (w : Wp.τ) (g : G.σ), (interact (Wp.world G) A (w, g)).map (fun x => ((x.1, x.2.1), x.2.2)) =
      interact G (Wp.subst A w) g := by
  induction A with
  | halt a => intro w g; simp only [interact, Wrap.subst, PMF.pure_map]
  | sample n k ih => intro w g; simp only [interact, Wrap.subst, PMF.map_bind, ih]
  | query o q k ih =>
    intro w g
    simp only [interact, Wrap.subst, PMF.map_bind, interact_bind]
    show ((interact G (Wp.ans w o q) g).map _).bind _ = _
    rw [PMF.bind_map]
    exact congrArg _ (funext fun x => ih _ _ _)
  | call m k ih =>
    intro w g
    simp only [interact, Wrap.subst, PMF.map_bind, interact_bind]
    show ((interact G (Wp.rep w m) g).map _).bind _ = _
    rw [PMF.bind_map]
    exact congrArg _ (funext fun x => ih _ _ _)

/-- `Wp.subst A w` with the wrapper's final state dropped. -/
def Wrap.adv (Wp : Wrap S Out In Out' In') (A : Adv S Out In α) (w : Wp.τ) : Adv S Out' In' α :=
  (Wp.subst A w).bind fun x => .halt x.1

theorem interact_adv (Wp : Wrap S Out In Out' In') (G : World S Out' In')
    (A : Adv S Out In α) (w : Wp.τ) (g : G.σ) :
    (interact (Wp.world G) A (w, g)).map Prod.fst = (interact G (Wp.adv A w) g).map Prod.fst := by
  rw [Wrap.adv, interact_bind, ← interact_subst, PMF.bind_map, PMF.map_bind]
  simp only [Function.comp_def, interact, PMF.pure_map]
  rfl

/-! ### Maps of states -/

/-- A map Φ of states that commutes with all moves, on an invariant that all moves keep, keeps the
law of the output, from every state in the invariant. -/
theorem interact_lump (W₁ W₂ : World S Out In) (Φ : W₁.σ → W₂.σ) (Inv : W₁.σ → Prop)
    (ha : ∀ s o q, Inv s → (W₁.answer s o q).map (Prod.map id Φ) = W₂.answer (Φ s) o q)
    (hr : ∀ s m, Inv s → (W₁.reply s m).map (Prod.map id Φ) = W₂.reply (Φ s) m)
    (ia : ∀ s o q, Inv s → ∀ x ∈ (W₁.answer s o q).support, Inv x.2)
    (ir : ∀ s m, Inv s → ∀ x ∈ (W₁.reply s m).support, Inv x.2)
    (A : Adv S Out In α) :
    ∀ s, Inv s → (interact W₁ A s).map (Prod.map id Φ) = interact W₂ A (Φ s) := by
  induction A with
  | halt a => intro s _; simp only [interact, PMF.pure_map]; rfl
  | sample n k ih => intro s hs; simp only [interact, PMF.map_bind, ih _ s hs]
  | query o q k ih =>
    intro s hs
    simp only [interact, PMF.map_bind]
    rw [← ha s o q hs, PMF.bind_map]
    refine bind_congr_support _ fun x hx => ?_
    exact ih _ _ (ia s o q hs x hx)
  | call m k ih =>
    intro s hs
    simp only [interact, PMF.map_bind]
    rw [← hr s m hs, PMF.bind_map]
    refine bind_congr_support _ fun x hx => ?_
    exact ih _ _ (ir s m hs x hx)

end Rom
