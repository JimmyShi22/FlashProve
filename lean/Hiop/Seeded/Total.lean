-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/Seeded/Total.lean: the bound of Hiop/Seeded/Form.lean and Hiop/Seeded/Game.lean with the
sessions counted as they are made.

Definitions, statements and proofs. General theorems; this file states no goal of the release.

`BoundsR.err` charges every session that the bounds ALLOW: (sessions allowed on each encoded index,
summed over all of them) · shown · zO. With many encoded indices and a large allowance on each, that
is far more than an adversary with n sessions in all can make. The proof bounds the distance by the
sum of the errors of the runs on the worst path, so it gives more. Here an environment, or an
adversary, makes at most n sessions in all, on every path (`EnvF.SessLe`, `SessLe`), and the error
is
    `errN B n` = (all tests allowed) · zT + (all links allowed) · zL + n · shown · zO.
The allowance of sessions on each encoded index stays in the bounds B: it is what the budget of
reads (`BoundsR.Fits`) and the game's own counter need. n is for the error alone. A call for a
session counts in n whether the game serves it or refuses it.

Main names: `Spec.form_laws_n`, `Spec.game_of_view_n`, `Spec.lifeSeededN`, and their proofs of the
same names. The proofs follow those of `form_laws` (Hiop/Seeded/FormProof.lean), `game_of_view` and
`lifeSeeded` (Hiop/Seeded/GameProof.lean) closely; what is new is the count (`cost_toPlayF_n`).

Limits: those of Hiop/Seeded/Game.lean.
Terms: lean/GLOSSARY.md.

-/
import Hiop.Seeded.GameProof

set_option autoImplicit false

noncomputable section

namespace Hiop.Seeded
open Prob Iop Rom Compile.Lifetime
open scoped ENNReal
open scoped Classical

variable {I X : Type} {L : HolographicProtocol I X} {F : Form X} {S : OSpec} {α : Type}

/-! ## 1. Definitions and statements -/

/-- On every path the environment asks for at most n sessions. -/
def EnvF.SessLe : EnvF L F α → ℕ → Prop
  | .stop _, _ => True
  | .fresh _ k, n => ∀ a, (k a).SessLe n
  | .test _ k, n => ∀ a, (k a).SessLe n
  | .link _ k, n => ∀ a, (k a).SessLe n
  | .session _ _ _ _, 0 => False
  | .session _ _ _ k, n + 1 => ∀ a, (k a).SessLe n
  | .read _ _ k, n => ∀ y, (k y).SessLe n
  | .draw _ _ k, n => ∀ y, (k y).SessLe n

def PreF.SessLe : PreF L F α → ℕ → Prop
  | .stop _, _ => True
  | .first _ E, n => ∀ a, (E a).SessLe n
  | .draw _ _ k, n => ∀ y, (k y).SessLe n

/-- On every path the adversary makes at most n calls for a session. -/
def SessLe : Adv S (GOut L F) (GIn L F) α → ℕ → Prop
  | .halt _, _ => True
  | .sample _ k, n => ∀ r, SessLe (k r) n
  | .query _ _ k, n => ∀ r, SessLe (k r) n
  | .call (.sess _ _ _) _, 0 => False
  | .call (.sess _ _ _) k, n + 1 => ∀ a, SessLe (k a) n
  | .call (.table _) k, n => ∀ a, SessLe (k a) n
  | .call (.test _) k, n => ∀ a, SessLe (k a) n
  | .call (.link _) k, n => ∀ a, SessLe (k a) n
  | .call (.read _ _) k, n => ∀ a, SessLe (k a) n

/-- The error, with n sessions in all. -/
def errN (B : BoundsR) (n : ℕ) (zT zL zO : ℝ≥0∞) : ℝ≥0∞ :=
  B.sum B.tests * zT + B.sum B.links * zL + n * (B.shown * zO)

/-- `ViewNearF` for environments with at most n sessions in all. -/
def ViewNearN (H : HostF L F) (Gs : L.OutOfDomainSeed → Prop) (ok : X → Prop) (B : BoundsR) (n : ℕ)
    (Sim : SimulatorF L F) (z : ℝ≥0∞) : Prop :=
  ∀ (α : Type) (s₀ : L.OutOfDomainSeed) (E : L.Rec → EnvF L F α), Gs s₀ →
    (∀ a, (E a).Adm B Gs ok 0 UsedR.zero) → (∀ a, (E a).SessLe n) →
      tv (H.view s₀ E) (Sim.host.view s₀ E) ≤ z

namespace Spec

def form_laws_n : Prop :=
  ∀ (I X : Type) (L : HolographicProtocol I X) (F : Form X) (Gs : L.OutOfDomainSeed → Prop) (ok : X → Prop)
      (b qT qpar qch qon : ℕ) (zT zL zO : ℝ≥0∞),
    HidE L Gs b →
    ∀ Sm : SimsF L F, Sm.Counts qT qpar qch qon →
      ∀ (W : LawsF L F) (i : I), W.Near Sm Gs i ok zT zL zO →
        ∀ B : BoundsR, B.Fits b qT qpar qch qon →
          ∀ (i₀ : I) (n : ℕ), ViewNearN W.host Gs ok B n (simWholeF L F Sm i₀) (errN B n zT zL zO)

def game_of_view_n : Prop :=
  ∀ (S : OSpec) (I X : Type) (L : HolographicProtocol I X) (F : Form X) (H : HostF L F) (Gs : L.OutOfDomainSeed → Prop)
      (ok : X → Prop) (B : BoundsR) (n : ℕ) (Sim : SimulatorF L F) (z : ℝ≥0∞),
    ViewNearN H Gs ok B n Sim z →
    ∀ (α : Type) (A : Adv S (GOut L F) (GIn L F) α), A.CallsOK (okCall ok) → SessLe A n →
      tv ((interact (gameW H B Gs S) A (none, Table.empty S)).map Prod.fst)
          ((interact (gameW Sim.host B Gs S) A (none, Table.empty S)).map Prod.fst) ≤ z

/-- The real game and the simulated game (Hiop/Seeded/Game.lean), for an adversary with at most n
calls for a session, all of whose instances are in the relation with the index. -/
def lifeSeededN : Prop :=
  ∀ (S : OSpec) (I X : Type) (L : HolographicProtocol I X) (K : Kit L) (Gs : L.OutOfDomainSeed → Prop) (Ryes : I → X → Prop)
      (b qT qpar qch qon : ℕ) (zT zL zO : ℝ≥0∞),
    ReadsG L Gs b qT qpar qch qon →
    ∀ P : RecsG L, P.Ext →
      ∀ Sm : SimsG L, Sm.Good K P Gs Ryes zT zL zO →
        ∀ B : BoundsR, B.Fits b qT qpar qch qon →
          ∀ (i i₀ : I) (n : ℕ) (α : Type) (A : Adv S (GOut L K.form) (GIn L K.form) α),
            A.CallsOK (okCall (Ryes i)) → SessLe A n →
              tv ((interact (gameReal L K P i B Gs S) A (none, Table.empty S)).map Prod.fst)
                  ((interact (gameSim L K Sm i₀ B Gs S) A (none, Table.empty S)).map Prod.fst) ≤
                errN B n zT zL zO

end Spec

/-! ## 2. Proofs -/

theorem EnvF.SessLe.mono (t : EnvF L F α) : ∀ n, t.SessLe n → t.SessLe (n + 1) := by
  induction t with
  | stop a => intro _ _; exact trivial
  | fresh s k ih => intro n h a; exact ih a n (h a)
  | test e k ih => intro n h a; exact ih a n (h a)
  | link e k ih => intro n h a; exact ih a n (h a)
  | session e q hq k ih =>
    intro n h
    cases n with
    | zero => exact h.elim
    | succ m => exact fun a => ih a m (h a)
  | read e p k ih => intro n h y; exact ih y n (h y)
  | draw β d k ih => intro n h y; exact ih y n (h y)

theorem PreF.SessLe.mono (t : PreF L F α) : ∀ n, t.SessLe n → t.SessLe (n + 1) := by
  induction t with
  | stop a => intro _ _; exact trivial
  | first s₀ E => intro n h a; exact EnvF.SessLe.mono (E a) n (h a)
  | draw β d k ih => intro n h y; exact ih y n (h y)

section Cost
variable {B : BoundsR} {Gs : L.OutOfDomainSeed → Prop} {ok : X → Prop}

theorem cost_toPlayF_n {zT zL zO : ℝ≥0∞} (t : EnvF L F α) :
    ∀ (c : ℕ) (g : ℕ → L.OutOfDomainSeed) (u : UsedR) (n : ℕ), t.Adm B Gs ok c u → c ≤ B.nenc → t.SessLe n →
      (toPlayF B.nenc t c g).cost (errF zT zL zO) ≤
        (leftR B B.tests u.tests : ℝ≥0∞) * zT + (leftR B B.links u.links : ℝ≥0∞) * zL +
          (n : ℝ≥0∞) * (B.shown * zO) := by
  induction t with
  | stop a => intro c g u n _ _ _; exact zero_le _
  | draw β d k ih =>
    intro c g u n h hc hn
    simp only [toPlayF, Play.cost_draw]
    exact iSup_le fun y => ih y c g u n (h y) hc (hn y)
  | fresh s k ih =>
    intro c g u n h hc hn
    simp only [toPlayF, Play.cost_call]
    refine (add_le_add (le_refl _)
      (iSup_le fun a => ih a (c + 1) _ u n (h.2.2 a) h.2.1 (hn a))).trans (le_of_eq ?_)
    show (0 : ℝ≥0∞) + _ = _
    rw [zero_add]
  | read e p k ih =>
    intro c g u n h hc hn
    simp only [toPlayF, Play.cost_call]
    refine (add_le_add (le_refl _)
      (iSup_le fun y => ih y c g _ n (h.2.2 y) hc (hn y))).trans (le_of_eq ?_)
    show (0 : ℝ≥0∞) + _ = _
    rw [zero_add]
  | test e k ih =>
    intro c g u n h hc hn
    obtain ⟨he, hs, h3⟩ := h
    simp only [toPlayF, Play.cost_call]
    refine (add_le_add (le_refl _)
      (iSup_le fun a => ih a c g _ n (h3 a) hc (hn a))).trans (le_of_eq ?_)
    show zT + ((leftR B B.tests (bump u.tests e) : ℝ≥0∞) * zT + _ + _) = _
    rw [leftR_step (he.trans hc) hs]
    push_cast
    ring
  | link e k ih =>
    intro c g u n h hc hn
    obtain ⟨-, he, hs, h3⟩ := h
    simp only [toPlayF, Play.cost_call]
    refine (add_le_add (le_refl _)
      (iSup_le fun a => ih a c g _ n (h3 a) hc (hn a))).trans (le_of_eq ?_)
    show zL + (_ + (leftR B B.links (bump u.links e) : ℝ≥0∞) * zL + _) = _
    rw [leftR_step (he.trans hc) hs]
    push_cast
    ring
  | session e q hq k ih =>
    intro c g u n h hc hn
    obtain ⟨he, hs, hJ, -, h6⟩ := h
    cases n with
    | zero => exact hn.elim
    | succ m =>
      simp only [toPlayF, Play.cost_call]
      have h2 : errF zT zL zO
          (.bat (nm B.nenc e, g e) e q hq : FCall (Row L B.nenc) F L.wordLength) ≤ B.shown * zO :=
        mul_le_mul' (Nat.cast_le.2 hJ) le_rfl
      refine (add_le_add h2
        (iSup_le fun a => ih a c g _ m (h6 a) hc (hn a))).trans (le_of_eq ?_)
      show (B.shown : ℝ≥0∞) * zO +
          ((leftR B B.tests u.tests : ℝ≥0∞) * zT + (leftR B B.links u.links : ℝ≥0∞) * zL +
            (m : ℝ≥0∞) * (B.shown * zO)) = _
      push_cast
      ring

end Cost

theorem form_laws_n : Spec.form_laws_n := by
  intro I X L F Gs ok b qT qpar qch qon zT zL zO hR Sm hC W i hN B hB i₀ n α s₀ E h0 hE hn
  rw [simHostF_eq, viewF_eq _ s₀ E hE, viewF_eq _ s₀ E hE]
  refine (lifetimeF hR hC hN i₀ Prod.snd (wholeF B.nenc s₀ E)
    ⟨h0, fun a => calls_toPlayF (E a) 0 _ _ (hE a) fun _ _ => h0⟩ ?_).trans ?_
  · intro a
    refine fits_toPlayF (E a) 0 _ _ _ (hE a) (Nat.zero_le _) fun j hj s => ?_
    have h := hB j hj
    show 0 + 0 + (B.tests j - 0) * qT + (if j = 0 then leftR B B.links (fun _ => 0) * qpar else 0) +
        (B.links j - 0) * qch + (B.sess j - 0) * qon + (B.reads j - 0) ≤ b
    rw [leftR_zero]
    simp only [Nat.sub_zero]
    omega
  · unfold wholeF
    rw [Play.cost_call]
    refine (add_le_add (le_refl _)
        (iSup_le fun a => cost_toPlayF_n (E a) 0 _ _ n (hE a) (Nat.zero_le _) (hn a))).trans
      (le_of_eq ?_)
    show (0 : ℝ≥0∞) +
        ((leftR B B.tests (fun _ => 0) : ℝ≥0∞) * zT + (leftR B B.links (fun _ => 0) : ℝ≥0∞) * zL +
          (n : ℝ≥0∞) * (B.shown * zO)) = _
    rw [zero_add, leftR_zero, leftR_zero]
    rfl

theorem ViewNearN.pre {H : HostF L F} {Gs : L.OutOfDomainSeed → Prop} {ok : X → Prop} {B : BoundsR} {n : ℕ}
    {Sim : SimulatorF L F} {z : ℝ≥0∞} (h : ViewNearN H Gs ok B n Sim z) (t : PreF L F α)
    (ht : t.Adm B Gs ok) (hn : t.SessLe n) : tv (t.run H) (t.run Sim.host) ≤ z := by
  induction t with
  | stop a =>
    show tv (PMF.pure a) (PMF.pure a) ≤ z
    rw [tv_self]
    exact zero_le z
  | first s₀ E => exact h α s₀ E ht.1 ht.2 hn
  | draw β d k ih => exact tv_bind_right_le_of_forall d _ _ fun y _ => ih y (ht y) (hn y)

section Count
variable {B : BoundsR} {Gs : L.OutOfDomainSeed → Prop}

theorem sessLe_envOf (A : Adv S (GOut L F) (GIn L F) α) :
    ∀ (c : ℕ) (u : UsedR) (T : Table S) (n : ℕ), SessLe A n → (envOf B Gs A c u T).SessLe n := by
  induction A with
  | halt a => intro _ _ _ _ _; exact trivial
  | sample m k ih => intro c u T n hA r; exact ih r c u T n (hA r)
  | query o q k ih => intro c u T n hA y; exact ih y.1 c u y.2 n (hA y.1)
  | call m k ih =>
    intro c u T n hA
    cases m with
    | table s =>
      by_cases h : Gs s ∧ c < B.nenc
      · simp only [envOf, if_pos h]
        exact fun a => ih _ _ _ _ n (hA _)
      · simp only [envOf, if_neg h]
        exact ih _ _ _ _ n (hA _)
    | test e =>
      by_cases h : e ≤ c ∧ u.tests e < B.tests e
      · simp only [envOf, if_pos h]
        exact fun a => ih _ _ _ _ n (hA _)
      · simp only [envOf, if_neg h]
        exact ih _ _ _ _ n (hA _)
    | link e =>
      by_cases h : 1 ≤ e ∧ e ≤ c ∧ u.links e < B.links e
      · simp only [envOf, if_pos h]
        exact fun a => ih _ _ _ _ n (hA _)
      · simp only [envOf, if_neg h]
        exact ih _ _ _ _ n (hA _)
    | sess e q hq =>
      cases n with
      | zero => exact hA.elim
      | succ j =>
        by_cases h : e ≤ c ∧ u.sess e < B.sess e ∧ F.wt q ≤ B.shown
        · simp only [envOf, if_pos h]
          exact fun a => ih _ _ _ _ j (hA _)
        · simp only [envOf, if_neg h]
          exact EnvF.SessLe.mono _ j (ih _ _ _ _ j (hA _))
    | read e p =>
      by_cases h : e ≤ c ∧ u.reads e < B.reads e
      · simp only [envOf, if_pos h]
        exact fun y => ih _ _ _ _ n (hA _)
      · simp only [envOf, if_neg h]
        exact ih _ _ _ _ n (hA _)

theorem sessLe_preOf (A : Adv S (GOut L F) (GIn L F) α) :
    ∀ (T : Table S) (n : ℕ), SessLe A n → (preOf B Gs A T).SessLe n := by
  induction A with
  | halt a => intro _ _ _; exact trivial
  | sample m k ih => intro T n hA r; exact ih r T n (hA r)
  | query o q k ih => intro T n hA y; exact ih y.1 y.2 n (hA y.1)
  | call m k ih =>
    intro T n hA
    cases m with
    | table s =>
      by_cases h : Gs s
      · simp only [preOf, if_pos h]
        exact fun a => sessLe_envOf _ _ _ _ n (hA _)
      · simp only [preOf, if_neg h]
        exact ih _ _ n (hA _)
    | test e => simp only [preOf]; exact ih _ _ n (hA _)
    | link e => simp only [preOf]; exact ih _ _ n (hA _)
    | sess e q hq =>
      cases n with
      | zero => exact hA.elim
      | succ j =>
        simp only [preOf]
        exact PreF.SessLe.mono _ j (ih _ _ j (hA _))
    | read e p => simp only [preOf]; exact ih _ _ n (hA _)

end Count

theorem game_of_view_n : Spec.game_of_view_n := by
  intro S I X L F H Gs ok B n Sim z hV α A hA hn
  rw [run_preOf, run_preOf]
  exact hV.pre _ (adm_preOf A _ hA) (sessLe_preOf A _ n hn)

theorem lifeSeededN : Spec.lifeSeededN := by
  intro S I X L K Gs Ryes b qT qpar qch qon zT zL zO hR P hX Sm hS B hB i i₀ n α A hA hn
  exact game_of_view_n S I X L K.form (realLawsG L K P i).host Gs (Ryes i) B n
    (simWholeF L K.form (simsFG L K Sm) i₀) (errN B n zT zL zO)
    (form_laws_n I X L K.form Gs (Ryes i) b qT qpar qch qon zT zL zO hR.hidE (simsFG L K Sm)
      (counts_simsFG hR K Sm) (realLawsG L K P i) i (near_realG hX hS i) B hB i₀ n) α A hA hn

end Hiop.Seeded

#print axioms Hiop.Seeded.form_laws_n
#print axioms Hiop.Seeded.game_of_view_n
#print axioms Hiop.Seeded.lifeSeededN
