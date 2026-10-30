-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdPscProofsOur.lean: proofs for Cb/Ld/LdPsc.lean, third part: the instance with one dummy last
variable (`Spec.psc_our_sum` to `Spec.psc_our_card`).

Lemmas:
  `hSumAll_snoc`, `HDeg_snoc`, `mem_pVars_snoc`, `hLast_val`: sums, degrees, variables and
    challenges of a list of variables with one more at the end.
-/
import Cb.Ld.LdPscProofsIor

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

section Snoc
variable {E : Type} [Field E]

theorem hSumAll_snoc :
    ∀ (l : List (PFmt E)) (d : PDats l) (f : PFmt E) (e : PDat E f) (h : HPt (pVars l d) → E → E),
      hSumAll (pVars (l ++ [f]) (PDats.snoc l d f e))
          (fun X => h (hInit l d f e X) (hLast l d f e X)) =
        hSumAll (pVars l d) fun X => (f.var e).sum (h X) := by
  intro l
  induction l with
  | nil => intro d f e h; rfl
  | cons f0 l ih =>
      intro d f e h
      exact congrArg (f0.var d.1).sum (funext fun x => ih d.2 f e fun X y => h (x, X) y)

theorem HDeg_snoc :
    ∀ (l : List (PFmt E)) (d : PDats l) (f : PFmt E) (e : PDat E f) (h : HPt (pVars l d) → E → E),
      (∀ y, HDeg (pVars l d) fun X => h X y) →
      (∀ X, ∃ c : Fin (f.n + 1) → E, ∀ y, h X y = hev c y) →
      HDeg (pVars (l ++ [f]) (PDats.snoc l d f e)) fun X =>
        h (hInit l d f e X) (hLast l d f e X) := by
  intro l
  induction l with
  | nil => intro d f e h _ h2; exact ⟨fun _ => h2 (), fun _ => trivial⟩
  | cons f0 l ih =>
      intro d f e h h1 h2
      exact ⟨fun xs => (h1 (hLast l d.2 f e xs)).1 (hInit l d.2 f e xs),
        fun x => ih d.2 f e (fun X y => h (x, X) y) (fun y => (h1 y).2 x) fun X => h2 (x, X)⟩

omit [Field E] in
theorem mem_pVars_snoc :
    ∀ (l : List (PFmt E)) (d : PDats l) (f : PFmt E) (e : PDat E f) (v : HVar E),
      v ∈ pVars (l ++ [f]) (PDats.snoc l d f e) → v ∈ pVars l d ∨ v = f.var e := by
  intro l
  induction l with
  | nil => intro d f e v hv; exact Or.inr (List.mem_singleton.1 hv)
  | cons f0 l ih =>
      intro d f e v hv
      rcases List.mem_cons.1 hv with h | h
      · exact Or.inl (h ▸ List.mem_cons_self)
      · exact (ih d.2 f e v h).imp (List.mem_cons_of_mem _) id

theorem hLast_val :
    ∀ (l : List (PFmt E)) (d : PDats l) (f : PFmt E) (e : PDat E f) (ρ : Rho (pRounds (l ++ [f]))),
      ∃ c : f.Ch,
        hLast l d f e (pH (l ++ [f]) (PDats.snoc l d f e) (pG (l ++ [f]) ρ)) = f.val c := by
  intro l
  induction l with
  | nil => intro d f e ρ; exact ⟨ρ.1, rfl⟩
  | cons f0 l ih => intro d f e ρ; exact ih d.2 f e ρ.2

variable [Fintype E]

theorem pDummy_sum (D : ℕ) (g : E → E) : ((pDummy E D).var (pDummyD E D)).sum g = g 0 := by
  show ∑ _s : Unit, (1 : E) • g 0 = g 0
  simp

theorem pDummy_ok (D : ℕ) : ((pDummy E D).var (pDummyD E D)).OK := by
  show ((pDummy E D).var (pDummyD E D)).sum
      (hev fun t : Fin (D + 1) => if t = 0 then (1 : E) else 0) = 1
  rw [pDummy_sum, hev_const]

end Snoc

section Main
variable (E : Type) [Field E] [Fintype E]

theorem psc_our_sum : Spec.psc_our_sum E := by
  intro T x m
  have key : hSumAll (T.par.vars x.2) (T.par.sum x.2 m) = hSumAll (T.vars x.2) (T.sum x.2 m) := by
    refine (hSumAll_snoc T.fmt (T.dat x.2) (pDummy E T.DY) (pDummyD E T.DY) fun X y =>
      T.S0 x.2 X (fun a => T.F x.2 m a X + m (T.cAt a) * y) +
        ∑ b, T.S1 x.2 X (fun a => T.F x.2 m a X + m (T.cAt a) * y) b * T.Fb x.2 m b X).trans ?_
    refine congrArg _ (funext fun X => ?_)
    rw [pDummy_sum]
    unfold PscOur.sum
    simp only [mul_zero, add_zero]
  unfold PscPar.SumHolds PscOur.SumHolds
  rw [key]
  exact Iff.rfl

theorem psc_our_ok : Spec.psc_our_ok E := by
  intro T
  refine ⟨fun h st v hv => ?_, fun h f hf => ?_⟩
  · rcases mem_pVars_snoc T.fmt (T.dat st) (pDummy E T.DY) (pDummyD E T.DY) v hv with h1 | h1
    · exact h st v h1
    · rw [h1]; exact pDummy_ok T.DY
  · rcases List.mem_append.1 hf with h1 | h1
    · exact h f h1
    · rw [List.mem_singleton.1 h1]; exact Subtype.val_injective

theorem psc_our_deg : Spec.psc_our_deg E := fun T hX hY st m =>
  HDeg_snoc T.fmt (T.dat st) (pDummy E T.DY) (pDummyD E T.DY)
    (fun X y =>
      T.S0 st X (fun a => T.F st m a X + m (T.cAt a) * y) +
        ∑ b, T.S1 st X (fun a => T.F st m a X + m (T.cAt a) * y) b * T.Fb st m b X)
    (fun y => hX st m fun a => m (T.cAt a) * y)
    fun X => hY st X (fun a => T.F st m a X) (fun a => m (T.cAt a)) fun b => T.Fb st m b X

theorem psc_our_val : Spec.psc_our_val E := fun _ _ _ _ => Iff.rfl

theorem psc_our_next : Spec.psc_our_next E := by
  classical
  intro T T' ι o m a st' hF hS
  have hs : ∑ j, T'.slS st' j * m (ι j) = m (T.cAt a) * T.lst o.st (T.par.hp o.st o.pt) := by
    simp only [hS]
    rw [Equiv.sum_comp ι fun i =>
        (if i = T.cAt a then T.lst o.st (T.par.hp o.st o.pt) else 0) * m i]
    simp [mul_comm]
  show T.F o.st m a (T.ini o.st (T.par.hp o.st o.pt)) +
        m (T.cAt a) * T.lst o.st (T.par.hp o.st o.pt) = o.vals a ↔
    hSumAll (T'.vars st') (T'.sum st' fun j => m (ι j)) + ∑ j, T'.slS st' j * m (ι j) = o.vals a
  rw [hs, hF]

theorem psc_our_nz : Spec.psc_our_nz E := by
  intro T x τ z hz
  unfold PscPar.outC at hz
  split at hz
  · obtain rfl := Option.some.inj hz
    obtain ⟨c, hc⟩ := hLast_val T.fmt (T.dat x.2) (pDummy E T.DY) (pDummyD E T.DY) τ.rho.2
    show hLast T.fmt (T.dat x.2) (pDummy E T.DY) (pDummyD E T.DY) (pH _ _ (pG _ τ.rho.2)) ≠ 0
    rw [hc]
    exact c.2
  · exact absurd hz (by simp)

theorem psc_our_degs : Spec.psc_our_degs E := fun T => by
  show (T.fmt ++ [pDummy E T.DY]).map PFmt.n = _
  rw [List.map_append]
  rfl

theorem psc_our_len : Spec.psc_our_len E := fun T Ex => by
  rw [psc_len E T.par Ex]
  show (T.fmt ++ [pDummy E T.DY]).length + 2 = _
  simp

theorem psc_our_card : Spec.psc_our_card E := fun D => by
  classical
  show Fintype.card {x : E // x ≠ 0} = _
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]

end Main
end Cb
