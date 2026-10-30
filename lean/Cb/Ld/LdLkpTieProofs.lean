-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpTieProofs.lean: the proofs of the statements of Cb/Ld/LdLkpTie.lean (the two sides of a
lookup's identity, tied by a chain of sumchecks without variable).

Nothing is defined here that a statement reads.
-/
import Cb.Ld.LdLkpTie
import Cb.Ld.LdLkpTreePProofs
import Cb.Ld.LdPscProofsOur

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp

section
variable {E : Type} [Field E] [Fintype E] (D : TieP E)

theorem LdLkp.TieP.cover : ∀ (l : ℕ) (a : (D.lv l).T.A), a = (D.lv l).nx ∨ a = (D.lv l).pt
  | 0, true => Or.inl rfl
  | 0, false => Or.inr rfl
  | _ + 1, false => Or.inl rfl
  | _ + 1, true => Or.inr rfl

/-- The value that the next step takes up is Q_l. -/
theorem LdLkp.TieP.F_nx :
    ∀ (l : ℕ) (st : (D.lv l).T.St) (m : D.J → E) (X : HPt ((D.lv l).T.vars st)),
      (D.lv l).T.F st (fun j => m ((D.lv l).toJ j)) (D.lv l).nx X = D.Q ((D.lv l).base st) m l
  | 0, _, _, _ => rfl
  | _ + 1, _, _, _ => rfl

theorem LdLkp.TieP.fmt_nil : ∀ l, (D.lv l).T.fmt = []
  | 0 => rfl
  | _ + 1 => rfl

end

section
variable (E : Type) [Field E] [Fintype E]

theorem ldLkpTie_sum0 : Spec.ldLkpTie_sum0 E := by
  intro D x m
  show (D.PK x.2 m - D.Q x.2 m 0 + ∑ b : Empty, (b.elim : E) * (b.elim : E)) +
        ∑ j : D.J, (0 : E) * m j = x.1 ↔
    D.PK x.2 m - D.Q x.2 m 0 = x.1
  simp

theorem ldLkpTie_sum : Spec.ldLkpTie_sum E := by
  intro D l x m h
  show (D.Q ((D.lv (l + 1)).base x.2) m (l + 1) ^ 2 * D.PT ((D.lv (l + 1)).base x.2) m l +
          ∑ b : Empty, (b.elim : E) * (b.elim : E)) +
        ∑ j, (D.lv (l + 1)).T.slS x.2 j * m ((D.lv (l + 1)).toJ j) = x.1 ↔
    D.Q ((D.lv (l + 1)).base x.2) m l + ∑ j, (D.lv (l + 1)).T.slS x.2 j * m ((D.lv (l + 1)).toJ j) =
      x.1
  rw [h, Finset.univ_eq_empty, Finset.sum_empty, add_zero]

theorem ldLkpTie_form : Spec.ldLkpTie_form E := by
  classical
  intro D l o m
  show ∑ j : D.J,
      (if j = (D.lv l).toJ ((D.lv l).T.cAt (D.lv l).nx) then
            (D.lv l).T.lst o.st ((D.lv l).T.par.hp o.st o.pt)
          else 0) * m j = _
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

omit [Fintype E] in
variable {E} in
theorem ldLkpTie_deg3 (v u : Bool → E) :
    ∃ c : Fin (3 + 1) → E, ∀ y : E, (v false + u false * y) ^ 2 * (v true + u true * y) = hev c y :=
  ⟨![v false ^ 2 * v true, 2 * v false * u false * v true + v false ^ 2 * u true, u false ^ 2 * v true + 2 * v false * u false * u true, u false ^ 2 * u true], fun y => by
    simp [hev, Fin.sum_univ_four]
    ring⟩

theorem ldLkpTie_ok : Spec.ldLkpTie_ok E := by
  intro D l
  cases l with
  | zero =>
    refine ⟨fun _ _ hv => absurd hv (List.not_mem_nil),
      fun _ hf => absurd hf (List.not_mem_nil),
      fun _ _ _ => trivial,
      fun _ _ v u r => ⟨![v false - v true, u false - u true], fun y => ?_⟩⟩
    show (v false + u false * y) - (v true + u true * y) + ∑ b : Empty, (b.elim : E) * r b =
      hev ![v false - v true, u false - u true] y
    simp [hev, Fin.sum_univ_two]
    ring
  | succ l =>
    refine ⟨fun _ _ hv => absurd hv (List.not_mem_nil),
      fun _ hf => absurd hf (List.not_mem_nil),
      fun _ _ _ => trivial,
      fun _ _ v u r => ?_⟩
    obtain ⟨c, hc⟩ := ldLkpTie_deg3 v u
    refine ⟨c, fun y => ?_⟩
    show (v false + u false * y) ^ 2 * (v true + u true * y) + ∑ b : Empty, (b.elim : E) * r b =
      hev c y
    rw [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    exact hc y

/-- The row on the value taken up is the next joint's own claim. -/
theorem ldLkpTie_next (D : TieP E) (l : ℕ) (o : (D.lv l).T.par.Out) (m : D.J → E) :
    (D.lv l).T.par.EHolds o (fun j => m ((D.lv l).toJ j)) (D.lv l).nx ↔
    D.claim (l + 1) (D.nxt l o) m := by
  refine (psc_our_val E (D.lv l).T o _ (D.lv l).nx).trans ?_
  have hF : (D.lv l).T.F o.st (fun j => m ((D.lv l).toJ j)) (D.lv l).nx
        ((D.lv l).T.ini o.st ((D.lv l).T.par.hp o.st o.pt)) =
      D.Q ((D.lv l).base o.st) m l :=
    D.F_nx l o.st m _
  show _ ↔ D.Q ((D.lv l).base o.st) m l + ∑ j, (D.lv (l + 1)).T.slS o j * m ((D.lv (l + 1)).toJ j) =
      o.vals (D.lv l).nx
  have h2 := (ldLkpTie_form E D l o m).trans (mul_comm _ _)
  exact ⟨fun h => (congrArg₂ (· + ·) hF.symm h2).trans h,
    fun h => (congrArg₂ (· + ·) hF h2.symm).trans h⟩

theorem ldLkpTie_jt (D : TieP E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → D.J → E)
    (A0 : Rels Kc D.St0 Ex (M × Wp)) (l : ℕ) (hS : D.StepTo l) :
    (D.lv l).T.baseIn (D.ride msg A0 l) (fun w => D.msgAt M msg l w.1) = D.jtAt msg A0 l := by
  have h : ∀ (x : E × (D.lv l).T.St) (m : D.J → E),
      (D.lv l).T.SumHolds x (fun j => m ((D.lv l).toJ j)) ↔ D.claim l x m := by
    cases l with
    | zero => exact ldLkpTie_sum0 E D
    | succ l => exact fun x m => ldLkpTie_sum E D l x m (hS _ m l (Nat.lt_succ_self l))
  exact rels_ext
    (funext fun x =>
      funext fun y => funext fun w => propext (and_congr_right fun _ => h x (msg w.1)))
    (funext fun a => funext fun w => propext (and_congr_right fun _ => h a.1 (msg w.1))) rfl rfl

theorem ldLkpTie_step : Spec.ldLkpTie_step E := by
  intro D Ex M Wp Kc msg A0 l hS
  have ok := ldLkpTie_ok E D l
  have g1 := psc_our_goodAt E (D.lv l).T Ex M Wp Kc (D.ride msg A0 l) (D.msgAt M msg l)
    ok.1 ok.2.2.1 ok.2.2.2 ok.2.1
  rw [ldLkpTie_jt E D Ex M Wp Kc msg A0 l hS] at g1
  refine goodAt_postMap Kc M _ _ _ Ex Ex Wp Wp _ _ _ _ (D.jtAt msg A0 (l + 1)) _ _ (D.nxt l) g1 ?_
    (fun _ _ h => h) (fun _ => rfl) ?_
  · intro o y w h
    exact ⟨⟨h.1, h.2.1, h.2.2 _⟩, (ldLkpTie_next E D l o (msg w.1)).1 (h.2.2 _)⟩
  · intro o y w _ h
    refine ⟨h.1.1, h.1.2.1, fun a => ?_⟩
    rcases D.cover l a with rfl | rfl
    · exact (ldLkpTie_next E D l o (msg w.1)).2 h.2
    · exact h.1.2.2

theorem ldLkpTie_chain : Spec.ldLkpTie_chain E := by
  intro D Ex M Wp Kc msg A0 n hS
  exact ldLkpP_chain Kc M Ex Wp (fun l => E × (D.lv l).T.St) (D.stepA Ex Wp Kc msg)
      (D.jtAt msg A0) n fun l hl =>
    ldLkpTie_step E D Ex M Wp Kc msg A0 l fun st m j hj => hS st m j (Nat.lt_of_lt_of_le hj hl)

theorem ldLkpTie_sig : Spec.ldLkpTie_sig E := by
  intro D S E₀ Wp Kc msg A0 n hS
  exact sigLift_goodB E S Kc _ _ Wp Wp E₀ E₀ _ _ _ _ _ _
    (ldLkpTie_chain E D E₀ S.Msg Wp Kc msg A0 n hS)

theorem ldLkpTie_rounds : Spec.ldLkpTie_rounds E := by
  intro D Ex M Wp Kc msg n
  have hl : ∀ l, (D.stepA Ex Wp Kc msg l).R.shape.length = 3 := fun l => by
    have e : (D.stepA Ex Wp Kc msg l).R.shape = ((D.lv l).T.par.psc Ex).shape := rfl
    rw [e, psc_our_len E (D.lv l).T Ex, D.fmt_nil l]
    rfl
  unfold TieP.tieA
  induction n with
  | zero => simpa [BkA.chain] using hl 0
  | succ n ih =>
    have e : (BkA.chain (fun l => E × (D.lv l).T.St) (D.stepA Ex Wp Kc msg) (n + 1)).R.shape =
        (BkA.chain (fun l => E × (D.lv l).T.St) (D.stepA Ex Wp Kc msg) n).R.shape ++
          (D.stepA Ex Wp Kc msg (n + 1)).R.shape := rfl
    rw [e, List.length_append, ih, hl (n + 1)]
    ring

theorem ldLkpTie_ride : Spec.ldLkpTie_ride E := by
  intro D m
  exact ⟨fun o => psc_our_val E (D.lv 0).T o _ (D.lv 0).pt,
    fun j o => psc_our_val E (D.lv (j + 1)).T o _ (D.lv (j + 1)).pt⟩

end
end Cb
