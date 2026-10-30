-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegCloseProofs.lean: the proofs of the statements of Cb/Req1/LdSegClose.lean (the first
half of a closing as lists of moves).
Named tools: `ldStepF_hyp` (what a step that only maps the explicit part has to meet), `bat_zero` (a
combination of forms that vanish at an entry vanishes there), `all_one` (a family of claims with one
name is the claim). Nothing is defined here that a statement reads.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegClose
import Cb.Ld.LdBatPeelProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Ood IOR

theorem ldStepF_hyp {E Kc : Type} [Field E] [Fintype E] (S : Sig E) {St St' Wp : Type}
    {E₀ : ExtSpec} (A : IOR.Rels Kc St E₀ (S.Msg × Wp)) (A' : IOR.Rels Kc St' E₀ (S.Msg × Wp))
    (f : St → St') (hfw : ∀ st y w, A.rel st y w → A'.rel (f st) y w)
    (hon : ∀ st y, A.on (st, y) → A'.on (f st, y)) (hcore : ∀ w, A'.core w = A.core w)
    (hbw : ∀ st y w, A.on (st, y) → A'.relR (f st, y) w → A.relR (st, y) w) :
    (ldStepF S A A' f).Hyp :=
  ldPeel_cf _ _ _ _ _ _ _ _ _ _ _ _ _
    (ldPeel_base E Kc St St' Wp Wp S E₀ E₀ A A' f (ExtMap.id E₀) (fun _ w => w.2) (fun _ w => w.2)
      (extMap_isLocal.1 E₀) hfw hon (fun _ w => hcore w) hbw)

theorem bat_zero {E J B D : Type} [Field E] [Fintype B] {Sb : B → Type} (Z : D → B → E)
    (sl : ∀ b, Slf E (Sb b) J) (n : J) (h : ∀ b st, sl b st n = 0) (x : (∀ b, Sb b) × D) :
    Slf.bat Z sl x n = 0 :=
  Finset.sum_eq_zero fun b _ => by rw [h b, zero_mul]

theorem all_one {E St J : Type} [Field E] [Fintype J] (sl : Slf E St J) (x : E × St) (u : J → E) :
    Slf.All (fun _ : Unit => sl) (oneClaim x) u ↔ sl.Holds x u :=
  ⟨fun h => h (), fun h _ => h⟩

theorem ldSegCl_one : Spec.ldSegCl_one := by
  intro E Kc _ _ D l hZ hs hl
  have hi : ∀ (x : E × D.Sx) (m : D.S.Msg),
      Slf.All (fun _ : Unit => D.row.onG D.G) (oneClaim x) (D.G.msg m) ↔
      D.row.Holds x (D.S.ents m) := by
    intro x m
    rw [all_one]
    have e := ldPeel_onG E D.S D.G D.Sx D.row x.2 m fun n hn =>
      bat_zero D.Z.ze D.sl n (fun b st => hs b st n hn) x.2
    exact ⟨fun h => e.symm.trans h, fun h => e.trans h⟩
  suffices key : ((True ∧ (LdMv.bat D.bat).Hyp) ∧ D.step.Hyp) ∧ (LdMv.fold D.fold l).Hyp by
    simpa only [LdCl1.prog, LdProg.Hyp] using key
  refine ⟨⟨⟨trivial, hZ⟩, ?_⟩, hl⟩
  exact ldStepF_hyp D.S _ _ _ (fun st y w h => ⟨(hi st.1 w.1).2 h.1, h.2⟩) (fun _ _ h => h)
    (fun _ => rfl) fun st y w _ h => ⟨(hi st.1 w.1).1 h.1, h.2⟩

theorem ldSegCl_two : Spec.ldSegCl_two := by
  intro E Kc _ _ D F l₁ l₂ hZ hF h₁ h₂
  have hrow0 : ∀ (n : D.S.Ent), (∀ b st, D.sl b st n = 0) → ∀ x, D.row x n = 0 := fun n h x =>
    bat_zero D.Z.ze D.sl n h x
  -- stepA
  have hA : ∀ (x : E × D.Sx) (m : D.S.Msg),
      splitIn D.sl₁ D.sl₂ (x.1, (x.2, x.2)) m ↔ D.row.Holds x (D.S.ents m) := by
    intro x m
    have e := ldPeel_two E D.S D.G₁ D.G₂ D.Sx D.row x.2 m fun n h1 h2 =>
      hrow0 n (fun b st => hF.supp b st n h1 h2) x.2
    exact ⟨fun h => e.symm.trans h, fun h => e.trans h⟩
  -- stepB
  have hB : ∀ (x : E × D.Sx) (m : D.S.Msg),
      Slf.All (fun _ : Unit => D.r₂.toSub D.kp₁) (oneClaim x)
        ((D.G₂.sub D.kp₁).msg (D.S.res (T := OMsg.Msg) D.kp₁ m)) ↔
      D.r₂.Holds x (D.G₂.msg m) := by
    intro x m
    rw [all_one]
    have e := ldPeel_toSub E D.S D.G₂ D.kp₁ D.Sx D.r₂ x.2 m hF.kept
    exact ⟨fun h => e.symm.trans h, fun h => e.trans h⟩
  -- stepC
  have hres : ∀ (m : D.S₂.Msg) (u : ∀ k, (D.fold₁.held.o k).Msg),
      (D.S.sub D.kp₁).res (T := OMsg.Msg) (fun a => ¬ D.cl a) (D.fold₁.rd m u) = m := by
    intro m u
    funext a
    show (if h : D.cl a.1 then u ⟨a.1, h⟩ else m ⟨a.1, h⟩) = m a
    rw [dif_neg a.2]
  have hC : ∀ (x : D.Cl) (m : D.S₂.Msg) (u : ∀ k, (D.fold₁.held.o k).Msg),
      Slf.All (fun _ : Unit => D.r₂') x (D.G₂'.msg m) ↔
      Slf.All (fun _ : Unit => D.r₂.toSub D.kp₁) x ((D.G₂.sub D.kp₁).msg (D.fold₁.rd m u)) := by
    intro x m u
    have e := ldPeel_toSub E (D.S.sub D.kp₁) (D.G₂.sub D.kp₁) (fun a => ¬ D.cl a) D.Sx
      (D.r₂.toSub D.kp₁) (x.2 ()) (D.fold₁.rd m u) hF.free
    rw [hres m u] at e
    exact ⟨fun h _ => e.symm.trans (h ()), fun h _ => e.trans (h ())⟩
  suffices key : ((((True ∧ (LdMv.bat D.bat).Hyp) ∧ D.stepA.Hyp) ∧ (LdMv.split D.spl).Hyp) ∧
        D.stepB.Hyp) ∧
      (((True ∧ (LdMv.fold D.fold₁ l₁).Hyp) ∧ F.stepC.Hyp) ∧ (LdMv.fold F.fold₂ l₂).Hyp) by
    simpa only [LdCl2.progBat, LdCl2b.progFold, LdProg.Hyp] using key
  refine ⟨⟨⟨⟨⟨trivial, hZ⟩, ?_⟩, ?_⟩, ?_⟩, ⟨⟨trivial, h₁⟩, ?_⟩, h₂⟩
  · exact ldStepF_hyp D.S _ _ _ (fun st y w h => ⟨(hA st.1 w.1).2 h.1, h.2⟩) (fun _ _ h => h)
      (fun _ => rfl) fun st y w _ h => ⟨(hA st.1 w.1).1 h.1, h.2⟩
  · refine ⟨fun st => hrow0 _ hF.own st, fun st => if_pos D.k.h₁,
      fun st n hn => hrow0 _ (fun b s => hF.rd b s _ hn) st, fun st n hn => ?_, hF.rdK⟩
    show (if D.G₁.mem (D.G₂.ent n).1 then 0 else D.row st (D.G₂.ent n)) = 0
    rw [hrow0 _ (fun b s => hF.rd b s _ hn) st, ite_self]
  · exact ldStepF_hyp D.S _ _ _
      (fun st y w h => ⟨(all_one _ _ _).2 h.1.1, (hB st.1.2 w.1).2 h.1.2, h.2⟩) (fun _ _ h => h)
      (fun _ => rfl) fun st y w _ h => ⟨⟨(all_one _ _ _).1 h.1, (hB st.1.2 w.1).1 h.2.1⟩, h.2.2⟩
  · refine ldStepF_hyp D.S₂ _ _ _ (fun st y w h => ⟨(hC st.2.1 w.1 _).2 h.2.2.1, h.1, h.2.1, ?_⟩)
      (fun _ _ h => h) (fun w => ?_) fun st y w _ h => ⟨h.2.1, h.2.2.1, (hC st.2.1 w.1 _).1 h.1, ?_⟩
    · have h3 := h.2.2.2
      show D.A₀.rel st.2.2 y.2
        (F.rd' (D.S₂.res (T := OMsg.Msg) F.kp₂ w.1) (D.fold₁.held.msg w.2.1.1), w.2.2)
      rw [← hF.hρ]
      exact h3
    · show D.A₀.core
          (F.rd' (D.S₂.res (T := OMsg.Msg) F.kp₂ w.1) (D.fold₁.held.msg w.2.1.1), w.2.2) =
        D.A₀.core (D.ρ (D.fold₁.rd w.1 (D.fold₁.held.msg w.2.1.1)), w.2.2)
      rw [hF.hρ]
    · have h3 := h.2.2.2
      show D.A₀.relR (st.2.2, y.2) (D.ρ (D.fold₁.rd w.1 (D.fold₁.held.msg w.2.1.1)), w.2.2)
      rw [hF.hρ]
      exact h3

theorem ldSegCl_kinds : Spec.ldSegCl_kinds := by
  intro E Kc _ _ D F l₁ l₂
  constructor
  · simp only [LdCl2.progBat, LdProg.All]
    exact ⟨⟨⟨⟨trivial, Or.inl rfl⟩, Or.inr (Or.inr rfl)⟩, Or.inr (Or.inl rfl)⟩, Or.inr (Or.inr rfl)⟩
  · simp only [LdCl2b.progFold, LdProg.All]
    exact ⟨⟨⟨trivial, Or.inl rfl⟩, Or.inr rfl⟩, Or.inl rfl⟩

end Cb
