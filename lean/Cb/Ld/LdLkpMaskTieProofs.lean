-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpMaskTieProofs.lean: proofs for Cb/Ld/LdLkpMaskTie.lean.

Main names (statements and hypotheses: Cb/Ld/LdLkpMaskTie.lean):
  `ldLkpMaskTie_own`: the places (`D.ownAt`), written out.
  `ldLkpMaskTie_link`: see its statement in Cb/Ld/LdLkpMaskTie.lean.
  `ldLkpMaskTie_mm`: see its statement in Cb/Ld/LdLkpMaskTie.lean.
  `ldLkpMaskTie_sound`: it speaks of the honest run of the tie; it says nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpMaskTie
import Cb.Ld.LdLkpTieProofs
import Cb.Ld.LdLkpFormatAsm

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp

section
variable (E : Type) [Field E] [Fintype E]

/-- Under `hO`: the messages of the sumcheck over the chain's entries read RdT only. -/
theorem mjOur_reads (T : PscOur E) (Ex : ExtSpec) (J : Type) (e : T.J ≃ J)
    (Rd RdT : J → Prop) (hO : T.OwnOur fun j' => RdT (e j')) : (T.mjJ Ex e Rd).MReads RdT :=
  fun _ _ x ρ hk =>
    (mjPsc_reads E T.par Ex (T.own fun j' => Rd (e j'))
        (T.own fun j' => RdT (e j')) (psc_our_own E T _ hO)).msg
      _ _ x ρ fun j' hj => hk (e j') hj

theorem ldLkpMaskTie_own : Spec.ldLkpMaskTie_own E := by
  intro D j
  refine ⟨⟨?_, ?_⟩, fun l => ⟨?_, ?_⟩⟩
  · rintro ⟨i | b, h⟩
    · exact Or.inl ⟨i, h⟩
    · exact Or.inr ⟨b, h⟩
  · rintro (⟨i, h⟩ | ⟨b, h⟩)
    · exact ⟨.inl i, h⟩
    · exact ⟨.inr b, h⟩
  · rintro ⟨i | b, h⟩
    · exact Or.inl ⟨i, h⟩
    · exact Or.inr ⟨b, h⟩
  · rintro (⟨i, h⟩ | ⟨b, h⟩)
    · exact ⟨.inl i, h⟩
    · exact ⟨.inr b, h⟩

variable {E}

/-- The place of the mask that the next step's form reads is an own place of this step. -/
theorem LdLkp.TieP.inc_own (D : TieP E) (l : ℕ) :
    D.ownAt l ((D.lv l).toJ ((D.lv l).T.cAt (D.lv l).nx)) :=
  ⟨.inr (D.lv l).nx, rfl⟩

theorem LdLkp.TieP.sr_own (D : TieP E) {n : ℕ} {Dt : D.J → Prop} (h : D.MaskOK n Dt) {l l' : ℕ}
    (h1 : l < l') (h2 : l' ≤ n) (j : D.J) (hj : D.srAt Dt l j) : ¬ D.ownAt l' j := by
  rcases hj with hj | ⟨l'', hl, hj⟩
  · exact h.dt l' h2 j hj
  · exact h.disj l'' l' (Nat.lt_of_le_of_lt hl h1) h2 j hj

/-- Under `h`: the conditions `OwnOur` of the item "masked messages" (`Honest.MM`, Ior/Masked.lean),
at the set `D.srAt Dt l`, hold at every step l ≤ n. -/
theorem LdLkp.TieP.own_our (D : TieP E) {n : ℕ} {Dt : D.J → Prop} (h : D.MaskOK n Dt) :
    ∀ l ≤ n, (D.lv l).T.OwnOur fun j' => D.srAt Dt l (D.eJ l j')
  | 0, hl => by
      refine ⟨h.inj 0 hl, fun i => Or.inr ⟨0, le_refl 0, i, rfl⟩, fun st m m' hm => ?_,
        fun _ _ _ _ => funext fun b => b.elim, fun _ _ _ => rfl, fun st m m' hm => ?_,
        fun _ _ _ _ => funext fun b => b.elim, fun _ _ => rfl⟩
      · obtain ⟨a1, -, a3⟩ := h.rd st m m' fun j hj => hm j (Or.inl hj)
        funext (b : Bool) X
        show (if b then D.Q st m 0 else D.PK st m) = if b then D.Q st m' 0 else D.PK st m'
        rw [a1, a3]
      · obtain ⟨a1, -, a3⟩ := h.rd st m m' fun j hj => hm j fun i hi => h.dt 0 hl j hj ⟨i, hi⟩
        funext (b : Bool) X
        show (if b then D.Q st m 0 else D.PK st m) = if b then D.Q st m' 0 else D.PK st m'
        rw [a1, a3]
  | l + 1, hl => by
      classical
      refine ⟨h.inj (l + 1) hl, fun i => Or.inr ⟨l + 1, le_refl _, i, rfl⟩, fun st m m' hm => ?_,
        fun _ _ _ _ => funext fun b => b.elim, fun st j hj => ?_, fun st m m' hm => ?_,
        fun _ _ _ _ => funext fun b => b.elim, fun st i => ?_⟩
      · obtain ⟨-, a2, a3⟩ := h.rd ((D.lv l).base st.st) m m' fun j hj => hm j (Or.inl hj)
        funext (b : Bool) X
        show (if b then D.PT ((D.lv l).base st.st) m l else D.Q ((D.lv l).base st.st) m (l + 1)) =
          if b then D.PT ((D.lv l).base st.st) m' l else D.Q ((D.lv l).base st.st) m' (l + 1)
        rw [a2, a3]
      · exact if_neg fun e =>
          hj (Or.inr
              ⟨l, Nat.le_succ l, by rw [show D.eJ (l + 1) j = j from rfl, e]; exact D.inc_own l⟩)
      · obtain ⟨-, a2, a3⟩ :=
          h.rd ((D.lv l).base st.st) m m' fun j hj => hm j fun i hi => h.dt (l + 1) hl j hj ⟨i, hi⟩
        funext (b : Bool) X
        show (if b then D.PT ((D.lv l).base st.st) m l else D.Q ((D.lv l).base st.st) m (l + 1)) =
          if b then D.PT ((D.lv l).base st.st) m' l else D.Q ((D.lv l).base st.st) m' (l + 1)
        rw [a2, a3]
      · exact if_neg fun e => h.disj l (l + 1) (Nat.lt_succ_self l) hl _ (D.inc_own l) ⟨i, e.symm⟩

variable (E)

theorem ldLkpMaskTie_link : Spec.ldLkpMaskTie_link E := by
  intro D Ex M Wp Kc msg n Dt Rd C hS hM hRd hC hCs
  have hreads : ∀ l ≤ n, (D.mjAt Ex Rd l).MReads (D.srAt Dt l) := fun l hl =>
    mjOur_reads E (D.lv l).T Ex D.J (D.eJ l) Rd (D.srAt Dt l) (D.own_our hM l hl)
  refine mjl_chain (fun l => E × (D.lv l).T.St) (D.stepA Ex Wp Kc msg) (fun l => D.mjAt Ex Rd l) C
    (fun w => mjCut Rd (msg w.1)) (D.srAt Dt) D.ownAt n (fun l hl => ?_)
    (fun l l' h1 h2 j hj => D.sr_own hM h1 h2 j hj) hCs
  have ok := ldLkpTie_ok E D l
  refine mjl_post
    (mjl_our E (D.lv l).T Ex D.J (D.eJ l) (M × Wp) (fun w => msg w.1) Rd (D.srAt Dt l) ok.1 ok.2.2.1
      ok.2.2.2 (D.own_our hM l hl)
      (fun j hj => hRd j (hj.elim Or.inl fun ⟨l', h1, h2⟩ => Or.inr ⟨l', h1.trans hl, h2⟩)) _ ?_ ?_)
    _ _ (D.nxt l) (fun o => (D.nxt l o.1, o.2)) _ (fun _ => rfl) fun _ => rfl
  · intro x k hx
    cases l with
    | zero => exact (ldLkpTie_sum0 E D x k).2 (hC x k hx)
    | succ l =>
      obtain ⟨x0, ρ, -, rfl⟩ := hx
      have ok' := ldLkpTie_ok E D l
      have h1 :=
        (mjOur_out E (D.lv l).T Ex D.J (D.eJ l) Rd ok'.1 ok'.2.2.1 ok'.2.2.2 k x0 ρ).1.2 (D.lv l).nx
      exact (ldLkpTie_sum E D l _ k (hS _ k l (Nat.lt_of_succ_le hl))).2
        ((ldLkpTie_next E D l _ k).1 h1)
  · exact mjst_spTo (fun l => E × (D.lv l).T.St) (D.stepA Ex Wp Kc msg)
      (fun l => D.mjAt Ex Rd l) C (D.ownAt l) (D.srAt Dt) (hCs l hl) l
      (fun l' h => hreads l' ((Nat.le_of_lt h).trans hl)) fun l' h j hj => D.sr_own hM h hl j hj

theorem ldLkpMaskTie_mm : Spec.ldLkpMaskTie_mm E := by
  intro D Ex M Wp Kc msg n Dt Rd hS hM hRd
  refine mjl_mm
    (ldLkpMaskTie_link E D Ex M Wp Kc msg n Dt Rd (D.claim 0) hS hM hRd
      (fun _ _ h => h) fun l hl x k k' hk hc => ?_)
  obtain ⟨a1, -, a3⟩ := hM.rd x.2 k k' fun j hj => hk j (hM.dt l hl j hj)
  show D.PK x.2 k' - D.Q x.2 k' 0 = x.1
  rw [← a1, ← a3]
  exact hc

theorem ldLkpMaskTie_sound : Spec.ldLkpMaskTie_sound E := by
  intro D Ex Kc A0 n Dt Rd C hS hM hRd hC0 hC hCs
  refine mjsp_good (b := D.tieA Ex Unit Kc (fun m => m) n)
    (ldLkpMaskTie_link E D Ex (D.J → E) Unit Kc (fun m => m) n Dt Rd C hS hM hRd hC0 hCs)
    (fun w j ⟨l, hl, hj⟩ => mjCut_of w.1 (hRd j ?_))
    (plain_tie Ex (D.J → E) Unit Kc D (fun m => m) n)
    (ldLkpTie_chain E D Ex (D.J → E) Unit Kc (fun m => m) A0 n hS) hC
  exact hj.elim Or.inl fun ⟨l', h1, h2⟩ => Or.inr ⟨l', h1.trans hl, h2⟩

end
end Cb
