-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBatPeelProofs.lean: the proofs of the statements of Cb/Ld/LdBatPeel.lean (reductions without
messages that write one linear claim on encoded messages in another form: steps without rounds
between joints over one signature; forms on groups and on kept messages).

Named tools: `sum_subtype_zero` (a sum over a subtype equals the sum over the whole type, if the
summand vanishes outside it). Nothing is defined here that a statement reads.

Main names (statements and hypotheses: Cb/Ld/LdBatPeel.lean):
  `ldPeel_cf`: steps between joints in the form `Rels.cf`.
  `ldPeel_base`: the rule: a change of the base joint, the messages untouched.
  `ldPeel_onG`, `ldPeel_two`, `ldPeel_onSub`, `ldPeel_toSub`: a form's value on a group's message,
    on two groups, on the kept messages, on `G.sub kp`.
  `ldPeel_sub_fits`: `Grp.Fits` of `G.sub kp`.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdBatPeel
import Cb.Ld.LdBatSigProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Ood IOR

theorem ldPeel_cf : Spec.ldPeel_cf := by
  intro K X X' W W' Ex Ex' f g m back A B h
  refine ⟨h.isLocal, h.acc, fun _ _ _ _ _ => trivial, h.keeps, fun x y x' w' _ hx hB => ?_⟩
  by_cases ha : A.on (x, y)
  · exact hB.elim (fun hr => Or.inl (h.know x y x' w' ha hx hr)) fun hn =>
      absurd (h.onOut x y x' ha hx) hn
  · exact Or.inr ha

theorem ldPeel_base : Spec.ldPeel_base := by
  intro E Kc St St' Wp Wp' _ S E₀ E₀' A A' f g₀ up dn hg hfw hon hcore hbw
  obtain ⟨_, hfs, _, hcomp, hpair⟩ := extMap_isLocal
  refine ⟨hpair _ _ _ _ _ (hcomp _ _ _ _ _ hg (hfs E₀ S.ext).1) (hfs E₀ S.ext).2, ?_, ?_,
    fun x w => hcore x.1 (S.msgs w.1, w.2), ?_⟩
  · rintro x y w ⟨h1, h2, h3⟩
    exact ⟨rfl, h1, h2, hfw x.1 y.1 _ h3⟩
  · rintro x y x' ⟨h1, h2⟩ hx
    rw [← Option.some.inj hx]
    exact ⟨h1, hon x.1 y.1 h2⟩
  · rintro x y x' w' ⟨_, h2⟩ hx hB
    rw [← Option.some.inj hx] at hB
    exact ⟨hB.1, hbw x.1 y.1 _ h2 hB.2⟩

theorem sum_subtype_zero {α M : Type} [Fintype α] [AddCommMonoid M] (p : α → Prop) [DecidablePred p]
    (f : α → M) (h : ∀ a, ¬ p a → f a = 0) :
    ∑ a : {a // p a}, f a.1 = ∑ a, f a := by
  rw [← Fintype.sum_subtype_add_sum_subtype p f,
    Finset.sum_eq_zero (s := (Finset.univ : Finset {a // ¬ p a})) fun a _ => h a.1 a.2, add_zero]

section
variable (E : Type) [Field E]

theorem ldPeel_onG : Spec.ldPeel_onG E := by
  intro S G St sl st m h
  show ∑ n : (Σ a : G.A, (S.om a.1).C.J), sl st ⟨n.1.1, n.2⟩ * m n.1.1 n.2 =
    ∑ n : (Σ a, (S.om a).C.J), sl st n * m n.1 n.2
  rw [Fintype.sum_sigma, Fintype.sum_sigma]
  exact sum_subtype_zero G.mem (fun o => ∑ j, sl st ⟨o, j⟩ * m o j) fun o ho =>
    Finset.sum_eq_zero fun j _ => by rw [h ⟨o, j⟩ ho, zero_mul]

theorem ldPeel_two : Spec.ldPeel_two E := by
  intro S G₁ G₂ St sl st m h
  have h2 := ldPeel_onG E S G₂ St (sl.offG G₁) st m fun n hn => by
    show (if G₁.mem n.1 then 0 else sl st n) = 0
    by_cases h1 : G₁.mem n.1
    · rw [if_pos h1]
    · rw [if_neg h1, h n h1 hn]
  have h1 :=
    ldPeel_onG E S G₁ St (fun st n => if G₁.mem n.1 then sl st n else 0) st m fun n hn => if_neg hn
  have e1 : (sl.onG G₁).val st (G₁.msg m) =
      (Slf.onG (fun st n => if G₁.mem n.1 then sl st n else 0) G₁).val st (G₁.msg m) :=
    Finset.sum_congr rfl fun n _ => by
      show sl st (G₁.ent n) * _ = (if G₁.mem (G₁.ent n).1 then sl st (G₁.ent n) else 0) * _
      rw [if_pos (show G₁.mem (G₁.ent n).1 from n.1.2)]
  rw [e1, h1, h2]
  unfold Slf.val
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  show (if G₁.mem n.1 then sl st n else 0) * _ + (if G₁.mem n.1 then 0 else sl st n) * _ = _
  by_cases hn : G₁.mem n.1
  · rw [if_pos hn, if_pos hn, zero_mul, add_zero]
  · rw [if_neg hn, if_neg hn, zero_mul, zero_add]

theorem ldPeel_onSub : Spec.ldPeel_onSub E := by
  intro S kp _ St sl st m h
  show ∑ n : (Σ a : {o // kp o}, (S.om a.1).C.J), sl st ⟨n.1.1, n.2⟩ * m n.1.1 n.2 =
    ∑ n : (Σ a, (S.om a).C.J), sl st n * m n.1 n.2
  rw [Fintype.sum_sigma, Fintype.sum_sigma]
  exact sum_subtype_zero kp (fun o => ∑ j, sl st ⟨o, j⟩ * m o j) fun o ho =>
    Finset.sum_eq_zero fun j _ => by rw [h ⟨o, j⟩ ho, zero_mul]

theorem ldPeel_toSub : Spec.ldPeel_toSub E := by
  intro S G kp _ St sl st m h
  show ∑ n : (Σ a : {a : {o // kp o} // G.mem a.1}, (S.om a.1.1).C.J),
      sl st ⟨⟨n.1.1.1, n.1.2⟩, n.2⟩ * m n.1.1.1 n.2 =
    ∑ n : (Σ a : {o // G.mem o}, (S.om a.1).C.J), sl st n * m n.1.1 n.2
  rw [Fintype.sum_sigma, Fintype.sum_sigma]
  let e : {a : {o // kp o} // G.mem a.1} ≃ {o // G.mem o} :=
    ⟨fun a => ⟨a.1.1, a.2⟩, fun a => ⟨⟨a.1, h a.1 a.2⟩, a.2⟩, fun _ => rfl, fun _ => rfl⟩
  exact Equiv.sum_comp e fun a : {o // G.mem o} => ∑ j, sl st ⟨a, j⟩ * m a.1 j

theorem ldPeel_sub_fits : Spec.ldPeel_sub_fits E := fun _ _ _ _ h a f g hn => h ⟨a.1.1, a.2⟩ f g hn

end
end Cb
