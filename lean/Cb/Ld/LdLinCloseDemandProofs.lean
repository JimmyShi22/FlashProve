-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinCloseDemandProofs.lean: the proofs of the statements of Cb/Ld/LdLinCloseDemand.lean (what
several tests in a row need of the oracle messages).
Nothing is defined here that a statement reads.
-/
import Cb.Ld.LdLinCloseDemand

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- membership in a union, whatever the instance that decides equality -/
theorem ldDemand_mem_biUnion
    {α β : Type} (inst : DecidableEq β) {s : Finset α} {t : α → Finset β} {b : β} :
    b ∈ @Finset.biUnion α β inst s t ↔ ∃ a ∈ s, b ∈ t a :=
  Finset.mem_biUnion

theorem ldDemand_mem_image {α β : Type} (inst : DecidableEq β) {f : α → β} {s : Finset α} {b : β} :
    b ∈ @Finset.image α β inst f s ↔ ∃ a ∈ s, f a = b := Finset.mem_image

theorem ldDemand_nil : Spec.ldDemand_nil := by
  intro E _ S E₀ Wp w₀ q₀ b hq V hV
  have hV' : V = ∅ := hV
  subst hV'
  exact ⟨hq,
    fun o => by rw [cnt_false fun x hx => absurd hx (Finset.notMem_empty _)]; exact Nat.zero_le _⟩

section BrG
variable {E : Type} {S : Sig E} (G : Grp S) (kp : S.O → Prop) [DecidablePred kp] (E₀ : ExtSpec)

/-- a position of the further oracles is a source if and only if it is needed on the carried side -/
theorem ldBrG_mem_inl (inst : DecidableEq (E₀.prod S.ext).Pos)
    (U : Finset (LdBrE G kp E₀).Pos) (p₀ : E₀.Pos) :
    (Sum.inl p₀ : (E₀.prod S.ext).Pos) ∈ @Finset.biUnion _ _ inst U (ldBrG G kp E₀).src ↔
    (Sum.inl p₀ : (E₀.prod (S.sub kp).ext).Pos) ∈ U.toRight := by
  constructor
  · intro h
    obtain ⟨u, hu, hp⟩ := (ldDemand_mem_biUnion _).1 h
    rcases u with z | p | q
    · obtain ⟨q', _, hq'⟩ := (ldDemand_mem_biUnion _).1 hp
      exact absurd (Finset.mem_singleton.1 hq') (by simp)
    · have hp' : (Sum.inl p₀ : (E₀.prod S.ext).Pos) ∈ ({Sum.inl p} : Finset (E₀.prod S.ext).Pos) :=
        hp
      obtain rfl := Sum.inl.inj (Finset.mem_singleton.1 hp')
      exact Finset.mem_toRight.2 hu
    · obtain ⟨q', _, hq'⟩ := (ldDemand_mem_biUnion _).1 hp
      exact absurd (Finset.mem_singleton.1 hq') (by simp)
  · intro h
    exact (ldDemand_mem_biUnion _).2
      ⟨Sum.inr (Sum.inl p₀), Finset.mem_toRight.1 h, Finset.mem_singleton_self _⟩

/-- a long position of an oracle message is a source only if it is read for a common position of the
group, or needed on the carried side -/
theorem ldBrG_mem_inr (inst : DecidableEq (E₀.prod S.ext).Pos) (U : Finset (LdBrE G kp E₀).Pos)
    (o : S.O) (x : (S.om o).P)
    (h : (Sum.inr ⟨o, x⟩ : (E₀.prod S.ext).Pos) ∈ @Finset.biUnion _ _ inst U (ldBrG G kp E₀).src) :
    (∃ h : G.mem o, ∃ z ∈ U.toLeft, G.pos ⟨o, h⟩ z = x) ∨
    ∃ h : kp o, (Sum.inr ⟨⟨o, h⟩, x⟩ : (E₀.prod (S.sub kp).ext).Pos) ∈ U.toRight := by
  obtain ⟨u, hu, hp⟩ := (ldDemand_mem_biUnion _).1 h
  rcases u with z | p | q
  · left
    obtain ⟨q', hq1, hq'⟩ := (ldDemand_mem_biUnion _).1 hp
    obtain rfl : (⟨o, x⟩ : S.ext.Pos) = q' := Sum.inr.inj (Finset.mem_singleton.1 hq')
    obtain ⟨a, _, ha⟩ := (ldDemand_mem_image _).1 hq1
    obtain ⟨a', ha'⟩ := a
    obtain rfl : a' = o := congrArg Sigma.fst ha
    exact ⟨ha', z, Finset.mem_toLeft.2 hu, eq_of_heq (Sigma.mk.inj ha).2⟩
  · have hp' : (Sum.inr ⟨o, x⟩ : (E₀.prod S.ext).Pos) ∈
        ({Sum.inl p} : Finset (E₀.prod S.ext).Pos) := hp
    exact absurd (Finset.mem_singleton.1 hp') (by simp)
  · right
    obtain ⟨q', hq1, hq'⟩ := (ldDemand_mem_biUnion _).1 hp
    obtain rfl : (⟨o, x⟩ : S.ext.Pos) = q' := Sum.inr.inj (Finset.mem_singleton.1 hq')
    obtain ⟨⟨a', ha'⟩, x'⟩ := q
    have hq2 : (⟨o, x⟩ : S.ext.Pos) = ⟨a', x'⟩ := Finset.mem_singleton.1 hq1
    obtain rfl : o = a' := congrArg Sigma.fst hq2
    obtain rfl : x = x' := eq_of_heq (Sigma.mk.inj hq2).2
    exact ⟨ha', Finset.mem_toRight.2 hu⟩

theorem ldBrG_toLeft (inst : DecidableEq (E₀.prod S.ext).Pos) (U : Finset (LdBrE G kp E₀).Pos) :
    (@Finset.biUnion _ _ inst U (ldBrG G kp E₀).src).toLeft = U.toRight.toLeft := by
  ext p₀
  rw [Finset.mem_toLeft, Finset.mem_toLeft]
  exact ldBrG_mem_inl G kp E₀ inst U p₀

end BrG

theorem ldDemand_cons : Spec.ldDemand_cons := by
  classical
  intro E _ _ S E₀ Wp D Q d d' q₀ b' hQ V hV
  obtain ⟨U, ⟨hU1, hU2⟩, rfl⟩ := hV
  obtain ⟨hq, hb⟩ := hQ _ hU2
  refine ⟨?_, fun o => ?_⟩
  · rw [ldBrG_toLeft]
    exact hq
  · refine (cnt_le_add (ldBrG_mem_inr D.G D.kp E₀ _ U o)).trans (Nat.add_le_add ?_ ?_)
    · by_cases h : D.G.mem o
      · rw [if_pos h, cnt_eq_card_filter]
        refine le_trans
          (le_trans (Finset.card_le_card (t := U.toLeft.image (D.G.pos ⟨o, h⟩)) fun x hx => ?_)
            Finset.card_image_le) hU1
        obtain ⟨_, z, hz, hzx⟩ := (Finset.mem_filter.1 hx).2
        exact Finset.mem_image.2 ⟨z, hz, hzx⟩
      · rw [if_neg h, cnt_false fun x hx => h hx.1]
    · by_cases h : D.kp o
      · rw [dif_pos h]
        exact (cnt_mono fun x hx => hx.2).trans (hb ⟨o, h⟩)
      · rw [dif_neg h, cnt_false fun x hx => h hx.1]

theorem ldDemand_le : Spec.ldDemand_le := by
  intro E _ _ S D b' o
  refine Nat.add_le_add_right ?_ _
  by_cases h : D.G.mem o
  · rw [if_pos h]
  · rw [if_neg h]
    exact Nat.zero_le _

section
variable {E ι κ J Y : Type} [Field E] (C : LdLinC E ι κ J Y)

/-- the re-bracketing of positions, forth and back -/
def LdLinC.fromPos : (C.E₀.prod C.S.ext).Pos → C.P.E5.Pos
  | .inl p => .inl (.inl (.inl (.inl p)))
  | .inr ⟨.inl (.inl (.inl a)), x⟩ => .inl (.inl (.inl (.inr ⟨a, x⟩)))
  | .inr ⟨.inl (.inl (.inr a)), x⟩ => .inl (.inl (.inr ⟨a, x⟩))
  | .inr ⟨.inl (.inr a), x⟩ => .inl (.inr ⟨a, x⟩)
  | .inr ⟨.inr a, x⟩ => .inr ⟨a, x⟩

def LdLinC.toPos : C.P.E5.Pos → (C.E₀.prod C.S.ext).Pos
  | .inl (.inl (.inl (.inl p))) => .inl p
  | .inl (.inl (.inl (.inr ⟨a, x⟩))) => .inr ⟨.inl (.inl (.inl a)), x⟩
  | .inl (.inl (.inr ⟨a, x⟩)) => .inr ⟨.inl (.inl (.inr a)), x⟩
  | .inl (.inr ⟨a, x⟩) => .inr ⟨.inl (.inr a), x⟩
  | .inr ⟨a, x⟩ => .inr ⟨.inr a, x⟩

theorem LdLinC.toPos_fromPos (v : (C.E₀.prod C.S.ext).Pos) : C.toPos (C.fromPos v) = v := by
  rcases v with p | ⟨((a | a) | a) | a, x⟩ <;> rfl

theorem LdLinC.toE_src (v : (C.E₀.prod C.S.ext).Pos) : C.toE.src v = {C.fromPos v} := by
  rcases v with p | ⟨((a | a) | a) | a, x⟩ <;> rfl

theorem LdLinC.mem_toE [DecidableEq C.P.E5.Pos]
    (V : Finset (C.E₀.prod C.S.ext).Pos) (v : (C.E₀.prod C.S.ext).Pos) :
    C.fromPos v ∈ V.biUnion C.toE.src ↔ v ∈ V := by
  constructor
  · intro h
    obtain ⟨u, hu, hp⟩ := Finset.mem_biUnion.1 h
    rw [C.toE_src u] at hp
    have e := congrArg C.toPos (Finset.mem_singleton.1 hp)
    rw [C.toPos_fromPos, C.toPos_fromPos] at e
    rw [e]
    exact hu
  · intro h
    exact Finset.mem_biUnion.2 ⟨v, h, by rw [C.toE_src v]; exact Finset.mem_singleton_self _⟩

end

section
variable (E ι κ J Y : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

omit [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y] in
open Classical in
theorem ldDemand_lin : Spec.ldDemand_lin E ι κ J Y := by
  intro C Sn qa q₀ ba b hqa hA hW hU hO V hV
  obtain ⟨hq, hb⟩ := hV
  refine ⟨⟨⟨hqa _ ⟨?_, fun a => ?_⟩, fun a => ?_⟩, fun a => ?_⟩, fun a => ?_⟩
  · have e : (V.biUnion C.toE.src).toLeft.toLeft.toLeft.toLeft = V.toLeft := by
      ext p
      rw [Finset.mem_toLeft, Finset.mem_toLeft, Finset.mem_toLeft,
        Finset.mem_toLeft, Finset.mem_toLeft]
      exact C.mem_toE V (.inl p)
    rw [e]
    exact hq
  · refine ((cnt_mono fun x hx => ?_).trans (hb (.inl (.inl (.inl a))))).trans (hA a)
    exact (C.mem_toE V (.inr ⟨.inl (.inl (.inl a)), x⟩)).1
      (Finset.mem_toLeft.1 (Finset.mem_toLeft.1 (Finset.mem_toLeft.1 hx)))
  · refine ((cnt_mono fun x hx => ?_).trans (hb (.inl (.inl (.inr a))))).trans (hW a)
    exact (C.mem_toE V (.inr ⟨.inl (.inl (.inr a)), x⟩)).1
      (Finset.mem_toLeft.1 (Finset.mem_toLeft.1 hx))
  · refine ((cnt_mono fun x hx => ?_).trans (hb (.inl (.inr a)))).trans (hU a)
    exact (C.mem_toE V (.inr ⟨.inl (.inr a), x⟩)).1 (Finset.mem_toLeft.1 hx)
  · refine ((cnt_mono fun x hx => ?_).trans (hb (.inr a))).trans (hO a)
    exact (C.mem_toE V (.inr ⟨.inr a, x⟩)).1 hx

omit [Fintype ι] [Nonempty ι] in
open Classical in
theorem ldDemand_plan : Spec.ldDemand_plan E ι κ J Y := by
  intro C p T Sn qa q₀ ba b' hQ hqa hA hW hU hO V hV
  exact ldDemand_lin E ι κ J Y C Sn qa q₀ ba _ hqa hA hW hU hO V
    (ldDemand_cons E C.S C.E₀ C.Wpa T.D₁ _ T.d₁ T.d₁' q₀ _
      (ldDemand_cons E p.S₁ C.E₀ C.Wpa T.D₂ T.Q' T.d₂ T.d₂' q₀ b' hQ) V hV)

omit [Fintype ι] [Nonempty ι] in
theorem ldDemand_plain : Spec.ldDemand_plain E ι κ J Y := by
  intro C p T b' o c hc
  have h1 := ldDemand_le E C.S T.D₁ (T.D₂.need b') o
  refine h1.trans ?_
  by_cases hk : p.kp₁ o
  · rw [dif_pos hk]
    have h2 := ldDemand_le E p.S₁ T.D₂ b' ⟨o, hk⟩
    have h3 : (if h : p.kp₂ ⟨o, hk⟩ then b' ⟨⟨o, hk⟩, h⟩ else 0) ≤ c := by
      by_cases hk2 : p.kp₂ ⟨o, hk⟩
      · rw [dif_pos hk2]
        exact hc hk hk2
      · rw [dif_neg hk2]
        exact Nat.zero_le _
    have h4 : T.D₂.need b' ⟨o, hk⟩ ≤ T.t₂ + c := h2.trans (Nat.add_le_add_left h3 _)
    have h5 : T.D₁.t + T.D₂.need b' ⟨o, hk⟩ ≤ T.t₁ + (T.t₂ + c) := Nat.add_le_add_left h4 _
    rw [Nat.add_assoc]
    exact h5
  · rw [dif_neg hk]
    exact Nat.le_trans (Nat.le_of_eq (Nat.add_zero _))
      (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_of_eq (Nat.add_assoc _ _ _).symm))

theorem ldLinPlan_tail : Spec.ldLinPlan_tail E ι κ J Y := by
  intro C p T on0 εf Sn qa d q₀ ba b' hF hpy hS hr hA hD₁ hD₂ hQ' hq hqa h1 h2 h3 h4
  exact ldLinCl_tail E ι κ J Y C on0 εf Sn qa d T.Q T.fq hF hpy hS
    (ldLinPlan_says E ι κ J Y C p _ T.Q'.base T.fa hr hA)
    (ldChain_cons E C.S C.E₀ C.Wpa T.D₁ _ T.d₁ T.d₁' hD₁
      (ldChain_cons E p.S₁ C.E₀ C.Wpa T.D₂ T.Q' T.d₂ T.d₂' hD₂ hQ'))
    (ldDemand_plan E ι κ J Y C p T Sn qa q₀ ba b' hq hqa h1 h2 h3 h4)

end
end Cb
