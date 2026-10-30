-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Plain/Moves.lean: how the plain form (`Leads`, `LeadsK`) moves: along an equation of
the lists of rounds; to a reduction over the same rounds that follows the first; behind one round
more in front; along an equation of what is put out. And the law of keys (`KeyLaw`) with three of
these moves (not the second) and `seq`. The like for `Know`: Johnson/Desc/Sound/KnowMoves.lean.
Small closed laws, each with its proof.
Nearest kin: KnowMoves.lean | LinkMoves.lean (Johnson/Desc/Sound/): the knowledge form's moves;
these are their plain twins.

-/
import Johnson.Desc.Plain.Keyed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Iop
namespace Reduction
open _root_.Prob (cnt cnt_false)
variable {A B C A' B' κ κ' κ₂ κ₃ : Type}

/-- The key behind is a function of the key in front and of the transcript. -/
def KeyLaw (K : Reduction A B) (key : A → κ) (key' : B → κ') : Prop :=
  ∃ g : κ → Tr K.shape → κ', ∀ a τ b, K.out a τ = some b → key' b = g (key a) τ

theorem KeyLaw.seq {K₁ : Reduction A B} {K₂ : Reduction B C} {k₁ : A → κ} {k₂ : B → κ₂}
    {k₃ : C → κ₃} (h₁ : K₁.KeyLaw k₁ k₂) (h₂ : K₂.KeyLaw k₂ k₃) : (K₁.seq K₂).KeyLaw k₁ k₃ := by
  obtain ⟨g₁, l₁⟩ := h₁
  obtain ⟨g₂, l₂⟩ := h₂
  refine ⟨fun k τ => g₂ (g₁ k (Tr.fst τ)) (Tr.snd (s := K₁.shape) τ), fun a τ c hc => ?_⟩
  obtain ⟨b, hb, hbc⟩ := Option.bind_eq_some_iff.1 hc
  rw [l₂ b _ c hbc, l₁ a _ b hb]

/-- `LeadsK.seq` with the law of keys as a proposition. -/
theorem LeadsK.seq' {K₁ : Reduction A B} {K₂ : Reduction B C} {key₁ : A → κ} {key₂ : B → κ₂}
    {on₁ : A → Prop} {on₂ : B → Prop} {Q₁ : A → B → Prop} {Q₂ : B → C → Prop}
    {ε₁ : Err K₁.shape} {ε₂ : Err K₂.shape} (h₁ : K₁.LeadsK key₁ on₁ Q₁ ε₁)
    (h₂ : K₂.LeadsK key₂ on₂ Q₂ ε₂) (hon : ∀ a b, on₁ a → Q₁ a b → on₂ b)
    (law : K₁.KeyLaw key₁ key₂) :
    (K₁.seq K₂).LeadsK key₁ on₁ (fun a c => ∃ b, Q₁ a b ∧ Q₂ b c) (Err.app ε₁ ε₂) := by
  obtain ⟨g, l⟩ := law
  exact h₁.seq h₂ hon g l

/-! ## Along an equation of the lists of rounds -/

theorem leadsK_cast {s t : Shape} (h : s = t) (out : A → Tr t → Option B) (key : A → κ)
    (on : A → Prop) (Q : A → B → Prop) (ε : Err s)
    (k : (⟨s, fun a τ => out a (cast (congrArg Tr h) τ)⟩ : Reduction A B).LeadsK key on Q ε) :
    (⟨t, out⟩ : Reduction A B).LeadsK key on Q (cast (congrArg Err h) ε) := by
  subst h
  exact k

theorem leads_cast {s t : Shape} (h : s = t) (out : A → Tr t → Option B) (on : A → Prop)
    (Q : A → B → Prop) (ε : Err s)
    (k : (⟨s, fun a τ => out a (cast (congrArg Tr h) τ)⟩ : Reduction A B).Leads on Q ε) :
    (⟨t, out⟩ : Reduction A B).Leads on Q (cast (congrArg Err h) ε) := by
  subst h
  exact k

theorem keyLaw_cast {s t : Shape} (h : s = t) (out : A → Tr t → Option B) (key : A → κ)
    (key' : B → κ')
    (k : (⟨s, fun a τ => out a (cast (congrArg Tr h) τ)⟩ : Reduction A B).KeyLaw key key') :
    (⟨t, out⟩ : Reduction A B).KeyLaw key key' := by
  subst h
  exact k

/-! ## To a reduction over the same rounds that follows the first -/

theorem leadsK_sim (K : Reduction A B) (out' : A' → Tr K.shape → Option B') (key : A → κ)
    (key' : A' → κ') (f : κ' → κ) (on : A → Prop) (Q : A → B → Prop) (ε : Err K.shape)
    (on' : A' → Prop) (Q' : A' → B' → Prop)
    (h : ∀ a', on' a' → (∀ τ, out' a' τ = none) ∨ ∃ a, key a = f (key' a') ∧ on a ∧
      ∀ τ b', out' a' τ = some b' → ∃ b, K.out a τ = some b ∧ (Q a b → Q' a' b'))
    (k : K.LeadsK key on Q ε) : (⟨K.shape, out'⟩ : Reduction A' B').LeadsK key' on' Q' ε := by
  intro k'
  refine Doomed.mono _ _ ?_ (k (f k'))
  intro τ hτ a' hk' ha' b' hb'
  have hb'' : out' a' τ = some b' := hb'
  rcases h a' ha' with hn | ⟨a, hk, ha, hs⟩
  · rw [hn τ] at hb''
    cases hb''
  · obtain ⟨b, h1, h2⟩ := hs τ b' hb''
    exact h2 (hτ a (by rw [hk, hk']) ha b h1)

theorem leads_sim (K : Reduction A B) (out' : A' → Tr K.shape → Option B') (on : A → Prop)
    (Q : A → B → Prop) (ε : Err K.shape) (on' : A' → Prop) (Q' : A' → B' → Prop)
    (h : ∀ a', on' a' → (∀ τ, out' a' τ = none) ∨ ∃ a, on a ∧
      ∀ τ b', out' a' τ = some b' → ∃ b, K.out a τ = some b ∧ (Q a b → Q' a' b'))
    (k : K.Leads on Q ε) : (⟨K.shape, out'⟩ : Reduction A' B').Leads on' Q' ε := by
  intro a' ha'
  rcases h a' ha' with hn | ⟨a, ha, hs⟩
  · refine Doomed.of_forall _ _ fun τ b hb => ?_
    have hb' : out' a' τ = some b := hb
    rw [hn τ] at hb'
    cases hb'
  · refine Doomed.mono _ _ ?_ (k a ha)
    intro τ hτ b' hb'
    obtain ⟨b, h1, h2⟩ := hs τ b' hb'
    exact h2 (hτ b h1)

/-! ## Behind one round more in front -/

theorem leadsK_front (r : Round) (K : Reduction A B) (ok : A → r.Msg → Bool) (key : A → κ)
    (on : A → Prop) (Q : A → B → Prop) (ε : Err K.shape) (k : K.LeadsK key on Q ε) :
    (⟨r :: K.shape, fun a τ => if ok a τ.1 then K.out a τ.2.2 else none⟩ :
      Reduction A B).LeadsK key on Q (0, ε) := by
  intro k' m
  rw [cnt_false]
  intro c hc
  refine hc (Doomed.mono _ _ ?_ (k k'))
  intro τ hτ a hk ha b hb
  have hb' : (if ok a m then K.out a τ else none) = some b := hb
  cases ho : ok a m with
  | false =>
    rw [ho] at hb'
    cases hb'
  | true =>
    rw [ho] at hb'
    exact hτ a hk ha b hb'

theorem leads_front (r : Round) (K : Reduction A B) (ok : A → r.Msg → Bool) (on : A → Prop)
    (Q : A → B → Prop) (ε : Err K.shape) (k : K.Leads on Q ε) :
    (⟨r :: K.shape, fun a τ => if ok a τ.1 then K.out a τ.2.2 else none⟩ :
      Reduction A B).Leads on Q (0, ε) := by
  intro a ha m
  rw [cnt_false]
  intro c hc
  refine hc (Doomed.mono _ _ ?_ (k a ha))
  intro τ hτ b hb
  have hb' : (if ok a m then K.out a τ else none) = some b := hb
  cases ho : ok a m with
  | false =>
    rw [ho] at hb'
    cases hb'
  | true =>
    rw [ho] at hb'
    exact hτ b hb'

theorem keyLaw_front (r : Round) (K : Reduction A B) (ok : A → r.Msg → Bool) (key : A → κ)
    (key' : B → κ') (k : K.KeyLaw key key') :
    (⟨r :: K.shape, fun a τ => if ok a τ.1 then K.out a τ.2.2 else none⟩ :
      Reduction A B).KeyLaw key key' := by
  obtain ⟨g, l⟩ := k
  refine ⟨fun x τ => g x τ.2.2, fun a τ b hb => ?_⟩
  have hb' : (if ok a τ.1 then K.out a τ.2.2 else none) = some b := hb
  cases ho : ok a τ.1 with
  | false =>
    rw [ho] at hb'
    cases hb'
  | true =>
    rw [ho] at hb'
    exact l a _ b hb'

/-! ## Along an equation of what is put out -/

theorem leadsK_congr (K : Reduction A B) (out' : A → Tr K.shape → Option B)
    (h : ∀ a τ, out' a τ = K.out a τ) (key : A → κ) (on : A → Prop) (Q : A → B → Prop)
    (ε : Err K.shape) (k : K.LeadsK key on Q ε) :
    (⟨K.shape, out'⟩ : Reduction A B).LeadsK key on Q ε := fun k' =>
  Doomed.mono _ _ (fun τ hτ a hk ha b hb => hτ a hk ha b ((h a τ).symm.trans hb)) (k k')

theorem leads_congr (K : Reduction A B) (out' : A → Tr K.shape → Option B)
    (h : ∀ a τ, out' a τ = K.out a τ) (on : A → Prop) (Q : A → B → Prop) (ε : Err K.shape)
    (k : K.Leads on Q ε) : (⟨K.shape, out'⟩ : Reduction A B).Leads on Q ε := fun a ha =>
  Doomed.mono _ _ (fun τ hτ b hb => hτ b ((h a τ).symm.trans hb)) (k a ha)

theorem keyLaw_congr (K : Reduction A B) (out' : A → Tr K.shape → Option B)
    (h : ∀ a τ, out' a τ = K.out a τ) (key : A → κ) (key' : B → κ') (k : K.KeyLaw key key') :
    (⟨K.shape, out'⟩ : Reduction A B).KeyLaw key key' := by
  obtain ⟨g, l⟩ := k
  exact ⟨g, fun a τ b hb => l a τ b ((h a τ).symm.trans hb)⟩

end Reduction
end Iop

#print axioms Iop.Reduction.leadsK_sim
#print axioms Iop.Reduction.leadsK_front
#print axioms Iop.Reduction.KeyLaw.seq
