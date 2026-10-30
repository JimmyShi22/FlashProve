-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/SubcodeList.lean: from a code to a part of it, the count of exceptional points of a
line grows by at most the list of pairs: at every radius below the distance. NOTHING IS ASSUMED
HERE; no code of the format occurs.

The library passes a bound on the exceptional points of a line (mutual correlated agreement) from a
code D to a subcode D' within half the distance (`Code.MCAOn.subcode`, Code/Mutual.lean: 2 e < d).
This file has the step at every radius e below the distance d, at a price: the number L of pairs of
words of D that agree with a given pair of words on one common set of all but e positions. If D has
at most A exceptional points on every line, D' has at most A + L.

The argument. Let θ be exceptional for D' on the set S. If f₀ and f₁ do not both agree on S with
words of D, θ is exceptional for D: at most A values. Else they agree on S with words c₀ and c₁ of
D, a pair of the list. The word c₀ + θ c₁ of D agrees on S with a word of D', so it is that word,
since e < d. Not both c₀ and c₁ lie in D'. To one such pair belongs at most one θ: from two, c₁ and
then c₀ would lie in D'.

Main definition: `PairNear`. Main theorem: `mcaOn_subcode_list`.

Not claimed. One row only. Nothing on how large the list of pairs is (`pairNear_johnson`,
OnBytes/Slice/MaskBchks.lean, bounds it below the Johnson radius). Nothing here on a Reed-Solomon
code, on the format's repeated mask code or on a stage: OnBytes/Slice/MaskBchks.lean applies it to
them. It proves no soundness of anything.

-/
import Code.Mutual

set_option autoImplicit false

namespace OnBytes.Slice
open Code Prob Finset

variable {E ι : Type} [Field E] [Fintype ι]

/-- c is a pair of words of the code D that agrees with the pair of words f₀, f₁ on one common set
of all but at most e positions. -/
def PairNear (D : Submodule E (ι → E)) (e : ℕ) (f₀ f₁ : ι → E) (c : (ι → E) × (ι → E)) : Prop :=
  c.1 ∈ D ∧ c.2 ∈ D ∧ ∃ S : Finset ι, Fintype.card ι ≤ S.card + e ∧ (∀ j ∈ S, f₀ j = c.1 j) ∧
    ∀ j ∈ S, f₁ j = c.2 j

/-- **From a code to a part of it, below the distance.** D has the minimum distance d, e is below d,
D' is a part of D, a line has at most A exceptional points for D at the radius e, and every pair of
words has at most L pairs of words of D near it. Then a line has at most A + L exceptional points
for D' at the radius e. -/
theorem mcaOn_subcode_list [Finite E] {D D' : Submodule E (ι → E)} {d e A L : ℕ}
    (hd : MinDist D d) (he : e < d) (hD : D' ≤ D) (h : MCAOn Unit D e A)
    (hL : ∀ f₀ f₁ : ι → E, cnt (PairNear D e f₀ f₁) ≤ L) : MCAOn Unit D' e (A + L) := by
  classical
  haveI := Fintype.ofFinite E
  intro f₀ f₁
  have hsplit : ∀ θ : E, BadAt D' e f₀ f₁ θ → BadAt D e f₀ f₁ θ ∨
      ∃ c, PairNear D e (f₀ ()) (f₁ ()) c ∧ c.1 + θ • c.2 ∈ D' ∧ ¬ (c.1 ∈ D' ∧ c.2 ∈ D') := by
    rintro θ ⟨S, hS, hl, hn⟩
    by_cases hb : (∀ a, f₀ a ∈ agreeOn D S) ∧ ∀ a, f₁ a ∈ agreeOn D S
    · obtain ⟨c₀, hc₀, h0⟩ := mem_agreeOn.mp (hb.1 ())
      obtain ⟨c₁, hc₁, h1⟩ := mem_agreeOn.mp (hb.2 ())
      obtain ⟨w, hw, hfw⟩ := mem_agreeOn.mp (hl ())
      refine Or.inr ⟨(c₀, c₁), ⟨hc₀, hc₁, S, hS, h0, h1⟩, ?_, fun hcc => hn ⟨?_, ?_⟩⟩
      · have hwc : w = c₀ + θ • c₁ :=
          hd.eq_of_agree (hD hw) (D.add_mem hc₀ (D.smul_mem _ hc₁)) (S := S) (by omega)
            fun j hj => by
              rw [← hfw j hj, Pi.add_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, h0 j hj,
                h1 j hj]
        show c₀ + θ • c₁ ∈ D'
        rw [← hwc]
        exact hw
      · rintro ⟨⟩
        exact mem_agreeOn.mpr ⟨c₀, hcc.1, h0⟩
      · rintro ⟨⟩
        exact mem_agreeOn.mpr ⟨c₁, hcc.2, h1⟩
    · exact Or.inl ⟨S, hS, fun a => agreeOn_mono hD S (hl a), hb⟩
  refine le_trans (cnt_le_add hsplit) (Nat.add_le_add (h f₀ f₁) ?_)
  refine le_trans ?_ (hL (f₀ ()) (f₁ ()))
  refine Nat.card_le_card_of_injective
    (fun θ : {θ : E // ∃ c, PairNear D e (f₀ ()) (f₁ ()) c ∧ c.1 + θ • c.2 ∈ D' ∧
        ¬ (c.1 ∈ D' ∧ c.2 ∈ D')} =>
      (⟨θ.2.choose, θ.2.choose_spec.1⟩ : {c // PairNear D e (f₀ ()) (f₁ ()) c})) ?_
  intro θ θ' hEq
  have hc : θ.2.choose = θ'.2.choose := congrArg Subtype.val hEq
  obtain ⟨-, h1, hn⟩ := θ.2.choose_spec
  obtain ⟨-, h2, -⟩ := θ'.2.choose_spec
  rw [← hc] at h2
  by_contra hne
  have hne' : θ.1 - θ'.1 ≠ 0 := sub_ne_zero.mpr fun h0 => hne (Subtype.ext h0)
  have h3 : (θ.1 - θ'.1) • θ.2.choose.2 ∈ D' := by
    have h4 := D'.sub_mem h1 h2
    have h5 : θ.2.choose.1 + θ.1 • θ.2.choose.2 - (θ.2.choose.1 + θ'.1 • θ.2.choose.2) =
        (θ.1 - θ'.1) • θ.2.choose.2 := by
      rw [sub_smul]
      abel
    rwa [h5] at h4
  have h6 : θ.2.choose.2 ∈ D' := by
    have h7 := D'.smul_mem (θ.1 - θ'.1)⁻¹ h3
    rwa [smul_smul, inv_mul_cancel₀ hne', one_smul] at h7
  have h8 : θ.2.choose.1 ∈ D' := by
    have h9 := D'.sub_mem h1 (D'.smul_mem θ.1 h6)
    rwa [add_sub_cancel_right] at h9
  exact hn ⟨h8, h6⟩

end OnBytes.Slice
