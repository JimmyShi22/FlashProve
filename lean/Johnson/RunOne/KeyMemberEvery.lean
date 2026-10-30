-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyMemberEvery.lean: THEOREMS. **At an honest word NO seed is a collision**: where the radius is below the code's distance, the list of a code word holds its own message alone. So at honest words the condition of KeyLetters.lean holds AT EVERY SEED, not only outside a share.
OBJECT: OMsg.InList | OMsg.Clash at portOmZ cs s e and the word sent of KeyMember.lean. USER: Johnson/RunOne/KeyHonestPins.lean | KeyMemberTable.lean call no_clash_sent. LETTERS: cs · s · e · d.
  near_unique     laws and distance d, e < d: a message some encoding of which is within e of the code word of (m, r) is m
  list_sent       the list of the word sent is {m}
  no_clash_sent   **no seed is a collision of the list of the word sent**
  member_one_every | member_two_every   member_one | member_two without the premises on the seeds
  lt_of_johnson | base_of_meets   the library's test on numbers gives laws, the distance dOf and e < dOf
What it is for. The share of the colliding seeds (clash_share) is what SOUNDNESS pays at a word that an adversary picks. The member does not need it.
What is not claimed. Nothing at a word that is no code word. Nothing on soundness or on hiding.

-/
import Johnson.RunOne.KeyMemberBack

set_option autoImplicit false

namespace Johnson.RunOne.KeyLetters

open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice Johnson.Pack Cb Cb.Ood Prob
open VerifiableInference.Desc VerifiableInference.Desc.K1

/-- Below the distance a code word is near no other code word. -/
theorem near_unique {P : Type} [Finite P] (C : LdCode GE P) (hL : C.Laws) {d e : Nat} (hD : C.Dist d) (he : e < d)
    {m u : C.J → GE} {r r' : C.Q → GE} (h : C.Near e (C.enc m r) (C.enc u r')) : u = m := by
  by_contra hne
  have h0 : ¬ (m - u = 0 ∧ r - r' = 0) := fun c => hne (sub_eq_zero.1 c.1).symm
  have h1 := hD (m - u) (r - r') h0
  have e1 : C.enc (m - u) (r - r') = C.enc m r - C.enc u r' := hL.encLin.map_sub (m, r) (u, r')
  have e2 : cnt (fun x => C.T (C.enc (m - u) (r - r')) x ≠ 0) = cnt (fun x => C.T (C.enc m r) x ≠ C.T (C.enc u r') x) := by
    refine cnt_congr fun x => ?_
    rw [e1, hL.tLin.map_sub]
    exact sub_ne_zero
  rw [e2] at h1
  exact absurd (lt_of_lt_of_le he (le_trans h1 h)) (lt_irrefl _)

variable {cs : Codes} {s : OracleShape} {e d : Nat}

theorem list_sent (hL : (portCode cs s).Laws) (hD : (portCode cs s).Dist d) (he : e < d) {m : (portCode cs s).J → GE} {r : (portCode cs s).Q → GE}
    (h : Sendable cs s m r) {u : (portCode cs s).J → GE} (hu : (portOmZ cs s e).InList (sent cs s e m r) u) : u = m := by
  obtain ⟨r', hr⟩ := hu
  have hr' : (portCode cs s).Near e ((portOmZ cs s e).upW (sent cs s e m r)) ((portCode cs s).enc u r') := hr
  rw [up_sent h] at hr'
  exact near_unique (portCode cs s) hL hD he hr'

/-- **No seed is a collision of the list of the word sent.** -/
theorem no_clash_sent (hL : (portCode cs s).Laws) (hD : (portCode cs s).Dist d) (he : e < d) {m : (portCode cs s).J → GE} {r : (portCode cs s).Q → GE}
    (h : Sendable cs s m r) (ρ : (Fin (bitsZ cs s) → GE) × GEˣ) : ¬ (portOmZ cs s e).Clash (sent cs s e m r) ρ := by
  rintro ⟨u, u', hu, hu', hne, -⟩
  exact hne ((list_sent hL hD he h hu).trans (list_sent hL hD he h hu').symm)

theorem lt_of_johnson {n d e : Nat} (hd : d ≤ n) (h : InJohnson n d e) : e < d := by
  unfold InJohnson at h
  by_contra hc
  have h1 : n - e ≤ n - d := Nat.sub_le_sub_left (Nat.le_of_not_lt hc) n
  have h2 : (n - e) ^ 2 ≤ (n - d) ^ 2 := Nat.pow_le_pow_left h1 2
  have h3 : (n - d) ^ 2 ≤ n * (n - d) := by
    rw [pow_two]
    exact Nat.mul_le_mul_right _ (Nat.sub_le n d)
  omega

/-- The library's test on numbers gives the laws, the distance and that the radius is below it. dOf is the code's distance AS READ AT THE LONG POSITIONS (a long position holds the main rows' and the mask rows' symbols there): the positions that Near counts. -/
theorem base_of_meets (h : meetsB cs s e = true) : (portCode cs s).Laws ∧ (portCode cs s).Dist (dOf cs s) ∧ e < dOf cs s := by
  have g := (meetsB_sound cs s e h).1
  unfold meetsB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨port_laws cs s g.ok, port_dist cs s g.ok _ g.d1 g.d2, lt_of_johnson h.2 h.1.2⟩

/-- member_one, at every seed. -/
theorem member_one_every (hT : Tie cs s) (hm : meetsB cs s e = true) {m : (portCode cs s).J → GE} {r : (portCode cs s).Q → GE} (h : Sendable cs s m r) {St : Statement} {o : Nat}
    {ρ : (Fin (bitsZ cs s) → GE) × GEˣ} (hI : SeedIs cs s St o ρ ((portZ cs s).val ρ m ())) :
    Sealed cs s e (sent cs s e m r) St o ∧ decAt cs s e (sent cs s e m r) St o = some m :=
  member_one hT h hI (no_clash_sent (base_of_meets hm).1 (base_of_meets hm).2.1 (base_of_meets hm).2.2 h ρ)

section two
variable {s₀ s₁ : OracleShape} {e₀ e₁ o₀ o₁ : Nat} {X Y MW : Type} {stOf : X → Statement}
  {f₀ : Y → (portOmZ cs s₀ e₀).Str} {f₁ : Y → (portOmZ cs s₁ e₁).Str} {decW : Y → Option MW}

/-- **member_two, at every pair of seeds**: at honest words, records with the honest answers: cond₂ holds and dec₂ returns the triple. -/
theorem member_two_every (hT₀ : Tie cs s₀) (hT₁ : Tie cs s₁) (hm₀ : meetsB cs s₀ e₀ = true) (hm₁ : meetsB cs s₁ e₁ = true)
    {m₀ : (portCode cs s₀).J → GE} {r₀ : (portCode cs s₀).Q → GE} {m₁ : (portCode cs s₁).J → GE} {r₁ : (portCode cs s₁).Q → GE}
    (h₀ : Sendable cs s₀ m₀ r₀) (h₁ : Sendable cs s₁ m₁ r₁) {a : X × Y} {W : MW}
    (hf₀ : f₀ a.2 = sent cs s₀ e₀ m₀ r₀) (hf₁ : f₁ a.2 = sent cs s₁ e₁ m₁ r₁) (hW : decW a.2 = some W)
    {ρ₀ : (Fin (bitsZ cs s₀) → GE) × GEˣ} {ρ₁ : (Fin (bitsZ cs s₁) → GE) × GEˣ}
    (hI₀ : SeedIs cs s₀ (stOf a.1) o₀ ρ₀ ((portZ cs s₀).val ρ₀ m₀ ())) (hI₁ : SeedIs cs s₁ (stOf a.1) o₁ ρ₁ ((portZ cs s₁).val ρ₁ m₁ ())) :
    cond₂ cs s₀ s₁ e₀ e₁ o₀ o₁ stOf f₀ f₁ a ∧ dec₂ cs s₀ s₁ e₀ e₁ o₀ o₁ stOf f₀ f₁ decW a = some (m₀, m₁, W) :=
  member_two hT₀ hT₁ h₀ h₁ hf₀ hf₁ hW hI₀ hI₁
    (no_clash_sent (base_of_meets hm₀).1 (base_of_meets hm₀).2.1 (base_of_meets hm₀).2.2 h₀ ρ₀)
    (no_clash_sent (base_of_meets hm₁).1 (base_of_meets hm₁).2.1 (base_of_meets hm₁).2.2 h₁ ρ₁)
end two

end Johnson.RunOne.KeyLetters

#print axioms Johnson.RunOne.KeyLetters.near_unique
#print axioms Johnson.RunOne.KeyLetters.list_sent
#print axioms Johnson.RunOne.KeyLetters.no_clash_sent
#print axioms Johnson.RunOne.KeyLetters.base_of_meets
#print axioms Johnson.RunOne.KeyLetters.member_one_every
#print axioms Johnson.RunOne.KeyLetters.member_two_every
