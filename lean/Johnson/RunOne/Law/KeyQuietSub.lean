-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/KeyQuietSub.lean: the table of joints of the key file: the two halves of a row that closes pins and lays a message (the proximity tests' rows): two rules, general in F G at_ Mg, beside the tables' files' onAt_fwd and relAt_back (Johnson/Desc/Key/KeyQuiet.lean, whose head says: "what is not here: a row that opens or closes a pin (the sendings; the tests)"). Statements with proofs. It imports that file alone (whose own head says "No Mathlib").
Object. `onAt` and `relAt` (Johnson/Desc/Key/KeyBorders.lean): the promise and the relation at a border.
User. Whoever pays a row that closes pins: 1.15 · 2.9 · 2.10 · 3.2.
Letters. All free: the description F, the reading G, the seats at_, the meaning Mg, the two states a (in front) and a' (behind), the two strings y | y', the open sets.

  onAt_fwd_sub: the promise's half: onAt_fwd with two premises weakened to what its proof spends: the pins open behind are among those open in front (an inclusion for an equation) · the samples agree at the pins still open behind (not at every seat; and of the reading's two letters that SamePins compares, smp and recOf, the second is no premise here: onAt_fwd's own proof does not spend it) · and "a record that is unmarked behind was unmarked in front" in the meaning's own word.
  onAt_fwd_sub's premises hfree and hsmp may spend the book-keeping in front besides: "shape a.2 = true → free a y → free' a' y'" and "shape a.2 = true → free a y → ∀ k ∈ pinned O', …": weaker premises, the same conclusion: in the promise the two stand side by side.
  onAt_fwd_case: onAt_fwd's kind of premises (an equation of the pins; SamePins) give these, still general in Mg and at two states.
  onAt_fwd_is: onAt_fwd's own statement, to the letter (at (p, s) (p, s'), the meaning meaning₁ …, "X.marked s = X.marked s'"), by one call: so that rule is this one's case, and the one may be swapped for the other.
  relAt_back_to: the claim's half: relAt_back with another witness in front (w behind, w' in front): in the row's law's and the frames' conclusions and in the rule's. The caller names w' (a witness with a message laid).
  relAt_back_case: at w' := w it is relAt_back's statement.
Limits. Rules: as empty as their premises. No block is shown to have them. Nothing on soundness, nothing on hiding.

-/
import Johnson.Desc.Key.KeyQuiet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.KeyQuietSub
open OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.Key

section
variable {XI P S Cells M Smp Rec : Type} (F : FileDescription XI) (G : Reading (P × S) Cells M Smp Rec) (at_ : Where) (Mg : KMeaning P S (Wit Cells Unit M))

/-- **The promise's half of a row that closes pins and opens none.** a: the state in front; a': behind. -/
theorem onAt_fwd_sub (shape shape' : S → Bool) (free free' : P × S → Strs → Prop) (O O' : List KItem)
    (hpin : ∀ k ∈ pinned O', k ∈ pinned O) (a a' : P × S) (y y' : Strs)
    (hm : Mg.unmarked a' → Mg.unmarked a)
    (hsmp : shape a.2 = true → free a y → ∀ k ∈ pinned O', G.smp a (at_ k).1 (at_ k).2 = G.smp a' (at_ k).1 (at_ k).2)
    (Hy : StrsStay F at_ O y y') (hfree : shape a.2 = true → free a y → free' a' y') (step : shape a.2 = true → shape' a'.2 = true)
    (h : onAt F G at_ Mg shape free O a y) : onAt F G at_ Mg shape' free' O' a' y' := by
  cases h with
  | inl hn => exact Or.inl fun hu => hn (hm hu)
  | inr hr =>
    obtain ⟨h1, h2, h3, h4⟩ := hr
    have hsmp := hsmp h1 h3
    refine Or.inr ⟨step h1, ?_, hfree h1 h3, ?_⟩
    · refine List.all_eq_true.2 fun k hk => ?_
      have h5 := List.all_eq_true.1 h2 k (hpin k hk)
      simp only [hasSmp] at h5 ⊢
      rw [← hsmp k hk]
      exact h5
    · intro k hk o z ho hz m m' hm1 hm2
      exact h4 k (hpin k hk) o z ho ((hsmp k hk).trans hz) m m'
        ((member_congr F G o _ _ y y' z m (Hy.word k (hpin k hk))).1 hm1)
        ((member_congr F G o _ _ y y' z m' (Hy.word k (hpin k hk))).1 hm2)

/-- The tables' files' rule for a row that turns no pin (onAt_fwd) is this rule's case. -/
theorem onAt_fwd_case (shape shape' : S → Bool) (free free' : P × S → Strs → Prop) (O O' : List KItem)
    (hpin : pinned O' = pinned O) (a a' : P × S) (y y' : Strs) (hm : Mg.unmarked a' → Mg.unmarked a)
    (hP : SamePins G a a') (Hy : StrsStay F at_ O y y') (hfree : free a y → free' a' y')
    (step : shape a.2 = true → shape' a'.2 = true) (h : onAt F G at_ Mg shape free O a y) :
    onAt F G at_ Mg shape' free' O' a' y' :=
  onAt_fwd_sub F G at_ Mg shape shape' free free' O O' (fun k hk => hpin ▸ hk) a a' y y' hm
    (fun _ _ _ _ => hP.smp _ _) Hy (fun _ => hfree) step h

/-- **The claim's half of any row, with another witness in front.** w: behind; w': in front. -/
theorem relAt_back_to (r : KRow) (O : List KItem) (a a' : P × S) (y y' : Strs) (w w' : Wit Cells Unit M)
    (hctx : ∀ i ∈ r.ctx, i ∈ O ∧ i ∉ r.ins)
    (law : (∀ i ∈ r.outs ++ r.ctx, i.holds F G at_ Mg a' y' w) → ∀ i ∈ r.ins, i.holds F G at_ Mg a y w')
    (ride : ∀ i ∈ O, i ∉ r.ins → i.holds F G at_ Mg a' y' w → i.holds F G at_ Mg a y w')
    (h : relAt F G at_ Mg (stepOpen O r) a' y' w) : relAt F G at_ Mg O a y w' := by
  intro i hi
  by_cases hin : i ∈ r.ins
  · refine law (fun j hj => ?_) i hin
    rcases List.mem_append.1 hj with ho | hc
    · exact h j (mem_step_of_out O r j ho)
    · exact h j (mem_step_of_rest O r j (hctx j hc).1 (hctx j hc).2)
  · exact ride i hi hin (h i (mem_step_of_rest O r i hi hin))

/-- At the same witness it is the tables' files' rule relAt_back, to the letter of its statement. -/
theorem relAt_back_case (r : KRow) (O : List KItem) (a a' : P × S) (y y' : Strs) (w : Wit Cells Unit M)
    (hctx : ∀ i ∈ r.ctx, i ∈ O ∧ i ∉ r.ins)
    (law : (∀ i ∈ r.outs ++ r.ctx, i.holds F G at_ Mg a' y' w) → ∀ i ∈ r.ins, i.holds F G at_ Mg a y w)
    (ride : ∀ i ∈ O, i ∉ r.ins → i.holds F G at_ Mg a' y' w → i.holds F G at_ Mg a y w)
    (h : relAt F G at_ Mg (stepOpen O r) a' y' w) : relAt F G at_ Mg O a y w :=
  relAt_back_to F G at_ Mg r O a a' y y' w w hctx law ride h

end

section
variable {XI P S Cells M Smp Rec : Type} (F : FileDescription XI) (G : Reading (P × S) Cells M Smp Rec) (at_ : Where)
  (K : KPlan) (R : KRead Cells M) (X : KReaders S)
  (near : Nat → P × S → Strs → Prop) (forms worth other : Nat → String → P × S → Strs → Wit Cells Unit M → Prop)

/-- **onAt_fwd, ITS STATEMENT TO THE LETTER** (Johnson/Desc/Key/KeyQuiet.lean: its variables, its binders, its meaning), by one call of the rule above. -/
theorem onAt_fwd_is (shape shape' : S → Bool) (free free' : P × S → Strs → Prop) (O O' : List KItem) (hpin : pinned O' = pinned O) (p : P) (s s' : S) (y y' : Strs)
    (hm : X.marked s = X.marked s') (hP : SamePins G (p, s) (p, s')) (Hy : StrsStay F at_ O y y') (hfree : free (p, s) y → free' (p, s') y') (step : shape s = true → shape' s' = true)
    (h : onAt F G at_ (meaning₁ K R X near forms worth other) shape free O (p, s) y) : onAt F G at_ (meaning₁ K R X near forms worth other) shape' free' O' (p, s') y' :=
  onAt_fwd_case F G at_ (meaning₁ K R X near forms worth other) shape shape' free free' O O' hpin (p, s) (p, s') y y'
    (fun hu => hm.trans hu) hP Hy hfree step h

end

end Johnson.RunOne.Law.KeyQuietSub

#print axioms Johnson.RunOne.Law.KeyQuietSub.onAt_fwd_sub
#print axioms Johnson.RunOne.Law.KeyQuietSub.onAt_fwd_case
#print axioms Johnson.RunOne.Law.KeyQuietSub.relAt_back_to
#print axioms Johnson.RunOne.Law.KeyQuietSub.relAt_back_case
#print axioms Johnson.RunOne.Law.KeyQuietSub.onAt_fwd_is
