-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
In this library the records through which a count for agreement is claimed (`IsGlJ`, `IsGlS`:
Cb/Gl/GlLdJ.lean; `IsGlCpJ`: Cb/Gl/GlCopy.lean) do not ask a
radius within half the distance, and the fact on agreement, `Gl.AgreeJ`, is stated nowhere as a
separate theorem: it follows, by one application that is written down nowhere, from `Cb.BCHKS46At`
(`Cb.Gl.glAg_ofAt`, Cb/Gl/GlFinalAg.lean), which this library proves in Cb/Bridge (bchks46At), from
files adapted from ArkLib and Mathlib (lean/LIMITS.md,
L15), and applies in second forms of some of its theorems (files named `…Codes.lean` under
Johnson/; a bound on the entry file's closed check); this file
does not apply that proof.
So read the Lean text, not the words below, to see
what is a hypothesis here: neither "the statement on codes" nor "the fact on agreement" in these
words tells whether it is one.
A theorem with no premise rests on nothing unproved beyond Lean's three axioms (a theorem's premises
are the hypotheses in its statement; how the axioms are checked: lean/CHECKING.md). A theorem that
has the premise Gl.AgreeJ takes it as a hypothesis: this library states it nowhere as a separate
theorem (only its conclusion within half the distance: agreeHalf, Cb/Gl/GlAgreeHalf.lean). A
statement that has the premise Cb.BCHKS46, BCHKS46F or BCHKS46At takes it as a hypothesis; this file
does not prove it. Cb/Bridge/ proves BCHKS46 and BCHKS46At from the files under ThirdParty/,
which are adapted from ArkLib and Mathlib, and BCHKS46F follows from the first by one
line
(Cb.bchks46F_of_wide). Its
source: Theorem 4.6 of the full version (ePrint 2025/2055) of a paper published at STOC 2026; the
theorem is not in the proceedings, which state the plain form (their Theorem 1.5). Of a statement
with any other premise these lines say nothing: it rests on what that premise asks. (More on the
source, of which no full proof was checked for this library: the head of
Cb/Gen/CodeListRS.lean.) Cb/Gen/CodeRepRS.lean: several Reed-Solomon codes of different lengths,
read at common positions (a group under an even reading): list size and mutual correlated agreement
below the Johnson radius of the group.

Statements and proofs. This file shows that the results of five files fit together:
Cb/Gen/JohnsonList.lean, Cb/Gen/CodeList.lean, Cb/Gen/CodeListRS.lean, Cb/Gen/CodeListRows.lean,
Cb/Gen/CodeRep.lean.
A group is a family of codes C a, each with its own length. A reading T (`Reading`,
Cb/Gen/CodeRep.lean) has one set of long positions, each read at one position of every component a;
it is even (`Reading.Even`) if every position of a is read exactly mult a > 0 times. Radii under T
count long positions.

Main names:
  `Spec.inJohnson_comp`: a long radius below the Johnson radius of the group (m n positions,
    distance D <= m d) is, as a fraction, below the Johnson radius of the component (n positions,
    distance d): no separate condition on the components is needed;
  Spec.rs_group_prox **under the one hypothesis BCHKS46** (Cb/Gen/CodeListRS.lean: stated in its
    source with an outline of a proof; taken as a named hypothesis; see that file's header for how
    far the source carries): for Reed-Solomon codes of dimensions k a + 1 on n a distinct points,
    tables of any rows, any even reading T with N long positions, and any
    D <= mult a * (n a - k a), with 0 < k a < n a for all a: at every long radius e below the
    Johnson radius for (N, D) with mult a <= e for all a, the list under T has at most
    `listMax N D e` members, and at most the sum over a of the theorem's counts (`bchksBound`,
    Cb/Gen/CodeListRS.lean) (rounded down) at the radii e / mult a values of θ are exceptional.

Limits: except that `Spec.inJohnson_comp` has no premise m ≤ e, no statement of this file speaks of
radii e < mult a (for some a). The component's radius is then 0, which the statement on codes
(`Cb.BCHKS46`) leaves out; `Cb.prox_third` covers it (its premise: `HasDist C.G C.d`; its radii:
3 e < d). This file says nothing on numerals: whether the count is small against a given field is
not looked at.
Terms: lean/GLOSSARY.md.
-/
import Cb.Gen.CodeRepProofs

set_option autoImplicit false

namespace Cb
open Prob Blocks

namespace Spec

def even_card : Prop :=
  ∀ (F A : Type) (C : A → Code.Enc F) (T : Reading C),
    T.Even → ∀ a, Fintype.card T.P = T.mult a * (C a).n

def inJohnson_comp : Prop :=
  ∀ n d m D e : ℕ, D ≤ m * d → InJohnson (m * n) D e → InJohnson n d (e / m)

def rs_group_prox : Prop :=
  BCHKS46 →
  ∀ (F E : Type) [Field F] [Field E] [Finite E] [Algebra F E] (A : Type) [Fintype A]
      (n k msg r : A → ℕ) (x : ∀ a, Fin (n a) → F),
    (∀ a, Function.Injective (x a)) → (∀ a, 0 < k a) → (∀ a, k a < n a) →
    ∀ T : Reading (fun a => Code.RS.code (x a) (k a + 1) (msg a) (r a) 0 0), T.Even →
      ∀ D : ℕ, (∀ a, D ≤ T.mult a * (n a - k a)) →
        ∀ (R : A → Type) [∀ a, Finite (R a)], T.Prox E R
          (fun e => InJohnson (Fintype.card T.P) D e ∧ ∀ a, T.mult a ≤ e)
          (fun e => listMax (Fintype.card T.P) D e)
          (fun e => ∑ a, ⌊bchksBound (n a) (k a) (e / T.mult a)⌋₊)

end Spec

open CodeRep CodeListRS

theorem even_card : Spec.even_card := by
  intro F A C T hT a
  have h := cnt_comp_even (T.pos a) (T.mult a) (hT a).2 (fun _ => True)
  rwa [cnt_true, cnt_true, Fintype.card_fin] at h

theorem inJohnson_comp : Spec.inJohnson_comp := by
  intro n d m D e hD h
  unfold InJohnson at *
  have h1 : m * (n - d) ≤ m * n - D := by
    rw [Nat.mul_sub]
    omega
  have h2 : m * n - e ≤ m * (n - e / m) := by
    have := Nat.mul_div_le e m
    rw [Nat.mul_sub]
    omega
  have h3 : (m * m) * (n * (n - d)) < (m * m) * (n - e / m) ^ 2 :=
    calc (m * m) * (n * (n - d)) = (m * n) * (m * (n - d)) := by ring
      _ ≤ (m * n) * (m * n - D) := Nat.mul_le_mul_left _ h1
      _ < (m * n - e) ^ 2 := h
      _ ≤ (m * (n - e / m)) ^ 2 := Nat.pow_le_pow_left h2 2
      _ = (m * m) * (n - e / m) ^ 2 := by ring
  exact Nat.lt_of_mul_lt_mul_left h3

-- Limit: the statement has the premise `Cb.BCHKS46`, a hypothesis; this file does not prove it.
theorem rs_group_prox : Spec.rs_group_prox := by
  intro H F E _ _ _ _ A _ n k msg r x hx hk hkn T hT D hD R _
  have hd : ∀ a, HasDist (Code.RS.code (x a) (k a + 1) (msg a) (r a) 0 0).G
      (Code.RS.code (x a) (k a + 1) (msg a) (r a) 0 0).d :=
    fun a => Code.RS.code_dist (hx a) (hkn a)
  have hD' : ∀ a, D ≤ T.mult a * (Code.RS.code (x a) (k a + 1) (msg a) (r a) 0 0).d := fun a => by
    show D ≤ T.mult a * (n a - (k a + 1) + 1)
    rw [dist_eq (hkn a)]
    exact hD a
  have hP := prox_johnson_of_comps F E A _ T hT hd D hD' R _ _ _ fun a =>
    rs_prox H F E (n a) (k a) (msg a) (r a) 0 0 (x a) (hx a) (hk a)
  have hok : ∀ e, (InJohnson (Fintype.card T.P) D e ∧ ∀ a, T.mult a ≤ e) →
      InJohnson (Fintype.card T.P) D e ∧
      ∀ a, 0 < e / T.mult a ∧ n a * k a < (n a - e / T.mult a) ^ 2 := by
    intro e he
    refine ⟨he.1, fun a => ⟨Nat.div_pos (he.2 a) (hT a).1, ?_⟩⟩
    have hc : Fintype.card T.P = T.mult a * n a := even_card F A _ T hT a
    have h1 := he.1
    rw [hc] at h1
    have h2 := inJohnson_comp (n a) (n a - k a) (T.mult a) D e (hD a) h1
    unfold InJohnson at h2
    rwa [Nat.sub_sub_self (hkn a).le] at h2
  exact ⟨fun e he => hP.list e (hok e he), fun e he => hP.mca e (hok e he)⟩

end Cb
