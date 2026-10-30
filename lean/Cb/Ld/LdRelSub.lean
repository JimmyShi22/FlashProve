-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdRelSub.lean: agreement of a subcode: at most that of the whole code plus the list of two
rows of the whole code, under the hypotheses of `Spec.ld_sub_mca`.

This file states a bound on the mutual correlated agreement of a linear subcode, in terms of the
agreement and a list size of two rows of the whole code.
Definitions and statements (each a `Prop` in `Cb.Spec`); the proofs are in
Cb/Ld/LdRelSubProofs.lean. Generic: any finite field, any codes read under a transformation.

Why: the codewords of a code read under a transformation (Cb/Ld/LdRel.lean) are the encodings of
(message, randomness). If message and randomness do not fill the dimension of the code behind
(Code/Iface.lean: msg + r < k: the rest of the generator's input is 0) they form a proper subcode.
What is known on mutual correlated agreement beyond a third of the distance speaks of the whole
code. It does not pass to subcodes by itself: outside the whole code's exceptional values the two
words agree on the set S with codewords c₀, c₁ of the whole code, and c₀ + θ c₁ lies in the subcode;
c₀, c₁ need not.
The lemma: for one pair (c₀, c₁), not both in the subcode, c₀ + θ c₁ lies in the subcode for at most
one θ (the subcode is linear). The pair is a codeword of two rows of the whole code within e of the
two words: there are at most L2 such pairs. So the subcode has at most bad + L2 exceptional values.

Main names:
  `C.SubOf C' φ`: C' is a subcode of C, at the same long words, up to an onto renaming
    φ : C'.Aa → C.Aa of the coordinates of a long symbol: every transformed native word of C' is one
    of C read through φ; every transformed codeword of C' is one of C.
  `Spec.ld_sub_mca`: C.SubOf C' φ; laws of both; C.Dist d, e < d; C.MCAat e bad;
    (C.il Bool).ListAt e L2 ⇒ C'.MCAat e (bad + L2).
  `Spec.ld_sub_il`: rows of a subcode are a subcode of rows.
  `Spec.ld_sub_rows`: the same whatever the number of rows (Cb/Ld/LdRelRows.lean: `MCArows`), if two
    rows of rows of C have lists of at most L2, for all rows.
  `Spec.ld_sub_ld`: a family of codes of Code/Iface.lean with rows under a reading: with r a ≤ r' a
    for all a, T.ld E R at the codes C a is a subcode of the same at the codes (C a).setR (r' a).

Limits: its standing. Where message and randomness fill the dimension (free room is filled with
entries of the message) there is no proper subcode; this lemma is no hypothesis of any headline (it
is proved: Cb/Ld/LdRelSubProofs.lean). It answers the question what becomes of agreement if they do
not. `ld_sub_rows` is applied in Cb/Gl/GlCopyJ.lean (`glCp_rows_of`), Cb/Gl/GlLdJProofs.lean
(`glS_rows`), Cb/Gl/GlLdJAt.lean (`glAt_rowsS`), Cb/Gl/GlFinalAg.lean (`glAg_rowsS`).
This file does not say that the term L2 is needed (no example). It says nothing on lists: a
subcode's list is no longer than the whole code's; below the Johnson radius both follow from laws
and distance.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdRelRows

set_option autoImplicit false

namespace Code

/-- the same generator and message, r' coordinates of randomness -/
@[reducible] def Enc.setR {F : Type} (C : Enc F) (r' : ℕ) : Enc F := { C with r := r' }

end Code

namespace Cb
open Prob

/-- C' is a subcode of C, at the same long words. -/
structure LdCode.SubOf {E P : Type} (C C' : LdCode E P) (φ : C'.Aa → C.Aa) : Prop where
  onto : Function.Surjective φ
  word : ∀ f' : C'.Word, ∃ f : C.Word, ∀ x α, C'.T f' x α = C.T f x (φ α)
  code : ∀ m' r', ∃ m r, ∀ x α, C'.T (C'.enc m' r') x α = C.T (C.enc m r) x (φ α)

namespace Spec
section
variable (E P : Type) [Field E] [Finite E] [Fintype P]

/-- States, under the hypotheses below: C' has at most bad + L2 exceptional values at the radius e.
-/
def ld_sub_mca : Prop :=
  ∀ (C C' : LdCode E P) (φ : C'.Aa → C.Aa) (d e bad L2 : ℕ), C.SubOf C' φ → C.Laws → C'.Laws →
    C.Dist d → e < d → C.MCAat e bad → (C.il Bool).ListAt e L2 → C'.MCAat e (bad + L2)

def ld_sub_il : Prop :=
  ∀ (C C' : LdCode E P) (φ : C'.Aa → C.Aa) (R : Type) [Fintype R] [DecidableEq R],
    C.SubOf C' φ → (C.il R).SubOf (C'.il R) fun α => (α.1, φ α.2)

/-- Whatever the number of rows. -/
def ld_sub_rows : Prop :=
  ∀ (C C' : LdCode E P) (φ : C'.Aa → C.Aa) (d e bad L2 : ℕ), C.SubOf C' φ → C.Laws → C'.Laws →
    C.Dist d → e < d → C.MCArows e bad →
    (∀ (R : Type) [Fintype R] [DecidableEq R], ((C.il R).il Bool).ListAt e L2) →
    C'.MCArows e (bad + L2)

end

/-- States, of families of codes with rows, under a reading: less randomness gives a subcode. -/
def ld_sub_ld (F : Type) [Field F] (E : Type) [Field E] [Algebra F E] : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A] (C : A → Code.Enc F) (r' : A → ℕ) (P : Type)
      [Fintype P] (pos : ∀ a, P → Fin (C a).n) (mult : A → ℕ) (R : A → Type)
      [∀ a, Fintype (R a)] [∀ a, DecidableEq (R a)],
    (∀ a, (C a).r ≤ r' a) →
    ((⟨P, pos, mult⟩ : Reading fun a => (C a).setR (r' a)).ld E R).SubOf
      ((⟨P, pos, mult⟩ : Reading C).ld E R) fun α => α

end Spec
end Cb
