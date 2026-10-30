-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/MustFail.lean: four negative tests on parts of the link prover's algorithm:
a pad set to 0, one pad used twice, a tail one entry short, and the base case's first element by
the prover's own formula. In each, under its premise of non-degeneracy, what the comparison of the
two algorithms needs fails.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

What this file proves. Each theorem holds for all parameters and carries its premise of
non-degeneracy in its statement.
  pad_struck      (1) The pad struck. With both pads of the link's front set to 0 (strikePad), the
                  answer to the link proof's own first OOD sample does not depend on the coins.
                  Two data whose answers then differ are not the same up to any shift of the
                  coins.
  one_pad         (2) One pad for both answers. Assume the pad has an entry of its own (PadRoom S).
                  With the first pad used for both folded rows (onePad), the difference of the two
                  answers does not depend on the coins. Two data with different differences are
                  not the same up to any shift.
  short_misses, tail_short   (3) A tail one coin short. At as many positions, with different
                  points, as the tail is long, a tail whose last entry is forced to 0 misses a
                  family of symbols, whatever the message.
  shown_fixes     (4a) The four lists that the base case's second round discloses fix, entry by
                  entry, "masking word plus sampled element times last message".
  tau_own_fails   (4b) The element of the base case's first round, by the prover's own formula. If
                  the second round's lists agree, the sampled element is not 0, and the claim's left
                  side is not 0 at the difference of the two last messages, then the two first
                  rounds' elements differ. By (4a) there is no other choice of the masking word.

Why. The prover's algorithm and the simulator's algorithm are compared in one form: they disclose
the same up to a shift of the coins that can be undone (UpToShift, Johnson/LinkSim/UpTo.lean;
Spec.linkShift, Johnson/LinkSim/AtText/SpecShift.lean; Spec.linkShiftIn, SpecShiftIn.lean). A
statement of that form is worth something only if it can fail. Here it does in (1) and (2), and what
it needs does in (3) and (4), each time under a premise of non-degeneracy, at the prover's own
definitions (Johnson/Prover/Link/), for the front's pads, a tail and the masking word; a fold's
coefficients and a switch's free entries have no test here. The file proves nothing for hiding: each
theorem says that one function of a weakened algorithm fails what that comparison needs (see Limits:
nothing says that the whole weakened algorithm fails).

How it fits. Under Johnson/LinkSim/ no other file uses these theorems; here tail_short calls
short_misses and tau_own_fails calls shown_fixes. pad_struck and one_pad refute UpToShift,
Spec.linkShift's form, for a weakened part; tail_short and tau_own_fails are stated of values, not
in that form. Defs.lean's head cites tau_own_fails for why the simulator replaces one element;
SpecShift.lean's, for why the premise on the honest run cannot be dropped.

The other names (namespace OnBytes.LinkSim.AtText).
  ansOf           the answer to the link proof's own first OOD sample that the prover's algorithm
                  computes for folded row a, in the field.
  dataAns         the same answer without the pad: a function of the data and the challenges alone.
  strikePad, onePad   the coins with both pads 0; with the first pad used for both folded rows.
  zC              the coins 0: a value of the coins' type, used as a witness.
  ansOf_strike, ansOf_split, ansOf_diff   with the pad struck the answer does not depend on the
                  coins; if PadRoom S, an answer is the data's share plus the pad's, and with one
                  pad for both the difference of the two answers does not depend on the coins.
  wr_inj          two written lists that are equal have equal entries.

Limits.
  - That a premise of non-degeneracy can be met is not proved, for any of the four: (1) two data
    with different answers; (2) two data with different differences; (3) positions with different
    points; (4) a claim whose left side is not 0 there.
  - (3) is stated of values, not of two messages: for a given change of the message the short
    tail may still suffice (for the change "1 at entry 0", if the points add up to 0).
  - They are tests of single functions of the prover's algorithm, not of the whole algorithm.
    Nothing says that the whole weakened algorithm fails, though what fails here is a part of what
    it discloses.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtText.Pad
import Johnson.LinkSim.AtText.PadPlace
import Johnson.LinkSim.AtText.Cols
import Johnson.LinkSim.AtText.Defs
import Johnson.LinkSim.UpTo

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.AtText
open OnBytes OnBytes.Slice Cb
open OnBytes.LinkSim
open Johnson.Prover.Link
open Polynomial

/-! ## The answers to the link proof's own first OOD sample -/

section Front
variable (S : Sz) (t : ℕ) (X X' : LIn S) (C : LCoins) (D : ℕ → Fmt.Drawn)

/-- The answer that the prover's algorithm computes for folded row a, in the field. -/
def ansOf (a : Bool) : GE := smAt S t (lSeed S D) (mu0 S t (lMem S X C D)) a

/-- The same answer without the pad. -/
def dataAns (a : Bool) : GE :=
  smAt S t (lSeed S D) (mu0 S t (frontMem S (lGam S D) X.M₀ X.M₁ 0)) a

end Front

/-- Both pads 0. -/
def strikePad (C : LCoins) : LCoins := { C with pad := fun _ => 0 }

/-- The first pad used for both folded rows. -/
def onePad (C : LCoins) : LCoins := { C with pad := fun _ => C.pad false }

/-- The coins 0. -/
def zC : LCoins where
  pad := fun _ => 0
  tN := fun _ _ _ => 0
  ψN := fun _ => 0
  body :=
    { W := fun _ _ _ => 0
      new := fun _ =>
        { tabM := fun _ => 0, tabZ := fun _ => 0, tM := fun _ _ => 0, tZ := fun _ _ => 0
          fM := fun _ _ => 0, fT := fun _ _ => 0, sM := fun _ => 0, sT := fun _ => 0 }
      fr := fun _ _ => 0 }

section Front
variable (S : Sz) (t : ℕ) (X X' : LIn S) (D : ℕ → Fmt.Drawn)

/-- With the pad struck, the answer does not depend on the coins. -/
theorem ansOf_strike (C C' : LCoins) (a : Bool) :
    ansOf S t X (strikePad C) D a = ansOf S t X (strikePad C') D a := rfl

/-- **(1) The pad struck.** -/
theorem pad_struck (a : Bool)
    (hne : ansOf S t X (strikePad zC) D a ≠ ansOf S t X' (strikePad zC) D a) :
    ¬ UpToShift addC (fun C => ansOf S t X (strikePad C) D a)
      (fun C => ansOf S t X' (strikePad C) D a) := by
  rintro ⟨s, _, h⟩
  exact hne ((h zC).1.trans (ansOf_strike S t X' D _ zC a))

/-- An answer is the data's share plus the pad's. -/
theorem ansOf_split (h : PadRoom S) (C : LCoins) (a : Bool) :
    ansOf S t X C D a = dataAns S t X D a +
      smAt S t (lSeed S D) (mu0 S t fun b => Pi.single S.padJ (C.pad b)) a := by
  unfold ansOf dataAns
  rw [lMem_split S X C D h, smAt_add]

/-- With one pad for both, the difference of the two answers does not depend on the coins. -/
theorem ansOf_diff (h : PadRoom S) (C : LCoins) :
    ansOf S t X (onePad C) D false - ansOf S t X (onePad C) D true =
      dataAns S t X D false - dataAns S t X D true := by
  rw [ansOf_split S t X D h, ansOf_split S t X D h]
  have e : smAt S t (lSeed S D) (mu0 S t fun b => Pi.single S.padJ ((onePad C).pad b)) false =
      smAt S t (lSeed S D) (mu0 S t fun b => Pi.single S.padJ ((onePad C).pad b)) true := by
    rw [smAt_val, smAt_val]
    rfl
  rw [e, add_sub_add_right_eq_sub]

/-- **(2) One pad for both answers.** -/
theorem one_pad (h : PadRoom S)
    (hne : dataAns S t X D false - dataAns S t X D true ≠
      dataAns S t X' D false - dataAns S t X' D true) :
    ¬ UpToShift addC
      (fun C => (ansOf S t X (onePad C) D false, ansOf S t X (onePad C) D true))
      (fun C => (ansOf S t X' (onePad C) D false, ansOf S t X' (onePad C) D true)) := by
  rintro ⟨s, _, hs⟩
  have e := (hs zC).1
  have e1 := congrArg Prod.fst e
  have e2 := congrArg Prod.snd e
  simp only at e1 e2
  apply hne
  rw [← ansOf_diff S t X D h zC, ← ansOf_diff S t X' D h (addC zC (s zC)), e1, e2]

end Front

/-! ## A tail one coin short -/

/-- At r different points, r coefficients of which the last is 0 do not take the values p ^ (r - 1).
-/
theorem short_misses {F : Type} [Field F] (pts : Finset F) (r : ℕ) (hr : 0 < r)
    (hc : pts.card = r) :
    ¬ ∃ c : ℕ → F, c (r - 1) = 0 ∧
      ∀ p ∈ pts, ∑ q ∈ Finset.range r, p ^ q * c q = p ^ (r - 1) := by
  rintro ⟨c, h0, hv⟩
  let P : F[X] := ∑ q ∈ Finset.range r, Polynomial.C (c q) * X ^ q - X ^ (r - 1)
  have hev : ∀ p ∈ pts, P.eval p = 0 := by
    intro p hp
    show (∑ q ∈ Finset.range r, Polynomial.C (c q) * X ^ q - X ^ (r - 1)).eval p = 0
    rw [eval_sub, eval_finset_sum, eval_pow, eval_X, ← hv p hp, sub_eq_zero]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [eval_mul, eval_C, eval_pow, eval_X, mul_comm]
  have hdeg : P.natDegree < pts.card := by
    rw [hc]
    refine lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt ?_ ?_)
    · refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := r - 1) fun q hq => ?_)
        (by omega)
      refine le_trans (natDegree_C_mul_X_pow_le _ _) ?_
      have := Finset.mem_range.1 hq
      omega
    · rw [natDegree_X_pow]
      omega
  have hz : P = 0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P pts hev hdeg
  have hco : P.coeff (r - 1) = -1 := by
    show (∑ q ∈ Finset.range r, Polynomial.C (c q) * X ^ q - X ^ (r - 1)).coeff (r - 1) = -1
    rw [coeff_sub, finset_sum_coeff, coeff_X_pow, if_pos rfl,
      Finset.sum_eq_single (r - 1)]
    · rw [coeff_C_mul_X_pow, if_pos rfl, h0, zero_sub]
    · intro q _ hq
      rw [coeff_C_mul_X_pow, if_neg (Ne.symm hq)]
    · intro hn
      exact absurd (Finset.mem_range.2 (by omega)) hn
  rw [hz, coeff_zero] at hco
  exact one_ne_zero (neg_eq_zero.1 hco.symm)

open Classical in
/-- **(3) A tail one coin short**: at as many positions with different points as the tail is long, a
tail whose last entry is 0 misses a family of symbols, whatever the message. -/
theorem tail_short (C : Fmt.M1.Code) (Q : Finset ℕ) (hr : 0 < C.r) (hQ : Q.card = C.r)
    (hinj : Set.InjOn (ptG C.a) Q) (m : ℕ → GE) :
    ∃ v : ℕ → GE, ¬ ∃ tl : ℕ → GE, tl (C.r - 1) = 0 ∧ ∀ x ∈ Q, symG C x m tl = v x := by
  refine ⟨fun x => ptG C.a x ^ (C.r - 1) + msgPart C.r C.l (ptG C.a x) m, ?_⟩
  rintro ⟨tl, h0, hv⟩
  refine short_misses (Q.image (ptG C.a)) C.r hr
    (by rw [Finset.card_image_of_injOn hinj, hQ]) ⟨tl, h0, fun p hp => ?_⟩
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hp
  have e := hv x hx
  rw [symG_eq] at e
  unfold sym at e
  exact add_right_cancel e

/-! ## The base case -/

/-- Two written lists that are equal have equal entries. -/
theorem wr_inj (n : ℕ) (f g : ℕ → GE) (h : wr n f = wr n g) : ∀ j, j < n → f j = g j :=
  fun j hj => by rw [← lst_wr n f j hj, ← lst_wr n g j hj, h]

/-- (4a) What the base case's second round discloses fixes "masking word plus sampled element
times last message", entry by entry, in all four lists. -/
theorem shown_fixes (C Z : Fmt.M1.Code) (lam : Fmt.M1.E)
    (m0 r0 m1 r1 h0 s0 h1 s1 m0' r0' m1' r1' h0' s0' h1' s1' : ℕ → GE)
    (h : shownAll C Z lam m0 r0 m1 r1 h0 s0 h1 s1 =
      shownAll C Z lam m0' r0' m1' r1' h0' s0' h1' s1') :
    (∀ j, j < C.l → h0 j + toE lam * m0 j = h0' j + toE lam * m0' j) ∧
    (∀ j, j < Z.l → h1 j + toE lam * m1 j = h1' j + toE lam * m1' j) ∧
    (∀ q, q < C.r → s0 q + toE lam * r0 q = s0' q + toE lam * r0' q) ∧
    (∀ q, q < Z.r → s1 q + toE lam * r1 q = s1' q + toE lam * r1' q) := by
  unfold shownAll at h
  obtain ⟨a1, h⟩ := List.append_inj h (by rw [length_wr, length_wr])
  obtain ⟨a2, h⟩ := List.append_inj h (by rw [length_wr, length_wr])
  obtain ⟨a3, a4⟩ := List.append_inj h (by rw [length_wr, length_wr])
  exact ⟨wr_inj _ _ _ a1, wr_inj _ _ _ a2, wr_inj _ _ _ a3, wr_inj _ _ _ a4⟩

/-- (4b) The first round's element, computed by the prover's own formula, differs between two runs
whose second rounds agree, if the sampled element and the claim at the difference are not 0. -/
theorem tau_own_fails (C Z : Fmt.M1.Code) (c d : Array Fmt.M1.E) (lam : Fmt.M1.E)
    (m0 r0 m1 r1 h0 s0 h1 s1 m0' r0' m1' r1' h0' s0' h1' s1' : ℕ → GE)
    (h : shownAll C Z lam m0 r0 m1 r1 h0 s0 h1 s1 =
      shownAll C Z lam m0' r0' m1' r1' h0' s0' h1' s1')
    (hl : toE lam ≠ 0)
    (hcl : formG C.l c (fun j => m0 j - m0' j) + formG Z.l d (fun j => m1 j - m1' j) ≠ 0) :
    tauSW C Z c d h0' h1' ≠ tauSW C Z c d h0 h1 := by
  obtain ⟨a1, a2, -, -⟩ := shown_fixes C Z lam m0 r0 m1 r1 h0 s0 h1 s1 m0' r0' m1' r1' h0' s0' h1'
    s1' h
  have e0 : formG C.l c h0' = formG C.l c fun j => h0 j + toE lam * (m0 j - m0' j) :=
    formG_congr _ _ _ _ fun j hj => by
      have := a1 j hj
      linear_combination -this
  have e1 : formG Z.l d h1' = formG Z.l d fun j => h1 j + toE lam * (m1 j - m1' j) :=
    formG_congr _ _ _ _ fun j hj => by
      have := a2 j hj
      linear_combination -this
  intro ht
  have ht' := congrArg toE ht
  unfold tauSW at ht'
  rw [toE_ofE, toE_ofE, e0, e1, tauSW_line] at ht'
  exact mul_ne_zero hl hcl (add_eq_left.1 ht')

end OnBytes.LinkSim.AtText

#print axioms OnBytes.LinkSim.AtText.pad_struck
#print axioms OnBytes.LinkSim.AtText.one_pad
#print axioms OnBytes.LinkSim.AtText.short_misses
#print axioms OnBytes.LinkSim.AtText.tail_short
#print axioms OnBytes.LinkSim.AtText.shown_fixes
#print axioms OnBytes.LinkSim.AtText.tau_own_fails
