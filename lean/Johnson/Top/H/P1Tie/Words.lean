-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/P1Tie/Words.lean: the masked sumcheck's short text (Johnson/Desc/Part/MaskedSum4.lean)
and the verifier program's plain functions (OnBytes/Iop/Psc.lean, OnBytes/Model/Psc.lean): where the
two part, they give the same words. Theorems.

What is shown. At a variable that is summed at a point the two texts part in two expressions alone:
the coefficient that is not sent (`complete_eq`) and psi at the challenge (`psi_eq`). In both, each
side is the output of a field operation. An output has words below the prime whatever went in
(`okE_add`, `okE_sub`, `okE_mul`, over Fmt/FieldE.lean's ok_add, ok_sub); the reading into the field
is a homomorphism at all words (OnBytes/Slice/ProgField.lean: readE_add, readE_sub, readE_mul: no
premise); and two elements with words below the prime and one reading are one (readE_inj, there). So
these are equations of machine words, at all words: no premise says that a sent scalar, a draw or a
coordinate is below the prime. All else is a re-spelling of lists: `hiding_eq`, `addSlots_eq`,
`walk_eq`, `rowForm_eq` (over `powers_eq`, which is imported).

Imported from Johnson/Desc/Part/MaskedSumTie.lean, a file on the same two texts whose equations are
under a reading, and not said a second time here: Var.weight, Var.weight_d, powersLoop_eq,
powers_eq, asW, zip_weight, rowAff (and one_of_length, which Johnson/Top/H/P1Tie/Tie1.lean spends).
Taken over from it: the way in which its proofs show the two walks' arms.

Limits. NOT AT A VARIABLE THAT IS SUMMED PLAINLY: there psi at the challenge is the raw challenge in
the one text and an output in the other: these can part as words at a challenge that is not below
the prime. Every statement on psi asks `Var.isPoint`. A tie of two texts: it has no error term.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Part.MaskedSum4
import Johnson.Desc.Part.MaskedSumTie
import OnBytes.Model.Psc
import OnBytes.Slice.ProgField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Part.MaskedSum
open OnBytes
open OnBytes.Model (Aff Fork Psc)
open OnBytes.Slice (readE readE_add readE_sub readE_mul readE_zero readE_one readE_inj)

/-! ## An output has words below the prime -/

theorem okE_add (a b : E) : okE (addE a b) = true := by
  rw [okE_triple, addE_triple]
  simp only [Fmt.Fld.okE, Fmt.Fld.addE, Fmt.Fld.ok_add, Bool.and_self]

theorem okE_sub (a b : E) : okE (subE a b) = true := by
  rw [okE_triple, subE_triple]
  simp only [Fmt.Fld.okE, Fmt.Fld.subE, Fmt.Fld.ok_sub, Bool.and_self]

theorem okE_mul (a b : E) : okE (mulE a b) = true := by
  rw [okE_triple, mulE_triple]
  simp only [Fmt.Fld.okE, Fmt.Fld.mulE, Fmt.Fld.ok_add, Bool.and_self]

theorem okE_one : okE oneE = true := rfl

/-! ## The two places where the texts part -/

theorem foldl_add_read : ∀ (l : List E) (a : E), readE (l.foldl addE a) = readE a +
    (l.map readE).sum
  | [], a => by simp
  | x :: l, a => by
    rw [List.foldl_cons, foldl_add_read l (addE a x), readE_add, List.map_cons, List.sum_cons]
    ring

theorem dot_rep_read (z : E) : ∀ (l : List E) (n : Nat) (a : E), l.length ≤ n →
    readE (((List.replicate n z).zip l).foldl (fun r p => addE r (mulE p.1 p.2)) a) =
      readE a + readE z * (l.map readE).sum
  | [], n, a, _ => by
    rw [List.zip_nil_right, List.foldl_nil, List.map_nil, List.sum_nil, mul_zero, add_zero]
  | x :: l, 0, a, h => absurd h (Nat.not_succ_le_zero l.length)
  | x :: l, n + 1, a, h => by
    rw [List.replicate_succ, List.zip_cons_cons, List.foldl_cons,
      dot_rep_read z l n (addE a (mulE z x)) (Nat.le_of_succ_le_succ h), readE_add, readE_mul,
      List.map_cons, List.sum_cons, mul_add, add_assoc]

/-- (I1) **The coefficient that is not sent**: the same words, at all words. -/
theorem fixed_eq (z c : E) (s : List E) (d : Nat) (hl : s.length + 1 = d) :
    mulE (subE c (OnBytes.Psc.dot (oneE :: List.replicate (d - 1) z) (zeroE :: s))) oneE =
      subE c (mulE z (total s)) := by
  apply readE_inj _ _ (okE_mul _ _) (okE_sub _ _)
  have e1 : readE (OnBytes.Psc.dot (oneE :: List.replicate (d - 1) z) (zeroE :: s)) =
      readE z * (s.map readE).sum := by
    unfold OnBytes.Psc.dot
    simp only [List.zip_cons_cons, List.foldl_cons]
    rw [dot_rep_read z s (d - 1) _ (by omega), readE_add, readE_mul, readE_zero, readE_one]
    ring
  have e2 : readE (total s) = (s.map readE).sum := by
    unfold total
    rw [foldl_add_read, readE_zero]
    ring
  rw [readE_mul, readE_sub, e1, readE_one, readE_sub, readE_mul, e2]
  ring

/-- The variable is summed at a point. -/
def Var.isPoint : Var → Bool
  | .plain _ => false
  | .point _ _ => true

/-- **A round's completed polynomial is `verify-on-bytes`'s, word for word.** -/
theorem complete_eq (z c : E) (s : List E) (d : Nat) (hl : s.length + 1 = d) :
    (OnBytes.Psc.Weight.equality z d).complete s c = complete (.point z d) s c := by
  show mulE (subE c (OnBytes.Psc.dot (oneE :: List.replicate (d - 1) z) (zeroE :: s))) oneE :: s =
    subE c (mulE z (total s)) :: s
  rw [fixed_eq z c s d hl]

/-- (I2) **psi at the challenge**: the same words, at all words. -/
theorem psi_eq (g : E) : addE (mulE zeroE g) oneE = oneE := by
  apply readE_inj _ _ (okE_add _ _) okE_one
  rw [readE_add, readE_mul, readE_zero, readE_one]
  ring

theorem psi_word (v : Var) (hv : v.isPoint = true) (r : E) :
    OnBytes.Psc.polyAt v.weight.psi r = psiAt v r := by
  cases v with
  | plain d => cases hv
  | point z d =>
    show addE (mulE zeroE r) oneE = oneE
    exact psi_eq r

theorem valueAt_eq (g : List E) (x : E) : OnBytes.Psc.polyAt g x = valueAt g x := rfl

/-- 1 times 1 is 1, as words. -/
theorem one_mul_one : mulE oneE oneE = oneE := by
  apply readE_inj _ _ (okE_mul _ _) okE_one
  rw [readE_mul, readE_one]
  ring

/-- **The program's two tests on a weight hold at every point**, where the polynomial has two
coefficients at least. -/
theorem equality_held (z : E) (d : Nat) (hd : 2 ≤ d) :
    ((OnBytes.Psc.Weight.equality z d).fits && Model.weightHeld (OnBytes.Psc.Weight.equality z d)) =
      true := by
  have h1 : (OnBytes.Psc.Weight.equality z d).fits = true := by
    simp only [OnBytes.Psc.Weight.fits, OnBytes.Psc.Weight.equality, List.length_cons,
      List.length_replicate,
      List.length_nil, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    omega
  have h2 : OnBytes.Psc.dot (oneE :: List.replicate (d - 1) z) [oneE] = oneE := by
    unfold OnBytes.Psc.dot
    simp only [List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil]
    apply readE_inj _ _ (okE_add _ _) okE_one
    rw [readE_add, readE_mul, readE_zero, readE_one]
    ring
  have h3 : Model.weightHeld (OnBytes.Psc.Weight.equality z d) = true := by
    show (mulE oneE oneE == oneE && OnBytes.Psc.dot (oneE :: List.replicate (d - 1) z) [oneE] ==
      oneE) = true
    rw [one_mul_one, h2]
    simp
  rw [h1, h3]
  rfl

/-! ## The hiding polynomial -/

/-- **The hiding polynomial's linear form and P are `verify-on-bytes`'s, word for word**, where
every variable is summed at a point. -/
theorem hiding_eq : ∀ (l : List (Var × E)), (∀ p ∈ l, p.1.isPoint = true) →
    OnBytes.Psc.hidingWalk (l.map asW) = hidingAt l
  | [], _ => rfl
  | [(v, r)], h => by
    show (OnBytes.Psc.powers oneE r v.weight.d, OnBytes.Psc.polyAt v.weight.psi r) =
      (powersFrom r v.d oneE, psiAt v r)
    rw [powers_eq, Var.weight_d, psi_word v (h (v, r) (by simp)) r]
  | (v, r) :: q :: rest, h => by
    have ih := hiding_eq (q :: rest) (fun p hp => h p (List.mem_cons_of_mem _ hp))
    show (OnBytes.Psc.powers (mulE (OnBytes.Psc.hidingWalk ((q :: rest).map asW)).2 r) r
      (v.weight.d - 1) ++
        (OnBytes.Psc.hidingWalk ((q :: rest).map asW)).1,
      mulE (OnBytes.Psc.hidingWalk ((q :: rest).map asW)).2 (OnBytes.Psc.polyAt v.weight.psi r)) =
      (powersFrom r (v.d - 1) (mulE (hidingAt (q :: rest)).2 r) ++ (hidingAt (q :: rest)).1,
        mulE (hidingAt (q :: rest)).2 (psiAt v r))
    rw [ih, powers_eq, Var.weight_d, psi_word v (h (v, r) (by simp)) r]

/-! ## The row -/

theorem slots_fold : ∀ (u : List E) (s : Nat × Aff), u.foldl Model.addSlot s =
    u.foldl (fun (s : Nat × Aff) x => (s.1 + 1, Aff.addMul s.2 (Aff.slot s.1) x)) s
  | [], _ => rfl
  | x :: u, (j, a) => by
    rw [List.foldl_cons, List.foldl_cons]
    exact slots_fold u _

theorem addSlots_eq (a : Aff) (first : Nat) (u : List E) :
    Model.addSlots a first u.toArray = onSlots a first u := by
  unfold Model.addSlots onSlots
  rw [← slots_fold, ← Array.foldl_toList]

/-- **`verify-on-bytes`'s record of a sumcheck as it was heard.** ended: the round in the further
variable has been run. No row is made yet. -/
def Heard.psc (h : Heard) (ended : Bool) : Psc :=
  { start := h.start, target := h.target, eps := h.eps, claim := h.claim, first := h.first
    vars := (h.vars.map Var.weight).toArray, r := h.r.toArray
    ended := ended, rowMade := false, started := true }

theorem walk_eq (h : Heard) (b : Bool) (hp : ∀ v ∈ h.vars, v.isPoint = true) :
    (h.psc b).walk = hidingAt (h.vars.zip h.r) := by
  unfold Model.Psc.walk
  rw [OnBytes.zipT_eq]
  show OnBytes.Psc.hidingWalk ((h.vars.map Var.weight).zip h.r) = _
  rw [zip_weight, hiding_eq _ (fun p hq => hp p.1 (List.of_mem_zip (a := p.1) (b := p.2) hq).1)]

/-- **The row's form is `verify-on-bytes`'s, term for term.** -/
theorem rowForm_eq (h : Heard) (b : Bool) (hp : ∀ v ∈ h.vars, v.isPoint = true) (S0 : E)
    (kept : Aff) :
    (h.psc b).rowForm S0 kept = rowAff h S0 kept := by
  unfold Model.Psc.rowForm
  simp only [walk_eq h b hp, addSlots_eq]
  rfl

end VerifiableInference.Desc.Part.MaskedSum

#print axioms VerifiableInference.Desc.Part.MaskedSum.complete_eq
#print axioms VerifiableInference.Desc.Part.MaskedSum.hiding_eq
#print axioms VerifiableInference.Desc.Part.MaskedSum.rowForm_eq
#print axioms VerifiableInference.Desc.Part.MaskedSum.equality_held
