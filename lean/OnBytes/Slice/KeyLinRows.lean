-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/KeyLinRows.lean: the rows that the test for a linear claim leaves, as vectors on the
tables of proximity tests' first stages.

The test for a linear claim on a stored table (OnBytes/Slice/KeyLinVec.lean) leaves rows on three
vectors w', u', ω'. In a key's chains the three vectors are parts of sent messages, and each row is
closed by a proximity test on a group of sent messages (OnBytes/Slice/KeyGroup.lean). This file
writes each row as a vector on the entries of a stage's tables and shows that its value at the
members' messages is the row's.

A vector is made of coefficients on some entries of one member (Gp.push), and of sums and
differences of such vectors. Gp.val is the value of a vector at the members' messages, the left
side of a row in Gp.RowsHold. The weights of a row may be any elements: the dot product's row has
the claim's weights written out.

The rows, each for any group that has the members named:
 the evaluation's row on w' and on mask entries of a further member (evalV, eval_iff);
 the dot product's row on ω' and w' (dotV, dot_iff);
 a drawn column's row on u' (colV, col_iff);
 the two halves of the fold's row, one on ω' and one on u', each with the shared element, which is
 one entry of a further member (omHalfV, uHalfV, fold_of_halves).

Main definitions: Gp.val, Gp.push, KLin.evalV, dotV, colV, omHalfV, uHalfV.

Main theorems: Gp.rowsHold_iff, Gp.val_push, Gp.val_unit, Gp.val_add, Gp.val_sub, Gp.val_neg,
KLin.eval_iff, dot_iff, col_iff, omHalf_iff, uHalf_iff, fold_of_halves.

Not claimed. That a given verifier's rows are these vectors, on the members' entries or elsewhere.
Where the three vectors stand in the sent messages: the places are variables.

-/
import OnBytes.Slice.KeyExit
import OnBytes.Slice.KeyLinVec

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Run

namespace Gp
variable {s : Sg} (G : Gp s)

/-- **The value of a vector on the stage's entries at the members' messages.** -/
def val (m : G.Msgs) (v : s.cIn.J → GE) : GE := ∑ k : G.J, v (G.ent k) * m k.1 k.2

/-- All rows hold if and only if each vector has its target as its value. -/
theorem rowsHold_iff (m : G.Msgs) {n : ℕ} (tg : Fin n → GE) (vs : Fin n → s.cIn.J → GE) :
    G.RowsHold m tg vs ↔ ∀ b, G.val m (vs b) = tg b := Iff.rfl

/-- **Coefficients c on the entries φ a of the member i, as a vector on the stage's entries.** -/
def push (i : G.ι) {I : Type} [Fintype I] (φ : I → (G.mb i).cd.J) (c : I → GE) : s.cIn.J → GE :=
  fun j => ∑ a, if G.ent ⟨i, φ a⟩ = j then c a else 0

variable {G}

/-- The value of a sum of two vectors. -/
theorem val_add (m : G.Msgs) (v v' : s.cIn.J → GE) : G.val m (v + v') = G.val m v + G.val m v' := by
  unfold val
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => add_mul _ _ _

/-- The value of the negative of a vector. -/
theorem val_neg (m : G.Msgs) (v : s.cIn.J → GE) : G.val m (-v) = -G.val m v := by
  unfold val
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k _ => neg_mul _ _

/-- The value of a difference of two vectors. -/
theorem val_sub (m : G.Msgs) (v v' : s.cIn.J → GE) : G.val m (v - v') = G.val m v - G.val m v' := by
  rw [sub_eq_add_neg, val_add, val_neg, ← sub_eq_add_neg]

/-- **The value of coefficients on a member's entries.** -/
theorem val_push (hA : G.Apart) (m : G.Msgs) (i : G.ι) {I : Type} [Fintype I]
    (φ : I → (G.mb i).cd.J) (c : I → GE) : G.val m (G.push i φ c) = ∑ a, c a * m i (φ a) := by
  unfold val push
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single (⟨i, φ a⟩ : G.J)]
  · rw [if_pos rfl]
  · intro k _ hk
    rw [if_neg fun h => hk (ent_inj hA h).symm, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The value of the coefficient 1 on one entry of a member. -/
theorem val_unit (hA : G.Apart) (m : G.Msgs) (i : G.ι) (j : (G.mb i).cd.J) :
    G.val m (G.push i (fun _ : Unit => j) fun _ => 1) = m i j := by
  rw [val_push hA, Fintype.sum_unique, one_mul]

end Gp

namespace KLin
variable {K : KLin} {s : Sg} (G : Gp s)

/-- **The evaluation's row**: the weights of the point ψ on w', which stands at the entries lW of
the member iW, and the coefficients cZ on the entries φZ of the member iZ. -/
noncomputable def evalV (iW : G.ι) (lW : K.D.Col → (G.mb iW).cd.J) (ψ : K.D.Pt) (iZ : G.ι)
    {I : Type} [Fintype I] (φZ : I → (G.mb iZ).cd.J) (cZ : I → GE) : s.cIn.J → GE :=
  G.push iW lW (Alg.eqk (K.D.pt ψ)) + G.push iZ φZ cZ

/-- **The dot product's row**: the written-out weights g on ω', which stands at the entries lO of
the member iO, less the weights of the shared point on w'. -/
noncomputable def dotV (iO : G.ι) (lO : Fin K.nY → (G.mb iO).cd.J) (g : Fin K.nY → GE) (iW : G.ι)
    (lW : K.D.Col → (G.mb iW).cd.J) (ψs : K.D.Pt) : s.cIn.J → GE :=
  G.push iO lO g - G.push iW lW (Alg.eqk (K.D.pt ψs))

/-- **A drawn column's row**: the row of the table's generator matrix at the location x, on u',
which stands at the entries lU of the member iU. -/
noncomputable def colV (iU : G.ι) (lU : K.S.Co → (G.mb iU).cd.J) (x : K.S.Pos) : s.cIn.J → GE :=
  G.push iU lU fun k => K.D.X.G x k

/-- **The half of the fold's row on ω'**, with the shared element, the entry jK of the member
iK. -/
noncomputable def omHalfV (iO : G.ι) (lO : Fin K.nY → (G.mb iO).cd.J) (ζ : Fin K.l → GE) (iK : G.ι)
    (jK : (G.mb iK).cd.J) : s.cIn.J → GE :=
  G.push iO lO (fun y => Alg.eqk ζ (K.py y)) + G.push iK (fun _ : Unit => jK) fun _ => 1

/-- **The half of the fold's row on u'**, with the shared element. -/
noncomputable def uHalfV (iU : G.ι) (lU : K.S.Co → (G.mb iU).cd.J) (ζ : Fin K.l → GE)
    (ψlo : Fin K.klo → GE) (iK : G.ι) (jK : (G.mb iK).cd.J) : s.cIn.J → GE :=
  -G.push iU (fun p : Fin K.nY × (Fin K.klo → Bool) => lU (K.D.X.pl (K.lay p)))
      (fun p => Alg.eqk ζ (K.py p.1) * Alg.eqk ψlo p.2) -
    G.push iK (fun _ : Unit => jK) fun _ => 1

variable {G}

/-- The evaluation's row holds of the members' messages if and only if the library's row holds of
w', with the value of the coefficients cZ as the element that stands for other messages. -/
theorem eval_iff (hA : G.Apart) (m : G.Msgs) (iW : G.ι) (lW : K.D.Col → (G.mb iW).cd.J)
    (ψ : K.D.Pt) (iZ : G.ι) {I : Type} [Fintype I] (φZ : I → (G.mb iZ).cd.J) (cZ : I → GE)
    (τ : GE) :
    G.val m (evalV G iW lW ψ iZ φZ cZ) = τ ↔
      K.D.Eval ψ (fun c => m iW (lW c)) (∑ a, cZ a * m iZ (φZ a)) τ := by
  unfold evalV
  rw [Gp.val_add, Gp.val_push hA, Gp.val_push hA]
  exact Iff.rfl

/-- The dot product's row holds of the members' messages if and only if the library's holds of ω'
and w'. -/
theorem dot_iff (hA : G.Apart) (m : G.Msgs) (iO : G.ι) (lO : Fin K.nY → (G.mb iO).cd.J)
    (g : Fin K.nY → GE) (iW : G.ι) (lW : K.D.Col → (G.mb iW).cd.J) (ψs : K.D.Pt) :
    G.val m (dotV G iO lO g iW lW ψs) = 0 ↔
      K.D.Dot g (fun y => m iO (lO y)) ψs fun c => m iW (lW c) := by
  unfold dotV
  rw [Gp.val_sub, Gp.val_push hA, Gp.val_push hA, sub_eq_zero]
  exact Iff.rfl

/-- The drawn columns' rows hold of the members' messages if and only if the library's hold of
u'. -/
theorem col_iff (hA : G.Apart) (m : G.Msgs) (iU : G.ι) (lU : K.S.Co → (G.mb iU).cd.J)
    (f : K.S.Pos → Run.PQ.SgX) (γ : Fin K.D.X.v → GE) (Q : Fin K.t → K.S.Pos) :
    (∀ i, G.val m (colV G iU lU (Q i)) = foldAll γ (K.tab f) (Q i)) ↔
      K.D.ColR (K.tab f) γ (fun k => m iU (lU k)) Q := by
  refine forall_congr' fun i => ?_
  unfold colV
  rw [Gp.val_push hA]
  exact Iff.rfl

/-- The value of the half on ω'. -/
theorem omHalf_iff (hA : G.Apart) (m : G.Msgs) (iO : G.ι) (lO : Fin K.nY → (G.mb iO).cd.J)
    (ζ : Fin K.l → GE) (iK : G.ι) (jK : (G.mb iK).cd.J) (v : GE) :
    G.val m (omHalfV G iO lO ζ iK jK) = v ↔
      ∑ y, Alg.eqk ζ (K.py y) * m iO (lO y) + m iK jK = v := by
  unfold omHalfV
  rw [Gp.val_add, Gp.val_unit hA, Gp.val_push hA]

/-- The value of the half on u'. -/
theorem uHalf_iff (hA : G.Apart) (m : G.Msgs) (iU : G.ι) (lU : K.S.Co → (G.mb iU).cd.J)
    (ζ : Fin K.l → GE) (ψlo : Fin K.klo → GE) (iK : G.ι) (jK : (G.mb iK).cd.J) (v : GE) :
    G.val m (uHalfV G iU lU ζ ψlo iK jK) = 0 - v ↔
      -(∑ y, Alg.eqk ζ (K.py y) * K.D.omU (K.D.X.msg fun k => m iU (lU k)) ψlo y) - m iK jK =
        0 - v := by
  unfold uHalfV
  rw [Gp.val_sub, Gp.val_neg, Gp.val_unit hA, Gp.val_push hA, Fintype.sum_prod_type]
  have h : ∀ y, ∑ j, Alg.eqk ζ (K.py y) * Alg.eqk ψlo j * m iU (lU (K.D.X.pl (K.lay (y, j)))) =
      Alg.eqk ζ (K.py y) * K.D.omU (K.D.X.msg fun k => m iU (lU k)) ψlo y := fun y => by
    unfold LdLinW.omU
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => mul_assoc _ _ _
  rw [Finset.sum_congr rfl fun y _ => h y]

/-- **The fold's row from its two halves**, which stand in two groups. The shared element is the
same in both, and so is nothing else: ω' is read in the first group, u' in the second. -/
theorem fold_of_halves {s' : Sg} {G' : Gp s'} (hA : G.Apart) (hA' : G'.Apart) (m : G.Msgs)
    (m' : G'.Msgs) (iO : G.ι) (lO : Fin K.nY → (G.mb iO).cd.J) (iU : G'.ι)
    (lU : K.S.Co → (G'.mb iU).cd.J) (ζ : Fin K.l → GE) (ψlo : Fin K.klo → GE) (iK : G.ι)
    (jK : (G.mb iK).cd.J) (iK' : G'.ι) (jK' : (G'.mb iK').cd.J) (hκ : m iK jK = m' iK' jK')
    (v : GE) (h1 : G.val m (omHalfV G iO lO ζ iK jK) = v)
    (h2 : G'.val m' (uHalfV G' iU lU ζ ψlo iK' jK') = 0 - v) :
    K.D.FoldR ζ ψlo (K.D.X.msg fun k => m' iU (lU k)) fun y => m iO (lO y) := by
  by_contra hno
  rcases fold_split ζ ψlo (fun k => m' iU (lU k)) (fun y => m iO (lO y)) hno (m iK jK) v with h | h
  · exact h ((omHalf_iff hA m iO lO ζ iK jK v).1 h1)
  · rw [hκ] at h
    exact h ((uHalf_iff hA' m' iU lU ζ ψlo iK' jK' v).1 h2)

end KLin

end OnBytes.Slice
