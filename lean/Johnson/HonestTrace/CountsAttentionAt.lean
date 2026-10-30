-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/CountsAttentionAt.lean

The law of the lookup of an attention sub-proof's own calls (lawA,
Johnson/HonestTrace/CountsAttention.lean) with its premise on the keys in the words of
Johnson/Road/Lane5ForIn.lean: ForInA, at the field Cb.Gl.E. With it: the number of columns of the
matrix bA, and the reading of a list of integer matrices in which bA has been laid.

Main theorems. (hs) stands for the premise "shapeHid lid cf = .ok (S, fs)".
* "kbA_A": under (hs), the field kbA of S is NC 2^(kT + 5 - lmb). "bA_outside": under (hs), bA is 0
  from row 2^lmb on and from column S.kbA on.
* "inTable_of_forInA": ForInA S fs cell is, term for term, lawA's premise "for every call c below
  NC, every place of A.kvA S fs cell c holds the value of a row below 2^(k_c) of tabOf".
* "lawA_forInA": under (hs), if ForInA S fs cell and LaidBA S fs cell hold, then for all θ and al
  Cb.Lkp.MidP holds of A.keyA, A.tabA, FoNums.pads fs and A.bitsA, with the keys and the bits read
  at cell.
* "cellZ_withBA": if a list Z' of integer matrices is the list Z outside number NAs + 2 and holds
  there bA of the reading of Z, then cellZ Z' is withBA S fs (cellZ Z).

Limits. LaidBA asks that the cells of matrix number NAs + 2, at the rows below 2^lmb and the columns
below NC 2^(kT + 5 - lmb), are bA of these very cells. This file makes no list of matrices that
meets ForInA and LaidBA together; at the full size, at public files in the goals' scope and a
request that is served, list 2 g + 1 of theTrace, for g below 12, meets both ("planesLaid_in_scope",
and the field keysA of "meetsAll_theTrace", Johnson/Goal/HonestTrace/FullPlanesInScope.lean). The
subtraction in kT + 5 - lmb is that of natural numbers.

Not claimed: that a prover's committed cells are such matrices; that a verifier accepts anything;
that the premises hold of any parameter file or request.

-/
import Johnson.HonestTrace.CountsAttention
import Johnson.Road.Lane5ForIn

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open OnBytes.Model
open OnBytes.Ends (NameA)
open OnBytes.Road.L5 (ForInA cellZ Zs bind_ok refuse_ok)

variable {lid : ℕ} {cf : Attention.Cfg} {S : Attention.Shape} {fs : Forest.Shape}

/-- Where shapeHid returns (S, fs), the field kbA of S, the number of columns of the matrix bA, is
NC 2^(kT + 5 - lmb). -/
theorem kbA_A (hs : Attention.shapeHid lid cf = Except.ok (S, fs)) :
    S.kbA = fs.NC * 2 ^ (fs.kT + 5 - S.cf.lmb) := by
  have ec := (Fo.Pub2.shapeOf_shapeHid hs).2
  unfold Attention.shapeHid at hs
  obtain ⟨A, -, h⟩ := bind_ok hs
  obtain ⟨f, -, h⟩ := bind_ok h
  obtain ⟨-, h⟩ := refuse_ok h
  obtain ⟨kbA, hk, h⟩ := bind_ok h
  obtain ⟨counted, -, h⟩ := bind_ok h
  obtain ⟨-, -, h⟩ := bind_ok h
  have e := Except.ok.inj h
  obtain ⟨e1, e2⟩ := Prod.mk.inj e
  subst e1
  subst e2
  rw [ec]
  unfold Forest.planeCols at hk
  split_ifs at hk
  exact (Except.ok.inj hk).symm

/-- Where shapeHid returns (S, fs): from row 2^lmb on and from column S.kbA on, bA is 0, at every
reading of the names over every field with decidable equality. -/
theorem bA_outside {K : Type} [Field K] [DecidableEq K]
    (hs : Attention.shapeHid lid cf = Except.ok (S, fs)) (cell : NameA → K) {r c : ℕ}
    (ho : 2 ^ S.cf.lmb ≤ r ∨ S.kbA ≤ c) : bA S fs cell r c = 0 := by
  rw [kbA_A hs] at ho
  exact plane_outside _ _ _ ho

/-- ForInA S fs cell is the premise of lawA on the keys, at the field Cb.Gl.E. -/
theorem inTable_of_forInA {cell : NameA → Cb.Gl.E} (H : ForInA S fs cell) :
    ∀ c < fs.NC, Cb.Lkp.InTable (FoNums.nOf fs c) (FoNums.kOf fs c) (Ends.A.kvA S fs cell c)
      (tabOf Cb.Gl.E fs c) := H

/-- Where shapeHid returns (S, fs): if ForInA S fs cell and LaidBA S fs cell hold, then for all θ
and al: Cb.Lkp.MidP holds of the joint key vector, the joint table, the public padding and the
planes' bits, with the keys and the bits read at cell. -/
theorem lawA_forInA (hs : Attention.shapeHid lid cf = Except.ok (S, fs)) (cell : NameA → Cb.Gl.E)
    (H : ForInA S fs cell) (hb : LaidBA S fs cell) (θ al : Cb.Gl.E) :
    Cb.Lkp.MidP fs.v fs.d 5 32 (Ends.A.keyA S fs cell θ) (Ends.A.tabA fs θ) (FoNums.pads fs)
      (fun u j => Ends.A.bitsA S fs cell (u * 32 + j)) al :=
  lawA hs cell (inTable_of_forInA H) hb θ al

/-- If the list Z' of integer matrices is the list Z outside number NAs + 2, and holds there bA of
the reading of Z, then the reading of Z' is the reading of Z with bA laid over it. S and fs are any
two values; K is any field with decidable equality. -/
theorem cellZ_withBA {K : Type} [Field K] [DecidableEq K] (S : Attention.Shape)
    (fs : Forest.Shape) {Z Z' : Zs} (h1 : ∀ a, a ≠ S.cf.NAs + 2 → Z' a = Z a)
    (h2 : ∀ r c, Z' (S.cf.NAs + 2) r c = ((bA S fs (cellZ Z : NameA → K) r c : ℕ) : ℤ)) :
    (cellZ Z' : NameA → K) = withBA S fs (cellZ Z) := by
  funext n
  obtain ⟨M, r, c⟩ := n
  unfold withBA
  by_cases hM : M = S.cf.NAs + 2
  · subst hM
    rw [if_pos rfl]
    show ((Z' (S.cf.NAs + 2) r c : ℤ) : K) = _
    rw [h2, Int.cast_natCast]
  · rw [if_neg hM]
    show ((Z' M r c : ℤ) : K) = ((Z M r c : ℤ) : K)
    rw [h1 M hM]

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.kbA_A
#print axioms OnBytes.HonestTrace.bA_outside
#print axioms OnBytes.HonestTrace.inTable_of_forInA
#print axioms OnBytes.HonestTrace.lawA_forInA
#print axioms OnBytes.HonestTrace.cellZ_withBA
