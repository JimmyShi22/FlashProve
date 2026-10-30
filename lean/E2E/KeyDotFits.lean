--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyDotFits.lean: THE ROW (Dot) CAN BE MADE, AND ITS TERMS FIT THEIR PLACES, AT ALL VALUES, UNDER
ONE MARK ON THE ROW WEIGHTS AND TWO TESTS ON NUMBERS. So the ground's clause "the terms fit their
places" on that row (E2E/KeyDotRow.lean, `TermsFit`) and "the row (Dot) can be made" come down to a
Bool that reads the row weights' form and to the fitting of two places: the main table of Omega's
copy and the main table of W. Statements and proofs. Tests of the verifier's: NOTHING IS SHOWN OF
ANY PROVER.

Why a mark. How many terms the row has hangs on values: the library's
`tensorBelow`, which cuts each row weight at the matrix's rows, has two short cuts that ask which
factors are the element 0. The key file's row weights have a written-out factor on some of their
variables: there the cut returns by a short cut alone. So what the sub-protocol asks of all weights
and of all summands of their cuts is held as one Bool.

  **`weightsB S lay g`**: THE MARK: every row weight is well-formed (the library's `Tensor.ok`), has
    the matrix's row bits as its variables, and can be cut at the matrix's rows; every summand of
    the cut, laid on a table with the layout lay, is in order and has the table's index bits as its
    variables.
  `weightsB_spec`: what it says of one weight. `weights_ok`: every weight is well-formed.
  `inOrder_plain`, `cut_returns`, **`weightsB_of_plain`**: it holds of weights without a written-out
    factor, from numbers alone.
  `mapM_returns`, **`dot_returns`**: under the mark, at a point of the right length, `linDotRow`
    returns.
  `DotTerms`, **`dot_terms_form`**: the form of every term of the row: it lies on one of the two
    main tables, is in order, and has that table's index bits as its variables.
  **`dot_termsFit`**: so `TermsFit` holds where the two places fit.

Limits.
- THAT THE KEY FILE's ROW WEIGHTS HAVE THE MARK IS NOT SHOWN. They are made in the first chain (the
  rows on the table; the batching). Shown here of weights without a written-out factor alone.
- The mark reads which factors of a weight are the element 0, so it is a function of values. At the
  key file's weights these zeros stand at the place of a block of rows, which is public.


-/
import E2E.KeyPadClear
import E2E.KeyPasses
import OnBytes.Slice.BlkLinRead
import OnBytes.Slice.BlkLink
import OnBytes.Slice.BlkTensCut
import Johnson.Desc.Own.ShapesAgree

set_option autoImplicit false

namespace AtPublicFiles.AtFiles
open OnBytes OnBytes.Params
open VerifiableInference.Desc.Own (tensorInOrder placeFits)

/-! ## The mark -/

/-- **The mark on the row weights.** lay: the layout of the table on which the cut weights are laid.
-/
def weightsB (S : LinShape) (lay : VectorLay) (g : List Tensor) : Bool :=
  g.all fun v => v.ok && v.vars == S.kRow &&
    match tensorBelow v 0 S.kRow S.matrixRows with
    | some l => l.all fun t => tensorInOrder (lay.onTable t) && (lay.onTable t).vars == lay.bits
    | none => false

theorem weightsB_spec {S : LinShape} {lay : VectorLay} {g : List Tensor}
    (h : weightsB S lay g = true) (v : Tensor) (hv : v ∈ g) :
    v.ok = true ∧ v.vars = S.kRow ∧ ∃ l, tensorBelow v 0 S.kRow S.matrixRows = some l ∧
      ∀ t ∈ l, tensorInOrder (lay.onTable t) = true ∧ (lay.onTable t).vars = lay.bits := by
  have t := List.all_eq_true.1 h v hv
  simp only [Bool.and_eq_true, beq_iff_eq] at t
  obtain ⟨⟨a, b⟩, c⟩ := t
  cases hl : tensorBelow v 0 S.kRow S.matrixRows with
  | none =>
    rw [hl] at c
    cases c
  | some l =>
    rw [hl] at c
    refine ⟨a, b, l, rfl, fun t ht => ?_⟩
    have u := List.all_eq_true.1 c t ht
    simp only [Bool.and_eq_true, beq_iff_eq] at u
    exact u

theorem weights_ok {S : LinShape} {lay : VectorLay} {g : List Tensor}
    (h : weightsB S lay g = true) : ∀ v ∈ g, v.ok = true :=
  fun v hv => (weightsB_spec h v hv).1

/-! ## It holds of weights without a written-out factor -/

theorem inOrder_plain (v : Tensor) (hd : v.denseVars = []) (hv : v.vars ≤ 63) :
    tensorInOrder v = true := by
  unfold tensorInOrder
  rw [hd]
  have h : decide (v.pairs.length ≤ 63) = true := decide_eq_true hv
  rw [h]
  rfl

theorem cut_returns (v : Tensor) (hd : v.denseVars = []) (count len : Nat) (hv : count ≤ v.vars)
    (hl : len ≤ 2 ^ count) : ∃ l, tensorBelow v 0 count len = some l := by
  rw [Slice.tensorBelow_plain_at v hd, if_neg (by
    rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    omega)]
  split
  · exact ⟨_, rfl⟩
  · split
    · exact ⟨_, rfl⟩
    · split <;> exact ⟨_, rfl⟩

theorem weightsB_of_plain (S : LinShape) (lay : VectorLay) (g : List Tensor)
    (h : ∀ v ∈ g, v.vars = S.kRow ∧ v.denseVars = []) (h1 : S.matrixRows ≤ 2 ^ S.kRow)
    (h2 : S.kRow ≤ lay.bits) (h3 : lay.bits ≤ 63) : weightsB S lay g = true := by
  refine List.all_eq_true.2 fun v hv => ?_
  obtain ⟨e, d⟩ := h v hv
  obtain ⟨l, hl⟩ := cut_returns v d S.kRow S.matrixRows (by rw [e]) h1
  have ok : v.ok = true := by
    rw [VerifiableInference.Desc.Own.tensorInOrder_agrees]
    exact inOrder_plain v d (by omega)
  rw [ok, hl, beq_iff_eq.2 e, Bool.and_self, Bool.true_and, List.all_eq_true]
  intro t ht
  obtain ⟨d1, d2⟩ := _root_.Desc.K14.Law.tensorBelow_memG v 0 S.kRow S.matrixRows l hl t ht
  obtain ⟨o1, o2⟩ := Slice.onTable_vars lay t (d1.trans d) (by rw [d2, e]; exact h2)
  rw [inOrder_plain _ o2 (by rw [o1]; exact h3), o1, beq_self_eq_true]
  rfl

/-! ## The row can be made -/

theorem mapM_returns {α β : Type} (f : α → Option β) :
    ∀ l : List α, (∀ x ∈ l, ∃ y, f x = some y) → ∃ r, l.mapM f = some r :=
  fun l h => Option.isSome_iff_exists.1 (mapM_isSome f l fun x hx => by
    obtain ⟨y, e⟩ := h x hx
    rw [e]
    rfl)

/-- **The row (Dot) can be made, under the mark.** -/
theorem dot_returns (S : LinShape) (g : List Tensor) (psi : List E) (omega : Nat)
    (omegaLay : VectorLay) (w : Nat) (wLay : VectorLay) (h1 : psi.length = S.kCol)
    (h2 : weightsB S omegaLay g = true) :
    ∃ dot, linDotRow S g psi omega omegaLay w wLay = some dot := by
  obtain ⟨cut, hc⟩ := mapM_returns (fun v => tensorBelow v 0 S.kRow S.matrixRows) g fun v hv => by
    obtain ⟨-, -, l, hl, -⟩ := weightsB_spec h2 v hv
    exact ⟨l, hl⟩
  have hg : (psi.length == S.kCol && g.all (·.vars == S.kRow)) = true := by
    rw [beq_iff_eq.2 h1, Bool.true_and, List.all_eq_true]
    exact fun v hv => beq_iff_eq.2 (weightsB_spec h2 v hv).2.1
  have hgd : guard ((psi.length == S.kCol && g.all (·.vars == S.kRow)) = true) =
      (some () : Option Unit) := by
    rw [guard, if_pos hg]
    rfl
  unfold linDotRow
  simp only [Option.bind_eq_bind, hgd, Option.bind_some, hc, Option.pure_def]
  exact ⟨_, rfl⟩

/-! ## Its terms -/

/-- The form of every term of the row (Dot). -/
def DotTerms (omega : Nat) (omegaLay : VectorLay) (w : Nat) (wLay : VectorLay)
    (dot : OnBytes.Row) : Prop :=
  ∀ t ∈ dot.terms.toList, t.part = .main ∧ tensorInOrder t.v = true ∧
    ((t.oracle = omega ∧ t.v.vars = omegaLay.bits) ∨ (t.oracle = w ∧ t.v.vars = wLay.bits))

theorem dot_terms_form (S : LinShape) (g : List Tensor) (psi : List E) (omega : Nat)
    (omegaLay : VectorLay) (w : Nat) (wLay : VectorLay) (dot : OnBytes.Row)
    (h : linDotRow S g psi omega omegaLay w wLay = some dot) (hg : weightsB S omegaLay g = true)
    (hc : S.kCol ≤ wLay.bits) (hb : wLay.bits ≤ 63) : DotTerms omega omegaLay w wLay dot := by
  unfold linDotRow at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨_, hgd, cut, hcut, hrow⟩ := h
  have hgu : (psi.length == S.kCol && g.all (·.vars == S.kRow)) = true := by
    by_contra c
    simp [guard, c] at hgd
  obtain ⟨hpsi, -⟩ := Bool.and_eq_true_iff.1 hgu
  intro t ht
  rw [← hrow, (Slice.addLaid_terms _ _ _ _).1, (Slice.addLaid_terms _ _ _ _).1] at ht
  rcases List.mem_append.1 ht with ht | ht
  · rcases List.mem_append.1 ht with ht | ht
    · cases ht
    · obtain ⟨c, hcm, rfl⟩ := List.mem_map.1 ht
      obtain ⟨l, hl, hcl⟩ := List.mem_flatten.1 hcm
      obtain ⟨v, hv, hvl⟩ := mapM_mem _ g cut hcut l hl
      obtain ⟨-, -, l', hl', hall⟩ := weightsB_spec hg v hv
      obtain rfl : l' = l := Option.some.inj (hl'.symm.trans hvl)
      exact ⟨rfl, (hall c hcl).1, Or.inl ⟨rfl, (hall c hcl).2⟩⟩
  · obtain ⟨c, hcm, rfl⟩ := List.mem_map.1 ht
    obtain rfl := List.mem_singleton.1 hcm
    have e : (Tensor.eq psi (negE oneE)).vars = S.kCol := by
      show (Tensor.eq psi (negE oneE)).pairs.length = _
      simp [Tensor.eq, beq_iff_eq.1 hpsi]
    obtain ⟨o1, o2⟩ := Slice.onTable_vars wLay (Tensor.eq psi (negE oneE)) rfl
      (by rw [e]; exact hc)
    exact ⟨rfl, inOrder_plain _ o2 (by rw [o1]; exact hb), Or.inr ⟨rfl, o1⟩⟩

/-- **The clause on the row's terms, where the two places fit.** -/
theorem dot_termsFit {omega : Nat} {omegaLay : VectorLay} {w : Nat} {wLay : VectorLay}
    {dot : OnBytes.Row} (hf : DotTerms omega omegaLay w wLay dot) (st : Statement)
    (G : OnBytes.Group) (h1 : placeFits st G omega .main omegaLay.bits 0 = true)
    (h2 : placeFits st G w .main wLay.bits 0 = true) : TermsFit st G dot :=
  termsFit_of_list fun t ht => by
    obtain ⟨p, d, c⟩ := hf t ht
    rcases c with ⟨o, v⟩ | ⟨o, v⟩
    · rw [d, p, o, v, h1]
      rfl
    · rw [d, p, o, v, h2]
      rfl

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.weightsB_spec
#print axioms AtPublicFiles.AtFiles.weights_ok
#print axioms AtPublicFiles.AtFiles.inOrder_plain
#print axioms AtPublicFiles.AtFiles.cut_returns
#print axioms AtPublicFiles.AtFiles.weightsB_of_plain
#print axioms AtPublicFiles.AtFiles.mapM_returns
#print axioms AtPublicFiles.AtFiles.dot_returns
#print axioms AtPublicFiles.AtFiles.dot_terms_form
#print axioms AtPublicFiles.AtFiles.dot_termsFit
