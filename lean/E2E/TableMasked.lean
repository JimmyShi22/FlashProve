-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/TableMasked.lean: at every OOD seed the OOD answers of a committed table, one for each row, are
a one-to-one image of the rows' pads, whatever matrix the table holds. Definitions, statements and
proofs.

The setting. A row's message has l entries. The last three are the row's pad: three elements of the
base field, sampled by the committer, which hold nothing of the matrix (`cellWords`,
Johnson/Flat/CodingCells.lean, at cut = l - 3). The sample map of one row is `recZ l lg 1`
(OnBytes/Slice/RecordRead.lean): an OOD seed is a point of lg coordinates and a factor β other than
0; the row's one OOD answer is a weighted sum of the entries before the pad, with weights that the
point gives, plus β times the element of the cubic extension field that the pad's entries spell.
All rows share the OOD seed. (The Lean library calls the pair of an OOD seed and the OOD answers a
"record", `Rec`.)

What is shown.
  `padVal_theta`, `theta_basis`: three elements c of the base field spell the element
    (c 0, c 1, c 2) of the extension field; that map is one to one and onto (the library's
    `PadBasis`).
  `recZ_one`: the one answer of `recZ l lg 1`, parted into the entries before the pad and the pad.
  `withPads`, `answer_withPads`: for a row whose pad entries are the images of pad : three elements
    of the base field: the answer is a value that does not read the pad, plus β times what the pad
    spells.
  **`answer_bijective`**: so, at every OOD seed and for all entries before the pad, the map from
    the pad to the answer is one to one and onto.
  `hold_withPads`: the message that holds a matrix M under the pads η is, in each row, the message
    at pads 0 with that row's pad laid in.
  `rowsOf`, **`rowsOf_laws`**: the configuration of a committed table with the honest side
    `codingCells` is an "index in rows" in the library's sense (`ConfigurationWithOutOfDomainSample.Rows`, `Rows.Laws`,
    Hiop/RecRows.lean).
  **`masked_cells`**: so the pads mask the answers (`ConfigurationWithOutOfDomainSample.Masked`): at every OOD seed the law of
    all OOD answers, over uniform pads, is the same for all matrices. By the library's
    `rec_answers_uniform` it is the uniform law.

Who reads each letter. S: the code's message length l and the number 2^v of rows. lg: the number of
the point's coordinates; nothing is asked of it. cut: where the pads begin; asked: cut + 3 = l. N,
pp, req: they stand in the configuration's type; N also in how a matrix is laid into the rows. The
matrix is under "for all": EVERY matrix of cells, in range or not.

Limits.
- ONE OOD seed for each committed table. Two OOD samples of one table at two OOD seeds use each pad
  twice, and nothing here covers that (Hiop/RecRows.lean says the same of its laws): the difference
  of the two answers, each divided by its factor, would be a sum of the row's entries with no pad in
  it. One table's randomness is used under one set of public files alone. The same rows and pads
  under other public files would get another seed, and of two OOD samples on one table's pads this
  file says nothing. (In the byte format the OOD seed is derived from the table's root and the
  digest of the public files: the head of OnBytes/Slice/RecordRead.lean.)
- The factor β is other than 0 by the TYPE of an OOD seed. How a program derives an OOD seed, and
  that its factor is never 0, is not treated. (The library's reading of a program's OOD seed lays
  the factor 1 where the element read is 0: `seedOf1`, OnBytes/Slice/RecordRead.lean. That this
  branch is never taken at what the format samples is shown nowhere here.)
- The law is over uniform pads alone; the encoding randomness is not read by an answer. The joint
  law with opened columns is in E2E/TableHides.lean.
- A pad must be read by nothing else. Here that holds by the form of `cellWords` and of the claims'
  matrix, which reads no entry from the cut on; what a protocol's prover sends about a row's whole
  message is not treated here.
- That a program lays its pads so, or samples them uniformly and anew for each table, is not said.
- No verifier, no protocol, no commitment, no hash function occurs here.

BESIDE EVERY TELLING of the result on the index's committed tables, to which this file belongs
(E2E/WholeViewAtFiles.lean, E2E/TablesAtOwnObject.lean):
- placeholder provers: no message of the protocol is covered; it is not zero knowledge;
- before compilation: no hashing; each OOD seed is chosen before its table's coins are drawn, from
  nothing but what has been shown and coins of the environment's own: of a seed that hangs on
  anything hidden, another table's pads too, nothing is said;
- fresh uniform pads and encoding randomness for each table (as run: derived from the committer's
  secret seed); one OOD sample a table; one set of public files. One table's randomness is used
  under one set of public files alone. The same rows and pads under other public files would get
  another seed, and of two OOD samples on one table's pads this file says nothing.
- the budget is table by table, is kept by nobody, and has no slack: at one column more the
  interface's clause on the encoder fails (a theorem: some OOD seed, two matrices in range, at every
  set of that size; it states no size of the difference, only that the two laws differ; typed for
  the form with all OOD seeds alone); that the result itself fails there is typed by no environment;
- that the IOP's own tests on the public files pass is shown in the side library: at the library's
  two named sets of public files (AtFullSide/E2E/AtWrittenFiles.lean), and at the first set's files
  under every policy within four bounds (`theLive_zAt`, AtFullSide/Top/LiveAtPolicies.lean); no
  theorem ties any of these to a file on a disk.


-/
import Johnson.Flat.CodingCells
import OnBytes.Slice.RecordOK
import Cb.Gen.OodDecPadProofs
import Hiop.RecRows

set_option autoImplicit false

noncomputable section

namespace AtPublicFiles.Table
open Iop Prob Hiop
open OnBytes.Flat (relationsAndEncodingOfClaims Coding codingCells cellWords PadsOf MatrixNums claimsLedgerOnAt Cells)
open OnBytes.Slice (Sz GF GE toF ofF honestMsgs recZ padZ entryEquiv readE)
open OnBytes (thetaE)

/-! ## What three pad entries spell -/

/-- Three elements of the base field spell the element of the extension field with these
coordinates. -/
theorem padVal_theta (c : Fin 3 → GF) :
    Cb.Ood.padVal (F := GF) (fun t : Fin 3 => readE (thetaE t.val)) c = ⟨c 0, c 1, c 2⟩ := by
  unfold Cb.Ood.padVal
  rw [Fin.sum_univ_three]
  simp only [OnBytes.Slice.readE_theta]
  ext <;> simp

/-- **1, X, X^2, as the format writes them, are a basis of the extension field over the base
field.** -/
theorem theta_basis : Cb.Ood.PadBasis GF fun t : Fin 3 => readE (thetaE t.val) := by
  refine ⟨OnBytes.Slice.theta_indep, fun y => ⟨fun t => if t.val = 0 then y.c0 else
    if t.val = 1 then y.c1 else y.c2, ?_⟩⟩
  exact (padVal_theta _).trans rfl

/-- y ↦ c + β y is one to one and onto, if β is not 0. -/
theorem affine_bijective (c β : GE) (hβ : β ≠ 0) :
    Function.Bijective fun y : GE => c + β * y := by
  constructor
  · intro y y' h
    have h₁ : c + β * y = c + β * y' := h
    have h₂ : β * y = β * y' := add_left_cancel h₁
    exact mul_left_cancel₀ hβ h₂
  · intro z
    refine ⟨β⁻¹ * (z - c), ?_⟩
    show c + β * (β⁻¹ * (z - c)) = z
    rw [mul_inv_cancel_left₀ hβ]
    ring

/-! ## The one answer of a row -/

/-- **The one answer of a row, parted**: the entries before the pad, each with the weight that the
OOD seed's point gives it, and the OOD seed's factor times what the three pad entries spell. -/
theorem recZ_one (l lg : ℕ) (h : 3 * 1 ≤ l) (ρ : (recZ l lg 1).D) (v : Fin l → GE) :
    (recZ l lg 1).val ρ v (0 : Fin 1) =
      (∑ j : Fin (l - 3 * 1), (padZ l lg 1).mat ρ (0 : Fin 1) (Sum.inl j) *
          v ((entryEquiv l 1 h).symm (Sum.inl j))) +
        (ρ (0 : Fin 1)).2.val * ∑ t : Fin 3, readE (thetaE t.val) *
          v ((entryEquiv l 1 h).symm (Sum.inr ((0 : Fin 1), t))) := by
  rw [OnBytes.Slice.recZ_val l lg 1 h ρ v]
  show ∑ x, (padZ l lg 1).mat ρ (0 : Fin 1) x * v ((entryEquiv l 1 h).symm x) = _
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_one, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  show (if (0 : Fin 1) = 0 then (ρ (0 : Fin 1)).2.val * readE (thetaE t.val) else 0) * _ = _
  rw [if_pos rfl, mul_assoc]

variable (S : Sz) (cut : ℕ)

/-- A row's message: before the cut the entries of row; from the cut on the pad's elements, read in
the extension field. -/
def withPads (row : S.En → GE) (pad : Fin (S.P.T.l - cut) → GF) (j : S.En) : GE :=
  if h : j.val < cut then row j
  else algebraMap GF GE (pad ⟨j.val - cut, by have := j.isLt; omega⟩)

/-- Pad entry number t, of three. -/
def padAt (hc : cut + 3 = S.P.T.l) (t : Fin 3) : Fin (S.P.T.l - cut) :=
  ⟨t.val, by have := t.isLt; omega⟩

/-- The message has room for one answer's pad. -/
theorem room (hc : cut + 3 = S.P.T.l) : 3 * 1 ≤ S.P.T.l := by omega

/-- Before the pad the message is row. -/
theorem withPads_before (hc : cut + 3 = S.P.T.l) (row : S.En → GE)
    (pad : Fin (S.P.T.l - cut) → GF) (j : Fin (S.P.T.l - 3 * 1)) :
    withPads S cut row pad ((entryEquiv S.P.T.l 1 (room S cut hc)).symm (Sum.inl j)) =
      row ((entryEquiv S.P.T.l 1 (room S cut hc)).symm (Sum.inl j)) := by
  have hj : ((entryEquiv S.P.T.l 1 (room S cut hc)).symm (Sum.inl j)).val < cut := by
    show j.val < cut
    have := j.isLt
    omega
  unfold withPads
  exact dif_pos hj

/-- At the pad's three entries the message is the pad. -/
theorem withPads_pad (hc : cut + 3 = S.P.T.l) (row : S.En → GE)
    (pad : Fin (S.P.T.l - cut) → GF) (a : Fin 1) (t : Fin 3) :
    withPads S cut row pad ((entryEquiv S.P.T.l 1 (room S cut hc)).symm (Sum.inr (a, t))) =
      algebraMap GF GE (pad (padAt S cut hc t)) := by
  have ha := a.isLt
  have ht := t.isLt
  have hv : ((entryEquiv S.P.T.l 1 (room S cut hc)).symm (Sum.inr (a, t))).val =
      S.P.T.l - 3 * 1 + 3 * a.val + t.val := rfl
  have hn : ¬ ((entryEquiv S.P.T.l 1 (room S cut hc)).symm (Sum.inr (a, t))).val < cut := by
    rw [hv]
    omega
  unfold withPads
  rw [dif_neg hn]
  refine congrArg (fun q => algebraMap GF GE (pad q)) (Fin.ext ?_)
  show ((entryEquiv S.P.T.l 1 (room S cut hc)).symm (Sum.inr (a, t))).val - cut = t.val
  rw [hv]
  omega

variable (lg : ℕ)

/-- What the entries before the pad give to a row's answer. -/
def before (hc : cut + 3 = S.P.T.l) (ρ : (recZ S.P.T.l lg 1).D) (row : S.En → GE) : GE :=
  ∑ j : Fin (S.P.T.l - 3 * 1), (padZ S.P.T.l lg 1).mat ρ (0 : Fin 1) (Sum.inl j) *
    row ((entryEquiv S.P.T.l 1 (room S cut hc)).symm (Sum.inl j))

/-- **A row's answer**: what the entries before the pad give, plus the OOD seed's factor times what
the pad spells. -/
theorem answer_withPads (hc : cut + 3 = S.P.T.l) (ρ : (recZ S.P.T.l lg 1).D) (row : S.En → GE)
    (pad : Fin (S.P.T.l - cut) → GF) :
    (recZ S.P.T.l lg 1).val ρ (withPads S cut row pad) (0 : Fin 1) =
      before S cut lg hc ρ row + (ρ (0 : Fin 1)).2.val *
        Cb.Ood.padVal (F := GF) (fun t : Fin 3 => readE (thetaE t.val))
          (fun t => pad (padAt S cut hc t)) := by
  rw [recZ_one S.P.T.l lg (room S cut hc) ρ (withPads S cut row pad)]
  unfold before Cb.Ood.padVal
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro j _
    rw [withPads_before S cut hc row pad j]
  · exact congrArg (fun y => (ρ (0 : Fin 1)).2.val * y)
      (Finset.sum_congr rfl fun t _ => by rw [withPads_pad S cut hc row pad 0 t])

/-- Reading a pad at its three entries is one to one and onto. -/
theorem rePad_bijective (hc : cut + 3 = S.P.T.l) :
    Function.Bijective fun (pad : Fin (S.P.T.l - cut) → GF) (t : Fin 3) =>
      pad (padAt S cut hc t) := by
  constructor
  · intro p p' h
    funext q
    have hq : q.val < 3 := by
      have := q.isLt
      omega
    exact congrFun h ⟨q.val, hq⟩
  · intro c
    refine ⟨fun q => c ⟨q.val, by have := q.isLt; omega⟩, ?_⟩
    funext t
    rfl

/-- **The pad masks the answer**: at every OOD seed and for all entries before the pad, the map from
a row's pad to the row's answer is one to one and onto. -/
theorem answer_bijective (hc : cut + 3 = S.P.T.l) (ρ : (recZ S.P.T.l lg 1).D)
    (row : S.En → GE) :
    Function.Bijective fun pad : Fin (S.P.T.l - cut) → GF =>
      (recZ S.P.T.l lg 1).val ρ (withPads S cut row pad) (0 : Fin 1) := by
  have e : (fun pad : Fin (S.P.T.l - cut) → GF =>
      (recZ S.P.T.l lg 1).val ρ (withPads S cut row pad) (0 : Fin 1)) =
      (fun y : GE => before S cut lg hc ρ row + (ρ (0 : Fin 1)).2.val * y) ∘
        (Cb.Ood.padVal (F := GF) fun t : Fin 3 => readE (thetaE t.val)) ∘
          fun (pad : Fin (S.P.T.l - cut) → GF) (t : Fin 3) => pad (padAt S cut hc t) :=
    funext fun pad => answer_withPads S cut lg hc ρ row pad
  rw [e]
  exact Function.Bijective.comp (affine_bijective _ _ (ρ (0 : Fin 1)).2.property)
    (Function.Bijective.comp theta_basis (rePad_bijective S cut hc))

/-! ## The message that holds a matrix -/

variable (N : MatrixNums)

/-- **The message that holds a matrix under the pads η** is, in the row at the vertex k, the
message at pads 0 with that row's pad laid in. -/
theorem hold_withPads (Z : Cb.Ood.Sample GE S.En) (M : Cells (S.toDecR Z cut) N)
    (η : PadsOf S cut) (k : S.ix.Row) (j : S.En) :
    honestMsgs S (cellWords S Z cut N M η) (k, j) =
      withPads S cut (fun j => honestMsgs S (cellWords S Z cut N M fun _ _ => 0) (k, j))
        (η ⟨OnBytes.Slice.Sz.rowNo k, OnBytes.Slice.rowNo_lt k⟩) j := by
  show algebraMap GF GE
    (toF ((cellWords S Z cut N M η (OnBytes.Slice.Sz.rowNo k)).getD j.val 0)) = _
  unfold withPads
  by_cases hj : j.val < cut
  · rw [dif_pos hj]
    show _ = algebraMap GF GE
      (toF ((cellWords S Z cut N M (fun _ _ => 0) (OnBytes.Slice.Sz.rowNo k)).getD j.val 0))
    rw [OnBytes.Flat.cellWords_getD S Z cut N M η _ _ j.isLt,
      OnBytes.Flat.cellWords_getD S Z cut N M (fun _ _ => 0) _ _ j.isLt]
    unfold OnBytes.Flat.cellEntry OnBytes.Flat.cellEntryAt
    rw [if_pos hj, if_pos hj]
  · have hb : OnBytes.Slice.Sz.rowNo k < 2 ^ S.P.v ∧ j.val - cut < S.P.T.l - cut :=
      ⟨OnBytes.Slice.rowNo_lt k, by have := j.isLt; omega⟩
    rw [dif_neg hj, OnBytes.Flat.cellWords_getD S Z cut N M η _ _ j.isLt]
    unfold OnBytes.Flat.cellEntry OnBytes.Flat.cellEntryAt
    rw [if_neg hj, dif_pos hb, OnBytes.Slice.toF_ofF]

/-! ## The configuration is an index in rows -/

/-- The rows' vertices and the rows' numbers. -/
def rowEquiv (v : ℕ) : (Fin v → Bool) ≃ Fin (2 ^ v) where
  toFun k := ⟨OnBytes.Slice.Sz.rowNo k, OnBytes.Slice.rowNo_lt k⟩
  invFun b := fun t => b.val.testBit t.val
  left_inv k := funext (OnBytes.Slice.testBit_rowNo k)
  right_inv b := Fin.ext (by
    show OnBytes.Slice.Sz.rowNo (fun t : Fin v => b.val.testBit t.val) = b.val
    rw [OnBytes.Slice.rowNo_testBit, Nat.mod_eq_of_lt b.isLt])

variable {X : Type} (pp : Inst.Model.ScalesAndPolicy) (req : X → Inst.Model.Instance Inst.Model.ppref)

/-- The configuration of a committed table with one OOD answer for each row: the claims on a matrix
of cells, and the written honest side `codingCells`. -/
abbrev confCells : ConfigurationWithOutOfDomainSample :=
  OnBytes.Slice.DecR.configurationOfStoredTable (claimsLedgerOnAt (S.toDecR (recZ S.P.T.l lg 1) cut) N pp req)
    (relationsAndEncodingOfClaims _ (codingCells S (recZ S.P.T.l lg 1) cut N pp req))

/-- **The configuration as an index in rows**: the rows are named by their vertices; a row holds its
message at pads 0; a row's pad is its three elements of the base field; a row's answer is its one
OOD answer. -/
def rowsOf : (confCells S cut lg N pp req).Rows where
  K := Fin S.P.v → Bool
  Row := S.En → GE
  PadR := Fin (S.P.T.l - cut) → GF
  A := GE
  lay := fun M k j =>
    honestMsgs S (cellWords S (recZ S.P.T.l lg 1) cut N M fun _ _ => 0) (k, j)
  pads := Equiv.arrowCongr (rowEquiv S.P.v).symm (Equiv.refl (Fin (S.P.T.l - cut) → GF))
  answers :=
    { toFun := fun f k => f (k, (0 : Fin 1))
      invFun := fun g x => g x.1
      left_inv := fun f => funext fun x =>
        congrArg f (Prod.ext rfl (Subsingleton.elim (0 : Fin 1) x.2))
      right_inv := fun _ => rfl }
  ansRow := fun ρ row pad => (recZ S.P.T.l lg 1).val ρ (withPads S cut row pad) (0 : Fin 1)

/-- **Its two laws**: a row's answer reads that row alone, and the row's pad masks it. Asked: the
last three entries of a row's message are its pad. -/
theorem rowsOf_laws (hc : cut + 3 = S.P.T.l) : (rowsOf S cut lg N pp req).Laws where
  smp_hold := fun ρ M η k =>
    (Cb.ood_val_rows_same GE S.En (Fin S.P.v → Bool) (recZ S.P.T.l lg 1) ρ
      (honestMsgs S (cellWords S (recZ S.P.T.l lg 1) cut N M η)) k (0 : Fin 1)).trans
      (congrArg (fun u => (recZ S.P.T.l lg 1).val ρ u (0 : Fin 1))
        (funext fun j => hold_withPads S cut N (recZ S.P.T.l lg 1) M η k j))
  mask := fun ρ row => answer_bijective S cut lg hc ρ row

/-- **The pads mask the OOD answers**: at every OOD seed the law of the OOD answers of all rows,
over uniform pads, is the same for all matrices. -/
theorem masked_cells (hc : cut + 3 = S.P.T.l) : (confCells S cut lg N pp req).Masked :=
  rec_masked_of_rows _ (rowsOf S cut lg N pp req) (rowsOf_laws S cut lg N pp req hc)

end AtPublicFiles.Table

#print axioms AtPublicFiles.Table.theta_basis
#print axioms AtPublicFiles.Table.recZ_one
#print axioms AtPublicFiles.Table.answer_bijective
#print axioms AtPublicFiles.Table.hold_withPads
#print axioms AtPublicFiles.Table.rowsOf_laws
#print axioms AtPublicFiles.Table.masked_cells
