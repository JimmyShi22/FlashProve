-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyDotSays.lean: THE ROW (Dot) SAYS ITS CLAIM OF HONEST WORDS. The library's law on what the row
(Dot) says of words (`dotMeansOk`, Johnson/Desc/K14/Law/MeansDotOk.lean) turns it into one equation,
`DotEq` (Johnson/Desc/K14/Law/DotCount.lean): the row weights on Omega against the equality vector
at the shared point on W. Here: that equation at an Omega and a W that are made of one matrix.
Statements and proofs. NOTHING IS CLAIMED OF ANY PROVER: it is conditional throughout.

What is shown.
  **`dotEq_honest`**: where Omega is M applied to the equality vector at psi (the library's
    `OmegaIs`) and W is the row weights applied to M's rows, `DotEq` holds: a change of the order of
    two sums.
  **`omegaIs_honest`**: `OmegaIs` holds of the readings of the honest side's own Omega at the shared
    point (`omegaAtE`, Johnson/Desc/K14/Honest/Coded.lean), at the matrix that lies in the table's
    rows (the library's `matOf`): by that file's readings (CodedReads.lean) and the library's
    `omegaIs_of_col` (Johnson/Desc/K14/Law/OmegaTable.lean).
  **`dot_says`**: for every row that `linDotRow` returns, at well-formed row weights and two
    messages that have their tables (`PlacedDot`): it says its claim of ALL words m whose entries of
    W, read through W's layout, are the row weights applied to M's rows, and whose entries of Omega,
    read through Omega's layout, are M applied to the equality vector at psi.
  `wHalf_of_wIs`: the first of these two, from the library's `WIs` (which E2E/KeyWIs.lean's
    `wIs_held` gives at the words that the honest side's part of a sending has laid for W).
  **`matOf_rowsOf`**: ONE MATRIX IN BOTH HALVES: the matrix that lies in the table's rows, as the
    honest side's parts of the shared chain read them (`rowsOf`,
    Johnson/Desc/ProofFile/Honest/K14/Parts.lean), is the index's reader: at every row of the matrix
    and every NUMBER c (beyond the matrix's columns both sides read the reader beyond the matrix).
  **`dot_says_key`**: so the row says its claim of all words that hold the honest W (`WIs`) and, at
    Omega's number, the honest Omega of the same reader.

Limits.
- THE TWO HALVES ARE PREMISES OF `dot_says`. The half on Omega is shown here of the vector
  `omegaAtE`, NOT of any words: that the words at Omega's number in the statement at which the row
  is laid hold that vector through Omega's layout is not shown.
- `dot_says_key` leaves just that as its premise on Omega. The point's length is a premise too.
- FOR HONEST VECTORS ALONE. Nothing on soundness. Nothing on hiding follows from this file.


-/
import E2E.KeyWIs
import E2E.KeyStoredRows
import Johnson.Desc.K14.Law.MeansDotOk
import Johnson.Desc.K14.Law.OmegaTable
import Johnson.Desc.K14.Honest.CodedReads

set_option autoImplicit false

namespace AtPublicFiles.Key
open OnBytes OnBytes.Params OnBytes.Means
open OnBytes.Slice (GE)
open _root_.Desc.K14.Law (DotEq OmegaIs eqK matOf UIsFold omegaIs_of_col dotMeansOk PlacedDot)
open _root_.Desc.K14.Honest (omegaAtE uAtE val_omegaAtE val_uAtE omegaHon uHon foldRows)
open VerifiableInference.Desc.K13.Law (WIs weights ρg lowBits)

/-- **(Dot)'s equation at an Omega and a W that are made of one matrix.** -/
theorem dotEq_honest {K : Type} [Field K] (R k : ℕ) (M : ℕ → ℕ → K) (g om : ℕ → K) (psi : List K)
    (Wv : ℕ → K) (hO : OmegaIs R k M psi om)
    (hW : ∀ c < 2 ^ k, Wv c = ∑ y ∈ Finset.range R, g y * M y c) : DotEq R k g om psi Wv := by
  unfold DotEq
  have h1 : ∑ y ∈ Finset.range R, g y * om y =
      ∑ y ∈ Finset.range R, ∑ c ∈ Finset.range (2 ^ k), eqK psi c * (g y * M y c) :=
    Finset.sum_congr rfl fun y hy => by
      rw [hO y (Finset.mem_range.1 hy), Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by ring
  have h2 : ∑ c ∈ Finset.range (2 ^ k), eqK psi c * Wv c =
      ∑ c ∈ Finset.range (2 ^ k), ∑ y ∈ Finset.range R, eqK psi c * (g y * M y c) :=
    Finset.sum_congr rfl fun c hc => by rw [hW c (Finset.mem_range.1 hc), Finset.mul_sum]
  rw [h1, h2, Finset.sum_comm]

/-- **The honest side's own Omega at the shared point is the matrix in the table's rows, applied to
the equality vector there.** RwE: the table's rows before encoding. Asked: the point has one
coordinate for each bit of a column's number; the table has 2^v rows; the matrix's places lie within
a row's entries. -/
theorem omegaIs_honest {K : Type} [Field K] (ρ : OnBytes.Model.Reading K) (S : LinShape)
    (psi : List E) (RwE : ℕ → ℕ → E) (hpsi : psi.length = S.kCol)
    (hrows : S.fold.index.rows = 2 ^ S.fold.index.v)
    (hroom : S.matrixRows * 2 ^ S.kLo ≤ S.fold.entries) :
    OmegaIs S.matrixRows S.kCol (matOf S.kLo fun r k => ρ.val (RwE r k)) (psi.map ρ.val)
      fun y => ρ.val (omegaAtE S psi RwE y) := by
  have hlo : ((psi.take S.kLo).map ρ.val).length = S.kLo := by
    rw [List.length_map, List.length_take, hpsi]
    exact Nat.min_eq_left (Nat.le_add_right _ _)
  have hsplit : psi.map ρ.val = (psi.take S.kLo).map ρ.val ++ (psi.drop S.kLo).map ρ.val := by
    rw [← List.map_append, List.take_append_drop]
  rw [hsplit]
  refine omegaIs_of_col S.matrixRows S.kLo S.fold.index.v _ _ _ _
    (fun k => ρ.val (uAtE S psi RwE k)) hlo (fun y hy => ?_) fun k hk => ?_
  · rw [val_omegaAtE]
    unfold omegaHon
    rw [if_pos hy]
  · beta_reduce
    rw [val_uAtE]
    unfold uHon foldRows
    rw [if_pos (lt_of_lt_of_le hk hroom), hrows]

/-- **The row (Dot) says its claim of honest words.** -/
theorem dot_says {K : Type} [Field K] (ρ : OnBytes.Model.Reading K) (T : Statement) (S : LinShape)
    (ws : List Tensor) (psi : List E) (omega : ℕ) (omegaLay : VectorLay) (w : ℕ)
    (wLay : VectorLay) (row : OnBytes.Row)
    (hrow : linDotRow S ws psi omega omegaLay w wLay = some row) (hok : ∀ g ∈ ws, g.ok = true)
    (hP : PlacedDot T S omega omegaLay w wLay) (M : ℕ → ℕ → K) (m : Words K)
    (hW : ∀ c < 2 ^ S.kCol, m w .main (wLay.index c) =
      ∑ y ∈ Finset.range S.matrixRows, (ws.map fun g => ρ.val (g.entry y)).sum * M y c)
    (hO : OmegaIs S.matrixRows S.kCol M (psi.map ρ.val)
      fun y => m omega .main (omegaLay.index y)) :
    Says ρ T row m :=
  (dotMeansOk ρ T S ws psi omega omegaLay w wLay row hrow hok hP m).2
    (dotEq_honest S.matrixRows S.kCol M _ _ _ _ hO hW)

/-- The half on W, from the library's `WIs`: at a matrix by numbers M that spells the matrix by bits
mat. -/
theorem wHalf_of_wIs {nR k : ℕ} (mat : Fin nR → (Fin k → Bool) → GE) (m : Words GE)
    (g : List Tensor) (w : ℕ) (lay : VectorLay) (h : WIs mat m g w lay) (M : ℕ → ℕ → GE)
    (hM : ∀ (i : Fin nR) (e : ℕ), e < 2 ^ k → mat i (lowBits k e) = M i.val e) :
    ∀ c < 2 ^ k, m w .main (lay.index c) =
      ∑ y ∈ Finset.range nR, (g.map fun t => ρg.val (t.entry y)).sum * M y c := by
  intro c hc
  rw [h c hc, Finset.sum_range]
  exact Finset.sum_congr rfl fun i _ => by rw [hM i c hc]; rfl

/-! ## One matrix in both halves -/

/-- **The matrix that lies in the table's rows, as the honest side's parts of the shared chain read
them, is the index's reader**: at every row of the matrix and every column. -/
theorem matOf_rowsOf (S : LinShape) (entry pad tail : ℕ → ℕ → OnBytes.Slice.GF) (y c : ℕ)
    (hy : y < S.matrixRows) :
    matOf S.kLo (fun r k => ρg.val (ProofFile.Honest.K14.rowsOf S ⟨entry⟩ ⟨pad, tail⟩ r k)) y c =
      algebraMap OnBytes.Slice.GF GE (entry y c) := by
  have hp : 0 < 2 ^ S.kLo := Nat.two_pow_pos _
  have hm : c % 2 ^ S.kLo < 2 ^ S.kLo := Nat.mod_lt _ hp
  have hk : c % 2 ^ S.kLo + 2 ^ S.kLo * y < S.matrixRows * 2 ^ S.kLo := by
    have h3 : (y + 1) * 2 ^ S.kLo ≤ S.matrixRows * 2 ^ S.kLo := Nat.mul_le_mul_right _ hy
    rw [Nat.succ_mul, Nat.mul_comm y] at h3
    omega
  unfold matOf ProofFile.Honest.K14.rowsOf ProofFile.Honest.K14.entriesOf
  beta_reduce
  rw [if_pos hk, if_pos hk]
  show OnBytes.Slice.readE (ProofFile.Honest.eOfF _) = _
  rw [eOfF_read, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hm, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hm, Nat.mod_add_div]

/-- **The row (Dot) says its claim of words that hold the honest W and the honest Omega of one
index.** The half on W in the library's form `WIs`, at a matrix by bits that spells the index's
reader; the half on Omega: the words at Omega's number hold, through Omega's layout, the honest
side's own Omega at the shared point, made of the table's rows of the same reader. -/
theorem dot_says_key (T : Statement) (S : LinShape) (ws : List Tensor) (psi : List E) (omega : ℕ)
    (omegaLay : VectorLay) (w : ℕ) (wLay : VectorLay) (row : OnBytes.Row)
    (hrow : linDotRow S ws psi omega omegaLay w wLay = some row) (hok : ∀ g ∈ ws, g.ok = true)
    (hP : PlacedDot T S omega omegaLay w wLay) (entry pad tail : ℕ → ℕ → OnBytes.Slice.GF)
    (mat : Fin S.matrixRows → (Fin S.kCol → Bool) → GE)
    (hmat : ∀ (i : Fin S.matrixRows) (e : ℕ), e < 2 ^ S.kCol →
      mat i (lowBits S.kCol e) = algebraMap OnBytes.Slice.GF GE (entry i.val e))
    (m : Words GE) (hW : WIs mat m ws w wLay)
    (hOm : ∀ y < S.matrixRows, m omega .main (omegaLay.index y) =
      ρg.val (omegaAtE S psi (ProofFile.Honest.K14.rowsOf S ⟨entry⟩ ⟨pad, tail⟩) y))
    (hpsi : psi.length = S.kCol) (hrows : S.fold.index.rows = 2 ^ S.fold.index.v)
    (hroom : S.matrixRows * 2 ^ S.kLo ≤ S.fold.entries) : Says ρg T row m := by
  refine dot_says ρg T S ws psi omega omegaLay w wLay row hrow hok hP
    (matOf S.kLo fun r k => ρg.val (ProofFile.Honest.K14.rowsOf S ⟨entry⟩ ⟨pad, tail⟩ r k)) m
    (wHalf_of_wIs mat m ws w wLay hW _ fun i e he => ?_) fun y hy => ?_
  · rw [hmat i e he, matOf_rowsOf S entry pad tail i.val e i.isLt]
  · beta_reduce
    rw [hOm y hy]
    exact omegaIs_honest ρg S psi _ hpsi hrows hroom y hy

end AtPublicFiles.Key

#print axioms AtPublicFiles.Key.dotEq_honest
#print axioms AtPublicFiles.Key.omegaIs_honest
#print axioms AtPublicFiles.Key.dot_says
#print axioms AtPublicFiles.Key.wHalf_of_wIs
#print axioms AtPublicFiles.Key.matOf_rowsOf
#print axioms AtPublicFiles.Key.dot_says_key
