-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyArrays.lean: what an honest committer lays into the MAIN rows of the oracle messages of the
three sendings of a key file's one-time chain: the index-mask message, the multiplicities, W. (The
chain's proximity test sends oracle messages of its own; they are not here.) Each as a function
message ↦ main row ↦ place ↦ entry, of the committed matrix and of public values alone.
Definitions, statements and proofs.

The three sendings (Johnson/Desc/Key/One.lean: "idx.1.send", "msg.1.send", "w.1.send"). Mask rows,
pads, encoding randomness and the masks that are sent along with a message are coins; they are no
matter of this file. An entry is an element of the base field (to the left) or of the extension
field (to the right); "none": the place holds no datum: an honest prover lays 0 there, unless the
place belongs to the message's pad, which is a coin.

What is defined.
  `idxData`: the index-mask message has no main row: nothing.
  `msgData entry k lookups ell`: message 0 of the second sending: the planes of the multiplicities
    (`planesData`, E2E/KeyPlanes.lean), over the base field. The mask that is sent along has no main
    row.
  `wAt g entry rows c`: entry c of W: the sum over the matrix's rows y of g y times the entry in row
    y and column c. g: the weights of the matrix's rows: public, from what the verifier has sampled.
  `layVec high ell R n vec`: a vector of n entries in R main rows of ell places: with the rows'
    number in the high bits entry j stands in row j / ell at the place j % ell; else in row j % R at
    the place j / R.
  `wData g entry rows k high ell R`: message 0 of the third sending: W, over the extension field.
What is shown.
  **`w_read`**: at the weights of a list of the library's vectors (`weightAt`,
    Johnson/Desc/Key/KeyWords.lean) and a matrix of machine words, `wAt` is the reading of the very
    sum by which the library's sentence "V = gᵀM" (`VIs`, there) says what entry c is.
  `w_claim`: the sum over the columns c of e c times W's entry c is the sum over rows and columns of
    g y · e c · the matrix's entry: what a row on the matrix with the weights g and the column
    weights e reads.
  `layVec_high`, `layVec_low`: entry j of the vector stands where the rule says.
  `wVal`, **`w_is`**: W's entries as machine elements meet the library's sentence `VIs`, with "the
    same" read as "the same reading".
  `msgDataFull`, `wDataFull`, `wDataFull_at`: the two at the full size's numbers (two main rows of
    2^18 places; 3,076,096 rows, 2^18 columns, one main row).
  `one_matrix`: the reader at which E2E/KeyPlanesAtFull.lean counts (`entryOf`) and the reader of
    E2E/KeyReaders.lean (`cellsReader`), out of which the encoder's own messages are made
    (`stored_full`), are one function.

Limits. Data alone: no coin, no part of a prover, no round. Where the weights g come from (the row
that the batching of the rows on the table hands on) is not typed here. The folded row of the stored
table and Omega, which the shared chain sends, are not here. That a verifier's text reads W's vector
by `layVec`'s rule is a reading of the format's page, not a theorem. The numbers of section 3 are
set by hand; Lean's evaluator printed them for the written sizes of the key. `w_claim` is tied to
the library's sentence on a row on the matrix (`TensorRowHolds`, Johnson/Desc/Key/KeyWords.lean) by
no theorem. THAT THE PLANES COUNT THE MATRIX THAT THE COMMITTER HAS ENCODED IS NO THEOREM HERE:
`one_matrix` and `stored_full` state their matrices at two types, and no statement has one matrix in
both; the relation of E2E/KeyPadding.lean counts at machine words that spell a matrix, and no such
words are made of the encoder's here. Nothing on hiding follows from this file.


-/
import E2E.KeyPlanesRead
import Johnson.Desc.Key.KeySumRead
import E2E.KeyReaders

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtPublicFiles.Key
open Finset
open OnBytes.Slice (GF GE toF readE)
open OnBytes.Params (WfLookup)
open Johnson.Pack (lk0Full lk1Full)
open Inst.Model.Layout (kRef)

/-- An entry of a main row: of the base field or of the extension field. -/
abbrev Datum : Type := GF ⊕ GE

/-! ## 1. The index-mask message and the multiplicities -/

/-- The index-mask message has no main row. -/
def idxData : ℕ → ℕ → ℕ → Option Datum := fun _ _ _ => none

/-- **The multiplicities' main rows.** -/
def msgData (entry : ℕ → ℕ → GF) (k : ℕ) (lookups : List WfLookup) (ell : ℕ) :
    ℕ → ℕ → ℕ → Option Datum := fun msg row place =>
  if msg = 0 then (planesData entry k lookups ell row place).map Sum.inl else none

/-! ## 2. W -/

/-- **Entry c of W.** -/
def wAt (g : ℕ → GE) (entry : ℕ → ℕ → GF) (rows c : ℕ) : GE :=
  ∑ y ∈ range rows, g y * algebraMap GF GE (entry y c)

/-- A vector of n entries in R main rows of ell places. -/
def layVec (high : Bool) (ell R n : ℕ) (vec : ℕ → GE) (row place : ℕ) : Option GE :=
  if row < R ∧ place < ell ∧ (if high then row * ell + place else place * R + row) < n then
    some (vec (if high then row * ell + place else place * R + row))
  else none

/-- **W's main rows.** k: the logarithm of the number of the matrix's columns. -/
def wData (g : ℕ → GE) (entry : ℕ → ℕ → GF) (rows k : ℕ) (high : Bool) (ell R : ℕ) :
    ℕ → ℕ → ℕ → Option Datum := fun msg row place =>
  if msg = 0 then (layVec high ell R (2 ^ k) (wAt g entry rows) row place).map Sum.inr else none

/-- **It is the sum of the library's sentence "V = gᵀM", read in the field.** -/
theorem w_read (g : List OnBytes.Tensor) (mat : ℕ → ℕ → OnBytes.F) (rows c : ℕ) :
    wAt (fun y => readE (VerifiableInference.Desc.Key.weightAt g y)) (fun y x => toF (mat y x))
        rows c =
      readE (VerifiableInference.Desc.Key.sumE rows fun y =>
        OnBytes.mulE (VerifiableInference.Desc.Key.weightAt g y) (OnBytes.ofF (mat y c))) := by
  rw [VerifiableInference.Desc.Key.sumE_read readE OnBytes.Slice.readE_zero
    OnBytes.Slice.readE_add]
  unfold wAt
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [OnBytes.Slice.readE_mul, OnBytes.Slice.readE_ofF]

/-- What a row on the matrix reads is what the same column weights read of W. -/
theorem w_claim (g e : ℕ → GE) (entry : ℕ → ℕ → GF) (rows n : ℕ) :
    ∑ c ∈ range n, e c * wAt g entry rows c =
      ∑ y ∈ range rows, ∑ c ∈ range n, g y * e c * algebraMap GF GE (entry y c) := by
  unfold wAt
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun c _ => ?_
  ring

theorem layVec_high (ell R n : ℕ) (vec : ℕ → GE) (j : ℕ) (hj : j < n) (hR : j / ell < R)
    (hl : 0 < ell) : layVec true ell R n vec (j / ell) (j % ell) = some (vec j) := by
  have e : j / ell * ell + j % ell = j := Nat.div_add_mod' j ell
  unfold layVec
  simp only [if_true, e]
  rw [if_pos ⟨hR, Nat.mod_lt _ hl, hj⟩]

theorem layVec_low (ell R n : ℕ) (vec : ℕ → GE) (j : ℕ) (hj : j < n) (hl : j / R < ell)
    (hR : 0 < R) : layVec false ell R n vec (j % R) (j / R) = some (vec j) := by
  have e : j / R * R + j % R = j := Nat.div_add_mod' j R
  unfold layVec
  simp only [Bool.false_eq_true, if_false, e]
  rw [if_pos ⟨Nat.mod_lt _ hR, hl, hj⟩]

/-- Entry c of W as a machine element. -/
def wVal (g : List OnBytes.Tensor) (mat : ℕ → ℕ → OnBytes.F) (rows c : ℕ) : OnBytes.E :=
  OnBytes.E.ofTriple (OnBytes.Slice.ofE
    (wAt (fun y => readE (VerifiableInference.Desc.Key.weightAt g y)) (fun y x => toF (mat y x))
      rows c))

/-- **The library's sentence "V = gᵀM" holds of it**, with "the same" read as "the same reading". -/
theorem w_is (m : OnBytes.Wf.Matrix) (g : List OnBytes.Tensor) (mat : ℕ → ℕ → OnBytes.F) :
    VerifiableInference.Desc.Key.VIs (fun a b => readE a = readE b) m g mat
      (wVal g mat m.rows) := fun c _ => by
  show readE (wVal g mat m.rows c) = _
  unfold wVal
  rw [OnBytes.Slice.readE_ofTriple, OnBytes.Slice.toE_ofE, w_read]

/-! ## 3. At the full size's numbers -/

/-- The multiplicities' main rows: two of 2^18 places. -/
def msgDataFull (entry : ℕ → ℕ → GF) : ℕ → ℕ → ℕ → Option Datum :=
  msgData entry kRef [lk0Full, lk1Full] (2 ^ 18)

/-- W's main row: one of 2^18 places. -/
def wDataFull (g : ℕ → GE) (entry : ℕ → ℕ → GF) : ℕ → ℕ → ℕ → Option Datum :=
  wData g entry 3076096 18 true (2 ^ 18) 1

theorem wDataFull_at (g : ℕ → GE) (entry : ℕ → ℕ → GF) (c : ℕ) (hc : c < 2 ^ 18) :
    wDataFull g entry 0 0 c = some (.inr (wAt g entry 3076096 c)) := by
  unfold wDataFull wData
  rw [if_pos rfl]
  have h := layVec_high (2 ^ 18) 1 (2 ^ 18) (wAt g entry 3076096) c hc
    (by rw [Nat.div_eq_of_lt hc]; exact Nat.one_pos) (Nat.two_pow_pos _)
  rw [Nat.div_eq_of_lt hc, Nat.mod_eq_of_lt hc] at h
  rw [h]
  rfl

/-- The matrix's entries end before the cut. -/
theorem fit_full : VerifiableInference.OnPublicFiles.numsRef.rows *
    2 ^ VerifiableInference.OnPublicFiles.numsRef.kLo ≤ 402653181 := by
  show 3076096 * 2 ^ 7 ≤ 402653181
  norm_num

/-- The full size's encoder's message, out of the readers. -/
theorem stored_full
    (M : OnBytes.Flat.Cells (OnBytes.Slice.frS.toDecR OnBytes.Slice.frZ 402653181)
      VerifiableInference.OnPublicFiles.numsRef)
    (η : OnBytes.Flat.PadsOf OnBytes.Slice.frS 402653181) (k : OnBytes.Slice.frS.ix.Row)
    (j : OnBytes.Slice.frS.En) :
    OnBytes.Slice.honestMsgs OnBytes.Slice.frS
        (OnBytes.Flat.cellWords OnBytes.Slice.frS OnBytes.Slice.frZ 402653181
          VerifiableInference.OnPublicFiles.numsRef M η) (k, j) =
      algebraMap GF GE (storedAt (cellsReader M) (padReader η) 3076096 7 402653181
        OnBytes.Slice.frS.P.T.l (OnBytes.Slice.Sz.rowNo k) j.val) :=
  stored_eq_hold OnBytes.Slice.frS 402653181 VerifiableInference.OnPublicFiles.numsRef OnBytes.Slice.frZ
    fit_full M η k j

/-- The two readers are one function. -/
theorem one_matrix (M : Fin Inst.Model.Layout.hRef → Fin (2 ^ kRef) → GE) :
    entryOf M = cellsReader M := rfl

end AtPublicFiles.Key

#print axioms AtPublicFiles.Key.w_read
#print axioms AtPublicFiles.Key.w_claim
#print axioms AtPublicFiles.Key.layVec_high
#print axioms AtPublicFiles.Key.layVec_low
#print axioms AtPublicFiles.Key.w_is
#print axioms AtPublicFiles.Key.wDataFull_at
#print axioms AtPublicFiles.Key.stored_full
#print axioms AtPublicFiles.Key.one_matrix
