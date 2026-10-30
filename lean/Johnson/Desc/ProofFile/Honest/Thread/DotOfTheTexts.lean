-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/DotOfTheTexts.lean: THE ROW (Dot) AT THE TWO MESSAGES' OWN TEXTS.
The prover's text for W is wVec (Honest/K13/WData.lean): the row weights applied to the index's
matrix. Its text for Omega is omegaAtE (Johnson/Desc/K14/Honest/Coded.lean): the rows of the stored
table, rowsOf (Honest/K14/Parts.lean), folded at the shared point. The two read one thing, the
index's weights, in two dresses. Here they are made one, and (Dot) holds at the two texts.

  rows_matOf      the rows of the stored table, read as the library's matOf, are the matrix
  wVec_is_sum     W's text as a sum over the matrix's rows
  dot_of_vectors  (Dot) at any reading, from the library's dotEq_honest
  dot_of_texts    (Dot) at the two texts

What these are. Lemmas on our own definitions and the library's. None is one of the library's goals.
They say nothing of soundness, completeness or hiding.

Limits.
  * That a prover's messages are these texts is not said here.
  * The shape S is one letter: both texts are read at it.
-/
import Johnson.Desc.ProofFile.Honest.K13.WData
import Johnson.Desc.ProofFile.Honest.K14.Parts
import Johnson.Desc.K14.Honest.Values
import Johnson.Desc.K14.Honest.CodedReads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Door
open OnBytes OnBytes.Params
open OnBytes.Slice (GE)
open OnBytes.Model (Reading)
open Desc.K14.Law (DotEq matOf VIs)
open Desc.K14.Honest (omegaAtE uAtE uHon omegaHon val_uAtE val_omegaAtE uHon_isFold dotEq_honest)
open ProofFile.Honest.K14 (rowsOf entriesOf)
open ProofFile.Honest.K13 (wVec)
open VerifiableInference.Desc.K13.Law (weights ρg)

/-- **The rows of the stored table, read as matOf, are the matrix**, at the matrix's rows. -/
theorem rows_matOf (S : LinShape) (W : Weights) (c : TableRand) {y x : Nat}
    (hy : y < S.matrixRows) :
    matOf S.kLo (fun r k => Reading.gl.val (rowsOf S W c r k)) y x =
      Reading.gl.val (eOfF (W.entry y x)) := by
  have hp : 0 < 2 ^ S.kLo := Nat.two_pow_pos _
  have hk : x % 2 ^ S.kLo + 2 ^ S.kLo * y < S.matrixRows * 2 ^ S.kLo := by
    have h1 : x % 2 ^ S.kLo < 2 ^ S.kLo := Nat.mod_lt _ hp
    have h2 : (y + 1) * 2 ^ S.kLo ≤ S.matrixRows * 2 ^ S.kLo := Nat.mul_le_mul_right _ hy
    rw [Nat.succ_mul, Nat.mul_comm y] at h2
    omega
  show Reading.gl.val (rowsOf S W c (x / 2 ^ S.kLo) (x % 2 ^ S.kLo + 2 ^ S.kLo * y)) = _
  unfold rowsOf entriesOf
  rw [if_pos hk, if_pos hk, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt (Nat.mod_lt _ hp),
    Nat.zero_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Nat.mod_lt _ hp), Nat.mod_add_div]

/-- **W's text as a sum over the matrix's rows.** -/
theorem wVec_is_sum (S : LinShape) (W : Weights) (g : List Tensor) {x : Nat} (hx : x < 2 ^ S.kCol) :
    wVec S W g x = ∑ y ∈ Finset.range S.matrixRows,
      (g.map fun t => Reading.gl.val (t.entry y)).sum * Reading.gl.val (eOfF (W.entry y x)) := by
  unfold wVec
  rw [if_pos hx, List.sum_ofFn,
    Finset.sum_range (fun y => (g.map fun t => Reading.gl.val (t.entry y)).sum *
      Reading.gl.val (eOfF (W.entry y x)))]
  rfl

/-- **(Dot) at any reading**, where W is the row weights applied to matOf of the rows and Omega is its
text. -/
theorem dot_of_vectors {K : Type} [Field K] (ρ : OnBytes.Model.Reading K) (S : LinShape) (RwE : Nat → Nat → E)
    (psi : List E) (hp : psi.length = S.kCol)
    (hroom : S.matrixRows * 2 ^ S.kLo ≤ S.fold.index.plain) (g Om Wv : Nat → K)
    (hV : VIs S g (fun r k => ρ.val (RwE r k)) Wv)
    (hO : ∀ y < S.matrixRows, Om y = ρ.val (omegaAtE S psi RwE y)) :
    DotEq S.matrixRows S.kCol g Om (psi.map ρ.val) Wv := by
  have hlo : ((psi.take S.kLo).map ρ.val).length = S.kLo := by
    rw [List.length_map, List.length_take, hp]
    unfold LinShape.kCol
    omega
  have hu : (fun k => ρ.val (uAtE S psi RwE k)) =
      uHon S.fold (Desc.K14.Law.eqK ((psi.drop S.kLo).map ρ.val))
        (fun r k => ρ.val (RwE r k)) :=
    funext fun k => val_uAtE ρ S psi RwE k
  have hD := dotEq_honest S ((psi.take S.kLo).map ρ.val) ((psi.drop S.kLo).map ρ.val) g _ _ Wv
    (fun r k => ρ.val (RwE r k)) hlo
    (uHon_isFold S.fold (Desc.K14.Law.eqK ((psi.drop S.kLo).map ρ.val)) _)
    (fun _ _ => rfl) hroom hV
  have e : (psi.take S.kLo).map ρ.val ++ (psi.drop S.kLo).map ρ.val = psi.map ρ.val := by
    rw [← List.map_append, List.take_append_drop]
  rw [e] at hD
  unfold DotEq at hD ⊢
  rw [← hD]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [hO y (Finset.mem_range.1 hy), val_omegaAtE ρ S psi RwE y, hu]

/-- **(Dot) at the two texts.** psi: the shared point. hp: it has the shape's number of coordinates.
hroom: the matrix lies in front of the pads. -/
theorem dot_of_texts (S : LinShape) (W : Weights) (c : TableRand) (g : List Tensor) (psi : List E)
    (hp : psi.length = S.kCol) (hroom : S.matrixRows * 2 ^ S.kLo ≤ S.fold.index.plain)
    (Om Wv : Nat → GE) (hW : ∀ x < 2 ^ S.kCol, Wv x = wVec S W g x)
    (hO : ∀ y < S.matrixRows, Om y = Reading.gl.val (omegaAtE S psi (rowsOf S W c) y)) :
    DotEq S.matrixRows S.kCol (fun y => (g.map fun t => Reading.gl.val (t.entry y)).sum) Om
      (psi.map Reading.gl.val) Wv := by
  refine dot_of_vectors Reading.gl S (rowsOf S W c) psi hp hroom _ Om Wv ?_ hO
  intro x hx
  rw [hW x hx, wVec_is_sum S W g hx]
  exact Finset.sum_congr rfl fun y hy => by
    rw [rows_matOf S W c (Finset.mem_range.1 hy)]

end ProofFile.Honest.Door

#print axioms ProofFile.Honest.Door.rows_matOf
#print axioms ProofFile.Honest.Door.wVec_is_sum
#print axioms ProofFile.Honest.Door.dot_of_vectors
#print axioms ProofFile.Honest.Door.dot_of_texts
