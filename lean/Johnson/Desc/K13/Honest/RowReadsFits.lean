-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Honest/RowReadsFits.lean: WHAT THE ROWS OF THE PILE's FILLER `pileBySites`
(PileDefs.lean of this folder) ARE LIKE, WHEREVER IT YIELDS A ROW AT ALL: THEIR NUMBER; THE LENGTH
OF EACH COLUMN POINT; THAT EACH HAS A WEIGHT; THE NUMBER OF VARIABLES OF EACH WEIGHT. One
definition, and statements with their proofs. It stands on PileDefs.lean and the library alone.

The filler's weights are what the library's `weightsOnRows` (Johnson/Desc/Own/Stretch.lean) returns:
the blocks of a stretch of rows (`stretchBlocks`, OnBytes/Iop/Lin.lean). The library has of these
blocks what their entries read as and that each passes `Tensor.ok`
(Johnson/Road/Rows/StretchLaws.lean; `stretchBlocks_ok`, `memberWeightsOnRows_ok`:
Johnson/Desc/First/Pend/RowOk.lean), and that their pairs do not hang on the values
(`stretchBlocks_skel`, OnBytes/Flat/PendingSizes.lean): kin. A search for a law on their number of
variables, or that the list is not empty, found none that gives the number (`Tensor.ok` bounds it;
`PendAlike`, PendingSizes.lean, says that two rows' weights have the same numbers), and none on the
list. Called: `weightsOnRows_some`
(Johnson/Desc/Own/StretchAgree.lean), `weightsOnRows_iff`, `gamma_iff`, `added_size`
(Johnson/Desc/First/Pend/RowMeans.lean), `blockOf`, `stretchBlocks_succ`, `blockBits_spec`
(StretchLaws.lean), `choicePairs_length` (OnBytes/Iop/TensorLaws.lean), `mapM_length`,
`all_mapM_mem` (Johnson/Road/K4/Slots/Groups.lean: two lemmas on lists).
Main names:
  `blockOf_vars`, `stretchBlocks_vars`, `weightsOnRows_vars`: **each vector that `weightsOnRows`
    returns has the shape's kRow variables.** `weightsOnRows_ne`: **it returns no empty list where a
    value is written.** `gammaOf_size`: adding the claims' weights leaves the number of rows.
  `ReadsFit lay S q`: of a row's weights and column point: as many coordinates as the layout has
    column bits; at least one weight; kRow variables in each. (The library's `Sound.Piece.ReadsFit`,
    Johnson/Desc/Sound/ReadsOfData.lean, shares the last name and nothing else.)
  `rowReadsOf_fits`, `pileRowAt_fits`: **whatever `rowReadsOf` returns has it; so has the filler's
    row at a site.**
  `pileBySites_fits`: **wherever the filler yields a row at all, it yields as many rows as there are
    sites, and each has `ReadsFit`**: at every instance and all challenges.

What is not claimed. That the filler yields a row anywhere. That lay.lk is the shape's kCol. Nothing
on soundness, completeness or hiding.

-/
import Johnson.Desc.K13.Honest.PileDefs
import Johnson.Desc.First.Pend.RowMeans
import Johnson.Road.K4.Slots.Groups

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Params OnBytes.Model
open OnBytes.Road.Rows (blockOf stretchBlocks_succ blockBits_spec)
open VerifiableInference.Desc.Own (weightsOnRows weightsOnRows_some)
open VerifiableInference.Desc.First.Pend (gamma_iff gammaOf added_size weightsOnRows_iff)
open OnBytes.Desc.First.K4.Slots (all_mapM_mem mapM_length)

variable {Xi : Type}

/-! ## The weights on a stretch of rows -/

/-- The vector of one aligned piece of a stretch of rows has kRow variables. -/
theorem blockOf_vars (kRow firstRow : ℕ) (values : Array E) (start d : ℕ) (hd : d ≤ kRow) :
    (blockOf kRow firstRow values start d).vars = kRow := by
  unfold blockOf
  by_cases h : d = 0
  · subst h
    show (Tensor.insertChoice _ 0 kRow start).pairs.length = kRow
    unfold Tensor.insertChoice
    simp [choicePairs_length]
  · rw [if_neg (by simpa using h)]
    show ((Tensor.insertChoice (Tensor.pushDense {} d) d (kRow - d) (start / 2 ^ d)).setValues _
      _).pairs.length = kRow
    unfold Tensor.setValues Tensor.insertChoice Tensor.pushDense
    simp [choicePairs_length]
    omega

/-- So has each vector of a stretch's blocks. -/
theorem stretchBlocks_vars (kRow firstRow : ℕ) (values : Array E) : ∀ (fuel start : ℕ),
    ∀ t ∈ stretchBlocks kRow firstRow values fuel start, t.vars = kRow
  | 0, _, _, ht => absurd ht List.not_mem_nil
  | fuel + 1, start, t, ht => by
    rw [stretchBlocks_succ] at ht
    split at ht
    · exact absurd ht List.not_mem_nil
    · rename_i hs
      rcases List.mem_cons.1 ht with rfl | ht'
      · exact blockOf_vars _ _ _ _ _
          (blockBits_spec kRow start _ kRow 0 (Nat.zero_le _) (by simp) (by omega)).1
      · exact stretchBlocks_vars kRow firstRow values fuel _ t ht'

/-- **What `weightsOnRows` returns: each vector has the shape's kRow variables.** -/
theorem weightsOnRows_vars {S : LinShape} {first : ℕ} {values : Array E} {g : List Tensor}
    (h : weightsOnRows S first values = some g) : ∀ t ∈ g, t.vars = S.kRow := by
  rw [weightsOnRows_some h]
  exact stretchBlocks_vars _ _ _ _ _

/-- **It returns no empty list where a value is written.** -/
theorem weightsOnRows_ne {S : LinShape} {first : ℕ} {values : Array E} {g : List Tensor}
    (h : weightsOnRows S first values = some g) (hv : 0 < values.size) : g ≠ [] := by
  obtain ⟨⟨-, -, -, hsum⟩, rfl⟩ := (weightsOnRows_iff S first values g).1 h
  intro e
  rw [e] at hsum
  have : (0 : ℕ) = values.size := by simpa using hsum
  omega

/-- Adding the claims' weights leaves the number of rows. -/
theorem gammaOf_size (lay : WsLay) : ∀ (recs : List WsRecClaim) (G0 : Array E),
    (gammaOf lay recs G0).size = G0.size
  | [], _ => rfl
  | c :: t, G0 => by
    show (gammaOf lay t _).size = _
    rw [gammaOf_size lay t, added_size]

/-! ## A row of the filler -/

/-- What is said of a row's weights and column point: as many coordinates as the layout has column
bits; at least one weight; the shape's kRow variables in each weight. -/
def ReadsFit (lay : WsLay) (S : LinShape) (q : List Tensor × List E) : Prop :=
  q.2.length = lay.lk ∧ q.1 ≠ [] ∧ ∀ t ∈ q.1, t.vars = S.kRow

/-- **Whatever `rowReadsOf` returns has it.** -/
theorem rowReadsOf_fits {lay : WsLay} {S : LinShape} {n : ℕ} {recs : List WsRecClaim}
    {rm : Array E} {q : List Tensor × List E} (h : rowReadsOf lay S n recs rm = some q) :
    ReadsFit lay S q := by
  unfold rowReadsOf at h
  split at h
  · rename_i h0
    simp only [Bool.and_eq_true, beq_iff_eq] at h0
    split at h
    · rename_i first last hs
      split at h
      · rename_i h9
        split at h
        · rename_i Gamma hG
          obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.1 h
          have hsz : Gamma.size = last := by
            rw [((gamma_iff lay recs _ Gamma).1 hG).2, gammaOf_size, Array.size_replicate]
          refine ⟨by simp [h0.2], weightsOnRows_ne hg ?_, weightsOnRows_vars hg⟩
          rw [Array.size_extract, hsz]
          omega
        · cases h
      · cases h
    · cases h
  · cases h

/-- So has each row of the filler at a site. -/
theorem pileRowAt_fits {lay : WsLay} {S : LinShape} {claims : SiteClaims Xi} {x : Xi}
    {hd : List Fmt.Drawn} {m : MergeSite} {row : TensorRow}
    (h : pileRowAt lay S claims x hd m = some row) : ReadsFit lay S (row.g, row.psi) := by
  unfold pileRowAt at h
  obtain ⟨cl, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨y, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨q, hq, h⟩ := Option.bind_eq_some_iff.1 h
  obtain rfl := Option.some.inj h
  exact rowReadsOf_fits hq

/-- **THE FILLER, WHEREVER IT YIELDS A ROW AT ALL**: it yields as many rows as there are sites, and
each has `ReadsFit`. At every instance and all challenges. -/
theorem pileBySites_fits (lay : WsLay) (S : LinShape) (sites : List MergeSite)
    (claims : SiteClaims Xi) (x : Xi) (hd : List Fmt.Drawn)
    (h : pileBySites lay S sites claims x hd ≠ []) :
    (pileBySites lay S sites claims x hd).length = sites.length ∧
      ∀ row ∈ pileBySites lay S sites claims x hd, ReadsFit lay S (row.g, row.psi) := by
  unfold pileBySites at h ⊢
  cases hm : sites.mapM (pileRowAt lay S claims x hd) with
  | none =>
    rw [hm] at h
    exact absurd rfl h
  | some r =>
    exact ⟨mapM_length sites r hm,
      all_mapM_mem (Pr := fun row : TensorRow => ReadsFit lay S (row.g, row.psi)) sites r
        (fun _ _ _ e => pileRowAt_fits e) hm⟩

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.blockOf_vars
#print axioms VerifiableInference.Desc.K13.Honest.stretchBlocks_vars
#print axioms VerifiableInference.Desc.K13.Honest.weightsOnRows_vars
#print axioms VerifiableInference.Desc.K13.Honest.weightsOnRows_ne
#print axioms VerifiableInference.Desc.K13.Honest.gammaOf_size
#print axioms VerifiableInference.Desc.K13.Honest.rowReadsOf_fits
#print axioms VerifiableInference.Desc.K13.Honest.pileRowAt_fits
#print axioms VerifiableInference.Desc.K13.Honest.pileBySites_fits
