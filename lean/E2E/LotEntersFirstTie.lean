-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotEntersFirstTie.lean: THE PREMISE RangeTie OF E2E/LotEntersFirstCore.lean, PAID AT THE REAL VALUE: in
scope, at the matrices of the full size's shape, at the index's reader matrixReader and at any senders whose
test on the index is matrixInput.inRange ("the matrix holds an index").

It ties three texts of "in range": the prover's test (matrixInput.inRange, E2E/TheHonestProver.lean) · the
object's cut (Flat.InRange; inRange_iff, E2E/KeyRangeOne.lean) · the two items of the first chain's
table (Key.InRange at the plan's two lookups, on machine words).

  `says_matrix`: at a matrix whose cells lie in the base field, the table of matrixReader says the matrix.
  **`rangeTie_atValue`**: RangeTie.
  `entersFirst_atValue`: so the first chain begins there, with no premise on the range. At the prover's own
    senders: E2E/LotEntersFirstAtTerm.lean.

What is spent. inRange_iff (E2E/KeyRangeOne.lean) · ranges_of_inRange (E2E/LotEntersFirstRanges.lean; its road is
wfPairs_iff_inRange, not PartsIn) · in scope the plan's lookups are lk0Full,
lk1Full and its matrix has kRef column bits (LPFD.one_full, looks_full, kCol_full) · inBase_of_inRange
(E2E/KeyPlanesAtFull.lean) · matAt_cells (E2E/FirstHFill.lean).

Limits. ONE WAY, AND NOT TO BE WORDED AS "IF AND ONLY IF": from the prover's test to the two items. The way back
fails at this reader: it reads each cell's first coordinate alone, and a matrix all of whose cells are
(0, 1, 0) is out of range while both items hold of what is read off it
. In scope alone, at the reference sizes alone: only there are the two items these two
sentences. E2E/KeyRangeOne.lean, which is called, has stood in a working ride, under no seal. Nothing on
any prover's run, on a verifier, or on any property.
-/
import E2E.LotEntersFirstCore
import E2E.LotEntersFirstRanges
import E2E.KeyRangeOne
import E2E.KeyArgumentsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace AtPublicFiles.FirstH.Lots
open OnBytes OnBytes.Slice
open VerifiableInference.Desc.Key (Source LaterPlaces matAt InRange)
open Johnson.RunOne.KeyRows1 (plan₁)
open Johnson.Pack (lk0Full lk1Full)
open Inst.Model.Layout (kRef hRef)
open AtPublicFiles.KeyThread (one₀)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.AtFiles (KeySourced FullSizeMatrix)
open AtPublicFiles.AtFiles.HonestTerm (inRange_iff matrixReader)
open ProofFile.Honest.Term (matrixInput)
open VerifierAndGoals (PublicFiles InScope)
open LPFD (rdF)

/-- At a matrix whose cells lie in the base field, the table of its reader says the matrix. -/
theorem says_matrix (S : OnBytes.Params.LinShape) (M : FullSizeMatrix) (hb : AtPublicFiles.Key.InBase M)
    (y : Fin hRef) (c : Fin (2 ^ kRef)) :
    M y c = rdF (matAt S (cellsOf S ⟨AtPublicFiles.Key.cellsReader M⟩) y.val c.val) := by
  rw [matAt_cells]
  show M y c = readE (OnBytes.ofF (OnBytes.Slice.ofF (AtPublicFiles.Key.cellsReader M y.val c.val)))
  rw [readE_ofF, toF_ofF]
  unfold AtPublicFiles.Key.cellsReader
  rw [dif_pos ⟨y.isLt, c.isLt⟩]
  exact hb y c

section
variable {Rc X₀ X' Wk : Type} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces} {Z : PublicFiles}

/-- **RangeTie at the real value.** -/
theorem rangeTie_atValue (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (K : KeyParts FullSizeMatrix Rc X₀ X' Wk) (hK : K.inRange = matrixInput.inRange) (M : FullSizeMatrix) :
    RangeTie Xs K matrixReader M := by
  intro inR l hl v hv
  obtain ⟨Y₀, m, h0, hm, hX, -, -⟩ := hs.source
  obtain ⟨e1, e2, -⟩ := LPFD.one_full (N := N) (P := Pl) scope
    (Johnson.RunOne.Law.ReadAtO.readOf_publicOfO h0) hm hX hs.named.plan
  have hlk : (plan₁ (one₀ Xs)).lookups = [lk0Full, lk1Full] := by
    show (one₀ Xs).ranges.lookups = _
    rw [e1]
    exact LPFD.looks_full
  have hk : (plan₁ (one₀ Xs)).m.kCol = kRef := by
    show (OnBytes.Wf.matrixOf (one₀ Xs).lin).kCol = kRef
    rw [e2]
    exact LPFD.kCol_full
  have hR : VerifiableInference.OnPublicFiles.Flat.InRange M := (inRange_iff M).1 (hK ▸ inR)
  obtain ⟨r0, r1⟩ := ranges_of_inRange readH.same (fun _ _ h => h) (plan₁ (one₀ Xs)).m hk
    (matAt (one₀ Xs).lin (cellsOf (one₀ Xs).lin ⟨AtPublicFiles.Key.cellsReader M⟩)) M
    (says_matrix (one₀ Xs).lin M (AtPublicFiles.Key.inBase_of_inRange M hR)) hR
  show ∃ L, (plan₁ (one₀ Xs)).lookups[l]? = some L ∧
    InRange readH.same (plan₁ (one₀ Xs)).m L (matAt (one₀ Xs).lin v.cells)
  rw [hlk, hv]
  obtain rfl | rfl : l = 0 ∨ l = 1 := by omega
  · exact ⟨lk0Full, rfl, r0⟩
  · exact ⟨lk1Full, rfl, r1⟩

/-- **So the first chain begins at the real value, WITH NO PREMISE ON THE RANGE**: at any senders whose test on
the index is matrixInput.inRange, at the index's reader matrixReader. («ready returns» holds the test's yes.) -/
theorem entersFirst_atValue {Bk : ProofFile.Honest.ProverCoinCounts} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (K : KeyParts FullSizeMatrix Rc X₀ X' Wk) (hK : K.inRange = matrixInput.inRange)
    (Q : LaterFill Bk FullSizeMatrix Rc) (M : FullSizeMatrix) (rc : Rc) (x : VerifiableInference.Desc.Key.Xi)
    (rel : Q.Rel M rc x) (k : ProofFile.Honest.Coins Bk)
    (R : ProofFile.Honest.Ready FullSizeMatrix Rc VerifiableInference.Desc.Key.Xi OnBytes.TableKey Unit X₀ X')
    (hR : ProofFile.Honest.ready (AtPublicFiles.AtFiles.keyFileDescription Xs N Pl) Bk (AtPublicFiles.KeyFile.keyProver K) M rc x k = .ok R) :
    ProofFile.Honest.Enters₁ (AtPublicFiles.AtFiles.keyFileDescription Xs N Pl) (AtPublicFiles.KeyFile.keyProver K)
      (Th Xs N Pl K matrixReader Q M rc x) M rc x k R :=
  entersFirst_of_ready Xs N Pl K matrixReader Q M rc x hs scope (rangeTie_atValue hs scope K hK M) rel k R hR

end


end AtPublicFiles.FirstH.Lots

#print axioms AtPublicFiles.FirstH.Lots.says_matrix
#print axioms AtPublicFiles.FirstH.Lots.rangeTie_atValue
#print axioms AtPublicFiles.FirstH.Lots.entersFirst_atValue
