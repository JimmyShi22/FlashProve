-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/Digits.lean: THE SMALLNESS TEST, THE HONEST PROVER's SIDE: one
structure for two arrays as they are BEFORE ENCODING, as readers: the array of digits ZZ and the
bits BZ of the multiplicities of the lookup on the digits; and the first of the two, made of the
witness's cells and the drawn matrix. Which part encodes and sends them, with which coins, is not
said here. DEFINITIONS, WITH CODE. NO THEOREM. NOTHING IS CLAIMED ON COMPLETENESS, SOUNDNESS OR
HIDING.

It is meant to be made once and read by all who need these arrays: the part that encodes them, this
kind, and the lookup on the digits. NO COIN IS IN IT.

  `Digits`      zz u col: ZZ's entry in row u and column col; bz row col: BZ's
  `parOfTail`   the numbers that the digits hang on, off the plan's state of the smallness test:
                 each matrix's columns and rows of cells, and the number of combinations
  `zzOf tl mats C trits`   ZZ: the natural number `digitAt` (Johnson/Desc/K8/Honest/Window.lean),
                 as an element of the base field. mats: for each matrix of the list: its OWNER's
                 segment number, its name there as the verifier's own plan lays it, its first
                 column under that name (Honest/K8/Part.lean: `cellsAtOf`, and that head's WHICH
                 MATRIX IS WHICH): a list holds matrices of earlier segments too. trits: the matrix
                 entries of the kind's round, as drawn. NO TEST ON THE TWO LISTS' LENGTHS STANDS
                 HERE: `smallFits` and `drawnFits` (Honest/K8/Part.lean) are the caller's to ask
NOT HERE: BZ. It is a function of ZZ's digits, and the lookup's honest side's to make.
WRITTEN A FURTHER TIME: `parOfTail tl` has the text of the library's `parOf tl 0 0 [] [] []`
(Johnson/Desc/First/K8/LawAtS.lean), which is not called here. SHORT NAMES THAT STAND ELSEWHERE, FOR
OTHER THINGS: `Digits` (Johnson/AtFull/K3X/KernelTests.lean) · `zzOf`
(Cb/Pv/KeyLookup/CloseLaid.lean).

Limits. The entries lie in their digits' ranges at every drawn matrix; they give a combination back
only where it lies in its window (Johnson/Desc/K8/Honest/DigitsLaw.lean). Of the other numbers of
`parOfTail` nothing is read: they are laid as 0 and empty lists; that its three numbers are those at
which the part stands: Honest/K8/DigitsSame.lean, a file which this library may not hold.
-/
import Johnson.Desc.ProofFile.Honest.K8.Part

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open VerifiableInference.Desc.First.K8 (Par)
open VerifiableInference.Desc.First.K8.Honest (digitAt)

/-- The two arrays, before encoding, as readers. -/
structure Digits where
  /-- ZZ: row u below tau; column col below twice the rows of cells of all matrices: the low digits,
  then the high digits -/
  zz : Nat → Nat → Cb.Gl.F
  /-- BZ: 32 rows, 2^11 columns -/
  bz : Nat → Nat → Cb.Gl.F

/-- The numbers that the digits hang on, off the plan's state of the smallness test. -/
def parOfTail (tl : OnBytes.Model.HTailF2) : Par :=
  { link := 0, piece := 0, ks := tl.mats.toList.map (·.k), ms := tl.mats.toList.map (·.m)
    tau := tl.tau, asks := [], matsIn := [], readsIn := [] }

/-- **ZZ.** This is the array before encoding: which part sends it, with which coins, is not said
here. At a name in mats that is no label the cells are what the reader yields there. -/
def zzOf (tl : OnBytes.Model.HTailF2) (mats : List (Nat × String × Nat)) (C : Cells)
    (trits : List Int) : Nat → Nat → Cb.Gl.F :=
  fun u col => ((digitAt (parOfTail tl) (cellsAtOf C mats) trits.toArray u col : ℕ) : Cb.Gl.F)

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.Digits
#print axioms ProofFile.Honest.K8.parOfTail
#print axioms ProofFile.Honest.K8.zzOf
