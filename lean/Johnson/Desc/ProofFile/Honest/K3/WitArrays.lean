-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/WitArrays.lean: the honest side of the kind "lookup" (K3): the
digits' keys and bits are read off the one structure of the two arrays ZZ and BZ. Two small
theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: ZZ and BZ are the two arrays that are to be sent behind
the smallness test's round: the fields zz and bz of `Digits` (Honest/K8/Digits.lean).

What is shown. Honest/K8/Digits.lean has one structure `Digits` for the two arrays;
Johnson/HonestTrace/DigitsAtTrace.lean fills it: `digitsOf tl mats C trits`: ZZ is `zzOf`, BZ is
`bzOf` of it. The lookup's structure (`lookZ`, Honest/K3/WitFill.lean, at `zzOf`) is written from
`zzOf` and `bzOf`. These lemmas say that it reads the very fields of `digitsOf`.
  `lookZ_key_digitsOf`: the key vector is the joint vector of `kvZ` at the field zz of `digitsOf`,
    carried into the extension field.
  `lookZ_bit_digitsOf`: bit (u, j) is the field bz of `digitsOf` at BZ's own address of (u, j),
    carried into the extension field.

Imported, through Honest/K3/WitDigits.lean: Johnson/Desc/ProofFile/Honest/K8/Digits.lean and
Johnson/HonestTrace/DigitsAtTrace.lean.

Users. Honest/K3/BzTie.lean calls both theorems.

Limits. No sender of ZZ or BZ is written, in any file that this file imports:
the lemmas tie the lookup to the structure that a sender is meant to send, not to what is
sent. Shown in part: `bit_is_bzValsAt` and `key_is_zzVals` (Honest/K3/BzTie.lean) tie the lookup's
bits and keys to the values that `bzValsAt` (Johnson/HonestTrace/BZRows.lean) and `zzVals`
(Honest/K8/ZzData.lean) give for the two arrays.
Both theorems are conditional on the segment's public data
and on the round's having been heard; and by that file's limits the list of where the matrices are
read stays a letter at both fillings. The list mats is an argument on both sides.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.WitDigits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes.HonestTrace (digitsOf kvZ)
open ProofFile.Honest.K8 (zzOf)

/-- The keys are made of the ZZ of `digitsOf`. -/
theorem lookZ_key_digitsOf (tl : OnBytes.Model.HTailF2) (mats : List (ℕ × String × ℕ)) (C : Cells)
    (ts : List Int) (theta : Cb.Gl.E) (n : ℕ) :
    (lookZ tl (zzOf tl mats C ts)).key theta n =
      OnBytes.Ends.jointKey tl.f9 (kvZ tl (inExt (digitsOf tl mats C ts).zz)) theta n := rfl

/-- A bit is the BZ of `digitsOf` at BZ's own address. -/
theorem lookZ_bit_digitsOf (tl : OnBytes.Model.HTailF2) (mats : List (ℕ × String × ℕ)) (C : Cells)
    (ts : List Int) (u j : ℕ) :
    (lookZ tl (zzOf tl mats C ts)).bit u j =
      inExt (digitsOf tl mats C ts).bz ((OnBytes.DgP.portQ tl).bAt u j).2.1
        ((OnBytes.DgP.portQ tl).bAt u j).2.2 :=
  (map_natCast (algebraMap Cb.Gl.F Cb.Gl.E) _).symm

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.lookZ_key_digitsOf
#print axioms ProofFile.Honest.K3.lookZ_bit_digitsOf
