-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/KeyFillAtSizes.lean: THE FILLING's PUBLIC PREMISES AT THE REAL SIZES: the key file's six sampled messages at the full size, AT THE LIBRARY's OWN TYPED CODES AND SHAPES (Johnson/Top/H/KeyRows.lean: csKey · shIdx · shMul; KeyFamilies.lean: shW · shU · shO · shSp)
and those files' radii (6130 · 3131959 · 3138896 · 8342420 · 3138896 · 6130). BY THE KERNEL.
  six            the six, each with its radius
  hm_six         «hm» (Johnson/Desc/Key/KeyFill.lean's premise; the fifth clause of SeatFits, Johnson/Desc/Sound/MsgSig.lean): no main row, or the main rows' code is as long as the tree: AT ALL SIX
  caseE_six      CaseE (a mask row, or main rows over the extension field): under which the library's facts on the sample map portZ stand: AT ALL SIX
  meets_six      the library's own test meetsB (the codes fit · one answer · the pad fits · THE RADIUS LIES BELOW JOHNSON's · …) each at its own radius: AT ALL SIX
  deg_six        the degree is 1 or 3 (SeatFits' seventh clause)
  THE PLANTS: hm_plant: the multiplicities' shape with its main rows under code 10 (2^13: shorter than its mask rows' 2^16): hm says no (under code 13, 2^19, still the longer of the two, it rightly says yes) · meets_plant: each of the six at the radius 2 ^ aOf (the whole length): meetsB says no at all six · caseE_plant
OBJECT: none of F_K's text: the library's typed constants · USER: KeyFillNoCollAt.lean · Johnson/Top/Fire/Code/RowsEightSix.lean · LETTERS: none.
THAT F_K's SENDINGS SEND JUST THESE SHAPES UNDER JUST THESE CODES, AND THAT K1's AND K12's LAWS ARE CALLED AT JUST THESE RADII, IS NOT SAID HERE. Nothing on soundness.
-/
import Johnson.Top.H.KeyFamilies
import Johnson.Pack.Check

set_option autoImplicit false

namespace VerifiableInference.Desc.Key.Fill
open Johnson.Top.H Johnson.Top.H.Rows Johnson.Pack

def six : List (OnBytes.OracleShape × ℕ) :=
  [(Johnson.Top.H.shIdx, 6130), (Johnson.Top.H.shMul, 3131959), (Johnson.Top.H.shW, 3138896), (Johnson.Top.H.shU, 8342420), (Johnson.Top.H.shO, 3138896),
    (Johnson.Top.H.shSp, 6130)]

def hmB (cs : OnBytes.Codes) (s : OnBytes.OracleShape) : Bool := decide (s.mainRows = 0) || decide ((cMain cs s).a = aOf cs s)

theorem hmB_iff (cs : OnBytes.Codes) (s : OnBytes.OracleShape) : hmB cs s = true ↔ (s.mainRows = 0 ∨ (cMain cs s).a = aOf cs s) := by
  simp [hmB]

theorem hm_six : (six.all fun p => hmB csKey p.1) = true := by decide +kernel
theorem caseE_six : (six.all fun p => decide (CaseE p.1)) = true := by decide +kernel
theorem meets_six : (six.all fun p => meetsB csKey p.1 p.2) = true := by decide +kernel
theorem deg_six : (six.all fun p => decide (p.1.mainDeg = 1 ∨ p.1.mainDeg = 3)) = true := by decide +kernel

theorem hm_plant : hmB csKey { Johnson.Top.H.shMul with code := 10 } = false := by decide +kernel
theorem meets_plant : (six.any fun p => meetsB csKey p.1 (2 ^ aOf csKey p.1)) = false := by decide +kernel
theorem caseE_plant : decide (CaseE { Johnson.Top.H.shMul with maskRows := 0 }) = false := by decide +kernel

end VerifiableInference.Desc.Key.Fill

#print axioms VerifiableInference.Desc.Key.Fill.hm_six
#print axioms VerifiableInference.Desc.Key.Fill.caseE_six
#print axioms VerifiableInference.Desc.Key.Fill.meets_six
#print axioms VerifiableInference.Desc.Key.Fill.hm_plant
#print axioms VerifiableInference.Desc.Key.Fill.meets_plant
