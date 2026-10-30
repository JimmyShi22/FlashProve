-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Opts/WholeOfLaid.lean: AN OFFER TO WHOEVER OWES THIS TEST:
the named condition wholeB
(Johnson/P5J/OptsOk.lean: the sixth of OptsOk's seven: the proof file's rounds' data are there at
the public part: no default answers in silence) FROM «THE VALUE IS LAID» ALONE: NO SCOPE, NO PIN, AT
EVERY LETTER o FOR THE SECOND HASH FUNCTION.
  wholeAt_of_laid  under LaidAt (Johnson/P5J/LaidOpens.lean): ProofFile.wholeAt Zp = some D: AND
                   THE DATA ARE THE LAID ONES
  wholeB_of_laid   so (ProofFile.wholeAt Zp).isSome = true: THE TEST's OWN TEXT, UNFOLDED (OptsOk.lean
                   :65: def wholeB Zp := (ProofFile.wholeAt Zp).isSome): OptsOk.lean IS NOT IMPORTED: so
                   the file stands on LaidOpens.lean and CarryAtLaw.lean alone
HOW. At.Conds (Johnson/P5J/AtNameA.lean) asks its conditions under LaidAt.
descPure_seated (Johnson/Desc/ProofFile/Law/CarryAtLaw.lean) opens LaidAt's field «value» into the
public part, the places and the first chain's make; the public part is Zp by the field «pub»;
that file's wholeAt_of, at the field «data», is the statement.
LIMITS. Two short laws. That LaidAt can be met is not said here. No soundness is claimed.

-/
import Johnson.P5J.LaidOpens
import Johnson.Desc.ProofFile.Law.CarryAtLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1M2
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open P5J (LaidAt TS)

variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **Where the value is laid, the proof file's rounds' data are there at the public part**: and
they are the laid ones. -/
theorem wholeAt_of_laid (L : LaidAt o pol lay KL D r Zp Np cF) : ProofFile.wholeAt Zp = some D := by
  obtain ⟨Z', N', c', hZ, hN, hc, e⟩ := ProofFile.Law.descPure_seated L.value
  obtain rfl : Zp = Z' := Except.ok.inj (L.pub.symm.trans hZ)
  exact ProofFile.Law.wholeAt_of hN hc (e ▸ L.data)

/-- **OptsOk's sixth test**, unfolded: P5J.At.wholeB Zp := (ProofFile.wholeAt Zp).isSome. -/
theorem wholeB_of_laid (L : LaidAt o pol lay KL D r Zp Np cF) :
    (ProofFile.wholeAt Zp).isSome = true := by
  rw [wholeAt_of_laid L]
  rfl

end P1M2

#print axioms P1M2.wholeAt_of_laid
#print axioms P1M2.wholeB_of_laid
