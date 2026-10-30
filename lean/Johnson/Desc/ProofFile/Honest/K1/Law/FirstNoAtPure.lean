-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/FirstNoAtPure.lean: THE SHARED "SENDING" (the kind K1): THE
RECORD's FIELD firstNo (K1Seated, Honest/K1/Seated.lean) AT THE PROVER THAT onlineProverFromPublicFiles RETURNS, AT A
FILLING THAT IS A LETTER. PUBLIC NUMBERS. One theorem; no definition.

  - firstNo_atPure: UNDER h (the library's head) and hA (onlineProverFromPublicFiles returns A at the filling P), at a
    place p of the written list (P5J.At.ps[b]? = some p): the table's number of oracle messages in
    front of p is lotNo secondHashFunction A.Z p.

The road. TWO CALLS: A.Z = Zp (atPure_at_laid_ground, Honest/AtHeadGround.lean) · the same equation
at Zp (firstNo_laid, Honest/K1/Law/FirstNoTold.lean).

KIN, TOLD. firstNo_laid, firstNo_at_head and firstNo_at (FirstNoTold.lean) say it at Zp; here it
stands at A.Z: the form in which a job's first number is written. THE SAME STATEMENT AND PROOF STAND
UNDER THE NAME firstNo_wider IN AN ELDER FILE OF OURS THAT IS HANDED IN TO NO LIST
(RecordAtWider.lean: its other laws are nailed to one filling): it is laid here so that the records
at a filling that is a letter need not import that file.

Limits. UNDER h: A HYPOTHESIS. That onlineProverFromPublicFiles returns is a premise. THE FULL SIZE; the format's second
hash function. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.AtHeadGround
import Johnson.Desc.ProofFile.Honest.K1.Law.FirstNoTold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Place)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **firstNo AT THE EARLIER HASH**: at a job whose first number is lotNo secondHashFunction A.Z at its place,
at any filling P. The table's number is lotNo's by firstNo_laid (FirstNoTold.lean). -/
theorem firstNo_atPure (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) {b : ℕ} {p : Place}
    (hp : P5J.At.ps[b]? = some p) :
    (P5J.At.N Zp cF).msgsAt (some p) = lotNo OnBytes.secondHashFunction A.Z p := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨eZ, -, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  rw [eZ]
  exact firstNo_laid h.scope h.reads h.laid (List.mem_of_getElem? hp)

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.firstNo_atPure
