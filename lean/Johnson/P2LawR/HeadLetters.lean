-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/HeadLetters.lean: THE HEAD's LETTERS ARE FUNCTIONS OF THE THREE PUBLIC FILES. One
definition, two theorems. A top asks a test "at every
head" (∀ Zp Np cF x h), a file of evaluations evaluates it at one triple that it has made of the
files: between the two lies this file.

  P5J.lettersOf o pol lay KL   the six calls in a row by which the verifier's own road makes D, Zp,
  Np, cF of the files:
                   pubPlain · placesOfMade · baseOf · (partsAt …).base · chainBy · (F0T …).data
                   "proof file"; none where one fails
  P5J.AtMg.letters     under the one head: lettersOf o Z.pol Z.lay Z.KL = some (D, Zp, Np, cF)
  P5J.AtMg.letters_one   two heads over the same files, at the same o, have the same four letters
HOW. The head holds the opening of the maker (IM.Open, Johnson/IMR/SeatOpen.lean: each
letter by the call that made it) in its field laid.opened, and the fields laid.places and laid.data.
What is not claimed. That a head can be had. Whether Lean makes code for lettersOf is not tried
here. Nothing on soundness.
-/
import Johnson.P5J.AtMg
import Johnson.IMR.SeatOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)

/-- **The head's four letters, made of the three files**: the six calls in a row. -/
def lettersOf (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) :
    Option (WholeD × ProofFile.Pub × H2U.Places4 × Chain TS ProofFile.Cl) :=
  match ProofFile.pubPlain o pol lay KL with
  | .error _ => none
  | .ok Zp =>
    match H2U.placesOfMade Zp.made with
    | .error _ => none
    | .ok Np =>
      match ProofFile.baseOf Zp (ProofFile.pureSeat o Zp) with
      | .error _ => none
      | .ok Bs =>
        match (ProofFile.partsAt (ProofFile.pureSeat o Zp) Bs).base with
        | .error _ => none
        | .ok base =>
          match ProofFile.chainBy Zp base (ProofFile.partsAt (ProofFile.pureSeat o Zp) Bs).frames
              (ProofFile.partsAt (ProofFile.pureSeat o Zp) Bs).road with
          | .error _ => none
          | .ok cF =>
            match (F0T o Zp Np cF).data "proof file" with
            | .error _ => none
            | .ok D => some (D, Zp, Np, cF)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D D' : WholeD} {r r' : LPFD.Full.RunPF}
  {Zp Zp' : ProofFile.Pub} {Np Np' : H2U.Places4} {cF cF' : Chain TS ProofFile.Cl}

/-- **Under the one head its four letters are what the six calls make of the files.** -/
theorem AtMg.letters (h : AtMg o Z D r Zp Np cF) :
    lettersOf o Z.pol Z.lay Z.KL = some (D, Zp, Np, cF) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  unfold lettersOf
  simp only [O.pub, h.laid.places, O.made, O.places, O.chain, h.laid.data]

/-- **Two heads over the same files have the same four letters.** -/
theorem AtMg.letters_one (h : AtMg o Z D r Zp Np cF) (h' : AtMg o Z D' r' Zp' Np' cF') :
    D = D' ∧ Zp = Zp' ∧ Np = Np' ∧ cF = cF' := by
  have e := Option.some.inj (h.letters.symm.trans h'.letters)
  simp only [Prod.mk.injEq] at e
  exact e

end P5J

#print axioms P5J.AtMg.letters
#print axioms P5J.AtMg.letters_one
