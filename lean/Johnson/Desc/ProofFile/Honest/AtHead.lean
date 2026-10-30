-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/AtHead.lean: WHERE THE HONEST PROVER's MAKER (`onlineProverFromPublicFiles`,
Honest/AtPure.lean) YIELDS AT THE THREE PUBLIC FILES AT WHICH THE LIBRARY's VALUE IS LAID
(`P5J.LaidAt`, Johnson/P5J/LaidOpens.lean), ITS PUBLIC PART AND ITS DESCRIPTION ARE THE LIBRARY's
OWN TERMS: both are what `pubPlain` and `onlineDescription` return at these files. Statements and proofs: two
injections, and what follows by rewriting.

  `atPure_at_laid`   A.Z = Zp and A.F = P5J.F0T o Zp Np cF
  `atPure_is`        A is a structure of these two with a ground, a book, a prover, readers and
                    data: the form in which the equations can be spent: the states' and the claims'
                    types of A.F hang on A.F, so that an equation of its lists is typed only behind
                    it
  `atPure_planOk`    the description's own test on the plan: the library's field: NO EVALUATION
  `atPure_places`    the places' numbers are made of A's public part

What they are for. The laws on the first chain's letters stand at `P5J.F0T o Zp Np cF`; the book and
the prover are made by `onlineProverFromPublicFiles`. These join the two.

Limits. `P5J.LaidAt` is the full size's. The library's head has a member at the name under four
premises on the public files (the seal's `P5J.head_exists_at_name`,
Johnson/P5J/HeadExistsAtName.lean); none of our files calls it; no member of the head together with
a thread's sentence is shown. They say nothing where the maker rejects, and not that it yields at
any files. Nothing on a run, a coin or a measure. This file proves nothing about soundness,
completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.AtPureLaw
import Johnson.P5J.LaidOpens

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)
open P5J (LaidAt F0T TS)

variable {W₀ Rc Tr X₀ X : Type} {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {D : WholeD}
  {r : LPFD.Full.RunPF} {Zp : Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **The two injections.** -/
theorem atPure_at_laid (h : LaidAt o pol lay KL D r Zp Np cF) (hA : onlineProverFromPublicFiles o pol lay KL P = .ok A) :
    A.Z = Zp ∧ A.F = F0T o Zp Np cF := by
  obtain ⟨hZ, -, hF, -⟩ := atPure_ok hA
  exact ⟨Except.ok.inj (hZ.symm.trans h.pub), Except.ok.inj (hF.symm.trans h.value)⟩

/-- **The form in which they can be spent.** -/
theorem atPure_is (h : LaidAt o pol lay KL D r Zp Np cF) (hA : onlineProverFromPublicFiles o pol lay KL P = .ok A) :
    ∃ G B H rd rw, A = ⟨Zp, G, F0T o Zp Np cF, B, H, rd, rw⟩ := by
  obtain ⟨e1, e2⟩ := atPure_at_laid h hA
  cases A with
  | mk Z G F B H rd rw =>
    dsimp only at e1 e2
    subst e1
    subst e2
    exact ⟨G, B, H, rd, rw, rfl⟩

/-- The description's own test on the plan. -/
theorem atPure_planOk (h : LaidAt o pol lay KL D r Zp Np cF) (hA : onlineProverFromPublicFiles o pol lay KL P = .ok A) :
    A.F.planOk = true := by
  rw [(atPure_at_laid h hA).2]
  exact h.planOk

/-- The places' numbers. -/
theorem atPure_places (h : LaidAt o pol lay KL D r Zp Np cF) (hA : onlineProverFromPublicFiles o pol lay KL P = .ok A) :
    H2U.placesOfMade A.Z.made = .ok Np := by
  rw [(atPure_at_laid h hA).1]
  exact h.places

end ProofFile.Honest

#print axioms ProofFile.Honest.atPure_at_laid
#print axioms ProofFile.Honest.atPure_is
#print axioms ProofFile.Honest.atPure_planOk
#print axioms ProofFile.Honest.atPure_places
