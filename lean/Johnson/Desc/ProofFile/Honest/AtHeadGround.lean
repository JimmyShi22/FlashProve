-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/AtHeadGround.lean: the public part, the ground and the description in
the structure that `onlineProverFromPublicFiles` (Honest/AtPure.lean) returns are the values of three functions of the
public files. So a statement that names these three values speaks of the prover that `onlineProverFromPublicFiles`
returns. Four lemmas; no definition.

  1  `atPure_of_three`   if `pubPlain` returns `Zp`, `blankBy pureRoad.links Zp` is `some G` and
     `onlineDescription` returns `F`, all at the files at which `onlineProverFromPublicFiles` returns `A`, then `A.Z = Zp`,
     `A.G = G` and `A.F = F`
  2  `atPure_first_of_three`   then the first chain's prover's sides are `firstOf Zp G P.lots`
  3  `atPure_at_laid_ground`, `atPure_first_at_laid`   the same from the library's `P5J.LaidAt`
     (Johnson/P5J/LaidOpens.lean), which holds the first and the third hypothesis

Limits.
  * That `onlineProverFromPublicFiles` returns at any files is a hypothesis.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.AtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Chain FileDescription)
open OnBytes.Maker (WholeD)
open P5J (LaidAt F0T TS)

variable {W₀ Rc Tr X₀ X : Type} {o : SecondHashFunctionArgument} {pol lay KL : ByteArray}
  {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} {Zp : Pub} {G : Ground}

theorem atPure_of_three {F : FileDescription Inst} (hZ : pubPlain o pol lay KL = .ok Zp)
    (hG : blankBy pureRoad.links Zp = some G) (hF : onlineDescription o pol lay KL = .ok F)
    (hA : onlineProverFromPublicFiles o pol lay KL P = .ok A) : A.Z = Zp ∧ A.G = G ∧ A.F = F := by
  obtain ⟨h1, h2, h3, -⟩ := atPure_ok hA
  have e1 : A.Z = Zp := Except.ok.inj (h1.symm.trans hZ)
  rw [e1, hG] at h2
  exact ⟨e1, (Option.some.inj h2).symm, Except.ok.inj (h3.symm.trans hF)⟩

theorem atPure_first_of_three {F : FileDescription Inst} (hZ : pubPlain o pol lay KL = .ok Zp)
    (hG : blankBy pureRoad.links Zp = some G) (hF : onlineDescription o pol lay KL = .ok F)
    (hA : onlineProverFromPublicFiles o pol lay KL P = .ok A) : A.H.first = firstOf Zp G P.lots := by
  obtain ⟨e1, e2, -⟩ := atPure_of_three hZ hG hF hA
  rw [(atPure_ok hA).2.2.2.2.2.2.2.1, e1, e2]

variable {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

theorem atPure_at_laid_ground (h : LaidAt o pol lay KL D r Zp Np cF)
    (hG : blankBy pureRoad.links Zp = some G) (hA : onlineProverFromPublicFiles o pol lay KL P = .ok A) :
    A.Z = Zp ∧ A.G = G ∧ A.F = F0T o Zp Np cF :=
  atPure_of_three h.pub hG h.value hA

theorem atPure_first_at_laid (h : LaidAt o pol lay KL D r Zp Np cF)
    (hG : blankBy pureRoad.links Zp = some G) (hA : onlineProverFromPublicFiles o pol lay KL P = .ok A) :
    A.H.first = firstOf Zp G P.lots :=
  atPure_first_of_three h.pub hG h.value hA

end ProofFile.Honest

#print axioms ProofFile.Honest.atPure_of_three
#print axioms ProofFile.Honest.atPure_first_of_three
#print axioms ProofFile.Honest.atPure_at_laid_ground
#print axioms ProofFile.Honest.atPure_first_at_laid
