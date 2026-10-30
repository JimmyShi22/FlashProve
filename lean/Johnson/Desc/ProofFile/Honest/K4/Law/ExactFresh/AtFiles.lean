-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K4/Law/ExactFresh/AtFiles.lean: K4's hand-in for its simulators at the
base filling, for all public files in scope, read and live, at every return of the maker there; and
that a return exists. No letter is left but the base filling's own (the index's type, the reader I,
the sizes, the opening).

  `k4SimulatorAtTheFiles`   **at every return: the halves' equation; `K4HandIn` at the rows
      `k4SLotByPub`; no half of the kind in the later chains.**
  `k4SimulatorWhereTheMakerReturns`, `k4SimulatorAtTheMatrices`   **a return exists, with all of that.**

Limits. Those of Law/ExactFresh/HandIn.lean, of which nothing is taken back: THE SPENDER's HALF; fresh
TRUE AND EMPTY; NO JOINT LAW; A := B := False. AT THE BASE FILLING: the crossing to the term is made
once, above the rule, and is not K4's house's. Beneath these files lie files that are not in laws.14,
of our house and of other houses, among them the one that defines the base filling
(Honest/K1/Law/WSideAtFill.lean): the builder's walk of the lot's own ride says which. NOT HELD HERE: the owners' fresh (`K4OwnerFresh`,
OwedBeside.lean) · the carriers' laws and that a mask entry named by the verifier's count is the
book's · K4's plays at its borders · the book's lending of K4's runs · the falls (`k4Fall`,
`k4FreeSlotFall`: what each test reads; that `k4CoinZero` fires only where the member refuses) · that
none | some of K4's makers hangs on public sizes alone. It imports the library's head from the live
test, whose file stands on Johnson/Goal/. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.ExactFresh.HandIn
import Johnson.Desc.ProofFile.Honest.K4.Law.ExactFresh.AtBase
import Johnson.Desc.ProofFile.Honest.K4.Law.ExactFresh.KindHandsIn
import Johnson.P5J.HeadOfLive
import AtFullSide.K1.MakerReturnsBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.ExactFresh
open VerifierAndGoals (asDescriptionFiles)
open FlashProve (protocolDataWellFormed)

variable {W₀ : Type}

/-- **What stands at a return of the maker at the base filling.** -/
def K4AtBase (I : WiderIn W₀) (A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit) : Prop :=
  A.H.first.filter (fun y => decide (y.place.kind = .K4)) =
      ((k4SLotByPub (Rc := IndexCommitterCoins) (X := Unit) id I.weights fun _ _ => k4LookAt).rows A.Z A.G).map
        (·.half) ∧
    K4HandIn A.F.first.blocksInOrder A.B A.Z A.G
      ((k4SLotByPub (Rc := IndexCommitterCoins) (X := Unit) id I.weights fun _ _ => k4LookAt).rows A.Z A.G) ∧
    (∀ g ∈ A.H.shared, g.place.kind ≠ .K4) ∧ ∀ g ∈ A.H.second, g.place.kind ≠ .K4

/-- **K4's SIMULATORS AT THE BASE FILLING, FOR ALL PUBLIC FILES IN SCOPE, READ AND LIVE, AT EVERY RETURN
OF THE MAKER: THE SPENDER's HALF; fresh TRUE AND EMPTY; NO JOINT LAW; AT A := B := False.** -/
theorem k4SimulatorAtTheFiles (Z : VerifierAndGoals.PublicFiles) {pp : Inst.Model.ScalesAndPolicy}
    (scope : VerifierAndGoals.InScope Z = true) (read : VerifierAndGoals.readFiles Z = .ok pp)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I o S O) = .ok A) :
    K4AtBase I A := by
  obtain ⟨Zp, Np, cF, x, h⟩ := P5J.head_of_live Z scope read live
  have eF : A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF :=
    Except.ok.inj ((atPure_ok made).2.2.1.symm.trans h.laid.value)
  have plan : A.F.planOk = true := eF ▸ h.laid.planOk
  exact ⟨k4_halves_at_maker I o _ S O made, k4SimulatorHandInAtReturn h made id (I.weights A.Z) (fun _ _ => k4LookAt),
    k4_no_half_in_the_later_chains made plan⟩

/-- **THE SAME, WITH A RETURN: in scope and live, where the named index is in range, the maker returns
at the base filling, and all of it stands there: THE SPENDER's HALF; fresh TRUE AND EMPTY; NO JOINT
LAW; AT A := B := False.** -/
theorem k4SimulatorWhereTheMakerReturns (Z : VerifierAndGoals.PublicFiles) (scope : VerifierAndGoals.InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (range : I.inRange I.dummy = true) :
    ∃ A, onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A ∧
      K4AtBase I A := by
  obtain ⟨pp, read⟩ := LPFPol.read_of_scope scope
  obtain ⟨A, made⟩ := K1.maker_returns_base Z I S O range scope live
  exact ⟨A, made, k4SimulatorAtTheFiles Z scope read live I _ S O made⟩

/-- **THE SAME AT THE MATRICES.** -/
theorem k4SimulatorAtTheMatrices (Z : VerifierAndGoals.PublicFiles) (scope : VerifierAndGoals.InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    ∃ A, onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
        (onlineProverPartsInUse ProofFile.Honest.Term.matrixInput OnBytes.secondHashFunction S O) = .ok A ∧
      K4AtBase ProofFile.Honest.Term.matrixInput A :=
  k4SimulatorWhereTheMakerReturns Z scope live _ S O ProofFile.Honest.Term.range_matrixInput

end ProofFile.Honest.K4.ExactFresh

#print axioms ProofFile.Honest.K4.ExactFresh.k4SimulatorAtTheFiles
#print axioms ProofFile.Honest.K4.ExactFresh.k4SimulatorWhereTheMakerReturns
#print axioms ProofFile.Honest.K4.ExactFresh.k4SimulatorAtTheMatrices
