-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/LastFour.lean: THE LAST FOUR SUB-PROTOCOLS (blocks) OF THE PROOF FILE's FIRST CHAIN's
FLAT LIST, BY NUMBER, WITH THE STEP's ACCEPTING BROUGHT DOWN TO THE LOT's OWN DECISION: IN THE
GOALS' SCOPE.
WANTED FOR FoldFacts' field «K13.ownSits», a fact of position, and of use for «K13.pileMasks»: «c.blocksInOrder[n − 3]? = some b ∧ the step accepts from s to s' → ∃ rs gs, (K13.atM3 (K13.whereOf Z)).decide s rs gs = .ok s' … at n − 2 … at n − 1: s' = s».
THE STEP IS WRITTEN OUT (b.step ft s rs cols = .ok (s', n)): whoever holds StepYes (Johnson/Top/H0/Walk/Reach.lean) unfolds it to this.
CALLED: back_of · back_numbers (Johnson/IMR/BackSeat.lean) · seal_seated (Johnson/IMR/SealSeat.lean) · yes_alone (Johnson/IMR/SeatForm.lean) · step_inv (Johnson/Desc/K15/FoldInv.lean) · chainEnd_decide_iff (Johnson/Desc/ChainEndExact.lean).

  at_354    the proximity test at the first chain's finish: K12.atFinish (H2U.p12OfMade Z.made)'s own decision accepts from s to s' · no mark behind · the reply as it was.
  at_355    K13's batching: K13.atM3 (K13.whereOf Z)'s. The like.
  at_356    W's commitment: K13.atM4 (K13.whereOf Z) w's, w := K13.wBlock Z's value. The like.
  at_357    the seal: s' = s.

What is not claimed. Number 353 (K2's finish: other files' to show). Nothing on what these decisions do. No soundness.
-/
import Johnson.IMR.SealSeat
import Johnson.Desc.K15.FoldInv
import Johnson.Desc.ChainEndExact

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open VerifiableInference.Desc (Block Chain FileDescription Place KindName OpenedColumn)
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- A step's accepting at Chain.blocksInOrder's «bare» of a sub-protocol that stands alone, brought down to the lot's own decision. (Nearest kin: step_alone, Johnson/IMR/SeatForm.lean: the same at the step, without «bare»; Yes.alone, Johnson/IMR/GrownSeated.lean.) -/
theorem bare_alone_yes {b b' : Block S Cl} {name : String} {a : Place}
    (h : LaidAlone ProofFile.sameReply b b' name a) (hk : a.kind ≠ KindName.K7) {ft : ℕ} {s s' : S}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} {n : ℕ}
    (hy : ({ b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter } : Block S Cl).step ft s rs cols = .ok (s', n)) :
    (∃ rs' gs, b'.decide s rs' gs = .ok s') ∧ s'.failed = none ∧ ProofFile.sameReply s s' = true := by
  obtain ⟨-, -, -, hd⟩ := VerifiableInference.Desc.step_inv ft _ s s' rs cols n hy
  obtain ⟨h1, h2, h3⟩ := (yes_alone h hk s s' _ _).1 hd
  exact ⟨⟨_, _, h1⟩, h2, h3⟩

theorem at_354 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {b : Block S Cl}
    (hb : c.blocksInOrder[354]? = some b) {ft : ℕ} {s s' : S} {rs : List Fmt.RoundView} {cols : List OpenedColumn} {n : ℕ}
    (hy : b.step ft s rs cols = .ok (s', n)) :
    (∃ rs' gs, (VerifiableInference.Desc.K12.atFinish (H2U.p12OfMade Z.made) :
      Block S Unit).decide s rs' gs = .ok s') ∧ s'.failed = none ∧
      ProofFile.sameReply s s' = true := by
  obtain ⟨-, ⟨b1, b1', e1, -, rfl, hla⟩, -, -⟩ := back_of O
  obtain rfl := Option.some.inj (((back_numbers hS hR O).1 1 b1 e1).symm.trans hb)
  exact bare_alone_yes hla (by decide) hy

theorem at_355 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {b : Block S Cl}
    (hb : c.blocksInOrder[355]? = some b) {ft : ℕ} {s s' : S} {rs : List Fmt.RoundView} {cols : List OpenedColumn} {n : ℕ}
    (hy : b.step ft s rs cols = .ok (s', n)) :
    (∃ rs' gs, (VerifiableInference.Desc.K13.atM3 (VerifiableInference.Desc.K13.whereOf Z) :
      Block S Unit).decide s rs' gs = .ok s') ∧ s'.failed = none ∧
      ProofFile.sameReply s s' = true := by
  obtain ⟨-, -, ⟨b2, b2', e2, -, rfl, hla⟩, -⟩ := back_of O
  obtain rfl := Option.some.inj (((back_numbers hS hR O).1 2 b2 e2).symm.trans hb)
  exact bare_alone_yes hla (by decide) hy

theorem at_356 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {b : Block S Cl}
    (hb : c.blocksInOrder[356]? = some b) {ft : ℕ} {s s' : S} {rs : List Fmt.RoundView} {cols : List OpenedColumn} {n : ℕ}
    (hy : b.step ft s rs cols = .ok (s', n)) :
    ∃ w, VerifiableInference.Desc.K13.wBlock Z = some w ∧
      (∃ rs' gs, (VerifiableInference.Desc.K13.atM4 (VerifiableInference.Desc.K13.whereOf Z) w :
        Block S Unit).decide s rs' gs = .ok s') ∧ s'.failed = none ∧
      ProofFile.sameReply s s' = true := by
  obtain ⟨-, -, -, ⟨b3, b3', w, e3, -, hw, rfl, hla⟩⟩ := back_of O
  obtain rfl := Option.some.inj (((back_numbers hS hR O).1 3 b3 e3).symm.trans hb)
  exact ⟨w, hw, bare_alone_yes hla (by decide) hy⟩

theorem at_357 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {b : Block S Cl}
    (hb : c.blocksInOrder[357]? = some b) {ft : ℕ} {s s' : S} {rs : List Fmt.RoundView} {cols : List OpenedColumn} {n : ℕ}
    (hy : b.step ft s rs cols = .ok (s', n)) : s' = s := by
  obtain ⟨b', -, rfl, hla⟩ := seal_seated O
  obtain rfl := Option.some.inj ((back_numbers hS hR O).2.symm.trans hb)
  obtain ⟨⟨rs', gs, hd⟩, -, -⟩ := bare_alone_yes hla (by decide) hy
  have hd' : (VerifiableInference.Desc.ChainEnd.chainEnd (Cl := Unit) 1 5 true
      (VerifiableInference.Desc.K13.inFrontOf Z) VerifiableInference.Desc.First.endAsks).decide s rs'
      gs = .ok s' := hd
  exact ((VerifiableInference.Desc.ChainEnd.chainEnd_decide_iff (Cl := Unit) 1 5 true
    (VerifiableInference.Desc.K13.inFrontOf Z) VerifiableInference.Desc.First.endAsks s s' rs'
    gs).1 hd').1

end

end IM

#print axioms IM.at_354
#print axioms IM.at_355
#print axioms IM.at_356
#print axioms IM.at_357
