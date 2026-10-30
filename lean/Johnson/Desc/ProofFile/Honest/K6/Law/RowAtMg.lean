-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/RowAtMg.lean: CONDITIONAL, THREE TIMES OVER. NOT a law on a
distribution of its own, and NOT general in the public numbers: `Lettered.goodAt` for the row of the
sub-protocol "the output head's own rounds" AT THE FIRST CHAIN OF THE DESCRIPTION, as far as this
file has it: under (1) the premises of a counted statement (`P5J.AtMg`): THEY STAND AT THE FORMAT's
EARLIER HASH `OnBytes.secondHashFunction` ALONE, AT THE FULL SIZE ALONE, IN THE GOALS' SCOPE; THEY ARE MET UNDER
FOUR PREMISES ON THE THREE PUBLIC FILES (the library's `P5J.head_exists_at_name`,
Johnson/P5J/HeadExistsAtName.lean: in scope; `readFiles` returns; the verifier's own three values
are laid; `At.CondsOwed Z`), of which by that file's own Limits the first three are evaluated true
at the full-size public files (runs, no theorem) and the fourth is other files' to speak of
(Johnson/Goal/Skeleton/CondsOfLaid.lean); of (1) Johnson/Desc/Kinds/Law/K6WayUpAtSeat.lean has that
the chain's member number 341 has the form `K6MemberIs`; (2) that no two members of the chain's list
stand at one place; (3) the Bool on the book at the row's eight addresses.

  `head_seated_at_mg`   under (1) and (2): every member of the chain's list at K6's place has the
                        declared rounds and no oracle message: WHAT THE DOOR `headSeated_of_seated`
                        ASKS
  `head_goodAt_at_mg`   under all three:
                        `(headLettered …).goodAt earlier φ cF.blocksInOrder ord chain firstTree fs`, at every
                        `earlier` and every list of falls
  `head_seated_at_name`   under these four premises on the public files there are letters at which
                          (1) holds, and with it the first sentence (that second clause adds nothing
                          to `head_seated_at_mg`): so (1) is met wherever these four are

A FILE OF ITS OWN: what it imports has well over a hundred modules of the library's goals
(Johnson/Goal/) in its closure.

Called. `P4.k6_member_at_mg`: Johnson/Desc/Kinds/Law/K6WayUpAtSeat.lean. `P5J.head_exists_at_name`:
Johnson/P5J/HeadExistsAtName.lean. The masked sumcheck's law, another folder's, through
Honest/K6/Law/GoodRowSum.lean. OF THE FOLDER Johnson/Goal/ FIVE DEFINITIONS ARE NAMED HERE, all in
the statement of `head_seated_at_name`, because the library's `P5J.head_exists_at_name` is stated in
them: `P5J.At.CondsOwed` (Johnson/Goal/Skeleton/CondsOfLaid.lean), `FlashProve.protocolDataWellFormed`
(Johnson/Goal/Description/Live.lean), `VerifierAndGoals.asDescriptionFiles` (Johnson/Goal/Tie/ReadThruHead.lean),
`VerifierAndGoals.AtTheName.dpZ` (Johnson/Goal/Skeleton/ProofAtName.lean), `FlashProve.theProofRun`
(Johnson/Goal/Description/ProofFold.lean); nothing else of that folder is called.

Limits. The four premises of `head_seated_at_name` are premises. (2) is a named premise: the
description's own test on places is meant to give it; nothing here calls that test. A CHEAPER PAYER
OF WHAT `head_seated_at_mg` GIVES, without (1) and (2): the seat's test with code (`headSeatB`,
Honest/K6/Law/Row.lean), evaluated at a description's own list: this file does not evaluate it. At A
:= False (a field that `headLettered` lays, Honest/K6/Law/GoodRow.lean) `plays` and `acc` say
nothing. All that the Limits of Honest/K6/Law/GoodRow.lean and GoodRowSum.lean say holds here.
Nothing on any property.
-/
import Johnson.Desc.Kinds.Law.K6WayUpAtSeat
import Johnson.P5J.HeadExistsAtName
import Johnson.Desc.ProofFile.Honest.K6.Law.GoodRowSum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Place Claim Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head.Law (K6MemberIs workOf)
open ProofFile.Honest.Small

variable {X W₀ Rc Tr : Type} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- CONDITIONAL. Every member of the description's first chain at K6's place has the declared rounds
and no oracle message. -/
theorem head_seated_at_mg (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    (hu : ∀ b ∈ cF.blocksInOrder, ∀ b' ∈ cF.blocksInOrder, b.place = b'.place → b = b') :
    ∀ b' ∈ cF.blocksInOrder, b'.place = IM.k6Place →
      b'.rounds = (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))).rounds ∧
      b'.oracles = (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))).rounds.map fun _ => [] := by
  obtain ⟨b, e, M⟩ := P4.k6_member_at_mg h
  exact members_at_of_member M fun b' hb' hp =>
    hu b' hb' b (List.mem_of_getElem? e) (hp.trans (member_is M).1.symm)

/-- CONDITIONAL. **The premises of a counted statement can be met**: under the library's four
premises on the three public files there are letters at which they hold; and there the sentence
above. -/
theorem head_seated_at_name (Z : VerifierAndGoals.PublicFiles) {pp : Inst.Model.ScalesAndPolicy}
    (scope : VerifierAndGoals.InScope Z = true) (read : VerifierAndGoals.readFiles Z = .ok pp)
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) (owed : P5J.At.CondsOwed Z) :
    ∃ (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain P5J.TS ProofFile.Cl),
      P5J.AtMg OnBytes.secondHashFunction Z (VerifierAndGoals.AtTheName.dpZ Z)
        (FlashProve.theProofRun (VerifierAndGoals.asDescriptionFiles Z)) Zp Np cF ∧
      ((∀ b ∈ cF.blocksInOrder, ∀ b' ∈ cF.blocksInOrder, b.place = b'.place → b = b') →
        ∀ b' ∈ cF.blocksInOrder, b'.place = IM.k6Place →
          b'.rounds = (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))).rounds ∧
          b'.oracles =
            (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))).rounds.map fun _ => []) := by
  obtain ⟨Zp, Np, cF, _, h⟩ := P5J.head_exists_at_name Z scope read hl owed
  exact ⟨Zp, Np, cF, h.toAtMg, head_seated_at_mg h.toAtMg⟩

/-- CONDITIONAL, on h, hu and the Bool on the book hB. **The form that the frame's rule takes, at
the description's first chain.** In form alone: see `head_goodAt` (Honest/K6/Law/GoodRow.lean).
`earlier` is a free letter: the form stands at every value of it. -/
theorem head_goodAt_at_mg {earlier : List (Nat × Nat × List Fmt.DeclaredRound)}
    (φ : Face (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) Inst) (Bk : ProverCoinCounts)
    (wit : Local W₀ Rc Inst Tr → HeadAsk) (ord : List Place) (chain firstTree : Nat)
    (fs : List (Fall S)) (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    (hu : ∀ b ∈ cF.blocksInOrder, ∀ b' ∈ cF.blocksInOrder, b.place = b'.place → b = b')
    (hB : ((List.range 8).all fun i => noneSpent Bk ⟨IM.k6Place, i⟩) = true) :
    (headLettered (S := S) (Cl := Claim) (X := X) Bk wit
      (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) IM.k6Place).goodAt earlier φ cF.blocksInOrder ord
      chain firstTree fs :=
  head_goodAt_all φ Bk wit _ IM.k6Place cF.blocksInOrder ord chain firstTree fs (head_seated_at_mg h hu) hB

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.head_seated_at_mg
#print axioms ProofFile.Honest.K6.head_seated_at_name
#print axioms ProofFile.Honest.K6.head_goodAt_at_mg
