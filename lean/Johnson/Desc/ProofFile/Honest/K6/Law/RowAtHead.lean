-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/RowAtHead.lean: CONDITIONAL. NOT a law on a distribution of its
own, and NOT general in the public numbers: the sentences of Honest/K6/Law/RowAtMg.lean WITHOUT
THEIR PREMISE "no two members of the chain's list stand at one place": UNDER THE LIBRARY's ONE
HYPOTHESIS AT THE FULL SIZE (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean) that premise is a theorem of
another folder's (`nodupAtFull`, Johnson/Desc/K11/Exchange/NodupAtFull.lean), which is called here.
ONE PREMISE GOES, ANOTHER GROWS: `AtMgA` extends `AtMg`, under which that file's sentences stand, by
four fields.

  `one_at_a_place`   where the places of a list of blocks are pairwise different, two members at one
                     place are one: a line on lists
  `head_seated_at_head`   under that hypothesis alone: every member of the first chain's list at
                          K6's place has the declared rounds and no oracle message: WHAT THE DOOR
                          `headSeated_of_seated` ASKS
  `head_goodAt_at_head`   under it and the Bool on the book at the row's eight addresses:
                          `(headLettered …).goodAt earlier φ cF.blocksInOrder ord chain firstTree fs`, at
                          every `earlier` and every list of falls
  `head_seated_at_files`   under the library's four premises on the three public files
                           (`P5J.head_exists_at_name`, Johnson/P5J/HeadExistsAtName.lean) there are
                           letters at which the hypothesis holds, and with it the second sentence

A THIN FILE APART, because it imports that file of another folder.

Called. `nodupAtFull`: Johnson/Desc/K11/Exchange/NodupAtFull.lean. `head_seated_at_mg`,
`head_goodAt_at_mg`: Honest/K6/Law/RowAtMg.lean. `P5J.head_exists_at_name`:
Johnson/P5J/HeadExistsAtName.lean. OF THE FOLDER Johnson/Goal/ FIVE DEFINITIONS ARE NAMED HERE, all
in the statement of `head_seated_at_files`, because the library's `P5J.head_exists_at_name` is
stated in them: `P5J.At.CondsOwed` (Johnson/Goal/Skeleton/CondsOfLaid.lean), `FlashProve.protocolDataWellFormed`
(Johnson/Goal/Description/Live.lean), `VerifierAndGoals.asDescriptionFiles` (Johnson/Goal/Tie/ReadThruHead.lean),
`VerifierAndGoals.AtTheName.dpZ` (Johnson/Goal/Skeleton/ProofAtName.lean), `FlashProve.theProofRun`
(Johnson/Goal/Description/ProofFold.lean); nothing else of that folder is called.

Limits. THE HYPOTHESIS IS A PREMISE: it stands at the format's second hash function `OnBytes.secondHashFunction` alone,
at the full size alone, in the goals' scope; it is met under the four premises of the last sentence,
which are premises: by that file's own Limits the first three are evaluated true at the full-size
public files (runs, no theorem) and the fourth is other files' to speak of
(Johnson/Goal/Skeleton/CondsOfLaid.lean). The Bool on the book is a premise: this file evaluates it
at no book. At A := False (a field that `headLettered` lays, Honest/K6/Law/GoodRow.lean) `plays` and
`acc` say nothing; `goodAt` here is the rule's form alone. All that the Limits of
Honest/K6/Law/GoodRow.lean and GoodRowSum.lean say holds here. Nothing on any property.
-/
import Johnson.Desc.K11.Exchange.NodupAtFull
import Johnson.Desc.ProofFile.Honest.K6.Law.RowAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Place Claim Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head.Law (workOf)
open Johnson.Desc.First.ForkMerge.Exchange (nodupAtFull)
open ProofFile.Honest.Small

variable {X W₀ Rc Tr : Type} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL. Where the places are pairwise different, two members at one place are one. -/
theorem one_at_a_place {St Cl : Type} {bs : List (Block St Cl)}
    (h : (bs.map (·.place)).Nodup) : ∀ b ∈ bs, ∀ b' ∈ bs, b.place = b'.place → b = b' :=
  fun _ hb _ hb' e => List.inj_on_of_nodup_map h hb hb' e

/-- CONDITIONAL. Every member of the description's first chain at K6's place has the declared rounds
and no oracle message: under the one hypothesis at the full size, and no other premise. -/
theorem head_seated_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ b' ∈ cF.blocksInOrder, b'.place = IM.k6Place →
      b'.rounds = (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))).rounds ∧
      b'.oracles = (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))).rounds.map fun _ => [] :=
  head_seated_at_mg h.toAtMg (one_at_a_place (nodupAtFull Z D r Zp Np cF x h))

/-- CONDITIONAL. **The form that the frame's rule takes, at the description's first chain**: under
the one hypothesis and the Bool on the book. In form alone: see `head_goodAt`. `earlier` is a free
letter: the form stands at every value of it. -/
theorem head_goodAt_at_head {earlier : List (Nat × Nat × List Fmt.DeclaredRound)}
    (φ : Face (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) Inst) (Bk : ProverCoinCounts)
    (wit : Local W₀ Rc Inst Tr → HeadAsk) (ord : List Place) (chain firstTree : Nat)
    (fs : List (Fall S)) (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ((List.range 8).all fun i => noneSpent Bk ⟨IM.k6Place, i⟩) = true) :
    (headLettered (S := S) (Cl := Claim) (X := X) Bk wit
      (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) IM.k6Place).goodAt earlier φ cF.blocksInOrder ord
      chain firstTree fs :=
  head_goodAt_at_mg φ Bk wit ord chain firstTree fs h.toAtMg
    (one_at_a_place (nodupAtFull Z D r Zp Np cF x h)) hB

/-- CONDITIONAL. **The hypothesis can be met**: under the library's four premises on the three
public files there are letters at which it holds; and there the sentence on the seat, with no
premise more. -/
theorem head_seated_at_files (Z : VerifierAndGoals.PublicFiles) {pp : Inst.Model.ScalesAndPolicy}
    (scope : VerifierAndGoals.InScope Z = true) (read : VerifierAndGoals.readFiles Z = .ok pp)
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) (owed : P5J.At.CondsOwed Z) :
    ∃ (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain P5J.TS ProofFile.Cl)
      (x : VerifiableInference.Desc.First.Look.Place),
      P5J.AtMgA OnBytes.secondHashFunction Z (VerifierAndGoals.AtTheName.dpZ Z)
        (FlashProve.theProofRun (VerifierAndGoals.asDescriptionFiles Z)) Zp Np cF x ∧
      ∀ b' ∈ cF.blocksInOrder, b'.place = IM.k6Place →
        b'.rounds = (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))).rounds ∧
        b'.oracles =
          (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))).rounds.map fun _ => [] := by
  obtain ⟨Zp, Np, cF, x, h⟩ := P5J.head_exists_at_name Z scope read hl owed
  exact ⟨Zp, Np, cF, x, h, head_seated_at_head h⟩

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.one_at_a_place
#print axioms ProofFile.Honest.K6.head_seated_at_head
#print axioms ProofFile.Honest.K6.head_goodAt_at_head
#print axioms ProofFile.Honest.K6.head_seated_at_files
