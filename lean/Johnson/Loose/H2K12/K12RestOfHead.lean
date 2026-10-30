-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.K12LeftOfRest
import Johnson.Desc.Laid.ProofAsksLaw2
import Johnson.Goal.Numbers.KeyInScope
import Johnson.Desc.Ok.PlanWritten.CutTestLaws
/-
Johnson/Loose/H2K12/K12RestOfHead.lean: THE LAW
OF THE PROXIMITY TEST (the kind K12) ON THE PROOF FILE's FIRST CHAIN, sub-protocol number 354 of the
table's written list: THE TWO PINS OF THE SHORTER LIST OF DEBTS K12Rest₆ (K12LeftOfRest.lean) FROM
THE HEAD over a library whose list of the proof file's entry tests asks them. Three theorems: calls.
  pins_of_head     from the composed meaning's head (AtMgA, Johnson/P5J/MgAtAll.lean) alone:
                   PlanWritten.madeRow Zp = true, and the cut of the first chain's flat list is the
                   written one. The road: the head holds that every entry test of the proof file
                   says yes (its field laid.asks); in scope the key is the full size's
                   (key_in_scope_pure, Johnson/Goal/Numbers/KeyInScope.lean); there two of these
                   tests are the two pins (LPFD.asks_pins, Johnson/Desc/Laid/ProofAsksLaw2.lean), at
                   the head's own description and public part; the cut's test gives the equation
                   (cut_of_row, Johnson/Desc/Ok/PlanWritten/CutTestLaws.lean)
  k12Rest_of_head  K12Rest₆ from the head, the head with the facts on every reached state (AtMgR)
                   and THREE PREMISES, BY NAME: heads, radius, clear: K12Rest₆'s own fields, to the
                   letter; their docstrings stand there
  k12_kind_of_head the same premises: then LastTypedAt → h.Kind 𝔏 K12
WHAT IS LEFT OF K12's NAMED CONDITION BEHIND THIS FILE, ONE BY ONE: heads (an equation on the
letter 𝔏); AtMgR at the condition of the counted form (the composed meaning's laying returns
L; its whole structure of facts on reached states, unpaid here, of which seven clauses are
spent); radius (a closed fact on one radius); clear (a closed test on the table's numbers).
NEAREST KIN, DECLARED: P5J.AtMg.pins and P5J.AtMg.cut_written
(Johnson/P5J/NumbersAtHead.lean) are pins_of_head's two halves, by the same
three calls, at P5J.AtMg. They are not called here: that file imports nine modules, of which
these calls need two.
WHAT IT IS NOT. A JOINING: IT PAYS NO LAW. It stands only over a library in which lawsAsk
(Johnson/Desc/Laid/ProofAsks.lean) asks the two tests.
That the entry tests accept says that the made sizes, the sendings and the cut ARE the written ones
at these files; the written cut itself rests on prints of Lean's evaluator
(Johnson/Desc/First/CutWritten.lean, by its own head). No example. The full size alone.
No soundness statement. Nothing on hiding.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace H2K12

open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Slice
open VerifiableInference.Desc (KindName)
open P5J (AtMgA AtMgR F0T TS Free fullLinks)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **BOTH PINS FROM THE HEAD.** -/
theorem pins_of_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    VerifiableInference.PlanWritten.madeRow Zp = true ∧
      VerifiableInference.PlanWritten.cutOf cF.blocksInOrder =
        VerifiableInference.PlanWritten.cutFirstFull := by
  have hk : VerifiableInference.Desc.Door.atFullKey Zp = true :=
    decide_eq_true (VerifiableInference.PlanWritten.key_in_scope_pure h.scope h.laid.pub)
  obtain ⟨hm, hc⟩ := LPFD.asks_pins h.laid.asks h.laid.pub hk
  exact ⟨hm, (VerifiableInference.PlanWritten.cut_of_row hc).1⟩

/-- **THE SHORTER LIST OF DEBTS, FROM THE HEAD AND THREE PREMISES.** -/
theorem k12Rest_of_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    {L : VerifiableInference.Desc.K12.Door.Laid}
    (R : AtMgR OnBytes.secondHashFunction Z D r Zp Np cF h.toAtMg.rch (fun a => a.1) L)
    (heads : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (radius : ∀ R', Johnson.G.sendRowsOf Z.pol Z.lay Z.KL = .ok R' → P5T.rad? R' 75 0 =
      (((((Johnson.G.packFullLit.drop 24).take 82).map (·.2))[75]?).bind (·[0]?)).map (·.2))
    (clear : Rid354.clearB h.𝔇.arr (P5J.At.N Zp cF) fullLinks P5J.At.ps 354 = true) :
    K12Rest₆ h 𝔏 L :=
  ⟨heads, R, (pins_of_head h).1, (pins_of_head h).2, radius, clear⟩

/-- **THE KIND's LAW IN THE COUNTED FORM, FROM THE HEAD AND THREE PREMISES.** -/
theorem k12_kind_of_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    {L : VerifiableInference.Desc.K12.Door.Laid}
    (R : AtMgR OnBytes.secondHashFunction Z D r Zp Np cF h.toAtMg.rch (fun a => a.1) L)
    (heads : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (radius : ∀ R', Johnson.G.sendRowsOf Z.pol Z.lay Z.KL = .ok R' → P5T.rad? R' 75 0 =
      (((((Johnson.G.packFullLit.drop 24).take 82).map (·.2))[75]?).bind (·[0]?)).map (·.2))
    (clear : Rid354.clearB h.𝔇.arr (P5J.At.N Zp cF) fullLinks P5J.At.ps 354 = true) :
    LastTypedAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL → h.Kind 𝔏 KindName.K12 :=
  k12_kind_of_rest (k12Rest_of_head h 𝔏 R heads radius clear)

end H2K12

#print axioms H2K12.pins_of_head
#print axioms H2K12.k12Rest_of_head
#print axioms H2K12.k12_kind_of_head
