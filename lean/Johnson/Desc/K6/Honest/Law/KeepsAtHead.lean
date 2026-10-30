-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K6/Honest/Law/KeepsAtHead.lean: the three premises' forms of Honest/Law/KeepsForm.lean
(`K6Place`; the library's `K5Book` and `BlindOrder`) AT THE LETTERS OF THE FULL SIZE's TABLE OF
JOINTS: its written lists of segments and places, its numbers, and any filling whose two letters
"held" and "in order" are the closed filling's. CALLS AND TIES: no new mathematics.

  `plK6`, `plK6'`        the sub-protocol's place and the next
  `k6Place_at`           the five facts on the index: one by the kernel (decide +kernel), at the
                         written list of segments
  `k6_at341`, `k6_at342`  the two places stand at the numbers 341 and 342 of the written list
  `k6Book_at`            CONDITIONAL: the two facts on the table's numbers
  `blindOrder_at`        CONDITIONAL: the two letters do not read where the chain stands

What is called. `place341_full`, `place342_full` (Johnson/Desc/Sound/AtDriver.lean); that the
table's two numbers stay from 341 to 342 (`P5J.numbers_at_name`,
Johnson/HB/LLHARD/K6NumbersAtName.lean: in the goals' scope, where the value is laid); what "in
order" is over the closed base (`mgAll_inOrder_base`, Johnson/Desc/Sound/MgBase.lean).

A relative of `blindOrder_at`: `blindOrder_sig` (Johnson/Desc/Sound/K6AtSig.lean: at another
filling, under a premise on "in order").

Limits. THE FULL SIZE ALONE. `k6Book_at` and `blindOrder_at` stand under the hypothesis that ties
the letters to the IOP as written in Lean, which is not shown here: the library has it under four
premises (`P5J.head_exists_at_name`, Johnson/P5J/HeadExistsAtName.lean), of which, by that file's
own limits, three are evaluated true at the release's full-size files (runs, no theorem) and the
fourth that file leaves to others. Modules under lean/Johnson/Goal/ are among what this
file imports: it imports no module of that folder by name and calls nothing that is declared there:
they lie beneath the library's files that it calls. Nothing on any property.

-/
import Johnson.Desc.K6.Honest.Law.KeepsForm
import Johnson.HB.LLHARD.K6NumbersAtName
import Johnson.Desc.Sound.AtDriver
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Honest
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Wit)
open VerifiableInference.Desc.First (Meaning)
open VerifiableInference.Desc.First.Att.P (K5Book)
open VerifiableInference.Desc.Sound (MsgT BlindOrder mgAll_inOrder_base)
open P5J (AtMg AtMgA mgAtAll TS)

/-- The sub-protocol's place. -/
abbrev plK6 : Place := ⟨1, some 24, 4, .K6⟩

/-- The next place. -/
abbrev plK6' : Place := ⟨1, some 24, 5, .K1⟩

/-- **The five facts on the index.** -/
theorem k6Place_at : K6Place P5J.At.links 24 plK6 plK6' :=
  ⟨rfl, rfl, by decide +kernel, rfl, rfl⟩

/-- The sub-protocol's place stands at the number 341 of the written list of places. -/
theorem k6_at341 : P5J.At.ps[341]? = some plK6 := Sound.place341_full

/-- The next place stands at the number 342. -/
theorem k6_at342 : P5J.At.ps[341 + 1]? = some plK6' := Sound.place342_full

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl}

/-- **The two facts on the table's numbers.** CONDITIONAL: the hypothesis that ties the letters to
the IOP as written in Lean. -/
theorem k6Book_at (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) :
    K5Book (P5J.At.N Zp cF) plK6 plK6' := by
  have e := P5J.numbers_at_name h.scope h.laid
  rw [Sound.place341_full, show (341 + 1 : Nat) = 342 from rfl, Sound.place342_full] at e
  exact ⟨e.1, e.2⟩

variable {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- **The two letters do not read where the chain stands**, at a filling whose two letters are the
closed filling's. CONDITIONAL: the hypothesis that ties the letters to the IOP as written in Lean,
and these two equations. -/
theorem blindOrder_at {Cells Tok : Type} (Mg : Meaning ProofFile.InstPub (Wit Cells Tok MsgT))
    (hheld : Mg.held = (mgAtAll h).held) (hin : Mg.inOrder = (mgAtAll h).inOrder) :
    BlindOrder Mg :=
  ⟨fun z s h' => by
      rw [hin]
      exact (mgAll_inOrder_base h.𝔇 _).trans (mgAll_inOrder_base h.𝔇 _).symm,
    fun j t z s h' => by
      rw [hheld]
      rfl⟩

end

end VerifiableInference.Desc.Kinds.Head.Honest

#print axioms VerifiableInference.Desc.Kinds.Head.Honest.k6Place_at
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.k6_at341
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.k6_at342
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.k6Book_at
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.blindOrder_at
