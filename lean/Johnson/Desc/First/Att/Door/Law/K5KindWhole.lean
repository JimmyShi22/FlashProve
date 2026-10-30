-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5KindWhole.lean: kind K5: **THE KIND's NAMED CONDITION AND THE KIND's SHARE IN THE FORM AtMgA.Kind (Johnson/P5J/RowsAtAll.lean) FROM THE HEAD ALONE; AND SO THE TWO SENTENCES OVER ALL HEADS, K05Cond AND K05LawR, WITHOUT A PREMISE.** A joining: four calls. It
turns nothing of the condition (K5CondAt · K05Cond, Door/Law/K5LeftOfCond.lean), of the law's sentence (K05LawR, Door/Law/K05LawR.lean) or of the theorem k05_kind_of_cond (Door/Law/K05KindOfCond.lean).
READ THIS FIRST. (1) A caution: "FROM THE HEAD (OVER THE THIRTEEN-ROW LIST OF ENTRY TESTS)": THE PINS ARE MOVED INTO THE HEAD's FIELD "laid", NOT SHOWN; `lawsAsk` asks both, as rows 9 and 10. (2) K05Cond AND K05LawR ARE
SENTENCES "FOR ALL HEADS": WHERE NO HEAD EXISTS THEY SAY NOTHING. A MEMBER OF THE HEAD IS PROVED AT storedPublicFiles AND zGap ALONE (AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/). (A run evaluated each of the head's fields true at three public files: a run, no theorem.)
Against Door/Law/K5KindOfPads.lean: the one sentence pads falls: pads_of_head (Door/Law/K5PadsOfHead.lean) gives it from the head, over offC_head (Johnson/Top/H0/K2Ties/OffHead.lean).
WHAT "FROM THE HEAD" LEANS ON. (a) THE HEAD AtMgA (Johnson/P5J/MgAtAll.lean) IS A HYPOTHESIS: it holds the goals' scope, "the verifier's own value is laid" with every entry test's accept (the two comparisons with written values among them: (1) above), and
tests on the public part. (b) The closed facts beneath (on the fence, the seats, the plans' tests, the ties, the numbers, the pads) are sentences on WRITTEN values, which Lean's kernel has walked in their own files; the head's entry tests tie the written
values to the public files; that the written values are what the makers give is no theorem. (c) The seven facts along "reached" rest on the induction along the run (Johnson/P5J/FoldJ3Whole.lean) and on the call of it in another file
(Johnson/Loose/H2K12/ReachedOfPins.lean). (d) At the second hash function alone; the full size alone.
Compiled with the whole library.
(Where this and lean/THEOREM.md differ, the page holds.)

ONLY WHERE THE LIST OF Johnson/Desc/Laid/ProofAsks.lean HAS THE THIRTEEN TESTS OF ProofAsksFirstThirteenTests.lean AND THE HEAD OF Johnson/P5J/MgAtAll.lean HAS THE FIELDS opts · k3.

Main names:
  **k5CondAt_at_head**: the head · the listed seats are L → K5CondAt h L.
  **k05_kind_of_head**: the head · the three equations on the letter 𝔏 → h.Kind 𝔏 .K5.
  **k05Cond_holds : K05Cond**: the named condition over all heads. No binder. (Its premise K5Along is not spent.)
  **k05LawR_holds : K05LawR**: the kind's law in the counted form, at the picked condition. No binder. By k05LawR_of_cond (Door/Law/K5LeftOfCond.lean).
IS IT EMPTY HERE? EVERY ONE IS AN IMPLICATION FROM THE HEAD, OR A SENTENCE OVER ALL HEADS. A MEMBER OF THE HEAD IS PROVED AT storedPublicFiles AND zGap ALONE (AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/).
Nothing is claimed on soundness, completeness or hiding: the kind's law is one premise of a statement on the whole verifier, not that statement.

-/
import Johnson.Desc.First.Att.Door.Law.K5KindOfPads
import Johnson.Desc.First.Att.Door.Law.K5PadsOfHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace H2K5.Door
open OnBytes OnBytes.Flat OnBytes.Model OnBytes.Maker OnBytes.Slice KObj
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Door (Laid)
open P5J (AtMg AtMgA F0T TS Free)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- **THE KIND's NAMED CONDITION, FROM THE HEAD ALONE.** -/
theorem k5CondAt_at_head {L : Laid} (hL : P5J.At.laid? Zp = some L) : K5CondAt h L :=
  k5CondAt_of_pads h hL (pads_of_head h)

variable (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
  (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁) (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
  (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
include q₁ q₂ q₃

/-- **THE KIND's SHARE IN THE FORM AtMgA.Kind (RowsAtAll.lean), FROM THE HEAD ALONE.** -/
theorem k05_kind_of_head : h.Kind 𝔏 KindName.K5 :=
  k05_kind_of_pads h 𝔏 q₁ q₂ q₃ (pads_of_head h)

end

/-- **THE NAMED CONDITION OVER ALL HEADS.** -/
theorem k05Cond_holds : K05Cond := fun _ _ _ _ _ _ _ h _ hL _ => k5CondAt_at_head h hL

/-- **THE KIND's LAW IN THE COUNTED FORM, AT THE PICKED CONDITION.** -/
theorem k05LawR_holds : K05LawR := k05LawR_of_cond k05Cond_holds

end H2K5.Door

#print axioms H2K5.Door.k5CondAt_at_head
#print axioms H2K5.Door.k05_kind_of_head
#print axioms H2K5.Door.k05Cond_holds
#print axioms H2K5.Door.k05LawR_holds
