-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5KindOfPads.lean: kind K5: **THE KIND's NAMED CONDITION, AND SO THE KIND's SHARE IN THE FORM AtMgA.Kind (Johnson/P5J/RowsAtAll.lean), FROM THE HEAD AND THE ONE SENTENCE pads.** A joining: calls. It turns nothing of the condition (K5CondAt,
Door/Law/K5LeftOfCond.lean) or of the theorem k05_kind_of_cond (Door/Law/K05KindOfCond.lean).
Against Door/Law/K5KindOfHead.lean: the 36 Bools without a letter fall: seatsAllW_true | shapesAllW_true | tieWW_true (Door/Law/K5WrittenTrue.lean) say that they are true: closed facts on the written values, which Lean's kernel has walked
(Door/Law/K5PlansFTrue.lean | K5TieFTrue.lean, with their negative tests there).
WHERE THE CONDITION's NINE SENTENCES THEN COME FROM: fence · oneShape (Door/Law/K5HeadPaid.lean) · sent · someMem (Door/Law/K5SentOfK3.lean) · one (Door/Law/K5OneOfHead.lean) · seatsPlan · shapesPlan (Door/Law/K5WrittenPlans.lean with K5WrittenTrue.lean) · tie
(Door/Law/K5NamesTie.lean | K5TieOfNames.lean | K5TieWritten.lean | K5TieWitness.lean with K5WrittenTrue.lean): each from the head; pads: asked here as it stands.
Compiled with the whole library.

(Where this and lean/THEOREM.md differ, the page holds.)
ONLY WHERE THE LIST OF Johnson/Desc/Laid/ProofAsks.lean HAS THE THIRTEEN TESTS OF ProofAsksFirstThirteenTests.lean AND THE HEAD OF Johnson/P5J/MgAtAll.lean HAS THE FIELDS opts · k3.

Main names:
  k5PlansB₂_true: k5PlansB₂ = true. Nothing is evaluated here.
  **k5CondAt_of_pads**: the head · the listed seats are L · pads → K5CondAt h L.
  **k05_kind_of_pads**: the head · the three equations on 𝔏 · pads → h.Kind 𝔏 .K5. Whoever proves pads from the head calls this.
  k05_kind_of_offC: the same with pads from the named test offC (AtMg.offC, HidBearsAtMg.lean).
IS IT EMPTY HERE? IMPLICATIONS FROM THE HEAD. A MEMBER OF THE HEAD IS PROVED AT storedPublicFiles AND zGap ALONE (AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/). THE CLOSED FACTS ARE SENTENCES ON WRITTEN VALUES: the head's own entry tests tie these to the public files. THE KIND's LAW IS NOT PROVED.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5KindOfHead
import Johnson.Desc.First.Att.Door.Law.K5WrittenTrue

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

/-- The Bool at the written values that Door/Law/K5CondOfHead.lean leaves is true. -/
theorem k5PlansB₂_true : k5PlansB₂ = true := by
  unfold k5PlansB₂
  refine List.all_eq_true.2 fun g hg => ?_
  rw [Bool.and_eq_true]
  exact ⟨seatsAllW_true (List.mem_range.1 hg), shapesAllW_true (List.mem_range.1 hg)⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- **THE KIND's NAMED CONDITION, FROM THE HEAD AND pads.** -/
theorem k5CondAt_of_pads {L : Laid} (hL : P5J.At.laid? Zp = some L) (pads : PadsAll h) : K5CondAt h L :=
  k5CondAt_of_head₂ hL k5PlansB₂_true pads (cells_of_tie h fun _ hg => tieWW_true hg)

variable (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
  (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁) (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
  (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
include q₁ q₂ q₃

/-- **THE KIND's SHARE IN THE FORM AtMgA.Kind (RowsAtAll.lean), FROM THE HEAD AND pads.** -/
theorem k05_kind_of_pads (pads : PadsAll h) : h.Kind 𝔏 KindName.K5 :=
  k05_kind_of_head₃ h 𝔏 q₁ q₂ q₃ k5PlansB₂_true (fun _ hg => tieWW_true hg) pads

/-- The same with pads from the named test offC (Johnson/P5J/HidBearsAtMg.lean). -/
theorem k05_kind_of_offC (hC : h.toAtMg.offC = true) : h.Kind 𝔏 KindName.K5 :=
  k05_kind_of_pads h 𝔏 q₁ q₂ q₃ (pads_of_offC h hC)

end H2K5.Door

#print axioms H2K5.Door.k5PlansB₂_true
#print axioms H2K5.Door.k5CondAt_of_pads
#print axioms H2K5.Door.k05_kind_of_pads
#print axioms H2K5.Door.k05_kind_of_offC
