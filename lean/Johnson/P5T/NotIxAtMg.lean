-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5T/NotIxAtMg.lean: AT THE HEAD `AtMg`: THE CLOSED TEST `ownNotIndexB`
(Johnson/Desc/First/Link/Law/FifthTieLow.lean) ACCEPTS AT THE CONSTANT's DATA AND NUMBERS, AT EACH
OF THE 25 SEGMENTS AND EVERY MOMENT. It is what is left, beside the facts along the fold, of the
field notIx of the condition of the kind K9 (`notIx_of`,
Johnson/Desc/First/Link/Law/NotIxOf.lean). Six theorems. A joining: the evaluation is
Johnson/P5T/NotIxFull.lean's.
  `LaidAt.told_cut`, `LaidAt.msgs`, `LaidAt.indexNo`: in scope, where the value is laid, the
  table's count of messages by place and the index masks' number are the written ones. (As
  `LaidAt.trees`, Johnson/P5T/LowAtMg.lean: `withTold` lays all three off what the sub-protocols
  tell, and row 10 pins that.)
  `ownAt_msgs`: `ownAt` reads the numbers by `msgsAt` alone.
  `AtMg.own_is`: `ownAt` is the written one.
  `AtMg.notIx`: **`ownNotIndexB (At.foldD Zp cF Ld) m t (At.N Zp cF).indexNo = true`** at every
  Ld, every m below 25, EVERY t: so at whatever moment a caller computes.
How the shape is had: `AtMg.shape_full` (Johnson/P5J/ShapeFullAtMg.lean).
Limits. Over the verifier's list of thirteen entry tests (Johnson/Desc/Laid/ProofAsksFirstThirteenTests.lean)
alone. The full size alone. No probability: no soundness follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5T.NotIxFull
import Johnson.P5T.LowAtMg
import Johnson.P5J.ShapeFullAtMg
import Johnson.P5J.FoldAt
import Johnson.Desc.First.Link.Law.FifthTieLow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open OnBytes OnBytes.Model
open VerifiableInference
open VerifiableInference.Desc (Chain Place)
open VerifiableInference.Desc.First (Numbers ModelPart placesCut toldCut placesCut_is told_at_written
  msgsTold msgNoOf borderOf flatPlacesOf)
open VerifiableInference.Desc.First.FillSent (ownAt sentDataAt sentData1At baseAt base1At base2At)
open VerifiableInference.Desc.Sound (linksFull)
open VerifiableInference.Desc.LinkJoin (ownNotIndexB)
open VerifiableInference.Desc.ReqLit (shapeFull)
open OnBytes.Maker (WholeD)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- What the first chain's sub-protocols tell is the written list. -/
theorem LaidAt.told_cut (L : LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF)
    (hW : VerifierAndGoals.InScope Z = true) : At.told cF = toldCut := by
  rw [At.told_is]
  exact (told_at_written (pins_of_laid hW L).2).2

/-- In scope, where the value is laid, the table's count of messages is the written one's. -/
theorem LaidAt.msgs (L : LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF)
    (hW : VerifierAndGoals.InScope Z = true) : (At.N Zp cF).msgsAt = P5T.NFull.msgsAt := by
  funext p
  show msgsTold (At.told cF) (borderOf (flatPlacesOf linksFull true) p) =
    msgsTold toldCut (borderOf placesCut p)
  rw [L.told_cut hW, placesCut_is]

/-- And the index masks' number. -/
theorem LaidAt.indexNo (L : LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF)
    (hW : VerifierAndGoals.InScope Z = true) : (At.N Zp cF).indexNo = P5T.NFull.indexNo := by
  rw [L.N_is hW]
  show msgNoOf (At.told cF) P5T.N0Full.index = msgNoOf toldCut P5T.N0Full.index
  rw [L.told_cut hW]

/-- `ownAt` reads the numbers by `msgsAt` alone. -/
theorem ownAt_msgs (s : Params.ReqShape) {N N' : Numbers} (h : N.msgsAt = N'.msgsAt)
    (links : List ModelPart) (ps : List Place) (b : Array Stages.LinkH) (m j : ℕ) :
    ownAt s N links ps b m j = ownAt s N' links ps b m j := by
  unfold ownAt sentData1At sentDataAt
  have e0 : baseAt N links ps = baseAt N' links ps := by
    funext i
    unfold baseAt
    rw [h]
  have e1 : base1At N links ps = base1At N' links ps := by
    funext i
    unfold base1At
    rw [h]
  have e2 : base2At N links ps = base2At N' links ps := by
    funext i
    unfold base2At
    rw [h]
  rw [e0, e1, e2]

/-- Part 5's own numbers are the written ones. -/
theorem AtMg.own_is (h : AtMg o Z D r Zp Np cF) (Ld : Desc.K12.Door.Laid) (m t : ℕ) :
    (At.foldD Zp cF Ld).ownAt m t = P5T.ownFull m t := by
  show ownAt (At.shape Zp) (At.N Zp cF) At.links At.ps Zp.made.p.built.links m t =
    ownAt shapeFull P5T.NFull At.links At.ps #[] m t
  have es : At.shape Zp = shapeFull := h.shape_full
  rw [es, ownAt_msgs shapeFull (h.laid.msgs h.scope)]
  rfl

/-- **The closed test accepts, at every moment.** -/
theorem AtMg.notIx (h : AtMg o Z D r Zp Np cF) (Ld : Desc.K12.Door.Laid) {m : ℕ} (hm : m < 25)
    (t : ℕ) : ownNotIndexB (At.foldD Zp cF Ld) m t (At.N Zp cF).indexNo = true := by
  unfold ownNotIndexB
  rw [h.own_is Ld m t, h.laid.indexNo h.scope]
  exact P5T.notIx_every hm t

end P5J

#print axioms P5J.LaidAt.told_cut
#print axioms P5J.LaidAt.msgs
#print axioms P5J.LaidAt.indexNo
#print axioms P5J.ownAt_msgs
#print axioms P5J.AtMg.own_is
#print axioms P5J.AtMg.notIx
