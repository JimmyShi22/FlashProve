-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Lines/Layers/BatchedSumcheckSlots.lean: from a return of the hearing of the
layers' own rounds: which slots the three long forms of the batched sumcheck name. K.fin.Alin and
K.fin.Blin name none (the library's stack_fin). K.rowS names its own window, then those of its start
form: the slot of the second token sumcheck's claimed sum, those of the lookup's end form and those
of KT. KT names that sumcheck's window and the same slot. General; nothing is evaluated.

Why. OwnRecordClosedForm.lean keeps these forms' slots and needs them as functions of the plan. The
proofs call the library's hearStack_tape, joinStart_startOf, hearTerms_calls, tscIn_spec,
pscRow_spec, endP_spec, join_no_slot and slots_nil (Johnson/Desc/First/K4/Returns/JoinSlots.lean),
and win_len.

  weightedFold_addsNoSlots   forms that name no slot, added under weights, add no slot.
  batchedStart_slots      the slots of the batched sumcheck's start form.
  endForms_nameNoSlots    the two end forms name no slot.
  secondTokenForm_slots   what KT names.
  **batchedRow_slots**    what the batched sumcheck's row K.rowS names.

Limits. Slots alone: nothing on the forms' entries. From a return alone: that the hearing returns is
not said here. What any of this costs Lean's kernel is not measured here. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.Lines.Layers.HearingMovesShapes
import OnBytes.Desc.First.K4.StackTape
import Johnson.Road.K4.JoinTie
import Johnson.Road.K4.Slots.FillsMore
import Johnson.Desc.First.K4.Returns.JoinSlots
import Johnson.Desc.First.Shape.HearHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Desc.First.K4.Rt
open OnBytes OnBytes.K.Kc
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.Desc.First.P1 (tscIn_spec tscWs pscRow_spec endP_spec plainWs)
open OnBytes.Road (startOf)
open VerifiableInference.Desc.First.Shape

/-- Forms that name no slot, added under weights, add no slot. -/
theorem weightedFold_addsNoSlots (e : Nat → E) : ∀ (l : List Aff) (k : Nat) (a : Aff),
    (∀ x ∈ l, (affSh x).slots = []) →
    (affSh ((l.zipIdx k).foldl (fun (a : Aff) x => a.addMul x.1 (e x.2)) a)).slots = (affSh a).slots
  | [], _, _, _ => rfl
  | x :: l, k, a, h => by
    rw [List.zipIdx_cons, List.foldl_cons,
      weightedFold_addsNoSlots e l (k + 1) _ fun y hy => h y (List.mem_cons_of_mem _ hy),
          affSh_addMul]
    show (affSh a).slots ++ (affSh x).slots = _
    rw [h x List.mem_cons_self, List.append_nil]

/-- The slots of the batched sumcheck's start form. -/
theorem batchedStart_slots {H : Heard} {om : Array E} {parts : List Aff} {tT : Tsc}
    (hT : H.tT = some tT) (hp : ∀ a ∈ parts, (affSh a).slots = []) :
    (affSh (startOf H om parts)).slots =
      tT.sCl :: (affSh H.fo.cEnd).slots ++ (affSh H.KT).slots := by
  unfold startOf
  rw [hT]
  dsimp only
  rw [if_pos (show (some tT).isSome = true from rfl), affSh_addMul, affSh_sub, affSh_sub, affSh_add]
  show ((((affSh _).slots ++ []) ++ [tT.sCl]) ++ (affSh H.fo.cEnd).slots) ++ (affSh H.KT).slots = _
  rw [weightedFold_addsNoSlots (fun i => H.fo.e.getD i zeroE) parts 0 aff0 hp]
  rfl

variable {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {F G : Fork} {t u : Tape} {o : Own}

/-- The two end forms name no slot. -/
theorem endForms_nameNoSlots (hh : hearFl P hp g fo F t = some (o, G, u)) :
    (affSh o.K.fin.Alin).slots = [] ∧ (affSh o.K.fin.Blin).slots = [] := by
  obtain ⟨-, -, -, -, H1, hd2, cl, G1, G2, G3, G4, G5, u1, u2, u3, u4, u5, -, -, h3, -⟩ :=
    hear_parts hh
  obtain ⟨a, b⟩ := Slots.stack_fin (S := fun _ => False) h3
  exact ⟨slots_nil a, slots_nil b⟩

/-- What KT names: the second token sumcheck's window, then the slot of its claimed sum. -/
theorem secondTokenForm_slots (hh : hearFl P hp g fo F t = some (o, G, u)) :
    ∃ tT, o.H.tT = some tT ∧
      (affSh o.H.KT).slots = List.range' (tT.sCl + 1) (2 * P.y.h.lt + 2) ++ [tT.sCl] := by
  obtain ⟨-, -, -, -, H1, hd2, cl, G1, G2, G3, G4, G5, u1, u2, u3, u4, u5, -, h2, -⟩ :=
    hear_parts hh
  obtain ⟨tT, A1, a1, row, p', c1, -, c2, e⟩ := hearTerms_calls h2
  obtain ⟨rfl, -, -⟩ := pscRow_spec c2
  obtain ⟨a, b⟩ := tokenSumcheck_openShape c1
  obtain ⟨hlt, T, mu0, eps, ms, y, v1, v, G0, -, -, -, -, m1, -, -, -, hv, hr, -⟩ := tscIn_spec c1
  have hz : (H1.ztF.toList.take P.y.h.lt).length = P.y.h.lt := by
    rw [List.length_take, Array.length_toList]
    omega
  have hwl : (tscWs (H1.ztF.toList.take P.y.h.lt)).length = P.y.h.lt := by
    unfold tscWs
    rw [List.length_map, hz]
  have hm : ms.length = (tscWs (H1.ztF.toList.take P.y.h.lt)).length := by
    rw [← m1, List.length_map]
  have hw : tT.p.walk.1.length = 1 + 2 * (tscWs (H1.ztF.toList.take P.y.h.lt)).length + 1 :=
    ProofFile.Honest.K4.Live.win_len tT.p _ 1
      (fun w hw => by
        obtain ⟨z, -, rfl⟩ := List.mem_map.1 hw
        rfl) hv
      (by
        rw [hr, List.length_map, List.length_append, hm]
        rfl)
  have hf : tT.p.first = tT.sCl + 1 := by
    rw [b]
    exact congrArg PscSh.first a
  have hs : affSh tT.p.start = AffSh.mk [] [tT.sCl] := by
    rw [b]
    exact congrArg PscSh.start a
  refine ⟨{ tT with p := p' }, by rw [e], ?_⟩
  rw [e]
  show (affSh ((tT.p.rowForm zeroE {}).scale _)).slots = _
  rw [affSh_scale, affSh_rowForm, hw, hwl, hf, hs, show 1 + 2 * P.y.h.lt + 1 =
      2 * P.y.h.lt + 2 by omega]
  show (List.range' (tT.sCl + 1) (2 * P.y.h.lt + 2) ++ [tT.sCl]) ++ [] = _
  rw [List.append_nil]

/-- What the batched sumcheck's row K.rowS names. f: its first slot. -/
theorem batchedRow_slots (hh : hearFl P hp g fo F t = some (o, G, u)) :
    ∃ f tT, o.H.tT = some tT ∧ o.K.sA0 = f + 1 + 2 * hp.lamS + 2 ∧
      (affSh o.K.rowS).slots = List.range' f (2 * hp.lamS + 3) ++
        (tT.sCl :: (affSh o.H.fo.cEnd).slots ++ (affSh o.H.KT).slots) := by
  obtain ⟨-, -, -, -, H1, hd2, cl, G1, G2, G3, G4, G5, u1, u2, u3, u4, u5, -, -, h3, -⟩ :=
    hear_parts hh
  obtain ⟨x, mu0, eps, beta, T, rs, sentY, vals, w1, wY, wV, C, A1, ms, y, p, -, -, -, hj, -, -, hy,
    hp', hms, -, -, -, hsA, -, -, -, -, -, hrow, -⟩ := hearStack_tape h3
  obtain ⟨weighed, parts, laid, tT, -, hparts, -, -, -, hT, hC, -, -⟩ :=
    OnBytes.Road.K4.joinStart_startOf hj
  obtain ⟨e1, e2, -, e4, -, -, e7⟩ := endP_spec
    { target := T, first := G2.next, eps := eps, claim := addE mu0 (mulE eps T), start := C,
      started := true } ms y
  rw [← hp'] at e1 e2 e4 e7
  have hl : (plainWs hp.lamS).length = hp.lamS := by
    unfold plainWs
    rw [List.length_replicate]
  have hm : ms.length = (plainWs hp.lamS).length := by
    rw [← hms, List.length_map]
  have hv : p.vars.toList = plainWs hp.lamS ++ [OnBytes.Psc.Weight.atZero (2 + 1)] := by
    rw [e1, List.map_append, hms, hy]
    rfl
  have hw : p.walk.1.length = 1 + 2 * (plainWs hp.lamS).length + 2 :=
    ProofFile.Honest.K4.Live.win_len p _ 2
      (fun w hw => by
        rw [(List.mem_replicate.1 hw).2]
        rfl) hv
      (by
        rw [e2, List.map_append, List.length_append, List.length_append, List.length_map, hm]
        show 0 + ((plainWs hp.lamS).length + 1) = _
        omega)
  refine ⟨G2.next, tT, hT, hsA, ?_⟩
  rw [hrow, affSh_rowForm, hw, hl, e7, e4, hC,
    show 1 + 2 * hp.lamS + 2 = 2 * hp.lamS + 3 by omega]
  show (List.range' G2.next (2 * hp.lamS + 3) ++ (affSh (startOf o.H _ parts)).slots) ++ [] = _
  rw [List.append_nil, batchedStart_slots hT (join_no_slot hparts)]

end OnBytes.Desc.First.K4.Rt

#print axioms OnBytes.Desc.First.K4.Rt.weightedFold_addsNoSlots
#print axioms OnBytes.Desc.First.K4.Rt.batchedStart_slots
#print axioms OnBytes.Desc.First.K4.Rt.endForms_nameNoSlots
#print axioms OnBytes.Desc.First.K4.Rt.secondTokenForm_slots
#print axioms OnBytes.Desc.First.K4.Rt.batchedRow_slots
