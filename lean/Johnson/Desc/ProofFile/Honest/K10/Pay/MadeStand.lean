-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/MadeStand.lean: the closing of a segment (K10): at a list of challenges that fits the
rounds of the sub-protocols in front of the closing, every challenge of the folds in front has been heard and drew an
element: the job's test `heardAll` passes.

  `gammaTest`, `gamma_written`, `fold_draws`   by Lean's kernel, at the written plan: at each of the 25 closings each fold's
                    challenge in front stands among the rounds in front, and every round of a fold draws an element
  `declared_in_front`   the rounds in front of a border are the first of the public part's declared rounds
  `heard_reached`   the job's test passes, at the segments of the written plan

Limits. That the list of challenges fits is a premise: it is the clause (F) of the thread's invariant. The head is a premise.
The full size and the older hash alone.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.MadeHeard
import Johnson.Desc.ProofFile.Honest.K10.Pay.MadeParts
import Johnson.Desc.ProofFile.Honest.K10.Pay.AtReach
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc
open VerifiableInference.Desc.First.Close (Par hc_at_laid)
open VerifiableInference.PlanWritten (cutFirstFull)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open ProofFile.Honest.K2 (segmentsOf)
open ProofFile.Honest.K2.Law (segsW segsAt entryNumbers entries_at_head)

/-- How many rounds the sub-protocols in front of a border have, off the written cut. -/
def roundsW (b : Nat) : Nat := ((cutFirstFull.take b).map fun r => r.2.2.1).sum

/-- At closing l each fold's challenge in front stands among the rounds in front. -/
def gammaTest (l : Nat) : Bool :=
  (segsW.take (l + 1)).dropLast.all fun S => S.gamma.all fun i => decide (i < roundsW (14 * l + IM.nAt l + 5))

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
/-- So it is at the 25 closings. -/
theorem gamma_written : ((List.range 25).all gammaTest) = true := by decide +kernel

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
/-- Every round of a fold draws an element. -/
theorem fold_draws : (P5T.esFull.1.all fun e => e.name != "FOLD round" || decide (0 < e.drawE)) = true := by
  decide +kernel

/-- A fold's challenge is one of the rounds of that name. -/
theorem gamma_named {P? : Option P1K2.Prep} {fold : List Nat} {S : ProofFile.Honest.K2.SegmentPub}
    (hS : S ∈ segsAt P? fold) {i : Nat} (hi : i ∈ S.gamma) : i ∈ fold := by
  unfold segsAt at hS
  cases P? with
  | none => cases hS
  | some P =>
    obtain ⟨L, -, rfl⟩ := List.mem_map.1 hS
    exact List.mem_of_mem_drop (List.mem_of_mem_take hi)

/-- The numbers of a name's entries are entries of that name. -/
theorem entry_of_number {es : List Fmt.Entry} {name : String} {i : Nat} (h : i ∈ entryNumbers es name) :
    ∃ e, es[i]? = some e ∧ e.name = name := by
  unfold entryNumbers at h
  obtain ⟨d, hd, e⟩ := List.mem_filterMap.1 h
  split at e
  · rename_i hn
    obtain rfl := Option.some.inj e
    exact ⟨d.1, List.mem_zipIdx_iff_getElem?.1 hd, eq_of_beq hn⟩
  · cases e

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The rounds in front of a border are the first of the public part's declared rounds.** -/
theorem declared_in_front (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) (b : Nat) :
    declsTo cF.blocksInOrder b = Zp.D.1.take (declsTo cF.blocksInOrder b).length ∧ (declsTo cF.blocksInOrder b).length = roundsW b := by
  obtain ⟨Bs, base, O⟩ := h.toAtMg.laid.opened
  have PP := (FileDescription.planOk_ok _).1 h.toAtMg.laid.planOk
  rw [O.desc] at PP
  have hD : cF.blocksInOrder.flatMap (·.rounds) = Zp.D.1 := PP.decl₁
  have hc := hc_at_laid h.toAtMg.scope h.toAtMg.laid
  constructor
  · have e : Zp.D.1 = declsTo cF.blocksInOrder b ++ (cF.blocksInOrder.drop b).flatMap (·.rounds) := by
      unfold declsTo
      rw [← hD, ← List.flatMap_append, List.take_append_drop]
    conv_rhs => rw [e]
    rw [List.take_left' rfl]
  · unfold declsTo roundsW
    rw [List.length_flatMap, ← hc]
    unfold VerifiableInference.PlanWritten.cutOf
    rw [← List.map_take, List.map_map]
    rfl

/-- **At a list of challenges that fits the rounds in front, the job's test `heardAll` passes.** -/
theorem heard_reached (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {l : Nat} (hl : l < 25) {Qc : Par}
    (hQ : Qc.link = l) {Gr : ProofFile.Ground} (hS : segmentsOf Zp Gr = segsW) {front : List Fmt.Drawn}
    (hd : drawsFit (declsTo cF.blocksInOrder (14 * l + IM.nAt l + 5)) front = true) :
    heardAll (lotSegs Zp Gr Qc) front = .ok () := by
  have eS : lotSegs Zp Gr Qc = segsW.take (l + 1) := by
    show (segmentsOf Zp Gr).take (Qc.link + 1) = _
    rw [hS, hQ]
  rw [eS]
  refine heard_of_fit hd fun S hS' i hi => ?_
  have hg := List.all_eq_true.1 gamma_written l (List.mem_range.2 hl)
  unfold gammaTest at hg
  have h2 := List.all_eq_true.1 (List.all_eq_true.1 hg S hS') i hi
  have hlt := of_decide_eq_true h2
  obtain ⟨eT, eL⟩ := declared_in_front h (14 * l + IM.nAt l + 5)
  have hi2 : i < (declsTo cF.blocksInOrder (14 * l + IM.nAt l + 5)).length := by
    rw [eL]
    exact hlt
  have e3 : (declsTo cF.blocksInOrder (14 * l + IM.nAt l + 5))[i]? = Zp.D.1[i]? := by
    conv_lhs => rw [eT]
    exact List.getElem?_take_of_lt hi2
  refine ⟨_, List.getElem?_eq_getElem hi2, ?_⟩
  obtain ⟨Bs, base, O⟩ := h.toAtMg.laid.opened
  have hE := entries_at_head h.toAtMg O
  obtain ⟨e, he, en⟩ := entry_of_number
    (gamma_named (List.mem_of_mem_take (List.mem_of_mem_dropLast hS')) hi : i ∈ entryNumbers P5T.esFull.1 "FOLD round")
  have hb := List.all_eq_true.1 fold_draws e (List.mem_of_getElem? he)
  rw [en] at hb
  have hp : 0 < e.drawE := by simpa using hb
  rw [← hE, List.getElem?_map, ← e3, List.getElem?_eq_getElem hi2] at he
  have he' : ((declsTo cF.blocksInOrder (14 * l + IM.nAt l + 5))[i]).entry = e := Option.some.inj he
  show 0 < ((declsTo cF.blocksInOrder (14 * l + IM.nAt l + 5))[i]).entry.drawE
  rw [he']
  exact hp

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.roundsW
#print axioms ProofFile.Honest.K10.gammaTest
#print axioms ProofFile.Honest.K10.gamma_written
#print axioms ProofFile.Honest.K10.fold_draws
#print axioms ProofFile.Honest.K10.gamma_named
#print axioms ProofFile.Honest.K10.entry_of_number
#print axioms ProofFile.Honest.K10.declared_in_front
#print axioms ProofFile.Honest.K10.heard_reached
