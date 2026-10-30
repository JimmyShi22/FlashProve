-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/LettersHone.lean: under the library's head, the premise hone of w_ready_of_rows
(LettersReadyW.lean), from the clause of a thread's stand that the challenges heard fit the declared
rounds: the last 2 + kCol challenges in front of W's sending have one element each.

  last_draws_written   at the written description the last twenty rounds in front of number 356 draw
                       one element each
  drawsFit_elems       challenges that fit declared rounds have the counts of elements declared
  hone_at_head         hone, at challenges that fit the rounds in front of number 356

Limits.
- hd is a premise: a stand's clause holds it at the whole list heard, at a border 356.
- At the full size and the format's second hash function.
- Nothing on completeness, soundness or hiding.
-/
import AtFullSide.K12.LettersReadyW

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K12
open OnBytes
open ProofFile.Honest ProofFile.Honest.K13
open VerifiableInference.Desc (Chain alike₂_rounds)
open P2Law.ProofPlan (WP)
open P5J (AtMgA TS)

set_option maxRecDepth 1000000 in
/-- **At the written description the last twenty rounds in front of number 356 draw one element
each.** An evaluation in Lean's kernel. -/
theorem last_draws_written :
    (((WP.first.blocksInOrder.take 356).flatMap (·.rounds)).drop 48270).all
      (fun d => d.entry.drawE == 1) = true := by
  decide +kernel

/-- **Challenges that fit declared rounds have the declared counts of elements.** -/
theorem drawsFit_elems : ∀ (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn),
    drawsFit ds Rs = true → Rs.map (·.elems.length) = ds.map (·.entry.drawE)
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [drawsFit] at h
  | _ :: _, [], h => by simp [drawsFit] at h
  | d :: ds, R :: Rs, h => by
    have h' : (drawFit d R && drawsFit ds Rs) = true := h
    rw [Bool.and_eq_true] at h'
    obtain ⟨k, hr⟩ := h'
    unfold drawFit at k
    simp only [Bool.and_eq_true] at k
    rw [List.map_cons, List.map_cons, drawsFit_elems ds Rs hr, beq_iff_eq.1 k.1.1.1.1.1.1.1]

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **hone, at challenges that fit the rounds in front of number 356.** -/
theorem hone_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) (heard : List Fmt.Drawn)
    (hd : drawsFit (declsTo cF.blocksInOrder 356) (heard.take (wHeard Zp)) = true) :
    ((heard.take (wHeard Zp)).drop (wHeard Zp - (2 + Zp.first.lin.kCol))).all
      (fun d => d.elems.length == 1) = true := by
  have eN := AtFullSide.K13.k13_wHeard_at_head h
  have eK := (AtFullSide.K13.k13_wRow_at_head h).2.2.2
  rw [eK]
  rw [eN] at hd ⊢
  have hm := drawsFit_elems _ _ hd
  have A := ProofFile.Honest.K14.planAlike_at_head h
  have er : declsTo cF.blocksInOrder 356 = (WP.first.blocksInOrder.take 356).flatMap (·.rounds) :=
    (alike₂_rounds _ _ (List.forall₂_take 356 A.first)).symm
  rw [er] at hm
  refine List.all_eq_true.2 fun R hR => ?_
  have hmem : R.elems.length ∈ ((heard.take 48290).drop 48270).map (·.elems.length) :=
    List.mem_map.2 ⟨R, hR, rfl⟩
  rw [List.map_drop, hm, ← List.map_drop] at hmem
  obtain ⟨d, hd', e⟩ := List.mem_map.1 hmem
  have k := List.all_eq_true.1 last_draws_written d hd'
  rw [← e]
  exact k

end AtFullSide.K12

#print axioms AtFullSide.K12.last_draws_written
#print axioms AtFullSide.K12.drawsFit_elems
#print axioms AtFullSide.K12.hone_at_head
