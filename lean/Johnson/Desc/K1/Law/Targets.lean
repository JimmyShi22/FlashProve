-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/Targets.lean: the targets of the sample rows that a sending lays into the record
are the answers received, all of them, in their order.

Main names: sampleRow_target, rowsOf_targets, outs_targets, behind_targets; toy_answer (at the small
place the one answer received is other than 0, the decision says yes, and that answer is the target
of the one row in the record).

What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.Joined2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain

variable {L : Type}

/-- The row's target is the answer that it is made with. -/
theorem sampleRow_target (m : Msg) (o : Nat) (z : List E) (β : E) (i : Nat) (y : E) :
    (sampleRow m o z β i y).target = y := rfl

/-- The targets of a message's sample rows are its answers. -/
theorem rowsOf_targets (codes : Codes) (seeds : List (List E × E)) (o : Nat) (s : OracleShape)
    (ys : List E) (h1 : s.answers ≤ seeds.length) :
    (rowsOf codes seeds o s ys).toList.map (fun r => r.target) = ys.take s.answers := by
  have e : (((seeds.take s.answers).zip (ys.take s.answers)).zipIdx.map fun x =>
      sampleRow (Msg.of codes s) o x.1.1.1 x.1.1.2 x.2 x.1.2).map (fun r => r.target) =
      (((seeds.take s.answers).zip (ys.take s.answers)).zipIdx.map Prod.fst).map Prod.snd := by
    rw [List.map_map, List.map_map]
    rfl
  unfold rowsOf
  rw [e, List.zipIdx_map_fst, List.map_snd_zip]
  rw [List.length_take, List.length_take]
  omega

/-- The targets of all new sample rows, message by message, are the answers. -/
theorem outs_targets (codes : Codes) (seeds : List (List E × E)) (n : Nat)
    (hn : n ≤ seeds.length) : ∀ (l : List OracleShape) (o : Nat) (ys : List E),
    fitB codes n l ys = true →
    (outs codes seeds o l ys).flatMap (fun x => x.sampleRows.toList.map fun r => r.target) = ys
  | [], _, ys, h => by
    simp only [fitB, List.isEmpty_iff] at h
    subst h
    rfl
  | s :: l, o, ys, h => by
    unfold fitB at h
    simp only [outs, List.flatMap_cons]
    by_cases h0 : s.answers = 0
    · rw [if_pos h0] at h
      have ih := outs_targets codes seeds n hn l (o + 1) ys h
      rw [h0, List.drop_zero, ih]
      simp [wr, h0, fresh]
    · rw [if_neg h0] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      have ih := outs_targets codes seeds n hn l (o + 1) (ys.drop s.answers) h.2
      have hw : (wr codes seeds o s ys).sampleRows = rowsOf codes seeds o s ys := by
        simp [wr, h0]
      rw [ih, hw, rowsOf_targets codes seeds o s ys (Nat.le_trans h.1.1.1 hn),
        List.take_append_drop]

/-- **Behind a yes: the targets of the new messages' sample rows are the answers that the second
round holds, all of them, in their order.** -/
theorem behind_targets (P : Par) (owed : Option Nat) (d d' : DState L) (r₁ r₂ : Fmt.RoundView)
    (ids : Array Nat) (hyes : decideSend P owed d [r₁, r₂] = .ok (ids, d')) :
    (d'.st.oracles.toList.drop d.st.oracles.size).flatMap
      (fun x => x.sampleRows.toList.map fun r => r.target) = answersIn r₂ := by
  obtain ⟨⟨_, _, _, _, hf⟩, _, rfl⟩ := (decideSend_iff P owed d d' r₁ r₂ ids).1 hyes
  have e : (behind P d (seedsOf P r₁) (answersIn r₂)).st.oracles.toList =
      d.st.oracles.toList ++ outs P.codes (seedsOf P r₁) d.st.oracles.size (shapesOf P)
        (answersIn r₂) := rfl
  rw [e, List.drop_left' (by simp)]
  exact outs_targets P.codes (seedsOf P r₁) P.seeds
    (Nat.le_of_eq (cutSeeds_length _ _ _).symm) _ _ _ hf

/-- **A try at an answer other than 0.** -/
theorem toy_answer : isZeroE (E.ofTriple (5, 0, 0)) = false ∧
    ∃ ids d', decideSend toyP none toyD [toyR₁, toyR₂] = .ok (ids, d') ∧
      d'.st.oracles.toList.flatMap (fun x => x.sampleRows.toList.map fun r => r.target) =
        [E.ofTriple (5, 0, 0)] := by
  refine ⟨by decide, _, _,
    (decideSend_iff toyP none toyD _ toyR₁ toyR₂ _).2 ⟨toy_asks, rfl, rfl⟩, ?_⟩
  exact behind_targets toyP none toyD _ toyR₁ toyR₂ _
    ((decideSend_iff toyP none toyD _ toyR₁ toyR₂ _).2 ⟨toy_asks, rfl, rfl⟩)

end VerifiableInference.Desc.K1
