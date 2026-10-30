-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/SendP2.lean: towards the tie between the kind's decision of a sending and the
sending that is written over the verifier program's own functions (sendP): the loop over the
messages, the answers, and what the test of the rounds gives.

Main names: sampleLoop_of_lay (a yes of the kind's loop over all messages is a yes of the other
loop over the sampled ones, with the same record and no answer left); answers_all; fit_more.

What is not claimed. The tie itself is not in this file. Nothing on soundness, on an honest prover
or on hiding.

-/
import Johnson.Desc.K1.Law.SendP1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice

variable {L : Type}

/-- **The two loops.** -/
theorem sampleLoop_of_lay (p : GPar) (codes : Codes) (seeds : List (List E × E))
    (hl : codes.lengthsOk = true) :
    ∀ (l : List (Nat × OracleShape)) (ys : List E) (d d' : DState L),
    (∀ x ∈ l, x.2.answers ≠ 0 →
      Blk.shapeOk codes x.2 = true ∧ (Msg.of codes x.2).padFits = true) →
    layRows codes seeds l ys d = .ok d' →
    sampleLoop groundG p codes (seeds.map seedOf) (l.filter fun x => x.2.answers != 0) ys d =
      some (d', [])
  | [], ys, d, d', _, h => by
    unfold layRows at h
    split at h
    · rename_i he
      obtain rfl := Except.ok.inj h
      rw [List.isEmpty_iff.1 he]
      rfl
    · cases h
  | (o, s) :: l, ys, d, d', hq, h => by
    unfold layRows at h
    by_cases h0 : s.answers = 0
    · rw [if_pos (by simpa using h0)] at h
      rw [List.filter_cons_of_neg (by simpa using h0)]
      exact sampleLoop_of_lay p codes seeds hl l ys d d'
        (fun x hx => hq x (List.mem_cons_of_mem _ hx)) h
    · rw [if_neg (by simpa using h0)] at h
      split at h
      · cases h
      · rename_i h1
        split at h
        · cases h
        · rename_i h2
          obtain ⟨d₁, ha, h⟩ := (bind_ok _ _ _).1 h
          have ha' := (named_ok _ _ _).1 ha
          obtain ⟨q1, q2⟩ := hq (o, s) List.mem_cons_self h0
          have ih := sampleLoop_of_lay p codes seeds hl l (ys.drop s.answers) d₁ d'
            (fun x hx => hq x (List.mem_cons_of_mem _ hx)) h
          rw [List.filter_cons_of_pos (by simpa using h0)]
          unfold sampleLoop
          rw [rowsFor_eq codes s o seeds ys hl q1 q2 (by simpa using h1) (by simpa using h2)]
          have hadm : groundG.admit p d o (rowsOf codes seeds o s ys) = some d₁ := ha'
          simp only [hadm]
          exact ih

/-- Items that are all answers: their number, and that the two ways to read them agree. -/
theorem answers_all : ∀ (vals : List Fmt.ItemValue) (n : Nat),
    vals.map itemOf = List.replicate n .answer →
    vals.length = n ∧ (vals.mapM fun
      | .answer x => some (E.ofTriple x)
      | _ => none) = some (vals.filterMap fun | .answer x => some (E.ofTriple x) | _ => none)
  | [], n, h => by
    cases n with
    | zero => exact ⟨rfl, rfl⟩
    | succ n => simp [List.replicate_succ] at h
  | g :: l, n, h => by
    cases n with
    | zero => simp at h
    | succ n =>
      simp only [List.map_cons, List.replicate_succ, List.cons.injEq] at h
      obtain ⟨i1, i2⟩ := answers_all l n h.2
      cases g <;> simp_all [itemOf, List.mapM_cons]

/-- What more the test of the rounds gives here. -/
theorem fit_more (P : Par) (r₁ r₂ : Fmt.RoundView) (h : roundsFit (rounds P) [r₁, r₂] = true) :
    r₁.vals = [] ∧ r₁.drawn.poss = [] ∧ r₁.drawn.trits = [] ∧ r₂.drawn.elems = [] ∧
      r₂.drawn.poss = [] ∧ r₂.drawn.trits = [] := by
  simp only [rounds, roundsFit, Bool.and_eq_true, beq_iff_eq] at h
  have a1 : r₁.vals.map itemOf =
      (Fmt.DeclaredRound.items { entry := seedEntry P }).filter (· != .root) := by tauto
  have a2 : r₁.drawn.poss.length = (seedEntry P).poss := by tauto
  have a3 : r₁.drawn.trits.length = (seedEntry P).trits := by tauto
  have a4 : r₂.drawn.elems.length = (answerEntry P).drawE := by tauto
  have a5 : r₂.drawn.poss.length = (answerEntry P).poss := by tauto
  have a6 : r₂.drawn.trits.length = (answerEntry P).trits := by tauto
  have b1 : (Fmt.DeclaredRound.items { entry := seedEntry P }).filter (· != .root) = [] := by
    simp [Fmt.DeclaredRound.items, Fmt.Entry.cut, seedEntry]
  rw [b1] at a1
  exact ⟨List.map_eq_nil_iff.1 a1, List.eq_nil_of_length_eq_zero a2,
    List.eq_nil_of_length_eq_zero a3, List.eq_nil_of_length_eq_zero a4,
    List.eq_nil_of_length_eq_zero a5, List.eq_nil_of_length_eq_zero a6⟩

end VerifiableInference.Desc.K1
