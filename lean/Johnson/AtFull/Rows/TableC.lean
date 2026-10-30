-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/TableC.lean: Steps.lean's WALK BY A TABLE, WITH THE TEST BY CALLS
(StepC.lean: pieceC) IN pieceB's PLACE; and that the pieces of «proof 0» are faithful. Theorems. A
law file; no running text imports it.
  `good_consC`, `good_fromC`, `good_of_tableC` as good_cons | good_from | good_of_table, from
                  pieceC; each piece is asked to be faithful (for its own test) and to read no round
                  (to be laid behind the others).
  `faith_segA`, `faith_framePieces`, `faith_proof0Tail`, `faith_proof0Pieces`.
Limits. No closed fact is here. Nothing on soundness or on hiding.
-/
import Johnson.AtFull.Rows.StepC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom

theorem good_consC {s : Setting} {truth : List PlanRound} {st st' : SmallSt × Nat} {x y : N Unit}
    (hx : Faith x) (hy : Fr y) (h : pieceC s truth st x = some st') (g : Good s truth st' y) :
    Good s truth st (x >>= fun _ => y) := by
  obtain ⟨cs, rs, hr, e2, hs⟩ := stepC_runs hx h
  obtain ⟨cs', rs', sc', hr', hs'⟩ := g
  refine ⟨cs ++ cs', rs ++ rs', sc', RunsN.bind hr hy hr', ?_⟩
  rw [e2] at hs'
  have e : truth.drop st.2 = (truth.drop st.2).take rs.size ++ truth.drop (st.2 + rs.size) := by
    rw [← List.drop_drop, List.take_append_drop]
  rw [e, Array.toList_append]
  exact sameAll_app hs hs'

theorem good_fromC {s : Setting} {truth : List PlanRound} {sc' : Scope}
    (tab : Nat → SmallSt × Nat) :
    ∀ (xs : List (N Unit)) (k : Nat), (∀ x ∈ xs, Fr x) → (∀ x ∈ xs, Faith x) →
      (∀ i, i < xs.length →
        pieceC s truth (tab (k + i)) (xs.getD i (pure ())) = some (tab (k + i + 1))) →
      tab (k + xs.length) = (⟨sc', 0, 0, 0⟩, truth.length) → Good s truth (tab k) (seqN xs)
  | [], k, _, _, _, he => by
    rw [List.length_nil, Nat.add_zero] at he
    rw [he]
    exact good_nil
  | x :: xs, k, hf, ha, h, he => by
    have h0 := h 0 (Nat.succ_pos _)
    rw [Nat.add_zero, List.getD_cons_zero] at h0
    refine good_consC (ha x (List.mem_cons_self ..))
      (fr_seqN fun y hy => hf y (List.mem_cons_of_mem _ hy)) h0 ?_
    refine good_fromC (sc' := sc') tab xs (k + 1) (fun y hy => hf y (List.mem_cons_of_mem _ hy))
      (fun y hy => ha y (List.mem_cons_of_mem _ hy)) (fun i hi => ?_) ?_
    · have hi' := h (i + 1) (Nat.succ_lt_succ hi)
      rw [List.getD_cons_succ] at hi'
      have e : k + (i + 1) = k + 1 + i := by omega
      rw [e] at hi'
      exact hi'
    · have e : k + 1 + xs.length = k + (x :: xs).length := by
        rw [List.length_cons]
        omega
      rw [e]
      exact he

/-- **A table of the states between the pieces gives the walk: by the test by calls.** -/
theorem good_of_tableC {s : Setting} {truth : List PlanRound} {sc' : Scope}
    (tab : Nat → SmallSt × Nat)
    (xs : List (N Unit)) (hf : ∀ x ∈ xs, Fr x) (ha : ∀ x ∈ xs, Faith x)
    (h : ∀ i, i < xs.length → pieceC s truth (tab i) (xs.getD i (pure ())) = some (tab (i + 1)))
    (he : tab xs.length = (⟨sc', 0, 0, 0⟩, truth.length)) : Good s truth (tab 0) (seqN xs) := by
  refine good_fromC (sc' := sc') tab xs 0 hf ha (fun i hi => ?_) ?_
  · rw [Nat.zero_add]
    exact h i hi
  · rw [Nat.zero_add]
    exact he

theorem faith_segA (A : Nat → Arm) (z : ProofSized) (l : Nat) (g : ReqGroup) (gs : List ReqGroup)
    (links : List ReqLink) (open_ : List Nat) (before : GroupSize) :
    Faith (segA A z l g gs links open_ before) := by
  unfold segA
  cases links.head? with
  | none => fth
  | some lk => fth

theorem faith_framePieces (A : Nat → Arm) (z : ProofSized) :
    ∀ (gs : List ReqGroup) (l : Nat) (links : List ReqLink) (open_ : List Nat) (before : GroupSize),
    ∀ x ∈ framePieces A z l gs links open_ before, Faith x
  | [], _, _, _, _, x, hx => by
    unfold framePieces at hx
    cases hx
  | g :: gs, l, links, open_, before, x, hx => by
    unfold framePieces at hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact faith_segA A z l g gs links open_ before
    · cases h : links.head? with
      | none =>
        rw [h] at hx
        cases hx
      | some lk =>
        rw [h] at hx
        exact faith_framePieces A z gs _ _ _ _ x hx

theorem faith_proof0Tail (c : Configured) (pendingRows : Nat) :
    Faith (proof0Tail c pendingRows) := by
  have := faith_nLinFirst c.sized.proof.codes c.sized.proof.batch
  unfold proof0Tail
  fth

theorem faith_proof0Pieces (c : Configured) (openRows : List Nat) (pendingRows : Nat)
    (A : Nat → Arm) :
    ∀ x ∈ proof0Pieces c openRows pendingRows A, Faith x := by
  intro x hx
  unfold proof0Pieces at hx
  rcases List.mem_append.1 hx with hx | hx
  · exact faith_framePieces _ _ _ _ _ _ _ x hx
  · rcases List.mem_singleton.1 hx with rfl
    exact faith_proof0Tail c pendingRows

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.good_consC
#print axioms VerifiableInference.Desc.LinkJoin.good_of_tableC
#print axioms VerifiableInference.Desc.LinkJoin.faith_proof0Pieces
