-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/SumLaw/SumCut.lean: THE MASKED SUMCHECK's MESSAGES HAVE THE SHAPE's
COUNTS, where the call passes `shapeFair` (ShapeFair.lean) and the variables' challenges, Y's
counted, are as many as the call's variables, AND THE COINS ARE AS MANY AS THE SCALARS, at every
shape. Statements with their proofs.
Main names:
  `outK_lengths`, `sumMsgs_lengths`: message by message as many values as `scalarsOf` says.
  `runOf_sum`, `run_count`: **the two stretches of coins together are as many as the scalars sent**,
    at every shape.
  `roundsCut_flatten`: lists in a row, cut by their own lengths, are these lists.
  `shown_said`: what is shown of rounds in which scalars were said: their items, and no column.

Stated anew, so that no further file is imported: `foldl_sum` (as `foldl_add`,
OnBytes/Chain/Lists.lean).

Limits. No distribution occurs. No property of a protocol is stated.
-/
import Johnson.Desc.ProofFile.Honest.SumLaw.SumShown
import Johnson.Desc.ProofFile.Honest.SumLaw.PlaysSum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.SumLaw
open OnBytes (E zeroE)
open OnBytes.Model (Reading)
open OnBytes.Slice (GE ofE toE)
open VerifiableInference.Desc.Part.MaskedSum

variable {W X : Type}

/-- Each round sends d - 1 values. -/
theorem outK_lengths {K α : Type} [CommRing K] (q : List α → Nat → K) (eps : K) :
    ∀ (vs : List (VK K)) (u : Nat → K) (i : Nat) (past rs : List α), vs.length = rs.length →
      (∀ v ∈ vs, 2 ≤ v.2) →
      (outK q eps vs u i past rs).map List.length = vs.map fun v => v.2 - 1
  | [], _, _, _, [], _, _ => rfl
  | v :: rest, u, i, past, r :: rs, hl, h2 => by
    show (cutK v _).length :: (outK q eps rest u _ (past ++ [r]) rs).map List.length = _
    rw [cutK_length v (h2 v List.mem_cons_self), outK_lengths q eps rest u _ _ rs
      (by simp only [List.length_cons] at hl; omega)
      fun x hx => h2 x (List.mem_cons_of_mem _ hx)]
    rfl
  | [], _, _, _, _ :: _, hl, _ => by simp only [List.length_cons, List.length_nil] at hl; omega
  | _ :: _, _, _, _, [], hl, _ => by simp only [List.length_cons, List.length_nil] at hl; omega

/-- The numbers d - 1 of the call's variables in a run, Y's among them, by the shape. -/
theorem all_less (J : SumJob W X) (w : W) (fr : Front X) :
    (J.callAt w fr).all.map (fun v => v.d - 1) =
      J.shape.vs.map (fun v => v.d - 1) ++ (match J.shape.ends with
        | none => []
        | some e => [e.dY]) := by
  have e : ∀ l : List Var, (l.map fun v => v.d - 1) = (l.map Var.d).map (· - 1) := by
    intro l
    rw [List.map_map]
    rfl
  cases he : J.shape.ends with
  | none => rw [all_none J w fr he, e, withPoints_ds, ← e, List.append_nil]
  | some x =>
    rw [all_some J w fr x he, List.map_append, e, withPoints_ds, ← e]
    rfl

/-- **Message by message as many values as `scalarsOf` says.** -/
theorem sumMsgs_lengths (J : SumJob W X) (w : W) (fr : Front X) (eps : E) (rs : List E) (beta : E)
    (u m : Nat → GE) (hs : shapeFair (J.callAt w fr) = true)
    (hl : rs.length = (J.callAt w fr).all.length) :
    (sumMsgs J w fr eps rs beta u m).map List.length = scalarsOf J.shape := by
  unfold sumMsgs msgsK scalarsOf
  rw [List.map_cons, List.map_append, outK_lengths _ _ _ _ _ _ _
    (by rw [List.length_map]; exact hl.symm)
    (fun v hv => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hv
      rw [toK_snd]
      exact fair_all_two hs x hx),
    List.length_append, List.length_map, List.length_range, List.map_map]
  have e1 : ((fun v : VK GE => v.2 - 1) ∘ toK Reading.gl) = fun v : Var => v.d - 1 :=
    funext fun v => by
      show (toK Reading.gl v).2 - 1 = v.d - 1
      rw [toK_snd]
  rw [e1, all_less]
  cases J.shape.ends with
  | none => simp
  | some e => simp

/-- A sum from the left. -/
theorem foldl_sum : ∀ (l : List Nat) (a : Nat), l.foldl (· + ·) a = a + l.sum
  | [], a => rfl
  | x :: l, a => by
    rw [List.foldl_cons, foldl_sum l, List.sum_cons]
    omega

/-- How many scalars a call sends, as a sum. -/
theorem runOf_sum (k : Call) : runOf k = (scalarsOf k).sum := by
  unfold runOf
  rw [foldl_sum, Nat.zero_add]

/-- **The two stretches of coins together are as many as the scalars sent.** -/
theorem run_count (k : Call) : ownRun k + endsN k = runOf k := by
  obtain ⟨lead, vs, ends⟩ := k
  rw [runOf_sum]
  unfold ownRun endsN scalarsOf Call.all
  rw [ownSlots_one_add]
  cases ends with
  | none =>
    simp only [List.append_nil, List.sum_append, List.sum_cons, List.sum_nil, Option.map_none,
      Option.getD_none]
    omega
  | some e =>
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
      List.sum_nil, Option.map_some, Option.getD_some, Var.d]
    omega

/-- Lists in a row, cut by their own lengths, are these lists. -/
theorem roundsCut_flatten : ∀ L : List (List E), roundsCut (L.map List.length) L.flatten = L
  | [] => rfl
  | l :: L => by
    show (l ++ L.flatten).take l.length :: roundsCut _ ((l ++ L.flatten).drop l.length) = _
    rw [List.take_left, List.drop_left, roundsCut_flatten L]

/-- What is shown of rounds in which scalars were said: their items, and no column. -/
theorem shown_said (nm : String) (a : Addr) (asks : List (List (List Nat))) (rs : List Fmt.RoundView) :
    shownOf (rs.map (saidPlayed nm a)) asks = rs.map fun r => ⟨r.vals, []⟩ := by
  have h : ∀ (rs : List Fmt.RoundView) (n : Nat),
      ((rs.map (saidPlayed nm a)).zipIdx n).map (fun x : Played × Nat =>
        (⟨x.1.vals, x.1.tables.zipIdx.map fun y =>
          match y.1 with
          | some t => ((((asks[x.2]?).getD [])[y.2]?).getD []).map fun p => (p, t.col p)
          | none => []⟩ : Shown)) = rs.map fun r => ⟨r.vals, []⟩ := by
    intro rs
    induction rs with
    | nil => intro n; rfl
    | cons r rs ih =>
      intro n
      rw [List.map_cons, List.zipIdx_cons, List.map_cons, ih (n + 1)]
      rfl
  exact h rs 0

end ProofFile.Honest.SumLaw

#print axioms ProofFile.Honest.SumLaw.outK_lengths
#print axioms ProofFile.Honest.SumLaw.all_less
#print axioms ProofFile.Honest.SumLaw.sumMsgs_lengths
#print axioms ProofFile.Honest.SumLaw.foldl_sum
#print axioms ProofFile.Honest.SumLaw.runOf_sum
#print axioms ProofFile.Honest.SumLaw.run_count
#print axioms ProofFile.Honest.SumLaw.roundsCut_flatten
#print axioms ProofFile.Honest.SumLaw.shown_said
