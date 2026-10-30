-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Honest/Causal.lean: WHAT `stagesAll` (Johnson/Desc/K12/Honest/Stages.lean) SHOWS IN
A ROUND HANGS ON THE SAMPLED CHALLENGES IN FRONT OF THAT ROUND ALONE. Statements and proofs, after
the pattern of Johnson/Prover/Link/BodyCausal.lean, whose general lemmas are called; here the trees
that hold the first stage's rows are any list.

  `length_aFold`   a fold shows one round and one more for each row variable
  `aFold_congr`, `aPoint_congr`, `aNext_congr`, `aAns_congr`, `aSwitch_congr`, `aRec3_congr`   equal
                   sampled challenges, equal pieces of a stage
  **`stagesAll_causal`**   two families of sampled challenges that agree below o + i: the round at
                   place i shows the same items and sends the same tree

So a function of the sampled challenges so far can be cut out of the term.

Limits. It holds at all letters, also where the description's parts reject. THE VERIFIER's STATE IN
FRONT, THE PROVER's STATE, THE TREES AND THE COINS ARE HELD THE SAME AT BOTH FAMILIES: where one of
them is made of sampled challenges, whoever calls this law has to show that it is the same at both.
It says nothing of the groups of columns (they hang on the round's own positions), nothing on a
decision. Nothing on completeness, on soundness or on what is hidden.


-/
import Johnson.Desc.K12.Honest.Stages
import Johnson.Prover.Link.BodyCausal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open H2K.Pub (sgOf)

section Stage
variable (p : P12) (K : BCoins) (last : Bool) (j : ℕ) (cur next : Fmt.M1.Stage) (l : Laid) (o : ℕ)
  (t : T12) (P : PS) (trees : List Tree) (row : GroupRow) (D D' : ℕ → Fmt.Drawn)

/-- A fold shows one round and one more for each row variable. -/
theorem length_aFold : (aFold K j cur o P row D).length = 1 + ((sgOf cur).h + (sgOf cur).g) :=
  length_sRF K j cur o P row D

/-- The fold's rounds hang on the sampled challenges up to the last of these rounds alone. -/
theorem aFold_congr (h : ∀ n, n < o + (1 + ((sgOf cur).h + (sgOf cur).g)) → D n = D' n) :
    aFold K j cur o P row D = aFold K j cur o P row D' :=
  sRF_congr K j cur o P row D D' h

/-- So does the sampled point. -/
theorem aPoint_congr (h : ∀ n, n < o + (1 + ((sgOf cur).h + (sgOf cur).g)) → D n = D' n) :
    aPoint cur o D = aPoint cur o D' := by
  unfold aPoint
  congr 1
  refine List.map_congr_left fun n hn => ?_
  rw [h (o + (n + 1)) (by have := List.mem_range.1 hn; omega)]

/-- So does the prover's state behind the fold. -/
theorem aNext_congr (h : ∀ n, n < o + (1 + ((sgOf cur).h + (sgOf cur).g)) → D n = D' n) :
    aNext K last j cur next o P D = aNext K last j cur next o P D' := by
  unfold aNext
  rw [aPoint_congr cur o D D' h]

/-- The answer hangs on what the switch's first round sampled. -/
theorem aAns_congr (t₁ : T12) (Q : PS)
    (h1 : D (o + 1 + ((sgOf cur).h + (sgOf cur).g)) = D' (o + 1 + ((sgOf cur).h + (sgOf cur).g))) :
    aAns p j cur next o D t₁ Q = aAns p j cur next o D' t₁ Q := by
  unfold aAns
  rw [h1]

/-- The switch's two rounds hang on what they sampled. -/
theorem aSwitch_congr (a : GE)
    (h1 : D (o + 1 + ((sgOf cur).h + (sgOf cur).g)) = D' (o + 1 + ((sgOf cur).h + (sgOf cur).g)))
    (h2 : D (o + 2 + ((sgOf cur).h + (sgOf cur).g)) = D' (o + 2 + ((sgOf cur).h + (sgOf cur).g))) :
    aSwitch cur o D a = aSwitch cur o D' a := by
  unfold aSwitch
  rw [h1, h2]

/-- The verifier's state behind the switch hangs on what the switch's second round sampled. -/
theorem aRec3_congr (t₁ : T12) (rs : List Fmt.RoundView)
    (h2 : D (o + 2 + ((sgOf cur).h + (sgOf cur).g)) = D' (o + 2 + ((sgOf cur).h + (sgOf cur).g))) :
    aRec3 p last j cur next l o trees D t₁ rs = aRec3 p last j cur next l o trees D' t₁ rs := by
  unfold aRec3 aGroups
  rw [h2]

end Stage

/-- **What a round shows hangs on the sampled challenges in front of it alone.** -/
theorem stagesAll_causal (p : P12) (K : BCoins) : ∀ (rest : List Fmt.M1.Stage) (j : ℕ)
    (cur : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS) (trees : List Tree)
    (D D' : ℕ → Fmt.Drawn) (i : ℕ), (∀ n, n < o + i → D n = D' n) →
    ((stagesAll p K rest j cur l o t P trees D).rs[i]?).map (·.vals) =
        ((stagesAll p K rest j cur l o t P trees D').rs[i]?).map (·.vals) ∧
      (stagesAll p K rest j cur l o t P trees D).tr[i]? =
        (stagesAll p K rest j cur l o t P trees D').tr[i]?
  | [], j, cur, l, o, t, P, trees, D, D', i, h =>
    bodyAll_causal p K [] j cur l o t P (fun _ => []) D D' i h
  | next :: rest, j, cur, l, o, t, P, trees, D, D', i, h => by
    have hlen := length_aFold K j cur o P (rowOf t) D
    have hlen' := length_aFold K j cur o P (rowOf t) D'
    show ((aFold K j cur o P (rowOf t) D ++
        aSwitch cur o D (aAns p j cur next o D (aRec1 p j cur l t (aFold K j cur o P (rowOf t) D))
          (aNext K rest.isEmpty j cur next o P D)) ++
        (stagesAll p K rest _ _ _ _ _ _ _ D).rs)[i]?).map (·.vals) =
      ((aFold K j cur o P (rowOf t) D' ++
        aSwitch cur o D' (aAns p j cur next o D'
          (aRec1 p j cur l t (aFold K j cur o P (rowOf t) D'))
          (aNext K rest.isEmpty j cur next o P D')) ++
        (stagesAll p K rest _ _ _ _ _ _ _ D').rs)[i]?).map (·.vals) ∧
      ((aFold K j cur o P (rowOf t) D).map (fun _ _ => []) ++
        [aCol rest.isEmpty next (aNext K rest.isEmpty j cur next o P D), fun _ => []] ++
        (stagesAll p K rest _ _ _ _ _ _ _ D).tr)[i]? =
      ((aFold K j cur o P (rowOf t) D').map (fun _ _ => []) ++
        [aCol rest.isEmpty next (aNext K rest.isEmpty j cur next o P D'), fun _ => []] ++
        (stagesAll p K rest _ _ _ _ _ _ _ D').tr)[i]?
    have hm : ∀ E : ℕ → Fmt.Drawn, ((aFold K j cur o P (rowOf t) E).map
        (fun (_ : Fmt.RoundView) (_ : ℕ) => ([] : List UInt64))).length =
        1 + ((sgOf cur).h + (sgOf cur).g) := fun E => by
      rw [List.length_map]; exact length_aFold K j cur o P (rowOf t) E
    by_cases c1 : i < 1 + ((sgOf cur).h + (sgOf cur).g)
    · constructor
      · rw [get3_left _ _ _ i (by rw [hlen]; exact c1), get3_left _ _ _ i (by rw [hlen']; exact c1),
          ← fold_eq K j cur o P (rowOf t) D, ← fold_eq K j cur o P (rowOf t) D']
        exact vals_of_getD (by rw [length_sRF]; exact c1) (by rw [length_sRF]; exact c1)
          (foldRV_vals _ _ _ _ (fun n => D (o + n)) (fun n => D' (o + n)) i
            fun n hn => h (o + n) (Nat.add_lt_add_left hn o))
      · rw [get3_left _ _ _ i (by rw [hm]; exact c1), get3_left _ _ _ i (by rw [hm]; exact c1),
          List.getElem?_map, List.getElem?_map, List.getElem?_eq_getElem (by rw [hlen]; exact c1),
          List.getElem?_eq_getElem (by rw [hlen']; exact c1)]
        rfl
    · have hD : ∀ n, n < o + (1 + ((sgOf cur).h + (sgOf cur).g)) → D n = D' n :=
        fun n hn => h n (by omega)
      have hF := aFold_congr K j cur o P (rowOf t) D D' hD
      have hQ := aNext_congr K rest.isEmpty j cur next o P D D' hD
      rw [← hF, ← hQ]
      have l2 : ∀ (E : ℕ → Fmt.Drawn) (a : GE), (aSwitch cur o E a).length = 2 := fun _ _ => rfl
      by_cases c2 : i < 3 + ((sgOf cur).h + (sgOf cur).g)
      · constructor
        · rw [get3_mid _ _ _ i (by rw [hlen]; omega) (by rw [hlen, l2]; omega),
            get3_mid _ _ _ i (by rw [hlen]; omega) (by rw [hlen, l2]; omega), hlen]
          rcases (by omega : i - (1 + ((sgOf cur).h + (sgOf cur).g)) = 0 ∨
            i - (1 + ((sgOf cur).h + (sgOf cur).g)) = 1) with e | e
          · rw [e]; rfl
          · rw [e]
            show some [Fmt.ItemValue.answer (ofE (aAns p j cur next o D _ _))] =
              some [Fmt.ItemValue.answer (ofE (aAns p j cur next o D' _ _))]
            rw [aAns_congr p j cur next o D D' _ _ (h _ (by omega))]
        · rw [get3_mid _ _ _ i (by rw [hm]; omega) (by rw [hm]; show i < _ + 2; omega),
            get3_mid _ _ _ i (by rw [hm]; omega) (by rw [hm]; show i < _ + 2; omega)]
      · have h1 := h (o + 1 + ((sgOf cur).h + (sgOf cur).g)) (by omega)
        have h2 := h (o + 2 + ((sgOf cur).h + (sgOf cur).g)) (by omega)
        rw [← aAns_congr p j cur next o D D' _ _ h1, ← aSwitch_congr cur o D D' _ h1 h2,
          ← aRec3_congr p rest.isEmpty j cur next l o trees D D' _ _ h2]
        have ih := stagesAll_causal p K rest (j + 1) next (l.drop (cur.k + 3))
          (o + ((sgOf cur).h + (sgOf cur).g) + 3)
          (aRec3 p rest.isEmpty j cur next l o trees D
            (aRec1 p j cur l t (aFold K j cur o P (rowOf t) D))
            (aSwitch cur o D (aAns p j cur next o D
              (aRec1 p j cur l t (aFold K j cur o P (rowOf t) D))
              (aNext K rest.isEmpty j cur next o P D))))
          (aNext K rest.isEmpty j cur next o P D)
          [((sgOf next).C.a, aCol rest.isEmpty next (aNext K rest.isEmpty j cur next o P D))] D D'
          (i - (1 + ((sgOf cur).h + (sgOf cur).g) + 2)) fun n hn => h n (by omega)
        constructor
        · rw [get3_right _ _ _ i (by rw [hlen, l2]; omega),
            get3_right _ _ _ i (by rw [hlen, l2]; omega), hlen, l2]
          exact ih.1
        · rw [get3_right _ _ _ i (by rw [hm]; show _ + 2 ≤ i; omega),
            get3_right _ _ _ i (by rw [hm]; show _ + 2 ≤ i; omega), hm]
          exact ih.2

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.length_aFold
#print axioms ProofFile.Honest.K12.aFold_congr
#print axioms ProofFile.Honest.K12.aPoint_congr
#print axioms ProofFile.Honest.K12.aNext_congr
#print axioms ProofFile.Honest.K12.aAns_congr
#print axioms ProofFile.Honest.K12.aSwitch_congr
#print axioms ProofFile.Honest.K12.aRec3_congr
#print axioms ProofFile.Honest.K12.stagesAll_causal
