-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/BodyCausal.lean: WHAT bodyAll (Johnson/Prover/Link/BodyAll.lean) SHOWS IN A
ROUND HANGS ON THE DRAWS IN FRONT OF THAT ROUND ALONE. Statements and proofs.

  ptK_congr, showRV_congr, foldRV_congr   equal draws, equal rounds
  bodyAll_causal   two families of draws that agree below o + i: the round at place i shows the same
                   items and sends the same tree

So a function of the draws so far can be cut out of bodyAll. Not shown here: that any part says
yes. Nothing on soundness; nothing on what any value that is sent discloses or does not disclose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.BodyAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (sgOf)

theorem ptK_congr : ∀ (k : ℕ) (f f' : ℕ → GE), (∀ n, n < k → f n = f' n) → ptK k f = ptK k f'
  | 0, _, _, _ => rfl
  | k + 1, f, f', h => by
    show (f 0, ptK k fun n => f (n + 1)) = (f' 0, ptK k fun n => f' (n + 1))
    rw [h 0 (Nat.succ_pos k), ptK_congr k (fun n => f (n + 1)) (fun n => f' (n + 1))
      fun n hn => h (n + 1) (Nat.succ_lt_succ hn)]

theorem showRV_congr : ∀ (k : ℕ) (q : RIdx (sVars GE 2 k) → GE) (D D' : ℕ → Fmt.Drawn),
    (∀ n, n < k → D n = D' n) → showRV k q D = showRV k q D'
  | 0, _, _, _, _ => rfl
  | k + 1, q, D, D', h => by
    show _ :: showRV k _ (fun n => D (n + 1)) = _ :: showRV k _ (fun n => D' (n + 1))
    rw [h 0 (Nat.succ_pos k), showRV_congr k _ (fun n => D (n + 1)) (fun n => D' (n + 1))
      fun n hn => h (n + 1) (Nat.succ_lt_succ hn)]

theorem foldRV_congr (s : Sg) (v μ : s.cIn.J → GE) (W : HIdx (sVars GE 2 (s.h + s.g)) → GE)
    (D D' : ℕ → Fmt.Drawn) (h : ∀ n, n < 1 + (s.h + s.g) → D n = D' n) :
    foldRV s v μ W D = foldRV s v μ W D' := by
  have h0 : D 0 = D' 0 := h 0 (by omega)
  have hs : ∀ n, n < s.h + s.g → D (n + 1) = D' (n + 1) := fun n hn => h (n + 1) (by omega)
  unfold foldRV
  rw [h0, ptK_congr (s.h + s.g) (fun n => drawnE (D (n + 1))) (fun n => drawnE (D' (n + 1)))
    fun n hn => congrArg drawnE (hs n hn),
    showRV_congr (s.h + s.g) _ (fun n => D (n + 1)) (fun n => D' (n + 1)) hs]

/-! ## One stage -/

section Stage
variable (p : P12) (K : BCoins) (last : Bool) (j : ℕ) (cur next : Fmt.M1.Stage) (l : Laid) (o : ℕ)
  (t : T12) (P : PS) (col : ℕ → List UInt64) (row : GroupRow) (D D' : ℕ → Fmt.Drawn)

theorem length_sRF : (sRF K j cur o P row D).length = 1 + ((sgOf cur).h + (sgOf cur).g) :=
  length_foldRV _ _ _ _ _

theorem sRF_congr (h : ∀ n, n < o + (1 + ((sgOf cur).h + (sgOf cur).g)) → D n = D' n) :
    sRF K j cur o P row D = sRF K j cur o P row D' :=
  foldRV_congr _ _ _ _ _ _ fun n hn => h (o + n) (Nat.add_lt_add_left hn o)

theorem sNext_congr (h : sRF K j cur o P row D = sRF K j cur o P row D') :
    sNext K last j cur next o P row D = sNext K last j cur next o P row D' := by
  unfold sNext sGam
  rw [h]

theorem sCol_congr (h : sRF K j cur o P row D = sRF K j cur o P row D') :
    sCol K last j cur next o P row D = sCol K last j cur next o P row D' := by
  unfold sCol
  rw [sNext_congr K last j cur next o P row D D' h]

theorem sT1_congr (h : sRF K j cur o P row D = sRF K j cur o P row D') :
    sT1 p K j cur l o t P row D = sT1 p K j cur l o t P row D' := by
  unfold sT1
  rw [h]

theorem sAns_congr (h : sRF K j cur o P row D = sRF K j cur o P row D')
    (h1 : D (o + 1 + ((sgOf cur).h + (sgOf cur).g)) = D' (o + 1 + ((sgOf cur).h + (sgOf cur).g))) :
    sAns p K j cur next l o t P row D = sAns p K j cur next l o t P row D' := by
  unfold sAns sGam
  rw [h, h1, sT1_congr p K j cur l o t P row D D' h]

theorem sRS_congr (h : sRF K j cur o P row D = sRF K j cur o P row D')
    (h1 : D (o + 1 + ((sgOf cur).h + (sgOf cur).g)) = D' (o + 1 + ((sgOf cur).h + (sgOf cur).g)))
    (h2 : D (o + 2 + ((sgOf cur).h + (sgOf cur).g)) = D' (o + 2 + ((sgOf cur).h + (sgOf cur).g))) :
    sRS p K j cur next l o t P row D = sRS p K j cur next l o t P row D' := by
  unfold sRS
  rw [sAns_congr p K j cur next l o t P row D D' h h1, h1, h2]

theorem sT3_congr (h : sRF K j cur o P row D = sRF K j cur o P row D')
    (h1 : D (o + 1 + ((sgOf cur).h + (sgOf cur).g)) = D' (o + 1 + ((sgOf cur).h + (sgOf cur).g)))
    (h2 : D (o + 2 + ((sgOf cur).h + (sgOf cur).g)) = D' (o + 2 + ((sgOf cur).h + (sgOf cur).g))) :
    sT3 p K last j cur next l o t P col row D = sT3 p K last j cur next l o t P col row D' := by
  unfold sT3 sGS
  rw [sRS_congr p K j cur next l o t P row D D' h h1 h2, sT1_congr p K j cur l o t P row D D' h, h2]

end Stage

theorem vals_of_getD {l l' : List Fmt.RoundView} {i : ℕ} {d d' : Fmt.RoundView} (hl : i < l.length)
    (hl' : i < l'.length) (h : (l.getD i d).vals = (l'.getD i d').vals) :
    (l[i]?).map (·.vals) = (l'[i]?).map (·.vals) := by
  rw [List.getD_eq_getElem _ _ hl, List.getD_eq_getElem _ _ hl'] at h
  rw [List.getElem?_eq_getElem hl, List.getElem?_eq_getElem hl']
  exact congrArg some h

theorem get3_left {α : Type} (A B C : List α) (i : ℕ) (h : i < A.length) :
    (A ++ B ++ C)[i]? = A[i]? := by
  rw [List.append_assoc, List.getElem?_append_left h]

theorem get3_mid {α : Type} (A B C : List α) (i : ℕ) (h1 : A.length ≤ i)
    (h2 : i < A.length + B.length) : (A ++ B ++ C)[i]? = B[i - A.length]? := by
  rw [List.append_assoc, List.getElem?_append_right h1,
    List.getElem?_append_left (by omega)]

theorem get3_right {α : Type} (A B C : List α) (i : ℕ) (h : A.length + B.length ≤ i) :
    (A ++ B ++ C)[i]? = C[i - (A.length + B.length)]? := by
  rw [List.getElem?_append_right (by rw [List.length_append]; exact h), List.length_append]

/-- **What a round shows hangs on the draws in front of it alone.** -/
theorem bodyAll_causal (p : P12) (K : BCoins) : ∀ (rest : List Fmt.M1.Stage) (j : ℕ)
    (cur : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS) (col : ℕ → List UInt64)
    (D D' : ℕ → Fmt.Drawn) (i : ℕ), (∀ n, n < o + i → D n = D' n) →
    ((bodyAll p K rest j cur l o t P col D).rs[i]?).map (·.vals) =
        ((bodyAll p K rest j cur l o t P col D').rs[i]?).map (·.vals) ∧
      (bodyAll p K rest j cur l o t P col D).tr[i]? = (bodyAll p K rest j cur l o t P col D').tr[i]?
  | [], j, cur, l, o, t, P, col, D, D', 0, _ => ⟨rfl, rfl⟩
  | [], j, cur, l, o, t, P, col, D, D', 1, h => by
    have h0 : D o = D' o := h o (by omega)
    refine ⟨?_, rfl⟩
    show some ((shownAll _ _ ((D o).elems.headD (0, 0, 0)) _ _ _ _ _ _ _ _).map Fmt.ItemValue.e) =
      some ((shownAll _ _ ((D' o).elems.headD (0, 0, 0)) _ _ _ _ _ _ _ _).map Fmt.ItemValue.e)
    rw [h0]
  | [], j, cur, l, o, t, P, col, D, D', i + 2, _ => ⟨rfl, rfl⟩
  | next :: rest, j, cur, l, o, t, P, col, D, D', i, h => by
    have hlen := length_sRF K j cur o P (rowOf t) D
    have hlen' := length_sRF K j cur o P (rowOf t) D'
    show ((sRF K j cur o P (rowOf t) D ++ sRS p K j cur next l o t P (rowOf t) D ++
        (bodyAll p K rest _ _ _ _ _ _ _ D).rs)[i]?).map (·.vals) =
      ((sRF K j cur o P (rowOf t) D' ++ sRS p K j cur next l o t P (rowOf t) D' ++
        (bodyAll p K rest _ _ _ _ _ _ _ D').rs)[i]?).map (·.vals) ∧
      ((sRF K j cur o P (rowOf t) D).map (fun _ _ => []) ++
        [sCol K rest.isEmpty j cur next o P (rowOf t) D, fun _ => []] ++
        (bodyAll p K rest _ _ _ _ _ _ _ D).tr)[i]? =
      ((sRF K j cur o P (rowOf t) D').map (fun _ _ => []) ++
        [sCol K rest.isEmpty j cur next o P (rowOf t) D', fun _ => []] ++
        (bodyAll p K rest _ _ _ _ _ _ _ D').tr)[i]?
    have hm : ∀ E : ℕ → Fmt.Drawn, ((sRF K j cur o P (rowOf t) E).map
        (fun (_ : Fmt.RoundView) (_ : ℕ) => ([] : List UInt64))).length =
        1 + ((sgOf cur).h + (sgOf cur).g) := fun E => by
      rw [List.length_map]; exact length_sRF K j cur o P (rowOf t) E
    by_cases c1 : i < 1 + ((sgOf cur).h + (sgOf cur).g)
    · constructor
      · rw [get3_left _ _ _ i (by rw [hlen]; exact c1), get3_left _ _ _ i (by rw [hlen']; exact c1)]
        exact vals_of_getD (by rw [hlen]; exact c1) (by rw [hlen']; exact c1)
          (foldRV_vals _ _ _ _ (fun n => D (o + n)) (fun n => D' (o + n)) i
            fun n hn => h (o + n) (Nat.add_lt_add_left hn o))
      · rw [get3_left _ _ _ i (by rw [hm]; exact c1), get3_left _ _ _ i (by rw [hm]; exact c1),
          List.getElem?_map, List.getElem?_map, List.getElem?_eq_getElem (by rw [hlen]; exact c1),
          List.getElem?_eq_getElem (by rw [hlen']; exact c1)]
        rfl
    · have hF := sRF_congr K j cur o P (rowOf t) D D' fun n hn => h n (by omega)
      have hC := sCol_congr K rest.isEmpty j cur next o P (rowOf t) D D' hF
      have l2 : ∀ E : ℕ → Fmt.Drawn, (sRS p K j cur next l o t P (rowOf t) E).length = 2 :=
        fun _ => rfl
      by_cases c2 : i < 3 + ((sgOf cur).h + (sgOf cur).g)
      · constructor
        · rw [get3_mid _ _ _ i (by rw [hlen]; omega) (by rw [hlen, l2]; omega),
            get3_mid _ _ _ i (by rw [hlen']; omega) (by rw [hlen', l2]; omega), hlen, hlen']
          rcases (by omega : i - (1 + ((sgOf cur).h + (sgOf cur).g)) = 0 ∨
            i - (1 + ((sgOf cur).h + (sgOf cur).g)) = 1) with e | e
          · rw [e]; rfl
          · rw [e]
            show some [Fmt.ItemValue.answer (ofE (sAns p K j cur next l o t P (rowOf t) D))] =
              some [Fmt.ItemValue.answer (ofE (sAns p K j cur next l o t P (rowOf t) D'))]
            rw [sAns_congr p K j cur next l o t P (rowOf t) D D' hF (h _ (by omega))]
        · rw [get3_mid _ _ _ i (by rw [hm]; omega) (by rw [hm]; show i < _ + 2; omega),
            get3_mid _ _ _ i (by rw [hm]; omega) (by rw [hm]; show i < _ + 2; omega), hm, hm, hC]
      · have h1 := h (o + 1 + ((sgOf cur).h + (sgOf cur).g)) (by omega)
        have h2 := h (o + 2 + ((sgOf cur).h + (sgOf cur).g)) (by omega)
        have ih := bodyAll_causal p K rest (j + 1) next (l.drop (cur.k + 3))
          (o + ((sgOf cur).h + (sgOf cur).g) + 3)
          (sT3 p K rest.isEmpty j cur next l o t P col (rowOf t) D)
          (sNext K rest.isEmpty j cur next o P (rowOf t) D)
          (sCol K rest.isEmpty j cur next o P (rowOf t) D) D D'
          (i - (1 + ((sgOf cur).h + (sgOf cur).g) + 2)) fun n hn => h n (by omega)
        rw [← sT3_congr p K rest.isEmpty j cur next l o t P col (rowOf t) D D' hF h1 h2,
          ← sNext_congr K rest.isEmpty j cur next o P (rowOf t) D D' hF, ← hC]
        constructor
        · rw [get3_right _ _ _ i (by rw [hlen, l2]; omega),
            get3_right _ _ _ i (by rw [hlen', l2]; omega), hlen, hlen', l2, l2]
          exact ih.1
        · rw [get3_right _ _ _ i (by rw [hm]; show _ + 2 ≤ i; omega),
            get3_right _ _ _ i (by rw [hm]; show _ + 2 ≤ i; omega), hm, hm]
          exact ih.2

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.bodyAll_causal
#print axioms Johnson.Prover.Link.ptK_congr
#print axioms Johnson.Prover.Link.showRV_congr
#print axioms Johnson.Prover.Link.foldRV_congr
