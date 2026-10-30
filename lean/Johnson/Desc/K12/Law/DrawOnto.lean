-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Run.DrawPageProofs
import Run.DrawBSProofs
import Run.PlanPull
/-
Johnson/Desc/K12/Law/DrawOnto.lean: EVERY TYPED VALUE OF A ROUND's DRAWS IS REACHED BY SOME HASH BLOCKS: the block sampler of a round (Run/DrawPage.lean: bsOf; Run/PlanDraws.lean: bsRound) IS ONTO, where every position has at most 64 bits. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
WHY: the lemma on the proximity test speaks of typed transcripts whose challenges are hash blocks (ckP); to show that a typed transcript exists whose written view is a given view, each round's drawn values must come from some blocks.
HOW: the library counts the rows of words with a given value EXACTLY (Tr.N with N_pair · N_pad · N_trF · N_trE · N_again · N_word_map · N_map · N_words; drawWord_low · bits_eq; tryNum): each count is shown positive; rowOf is a bijection between blocks and rows (row_unrow).
  pos_tree    each value of one draw has a row · pos_all   each tuple of values of a list of draws has a row
  phi_onto    (bsOf f ds).φ is onto Vals f ds, for lawful ds
  dr_onto     at e.logN ≤ 64: for every typed v : Ch f e k there are blocks u with (ckP f).dr e k u = drawnOf f e k v
WHAT IT DOES NOT SAY: ONTO, NOT UNIFORM (the library's Good bounds the bias) · which untyped records Fmt.Drawn are drawnOf of a typed value: another file's.
EVERY THEOREM OF THIS FILE IS PROVED OUTRIGHT: nothing is left open and nothing is laid down by decree; what each rests on is printed at the file's end.
-/
set_option autoImplicit false
namespace H2K.Onto
open Prob Iop Run

theorem exists_of_cnt_pos {α : Type} [Finite α] {P : α → Prop} (h : 0 < cnt P) : ∃ a, P a := by
  by_contra hn
  rw [cnt_false fun a ha => hn ⟨a, ha⟩] at h
  exact absurd h (lt_irrefl 0)

theorem geo_pos (F T n : ℕ) (hT : 0 < T) : 0 < geo F T (n + 1) :=
  Nat.lt_of_lt_of_le (pow_pos hT n) (Nat.le_add_right _ _)

theorem nGive_pos (f : Fmt.Fld) : 0 < nGive f := by cases f <;> decide

theorem card_pos : 0 < Fintype.card UInt64 := by
  rw [card_u64]
  exact pow_pos (by decide) 64

theorem pos_trF (f : Fmt.Fld) (a : FV f) : 0 < Tr.N (0 : UInt64) 6 (trF (okF f) (zF f)) a := by
  classical
  have hx : 0 < wx (nGive f) (nFail f) (Fintype.card UInt64) :=
    Nat.mul_pos (nGive_pos f) (geo_pos _ _ 5 card_pos)
  rw [N_trF 0 (tryNum f)]
  split
  · exact Nat.lt_of_lt_of_le hx (wx_le_w0 _ _ _)
  · exact hx

theorem pos_trE (f : Fmt.Fld) (x : EV f) : 0 < Tr.N (0 : UInt64) 18 (trE (okF f) (zF f)) x := by
  rw [N_trE]
  exact Nat.mul_pos (pos_trF f _) (Nat.mul_pos (pos_trF f _) (pos_trF f _))

theorem pos_trNZ (f : Fmt.Fld) (c : NZ f) :
    0 < Tr.N (0 : UInt64) 36 (trNZ (okF f) (zF f) (oE f)) c := by
  show 0 < Tr.N (0 : UInt64) (18 + 18) ((trE (okF f) (zF f)).again (zF f, zF f, zF f) (oE f)) c
  rw [Tr.N_again 0 (most_trE _ _)]
  exact Nat.lt_of_lt_of_le (Nat.mul_pos (pos_trE f c.1) (pow_pos card_pos 18))
    (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))

theorem N_trMany {C : Type} (k : ℕ) (g : (Fin k → UInt64) → C) (c : C) :
    Tr.N (0 : UInt64) k (trMany k g) c = cnt fun u => g u = c := by
  classical
  have e := N_map (0 : UInt64) (Tr.most_vec (Tr.most_word (W := UInt64)) k) g c
  simp_rw [N_words] at e
  rw [Nat.mul_one] at e
  show Tr.N (0 : UInt64) k ((Tr.vec k Tr.word).map g) c = _
  rw [e, ← Finset.sum_filter, Finset.sum_const, ← cnt_eq_card_filter, smul_eq_mul, mul_one]

/-- Each value of one draw has a row of words. -/
theorem pos_tree (f : Fmt.Fld) (d : Fmt.Draw) (hd : Lawful d) (c : DVal f d) :
    0 < Tr.N (0 : UInt64) d.most (tree f d) c := by
  cases d with
  | elem => exact pos_trE f c
  | elemNZ => exact pos_trNZ f c
  | pos k =>
    show 0 < Tr.N (0 : UInt64) 1 (Tr.ask fun w => Tr.ret (low k w)) c
    rw [Tr.N_word_map, drawWord_low k hd]
    exact pow_pos (by decide) _
  | trits n =>
    show 0 < Tr.N (0 : UInt64) ((n + 31) / 32) (trMany ((n + 31) / 32) (bitsOf n)) c
    rw [N_trMany, bits_eq]
    exact pow_pos (by decide) _
  | sealed =>
    show 0 < Tr.N (0 : UInt64) 4 (trMany 4 (id : (Fin 4 → UInt64) → Fin 4 → UInt64)) c
    rw [N_trMany]
    have : cnt (fun u : Fin 4 → UInt64 => id u = c) = 1 := cnt_eq_const c
    rw [this]
    exact Nat.one_pos

/-- Each tuple of values of a list of draws has a row of words. -/
theorem pos_all (f : Fmt.Fld) : ∀ (ds : List Fmt.Draw), (∀ d ∈ ds, Lawful d) → ∀ v : Vals f ds,
    0 < Tr.N (0 : UInt64) (Fmt.mostAll ds) (all f ds) v
  | [], _, v => by
    show 0 < Tr.N (0 : UInt64) 0 (Tr.ret () : Tr UInt64 Unit) v
    rw [Tr.N_ret]
    split
    · exact pow_pos card_pos 0
    · rename_i h
      exact absurd rfl h
  | d :: ds, h, (c, v) => by
    haveI := finite_DVal f d
    haveI := finite_Vals f ds
    haveI : Fintype (DVal f d) := Fintype.ofFinite _
    haveI : Fintype (Vals f ds) := Fintype.ofFinite _
    have hd := h d List.mem_cons_self
    have hds : ∀ d' ∈ ds, Lawful d' := fun d' hd' => h d' (List.mem_cons_of_mem _ hd')
    show 0 < Tr.N (0 : UInt64) (d.most + Fmt.mostAll ds) ((tree f d).pair (all f ds)) (c, v)
    rw [Tr.N_pair 0 (drawPage_one f d hd).1.most (drawPage_all f ds hds).1.most]
    exact Nat.mul_pos (pos_tree f d hd c) (pos_all f ds hds v)

/-- The block sampler of a list of lawful draws is onto. -/
theorem phi_onto (f : Fmt.Fld) (ds : List Fmt.Draw) (h : ∀ d ∈ ds, Lawful d) (v : Vals f ds) :
    ∃ u, (bsOf f ds).φ u = v := by
  obtain ⟨j, hj⟩ : ∃ j, 4 * ((Fmt.mostAll ds + 3) / 4) = Fmt.mostAll ds + j :=
    ⟨4 * ((Fmt.mostAll ds + 3) / 4) - Fmt.mostAll ds, by omega⟩
  have hp : 0 < Tr.N (0 : UInt64) (4 * ((Fmt.mostAll ds + 3) / 4)) (all f ds) v := by
    rw [hj, Tr.N_pad 0 (drawPage_all f ds h).1.most]
    exact Nat.mul_pos (pos_all f ds h v) (pow_pos card_pos j)
  obtain ⟨row, hrow⟩ := exists_of_cnt_pos hp
  refine ⟨unrow e64 _ row, ?_⟩
  show (all f ds).ev 0 (4 * ((Fmt.mostAll ds + 3) / 4)) (rowOf e64 _ (unrow e64 _ row)) = v
  rw [row_unrow]
  exact hrow

/-- Every typed value of a round's draws is the sampler's value at some blocks. -/
theorem dr_onto (f : Fmt.Fld) (e : Fmt.Entry) (k : Fmt.Kind) (h : e.logN ≤ 64) (v : Ch f e k) :
    ∃ u : (ckP f).Ch e k, (ckP f).dr e k u = drawnOf f e k v := by
  obtain ⟨u, hu⟩ := phi_onto f (Fmt.dsOf e k) (lawful_dsOf e k h) v
  exact ⟨u, congrArg (drawnOf f e k) hu⟩

end H2K.Onto

#print axioms H2K.Onto.phi_onto
#print axioms H2K.Onto.dr_onto
