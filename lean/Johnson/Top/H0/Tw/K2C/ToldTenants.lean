-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/ToldTenants.lean: code switching (the kind K2): WHAT THE SWITCH's BLOCK
TELLS OF ITS SENDING NAMES EACH ANNOUNCED MESSAGE ONCE: the trees that the lot's maker tells
(oraclesAt, Johnson/Desc/ProofFile/Lot/K2OfPlan.lean) have, together, just as many tenants as
messages are announced. NO BLOCK IMPORTS THIS FILE.
  layTrees_shapes   what layTrees returns, with its trees' shapes written out
  lay_facts         the layout's two lists «tree» and «part» have one entry a message; tree number
                    τ has as many entries of main symbols as messages lie in it (cnt,
                    Johnson/Desc/Book/BookFits.lean)
  cnt_hit           below cnt tree τ N each number j is the part number of a message of tree τ
  sum_cnt           the trees' counts add up to the number of messages
  told_tenants      layTrees codes sent = some lay → ((oraclesAt grp codes sent).map fun o =>
                    o.tenants.length).sum = sent.size
On the plan alone. CALLED, NOT TYPED: fill_cnt · layTrees_fits · cnt (BookFits.lean) ·
lay_lt · laid_spec (OnBytes/Tie/Pv/Keeps/LayOne.lean). No soundness is claimed.

-/
import Johnson.Desc.ProofFile.Lot.K2OfPlan
import Johnson.Desc.Book.BookFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K2
open OnBytes
open OnBytes.Params (laidOf)
open OnBytes.Tie.Pv.Keeps.Fit (fillStep Blank laid_spec lay_lt)
open VerifiableInference.Desc.Book (cnt fill_cnt layTrees_fits LayFits)

theorem layTrees_shapes {codes : Codes} {sent : Array OracleNotice} {T : TreeLay}
    (h : layTrees codes sent = some T) :
    ∃ filled, (List.range sent.size).foldlM (fillStep codes sent (laidOf codes sent).2.2)
        ((laidOf codes sent).1, #[], Array.replicate (laidOf codes sent).1.size 0) = some filled ∧
      T.tree = (laidOf codes sent).2.2 ∧ T.part = filled.2.1 ∧
      T.shapes = filled.1.map fun t => if t.mainWidth == 0 then { t with logN := t.logNzk } else
          t := by
  unfold layTrees at h
  dsimp only at h
  obtain ⟨filled, hf, h2⟩ := Option.bind_eq_some_iff.mp h
  split at h2
  · rw [← Option.some.inj h2]
    exact ⟨filled, hf, rfl, rfl, rfl⟩
  · cases h2

theorem lay_facts {codes : Codes} {sent : Array OracleNotice} {T : TreeLay}
    (h : layTrees codes sent = some T) (h0 : 0 < sent.size) :
    T.tree.size = sent.size ∧ T.part.size = sent.size ∧
      ∀ τ, τ < T.shapes.size → (T.shapes.getD τ {}).mainSymbols.size = cnt T.tree τ sent.size := by
  obtain ⟨filled, hf, eT, eP, eS⟩ := layTrees_shapes h
  have hB : Blank (laidOf codes sent).1 := (laid_spec (codes := codes) h0).1.1
  have hz : (laidOf codes sent).2.2.size = sent.size := (laid_spec (codes := codes) h0).1.2
  have hr : ∀ j, j < sent.size → (laidOf codes sent).2.2.getD j 0 < (laidOf codes sent).1.size :=
    fun j hj => (laid_spec (codes := codes) hj).2.1
  obtain ⟨sz, ms, ps, _⟩ := fill_cnt codes sent _ _ _ hB hr sent.size filled (Nat.le_refl _) hf
  refine ⟨by rw [eT]; exact hz, by rw [eP]; exact ps, fun τ hτ => ?_⟩
  have hτ' : τ < filled.1.size := by
    rw [eS, Array.size_map] at hτ
    exact hτ
  rw [eT, ← ms τ (by rw [← sz]; exact hτ'), eS]
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map,
    Array.getElem?_eq_getElem hτ']
  show (if _ then _ else _ : TreeShape).mainSymbols.size = _
  split <;> rfl

theorem cnt_hit (tree : Array Nat) (τ : Nat) : ∀ (N j : Nat), j < cnt tree τ N →
    ∃ n, n < N ∧ tree.getD n 0 = τ ∧ cnt tree τ n = j
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | N + 1, j, h => by
    have e : cnt tree τ (N + 1) = cnt tree τ N + (if tree.getD N 0 = τ then 1 else 0) := rfl
    by_cases hj : j < cnt tree τ N
    · obtain ⟨n, h1, h2, h3⟩ := cnt_hit tree τ N j hj
      exact ⟨n, Nat.lt_succ_of_lt h1, h2, h3⟩
    · rw [e] at h
      by_cases ht : tree.getD N 0 = τ
      · rw [if_pos ht] at h
        exact ⟨N, Nat.lt_succ_self _, ht, by omega⟩
      · rw [if_neg ht] at h
        omega

theorem sum_one (a : Nat) : ∀ M : Nat,
    ((List.range M).map fun τ => if a = τ then 1 else 0).sum = if a < M then 1 else 0
  | 0 => rfl
  | M + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_one a M]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    split_ifs <;> omega

theorem sum_cnt (tree : Array Nat) (M : Nat) : ∀ N : Nat, (∀ n, n < N → tree.getD n 0 < M) →
    ((List.range M).map fun τ => cnt tree τ N).sum = N
  | 0, _ => by
    show ((List.range M).map fun _ => 0).sum = 0
    simp
  | N + 1, h => by
    have e : (fun τ => cnt tree τ (N + 1)) =
        fun τ => cnt tree τ N + (if tree.getD N 0 = τ then 1 else 0) := rfl
    rw [e, List.sum_map_add, sum_cnt tree M N fun n hn => h n (Nat.lt_succ_of_lt hn), sum_one,
      if_pos (h N (Nat.lt_succ_self _))]

theorem filterMap_all {α β : Type} (f : α → Option β) : ∀ l : List α,
    (∀ x ∈ l, (f x).isSome = true) → (l.filterMap f).length = l.length
  | [], _ => rfl
  | x :: l, h => by
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (h x (by simp))
    rw [List.filterMap_cons_some hy, List.length_cons, List.length_cons,
      filterMap_all f l fun z hz => h z (by simp [hz])]

/-- **The told trees' tenants are as many as the messages announced.** -/
theorem told_tenants {grp : Nat} {codes : Codes} {sent : Array OracleNotice} {lay : TreeLay}
    (h : layTrees codes sent = some lay) :
    ((oraclesAt grp codes sent).map fun o => o.tenants.length).sum = sent.size := by
  by_cases h0 : 0 < sent.size
  · obtain ⟨zt, zp, hs⟩ := lay_facts h h0
    have hF : LayFits sent.size lay := layTrees_fits h
    unfold oraclesAt
    rw [h]
    simp only [List.map_map]
    have key : ∀ x ∈ lay.shapes.toList.zipIdx,
        ((fun o : VerifiableInference.Desc.Oracle => o.tenants.length) ∘ fun x : TreeShape × Nat =>
          ({ logLength := x.1.logN, words := x.1.mainWidth + x.1.maskWidth
             tenants := (List.range x.1.mainSymbols.size).filterMap fun j =>
               ((List.range sent.size).find? fun n =>
                 lay.tree.getD n noId == x.2 && lay.part.getD n noId == j).map fun n =>
                 { main := x.1.mainSymbols.getD j 0, mask := x.1.maskSymbols.getD j 0,
                   degree := (sent.getD n default).shape.mainDeg,
                   sampled := (sent.getD n default).shape.answers != 0,
                   groups := if (sent.getD n default).shape.answers != 0 then [grp] else [] } } :
            VerifiableInference.Desc.Oracle)) x = cnt lay.tree x.2 sent.size := by
      rintro ⟨t, i⟩ hx
      have hi := List.mem_zipIdx hx
      have hlt : i < lay.shapes.size := by simpa using hi.2.1
      have ht : lay.shapes.getD i {} = t := by
        have := hi.2.2
        simp only [Nat.sub_zero, Array.getElem_toList] at this
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt, this]
        rfl
      have hsz : t.mainSymbols.size = cnt lay.tree i sent.size := by rw [← ht]; exact hs i hlt
      show ((List.range t.mainSymbols.size).filterMap _).length = _
      rw [filterMap_all, List.length_range, hsz]
      intro j hj
      have hj' : j < cnt lay.tree i sent.size := by rw [← hsz]; exact List.mem_range.1 hj
      obtain ⟨n, hn, e1, e2⟩ := cnt_hit lay.tree i sent.size j hj'
      rw [Option.isSome_map, List.find?_isSome]
      refine ⟨n, List.mem_range.2 hn, ?_⟩
      have g1 : lay.tree.getD n noId = lay.tree.getD n 0 := by
        rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
          Array.getElem?_eq_getElem (by rw [zt]; exact hn)]
        rfl
      have g2 : lay.part.getD n noId = lay.part.getD n 0 := by
        rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
          Array.getElem?_eq_getElem (by rw [zp]; exact hn)]
        rfl
      rw [g1, g2, e1, (hF n hn).2, e1, e2]
      simp
    rw [List.map_congr_left key]
    have e : (lay.shapes.toList.zipIdx.map fun x => cnt lay.tree x.2 sent.size) =
        (List.range lay.shapes.size).map fun τ => cnt lay.tree τ sent.size := by
      rw [show (fun x : TreeShape × Nat => cnt lay.tree x.2 sent.size) =
        (fun τ => cnt lay.tree τ sent.size) ∘ Prod.snd from rfl, ← List.map_map,
        List.zipIdx_map_snd, List.range_eq_range']
      simp
    rw [e]
    exact sum_cnt lay.tree lay.shapes.size sent.size fun n hn => lay_lt h hn
  · have hz : sent.size = 0 := by omega
    obtain ⟨filled, hf, _, _, eS⟩ := layTrees_shapes h
    have hl : (laidOf codes sent).1.size = 0 := by
      unfold laidOf
      simp [Params.layPass, hz]
    have hsz : lay.shapes.size = 0 := by rw [OnBytes.Params.layTrees_size h]; exact hl
    unfold oraclesAt
    rw [h, hz]
    have : lay.shapes.toList = [] := by
      rw [← List.length_eq_zero_iff]
      simpa using hsz
    simp [this]

end P1K2

#print axioms P1K2.lay_facts
#print axioms P1K2.sum_cnt
#print axioms P1K2.told_tenants
