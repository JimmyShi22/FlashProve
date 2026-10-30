-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/LongMasks.lean: WHAT STANDS IN THE MASK TABLE AND IN THE LIST OF KEPT
SYMBOLS THAT THE TEXT LAYS OF THE MEMBERS' COLUMNS AT ONE POSITION (`layMembers`,
Johnson/Desc/Own/Symbols.lean): LongTables.lean's laws on the main table, for the two other tables.
Theorems. No text already in the library turns.

  `OffMask L n w i`: row i lies outside member w's block of n rows of the mask table.
  `mask_off`: a row outside every laid member's block holds what it held. `mask_laid`: **at a member
    w of the list laid (no number twice), at a row maskFirst w + j that lies outside every other
    member's block: that row holds w's column's mask symbol j** (kept or not: every member's mask
    rows are laid).
  `keptOf L opened i ws`: the kept members' main symbols, one member after the other.
  `kept_laid`: **the list of kept symbols behind the laying is what it was, then keptOf.**
Limits. «Outside every other member's block» is a premise: the layout's blocks are apart. Nothing on
the typed arrangement. Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.LongTables

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Slice
open VerifiableInference.Desc.Own (Tables layFrom layRows layMember layMembers)

/-- Row i lies outside member w's block of the mask table. -/
def OffMask (L : GroupLayout) (n : ℕ) (w i : ℕ) : Prop :=
  ∀ f, L.maskFirst.getD w none = some f → i < f ∨ f + n ≤ i

theorem layMember_maskOff {L : GroupLayout} {w : ℕ} {col : Column} {t t' : Tables}
    (h : layMember L w col t = some t') {i : ℕ} (hi : OffMask L col.mask.size w i) :
    t'.mask.getD i zeroE = t.mask.getD i zeroE := by
  unfold layMember at h
  obtain ⟨mask, hm, h2⟩ := Option.bind_eq_some_iff.1 h
  split at h2
  · rw [← Option.some.inj h2]
    exact layRows_off hm hi
  · obtain ⟨main, _, rfl⟩ := Option.map_eq_some_iff.1 h2
    exact layRows_off hm hi

theorem layMember_maskGet {L : GroupLayout} {w : ℕ} {col : Column} {t t' : Tables}
    (h : layMember L w col t = some t') {f : ℕ} (hf : L.maskFirst.getD w none = some f) {j : ℕ}
    (hj : j < col.mask.size) : t'.mask.getD (f + j) zeroE = col.mask.getD j zeroE := by
  unfold layMember at h
  obtain ⟨mask, hm, h2⟩ := Option.bind_eq_some_iff.1 h
  rw [hf] at hm
  split at h2
  · rw [← Option.some.inj h2]
    exact layRows_get hm hj
  · obtain ⟨main, _, rfl⟩ := Option.map_eq_some_iff.1 h2
    exact layRows_get hm hj

theorem mask_off (L : GroupLayout) (opened : Array (Array Column)) (i : ℕ) :
    ∀ (ws : List ℕ) (t t' : Tables), layMembers L opened i ws t = some t' → ∀ r,
      (∀ w ∈ ws, ∀ c, colAt opened i w = some c → OffMask L c.mask.size w r) →
      t'.mask.getD r zeroE = t.mask.getD r zeroE
  | [], t, t', h, _, _ => by rw [← Option.some.inj h]
  | w :: ws, t, t', h, r, ho => by
    unfold layMembers at h
    obtain ⟨col, hc, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨t₁, h1, h3⟩ := Option.bind_eq_some_iff.1 h2
    rw [mask_off L opened i ws t₁ t' h3 r fun w' hw' => ho w' (List.mem_cons_of_mem _ hw'),
      layMember_maskOff h1 (ho w List.mem_cons_self col hc)]

/-- **WHAT STANDS IN THE MASK TABLE.** -/
theorem mask_laid (L : GroupLayout) (opened : Array (Array Column)) (i : ℕ) :
    ∀ (ws : List ℕ) (t t' : Tables), layMembers L opened i ws t = some t' → ws.Nodup →
      ∀ w ∈ ws, ∀ f, L.maskFirst.getD w none = some f →
      ∀ c, colAt opened i w = some c → ∀ j, j < c.mask.size →
      (∀ w' ∈ ws, w' ≠ w → ∀ c', colAt opened i w' = some c' →
        OffMask L c'.mask.size w' (f + j)) →
      t'.mask.getD (f + j) zeroE = c.mask.getD j zeroE
  | [], _, _, _, _, _, hw, _, _, _, _, _, _, _ => nomatch hw
  | v :: ws, t, t', h, nd, w, hw, f, hf, c, hc, j, hj, ho => by
    unfold layMembers at h
    obtain ⟨col, hcol, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨t₁, h1, h3⟩ := Option.bind_eq_some_iff.1 h2
    obtain ⟨nv, nd'⟩ := List.nodup_cons.1 nd
    rcases List.mem_cons.1 hw with rfl | hw'
    · obtain rfl : col = c := Option.some.inj (hcol.symm.trans hc)
      rw [mask_off L opened i ws t₁ t' h3 (f + j) fun w' hw' c' hc' =>
        ho w' (List.mem_cons_of_mem _ hw') (fun e => nv (e ▸ hw')) c' hc']
      exact layMember_maskGet h1 hf hj
    · exact mask_laid L opened i ws t₁ t' h3 nd' w hw' f hf c hc j hj fun w' hw'' hne =>
        ho w' (List.mem_cons_of_mem _ hw'') hne

/-- The kept members' main symbols, one member after the other. -/
def keptOf (L : GroupLayout) (opened : Array (Array Column)) (i : ℕ) : List ℕ → Array E
  | [] => #[]
  | w :: ws =>
    (if L.kept.getD w false then ((colAt opened i w).map (·.main)).getD #[] else #[]) ++
      keptOf L opened i ws

theorem keptOf_cons (L : GroupLayout) (opened : Array (Array Column)) (i w : ℕ) (ws : List ℕ) :
    keptOf L opened i (w :: ws) =
      (if L.kept.getD w false then ((colAt opened i w).map (·.main)).getD #[] else #[]) ++
        keptOf L opened i ws := rfl

/-- **THE KEPT SYMBOLS.** -/
theorem kept_laid (L : GroupLayout) (opened : Array (Array Column)) (i : ℕ) :
    ∀ (ws : List ℕ) (t t' : Tables), layMembers L opened i ws t = some t' →
      t'.kept = t.kept ++ keptOf L opened i ws
  | [], t, t', h => by
    rw [← Option.some.inj h]
    exact (Array.append_empty).symm
  | w :: ws, t, t', h => by
    unfold layMembers at h
    obtain ⟨col, hc, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨t₁, h1, h3⟩ := Option.bind_eq_some_iff.1 h2
    rw [kept_laid L opened i ws t₁ t' h3]
    have hc' : colAt opened i w = some col := hc
    unfold layMember at h1
    obtain ⟨mask, _, h4⟩ := Option.bind_eq_some_iff.1 h1
    rw [keptOf_cons, hc']
    by_cases hk : L.kept.getD w false = true
    · rw [if_pos hk] at h4 ⊢
      rw [← Option.some.inj h4]
      exact Array.append_assoc
    · rw [if_neg hk] at h4 ⊢
      obtain ⟨main, _, e⟩ := Option.map_eq_some_iff.1 h4
      rw [← e, Array.empty_append]

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.mask_off
#print axioms VerifiableInference.Desc.LinkJoin.mask_laid
#print axioms VerifiableInference.Desc.LinkJoin.kept_laid
