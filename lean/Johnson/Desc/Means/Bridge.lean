-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Means/Bridge.lean: a group's row that is clean reads tables on the members' blocks
alone.

A table that is read off what a prover has sent can hold anything at an index whose row is in no
member's block. A group's row that has no coefficient there (Clean) does not see it. This file
shows: a clean group's row has the same value on any two tables that agree on the members' blocks
and on the kept members' main tables (groupValue_clean). So the laws of the laying and of the
batching hold for all tables that hold the words on the blocks (LaidOn): nothing is asked of the
tables elsewhere.

Main definitions: AgreeOn, LaidOn, LaidReal, padded.
Main theorems: groupValue_clean, laidOn_agree, groupValue_laidOn, rowMeans_on, combine_on,
padded_is, laidOn_of_real; RowIn.addScaled, combineRows_in.

On the rows beyond the real ones. A member's block has 2^(row bits) rows, of which the message has
the first ones; nobody sends the others. A row can have coefficients there. LaidReal says of tables
that they hold the words on the real rows and 0 on the others; no theorem here shows it of a table.
Tables that meet it hold, on the blocks, words that are 0 on these rows too (Padded):
laidOn_of_real, which asks Padded. Whoever makes words out of messages chooses the values on these
rows; padded makes them 0.

What is not claimed. That a table which a proximity test decodes meets LaidOn. Nothing on soundness.

-/
import Johnson.Desc.Means.Tables
import Johnson.Desc.Means.Combine

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means

open Model (Reading)

variable {K : Type} [CommRing K] (ρ : Reading K)
variable {S : Statement} {G : Group} {L : GroupLayout}

/-- Two tables agree at every index whose row is in a member's block, and on every kept member's
main table. -/
structure AgreeOn (S : Statement) (L : GroupLayout) (T T' : Tables K) : Prop where
  main : ∀ J < 2 ^ (L.k + L.logEll), ¬ OffMain S L J → T.main J = T'.main J
  mask : ∀ J < 2 ^ (L.h + L.logEllZk), ¬ OffMask S L J → T.mask J = T'.mask J
  kept : ∀ o, KeptAt L o → ∀ i < tableSize S o .main, T.kept o i = T'.kept o i

/-- **A clean group's row has the same value on tables that agree on the blocks.** -/
theorem groupValue_clean {R : GroupRow} {T T' : Tables K} (hc : Clean ρ S L R)
    (hA : AgreeOn S L T T') : groupValue ρ S L R T = groupValue ρ S L R T' := by
  unfold groupValue
  congr 1
  · congr 1
    · apply Finset.sum_congr rfl
      intro J hJ
      by_cases h : OffMain S L J
      · rw [hc.main J h, zero_mul, zero_mul]
      · rw [hA.main J (Finset.mem_range.1 hJ) h]
    · apply Finset.sum_congr rfl
      intro J hJ
      by_cases h : OffMask S L J
      · rw [hc.mask J (Finset.mem_range.1 hJ) h, zero_mul, zero_mul]
      · rw [hA.mask J (Finset.mem_range.1 hJ) h]
  · apply Finset.sum_congr rfl
    intro o _
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : KeptAt L o
    · rw [hA.kept o h i (Finset.mem_range.1 hi)]
    · rw [hc.kept o h i, zero_mul, zero_mul]

/-- The tables hold the words on the members' blocks and on the kept members' main tables. Nothing
is said of the tables elsewhere. -/
structure LaidOn (S : Statement) (L : GroupLayout) (m : Words K) (T : Tables K) : Prop where
  main_at : ∀ o i first, L.find o = some i → L.kept.getD i false = false →
    L.mainFirst.getD i none = some first → ∀ idx < tableSize S o .main,
      T.main (groupIndex idx (S.rowBits o .main) first L.k) = m o .main idx
  mask_at : ∀ o i first, L.find o = some i → L.maskFirst.getD i none = some first →
    ∀ idx < tableSize S o .mask,
      T.mask (groupIndex idx (S.rowBits o .mask) first L.h) = m o .mask idx
  kept_at : ∀ o i, L.find o = some i → L.kept.getD i false = true →
    ∀ idx < tableSize S o .main, T.kept o idx = m o .main idx

/-- Such tables agree on the blocks with the tables as the words fill them. -/
theorem laidOn_agree (F : LayFacts S G L) {m : Words K} {T : Tables K} (hT : LaidOn S L m T) :
    AgreeOn S L T (tablesOf S L m) := by
  refine ⟨fun J hJ h => ?_, fun J hJ h => ?_, fun o h i hi => ?_⟩
  · have hex : ∃ o i first, L.find o = some i ∧ L.kept.getD i false = false ∧
        L.mainFirst.getD i none = some first ∧ InBlock J (S.rowBits o .main) first L.k := by
      by_contra c
      exact h fun o i first hf hk hm hin => c ⟨o, i, first, hf, hk, hm, hin⟩
    obtain ⟨o, i, first, hf, hk, hm, hin⟩ := hex
    have hb := (F.main_block o i first hf hm).2.2
    have e := groupIndex_unshift J _ first L.k hb hin
    have hlt : unshift (S.rowBits o .main) (L.k - S.rowBits o .main) J < tableSize S o .main := by
      rw [F.mainSize hf hm]
      exact unshift_lt J _ first L.k L.logEll hb hJ
    rw [← e, hT.main_at o i first hf hk hm _ hlt, tablesOf_main_at F m hf hm]
  · have hex : ∃ o i first, L.find o = some i ∧
        L.maskFirst.getD i none = some first ∧ InBlock J (S.rowBits o .mask) first L.h := by
      by_contra c
      exact h fun o i first hf hm hin => c ⟨o, i, first, hf, hm, hin⟩
    obtain ⟨o, i, first, hf, hm, hin⟩ := hex
    have hb := (F.mask_block o i first hf hm).2
    have e := groupIndex_unshift J _ first L.h hb hin
    have hlt : unshift (S.rowBits o .mask) (L.h - S.rowBits o .mask) J < tableSize S o .mask := by
      rw [F.maskSize hf hm]
      exact unshift_lt J _ first L.h L.logEllZk hb hJ
    rw [← e, hT.mask_at o i first hf hm _ hlt, tablesOf_mask_at F m hf hm]
  · obtain ⟨j, hf, hk⟩ := h
    rw [hT.kept_at o j hf hk i hi, tablesOf_kept_at m ⟨j, hf, hk⟩]

/-- A clean group's row has on such tables the value that it has on the tables as the words fill
them. -/
theorem groupValue_laidOn (F : LayFacts S G L) {R : GroupRow} (hc : Clean ρ S L R) {m : Words K}
    {T : Tables K} (hT : LaidOn S L m T) :
    groupValue ρ S L R T = groupValue ρ S L R (tablesOf S L m) :=
  groupValue_clean ρ hc (laidOn_agree F hT)

/-- **A row laid on a group's tables holds of them just if it holds of the words**, for all tables
that hold the words on the blocks, whatever they hold elsewhere. -/
theorem rowMeans_on (S : Statement) (g : Nat) (G : Group) (L : GroupLayout) (row : Row)
    (hG : S.groups[g]? = some G) (hL : S.layout g = some L) (hOk : GroupOk S G)
    (hr : RowIn S G row) :
    ∃ R, addToGroupRow S L row oneE { group := g } = some R ∧ Clean ρ S L R ∧
      ∀ (m : Words K) (T : Tables K), LaidOn S L m T →
        (GroupSays ρ S L R T ↔ Says ρ S row m) := by
  have F := layFacts hG hL hOk
  obtain ⟨R, h, c, e⟩ := rowMeans ρ S g G L row hG hL hOk hr
  refine ⟨R, h, c, fun m T hT => ?_⟩
  rw [← e m]
  unfold GroupSays
  rw [groupValue_laidOn ρ F c hT]

/-- **The batching**, for all tables that hold the words on the blocks, whatever they hold
elsewhere. -/
theorem combine_on (S : Statement) (g : Nat) (G : Group) (L : GroupLayout) (rows : Array Row)
    (x : E) (hG : S.groups[g]? = some G) (hL : S.layout g = some L) (hOk : GroupOk S G)
    (hr : ∀ r ∈ rows.toList, RowIn S G r) :
    ∃ out, Bat.combine S g ⟨L, rows⟩ x = some out ∧ MaskReady L out ∧ Clean ρ S L out ∧
      ∀ (m : Words K) (T : Tables K), LaidOn S L m T → groupShort ρ S L out T =
        hornerSum (ρ.val x) (rows.toList.map fun r => short ρ S r m) := by
  have F := layFacts hG hL hOk
  obtain ⟨out, h, p, c, e⟩ := combine_means ρ S g G L rows x hG hL hOk hr
  refine ⟨out, h, p, c, fun m T hT => ?_⟩
  rw [← e m]
  unfold groupShort
  rw [groupValue_laidOn ρ F c hT]

/-! ## The rows beyond the real ones -/

/-- The words with 0 on the rows beyond the real ones. -/
def padded (S : Statement) (m : Words K) : Words K := fun o part i =>
  if i % 2 ^ S.rowBits o part < realRows S o part then m o part i else 0

theorem padded_is (S : Statement) (m : Words K) : Padded S (padded S m) := by
  intro o part i h
  unfold padded
  rw [if_neg (Nat.not_lt.2 h)]

/-- The tables hold the words on the real rows of the members' blocks and of the kept members' main
tables, and 0 on the rows of these beyond the real ones. -/
structure LaidReal (S : Statement) (L : GroupLayout) (m : Words K) (T : Tables K) : Prop where
  main_at : ∀ o i first, L.find o = some i → L.kept.getD i false = false →
    L.mainFirst.getD i none = some first → ∀ idx < tableSize S o .main,
      T.main (groupIndex idx (S.rowBits o .main) first L.k) =
        if idx % 2 ^ S.rowBits o .main < realRows S o .main then m o .main idx else 0
  mask_at : ∀ o i first, L.find o = some i → L.maskFirst.getD i none = some first →
    ∀ idx < tableSize S o .mask,
      T.mask (groupIndex idx (S.rowBits o .mask) first L.h) =
        if idx % 2 ^ S.rowBits o .mask < realRows S o .mask then m o .mask idx else 0
  kept_at : ∀ o i, L.find o = some i → L.kept.getD i false = true →
    ∀ idx < tableSize S o .main, T.kept o idx =
      if idx % 2 ^ S.rowBits o .main < realRows S o .main then m o .main idx else 0

/-- **Where Padded is asked**: tables that hold 0 on the rows that nobody sent hold, on the blocks,
words that are 0 there. -/
theorem laidOn_of_real {m : Words K} {T : Tables K} (hp : Padded S m) (h : LaidReal S L m T) :
    LaidOn S L m T := by
  have e : ∀ o part idx,
      (if idx % 2 ^ S.rowBits o part < realRows S o part then m o part idx else 0) =
        m o part idx := by
    intro o part idx
    by_cases c : idx % 2 ^ S.rowBits o part < realRows S o part
    · rw [if_pos c]
    · rw [if_neg c, hp o part idx (Nat.le_of_not_lt c)]
  exact ⟨fun o i first hf hk hm idx hi => by rw [h.main_at o i first hf hk hm idx hi, e],
    fun o i first hf hm idx hi => by rw [h.mask_at o i first hf hm idx hi, e],
    fun o i hf hk idx hi => by rw [h.kept_at o i hf hk idx hi, e]⟩

/-! ## Rows that stay rows -/

theorem ok_scale (v : Tensor) (x : E) : (v.scale x).ok = v.ok := by
  have e1 : (v.scale x).denseVars = v.denseVars := by
    unfold Tensor.scale
    rfl
  have e2 : (v.scale x).pairs = v.pairs := by
    unfold Tensor.scale
    rfl
  have e3 : (v.scale x).first = v.first := by
    unfold Tensor.scale
    rfl
  have e4 : (v.scale x).values = v.values := by
    unfold Tensor.scale
    rfl
  unfold Tensor.ok
  rw [Tensor.vars_scale, e1, e2, e3, e4]

theorem fits_scale (f : Form) (x : E) (vars : Nat) : (f.scale x).fits vars = f.fits vars := by
  unfold Form.fits Form.scale
  simp only [List.all_map, Function.comp_def, Tensor.vars_scale, ok_scale]

/-- A row plus a multiple of another passes the tests if both do. -/
theorem RowIn.addScaled {r other : Row} (hr : RowIn S G r) (ho : RowIn S G other) (x : E) :
    RowIn S G (r.addScaled other x) := by
  have ht : (r.addScaled other x).terms =
      r.terms ++ other.terms.map fun t => { t with v := t.v.scale x } := rfl
  have hu : (r.addScaled other x).units =
      r.units ++ other.units.map fun u => { u with coeff := mulE u.coeff x } := rfl
  have hm : (r.addScaled other x).runs = other.runs.foldl (mergeRun x) r.runs := rfl
  have hf : (r.addScaled other x).forms =
      r.forms ++ other.forms.map fun f => { f with c := f.c.scale x } := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ht]
    intro t h
    simp only [Array.toList_append, Array.toList_map, List.mem_append, List.mem_map] at h
    rcases h with c | ⟨v, hv, rfl⟩
    · exact hr.terms t c
    · show Blk.placeOk S G v.oracle v.part (v.v.scale x).vars 0 = true
      rw [Tensor.vars_scale]
      exact ho.terms v hv
  · rw [hu]
    intro u h
    simp only [Array.toList_append, Array.toList_map, List.mem_append, List.mem_map] at h
    rcases h with c | ⟨v, hv, rfl⟩
    · exact hr.units u c
    · exact ho.units v hv
  · rw [hm, ← Array.foldl_toList]
    exact foldl_mergeRun_in x _ _ ho.runs hr.runs
  · rw [hf]
    intro f h
    simp only [Array.toList_append, Array.toList_map, List.mem_append, List.mem_map] at h
    rcases h with c | ⟨v, hv, rfl⟩
    · exact hr.forms f c
    · exact ⟨(ho.forms v hv).1, by rw [fits_scale]; exact (ho.forms v hv).2⟩

/-- The batched row of rows that stay rows passes the tests if they all do. -/
theorem combineRows_in (rows : Array Row) (x : E) (h : ∀ r ∈ rows.toList, RowIn S G r) :
    RowIn S G (Bat.combineRows rows x) := by
  have gen : ∀ (l : List Row) (s : Row × E), (∀ r ∈ l, RowIn S G r) → RowIn S G s.1 →
      RowIn S G (l.foldl (fun (s : Row × E) r => (s.1.addScaled r s.2, mulE s.2 x)) s).1 := by
    intro l
    induction l with
    | nil => intro s _ hs; exact hs
    | cons r l ih =>
      intro s hl hs
      rw [List.foldl_cons]
      exact ih _ (fun a ha => hl a (by simp [ha])) (hs.addScaled (hl r (by simp)) s.2)
  unfold Bat.combineRows
  rw [← Array.foldl_toList]
  exact gen rows.toList _ h ⟨by simp, by simp, by simp, by simp⟩

end OnBytes.Means
