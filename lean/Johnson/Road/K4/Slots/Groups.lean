-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Slots/Groups.lean: WHICH SLOTS THE FORMS OF K4's CLAIMS NAME, GROUP BY GROUP, at
K4's own text (OnBytes/Desc/First/K4/Claims.lean). Statements and proofs. The twin, for slots, of
the walk over the entries (Johnson/Road/K4/Reads/): the norms' rows' part is carried over from
NormRowEnts.lean by a program, but that the carries' and the lines' premises are asked at s < 9 and
at s < 7 alone; the rest is typed at K4's own functions.

Each theorem: every form that the group's function returns (a list; in group 3 one form, which is
always there; in group 11 a pair; in group 12 one form) is `SlotsIn S`, IF S HOLDS OF THE SLOTS THAT
THE TEXT NAMES BY NUMBER: these are premises, each a slot or a stretch of
slots (a ≤ j < a + n):
  `normsForms_slots` (group 2): the squares' layer's own claim; its two end values' slots.
  `rowBatchForm_slots` (group 3): the row products' claimed sum's slot; the products' stretch.
  `rowsForms_slots` (groups 4 to 6): the end values' stretch (4 a norm); the sums' (9 a norm); the
    products' (7 a norm).
  `termsForms_slots` (group 7): the second token sumcheck's end values' stretch.
  `gatedForms_slots` (groups 8, 9): each layer's own claim and its two end values' slots.
  `oneHotForms_slots` (group 10): no slot.
  `planesParts_slots` (group 11): what is kept names no slot; the two claims: the slot of the bit.
  `embeddingForm_slots` (group 12): the slot of the embedding's value.

Limits. NOTHING ON WHETHER THESE SLOTS ARE FILLED. One direction: the forms may name fewer slots.
Nothing on soundness.
-/
import Johnson.Road.K4.Slots.Readers
import Johnson.Road.K4.Reads.NormRowEnts

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 40000

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Desc.First.K4.Slots

open OnBytes OnBytes.Model OnBytes.Model.Layer
open OnBytes.Road OnBytes.Road.Rows
open OnBytes.Desc.First.K4.Reads (digs fa fb cst tms ofDigits_eq carries_eq lines_eq all_mapM)

variable {S : ℕ → Prop}

/-! ### Two rules on lists -/

/-- What holds of every value that a function returns at a member holds of all members of the
list. -/
theorem all_mapM_mem {α β : Type} {g : α → Option β} {Pr : β → Prop} :
    ∀ (xs : List α) (ys : List β), (∀ a ∈ xs, ∀ b, g a = some b → Pr b) →
      xs.mapM g = some ys → ∀ y ∈ ys, Pr y
  | [], ys, _, h, y, hy => by
    cases h
    cases hy
  | a :: xs, ys, hg, h, y, hy => by
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := bind_some h
    obtain ⟨bs, hbs, h⟩ := bind_some h
    cases h
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hg a List.mem_cons_self _ hb
    · exact all_mapM_mem xs bs (fun a' ha' => hg a' (List.mem_cons_of_mem _ ha')) hbs y hy

theorem mapM_length {α β : Type} {g : α → Option β} :
    ∀ (xs : List α) (ys : List β), xs.mapM g = some ys → ys.length = xs.length
  | [], ys, h => by
    cases h
    rfl
  | a :: xs, ys, h => by
    rw [List.mapM_cons] at h
    obtain ⟨b, _, h⟩ := bind_some h
    obtain ⟨bs, hbs, h⟩ := bind_some h
    cases h
    simp [mapM_length xs bs hbs]

/-! ### The norms' rows -/

theorem slotsIn_sumTo (n : ℕ) {f : ℕ → Aff} (h : ∀ i, SlotsIn S (f i)) :
    SlotsIn S (P6.sumTo n f) :=
  slotsIn_foldl _ (fun _ _ hf => slotsIn_add hf (h _)) _ _ (slotsIn_ofConst _)


section Row
variable {D : ℕ → Aff} (hD : ∀ j, SlotsIn S (D j))
include hD

theorem slotsIn_digs (j n : ℕ) : SlotsIn S (digs D j n) :=
  slotsIn_sumTo n fun _ => slotsIn_scale _ (hD _)

theorem slotsIn_fa : SlotsIn S (fa D) :=
  slotsIn_add (slotsIn_add (slotsIn_add (slotsIn_scale _ (hD 58)) (hD 59))
    (slotsIn_scale _ (hD 60))) (slotsIn_scale _ (hD 61))

theorem slotsIn_fb : SlotsIn S (fb D) := slotsIn_add (hD 62) (slotsIn_scale _ (hD 63))

theorem sl_ofDigits_c (s : ℕ) : SlotsIn S ((P6.Row.ofDigits D).c s) := by
  rw [ofDigits_eq]
  show SlotsIn S (if s == 0 then cst 0 else if s == 9 then D 9
    else digs D (10 + 6 * (s - 1)) 6 - cst (2 ^ 47))
  by_cases h0 : (s == 0) = true
  · rw [if_pos h0]
    exact slotsIn_ofConst _
  · rw [if_neg h0]
    by_cases h9 : (s == 9) = true
    · rw [if_pos h9]
      exact hD 9
    · rw [if_neg h9]
      exact slotsIn_sub (slotsIn_digs hD _ _) (slotsIn_ofConst _)

theorem sl_ofDigits_four : ∀ x ∈ [(P6.Row.ofDigits D).a, (P6.Row.ofDigits D).b,
    (P6.Row.ofDigits D).Rlo, (P6.Row.ofDigits D).Rhi], SlotsIn S x := by
  intro x hx
  rw [ofDigits_eq] at hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact slotsIn_fa hD
  rcases List.mem_cons.mp hx with rfl | hx
  · exact slotsIn_fb hD
  rcases List.mem_cons.mp hx with rfl | hx
  · exact slotsIn_digs hD _ _
  rcases List.mem_cons.mp hx with rfl | hx
  · exact slotsIn_digs hD _ _
  cases hx

theorem slotsIn_carries {W : ℕ → Aff} (hW : ∀ s, s < 9 → SlotsIn S (W s)) :
    ∀ f ∈ P6.carries (P6.Row.ofDigits D) D W, SlotsIn S f := by
  intro f hf
  rw [carries_eq] at hf
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hf
  exact slotsIn_sub (slotsIn_sub (slotsIn_add (hW s (List.mem_range.mp hs)) (sl_ofDigits_c hD s))
    (hD s)) (slotsIn_scale _ (sl_ofDigits_c hD (s + 1)))

theorem slotsIn_lines {P : ℕ → Aff} (hP : ∀ s, s < 7 → SlotsIn S (P s)) (eps : E) {two : Aff}
    (h2 : SlotsIn S two) : ∀ f ∈ P6.lines (P6.Row.ofDigits D) P eps two, SlotsIn S f := by
  intro f hf
  rw [lines_eq, ofDigits_eq] at hf
  have hd := slotsIn_digs hD
  have ha := slotsIn_fa hD
  have hb := slotsIn_fb hD
  have hsig : SlotsIn S (fa D + tms (2 ^ 24) (fb D)) := slotsIn_add ha (slotsIn_scale _ hb)
  have hkap : SlotsIn S (D 79 - cst 4) := slotsIn_sub (hD 79) (slotsIn_ofConst _)
  rcases List.mem_cons.mp hf with rfl | hf
  · exact slotsIn_sub (slotsIn_sub (hP 1 (by omega)) (hd _ _)) (slotsIn_scale _ (hd _ _))
  rcases List.mem_cons.mp hf with rfl | hf
  · exact slotsIn_add (slotsIn_sub (slotsIn_sub (slotsIn_sub
      (slotsIn_add (hd _ _) (slotsIn_ofConst _)) (hP 0 (by omega))) (slotsIn_scale _ (hd _ _)))
      (hd _ _)) (slotsIn_scale _ hkap)
  rcases List.mem_cons.mp hf with rfl | hf
  · exact slotsIn_sub (slotsIn_sub (slotsIn_sub (hd _ _) (hd _ _)) (hP 2 (by omega))) hkap
  rcases List.mem_cons.mp hf with rfl | hf
  · exact slotsIn_sub (slotsIn_add (hd _ _) (hd _ _)) (slotsIn_scale _ hsig)
  rcases List.mem_cons.mp hf with rfl | hf
  · exact slotsIn_sub (slotsIn_add (hP 4 (by omega)) (hP 5 (by omega))) (hd _ _)
  rcases List.mem_cons.mp hf with rfl | hf
  · exact hP 6 (by omega)
  rcases List.mem_cons.mp hf with rfl | hf
  · exact slotsIn_sub (slotsIn_sub (slotsIn_sub (slotsIn_sub (slotsIn_add h2 hsig) (hD 59))
      (slotsIn_scale _ (hP 3 (by omega)))) (slotsIn_scale _ (hd _ _))) (slotsIn_scale _ (hd _ _))
  rcases List.mem_cons.mp hf with rfl | hf
  · exact slotsIn_add (slotsIn_sub (slotsIn_add (hd _ _) (hd _ _)) hsig) (slotsIn_ofConst _)
  cases hf

end Row

variable {v : Env}

/-- A digit is a cell of the reads plus 128. -/
theorem digitsAt_sl {P : String} {i : ℕ} {D : ℕ → Aff} (h : digitsAt v P i = some D) (j : ℕ) :
    SlotsIn S (D j) := by
  unfold digitsAt at h
  obtain ⟨cells, hc, e⟩ := map_some h
  subst e
  exact slotsIn_add (sl_rowCells hc j) (slotsIn_ofConst _)

/-- **Groups 4 to 6.** -/
theorem rowsForms_slots {H : Heard} {l : List Aff} (h : rowsForms v H = some l)
    (hE : ∀ j, H.tV.sEnd ≤ j → j < H.tV.sEnd + 4 * v.y.NI → S j)
    (hW : ∀ j, H.sW ≤ j → j < H.sW + 9 * v.y.NI → S j)
    (hP : ∀ j, H.sPv ≤ j → j < H.sPv + 7 * v.y.NI → S j) : ∀ f ∈ l, SlotsIn S f := by
  have h2 : ∀ i, SlotsIn S (twoM v i) := fun i => by
    unfold twoM
    exact slotsIn_ofConst _
  unfold rowsForms at h
  obtain ⟨ends, h1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨Ds, hDs, h⟩ := Option.bind_eq_some_iff.mp h
  have e := Option.some.inj h
  have hAll : ∀ D ∈ Ds, ∀ j, SlotsIn S (D j) :=
    all_mapM (Pr := fun D : ℕ → Aff => ∀ j, SlotsIn S (D j)) (fun _ _ hb => digitsAt_sl hb) _ Ds
      hDs
  have hlen : Ds.length = v.y.NI := by rw [mapM_length _ _ hDs, List.length_range]
  intro f hf
  rw [← e] at hf
  simp only [List.mem_append] at hf
  rcases hf with (hf | hf) | hf
  · obtain ⟨c, hc, hfc⟩ := List.mem_flatten.mp hf
    refine all_mapM_mem (Pr := fun x : List Aff => ∀ y ∈ x, SlotsIn S y) _ ends
      (fun i hi x hx => ?_) h1 c hc f hfc
    obtain ⟨D, hD, e'⟩ := map_some hx
    subst e'
    intro y hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
    have hi' := List.mem_range.mp hi
    have hz2 : z.2 < 4 := by simpa using List.snd_lt_of_mem_zipIdx hz
    exact slotsIn_sub (slotsIn_slot (hE _ (by omega) (by omega)))
      (sl_ofDigits_four (fun j => digitsAt_sl hD j) z.1 (List.fst_mem_of_mem_zipIdx hz))
  · obtain ⟨c, hc, hfc⟩ := List.mem_flatten.mp hf
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
    have hi : x.2 < v.y.NI := hlen ▸ List.snd_lt_of_mem_zipIdx hx
    exact slotsIn_carries (hAll x.1 (List.fst_mem_of_mem_zipIdx hx))
      (fun s hs => slotsIn_slot (hW _ (by omega) (by omega))) f hfc
  · obtain ⟨c, hc, hfc⟩ := List.mem_flatten.mp hf
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
    have hi : x.2 < v.y.NI := hlen ▸ List.snd_lt_of_mem_zipIdx hx
    exact slotsIn_lines (hAll x.1 (List.fst_mem_of_mem_zipIdx hx))
      (fun s hs => slotsIn_slot (hP _ (by omega) (by omega))) _ (h2 _) f hfc

/-! ### The other groups -/

/-- **Group 2.** -/
theorem normsForms_slots {P : Pub} {H : Heard} {l : List Aff} (h : normsForms P v H = some l)
    (hrow : SlotsIn S H.wpl.row) (hL : S H.wpl.sL) (hR : S H.wpl.sR) : ∀ f ∈ l, SlotsIn S f := by
  unfold normsForms at h
  obtain ⟨txs, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨tI, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨tA, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨e, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨sum, hsum, h⟩ := Option.bind_eq_some_iff.mp h
  have e' := Option.some.inj h
  have hs : SlotsIn S sum := sl_sumForms (fun x p hx => by
    obtain ⟨c, hc, e1⟩ := map_some hx
    subst e1
    split at hc
    · exact sl_U3at hc
    · exact sl_U3at hc) hsum
  intro f hf
  rw [← e'] at hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact hrow
  · exact slotsIn_sub (slotsIn_slot hL) (slotsIn_slot hR)
  · exact slotsIn_add (slotsIn_slot hL) hs

/-- **Group 3, first claim.** -/
theorem rowBatchForm_slots (y : Lay) (H : Heard) (hCl : S H.tV.sCl)
    (hP : ∀ j, H.sPv ≤ j → j < H.sPv + ledNP y.h.xl * y.NI → S j) :
    SlotsIn S (rowBatchForm y H) := by
  unfold rowBatchForm
  refine slotsIn_foldl_mem _ _ (fun f i hi hf => ?_) _ (slotsIn_slot hCl)
  have hi' := List.mem_range.mp hi
  exact slotsIn_addMul _ hf (slotsIn_slot (hP _ (by omega) (by omega)))

/-- **Group 7.** -/
theorem termsForms_slots {H : Heard} {l : List Aff} (h : termsForms v H = some l)
    (hT : ∀ tT, H.tT = some tT → ∀ j, tT.sEnd ≤ j →
      j < tT.sEnd + (v.y.NN * v.y.Lam + v.y.LamM + v.y.LamM * v.y.h.NE) → S j) :
    ∀ f ∈ l, SlotsIn S f := by
  unfold termsForms at h
  obtain ⟨tT, hTT, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
  have e := Option.some.inj h
  have hS := hT tT hTT
  intro f hf
  rw [← e] at hf
  simp only [List.mem_append] at hf
  rcases hf with (hf | hf) | hf
  · refine all_mapM_mem (Pr := SlotsIn S) _ a (fun i hi x hx => ?_) ha f hf
    obtain ⟨z, hz, rfl⟩ := map_some hx
    have hi' := List.mem_range.mp hi
    exact slotsIn_sub (slotsIn_slot (hS _ (by omega) (by omega))) (sl_rowR hz)
  · refine all_mapM_mem (Pr := SlotsIn S) _ b (fun i hi x hx => ?_) hb f hf
    obtain ⟨z, hz, rfl⟩ := map_some hx
    have hi' := List.mem_range.mp hi
    exact slotsIn_sub (slotsIn_slot (hS _ (by omega) (by omega))) (sl_shA hz)
  · refine all_mapM_mem (Pr := SlotsIn S) _ c (fun i hi x hx => ?_) hc f hf
    obtain ⟨z, hz, rfl⟩ := map_some hx
    have hi' := List.mem_range.mp hi
    exact slotsIn_sub (slotsIn_slot (hS _ (by omega) (by omega))) (sl_shA hz)

/-- The two claims on a product layer's end values. -/
theorem endsForms_slots {o : Level} {e : Array E} {t rows blocks stride : ℕ} {lamOf : ℕ → ℕ}
    {first : ℕ} {l : List Aff} (h : endsForms v o e t rows blocks stride lamOf first = some l)
    (hL : S o.sL) (hR : S o.sR) : ∀ f ∈ l, SlotsIn S f := by
  unfold endsForms at h
  obtain ⟨ts, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨tu, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨aS, hS, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨aU, hU, h⟩ := Option.bind_eq_some_iff.mp h
  have e' := Option.some.inj h
  have key : ∀ {X : Ten} {a : Aff}, sumForms (rows * blocks) (fun x =>
      (v.longA t X (lamOf (x / blocks)) (first + x % blocks)).map fun a =>
        (a, e.getD (x / blocks * stride + x % blocks) zeroE)) = some a → SlotsIn S a :=
    fun hs => sl_sumForms (fun x p hp => by
      obtain ⟨a', ha, e1⟩ := map_some hp
      subst e1
      exact sl_longA ha) hs
  intro f hf
  rw [← e'] at hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact slotsIn_add (slotsIn_slot hL) (key hS)
  · exact slotsIn_add (slotsIn_slot hR) (key hU)

/-- **Groups 8 and 9.** -/
theorem gatedForms_slots {P : Pub} {hd : Level} {hd2 : Option Level} {l : List Aff}
    (h : gatedForms P v hd hd2 = some l) (hr : SlotsIn S hd.row) (hL : S hd.sL) (hR : S hd.sR)
    (h2 : ∀ o, hd2 = some o → SlotsIn S o.row ∧ S o.sL ∧ S o.sR) : ∀ f ∈ l, SlotsIn S f := by
  unfold gatedForms at h
  obtain ⟨e, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨t, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨o, ho, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨e2, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨t2, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
  have e' := Option.some.inj h
  obtain ⟨o1, o2, o3⟩ := h2 o ho
  intro f hf
  rw [← e'] at hf
  simp only [List.cons_append, List.mem_cons, List.mem_append] at hf
  rcases hf with rfl | hf | rfl | hf
  · exact hr
  · exact endsForms_slots ha hL hR f hf
  · exact o1
  · exact endsForms_slots hb o2 o3 f hf

/-- **Group 10**: no slot. -/
theorem oneHotForms_slots {l : List Aff} (h : oneHotForms v = some l) : ∀ f ∈ l, SlotsIn S f := by
  unfold oneHotForms at h
  refine all_mapM (Pr := SlotsIn S) (fun lm x hx => ?_) _ l h
  obtain ⟨s, hs, rfl⟩ := map_some hx
  refine slotsIn_add (slotsIn_ofConst _) (sl_sumForms (fun x p hp => ?_) hs)
  obtain ⟨c, hc, e'⟩ := map_some hp
  subst e'
  exact sl_shA hc

/-- **Group 11.** -/
theorem planesParts_slots {fo : Forest.Heard} {pp : Aff × List Aff}
    (h : planesParts v fo = some pp) :
    SlotsIn S pp.1 ∧ (S fo.sBit → ∀ f ∈ pp.2, SlotsIn S f) := by
  unfold planesParts at h
  obtain ⟨tB0, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨tB1, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨tP, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨at0, h0, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨at1, h1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨count, hc, h⟩ := Option.bind_eq_some_iff.mp h
  have e := Option.some.inj h
  have hcol : ∀ (t x : ℕ) (a : Aff),
      (if x < v.y.kbm then v.U3at t x else none) = some a → SlotsIn S a := by
    intro t x a ha
    split at ha
    · exact sl_U3at ha
    · cases ha
  rw [← e]
  refine ⟨slotsIn_scale _ (sl_planesAt (fun e x a ha => hcol _ x a ha) h0), ?_⟩
  intro hB f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact slotsIn_sub (slotsIn_slot hB) (sl_planesAt (fun e x a ha => hcol _ x a ha) h1)
  · exact sl_foldlM_add (fun x a ha => hcol _ x a ha) _ _ _ (slotsIn_ofConst _) hc

/-- **Group 12.** -/
theorem embeddingForm_slots {H : Heard} {sVE : ℕ} {f : Aff}
    (h : embeddingForm v H sVE = some f) (hV : S sVE) : SlotsIn S f := by
  unfold embeddingForm at h
  obtain ⟨t, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨s, hs, h⟩ := Option.bind_eq_some_iff.mp h
  have e := Option.some.inj h
  rw [← e]
  refine slotsIn_add (slotsIn_scale _ (slotsIn_slot hV)) (sl_sumForms (fun kh p hp => ?_) hs)
  obtain ⟨a, ha, e1⟩ := map_some hp
  subst e1
  exact sl_xbA ha

end OnBytes.Desc.First.K4.Slots

#print axioms OnBytes.Desc.First.K4.Slots.rowsForms_slots
#print axioms OnBytes.Desc.First.K4.Slots.normsForms_slots
#print axioms OnBytes.Desc.First.K4.Slots.rowBatchForm_slots
#print axioms OnBytes.Desc.First.K4.Slots.termsForms_slots
#print axioms OnBytes.Desc.First.K4.Slots.gatedForms_slots
#print axioms OnBytes.Desc.First.K4.Slots.oneHotForms_slots
#print axioms OnBytes.Desc.First.K4.Slots.planesParts_slots
#print axioms OnBytes.Desc.First.K4.Slots.embeddingForm_slots
