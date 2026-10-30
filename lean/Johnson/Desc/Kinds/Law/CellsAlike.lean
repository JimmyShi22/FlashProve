-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/CellsAlike.lean: THE CONGRUENCE ON THE HEAD's SIDE: THE LOOKUP's ITEM AND
THE RIDER's ITEM AT THE HEAD (HeadTablesLaw.lean's HeadParts: lookCalls: every place of every call's
key table is a row · rider: the clip's and the table's corner values are 0) READ NO CELL BEYOND THE
RANGES: two records of cells that agree on the features and positions that the head's relation names
have THE SAME KEY TABLES AND
THE SAME TWO CORNER VALUES, AS ELEMENTS OF THE PROGRAM's FIELD: STATED AND PROVED. FOR "THE TIE AT
ONE c": another reading of the cells (which walks into the neighbour's matrix beyond a
matrix's features) and Law/K6Cut.lean's (0 outside the four ranges) may be exchanged in these two
items wherever they agree inside the ranges. It is the twin, on our relation, of the library's
Policy.SameMain laws
(Policy/Seg/HeadAsm.lean) and of the AgreeH laws (Goal/Meaning/HidHeadCongr.lean) on theirs.
OBJECT: no constant of the seated text: a tool on our relation on cells (keyTable, clipAt, tableAt).
MEANT FOR whoever joins the lookup's law at the head (its cells) to Law/K6Cut.lean's
k06_ord. LETTERS: c, c' (two records of cells): tied by SameCells alone.
HOW. No form is opened: each of the nine keys and the two guests at a corner is written canonically
(okE_keyAt | okE_keyNAt | okE_clipAt | okE_tableAt) and is read as the cast of an integer
that names its cells (rd_key_* | rd_keyN_* | rd_clip | rd_table): the integers agree cell
by cell; eq_of_rd closes.
  SameCells c c' wide below 4 d + 6 JV · act below 2 d · row below NR + 21 · the stream below 5 d,
      at positions below T · the weights at k below d, v below V.
  keyAt_same · keyNAt_same · cornerKey_same · keyTable_same · clip_same · table_same
  lookCalls_same · rider_same     THE TWO ITEMS.
WHAT IT DOES NOT SAY. Nothing on idn (the 17 row forms and the two sums: K6's own item: it stands at
K6's own reading and needs no exchange). The tests on the plan and the request and "the token is
below V" are premises (these lemmas ask them). That any two readings agree inside the ranges:
the caller's. No chance in it.

-/
import Mathlib
import Johnson.Desc.Kinds.HeadTablesLaw
import Johnson.Desc.Kinds.Law.Values
import Johnson.Desc.Kinds.Law.NormProof
import Johnson.Desc.Kinds.Law.TableTie
import Johnson.Desc.Kinds.Law.Clamp
import Johnson.Desc.Kinds.Law.K06Statement
import Policy.Seg.HeadAsm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open Norm (lt ls d lPd T S2)

variable [Sizes] [Policy] [Request] [Token]

/-- **Two records of cells agree on what the head's relation names.** -/
structure SameCells (c c' : NCells) : Prop where
  wide : ∀ f t, f < 4 * d + 6 * JV → t < T → c.cell .wide f t = c'.cell .wide f t
  act : ∀ f t, f < 2 * d → t < T → c.cell .act f t = c'.cell .act f t
  row : ∀ f t, f < NR + 21 → t < T → c.cell .row f t = c'.cell .row f t
  stream : ∀ f t, f < 5 * d → t < T → c.stream f t = c'.stream f t
  Wh : ∀ k v, k < d → v < V → c.Wh k v = c'.Wh k v

namespace Came

variable {c c' : NCells}

theorem numZ_same (h : SameCells c c') (n : Number) {t : Nat} (ht : t < T) :
    numZ c.toCells n t = numZ c'.toCells n t := by
  unfold numZ
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' := Finset.mem_range.1 hl
  have hb : NR + n.digits.1 + l < NR + 21 := by
    cases n <;> simp only [Number.digits] at hl' ⊢ <;> omega
  show _ * (c.cell .row _ t + 128) = _ * (c'.cell .row _ t + 128)
  rw [h.row _ t hb ht]

theorem midZ_same (h : SameCells c c') {x t : Nat} (hx : x < JV) (ht : t < T) :
    midZ c.toCells x t = midZ c'.toCells x t := by
  unfold midZ
  show _ + (c.cell .wide _ t + 256 * c.cell .wide _ t) = _ + (c'.cell .wide _ t + 256 * c'.cell
      .wide _ t)
  rw [h.wide _ t (by omega) ht, h.wide _ t (by omega) ht]

theorem lowZ_same (h : SameCells c c') {x t : Nat} (hx : x < JV) (ht : t < T) :
    lowZ c.toCells x t = lowZ c'.toCells x t := by
  unfold lowZ
  show _ + c.cell .wide _ t = _ + c'.cell .wide _ t
  rw [h.wide _ t (by omega) ht]

theorem tvZ_same (h : SameCells c c') {x t : Nat} (hx : x < JV) (ht : t < T) :
    tvZ c.toCells x t = tvZ c'.toCells x t := by
  unfold tvZ
  congr 1
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' := Finset.mem_range.1 hl
  show _ * c.cell .wide _ t = _ * c'.cell .wide _ t
  have hb : 4 * d + (3 + l) * JV + x < 4 * d + 6 * JV := by
    have : (3 + l) * JV ≤ 5 * JV := Nat.mul_le_mul_right _ (by omega)
    omega
  rw [h.wide _ t hb ht]

theorem act_same (h : SameCells c c') {t k : Nat} (ht : t < T) (hk : k < d) :
    act c.toCells t k = act c'.toCells t k := by
  unfold act
  show c.cell .act _ t + 256 * c.cell .act _ t = c'.cell .act _ t + 256 * c'.cell .act _ t
  rw [h.act _ t (by omega) ht, h.act _ t (by omega) ht]

theorem logit_same (h : SameCells c c') {t v : Nat} (ht : t < T) (hv : v < V) :
    logit c.toCells t v = logit c'.toCells t v := by
  unfold logit
  rw [sumZ_eq, sumZ_eq]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.1 hk
  show _ * c.Wh k v = _ * c'.Wh k v
  rw [act_same h ht hk', h.Wh k v hk' hv]

theorem topNum_same (h : SameCells c c') (hreq : Request.ok = true) (hy : y < V) {x t : Nat}
    (hx : x < JV) (ht : t < T) : topNum c.toCells x t = topNum c'.toCells x t := by
  unfold topNum liftZ
  rw [midZ_same h hx ht, lowZ_same h hx ht, numZ_same h .paid ht, numZ_same h .over ht,
    logit_same h ht (win_lt hreq hy t)]
  by_cases hxV : x < V
  · rw [logit_same h ht hxV]
  · simp only [hxV, false_and, if_false]

/-- **The head's five keys at a corner.** -/
theorem keyAt_same (h : SameCells c c') (P : PlanFacts) (hreq : Request.ok = true) (hy : y < V)
    (k : Key) {x t : Nat} (hx : x < len k) (ht : t < T) :
    keyAt c.toCells (corner x t) k = keyAt c'.toCells (corner x t) k := by
  refine eq_of_rd (okE_keyAt _ _ _) (okE_keyAt _ _ _) ?_
  cases k with
  | marginTop =>
    have hx' : x < JV := hx
    rw [rd_key_top P hreq hy hx' ht, rd_key_top P hreq hy hx' ht, topNum_same h hreq hy hx' ht]
  | marginMid =>
    have hx' : x < JV := hx
    rw [rd_key_mid P hx' ht, rd_key_mid P hx' ht, midZ_same h hx' ht]
  | marginLow =>
    have hx' : x < JV := hx
    rw [rd_key_low P hx' ht, rd_key_low P hx' ht, lowZ_same h hx' ht]
  | tableA =>
    have hx' : x < JVa := hx
    have hx2 : x < JV := lt_of_lt_of_le hx' (JVa_le (by have := P.hV2; omega))
    rw [rd_key_tableA P hx' ht, rd_key_tableA P hx' ht, midZ_same h hx2 ht, tvZ_same h hx2 ht]
  | tableB =>
    have hx' : x < JV - JVa := hx
    have hx2 : JVa + x < JV := by omega
    rw [rd_key_tableB P hx' ht, rd_key_tableB P hx' ht, midZ_same h hx2 ht, tvZ_same h hx2 ht]

theorem digZ_same (h : SameCells c c') {t j : Nat} (ht : t < T) (hj : j < NR + 21) :
    digZ c t j = digZ c' t j := by
  unfold digZ
  rw [h.row j t hj ht]

theorem recZ_same (h : SameCells c c') {t : Nat} (ht : t < T) : recZ c t = recZ c' t := by
  have hD : ∀ n < 120, digZ c t n = digZ c' t n := fun n hn => digZ_same h ht hn
  unfold recZ Inst.Model.Ledger.R Inst.Model.Ledger.Rlo Inst.Model.Ledger.Rhi
  rw [_root_.Policy.b256M_same hD (by norm_num), _root_.Policy.b256M_same hD (by norm_num)]

theorem str_same (h : SameCells c c') {t k : Nat} (ht : t < T) (hk : k < d) :
    str c t k = str c' t k := by
  unfold str
  rw [sumZ_eq, sumZ_eq]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' := Finset.mem_range.1 hl
  unfold limbZ
  have hb : l * d + k < 5 * d := by
    have : l * d ≤ 4 * d := Nat.mul_le_mul_right _ (by omega)
    omega
  rw [h.stream _ t hb ht]

theorem awZ_same (h : SameCells c c') {t x : Nat} (ht : t < T) (hx : x < d) :
    awZ c t x = awZ c' t x := by
  unfold awZ
  rw [h.wide _ t (by omega) ht, h.wide _ t (by omega) ht]

theorem remZ_same (h : SameCells c c') {t x : Nat} (ht : t < T) (hx : x < d) :
    remZ c t x = remZ c' t x := by
  unfold remZ
  rw [h.wide _ t (by omega) ht, h.wide _ t (by omega) ht]

/-- **The normalization's four keys at a corner.** -/
theorem keyNAt_same (h : SameCells c c') (hd : S2 ∣ d) (k : FinalNorm.Key) {x t : Nat}
    (hx : x < lenN k) (ht : t < T) :
    keyNAt c (cornerN x t) k = keyNAt c' (cornerN x t) k := by
  refine eq_of_rd (okE_keyNAt _ _ _) (okE_keyNAt _ _ _) ?_
  cases k with
  | remLow =>
    have hx' : x < d := hx
    rw [rd_keyN_remLow ht hd hx', rd_keyN_remLow ht hd hx', str_same h ht hx', recZ_same h ht,
      awZ_same h ht hx', remZ_same h ht hx']
  | remHigh =>
    have hx' : x < d := hx
    rw [rd_keyN_remHigh ht hd hx', rd_keyN_remHigh ht hd hx', remZ_same h ht hx']
  | clamp =>
    have hx' : x < d := hx
    rw [rd_keyN_clamp ht hd hx', rd_keyN_clamp ht hd hx', awZ_same h ht hx', act_same h ht hx']
  | digits =>
    have hx' : x < NR + 21 := hx
    rw [rd_keyN_digits ht hx', rd_keyN_digits ht hx', digZ_same h ht hx']

/-- A key of the place at a corner. -/
theorem cornerKey_same (h : SameCells c c') (P : PlanFacts) (hreq : Request.ok = true) (hy : y < V)
    (kk : PlaceKey) {x t : Nat} (hx : x < lenOf kk) (ht : t < T) :
    cornerKey c kk x t = cornerKey c' kk x t := by
  cases kk with
  | inl k =>
    refine keyNAt_same h (Nat.dvd_of_mod_eq_zero P.hdS) k ?_ ht
    cases k <;> exact hx
  | inr k => exact keyAt_same h P hreq hy k hx ht

/-- A call's entries hang on the values below the keys' lengths alone. -/
theorem entriesOf_same {α : Type} (lens : List Nat) (g g' : Nat → Nat → α)
    (hg : ∀ s x, s < lens.length → x < lens.getD s 0 → g s x = g' s x) :
    entriesOf lens g = entriesOf lens g' := by
  unfold entriesOf
  refine List.flatMap_congr fun s hs => List.map_congr_left fun x hx => ?_
  rw [hg s x (List.mem_range.1 hs) (List.mem_range.1 hx)]

/-- **THE CALL's TABLE.** -/
theorem keyTable_same (h : SameCells c c') (P : PlanFacts) (hreq : Request.ok = true) (hy : y < V)
    (call col : Nat) {t : Nat} (ht : t < T) : keyTable c call col t = keyTable c' call col t := by
  unfold keyTable callTable tableOf
  rw [entriesOf_same _ _ (fun s x => cornerKey c' (slot (callKeys call) s) x t) fun s x hs hx => ?_]
  rw [List.length_map] at hs
  refine cornerKey_same h P hreq hy _ ?_ ht
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hs), List.getElem_map] at hx
  unfold slot
  rw [List.getD_eq_getElem _ _ hs]
  exact hx

theorem clip_same (h : SameCells c c') {t : Nat} (ht : t < T) :
    clipAt c.toCells (corner 0 t) = clipAt c'.toCells (corner 0 t) := by
  refine eq_of_rd (okE_clipAt _ _) (okE_clipAt _ _) ?_
  rw [rd_clip ht, rd_clip ht, numZ_same h .paid ht, numZ_same h .slackClip ht]

theorem table_same (h : SameCells c c') (P : PlanFacts) {t : Nat} (ht : t < T) :
    tableAt c.toCells (corner 0 t) = tableAt c'.toCells (corner 0 t) := by
  refine eq_of_rd (okE_tableAt _ _) (okE_tableAt _ _) ?_
  rw [rd_table P ht, rd_table P ht, numZ_same h .slackTable ht,
    Finset.sum_congr rfl fun x hx => tvZ_same h (Finset.mem_range.1 hx) ht]

/-- **THE LOOKUP's ITEM READS NO CELL BEYOND THE RANGES.** -/
theorem lookCalls_same (h : SameCells c c') (P : PlanFacts) (hreq : Request.ok = true) (hy : y < V)
    (floor : Nat) (tab : Nat → Nat)
    (hl : ∀ call, call < 6 → ∀ col, col < 2 ^ lJ floor (callKeys call) → ∀ t, t < T →
      InTable tab call (keyTable c call col t)) :
    ∀ call, call < 6 → ∀ col, col < 2 ^ lJ floor (callKeys call) → ∀ t, t < T →
      InTable tab call (keyTable c' call col t) := fun call hc col hcol t ht => by
  rw [← keyTable_same h P hreq hy call col ht]
  exact hl call hc col hcol t ht

/-- **THE RIDER's ITEM READS NO CELL BEYOND THE RANGES.** -/
theorem rider_same (h : SameCells c c') (P : PlanFacts) (hr : CornerGuests c.toCells) :
    CornerGuests c'.toCells := fun t ht => by
  rw [← clip_same h ht, ← table_same h P ht]
  exact hr t ht

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.keyTable_same
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.lookCalls_same
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.rider_same
