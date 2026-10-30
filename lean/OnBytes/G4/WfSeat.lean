-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/G4/WfSeat.lean: the seat of a key's lookup: a context of the program together with what the
key's one-time chain tells Lkp.verify (Wf.lookupsVerify, OnBytes/Iop/Wf.lean), and facts that can be
evaluated from which the seat is good (OnBytes/G4/SeatLaws.lean).

`wfSeat b x m codes i group indexMasksId`: the context b; the public inputs Wf.lookupOf x.messageId
m l, with l the lookup number i of the item x; the bits are read by Wf.planesAt x codes i; mask
entries come from the message x.messageId, those of each part's last key level from indexMasksId.
`wfFacts` is a test on the base's statement and on public numbers: the two messages differ; both are
there and sampled; the group is there and its proximity test has not begun; each block of planes of
the lookup gives a vector that has as many variables as the message's main table has index bits, at
most 63, and the message is a member of the group with main rows; and no entry that masks an answer
to a sample lies in that main table.
`wfSeat_good`: where the test says yes, the seat is good. So its caller meets the laws of
OnBytes/G4/AnyCaller.lean (`wfSeat_laws`).

Main definitions: wfSeat, stayingVars, blockVars, wfFacts.
Main theorems: setBits_shape, insertChoice_vars, Seat.rowFine_add, wf_planes, wfSeat_good,
wfSeat_laws.
Not claimed. That the context in which a key's one-time chain calls the lookups passes the test.


-/
import OnBytes.G4.SeatLaws
import OnBytes.Iop.Wf

set_option autoImplicit false

namespace OnBytes.G4

open Blk OnBytes.Params

/-! ## Vectors of product form -/

theorem choiceCount : ∀ (count value : Nat), (choicePairs count value).length = count
  | 0, _ => rfl
  | n + 1, value => by simp [choicePairs, choiceCount n]

/-- Inserting variables that pick bits adds as many variables. -/
theorem insertChoice_vars (v : Tensor) (pos count value : Nat) :
    (v.insertChoice pos count value).vars = v.vars + count := by
  simp only [Tensor.insertChoice, Tensor.vars, List.length_append, List.length_take,
      List.length_drop,
    choiceCount]
  omega

theorem insertChoice_dense (v : Tensor) (pos count value : Nat) (h : v.denseVars = []) :
    (v.insertChoice pos count value).denseVars = [] := by
  simp [Tensor.insertChoice, h]

/-- A vector of product form is in order if it has at most 63 variables. -/
theorem ok_of_product (v : Tensor) (h : v.denseVars = []) (h63 : v.vars ≤ 63) : v.ok = true := by
  simp [Tensor.ok, h, h63, distinctNats]

theorem scale_dense (v : Tensor) (x : E) : (v.scale x).denseVars = v.denseVars := by
  generalize hy : mulE v.scalar x = y
  have e : v.scale x = { v with scalar := y } := by rw [← hy]; rfl
  rw [e]

theorem scale_pairs (v : Tensor) (x : E) : (v.scale x).pairs = v.pairs := by
  generalize hy : mulE v.scalar x = y
  have e : v.scale x = { v with scalar := y } := by rw [← hy]; rfl
  rw [e]

theorem scale_vars (v : Tensor) (x : E) : (v.scale x).vars = v.vars := by
  unfold Tensor.vars
  rw [scale_pairs]

theorem push_dense (v : Tensor) (l h : E) : (v.push l h).denseVars = v.denseVars := by
  simp [Tensor.push]

theorem push_vars (v : Tensor) (l h : E) : (v.push l h).vars = v.vars + 1 := by
  simp [Tensor.push, Tensor.vars]

/-- How many of the variables 0 .. n - 1 stay when those from low up to below high are set. -/
def stayingVars (n low high : Nat) : Nat :=
  ((List.range n).filter fun t => !(decide (low ≤ t) && decide (t < high))).length

/-- Setting variables to bits gives a vector of product form with the variables that stay. -/
theorem setBits_shape (v : Tensor) (low high number : Nat) :
    (Lkp.setBits v low high number).denseVars = [] ∧
      (Lkp.setBits v low high number).vars = stayingVars v.pairs.length low high := by
  unfold Lkp.setBits stayingVars
  have key : ∀ (l : List (Nat × (E × E))) (init : Tensor), init.denseVars = [] →
      (l.foldl (fun (part : Tensor) p =>
        if low ≤ p.1 && p.1 < high then
          part.scale (if number.testBit p.1 then p.2.2 else p.2.1)
        else part.push p.2.1 p.2.2) init).denseVars = [] ∧
      (l.foldl (fun (part : Tensor) p =>
        if low ≤ p.1 && p.1 < high then
          part.scale (if number.testBit p.1 then p.2.2 else p.2.1)
        else part.push p.2.1 p.2.2) init).vars =
        init.vars + ((l.map Prod.fst).filter fun t =>
            !(decide (low ≤ t) && decide (t < high))).length := by
    intro l
    induction l with
    | nil => intro init h; exact ⟨h, rfl⟩
    | cons p l ih =>
      intro init h
      simp only [List.foldl_cons, List.map_cons, List.filter_cons]
      cases hc : (decide (low ≤ p.1) && decide (p.1 < high)) with
      | true =>
        simp only [if_true, Bool.not_true, Bool.false_eq_true, if_false]
        have hi := ih (init.scale (if number.testBit p.1 then p.2.2 else p.2.1))
          (by rw [scale_dense]; exact h)
        rw [scale_vars] at hi
        exact hi
      | false =>
        simp only [Bool.false_eq_true, if_false, Bool.not_false, if_true, List.length_cons]
        obtain ⟨a, b⟩ := ih (init.push p.2.1 p.2.2) (by rw [push_dense]; exact h)
        refine ⟨a, ?_⟩
        rw [b, push_vars]
        omega
  obtain ⟨a, b⟩ := key ((List.range v.pairs.length).zip v.pairs) { scalar := v.scalar } rfl
  refine ⟨a, ?_⟩
  rw [b, List.map_fst_zip (by simp)]
  simp [Tensor.vars]

namespace Seat

/-- A structured vector elsewhere does not turn a row's coefficient on an entry. -/
theorem coefficient_add_ne (r : Row) (o' : Nat) (part' : Part) (v : Tensor) (o : Nat) (part : Part)
    (index : Nat) (h : ¬(o' = o ∧ part' = part)) :
    (r.add o' part' v).coefficient o part index = r.coefficient o part index := by
  simp [Row.coefficient, Row.add, h]

/-- A fine row stays fine when a structured vector is added that is in order, fits its table, reads
a declared message, and lies in no table that holds an entry that masks an answer to a sample. -/
theorem rowFine_add (Z : Seat) (r : Row) (o : Nat) (part : Part) (v : Tensor) (h : Z.RowFine r)
    (hok : v.ok = true) (hp : placeOk Z.base.st Z.groupOf o part v.vars 0 = true)
    (hd : (part != .main || Z.S.readFrom.contains o) = true)
    (hpad : ∀ q ∈ Z.groupOf.members, ∀ p ∈ Z.padsOf q, ¬(o = q ∧ part = p.1)) :
    Z.RowFine (r.add o part v) :=
  { kind := h.kind, runs := h.runs, forms := h.forms, units := h.units
    terms := by
      intro t ht
      simp only [Row.add, Array.mem_push] at ht
      rcases ht with ht | rfl
      · exact h.terms t ht
      · exact ⟨hok, hp, hd⟩
    pads := by
      intro q hq p hp'
      rw [coefficient_add_ne _ _ _ _ _ _ _ (hpad q hq p hp')]
      exact h.pads q hq p hp' }

end Seat

/-! ## The seat of a key's lookup -/

/-- The seat of lookup number i of the item x, at the context b. -/
def wfSeat (b : Ctx) (x : WfPublic) (m : Wf.Matrix) (codes : Codes) (i group indexMasksId : Nat) :
    Seat where
  base := b
  S := Wf.lookupOf x.messageId m (x.lookups.getD i default)
  planesAt := Wf.planesAt x codes i
  masks := x.messageId
  keyMasks := indexMasksId
  group := group

/-- The number of variables of the vector that Wf.planesAt adds for a block of planes. -/
def blockVars (x : WfPublic) (codes : Codes) (i : Nat) (b : Wf.Block) : Nat :=
  stayingVars ((x.lookups.getD i default).mu + (x.lookups.getD i default).d) b.logPlanes
      (x.lookups.getD i default).mu +
    ((codes.base.getD x.message.shape.code default).logEll - b.bits) +
    ceilLog2 x.message.shape.mainRows

/-- The facts on the base's statement and on public numbers from which the seat is good. -/
def wfFacts (b : Ctx) (x : WfPublic) (m : Wf.Matrix) (codes : Codes) (i group indexMasksId : Nat) :
    Bool :=
  let Z := wfSeat b x m codes i group indexMasksId
  x.messageId != indexMasksId &&
  ((b.st.oracles[x.messageId]?).any Oracle.sampled) &&
  ((b.st.oracles[indexMasksId]?).any Oracle.sampled) &&
  (b.st.groups[group]?).isSome && !Z.groupOf.inRun &&
  (((Wf.layout x.lookups (codes.base.getD x.message.shape.code default).ell).filter
      (·.lookup == i)).all fun k =>
    decide (blockVars x codes i k ≤ 63) &&
      placeOk b.st Z.groupOf x.messageId .main (blockVars x codes i k) 0) &&
  Z.groupOf.members.all fun q => (Z.padsOf q).all fun p => !(x.messageId == q && Part.main == p.1)

/-- The vector that Wf.planesAt adds for a block of planes. -/
def blockTensor (x : WfPublic) (codes : Codes) (i : Nat) (k : Wf.Block) (v : Tensor) : Tensor :=
  ((Lkp.onBlock v (x.lookups.getD i default).mu (k.first, k.logPlanes)).insertChoice k.bits
    ((codes.base.getD x.message.shape.code default).logEll - k.bits)
    (k.firstPlace / 2 ^ k.bits)).insertChoice 0 (ceilLog2 x.message.shape.mainRows) k.row

theorem blockTensor_shape (x : WfPublic) (codes : Codes) (i : Nat) (k : Wf.Block) (v : Tensor)
    (hv : v.vars = (x.lookups.getD i default).mu + (x.lookups.getD i default).d) :
    (blockTensor x codes i k v).denseVars = [] ∧
      (blockTensor x codes i k v).vars = blockVars x codes i k := by
  obtain ⟨a, b⟩ := setBits_shape v k.logPlanes (x.lookups.getD i default).mu k.first
  refine ⟨insertChoice_dense _ _ _ _ (insertChoice_dense _ _ _ _ a), ?_⟩
  unfold blockTensor blockVars
  rw [insertChoice_vars, insertChoice_vars]
  show (Lkp.setBits v k.logPlanes (x.lookups.getD i default).mu k.first).vars + _ + _ = _
  rw [b, show v.pairs.length = v.vars from rfl, hv]

/-- Where the facts hold, adding a vector of product form on the bits keeps a row fine. -/
theorem wf_planes (b : Ctx) (x : WfPublic) (m : Wf.Matrix) (codes : Codes)
    (i group indexMasksId : Nat)
    (h : wfFacts b x m codes i group indexMasksId = true) (r : Row) (v : Tensor)
    (hr : (wfSeat b x m codes i group indexMasksId).RowFine r)
    (hv : v.vars = (x.lookups.getD i default).mu + (x.lookups.getD i default).d) :
    (wfSeat b x m codes i group indexMasksId).RowFine (Wf.planesAt x codes i r v) := by
  unfold wfFacts at h
  simp only [Bool.and_eq_true, List.all_eq_true, Array.all_eq_true_iff_forall_mem,
    decide_eq_true_eq] at h
  obtain ⟨⟨_, hblocks⟩, hpads⟩ := h
  have key : ∀ (l : List Wf.Block), (∀ k ∈ l, k ∈ (Wf.layout x.lookups
      (codes.base.getD x.message.shape.code default).ell).filter (·.lookup == i)) → ∀ r : Row,
      (wfSeat b x m codes i group indexMasksId).RowFine r →
      (wfSeat b x m codes i group indexMasksId).RowFine
        (l.foldl (fun r k => r.add x.messageId .main (blockTensor x codes i k v)) r) := by
    intro l
    induction l with
    | nil => intro _ r hr; exact hr
    | cons k l ih =>
      intro hl r hr
      apply ih (fun q hq => hl q (by simp [hq]))
      obtain ⟨hd, hvars⟩ := blockTensor_shape x codes i k v hv
      obtain ⟨h63, hplace⟩ := hblocks k (hl k (by simp))
      apply Seat.rowFine_add _ r _ _ _ hr (ok_of_product _ hd (by rw [hvars]; exact h63))
        (by rw [hvars]; exact hplace)
      · show (Part.main != Part.main || [x.messageId].contains x.messageId) = true
        simp
      · intro q hq p hp hh
        have := hpads q hq p hp
        simp [hh.1, hh.2] at this
  exact key _ (fun _ hk => hk) r hr

/-- Where the facts hold, the seat is good. -/
theorem wfSeat_good (b : Ctx) (x : WfPublic) (m : Wf.Matrix) (codes : Codes)
    (i group indexMasksId : Nat) (h : wfFacts b x m codes i group indexMasksId = true) :
    (wfSeat b x m codes i group indexMasksId).Good := by
  have h' := h
  unfold wfFacts at h'
  simp only [Bool.and_eq_true] at h'
  obtain ⟨⟨⟨⟨⟨⟨hne, hs1⟩, hs2⟩, hg⟩, hopen⟩, _⟩, _⟩ := h'
  have s1 : ∃ y, b.st.oracles[x.messageId]? = some y ∧ y.sampled = true := by
    cases hy : b.st.oracles[x.messageId]? with
    | none => simp [hy] at hs1
    | some y => exact ⟨y, rfl, by simpa [hy] using hs1⟩
  have s2 : ∃ y, b.st.oracles[indexMasksId]? = some y ∧ y.sampled = true := by
    cases hy : b.st.oracles[indexMasksId]? with
    | none => simp [hy] at hs2
    | some y => exact ⟨y, rfl, by simpa [hy] using hs2⟩
  exact
    { apart := by simpa using hne
      sampled := by
        intro o ho
        rcases ho with rfl | rfl | ho
        · exact s1
        · exact s2
        · have : o = x.messageId := by
            have ho' : o ∈ [x.messageId] := ho
            simpa using ho'
          subst this
          exact s1
      group := Option.isSome_iff_exists.1 hg
      open_ := by simpa using hopen
      planes := fun r v hr hv _ _ => wf_planes b x m codes i group indexMasksId h r v hr hv }

/-- Where the facts hold, the caller of a key's lookup meets the laws. -/
theorem wfSeat_laws (b : Ctx) (x : WfPublic) (m : Wf.Matrix) (codes : Codes)
    (i group indexMasksId : Nat) (h : wfFacts b x m codes i group indexMasksId = true) :
    (wfSeat b x m codes i group indexMasksId).caller.Laws :=
  Seat.laws _ (wfSeat_good b x m codes i group indexMasksId h)

end OnBytes.G4

#print axioms OnBytes.G4.wfSeat_laws
