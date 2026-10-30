-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/FormsOfItem.lean: FROM WHAT THE TABLE OF JOINTS' ITEM formsT m 3 "own" SAYS OF K4's
TWO RUNS TO THE SENTENCE FormsT OF THE STATEMENT OF K4's LAW (Johnson/Desc/Plain/K04Plain.lean), at
every letter St that has StatedAt at the verifier's state (Johnson/Road/K4/FillStated.lean) and at
the Sem that is made of the table's own data. WHAT THE ITEM SAYS IS WRITTEN OUT BY HAND HERE (I1,
I2): the join with the table's own sentence and reader stands in Johnson/Road/K4/FormsLine.lean.

The item (Johnson/Desc/Sound/FormsQ.lean: formsTQ) says of each run, CALLED AT THE BORDER's LEDGER
F: each of its forms is worth 0 in worldOwn, at late := lateOf F (the ledger behind the run). FormsT
says: "front" from F leaves F₁; "back" FROM F₁ leaves F₂; each form is there at its ledger and is
worth 0 in that ledger's own world, the reads read as true.

  `semQ tl M s Dq`: the Sem of the table's data AT ONE STATE s OF THE VERIFIER: the mask row of a
    world w is Dq w's; the true value of an entry is entryTrue tl o (M s (Dq w)). IT HANGS ON THE
    STATE (s and Dq are read off it), WHILE THE LAW's LETTER Sem IS ONE FOR ALL STATES: so semQ is a
    stepping stone and no filling of that letter: formsT_sem carries the sentence on.
  `back_two`: a frame law for "back" at two ledgers, FROM BOTH RETURNS: from F and from a later
    ledger F₁ it gives ONE list, and under every slot that is filled behind the first the second has
    the same mark, shown value and factor. IT GIVES NO RETURN: that "back" returns from the ledger
    that "front" leaves ("front" lays none of the merge's slots) lies in the premise hb₁. Under the
    same two returns it would also serve the move that K04Plain's head names as owed.
  `worldOf_same`: a form has one value in the own worlds of two ledgers that agree under the slots
    which it names.
  `there_got`, `there_slots`: thereAt: each named slot is filled, so inside the array of marks; at a
    ledger with arrays of the right sizes: below the number of slots.
  `worldOf_mask`: one value at two mask rows that agree under the named slots.
  `formsT_sem`: FormsT passes to every Sem that agrees with the first WHERE THE SENTENCE READS: the
    mask rows BELOW A BOUND n on the two ledgers' arrays of marks (not at every number: one reader
    of a witness cuts the mask row to its length, another reads it uncut: beyond the length the two
    part), the entries at what the seat finds heard.
  `formsT_of_item`: THE TIE.
No new argument: hideRun_ok, formsBack_some, value_stated.
Limits. PREMISES of formsT_of_item: the verifier's state stands in a layers' link and holds o (hs,
ho) · the part has the link's context and ledger (hA, hF) · the reads' array's name (hc) · StatedAt
(X) · the ledger has arrays of the right sizes (hS) · the three returns (hf, hb, hb₁: the law that
both listings return, Johnson/Road/K4/Total/, under a member) · "front" leaves a later ledger with
arrays of the right sizes (L1, S1) · thereAt of each form at its ledger (T1, Tb, T2:
Johnson/Road/K4/Slots/RunsThere.lean has THE SLOTS' HALF, under three premises on what the lookup
has heard; THE ENTRIES' HALF, Fork.hasEnt, IS SHOWN BY NOBODY; by a run it held at honest proofs of
two sizes) · each entry that a form names has the reads' number, row 0 and a place below n (E1, E2:
Johnson/Road/K4/Reads/RowZero.lean: not called here) · the item's two halves (I1, I2). WHERE THE
LINE IS CALLED ITS CALLER HAS THE PROMISE BEHIND AND THE ITEM IN HAND, NO ACCEPTING RUN: hS, X's h2,
hb₁, T1, Tb, T2, E1, E2 must lie in that promise: laid there by nobody yet. NOT HERE: that the
table's reader at (2, "front") and (2, "back") gives these lists and these late slots (it does at
p.k3Runs = true alone) · THAT ONE Sem AGREES WITH semQ AT EVERY STATE OF THE LAW: two equations of
readers (the mask row below the number of slots; entryTrue at the matrices M and at the parameter
tl: Johnson/Road/K4/EntryCells.lean: agreement inside the ranges serves), to be shown at each state:
by nobody yet · that the forms are worth 0 anywhere. Met through Lean at no member. K04_law, the law
of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.


-/
import Johnson.Road.K4.FillStated
import Johnson.Desc.Plain.K04Plain
import Johnson.Desc.First.K4.SeatS
import OnBytes.Desc.First.K4.ClaimsLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Road.K4

open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.PscRun (Later Filled hideRun_ok hideRun_later paid_later)
open OnBytes.Desc.First.K4 (Par seatS formsBack formsBack_some)
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc.K9 (lateOf)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ Stated second worldOwn)
open VerifiableInference.Desc.Plain.K04 (Sem thereAt AllZero FormsT frontRun)

variable {Wt : Type}

/-- The Sem of the table's data. -/
def semQ (tl : HTailF2) (M : S → Bound GQ → Mats GQ) (s : S) (Dq : Wt → Bound GQ) : Sem Wt where
  mask := fun w => (Dq w).mask
  entryT := fun o w => entryTrue tl o (M s (Dq w))

/-- **"back" from two ledgers**: one list; the later run's ledger agrees with the earlier run's
under every slot that is filled behind the earlier. -/
theorem back_two {o : Own} {F F₁ Gb F₂ : Fork} {fa fb : Array Aff} (hS : PscRun.Sized F)
    (S1 : PscRun.Sized F₁)
    (L1 : Later F F₁) (ha : formsBack o F = some (fa, Gb)) (hb : formsBack o F₁ = some (fb, F₂)) :
    fb = fa ∧ ∀ j, Filled Gb j → Filled F₂ j ∧ F₂.vp.getD j zeroE = Gb.vp.getD j zeroE ∧
      F₂.mf.getD j zeroE = Gb.mf.getD j zeroE := by
  obtain ⟨A, ea, ra, rfl⟩ := formsBack_some ha
  obtain ⟨B, eb, rb, rfl⟩ := formsBack_some hb
  refine ⟨eb.trans ea.symm, fun j hj => ?_⟩
  obtain ⟨_, _, a3, a4⟩ := hideRun_ok F A _ _ _ hS ra
  obtain ⟨_, _, b3, b4⟩ := hideRun_ok F₁ B _ _ _ S1 rb
  have hj' : Filled A j := hj
  show Filled B j ∧ B.vp.getD j zeroE = A.vp.getD j zeroE ∧ B.mf.getD j zeroE = A.mf.getD j zeroE
  by_cases hin : o.wo.toWsMerged.p.first ≤ j ∧ j < o.wo.toWsMerged.p.first +
      (Array.replicate o.wo.toWsMerged.p.walk.1.length zeroE).size
  · have e : o.wo.toWsMerged.p.first + (j - o.wo.toWsMerged.p.first) = j := by omega
    obtain ⟨_, _, _, x4, x5⟩ := a3 (j - o.wo.toWsMerged.p.first) (by omega)
    obtain ⟨_, _, y3, y4, y5⟩ := b3 (j - o.wo.toWsMerged.p.first) (by omega)
    rw [e] at x4 x5 y3 y4 y5
    exact ⟨y3, y4.trans x4.symm, y5.trans x5.symm⟩
  · obtain ⟨x1, x2, x3⟩ := a4 j (by omega)
    obtain ⟨y1, y2, y3⟩ := b4 j (by omega)
    obtain ⟨k0, k1, k2⟩ := L1.keep j (x3.1 hj')
    exact ⟨y3.2 k0, (y1.trans k1).trans x1.symm, (y2.trans k2).trans x2.symm⟩

/-- One value in the own worlds of two ledgers that agree under the named slots. -/
theorem worldOf_same {G H : Fork} (mask : ℕ → GQ) (entry : ℕ → ℕ → ℕ → GQ) {f : Aff}
    (h : ∀ x ∈ f.slots.toList, H.vp.getD x.1 zeroE = G.vp.getD x.1 zeroE ∧
      H.mf.getD x.1 zeroE = G.mf.getD x.1 zeroE) :
    f.value Reading.gl (H.worldOf Reading.gl mask entry) =
      f.value Reading.gl (G.worldOf Reading.gl mask entry) := by
  refine VerifiableInference.Desc.Sound.value_eq _ _ f (fun _ _ => rfl) fun x hx => ?_
  show Reading.gl.val (H.vp.getD x.1 zeroE) - Reading.gl.val (H.mf.getD x.1 zeroE) * mask x.1 =
    Reading.gl.val (G.vp.getD x.1 zeroE) - Reading.gl.val (G.mf.getD x.1 zeroE) * mask x.1
  rw [(h x hx).1, (h x hx).2]

/-- What thereAt says of the slots: each is marked as filled, so it lies inside the array of marks.
-/
theorem there_got {G : Fork} {f : Aff} (h : thereAt G f = true) :
    ∀ x ∈ f.slots.toList, x.1 < G.gotF.size ∧ G.gotF.getD x.1 false = true := by
  intro x hx
  unfold thereAt at h
  obtain ⟨h1, _⟩ := Eq.mp (Bool.and_eq_true _ _) h
  have h2 : G.gotF.getD x.1 false = true :=
    Array.all_eq_true_iff_forall_mem.mp h1 x (Array.mem_toList_iff.mp hx)
  refine ⟨?_, h2⟩
  by_contra hlt
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)] at h2
  cases h2

/-- The same at a ledger with arrays of the right sizes. -/
theorem there_slots {G : Fork} (hG : PscRun.Sized G) {f : Aff} (h : thereAt G f = true) :
    ∀ x ∈ f.slots.toList, x.1 < G.ns ∧ G.gotF.getD x.1 false = true := fun x hx => by
  rw [← hG.2.2]
  exact there_got h x hx

/-- One value at two mask rows that agree under the slots which the form names. -/
theorem worldOf_mask {G : Fork} {mask mask' : ℕ → GQ} (entry : ℕ → ℕ → ℕ → GQ) {f : Aff}
    (h : ∀ x ∈ f.slots.toList, mask' x.1 = mask x.1) :
    f.value Reading.gl (G.worldOf Reading.gl mask' entry) =
      f.value Reading.gl (G.worldOf Reading.gl mask entry) := by
  refine VerifiableInference.Desc.Sound.value_eq _ _ f (fun _ _ => rfl) fun x hx => ?_
  show Reading.gl.val (G.vp.getD x.1 zeroE) - Reading.gl.val (G.mf.getD x.1 zeroE) * mask' x.1 =
    Reading.gl.val (G.vp.getD x.1 zeroE) - Reading.gl.val (G.mf.getD x.1 zeroE) * mask x.1
  rw [h x hx]

/-- **FormsT passes to every Sem that agrees with the first WHERE THE SENTENCE READS**: the mask
rows below n, a bound on the two ledgers' arrays of marks; the entries at what the seat finds
heard. -/
theorem formsT_sem {Sm Sm' : Sem Wt} {r₁ r₂ : Own → Fork → Option (Array Aff × Fork)} {s : S}
    {w : Wt} {n : ℕ} (hm : ∀ j, j < n → Sm'.mask w j = Sm.mask w j)
    (he : ∀ o, seatS.own s = some o → Sm'.entryT o w = Sm.entryT o w)
    (hn : ∀ o fs₁ F₁ fs₂ F₂, r₁ o (seatS.fork s) = some (fs₁, F₁) → r₂ o F₁ = some (fs₂, F₂) →
      F₁.gotF.size ≤ n ∧ F₂.gotF.size ≤ n)
    (h : FormsT seatS Sm r₁ r₂ s w) : FormsT seatS Sm' r₁ r₂ s w := by
  obtain ⟨o, fs₁, F₁, fs₂, F₂, h1, h2, h3, h4, h5⟩ := h
  obtain ⟨n1, n2⟩ := hn o fs₁ F₁ fs₂ F₂ h2 h3
  refine ⟨o, fs₁, F₁, fs₂, F₂, h1, h2, h3, fun f hf => ⟨(h4 f hf).1, ?_⟩,
    fun f hf => ⟨(h5 f hf).1, ?_⟩⟩
  · rw [he o h1, worldOf_mask _ fun x hx =>
      hm x.1 (Nat.lt_of_lt_of_le (there_got (h4 f hf).1 x hx).1 n1)]
    exact (h4 f hf).2
  · rw [he o h1, worldOf_mask _ fun x hx =>
      hm x.1 (Nat.lt_of_lt_of_le (there_got (h5 f hf).1 x hx).1 n2)]
    exact (h5 f hf).2

/-- **THE TIE**, under hs ho hA hc X hF hS · hf hb hb₁ · L1 S1 · T1 Tb T2 · E1 E2 · I1 I2. -/
theorem formsT_of_item {St : Stated} (M : S → Bound GQ → Mats GQ) (Dq : Wt → Bound GQ) {p : Par}
    {s : S}
    {b : LayOwn} {o : Own} {a : VerifiableInference.Desc.K9.Part} {c : ℕ × String}
    {tl : HTailF2} {n : ℕ} {F₁ Gb F₂ : Fork} {fs₁ fs₂ fs₂' : Array Aff} (w : Wt)
    (hs : s.here = .lay b) (ho : b.own = some o) (hA : a.L = b.L)
    (hc : b.L.arrayOf[o.v.iU3]? = some c) (X : StatedAt St M s tl o c n (Dq w)) (hF : a.F = b.F)
    (hS : PscRun.Sized b.F) (hf : frontRun p o b.F = some (fs₁, F₁))
    (hb : formsBack o b.F = some (fs₂, Gb)) (hb₁ : formsBack o F₁ = some (fs₂', F₂))
    (L1 : Later b.F F₁) (S1 : PscRun.Sized F₁)
    (T1 : ∀ f ∈ fs₁.toList, thereAt F₁ f = true) (Tb : ∀ f ∈ fs₂.toList, thereAt Gb f = true)
    (T2 : ∀ f ∈ fs₂.toList, thereAt F₂ f = true)
    (E1 : ∀ f ∈ fs₁.toList, ∀ x ∈ f.ents.toList, x.tree = o.v.iU3 ∧ x.row = 0 ∧ x.idx < n)
    (E2 : ∀ f ∈ fs₂.toList, ∀ x ∈ f.ents.toList, x.tree = o.v.iU3 ∧ x.row = 0 ∧ x.idx < n)
    (I1 : ∀ f ∈ fs₁.toList, f.value Reading.gl
      (worldOwn a (lateOf a.F F₁) (St.at1 s (Dq w))) = 0)
    (I2 : ∀ f ∈ fs₂.toList, f.value Reading.gl
      (worldOwn a (lateOf a.F Gb) (St.at1 s (Dq w))) = 0) :
    FormsT seatS (semQ tl M s Dq) (frontRun p) formsBack s w := by
  obtain ⟨e2, hk⟩ := back_two hS S1 L1 hb hb₁
  rw [e2] at hb₁
  have hown : seatS.own s = some o := by
    show (match s.here with | .lay a => a.own | _ => none) = _
    rw [hs]
    exact ho
  have hfork : seatS.fork s = b.F := by
    show (match s.here with | .lay a => a.F | _ => {}) = _
    rw [hs]
  have SGb : PscRun.Sized Gb ∧ Later b.F Gb := by
    obtain ⟨A, _, ra, rfl⟩ := formsBack_some hb
    exact ⟨(hideRun_ok _ A _ _ _ hS ra).2.1, (hideRun_later hS ra).trans (paid_later A _)⟩
  refine ⟨o, fs₁, F₁, fs₂, F₂, hown, by rw [hfork]; exact hf, hb₁, fun f hm => ⟨T1 f hm, ?_⟩,
    fun f hm => ⟨T2 f hm, ?_⟩⟩
  · rw [← I1 f hm]
    exact (value_stated hA hc X (hF ▸ L1) (there_slots S1 (T1 f hm)) (E1 f hm)).symm
  · rw [← I2 f hm, value_stated hA hc X (hF ▸ SGb.2) (there_slots SGb.1 (Tb f hm)) (E2 f hm)]
    exact worldOf_same _ _ fun x hx =>
      ((hk x.1 (there_slots SGb.1 (Tb f hm) x hx).2).2)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.back_two
#print axioms OnBytes.Road.K4.worldOf_same
#print axioms OnBytes.Road.K4.there_got
#print axioms OnBytes.Road.K4.there_slots
#print axioms OnBytes.Road.K4.worldOf_mask
#print axioms OnBytes.Road.K4.formsT_sem
#print axioms OnBytes.Road.K4.formsT_of_item
