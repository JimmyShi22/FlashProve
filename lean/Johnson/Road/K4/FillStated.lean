-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/FillStated.lean: THE STATED FUNCTION OF THE READS AT A LAYERS' SEGMENT, UP TO ONE
LETTER M: toward a filling of the letter u of Stated.of u (Johnson/Desc/Sound/FormsT.lean: "the
stated function: left, sort by sort of segment, to the kind that hears there, over D's own
cells": THAT LAST CLAUSE IS WHAT M LEAVES OPEN), AND THE TWO WORLDS OF A FORM MADE ONE: the world in
which the table of joints' sentence formsT reads a form (worldOwn, Johnson/Desc/Sound/FormsQ.lean)
against the world in which the statement of K4's law reads it (Fork.worldOf at the ledger behind the
run, OnBytes/Model/HideLaws.lean; AllZero, Johnson/Desc/Plain/K04Plain.lean).

  `uLay tl M`: tl: A PARAMETER: meant: THE PUBLIC PARAMETERS of the approximate range proof at that
    link (not the verifier's state's own copy: in front of the second sending no item of the table
    ties that copy to the public parameters). At a verifier's state inside a layers' link that holds
    what K4 has heard (o): cell (r, i) of THE ARRAY OF THE READS is entryTrue tl o (M s D) at the
    reads' number (Johnson/Road/K4/EntryTrue.lean): the sum of a table of o.funs that owns the
    place, over the matrices M s D (one table only where the tables lie apart); 0 WHERE NO TABLE
    OWNS IT. Every other array, and every other state, keeps D's cell: in front of the second
    sending that is 0, in silence, at an array of that sending. M: A LETTER: entry (r, c) of matrix
    number a of the approximate range proof's list, as a function of the data D.
  `StatedAt St M s tl o c n D`: WHAT THE LAWS BELOW ASK OF A LETTER St AT ONE STATE: at the array c,
    IN ROW 0, BELOW n, its cells are entryTrue; the mask row is D's. Not at all rows and places:
    another text of the entries (K5Law.entryOf, Johnson/Desc/First/Att/Claims/TabsByChoice.lean)
    parts from entryTrue at a place at or above the number of columns. St IS ONE LETTER FOR ALL
    SORTS OF SEGMENT: a table's St is made of several kinds' functions: so the laws are stated at
    every St with StatedAt, not at Stated.of (uLay tl M) to the letter.
  `statedAt_of`: Stated.of u has it wherever u gives uLay's cells at c. `statedAt_uLay`: so at uLay.
  `slotW_lateOf`: under a slot that is filled in a later ledger G, below its number of slots, the
    forms' world at late := lateOf F G has what G's own world has. General in the kind.
  `entry_stated`: at the reads' number, in row 0, below n, the forms' world has entryTrue.
  `value_stated`: so a form whose slots are filled at G and whose entries all name row 0 of the
    array of the reads, below n, has ONE value in the two worlds.
No new argument. Kin: the three small laws on lateOf (private here) stand also in
Johnson/Top/H0/MergeLaw/LateTie.lean.
Limits. M IS A LETTER: which cell of D is entry (r, c) of matrix a is said by nobody. THE STATED
DATA TURN WHERE K4's SUB-PROTOCOL ACCEPTS (own: none, then some o): an item that is open across K4
at the same St must be carried over that turn by whoever rides it. PREMISES of value_stated: the
part a has the link's context (hA) · the layout's name c of the reads' array (hc) · StatedAt (X) · G
is later than the part's ledger (hL) · each slot that the form names is filled in G and below its
number of slots (hsl) · each entry that it names has the reads' number, row 0 and a place below n
(hen). Of statedAt_of: the verifier's state stands in a layers' link and holds o (hs, ho) · hc · c
is of the segment's second sending (h2: a line on the link's layout: shown by nobody) · u's tie
(hu). NOT HERE: that a reader's forms are a run's; that the forms are worth 0 anywhere. Met through
Lean at no member. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on
soundness.


-/
import Johnson.Desc.Sound.FormsT
import Johnson.Desc.First.Batch.ReaderOf
import Johnson.Road.K4.EntryTrue
import OnBytes.Tie.Pv.Psc.PscLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Road.K4

open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.PscRun (Later Filled)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (segAt? lateAt lateOf)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ Stated second slotW slotW_late slotW_ledger worldOwn
  value_eq of_second of_mask)

/-- **The stated function of the reads at a layers' segment.** -/
def uLay (tl : HTailF2) (M : S → Bound GQ → Mats GQ) : S → Bound GQ → ℕ × String → ℕ → ℕ → GQ :=
  fun s D c r i =>
  match s.here with
  | .lay a =>
    match a.own with
    | some o =>
      if a.L.arrayOf[o.v.iU3]? = some c then entryTrue tl o (M s D) o.v.iU3 r i
      else D.cell c.1 c.2 r i
    | none => D.cell c.1 c.2 r i
  | _ => D.cell c.1 c.2 r i

/-- A member of lateOf's list: its slot is free in F, filled in G, and it holds G's values. -/
private theorem mem_lateOf {F G : Fork} {x : ℕ × E × E} (h : x ∈ lateOf F G) :
    x.1 < G.ns ∧ F.gotF.getD x.1 false = false ∧ G.gotF.getD x.1 false = true ∧
      x.2 = (G.vp.getD x.1 zeroE, G.mf.getD x.1 zeroE) := by
  unfold lateOf at h
  obtain ⟨j, hj, hx⟩ := List.mem_filterMap.1 h
  by_cases hc : (!(F.gotF.getD j false) && G.gotF.getD j false) = true
  · rw [if_pos hc] at hx
    obtain rfl := Option.some.inj hx
    obtain ⟨c1, c2⟩ := Eq.mp (Bool.and_eq_true _ _) hc
    exact ⟨List.mem_range.1 hj, by simpa using c1, c2, rfl⟩
  · rw [if_neg hc] at hx
    exact nomatch hx

/-- A slot that is free in F and filled in G, below G's number of slots, is late, at G's values. -/
private theorem lateAt_lateOf {F G : Fork} {j : ℕ} (hj : j < G.ns)
    (hF : F.gotF.getD j false = false)
    (hG : G.gotF.getD j false = true) :
    lateAt (lateOf F G) j = some (G.vp.getD j zeroE, G.mf.getD j zeroE) := by
  have hm : (j, G.vp.getD j zeroE, G.mf.getD j zeroE) ∈ lateOf F G := by
    unfold lateOf
    refine List.mem_filterMap.2 ⟨j, List.mem_range.2 hj, ?_⟩
    rw [if_pos (by rw [hF, hG]; rfl)]
  unfold lateAt
  cases e : (lateOf F G).find? (fun x => x.1 == j) with
  | none =>
    have := List.find?_eq_none.1 e _ hm
    simp at this
  | some x =>
    have h1 : x.1 = j := by simpa using List.find?_some e
    obtain ⟨_, _, _, h4⟩ := mem_lateOf (List.mem_of_find?_eq_some e)
    show some x.2 = _
    rw [h4, h1]

/-- A slot that is filled in F is not late. -/
private theorem lateAt_none {F G : Fork} {j : ℕ} (hF : F.gotF.getD j false = true) :
    lateAt (lateOf F G) j = none := by
  unfold lateAt
  cases e : (lateOf F G).find? (fun x => x.1 == j) with
  | none => rfl
  | some x =>
    have h1 : x.1 = j := by simpa using List.find?_some e
    obtain ⟨_, h2, _, _⟩ := mem_lateOf (List.mem_of_find?_eq_some e)
    rw [h1, hF] at h2
    cases h2

/-- **Under a slot that is filled in a later ledger G the forms' world has what G's own world
has.** -/
theorem slotW_lateOf {F G : Fork} (hL : Later F G) (mask : ℕ → GQ) {j : ℕ} (hj : j < G.ns)
    (hG : G.gotF.getD j false = true) :
    slotW F (lateOf F G) mask j =
      Reading.gl.val (G.vp.getD j zeroE) - Reading.gl.val (G.mf.getD j zeroE) * mask j := by
  cases hF : F.gotF.getD j false with
  | false => rw [slotW_late F _ mask j _ (lateAt_lateOf hj hF hG)]
  | true =>
    obtain ⟨_, k1, k2⟩ := hL.keep j hF
    rw [slotW_ledger F _ mask j (lateAt_none hF), k1, k2]

/-- **What the laws below ask of a letter St at one state of the verifier**: at the array c, IN ROW
0, BELOW n, its cells are entryTrue at tl (a parameter: meant: the public parameters of the
approximate range proof) and o; the mask row is D's. -/
structure StatedAt (St : Stated) (M : S → Bound GQ → Mats GQ) (s : S) (tl : HTailF2) (o : Own)
    (c : ℕ × String) (n : ℕ) (D : Bound GQ) : Prop where
  cell : ∀ i, i < n → (St.at1 s D).cell c.1 c.2 0 i = entryTrue tl o (M s D) o.v.iU3 0 i
  mask : (St.at1 s D).mask = D.mask

/-- uLay's cells at the reads' array, under hs, ho, hc. -/
theorem uLay_cell (tl : HTailF2) (M : S → Bound GQ → Mats GQ) {s : S}
    {b : VerifiableInference.Desc.First.LayOwn} {o : Own} {c : ℕ × String}
    (hs : s.here = .lay b) (ho : b.own = some o) (hc : b.L.arrayOf[o.v.iU3]? = some c)
    (D : Bound GQ) (r i : ℕ) : uLay tl M s D c r i = entryTrue tl o (M s D) o.v.iU3 r i := by
  unfold uLay
  rw [hs]
  show (match b.own with
    | some o' =>
      if b.L.arrayOf[o'.v.iU3]? = some c then entryTrue tl o' (M s D) o'.v.iU3 r i
      else D.cell c.1 c.2 r i
    | none => D.cell c.1 c.2 r i) = _
  rw [ho]
  show (if b.L.arrayOf[o.v.iU3]? = some c then entryTrue tl o (M s D) o.v.iU3 r i
    else D.cell c.1 c.2 r i) = _
  rw [if_pos hc]

/-- Stated.of u has StatedAt wherever u gives uLay's cells at c (hs, ho, hc, h2, hu). -/
theorem statedAt_of (u : S → Bound GQ → ℕ × String → ℕ → ℕ → GQ) (tl : HTailF2)
    (M : S → Bound GQ → Mats GQ) {s : S} {b : VerifiableInference.Desc.First.LayOwn} {o : Own}
    {c : ℕ × String}
    (hs : s.here = .lay b) (ho : b.own = some o) (hc : b.L.arrayOf[o.v.iU3]? = some c)
    (h2 : second s c = true) (n : ℕ) (D : Bound GQ)
    (hu : ∀ i, i < n → u s D c 0 i = uLay tl M s D c 0 i) :
    StatedAt (Stated.of u) M s tl o c n D :=
  ⟨fun i hi => by rw [of_second u s D c 0 i h2, hu i hi, uLay_cell tl M hs ho hc D 0 i],
    of_mask u s D⟩

/-- So at uLay itself (hs, ho, hc, h2). -/
theorem statedAt_uLay (tl : HTailF2) (M : S → Bound GQ → Mats GQ) {s : S}
    {b : VerifiableInference.Desc.First.LayOwn} {o : Own} {c : ℕ × String}
    (hs : s.here = .lay b) (ho : b.own = some o) (hc : b.L.arrayOf[o.v.iU3]? = some c)
    (h2 : second s c = true) (n : ℕ) (D : Bound GQ) :
    StatedAt (Stated.of (uLay tl M)) M s tl o c n D :=
  statedAt_of (uLay tl M) tl M hs ho hc h2 n D fun _ _ => rfl

/-- At the reads' number, in row 0, below n, the forms' world has entryTrue (hA, hc, X). -/
theorem entry_stated {St : Stated} {M : S → Bound GQ → Mats GQ} {s : S}
    {b : VerifiableInference.Desc.First.LayOwn} {o : Own} {a : VerifiableInference.Desc.K9.Part}
    {tl : HTailF2} {c : ℕ × String} {n : ℕ} {D : Bound GQ} (hA : a.L = b.L)
    (hc : b.L.arrayOf[o.v.iU3]? = some c) (X : StatedAt St M s tl o c n D)
    (late : List (ℕ × E × E)) {i : ℕ} (hi : i < n) :
    (worldOwn a late (St.at1 s D)).entry o.v.iU3 0 i = entryTrue tl o (M s D) o.v.iU3 0 i := by
  show (match a.L.arrayOf[o.v.iU3]? with
    | some x => (St.at1 s D).cell x.1 x.2 0 i
    | none => 0) = _
  rw [hA, hc]
  exact X.cell i hi

/-- **One value in the two worlds**, under hA, hc, X, hL, hsl, hen. -/
theorem value_stated {St : Stated} {M : S → Bound GQ → Mats GQ} {s : S}
    {b : VerifiableInference.Desc.First.LayOwn} {o : Own} {a : VerifiableInference.Desc.K9.Part}
    {tl : HTailF2} {c : ℕ × String} {n : ℕ} {G : Fork} {D : Bound GQ} (hA : a.L = b.L)
    (hc : b.L.arrayOf[o.v.iU3]? = some c) (X : StatedAt St M s tl o c n D) (hL : Later a.F G)
    {f : Aff} (hsl : ∀ x ∈ f.slots.toList, x.1 < G.ns ∧ G.gotF.getD x.1 false = true)
    (hen : ∀ x ∈ f.ents.toList, x.tree = o.v.iU3 ∧ x.row = 0 ∧ x.idx < n) :
    f.value Reading.gl (worldOwn a (lateOf a.F G) (St.at1 s D)) =
      f.value Reading.gl (G.worldOf Reading.gl D.mask (entryTrue tl o (M s D))) := by
  refine value_eq _ _ f (fun x hx => ?_) fun x hx => ?_
  · obtain ⟨e1, e2, e3⟩ := hen x hx
    rw [e1, e2]
    exact entry_stated hA hc X _ e3
  · show slotW a.F (lateOf a.F G) (St.at1 s D).mask x.1 = _
    rw [X.mask]
    exact slotW_lateOf hL D.mask (hsl x hx).1 (hsl x hx).2

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.slotW_lateOf
#print axioms OnBytes.Road.K4.uLay_cell
#print axioms OnBytes.Road.K4.statedAt_of
#print axioms OnBytes.Road.K4.statedAt_uLay
#print axioms OnBytes.Road.K4.entry_stated
#print axioms OnBytes.Road.K4.value_stated
