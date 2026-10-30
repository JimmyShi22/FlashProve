-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/PubAtLaterIndex.lean: FOUR
PUBLIC ITEMS OF THE TABLE OF JOINTS ARE KEPT BY A LATER MOMENT's SENDING OF KIND K1: indexIs,
indexThere, formsIn m k r, formsInT m k r: where the composed Bool of all layers (pubAll,
Johnson/Desc/First/PubAll.lean) says yes of the state in front of a yes of the block, it says yes
of the state behind. Definitions, and statements with their proofs.
OBJECT. The blocks B with LaterSend P B. Two members are shown: laterAt
(Johnson/Desc/K1/Places.lean: a link's digits; it is commitAtS, Johnson/Desc/K1/AtS.lean, at the
plan's numbers), and the reads' place's joined block k1Reads (Johnson/IMR/K1Seat.lean: the sending of the
reads with the quiet step joined behind it by Block.andThen). The Bools: K13.indexIsC,
K13.indexThereC (Johnson/Desc/K13/PubK13.lean) and K9.formsIn, K9.formsInA, K9.formsInT
(Johnson/Desc/First/Batch/FormsIn.lean, Ahead.lean), and through them pubAll D base at the four
items.
USER. The field pub of FillL (Johnson/Desc/K1/Law/KeepAtLater.lean) at the fifty later
places, at these four items; the Bool in front is had from the promise in front.
LETTERS. D : PubData and base: pubAll's: any. x, x': the chain's states with their public parts,
which are not read. rs: any two rounds. P: the place.
Main names:
  PartRides new a b   what the tests on forms read of the open segment's part is left or grows: the
                      arrays' map, the layout, the request's shape, the link's number, the slots; a
                      message that is found stays found, under its number; one that is found only
                      behind has a number of new; the book's older places stay.
  arrayIn_rides, entIn_rides, maskSeat_rides, lateOk_rides, slotIn_rides, affIn_rides,
  entInT_rides, affInT_rides, aheadOf_rides, entInA_rides, affInA_rides: each test, from a to b.
  RecRides new s s'   the same of two states, with the merge's slot. segAt_some, segAt_mk.
  formsIn_rides, formsInT_rides, formsInA_rides: the three tests at the state, at one run.
  whereIs_there, whereIs_fresh, commitAtS_layout, merge_put.
  commitAtS_rides: **a yes of commitAtS.**
  QuietP q            a yes of q leaves the statement, the book, "out", the open link's context, the
                      ledger, the merge's slot, whether the smallness test's fields is there, the
                      count of roots and the rows on the table.
  quietP_layers, _head, _att, _blockAt, _readsQuietAt, quietP_orLoud. RecRides.quiet.
  joined_yes, joined_rides, joined_index, joined_booked: **a yes of the joined block.**
  seats_new, seats_in_group: the premise hseat, from the book in front and a test on the plan.
  pubAll_indexIs, _indexThere, _formsIn, _formsInT: what pubAll is at the four, by unfolding.
  ReadersStay D m k r s s', readersStay_of_eq. indexIs_kept, indexThere_kept, formsIn_kept,
  formsInT_kept: the four items from IndexKept and RecRides.
  LaterSend P B; laterSend_commitAtS, laterSend_laterAt, laterSend_joined, laterSend_k1Reads.
  pub_indexIs_later, pub_indexThere_later, pub_formsIn_later (pub_formsIn_later_plan),
  pub_formsInT_later: **AN ITEM EACH, OVER THE BLOCK's OWN YES.**
PREMISES THAT STAY. At indexIs and indexThere: none but the yes. At formsIn and formsInT:
ReadersStay: AT EACH RUN THAT THE ITEM NAMES, WHAT THE SEGMENT's READER GAVE IN FRONT IT GIVES
BEHIND. The readers D.Rd are a letter: it is shown here of no reader; a reader that does not read
the state meets it. (formsQA_back, Johnson/Desc/Sound/FormsAhead.lean, asks the equation,
which is the stronger.) At formsIn alone, hseat: EACH NEW MESSAGE SITS, BY THE BOOK BEHIND, AT A
SEAT OF THE GROUP D.N.group m: an array that was ahead in front and is sent behind is then found by
the state. pub_formsIn_later_plan pays it where m is the sending's own segment: off the book in
front and a test with code on the plan.
IS IT EMPTY HERE? That a block ever says yes is not shown here. Where the Bool in front says no
nothing is said.






It imports Johnson/Desc/K1/Law/FrameAtLater.lean
(through LinkAtLater.lean).
What is not claimed. That the items are open at any border. That ReadersStay or hseat holds at the
plan's own numbers and readers. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.First.PubAll
import Johnson.Desc.K13.Law.IndexKept
import Johnson.Desc.K1.Law.LinkAtLater
import Johnson.Desc.K1.Law.TlAtRecord
import Johnson.Desc.K1.Law.NextKept
import Johnson.Desc.K1.KeepsSlots
import Johnson.Desc.K8.ReadsQuietLaws
import Johnson.Goal.Meaning.RecReadsAtt
import Johnson.Desc.K1.Places
import Johnson.IMR.K1Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S Pub PubData pubAll)
open VerifiableInference.Desc.K13.Law (IndexKept indexKept_of)
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc.K9 (Read Readers segAt? mergeOf seatAt seatAt_rides arrayIn
  arrayIn_some entIn entIn_some maskAt maskSeat lateOk slotIn affIn atMoment1 entInT affInT formsIn
  formsInT Ahead aheadOf aheadIn entInA affInA formsInA)

variable {Cl Pp : Type}

/-! ## The open segment's part -/

/-- **What the tests on forms read of the open segment's part is left or grows.** new: the numbers
of the messages that are found behind and not in front. -/
structure PartRides (new : List Nat) (a b : K9.Part) : Prop where
  arrayOf : b.L.arrayOf = a.L.arrayOf
  rows : b.L.check.rows = a.L.check.rows
  shape : b.L.check.frame.shape = a.L.check.frame.shape
  link : b.L.check.frame.link = a.L.check.frame.link
  there : ∀ l m o, a.L.check.frame.whereIs l m = some o → b.L.check.frame.whereIs l m = some o
  fresh : ∀ l m o, a.L.check.frame.whereIs l m = none → b.L.check.frame.whereIs l m = some o →
    o ∈ new
  place : ∀ (o : Nat) (y : Nat × Nat), a.d.book.place[o]? = some y → b.d.book.place[o]? = some y
  slots : PscRun.SlotsSame a.F b.F

/-- A part with the same link's context, ledger and book rides as well. -/
theorem PartRides.congr {new : List Nat} {a b c : K9.Part} (R : PartRides new a b)
    (e1 : c.L = b.L) (e2 : c.F = b.F) (e3 : c.d.book = b.d.book) : PartRides new a c := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e1]; exact R.arrayOf
  · rw [e1]; exact R.rows
  · rw [e1]; exact R.shape
  · rw [e1]; exact R.link
  · rw [e1]; exact R.there
  · rw [e1]; exact R.fresh
  · rw [e3]; exact R.place
  · rw [e2]; exact R.slots

section
variable {new : List Nat} {a b : K9.Part} (R : PartRides new a b) (own : List (Nat × Nat))
  (free : Option Nat) (late : List (Nat × E × E))
include R

theorem arrayIn_rides {t : Nat} {A : Params.ReqArray} (h : arrayIn own a t = some A) :
    arrayIn own b t = some A := by
  obtain ⟨c, o, x, h1, h2, h3, h4⟩ := arrayIn_some own a t A h
  simp only [arrayIn, R.arrayOf, h1, R.rows, h2, R.there _ _ _ h3,
    seatAt_rides own _ _ o x (R.place o) h4, Option.bind_some, Option.map_some]

theorem entIn_rides {x : Ent} (h : entIn own a x = true) : entIn own b x = true := by
  obtain ⟨A, hA⟩ := entIn_some own a x h
  unfold entIn at h ⊢
  rw [hA] at h
  rw [arrayIn_rides R own hA]
  exact h

theorem maskSeat_rides (h : (maskSeat own a).isSome = true) : (maskSeat own b).isSome = true := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 h
  unfold maskSeat at hx ⊢
  obtain ⟨o, ho, hx⟩ := Option.bind_eq_some_iff.1 hx
  unfold maskAt at ho
  obtain ⟨m, hm, hw⟩ := Option.bind_eq_some_iff.1 ho
  have hb : maskAt b.L.check.frame = some o := by
    unfold maskAt
    rw [R.shape, R.link, hm]
    exact R.there _ _ _ hw
  rw [hb]
  show (seatAt own b.d.book o).isSome = true
  rw [seatAt_rides own _ _ o x (R.place o) hx]
  rfl

theorem lateOk_rides : lateOk late b = lateOk late a := by
  unfold lateOk
  rw [R.slots.ns, R.slots.gotF, R.slots.vp, R.slots.mf]

theorem slotIn_rides {j : Nat} (h : slotIn own free late a j = true) :
    slotIn own free late b j = true := by
  unfold slotIn at h ⊢
  rw [R.slots.ns, R.slots.gotF, R.slots.vp, R.slots.mf]
  rw [Bool.and_eq_true, Bool.and_eq_true] at h ⊢
  exact ⟨h.1, maskSeat_rides R own h.2.1, h.2.2⟩

theorem affIn_rides {f : Aff} (h : affIn own free late a f = true) :
    affIn own free late b f = true := by
  unfold affIn at h ⊢
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h ⊢
  exact ⟨fun x hx => entIn_rides R own (h.1 x hx),
    fun x hx => slotIn_rides R own free late (h.2 x hx)⟩

theorem atMoment1_rides (c : Nat × String) (A : Params.ReqArray) :
    atMoment1 b c A = atMoment1 a c A := by
  unfold atMoment1
  rw [R.link, R.shape]

theorem entInT_rides {x : Ent} (h : entInT own a x = true) : entInT own b x = true := by
  unfold entInT at h ⊢
  rw [Bool.or_eq_true] at h ⊢
  rcases h with h | h
  · exact Or.inl (entIn_rides R own h)
  · refine Or.inr ?_
    rw [R.arrayOf, R.rows]
    simp only [atMoment1_rides R]
    exact h

theorem affInT_rides {f : Aff} (h : affInT own free late a f = true) :
    affInT own free late b f = true := by
  unfold affInT at h ⊢
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h ⊢
  exact ⟨fun x hx => entInT_rides R own (h.1 x hx),
    fun x hx => slotIn_rides R own free late (h.2 x hx)⟩

variable (sent : Nat → List (Nat × Nat))

/-- An array that is ahead in front is ahead behind, with the same seat; or it is sent, under a new
number. -/
theorem aheadOf_rides {c : Nat × String} {hh : Ahead} (e : aheadOf sent a c = some hh) :
    aheadOf sent b c = some hh ∨
      ∃ o, reqArray a.L.check.rows.layout c.1 c.2 = some hh.A ∧
        b.L.check.frame.whereIs c.1 hh.A.message = some o ∧ o ∈ new := by
  unfold aheadOf at e ⊢
  rw [R.link, R.rows, R.shape]
  split at e
  · rename_i hl
    rw [if_pos hl]
    obtain ⟨A, hA, e⟩ := Option.bind_eq_some_iff.1 e
    rw [hA]
    split at e
    · cases e
    · rename_i hw
      have hAeq : hh.A = A := by
        obtain ⟨ms, _, e'⟩ := Option.bind_eq_some_iff.1 e
        obtain ⟨M, _, e'⟩ := Option.bind_eq_some_iff.1 e'
        split at e'
        · cases e'
        · obtain ⟨x, _, e'⟩ := Option.map_eq_some_iff.1 e'
          subst e'
          rfl
      cases hb : b.L.check.frame.whereIs c.1 A.message with
      | none =>
        refine Or.inl ?_
        simp only [Option.bind_some, hb]
        exact e
      | some o =>
        refine Or.inr ⟨o, by rw [hAeq], by rw [hAeq]; exact hb, R.fresh _ _ _ hw hb⟩
  · cases e

theorem entInA_rides (hseat : ∀ o ∈ new, (seatAt own b.d.book o).isSome = true) {x : Ent}
    (h : entInA sent own a x = true) : entInA sent own b x = true := by
  unfold entInA at h ⊢
  rw [Bool.or_eq_true] at h ⊢
  rcases h with h | h
  · exact Or.inl (entIn_rides R own h)
  · cases e1 : a.L.arrayOf[x.tree]? with
    | none =>
      rw [e1] at h
      cases h
    | some c =>
      rw [e1, Option.bind_some] at h
      cases e2 : aheadIn sent own a c with
      | none =>
        rw [e2] at h
        cases h
      | some hh =>
        rw [e2] at h
        unfold aheadIn at e2
        obtain ⟨e3, e4⟩ := Option.filter_eq_some_iff.1 e2
        rcases aheadOf_rides R sent e3 with e5 | ⟨o, hA, hw, hn⟩
        · refine Or.inr ?_
          have e6 : aheadIn sent own b c = some hh := by
            unfold aheadIn
            exact Option.filter_eq_some_iff.2 ⟨e5, e4⟩
          rw [R.arrayOf, e1, Option.bind_some, e6]
          exact h
        · refine Or.inl ?_
          obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (hseat o hn)
          have e6 : arrayIn own b x.tree = some hh.A := by
            simp only [arrayIn, R.arrayOf, e1, R.rows, hA, hw, hy, Option.bind_some,
              Option.map_some]
          unfold entIn
          rw [e6]
          exact h

theorem affInA_rides (hseat : ∀ o ∈ new, (seatAt own b.d.book o).isSome = true) {f : Aff}
    (h : affInA sent own free late a f = true) : affInA sent own free late b f = true := by
  unfold affInA at h ⊢
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h ⊢
  exact ⟨fun x hx => entInA_rides R own sent hseat (h.1 x hx),
    fun x hx => slotIn_rides R own free late (h.2 x hx)⟩

end

/-! ## The chain's state -/

theorem segAt_some {s : S} {a : K9.Part} (h : segAt? s = some a) :
    ∃ tl, s.link? = some a.L ∧ s.fork? = some a.F ∧ s.tl? = some tl ∧ a.d.book = s.book := by
  unfold segAt? at h
  cases hL : s.link? with
  | none => simp [hL] at h
  | some L =>
    cases hF : s.fork? with
    | none => simp [hL, hF] at h
    | some F =>
      cases ht : s.tl? with
      | none => simp [hL, hF, ht] at h
      | some tl =>
        simp [hL, hF, ht] at h
        subst h
        exact ⟨tl, rfl, rfl, rfl, rfl⟩

theorem segAt_mk {s : S} {L : LinkCtx} {F : Fork} {tl : HTailF2} (hL : s.link? = some L)
    (hF : s.fork? = some F) (ht : s.tl? = some tl) :
    ∃ a, segAt? s = some a ∧ a.L = L ∧ a.F = F ∧ a.d.book = s.book := by
  refine ⟨{ owed := K9.owedOf s, used := (K9.usedOf s).getD 0, laid := K9.laidOf tl, L := L, F := F,
            d := { st := s.st, book := s.book, roots := s.roots, opened := [], loc := () } },
    ?_, rfl, rfl, rfl⟩
  unfold segAt?
  rw [hL, hF, ht]
  rfl

/-- **The same of two states.** -/
structure RecRides (new : List Nat) (s s' : S) : Prop where
  seg : ∀ a, segAt? s = some a → ∃ b, segAt? s' = some b ∧ PartRides new a b
  merge : mergeOf s' = mergeOf s

section
variable {new : List Nat} {s s' : S} (R : RecRides new s s') (Rd : Readers)
  (own : List (Nat × Nat)) (piece : Nat) (run : String)
  (hRd : ∀ X, Rd.forms piece run s = some X → Rd.forms piece run s' = some X)
include R hRd

/-- **"formsIn" at one run.** -/
theorem formsIn_rides (h : formsIn Rd own piece run s = true) :
    formsIn Rd own piece run s' = true := by
  unfold formsIn at h ⊢
  cases ea : segAt? s with
  | none =>
    rw [ea] at h
    cases h
  | some a =>
    cases er : Rd.forms piece run s with
    | none =>
      rw [ea, er] at h
      cases h
    | some X =>
      rw [ea, er] at h
      obtain ⟨b, hb, hR⟩ := R.seg a ea
      rw [hb, hRd X er, R.merge]
      have h' : (lateOk X.late a && X.forms.all fun f => affIn own (mergeOf s) X.late a f) = true :=
        h
      show (lateOk X.late b && X.forms.all fun f => affIn own (mergeOf s) X.late b f) = true
      rw [Bool.and_eq_true, List.all_eq_true] at h' ⊢
      exact ⟨by rw [lateOk_rides hR]; exact h'.1, fun f hf => affIn_rides hR own _ _ (h'.2 f hf)⟩

/-- **"formsInT" at one run.** -/
theorem formsInT_rides (h : formsInT Rd own piece run s = true) :
    formsInT Rd own piece run s' = true := by
  unfold formsInT at h ⊢
  cases ea : segAt? s with
  | none =>
    rw [ea] at h
    cases h
  | some a =>
    cases er : Rd.forms piece run s with
    | none =>
      rw [ea, er] at h
      cases h
    | some X =>
      rw [ea, er] at h
      obtain ⟨b, hb, hR⟩ := R.seg a ea
      rw [hb, hRd X er, R.merge]
      have h' : (lateOk X.late a &&
          X.forms.all fun f => affInT own (mergeOf s) X.late a f) = true := h
      show (lateOk X.late b && X.forms.all fun f => affInT own (mergeOf s) X.late b f) = true
      rw [Bool.and_eq_true, List.all_eq_true] at h' ⊢
      exact ⟨by rw [lateOk_rides hR]; exact h'.1, fun f hf => affInT_rides hR own _ _ (h'.2 f hf)⟩

/-- **"formsInA" at one run**: where each new message sits at a seat of own. -/
theorem formsInA_rides (sent : Nat → List (Nat × Nat))
    (hseat : ∀ o ∈ new, (seatAt own s'.book o).isSome = true)
    (h : formsInA Rd sent own piece run s = true) : formsInA Rd sent own piece run s' = true := by
  unfold formsInA at h ⊢
  cases ea : segAt? s with
  | none =>
    rw [ea] at h
    cases h
  | some a =>
    cases er : Rd.forms piece run s with
    | none =>
      rw [ea, er] at h
      cases h
    | some X =>
      rw [ea, er] at h
      obtain ⟨b, hb, hR⟩ := R.seg a ea
      obtain ⟨_, _, _, _, hbk⟩ := segAt_some hb
      rw [hb, hRd X er, R.merge]
      have h' : (lateOk X.late a &&
          X.forms.all fun f => affInA sent own (mergeOf s) X.late a f) = true := h
      show (lateOk X.late b && X.forms.all fun f => affInA sent own (mergeOf s) X.late b f) = true
      rw [Bool.and_eq_true, List.all_eq_true] at h' ⊢
      exact ⟨by rw [lateOk_rides hR]; exact h'.1,
        fun f hf => affInA_rides hR own _ _ sent (by rw [hbk]; exact hseat) (h'.2 f hf)⟩

end

/-! ## The sending -/

theorem whereIs_there (f : ReqFrame) (k : Nat) (ids : Array Nat) (l m o : Nat)
    (h : f.whereIs l m = some o) :
    ({ f with moment := k, own := f.own ++ ids } : ReqFrame).whereIs l m = some o := by
  unfold ReqFrame.whereIs at h ⊢
  dsimp only
  split at h
  · cases h
  · rename_i h1
    rw [if_neg h1]
    split at h
    · rename_i h2
      rw [if_pos h2]
      have hlt : m < f.own.size := by
        by_contra hn
        rw [Array.getElem?_eq_none (by omega)] at h
        cases h
      rw [Array.getElem?_append_left hlt]
      exact h
    · rename_i h2
      rw [if_neg h2]
      exact h

theorem whereIs_fresh (f : ReqFrame) (k : Nat) (ids : Array Nat) (l m o : Nat)
    (h0 : f.whereIs l m = none)
    (h : ({ f with moment := k, own := f.own ++ ids } : ReqFrame).whereIs l m = some o) :
    o ∈ ids.toList := by
  unfold ReqFrame.whereIs at h0 h
  dsimp only at h
  split at h
  · cases h
  · rename_i h1
    rw [if_neg h1] at h0
    split at h
    · rename_i h2
      rw [if_pos h2] at h0
      have hge : f.own.size ≤ m := by
        by_contra hn
        rw [Array.getElem?_eq_getElem (by omega)] at h0
        cases h0
      rw [Array.getElem?_append_right hge, ← Array.getElem?_toList] at h
      exact List.mem_of_getElem? h
    · rename_i h2
      rw [if_neg h2] at h0
      rw [h0] at h
      cases h

/-- The kind's block leaves the layout. -/
theorem commitOwn_layout (P : Par) (link moment : Nat) (arrays : Option (List Nat))
    (s s' : Owing (L3.St (DState Unit))) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitOwn P link moment arrays : Block _ Cl).decide s rs gs = .ok s') :
    s'.held.L.check.rows = s.held.L.check.rows := by
  unfold commitOwn at h
  dsimp only at h
  split at h
  · split at h
    · cases h
    · obtain ⟨t, ht, rfl⟩ := (map_ok _ _ _).1 h
      unfold L3.commitStep at ht
      obtain ⟨_, _, ht⟩ := (bind_ok _ _ _).1 ht
      obtain ⟨⟨check, w⟩, h2, ht⟩ := (bind_ok _ _ _).1 ht
      obtain ⟨⟨L, F⟩, h3, ht⟩ := (bind_ok _ _ _).1 ht
      have e : ({ s.held with L := L, F := F, w := w } : L3.St (DState Unit)) = t := by
        simpa [pure, Except.pure] using ht
      obtain ⟨ids, d₁, f', _, _, a3⟩ := laterOwn_ok P s.owed _ _ _ _ _ h2
      unfold L3.commitBehind at h3
      obtain ⟨F₁, _, h3⟩ := (bind_ok _ _ _).1 h3
      split at h3
      · have e3 := (Prod.mk.inj (Except.ok.inj h3)).1
        rw [← e, ← e3, a3]
      · cases h3
  · cases h

theorem commitAtS_layout (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (s s' : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s rs gs = .ok s') :
    ∃ L L', s.link? = some L ∧ s'.link? = some L' ∧ L'.check.rows = L.check.rows := by
  unfold commitAtS at h
  dsimp only at h
  split at h
  · rename_i L F tl hL _ _
    obtain ⟨y, hy, rfl⟩ := (map_ok _ _ _).1 h
    exact ⟨L, y.held.L, hL, link_put s _ L _ _ hL,
      commitOwn_layout P link moment arrays _ y rs gs hy⟩
  · cases h

/-- The puts leave the merge's slot. -/
theorem merge_put (s : S) (w : DState Unit) (L' : LinkCtx) (F' : Fork) :
    mergeOf (((laid s w).putLink L').putFork F') = mergeOf s := by
  cases hs : s.here with
  | head a => by_cases ho : a.opened = true <;> simp [mergeOf, S.putFork, S.putLink, laid, hs, ho]
  | _ => simp [mergeOf, S.putFork, S.putLink, laid, hs]

/-- **A YES OF THE SENDING.** -/
theorem commitAtS_rides (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (s s' : S)
    (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s [r₁, r₂] gs = .ok s') :
    RecRides (idsOf P s.st.oracles.size).toList s s' := by
  obtain ⟨L, L', hL, hL', hfr, _⟩ := commitAtS_frame P link moment arrays s s' r₁ r₂ gs h
  obtain ⟨L₁, L₁', a1, a2, _, _, harr⟩ := commitAtS_moments P link moment arrays s s' _ gs h
  obtain rfl : L = L₁ := Option.some.inj (hL.symm.trans a1)
  obtain rfl : L' = L₁' := Option.some.inj (hL'.symm.trans a2)
  obtain ⟨L₂, L₂', b1, b2, hrows⟩ := commitAtS_layout P link moment arrays s s' _ gs h
  obtain rfl : L = L₂ := Option.some.inj (hL.symm.trans b1)
  obtain rfl : L' = L₂' := Option.some.inj (hL'.symm.trans b2)
  obtain ⟨_, F, tl, y, _, hF, ht, hs, hsl⟩ := commitAtS_slots h
  have hF' : s'.fork? = some y.F := by
    rw [hs]
    exact fork_put s y.w y.L F y.F hF
  have ht' : s'.tl? = some tl := by
    rw [(commitAtS_tl P link moment arrays s s' _ gs h).1]
    exact ht
  have hbk := commitAtS_booked P link moment arrays s s' r₁ r₂ gs h
  refine ⟨fun a ha => ?_, ?_⟩
  · obtain ⟨_, c1, c2, _, c4⟩ := segAt_some ha
    obtain ⟨b, d1, d2, d3, d4⟩ := segAt_mk hL' hF' ht'
    have eL : a.L = L := Option.some.inj (c1.symm.trans hL)
    have eF : a.F = F := Option.some.inj (c2.symm.trans hF)
    refine ⟨b, d1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [d2, eL]; exact harr
    · rw [d2, eL]; exact hrows
    · rw [d2, eL, hfr]
    · rw [d2, eL, hfr]
    · rw [d2, eL, hfr]; exact fun l m o => whereIs_there _ _ _ l m o
    · rw [d2, eL, hfr]; exact fun l m o => whereIs_fresh _ _ _ l m o
    · rw [d4, c4]; exact fun o y hy => hbk.seat_kept hy
    · rw [d3, eF]; exact hsl
  · rw [hs]
    exact merge_put s _ _ _

/-! ## The quiet step behind the reads -/

/-- A yes of q leaves all that the four items' tests read themselves (and the count of roots and
the rows on the table: for Johnson/Desc/K1/Law/PubAtLaterDoor.lean [not in this library]). -/
def QuietP (q : Block S Cl) : Prop :=
  ∀ s s' rs gs, q.decide s rs gs = .ok s' →
    s'.st = s.st ∧ s'.book = s.book ∧ s'.out = s.out ∧ s'.link? = s.link? ∧ s'.fork? = s.fork? ∧
      mergeOf s' = mergeOf s ∧ s'.tl?.isSome = s.tl?.isSome ∧ s'.roots = s.roots ∧
      s'.rows = s.rows

theorem quietP_layers (P : K8.ReadsQuiet.PG) : QuietP (K8.ReadsQuiet.layers P) := by
  intro s s' rs gs h
  obtain ⟨a, own, tl', ha, _, _, rfl⟩ := K8.ReadsQuiet.layers_ok h
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, rfl, ?_⟩ <;>
    simp [S.link?, S.fork?, S.tl?, S.rows, mergeOf, ha]

theorem quietP_head (P : K8.ReadsQuiet.PH) : QuietP (K8.ReadsQuiet.head P) := by
  intro s s' rs gs h
  obtain ⟨a, cov, x, t, tl', ha, ho, _, _, _, _, rfl⟩ := K8.ReadsQuiet.head_ok h
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, rfl, ?_⟩ <;>
    simp [S.link?, S.fork?, S.tl?, S.rows, mergeOf, ha, ho]

theorem quietP_att {W : Verify.Public} {l g : Nat} {q : Block S Unit}
    (hq : First.Att.readsAtO W l g = some q) : QuietP q := by
  unfold First.Att.readsAtO at hq
  obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 hq
  intro s s' rs gs h
  obtain ⟨a, t, tl, ha, rfl⟩ := Meaning.K2.readsAtSO_eq h
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, rfl, ?_⟩ <;>
    simp [S.link?, S.fork?, S.tl?, S.rows, mergeOf, ha]

theorem quietP_blockAt {G : Array Layer.HPlan2} {hS : Head.Shape} {HLy : Head.HL}
    {H : Head.HPlanH2} {kinds : List (Nat × Nat)} {l : Nat} {q : Block S Unit}
    (h : K8.ReadsQuiet.blockAt G hS HLy H kinds l = some q) : QuietP q := by
  unfold K8.ReadsQuiet.blockAt at h
  obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · obtain ⟨hp, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact quietP_layers _
  · split at h
    · obtain rfl := Option.some.inj h
      exact quietP_head _
    · cases h

theorem quietP_readsQuietAt {G : ProofFile.Ground} (l : Nat) (X : LinkH) (piece : Nat) (q : Block S Unit)
    (h : ProofFile.readsQuietAt G l X piece = some q) : QuietP q := by
  unfold ProofFile.readsQuietAt at h
  by_cases h1 : (X.kind == 1) = true
  · rw [if_pos h1] at h
    by_cases h2 : (piece == 4) = true
    · rw [if_pos h2] at h
      exact quietP_att h
    · rw [if_neg h2] at h
      cases h
  · rw [if_neg h1] at h
    by_cases h2 : (piece == (if X.kind == 0 then 4 else 5)) = true
    · rw [if_pos h2] at h
      exact quietP_blockAt h
    · rw [if_neg h2] at h
      cases h

/-- **The quiet block as the lot joins it** (where none could be made the refuser never says
yes). -/
theorem quietP_orLoud (name : String) (p : Place) (what : String) (G : ProofFile.Ground) (l : Nat)
    (X : LinkH) (piece : Nat) :
    QuietP (ProofFile.orLoud name p what (ProofFile.readsQuietAt G l X piece)) := by
  cases hq : ProofFile.readsQuietAt G l X piece with
  | none => exact fun s s' rs gs h => nomatch h
  | some q => exact quietP_readsQuietAt l X _ q hq

/-- Riding, then such a yes, is riding. -/
theorem RecRides.quiet {new : List Nat} {s s₁ s' : S} (R : RecRides new s s₁)
    (e : s'.st = s₁.st ∧ s'.book = s₁.book ∧ s'.out = s₁.out ∧ s'.link? = s₁.link? ∧
      s'.fork? = s₁.fork? ∧ mergeOf s' = mergeOf s₁ ∧ s'.tl?.isSome = s₁.tl?.isSome) :
    RecRides new s s' := by
  obtain ⟨_, e2, _, e4, e5, e6, e7⟩ := e
  refine ⟨fun a ha => ?_, e6.trans R.merge⟩
  obtain ⟨b, hb, hR⟩ := R.seg a ha
  obtain ⟨tl, c1, c2, c3, c4⟩ := segAt_some hb
  rw [c3] at e7
  obtain ⟨tl', ht'⟩ := Option.isSome_iff_exists.1 e7
  obtain ⟨c, d1, d2, d3, d4⟩ := segAt_mk (e4.trans c1) (e5.trans c2) ht'
  exact ⟨c, d1, hR.congr d2 d3 (by rw [d4, c4, e2])⟩

/-- A yes of the joined block: a yes of the sending, then a yes of the quiet block. -/
theorem joined_yes (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (nm : String)
    (q : Block S Cl) (s s' : S) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (Block.andThen nm (commitAtS P link moment arrays) q).decide s [r₁, r₂] gs = .ok s') :
    ∃ s₁ gs₁ rs₂ gs₂, (commitAtS P link moment arrays : Block S Cl).decide s [r₁, r₂] gs₁ = .ok s₁ ∧
      q.decide s₁ rs₂ gs₂ = .ok s' := by
  have h' : ((commitAtS P link moment arrays : Block S Cl).decide s
      ([r₁, r₂].take (commitAtS P link moment arrays : Block S Cl).rounds.length)
      (gs.take (commitAtS P link moment arrays : Block S Cl).openings)).bind (fun s₁ =>
      q.decide s₁ ([r₁, r₂].drop (commitAtS P link moment arrays : Block S Cl).rounds.length)
        (gs.drop (commitAtS P link moment arrays : Block S Cl).openings)) = .ok s' := h
  obtain ⟨s₁, h1, h2⟩ := (bind_ok _ _ _).1 h'
  exact ⟨s₁, _, _, _, h1, h2⟩

/-- **A YES OF THE READS' PLACE's BLOCK.** -/
theorem joined_rides (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (nm : String)
    (q : Block S Cl) (hq : QuietP q) (s s' : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (Block.andThen nm (commitAtS P link moment arrays) q).decide s [r₁, r₂] gs = .ok s') :
    RecRides (idsOf P s.st.oracles.size).toList s s' := by
  obtain ⟨s₁, gs₁, rs₂, gs₂, h1, h2⟩ := joined_yes P link moment arrays nm q s s' r₁ r₂ gs h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, _⟩ := hq _ _ _ _ h2
  exact (commitAtS_rides P link moment arrays s s₁ r₁ r₂ gs₁ h1).quiet ⟨a1, a2, a3, a4, a5, a6, a7⟩

theorem joined_index (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (nm : String)
    (q : Block S Cl) (hq : QuietP q) (s s' : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (Block.andThen nm (commitAtS P link moment arrays) q).decide s [r₁, r₂] gs = .ok s') :
    IndexKept s s' := by
  obtain ⟨s₁, gs₁, rs₂, gs₂, h1, h2⟩ := joined_yes P link moment arrays nm q s s' r₁ r₂ gs h
  obtain ⟨e1, e2, e3, _⟩ := hq _ _ _ _ h2
  exact (K13.Law.commitAtS_index P link moment arrays s s₁ r₁ r₂ gs₁ h1).trans
    (indexKept_of e3 (by rw [e1]) fun i seat hs => by rw [e2]; exact hs)

/-- The book behind the joined block is the book behind the sending: what a sending does to it. -/
theorem joined_booked (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (nm : String)
    (q : Block S Cl) (hq : QuietP q) (s s' : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (Block.andThen nm (commitAtS P link moment arrays) q).decide s [r₁, r₂] gs = .ok s') :
    Booked P s.book s.st.oracles.size s'.book s'.st.oracles.size := by
  obtain ⟨s₁, gs₁, rs₂, gs₂, h1, h2⟩ := joined_yes P link moment arrays nm q s s' r₁ r₂ gs h
  obtain ⟨e1, e2, _⟩ := hq _ _ _ _ h2
  rw [e1, e2]
  exact commitAtS_booked P link moment arrays s s₁ r₁ r₂ gs₁ h1

/-- **The premise hseat, from the book**: where the book in front has a place for every message, and
the seats that the place's messages take behind the book's trees are seats of own. -/
theorem seats_new {P : Par} {bk bk' : TreeBook} {n n' : Nat} (hB : Booked P bk n bk' n')
    (hn : bk.place.size = n) (own : List (Nat × Nat))
    (hown : ∀ i, i < P.sent.size →
      own.contains (bk.trees.size + (layOf P).tree.getD i 0, (layOf P).part.getD i 0) = true) :
    ∀ o ∈ (idsOf P n).toList, (seatAt own bk' o).isSome = true := by
  intro o ho
  unfold idsOf at ho
  rw [Array.toList_map, Array.toList_range, List.mem_map] at ho
  obtain ⟨i, hi, rfl⟩ := ho
  have hi' := List.mem_range.1 hi
  unfold seatAt
  rw [Nat.add_comm i n, hB.newer hn hi', Option.bind_some, if_pos (hown i hi')]
  rfl

/-- The seats of the place's messages are seats of the segment's group, where they are the plan's
tenants of one of its three moments. -/
theorem seats_in_group (N : First.Numbers) (P : Par) (m t nT : Nat) (ht : t < 3)
    (hs : First.sameMembers ((List.range P.sent.size).map fun i =>
      (nT + (layOf P).tree.getD i 0, (layOf P).part.getD i 0)) (N.sent m t) = true) :
    ∀ i, i < P.sent.size →
      (N.group m).contains (nT + (layOf P).tree.getD i 0, (layOf P).part.getD i 0) = true := by
  intro i hi
  unfold First.sameMembers at hs
  rw [Bool.and_eq_true, List.all_eq_true] at hs
  have h1 := hs.1 _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)
  have hx : (nT + (layOf P).tree.getD i 0, (layOf P).part.getD i 0) ∈ N.sent m t := by
    simpa using h1
  have hg : (nT + (layOf P).tree.getD i 0, (layOf P).part.getD i 0) ∈ N.group m := by
    unfold First.Numbers.group
    rcases t with _ | _ | _ | t
    · exact List.mem_append_left _ (List.mem_append_left _ hx)
    · exact List.mem_append_left _ (List.mem_append_right _ hx)
    · exact List.mem_append_right _ hx
    · omega
  simpa using hg

/-! ## The four items at the composed Bool -/

section
variable (D : PubData) (base : Pub → Pp × S → Bool)

theorem pubAll_indexIs (a : Pp × S) :
    pubAll D base .indexIs a = K13.indexIsC D.N.indexNo a.2 := rfl

theorem pubAll_indexThere (a : Pp × S) : pubAll D base .indexThere a = K13.indexThereC a.2 := rfl

theorem pubAll_formsIn (m k : Nat) (r : String) (a : Pp × S) :
    pubAll D base (.formsIn m k r) a = (D.runs m k r).all fun p =>
      if D.ah p.1 p.2 then formsInA (D.Rd m) (D.N.sent m) (D.N.group m) p.1 p.2 a.2
      else formsIn (D.Rd m) (D.N.group m) p.1 p.2 a.2 := rfl

theorem pubAll_formsInT (m k : Nat) (r : String) (a : Pp × S) :
    pubAll D base (.formsInT m k r) a =
      (D.runs m k r).all fun p => formsInT (D.Rd m) (D.N.sent m 0) p.1 p.2 a.2 := rfl

/-- At each run that the item names, what the segment's reader gave in front it gives behind. -/
def ReadersStay (m k : Nat) (r : String) (s s' : S) : Prop :=
  ∀ p ∈ D.runs m k r, ∀ X, (D.Rd m).forms p.1 p.2 s = some X → (D.Rd m).forms p.1 p.2 s' = some X

/-- It follows from the equation hl of formsQA_back (Johnson/Desc/Sound/FormsAhead.lean). -/
theorem readersStay_of_eq (m k : Nat) (r : String) (s s' : S)
    (h : ∀ p ∈ D.runs m k r, (D.Rd m).forms p.1 p.2 s' = (D.Rd m).forms p.1 p.2 s) :
    ReadersStay D m k r s s' := fun p hp _ hX => (h p hp).trans hX

variable {D base}

theorem indexIs_kept {s s' : S} (K : IndexKept s s') (z z' : Pp)
    (h : pubAll D base .indexIs (z, s) = true) : pubAll D base .indexIs (z', s') = true :=
  K.1 D.N.indexNo h

theorem indexThere_kept {s s' : S} (K : IndexKept s s') (z z' : Pp)
    (h : pubAll D base .indexThere (z, s) = true) : pubAll D base .indexThere (z', s') = true :=
  K.2.1 h

theorem formsIn_kept {new : List Nat} {s s' : S} (R : RecRides new s s') (m k : Nat) (r : String)
    (hRd : ReadersStay D m k r s s')
    (hseat : ∀ o ∈ new, (seatAt (D.N.group m) s'.book o).isSome = true) (z z' : Pp)
    (h : pubAll D base (.formsIn m k r) (z, s) = true) :
    pubAll D base (.formsIn m k r) (z', s') = true := by
  rw [pubAll_formsIn, List.all_eq_true] at h ⊢
  intro p hp
  have h1 := h p hp
  by_cases ha : D.ah p.1 p.2 = true
  · rw [if_pos ha] at h1 ⊢
    exact formsInA_rides R _ _ _ _ (hRd p hp) _ hseat h1
  · rw [if_neg ha] at h1 ⊢
    exact formsIn_rides R _ _ _ _ (hRd p hp) h1

theorem formsInT_kept {new : List Nat} {s s' : S} (R : RecRides new s s') (m k : Nat) (r : String)
    (hRd : ReadersStay D m k r s s') (z z' : Pp)
    (h : pubAll D base (.formsInT m k r) (z, s) = true) :
    pubAll D base (.formsInT m k r) (z', s') = true := by
  rw [pubAll_formsInT, List.all_eq_true] at h ⊢
  exact fun p hp => formsInT_rides R _ _ _ _ (hRd p hp) (h p hp)

end

/-! ## The blocks, and the four items over a block's own yes -/

/-- **A block of a later moment's sending of the place P**: what a yes of it on two rounds does to
what the four items read. -/
def LaterSend (P : Par) (B : Block S Cl) : Prop :=
  ∀ s s' rs gs, rs.length = 2 → B.decide s rs gs = .ok s' →
    IndexKept s s' ∧ RecRides (idsOf P s.st.oracles.size).toList s s' ∧
      Booked P s.book s.st.oracles.size s'.book s'.st.oracles.size

/-- The sending alone. -/
theorem laterSend_commitAtS (P : Par) (link moment : Nat) (arrays : Option (List Nat)) :
    LaterSend P (commitAtS P link moment arrays : Block S Cl) := by
  intro s s' rs gs h2 h
  obtain ⟨r₁, r₂, rfl⟩ := List.length_eq_two.1 h2
  exact ⟨K13.Law.commitAtS_index P link moment arrays s s' r₁ r₂ gs h,
    commitAtS_rides P link moment arrays s s' r₁ r₂ gs h,
    commitAtS_booked P link moment arrays s s' r₁ r₂ gs h⟩

/-- **The first member**: a segment's later moment at the plan's numbers (a link's digits). -/
theorem laterSend_laterAt (q : Params.First) (gp : GPar) (link piece moment : Nat)
    (arrays : Option (List Nat)) :
    LaterSend (parLater q gp link piece moment)
      (laterAt q gp link piece moment arrays : Block S Cl) :=
  laterSend_commitAtS _ _ _ _

/-- The sending with a quiet block joined behind it. -/
theorem laterSend_joined (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (nm : String)
    (q : Block S Cl) (hq : QuietP q) :
    LaterSend P (Block.andThen nm (commitAtS P link moment arrays) q) := by
  intro s s' rs gs h2 h
  obtain ⟨r₁, r₂, rfl⟩ := List.length_eq_two.1 h2
  exact ⟨joined_index P link moment arrays nm q hq s s' r₁ r₂ gs h,
    joined_rides P link moment arrays nm q hq s s' r₁ r₂ gs h,
    joined_booked P link moment arrays nm q hq s s' r₁ r₂ gs h⟩

/-- **The second member**: the reads' place's joined block. -/
theorem laterSend_k1Reads (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : Nat) (X : LinkH) (pr : Nat)
    (reads : Option (List Nat)) :
    LaterSend (parLater G.first (gpOf Z) l pr 1) (IM.k1Reads Z G l X pr reads) :=
  laterSend_joined _ _ _ _ _ _ (quietP_orLoud _ _ _ G l X _)

section
variable {P : Par} {B : Block S Cl} (hB : LaterSend P B) (D : PubData)
  (base : Pub → Pp × S → Bool) (x x' : Pp × S) (rs : List Fmt.RoundView)
  (gs : List (List (Nat × List UInt64))) (h2 : rs.length = 2)
  (h : B.decide x.2 rs gs = .ok x'.2)
include hB h2 h

/-- **indexIs** over the block's own yes. -/
theorem pub_indexIs_later (h0 : pubAll D base .indexIs x = true) :
    pubAll D base .indexIs x' = true :=
  indexIs_kept (hB _ _ _ _ h2 h).1 x.1 x'.1 h0

/-- **indexThere** over the block's own yes. -/
theorem pub_indexThere_later (h0 : pubAll D base .indexThere x = true) :
    pubAll D base .indexThere x' = true :=
  indexThere_kept (hB _ _ _ _ h2 h).1 x.1 x'.1 h0

/-- **formsIn m k r** over the block's own yes. -/
theorem pub_formsIn_later (m k : Nat) (r : String) (hRd : ReadersStay D m k r x.2 x'.2)
    (hseat : ∀ o ∈ (idsOf P x.2.st.oracles.size).toList,
      (seatAt (D.N.group m) x'.2.book o).isSome = true)
    (h0 : pubAll D base (.formsIn m k r) x = true) : pubAll D base (.formsIn m k r) x' = true :=
  formsIn_kept (hB _ _ _ _ h2 h).2.1 m k r hRd hseat x.1 x'.1 h0

/-- **formsIn m k r**, hseat paid off the promise's clause on the book and a test on the plan: the
book in front has a place for every message and nT trees; the seats of the place's messages behind
nT trees are the plan's tenants of segment m at moment t (the row's owner's laterSeatsB, unfolded).
-/
theorem pub_formsIn_later_plan (m k : Nat) (r : String) (hRd : ReadersStay D m k r x.2 x'.2)
    (t nT : Nat) (ht : t < 3) (hb : x.2.book.place.size = x.2.st.oracles.size)
    (hT : x.2.book.trees.size = nT)
    (hs : First.sameMembers ((List.range P.sent.size).map fun i =>
      (nT + (layOf P).tree.getD i 0, (layOf P).part.getD i 0)) (D.N.sent m t) = true)
    (h0 : pubAll D base (.formsIn m k r) x = true) : pubAll D base (.formsIn m k r) x' = true :=
  pub_formsIn_later hB D base x x' rs gs h2 h m k r hRd
    (seats_new (hB _ _ _ _ h2 h).2.2 hb _ (by rw [hT]; exact seats_in_group D.N P m t nT ht hs)) h0

/-- **formsInT m k r** over the block's own yes. -/
theorem pub_formsInT_later (m k : Nat) (r : String) (hRd : ReadersStay D m k r x.2 x'.2)
    (h0 : pubAll D base (.formsInT m k r) x = true) : pubAll D base (.formsInT m k r) x' = true :=
  formsInT_kept (hB _ _ _ _ h2 h).2.1 m k r hRd x.1 x'.1 h0

end

end VerifiableInference.Desc.K1
