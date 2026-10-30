-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/K3X/KernelTests.lean: what the two lookups of a layers' link or of an attention link
ask of the public data (SixAt, Johnson/AtFull/K3X/SixAt.lean), as tests with code on the plans
alone; and that an accept of these tests gives the six statements. Definitions and general laws;
nothing is evaluated here.

Why. At the full size two of the things that the six statements read were reckoned too heavy to
evaluate in Lean's kernel: the layers' sixteen counts of padding keys (the layout's fo.pub) and the
host's own count at a layers' link (laidLayers): both walk over more than a hundred thousand columns
a call, with writes into an array, which in the kernel is a list. Neither was tried on its own; an
earlier try at one test that holds all six at one link ended at a cap on memory. The two are paid by
laws (Johnson/AtFull/K3X/CountsLaw.lean and LaidLayers.lean) and enter here as premises. All else
that the six read is small: the tests below gather it, and do not touch these two.

  `sameCall_eq`, `sameList_eq`: an accept of the light file's comparison of calls without tables,
    and of lists of them, gives the equation. The same two laws stand, on that file's own names of
    the same texts, in Johnson/AtFull/Desc/Lots/K3RowXB.lean, whose imports are heavy; they are
    proved here a second time so that this file stays over the light one.
  `nameOf i kind d`: the name that lookAt gives a lookup's place; `namesT`: at the 24 links in
    front of the head's it is the written name.
  `digitsT s ns tl`: the lookup on the digits, of a smallness test's structure tl, at a link of sort
    s with ns slots: its two calls, its counts, its depth limit, its first slot, the host's count,
    the test on the padding key.
  `layersT L G`: the layers' eight calls with their tables taken out, two numbers of the shape; for
    each of twelve groups the plan's first free slot, its number of slots, and digitsT.
  `attT A`: for each of twelve groups the attention plan's calls with their tables taken out, its
    counts, four numbers, the host's count, and digitsT. The test on the padding key of the lookup
    on the calls reads a row of a table of 65,536 rows: it is left out and enters as a premise; a
    law pays it (Johnson/AtFull/K3X/PadKeyLaw.lean).
  `view_of_fields`: a place's view is the written one if its eight parts are.
  **`six_even`**, **`six_odd`**: at a public part with profile 4 and twelve groups: an accept of
    namesT and layersT (with the two premises) gives SixAt at the links 0, 2, .., 22; an accept of
    namesT and attT (with the premise on the padding key) gives it at 1, 3, .., 23.

Limits. That a test accepts at any public data is not said here. The two premises on the layers'
counts are premises. Nothing on soundness, completeness or hiding.

-/
import Johnson.AtFull.K3X.SixAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.K3X

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.K3 (quietAt isHead)
open VerifiableInference.Desc.First.Look (lookAt laidAt tlAt padKeyAt laidDigits padKeyDigits
  padKeyAtt laidLayers digitsNext)
open Johnson.AtFull.ProofRows.K3 (strip)
open Johnson.AtFull.Lots.K3 (pubW sortOf quietW callerW nameW callsW firstW nsW lmW layCalls)
open Johnson.AtFull.Lots.K3.Light (viewOf viewW sameCall sameList ne24)

/-! ## 1 The comparison with code -/

theorem sameCall_eq {a b : Call} (h : sameCall a b = true) : a = b := by
  cases a
  cases b
  simp only [sameCall, Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, e5⟩, e6⟩, e7⟩, e8⟩, e9⟩, e10⟩, e11⟩ := h
  subst e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
  rfl

theorem sameList_eq : ∀ {l m : List Call}, sameList l m = true → l = m
  | [], [], _ => rfl
  | a :: l, b :: m, h => by
    simp only [sameList, Bool.and_eq_true] at h
    rw [sameCall_eq h.1, sameList_eq h.2]
  | [], _ :: _, h => by simp [sameList] at h
  | _ :: _, [], h => by simp [sameList] at h

/-! ## 2 The tests -/

/-- The name that lookAt gives a lookup's place. -/
def nameOf (i : Nat) (kind : String) (d : Bool) : String :=
  if d then s!"LINK {i} ({kind}) digits" else s!"LINK {i} ({kind}) calls"

/-- The names at the 24 links in front of the head's are the written ones. -/
def namesT : Bool :=
  (List.range 24).all fun i => [false, true].all fun d =>
    nameOf i (if i % 2 == 0 then "layers" else "attention") d == nameW i d

/-- The lookup on the digits. -/
def digitsT (s ns : Nat) (tl : HTailF2) : Bool :=
  sameList [tl.z1.call, tl.z2.call] (callsW s true).toList && tl.f9.pub == pubW s true &&
    tl.lidb == 28 && digitsNext ns 0 (Forest.elems tl.f9) == some (firstW s true) &&
    laidDigits tl == some (pubW s true) && padKeyDigits tl

/-- The layers' links. It reads neither L.y.fo.pub nor the calls' lists of columns. -/
def layersT (L : Layer.Pub) (G : Array Layer.HPlan2) : Bool :=
  sameList (L.y.cl.map strip).toList layCalls.toList && L.y.h.lidb == 28 && L.y.h.lmb == 16 &&
    (List.range 12).all fun g => (G[g]?).any fun hp =>
      hp.Fp.next == 0 && hp.ns == nsW (sortOf (2 * g)) && digitsT (sortOf (2 * g)) hp.ns hp.tl

/-- One attention plan, but for the test on the padding key. -/
def attOneT (a : Attention.Plan) : Bool :=
  sameList ((a.S.calls.map (·.call)).map strip).toList (callsW 1 false).toList &&
    a.fs.pub == pubW 1 false && a.lid == 28 && a.S.cf.lmb == 14 && a.seam.Fp.next == 0 &&
    a.ns == nsW 1 && (Attention.laidPadding a.S a.fs).toOption == some (pubW 1 false) &&
    digitsT 1 a.ns a.seam.tl

/-- The attention links, but for the test on the padding key. -/
def attT (A : Array Attention.Plan) : Bool :=
  (List.range 12).all fun g => (A[g]?).any attOneT

/-! ## 3 What an accept says -/

theorem names_at (h : namesT = true) {i : Nat} (hi : i < 24) (d : Bool) :
    nameOf i (if i % 2 == 0 then "layers" else "attention") d = nameW i d :=
  beq_iff_eq.1 (List.all_eq_true.1 (List.all_eq_true.1 h i (List.mem_range.2 hi)) d
    (by cases d <;> simp))

structure Digits (s ns : Nat) (tl : HTailF2) : Prop where
  calls : #[tl.z1.call, tl.z2.call] = callsW s true
  pub : tl.f9.pub = pubW s true
  lid : tl.lidb = 28
  next : digitsNext ns 0 (Forest.elems tl.f9) = some (firstW s true)
  laid : laidDigits tl = some (pubW s true)
  key : padKeyDigits tl = true

theorem digits_of {s ns : Nat} {tl : HTailF2} (h : digitsT s ns tl = true) : Digits s ns tl := by
  simp only [digitsT, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩ := h
  exact ⟨Array.toList_inj.1 (sameList_eq a), b, c, d, e, f⟩

/-- A place's view is the written one if its eight parts are. -/
theorem view_of_fields {x : First.Look.Place} {i : Nat} {d : Bool} (s : Bool)
    (h1 : x.name = nameW i d) (h2 : x.link = i)
    (h3 : (if s then x.calls.map strip else x.calls) = callsW (sortOf i) d)
    (h4 : x.pub = pubW (sortOf i) d) (h5 : x.lid = 28) (h6 : x.F.next = firstW (sortOf i) d)
    (h7 : x.ns = nsW (sortOf i)) (h8 : x.lm = lmW (sortOf i) d) : viewOf s x = viewW i d := by
  unfold Lots.K3.Light.viewOf Lots.K3.Light.viewW
  rw [h1, h2, h3, h4, h5, h6, h7, h8]

/-! ## 4 A layers' link -/

section
variable {X : Verify.Public} {i : Nat}

/-- The sort of an even link in front of the head's. -/
theorem sort_even (hi : i < 24) (h2 : i % 2 = 0) : sortOf i = 0 ∨ sortOf i = 2 := by
  unfold sortOf
  rw [ne24 hi]
  have : (i % 2 == 1) = false := by rw [h2]; rfl
  simp only [this, Bool.false_eq_true, if_false]
  by_cases h0 : (i == 0) = true
  · left; rw [if_pos h0]
  · right; rw [if_neg h0]

theorem sort_odd (hi : i < 24) (h2 : i % 2 = 1) : sortOf i = 1 := by
  unfold sortOf
  rw [ne24 hi]
  have : (i % 2 == 1) = true := by rw [h2]; rfl
  simp only [this, Bool.false_eq_true, if_false, if_true]

/-- **The six at one layers' link.** -/
theorem six_even_at (h4 : X.p4 = true) (hN : X.NGr = 12) (hi : i < 24) (h2 : i % 2 = 0)
    {hp : Layer.HPlan2} (e : X.G[i / 2]? = some hp) (hn : namesT = true)
    (c1 : X.layers.y.cl.map strip = layCalls) (l1 : X.layers.y.h.lidb = 28)
    (m1 : X.layers.y.h.lmb = 16) (f1 : hp.Fp.next = 0) (s1 : hp.ns = nsW (sortOf i))
    (D : Digits (sortOf i) hp.ns hp.tl)
    (hpub : X.layers.y.fo.pub = pubW 0 false) (hlaid : laidLayers X.layers = some (pubW 0 false)) :
    SixAt X i := by
  have b2 : (i % 2 == 0) = true := by rw [h2]; rfl
  have nm := fun d => names_at hn hi d
  simp only [b2, if_true] at nm
  have hs := sort_even hi h2
  have w1 : callsW (sortOf i) false = layCalls := by rcases hs with h | h <;> rw [h] <;> rfl
  have w2 : pubW (sortOf i) false = pubW 0 false := by
    rcases hs with h | h
    · rw [h]
    · rw [h]
      rfl
  have w3 : firstW (sortOf i) false = 0 := by rcases hs with h | h <;> rw [h] <;> rfl
  have w4 : lmW (sortOf i) false = 16 := by rcases hs with h | h <;> rw [h] <;> rfl
  have w5 : ∀ d, quietW i d = true := fun d => by
    unfold quietW
    rcases hs with h | h <;> rw [h] <;> cases d <;> rfl
  have w6 : callerW i = false := by
    unfold callerW
    rcases hs with h | h <;> rw [h] <;> rfl
  have t1 : tlAt X i = some hp.tl := by
    simp only [tlAt, h4, hN, ↓reduceIte, Nat.reduceMul, ne24 hi, Bool.false_eq_true, b2, e,
      Option.map_some]
  refine ⟨?_, ?_, fun d => ?_, fun d => ?_, fun d => ?_, ?_⟩
  · refine ⟨{ name := nameOf i "layers" false, link := i, calls := X.y.cl, pub := X.y.fo.pub
              lid := X.y.h.lidb, base := hp.Fp.fillL, F := hp.Fp.fillL.slots hp.ns, fs := X.y.fo
              ns := hp.ns, lm := X.y.h.lmb }, ?_, ?_⟩
    · simp only [lookAt, h4, hN, ↓reduceIte, Nat.reduceMul, ne24 hi, Bool.false_eq_true, b2, e,
        Option.bind_some]
      rfl
    · exact view_of_fields true (nm false) rfl (c1.trans w1.symm) (hpub.trans w2.symm) l1
        (f1.trans w3.symm) s1 (m1.trans w4.symm)
  · refine ⟨{ name := nameOf i "layers" true, link := i
              calls := #[hp.tl.z1.call, hp.tl.z2.call]
              pub := hp.tl.f9.pub, lid := hp.tl.lidb, base := hp.Fp.fillL
              F := { hp.Fp.fillL.slots hp.ns with next := firstW (sortOf i) true }
              fs := hp.tl.f9, ns := hp.ns, lm := 5 }, ?_, ?_⟩
    · simp only [lookAt, h4, hN, ↓reduceIte, Nat.reduceMul, ne24 hi, Bool.false_eq_true, b2, e,
        Option.bind_some, D.next, Option.map_some]
      rfl
    · exact view_of_fields false (nm true) rfl D.calls D.pub D.lid rfl s1 rfl
  · cases d
    · simp only [laidAt, h4, hN, ↓reduceIte, Nat.reduceMul, ne24 hi, Bool.false_eq_true, b2, e,
        Option.bind_some, hlaid, w2]
    · simp only [laidAt, t1, ↓reduceIte, Option.bind_some, D.laid]
  · cases d
    · simp only [padKeyAt, h4, hN, ↓reduceIte, Nat.reduceMul, ne24 hi, Bool.false_eq_true, b2, e,
        Option.map_some]
    · simp only [padKeyAt, t1, ↓reduceIte, Option.map_some, D.key]
  · rw [w5]
    cases d <;>
      simp only [quietAt, isHead, h4, hN, ↓reduceIte, Nat.reduceMul, ne24 hi, Bool.false_eq_true,
        b2, e, Option.map_some, Option.isSome_some]
  · rw [w6]
    simp only [K3Lot.readersAt, isHead, h4, hN, ↓reduceIte, Nat.reduceMul, ne24 hi,
      Bool.false_eq_true, b2, Option.isSome_none]

/-- **The six at one attention link.** -/
theorem six_odd_at (h4 : X.p4 = true) (hN : X.NGr = 12) (hi : i < 24) (h2 : i % 2 = 1)
    {a : Attention.Plan} (e : X.A[i / 2]? = some a) (hn : namesT = true)
    (ht : attOneT a = true) (hk : padKeyAtt a.S = true) : SixAt X i := by
  have b2 : (i % 2 == 0) = false := by rw [h2]; rfl
  have nm := fun d => names_at hn hi d
  simp only [b2, Bool.false_eq_true, if_false] at nm
  have hs := sort_odd hi h2
  simp only [attOneT, Bool.and_eq_true, beq_iff_eq] at ht
  obtain ⟨⟨⟨⟨⟨⟨⟨c0, p1⟩, l1⟩, m1⟩, f1⟩, s1⟩, q1⟩, d0⟩ := ht
  have c1 : (a.S.calls.map (·.call)).map strip = callsW 1 false :=
    Array.toList_inj.1 (sameList_eq c0)
  have D := digits_of d0
  have w5 : ∀ d, quietW i d = d := fun d => by
    unfold quietW
    rw [hs]
    cases d <;> rfl
  have w6 : callerW i = true := by
    unfold callerW
    rw [hs]
    rfl
  have t1 : tlAt X i = some a.seam.tl := by
    simp only [tlAt, h4, hN, ↓reduceIte, Nat.reduceMul, ne24 hi, Bool.false_eq_true, b2, e,
      Option.map_some]
  refine ⟨?_, ?_, fun d => ?_, fun d => ?_, fun d => ?_, ?_⟩
  · refine ⟨{ name := nameOf i "attention" false, link := i, calls := a.S.calls.map (·.call)
              pub := a.fs.pub, lid := a.lid, base := a.seam.Fp.fillL
              F := a.seam.Fp.fillL.slots a.ns, fs := a.fs, ns := a.ns, lm := a.S.cf.lmb }, ?_, ?_⟩
    · simp only [lookAt, h4, hN, ↓reduceIte, Nat.reduceMul, ne24 hi, Bool.false_eq_true, b2, e,
        Option.bind_some]
      rfl
    · rw [← hs] at c1 p1 s1
      exact view_of_fields true (nm false) rfl c1 p1 l1 (by rw [hs]; exact f1) s1
        (by rw [hs]; exact m1)
  · refine ⟨{ name := nameOf i "attention" true, link := i
              calls := #[a.seam.tl.z1.call, a.seam.tl.z2.call], pub := a.seam.tl.f9.pub
              lid := a.seam.tl.lidb, base := a.seam.Fp.fillL
              F := { a.seam.Fp.fillL.slots a.ns with next := firstW 1 true }
              fs := a.seam.tl.f9, ns := a.ns, lm := 5 }, ?_, ?_⟩
    · simp only [lookAt, h4, hN, ↓reduceIte, Nat.reduceMul, ne24 hi, Bool.false_eq_true, b2, e,
        Option.bind_some, D.next, Option.map_some]
      rfl
    · exact view_of_fields false (nm true) rfl (by rw [hs]; exact D.calls)
        (by rw [hs]; exact D.pub) D.lid (by rw [hs]) (by rw [hs]; exact s1) rfl
  · rw [hs]
    cases d
    · simp only [laidAt, h4, hN, ↓reduceIte, Nat.reduceMul, ne24 hi, Bool.false_eq_true, b2, e,
        Option.bind_some, q1]
    · simp only [laidAt, t1, ↓reduceIte, Option.bind_some, D.laid]
  · cases d
    · simp only [padKeyAt, h4, hN, ↓reduceIte, Nat.reduceMul, ne24 hi, Bool.false_eq_true, b2, e,
        Option.map_some, hk]
    · simp only [padKeyAt, t1, ↓reduceIte, Option.map_some, D.key]
  · rw [w5]
    cases d <;>
      simp only [quietAt, isHead, h4, hN, ↓reduceIte, Nat.reduceMul, ne24 hi, Bool.false_eq_true,
        b2, e, Option.map_some, Option.isSome_some, Option.isSome_none]
  · rw [w6]
    simp only [K3Lot.readersAt, isHead, h4, hN, ↓reduceIte, Nat.reduceMul, ne24 hi,
      Bool.false_eq_true, b2, e, Option.map_some, Option.isSome_some]

end

/-! ## 5 All twelve -/

variable {X : Verify.Public}

/-- **THE LAYERS' TWELVE LINKS.** -/
theorem six_even (h4 : X.p4 = true) (hN : X.NGr = 12) (hn : namesT = true)
    (ht : layersT X.layers X.G = true) (hpub : X.layers.y.fo.pub = pubW 0 false)
    (hlaid : laidLayers X.layers = some (pubW 0 false)) : ∀ g, g < 12 → SixAt X (2 * g) := by
  intro g hg
  simp only [layersT, Bool.and_eq_true, beq_iff_eq] at ht
  obtain ⟨⟨⟨c0, l1⟩, m1⟩, hall⟩ := ht
  have hg' := List.all_eq_true.1 hall g (List.mem_range.2 hg)
  have e2 : 2 * g / 2 = g := by omega
  cases e : X.G[g]? with
  | none =>
    rw [e] at hg'
    cases hg'
  | some hp =>
    rw [e] at hg'
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at hg'
    obtain ⟨⟨f1, s1⟩, d0⟩ := hg'
    exact six_even_at h4 hN (by omega) (by omega) (by rw [e2]; exact e) hn
      (Array.toList_inj.1 (sameList_eq c0)) l1 m1 f1 s1 (digits_of d0) hpub hlaid

/-- **THE ATTENTION's TWELVE LINKS.** -/
theorem six_odd (h4 : X.p4 = true) (hN : X.NGr = 12) (hn : namesT = true)
    (ht : attT X.A = true)
    (hk : ∀ (g : Nat) (a : Attention.Plan), X.A[g]? = some a → padKeyAtt a.S = true) :
    ∀ g, g < 12 → SixAt X (2 * g + 1) := by
  intro g hg
  have hg' := List.all_eq_true.1 ht g (List.mem_range.2 hg)
  have e2 : (2 * g + 1) / 2 = g := by omega
  cases e : X.A[g]? with
  | none =>
    rw [e] at hg'
    cases hg'
  | some a =>
    rw [e] at hg'
    exact six_odd_at h4 hN (by omega) (by omega) (by rw [e2]; exact e) hn hg' (hk g a e)

end Johnson.AtFull.K3X

#print axioms Johnson.AtFull.K3X.sameCall_eq
#print axioms Johnson.AtFull.K3X.sameList_eq
#print axioms Johnson.AtFull.K3X.names_at
#print axioms Johnson.AtFull.K3X.digits_of
#print axioms Johnson.AtFull.K3X.view_of_fields
#print axioms Johnson.AtFull.K3X.six_even_at
#print axioms Johnson.AtFull.K3X.six_odd_at
#print axioms Johnson.AtFull.K3X.six_even
#print axioms Johnson.AtFull.K3X.six_odd
