-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Rec/NextEntry.lean: THE PROOF of `NextEntryIs`
(Johnson/Road/K4/Rec/NextEntryStatement.lean): "at an unmarked statement inside the table of joints'
promise at a border, the number of the index masks' message, and the entry that its ledger hands out
next, are two numbers of the public parameters". GLUE: by unfolding the promise and the items'
tests, and calls: `shape_is` (Johnson/Desc/First/RecordPlan.lean), `takeEntry_no`
(Johnson/Desc/K13/Law/LedgerNo.lean). No draw, no count of a protocol. Over the statement:
the four items are taken out of `heldAt`, not out of `pubSets` alone.

  `three_at`, `pub_at`: three of the promise's tests, and an open public item's test, at an unmarked
    statement inside the promise (no open segment is asked).
  `pub_held`: the test of an item that the promise asks at the border (`heldAt`) accepts there.
  `open_of_next`: where `openNextB` accepts, each of the four items stands in `heldAt`.
  `left_of_room`: a yes of "pile.room"'s test: what is left in the ledger.
  **`nextEntryIs`**.

OBJECT: none of its own. USER: meant: the premise hname of Johnson/Road/K4/K4LinesWo.lean. LETTERS,
filled by nobody: as the statement's.

Limits. As the statement's file says: THE FIVE PREMISES ON THE MEANING ARE SHOWN AT NO TERM;
`EWithin` is an implication that hangs on a statement that is proved as `ledgersC`
(Johnson/Desc/K13/Law/LedgersC.lean); AT THE COMPOSED MEANING's OWN SMALL LIST OF EXTRA PUBLIC TESTS
`openNextB` REJECTS, SO `nextEntryIs` SAYS NOTHING THERE; at the wider meaning's list it accepts
(both by Lean's kernel: Johnson/Road/K4/Rec/OpenNextWide.lean). K04_law, the law of K4's
sub-protocol itself, IS NOT PROVED BY THIS. Nothing on soundness.
-/
import Johnson.Road.K4.Rec.NextEntryStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.Rec
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (S ModelPart Pub More Meaning Numbers start openSets pubSets pubHeld
  bookAt)
open VerifiableInference.Desc.First.Pend (takeEntry)
open VerifiableInference.Desc.First.RecordPlan (shape_is)
open VerifiableInference.Desc.K13.Law (LedgersFit LedgerAt takeEntry_no)
open VerifiableInference.Desc.Sound (Frame onQ)
open Johnson.Desc.First.Walk.Law (ledgerAt)
open Johnson.Desc.First.Walk.Tied (roomIsB leftIsB rowsBefore)

section
variable {P W : Type} {Fr : Frame} {N : Numbers} {Mg : Meaning P W} {Z : P} {links : List ModelPart}
  {ps : List Place} {j : ℕ} {b : S × Fr.E.Str}

/-- Three of the promise's six tests at an unmarked statement: "in order", the public items, the
book. -/
theorem three_at (hb : onQ N Mg links ps (fun s => (Z, s)) j b) (hu : b.1.failed = none) :
    Mg.inOrder (Z, b.1) = true ∧
      pubHeld Mg ((openSets links ps (start links))[j]?.getD [])
        ((pubSets Mg.more links ps)[j]?.getD []) (Z, b.1) = true ∧
      bookAt N ps[j]? b.1 = true := by
  obtain ⟨hB, _⟩ := hb.2.resolve_left fun x => x hu
  simp only [Bool.and_eq_true] at hB
  exact ⟨hB.1.1.2, hB.1.2, hB.2⟩

/-- An open public item's test says yes at the verifier's state. -/
theorem pub_at (hb : onQ N Mg links ps (fun s => (Z, s)) j b) (hu : b.1.failed = none) {q : Pub}
    (hq : OpenAt Mg links ps j q) : Mg.pub q (Z, b.1) = true :=
  List.all_eq_true.mp (three_at hb hu).2.1 q (List.mem_append_left _ hq)

/-- The test of an item that the promise asks at the border accepts at the verifier's state. -/
theorem pub_held (hb : onQ N Mg links ps (fun s => (Z, s)) j b) (hu : b.1.failed = none) {q : Pub}
    (hq : q ∈ heldAt Mg.more links ps j) : Mg.pub q (Z, b.1) = true :=
  List.all_eq_true.mp (three_at hb hu).2.1 q hq

end

/-- Where the test accepts, the promise asks each of the four at the border. -/
theorem open_of_next {P W : Type} {Mg : Meaning P W} {links : List ModelPart} {ps : List Place}
    {j m : ℕ} (h : openNextB Mg.more links ps j m = true) {q : Pub} (hq : q ∈ nextItems m) :
    q ∈ heldAt Mg.more links ps j := by
  have h1 := List.all_eq_true.mp h q hq
  simpa using h1

/-- A yes of "pile.room"'s test: what is left in the ledger. -/
theorem left_of_room {free0 : ℕ} {fvs : List Bool} {m : ℕ} {s : S} {l : Ledger}
    (h : roomIsB free0 fvs m s = true) (hl : ledgerAt s = some l) :
    l.left = free0 - rowsBefore fvs m := by
  unfold roomIsB leftIsB at h
  rw [hl] at h
  simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

theorem nextEntryIs : NextEntryIs := by
  intro P W Fr N Mg Z links ps j m M cs free0 fvs eI eS eC eW eR hO hF b hb hu
  have o1 : Pub.indexIs ∈ heldAt Mg.more links ps j := open_of_next hO (by simp [nextItems])
  have o2 : Pub.more none "K12.msgShapes" ∈ heldAt Mg.more links ps j :=
    open_of_next hO (by simp [nextItems])
  have o3 : Pub.more none "K13.pileWithin" ∈ heldAt Mg.more links ps j :=
    open_of_next hO (by simp [nextItems])
  have o4 : Pub.more (some m) "pile.room" ∈ heldAt Mg.more links ps j :=
    open_of_next hO (by simp [nextItems])
  have hi : b.1.out.indexMasks = N.indexNo := by
    have h1 := pub_held hb hu o1
    rw [eI (Z, b.1)] at h1
    exact beq_iff_eq.1 h1
  refine ⟨hi, fun l c l' hl ht => ?_⟩
  have hl0 := hl
  unfold ledgerAt at hl
  rw [hi] at hl
  obtain ⟨x, hx, hxl⟩ := Option.bind_eq_some_iff.1 hl
  have hsz : b.1.st.oracles.size = N.msgsAt ps[j]? := by
    have hk := (three_at hb hu).2.2
    simp only [bookAt, Bool.and_eq_true, beq_iff_eq] at hk
    exact hk.2
  have hsh : (M.take (N.msgsAt ps[j]?))[N.indexNo]? = some x.shape := by
    have h2 := pub_held hb hu o2
    rw [eS (Z, b.1)] at h2
    rw [← shape_is h2 hsz N.indexNo, hx]
    rfl
  have hc : b.1.st.codes = cs := eC (Z, b.1) (three_at hb hu).1
  unfold nextFitsB at hF
  rw [hsh] at hF
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hF
  obtain ⟨f1, f2⟩ := hF
  obtain ⟨k, hk⟩ := eW (Z, b.1) (pub_held hb hu o3) N.indexNo x hx (by rw [hxl]; rfl)
  have hleft : l.left = free0 - rowsBefore fvs m := by
    have h4 := pub_held hb hu o4
    rw [eR m (Z, b.1)] at h4
    exact left_of_room h4 hl0
  have hkk : k = rowsBefore fvs m := by
    obtain ⟨x₀, l₀, hx₀, hl₀, _, _, _, _, hs, _⟩ := hk
    obtain rfl : x₀ = x := Option.some.inj (hx₀.symm.trans hx)
    obtain rfl : l₀ = l := Option.some.inj (hl₀.symm.trans hxl)
    have hs' : l₀.left + k = free0 := by
      rw [f1, ← hc]
      exact hs
    omega
  rw [takeEntry_no hk hx hxl ht, hkk]
  unfold nextNoP
  rw [hsh]
  rfl

end OnBytes.Road.K4.Rec

#print axioms OnBytes.Road.K4.Rec.pub_held
#print axioms OnBytes.Road.K4.Rec.open_of_next
#print axioms OnBytes.Road.K4.Rec.nextEntryIs
