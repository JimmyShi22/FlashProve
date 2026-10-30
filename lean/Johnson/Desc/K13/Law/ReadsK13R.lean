-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/ReadsK13R.lean: THE SECOND FORM OF `OwedReadsK13` (OwedReadsK13.lean,
ReadsK13.lean): WHICH COMPONENTS OF THE WITNESS THE SENTENCE ON THE ROWS ON THE COMMITTED TABLE OF
WEIGHTS READS: WITH NO PREMISE THAT NAMES AN ITEM OF THE TABLE's DOOR AS OPEN. A statement as a
definition of a Prop, and its proof.

Why. The first form asks, at a border at which the index masks' pin is open, that four public items
of the door are open there ("K12.msgShapes", "K12.bookInOrder", "K12.seatsCarried",
"K13.pileMasks"). At the table's small door these four names are struck: there that premise is false
at every border, and the first form says nothing. ALL THAT THE PROOF SPENT OF THE FOUR ITEMS ARE
FOUR FACTS AT THE VERIFIER's STATE. Here they are premises at the state, inside a fence Rch ("the
state is reached"): whoever holds them of every reached state pays them by four projections.

Main names:
  `FactsR13 M L s`: the four facts, each in its layer's own text: `K12.Door.atFirstShapes M s`,
    `atFirstBook 0 s`, `atFirstSeats L s`, `pileMasksC s`.
  `rows_read_at`: **the core**: where the index masks' pin is open and the four facts hold: the
    rows' truth reads the witness at the cells, at the index masks' message and at its pad alone.
  `BorderK13R`: what is asked of the table at border k: the pin is open; or nothing is sent yet, at
    a place outside the members' stand. NO NAME OF THE DOOR.
  `OwedReadsK13R`, `readsK13R_ok`: the statement. Of the filling it asks FOUR PLAIN PREMISES (what
    "pile", "pileOne", "indexIs", "indexThere" say) and what "noneSent" says; of the plan two (hL,
    hbelow).
  `readsOkAtR_k13`: the same with the table's own list of components and its two side clauses: the
    clause of the fenced form of "the readers are as booked", at the two items.
  `borderK13RB`, `borderK13R_of`, `bordersK13RB`: the premise on the table as a test with code.
HAS THE TEST RUN? By `#eval`, over the table at its fifth hunk, at the empty door: `bordersK13RB` at
the small and at the full chain of links: true at both (79 and 359 borders at which one of the two
items is open). Three negative tests say false: `borderK13RB` at a border beyond the list; at no
links and no places; and THE FIRST FORM's `bordersK13B` at the empty door.
What is not claimed. That any state is reached; hFacts. K13_law,
the law of K13's sub-protocol itself, IS NOT PROVED BY THIS. Nothing on soundness.
Words. "The verifier's state": what the verifier carries from one sub-protocol to the next. "The
promise": what the table of joints says of every state at a border.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.ReadsK13

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice OnBytes.Maker
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers Comp)
open VerifiableInference.Desc.Sound (MsgT Frame onQ meansQ sameQ insQ outsQ openAfter)
open VerifiableInference.Desc.K12.Door (Laid atFirstShapes atFirstBook atFirstSeats toTree)

/-- **The four facts at the verifier's state.** -/
structure FactsR13 (M : List OracleShape) (L : Laid) (s : S) : Prop where
  shapes : atFirstShapes M s = true
  book : atFirstBook 0 s = true
  seats : atFirstSeats L s = true
  masks : pileMasksC s = true

section
variable {A Pp Cells Tok : Type} {nR kC : ℕ} {Fr : Frame}

/-- **The core.** -/
theorem rows_read_at (N : Numbers) (Mg : Meaning Pp (Desc.Wit Cells Tok MsgT)) (arr : ℕ → ℕ → ℕ)
    (mat : Cells → Fin nR → (Fin kC → Bool) → GE) (M : List OracleShape) (L : Laid)
    (hII : ∀ x, Mg.pub .indexIs x = indexIsC N.indexNo x.2)
    (hIT : ∀ x, Mg.pub .indexThere x = indexThereC x.2)
    (hL : L.places[N.indexNo]? = some N.index) (hbelow : PlanBelow L N) (links : List ModelPart)
    (ps : List Place) (get : A → Pp × S) (k : ℕ) (hpin : Item.pinI ∈ openAt links ps k)
    (a : A × Fr.E.Str) (ha : onQ N Mg links ps get k a) (hm : (get a.1).2.failed = none)
    (hFa : FactsR13 M L (get a.1).2) (w w' : Desc.Wit Cells Tok MsgT) (hc : w.cells = w'.cells)
    (hmsg : w.msg (arr N.index.1 N.index.2) = w'.msg (arr N.index.1 N.index.2))
    (hpad : w.pad N.index.1 N.index.2 = w'.pad N.index.1 N.index.2) :
    RowsTrue (rwBook arr mat (get a.1)) (get a.1).2 w ↔
      RowsTrue (rwBook arr mat (get a.1)) (get a.1).2 w' := by
  obtain ⟨hii, hit, hbk, _⟩ := promise_index N Mg links ps get k hpin a ha hm
  have hI : K1.indexIsB N.indexNo (get a.1).2 = true := by
    rw [← indexIsC_eq, ← hII]
    exact hii
  have hT : K1.indexThereB (get a.1).2 = true := by
    rw [← indexThereC_eq, ← hIT]
    exact hit
  have hbk' := hbk
  unfold First.bookAt at hbk'
  simp only [Bool.and_eq_true, beq_iff_eq] at hbk'
  have hseat : (get a.1).2.book.place[(get a.1).2.out.indexMasks]? = some N.index :=
    eq_of_beq (K1.indexSeat_of_carried ((K12.Coin.seatsPrefix_iff (toTree L) _).1 hFa.seats)
      hbk'.1.2 hT hI hL)
  have hthere : (get a.1).2.out.indexMasks < (get a.1).2.st.oracles.size := by
    have e : ((get a.1).2.st.oracles[(get a.1).2.out.indexMasks]?).isSome = true := hT
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 e
    exact (Array.getElem?_eq_some_iff.1 ho).1
  exact reads_rows arr mat N M L (get a.1).1 (get a.1).2 hFa.shapes hFa.book hFa.seats hbk'.1.2
    (below_of_plan hbelow (get a.1) ps[k]? hbk hFa.seats) hthere hseat hFa.masks w w' hc hmsg hpad

end

/-- **What is asked of the table at border k**: no name of the door. -/
def BorderK13R (M : First.More) (links : List ModelPart) (ps : List Place) (k : ℕ) : Prop :=
  Item.pinI ∈ openAt links ps k ∨
    (Pub.noneSent ∈ (First.pubSets M links ps)[k]?.getD [] ∧
      ∃ p, ps[k]? = some p ∧ First.standAt links p ≠ .mem)

/-- **OWED, THE SECOND FORM.** Inside the promise and the fence, without a mark: the sentence reads
the three components alone. -/
def OwedReadsK13R : Prop :=
  ∀ {A Pp Cells Tok : Type} {nR kC : ℕ} {Fr : Frame} (N : Numbers)
    (Mg : Meaning Pp (Desc.Wit Cells Tok MsgT)) (arr : ℕ → ℕ → ℕ)
    (mat : Cells → Fin nR → (Fin kC → Bool) → GE) (M : List OracleShape) (L : Laid)
    (links : List ModelPart) (ps : List Place) (get : A → Pp × S) (Rch : ℕ → A × Fr.E.Str → Prop)
    (k : ℕ),
    (∀ x y w, Mg.pile x y w ↔ RowsTrue (rwBook arr mat x) x.2 w) →
    (∀ x y w, Mg.pileOne x y w ↔ RowsTrue (rwBook arr mat x) x.2 w) →
    (∀ x, Mg.pub .indexIs x = indexIsC N.indexNo x.2) →
    (∀ x, Mg.pub .indexThere x = indexThereC x.2) →
    (∀ x, Mg.pub .noneSent x = noneSentC N x.2) →
    L.places[N.indexNo]? = some N.index → PlanBelow L N → BorderK13R Mg.more links ps k →
    (∀ a, Rch k a → (get a.1).2.failed = none → FactsR13 M L (get a.1).2) →
    ∀ (i : Item) (a : A × Fr.E.Str) (w w' : Desc.Wit Cells Tok MsgT), i = .pile ∨ i = .pileOne →
      onQ N Mg links ps get k a → Rch k a → (get a.1).2.failed = none →
      (∀ c ∈ readsK13 arr N i, sameQ c w w') → meansQ N Mg get i a w → meansQ N Mg get i a w'

theorem readsK13R_ok : OwedReadsK13R := by
  intro A Pp Cells Tok nR kC Fr N Mg arr mat M L links ps get Rch k hP hP1 hII hIT hNS hL hbelow hB
    hFacts i a w w' hi ha hr hm hsame hw
  have key : RowsTrue (rwBook arr mat (get a.1)) (get a.1).2 w →
      RowsTrue (rwBook arr mat (get a.1)) (get a.1).2 w' := by
    rcases hB with hpin | ⟨hns, p, hp, hst⟩
    · have h3 : w.msg (arr N.index.1 N.index.2) = w'.msg (arr N.index.1 N.index.2) ∧
          w.pad N.index.1 N.index.2 = w'.pad N.index.1 N.index.2 ∧ w.cells = w'.cells := by
        rcases hi with rfl | rfl <;>
          exact ⟨hsame (.msg _) (by simp [readsK13]), hsame (.pad _ _) (by simp [readsK13]),
            hsame .cells (by simp [readsK13])⟩
      exact (rows_read_at N Mg arr mat M L hII hIT hL hbelow links ps get k hpin a ha hm
        (hFacts a hr hm) w w' h3.2.2 h3.1 h3.2.1).1
    · exact fun _ => rowsTrue_nil _ (no_rows N Mg links ps get k hNS hns p hp hst a ha hm) w'
  rcases hi with rfl | rfl
  · exact (hP _ _ _).2 (key ((hP _ _ _).1 hw))
  · exact (hP1 _ _ _).2 (key ((hP1 _ _ _).1 hw))

/-- **The clause of the fenced form of "the readers are as booked", at the two items.** -/
theorem readsOkAtR_k13 {A Pp Cells Tok : Type} {nR kC : ℕ} {Fr : Frame} (N : Numbers)
    (Mg : Meaning Pp (Desc.Wit Cells Tok MsgT)) (arr : ℕ → ℕ → ℕ)
    (mat : Cells → Fin nR → (Fin kC → Bool) → GE) (M : List OracleShape) (L : Laid)
    (links : List ModelPart) (ps : List Place) (get : A → Pp × S) (Rch : ℕ → A × Fr.E.Str → Prop)
    (k : ℕ) (hP : ∀ x y w, Mg.pile x y w ↔ RowsTrue (rwBook arr mat x) x.2 w)
    (hP1 : ∀ x y w, Mg.pileOne x y w ↔ RowsTrue (rwBook arr mat x) x.2 w)
    (hII : ∀ x, Mg.pub .indexIs x = indexIsC N.indexNo x.2)
    (hIT : ∀ x, Mg.pub .indexThere x = indexThereC x.2)
    (hNS : ∀ x, Mg.pub .noneSent x = noneSentC N x.2) (hL : L.places[N.indexNo]? = some N.index)
    (hbelow : PlanBelow L N) (hB : BorderK13R Mg.more links ps k)
    (hFacts : ∀ a, Rch k a → (get a.1).2.failed = none → FactsR13 M L (get a.1).2)
    (i : Item) (hi : i = .pile ∨ i = .pileOne) (a : A × Fr.E.Str)
    (w w' : Desc.Wit Cells Tok MsgT) (ha : onQ N Mg links ps get k a) (hr : Rch k a)
    (hm : (get a.1).2.failed = none)
    (_ : openAfter (insQ links ps) (outsQ links ps) (· ∈ First.start links) k i)
    (_ : ¬ insQ links ps k i) (hc : ∀ c ∈ i.reads arr N links, sameQ c w w')
    (hw : meansQ N Mg get i a w) : meansQ N Mg get i a w' :=
  readsK13R_ok N Mg arr mat M L links ps get Rch k hP hP1 hII hIT hNS hL hbelow hB hFacts i a w w'
    hi ha hr hm (fun c h => hc c (readsK13_sub arr N links i c h)) hw

/-- **`BorderK13R` as a test with code.** -/
def borderK13RB (M : First.More) (links : List ModelPart) (ps : List Place) (k : ℕ) : Bool :=
  (openAt links ps k).contains .pinI ||
    (((First.pubSets M links ps)[k]?.getD []).contains .noneSent &&
      match ps[k]? with
      | some p => decide (First.standAt links p ≠ .mem)
      | none => false)

/-- Where the test says yes the premise holds. -/
theorem borderK13R_of {M : First.More} {links : List ModelPart} {ps : List Place} {k : ℕ}
    (h : borderK13RB M links ps k = true) : BorderK13R M links ps k := by
  unfold borderK13RB at h
  rcases Eq.mp (Bool.or_eq_true _ _) h with h | h
  · exact Or.inl (by simpa using h)
  · obtain ⟨h1, h2⟩ := Eq.mp (Bool.and_eq_true _ _) h
    refine Or.inr ⟨by simpa using h1, ?_⟩
    cases hp : ps[k]? with
    | none =>
      rw [hp] at h2
      cases h2
    | some p =>
      rw [hp] at h2
      exact ⟨p, rfl, of_decide_eq_true h2⟩

/-- The test at every border of a list at which one of the two items is open. -/
def bordersK13RB (M : First.More) (links : List ModelPart) (ps : List Place) : Bool :=
  (List.range (ps.length + 1)).all fun k =>
    !((openAt links ps k).contains .pile || (openAt links ps k).contains .pileOne) ||
      borderK13RB M links ps k

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.rows_read_at
#print axioms VerifiableInference.Desc.K13.Law.readsK13R_ok
#print axioms VerifiableInference.Desc.K13.Law.readsOkAtR_k13
#print axioms VerifiableInference.Desc.K13.Law.borderK13R_of
