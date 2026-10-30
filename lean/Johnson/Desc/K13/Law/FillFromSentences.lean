-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/FillFromSentences.lean: WHAT KIND K13's BLOCK AND W's COMMITMENT ASK OF THE
TABLE's LETTERS (`FillM3`, `FillM4`: Johnson/Desc/K13/Law/AtTable.lean, AtTableW.lean), CLAUSE BY
CLAUSE: WHICH IS PAID BY WHICH SENTENCE OF THE ONE FILLING; AND THE LAYER JOINED TO THE TIES.
Definitions and statements with their proofs.
Why. The table's letters are filled in layers, kind by kind. Each clause that hangs on OUR items
is paid from an equation "the letter at this item IS this test", which is rfl at our layer. What
hangs on other files' letters stays a premise, by name. WHICH PUBLIC ITEMS RIDE PAST OUR TWO
BLOCKS IS NOT OURS TO SAY: each kind's files may lay an item that is open from the chain's start and
never dropped: so everything here stands at ANY list Q of riders, read by membership, with ONE
PREMISE A RIDER.
Main names:
  `Sentences P cs sh ly N rest Mg rw`: the equations on our own items and fields; rest: what other
    layers say of "in order": it is conjoined with our test. `Sentences.of_agree`: they hang on
    these values of the filling alone: so a layer above ours that leaves them keeps them.
    `sentences_at_layer`: **our two layers (`fillK13Plus` over `fillK13`, FillK13.lean) have
    them**, by the make and FillK13Laws.lean's equations, but for `pubP` at our three items, which
    it hands on.
  `Rider3 Cl P Mg q`: over a bare step of K13's block the item's Bool and its `pubP` go on.
  `Rider4 Cl P P' N Mg Q p q`: over a step of W's commitment, INSIDE THE PROMISE IN FRONT (every
    rider's Bool; the book where the plan says of the block's place), the item's Bool holds behind,
    and its `pubP` goes on.
  Payers: `rider3_blind` (any item whose letters do not turn when the record's statement, its count
    of rows owed and its stand are replaced: K13's block turns nothing else), `rider3_book`,
    `rider3_seats`; `rider4_book`, `rider4_seats`, `rider4_frontOk`.
  `Others3`, `Others4`: WHAT STAYS: the clauses on `held`, `shown`, `noColl`, `decodes`, `pin`,
    `pinW` (other files' letters), on the reader rw, and `det`. `Others3.mono`, `Others4.mono`:
    more riders make them easier.
  `fillM3_of`, `fillM4_of`: **`FillM3`, `FillM4` at any Q.**
  `fillM3_at_layer`, `fillM4_at_layer`: at our layer; the second under `D.codes = P'.codes`.
  `k13_tied_at_layer`: **the layer joined to the tie at K13's block**, by a term.

THE EQUATIONS AND TESTS ON THE PLAN THAT ARE SPENT FOR W's COMMITMENT: FIVE: the joined block's
own `planOk`; `D.codes = P'.codes`; the number at which "K12.bookInOrder" counts is the place's
first tree (in `rider4_book`); the plan's two lists go on with what the place lays (in
`rider4_seats`).

What is not claimed. `Others3` | `Others4` at any filling: `det` above all. That what other layers
say of "in order" rides over our two steps (a premise: hrest). A rider's premise for an item that
is not named here. That "in order" or "all rows on the table are true" is kept by any block but
these two: AT OUR LAYER `Item.pile`, WHICH IS OPEN FROM THE CHAIN's START, SAYS "all rows on the
table are true" AT THE READER rw: EVERY BLOCK IN FRONT OF K13's OWES ITS GOING BACK. Nothing on
soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.FillK13
import Johnson.Desc.K13.Law.FillK13Laws
import Johnson.Desc.K13.Law.IndexSeatAtTable
import Johnson.Desc.K13.Law.IndexKept
import Johnson.Desc.Tidy.Chains
import Johnson.Desc.Means.TestsBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice
open OnBytes.Flat OnBytes.Maker
open OnBytes.Means (Tidy tidy4B tidy4B_iff)
open VerifiableInference.Desc.First (S ModelPart Pub Meaning Numbers)
open VerifiableInference.Desc.Sound (BookStep bookStepB bookStep_iff Frame TiedAt)
open VerifiableInference.Desc.Ground (groundQuiet_tidy)

/-- The door's item "K12.bookInOrder". -/
def bookItem : Pub := First.moreItem K12.Door.nBook

/-! ## 1 The sentences -/

/-- **The sentences of the one filling on which our two blocks' own clauses hang.** -/
structure Sentences {Pp W : Type} (P : Where) (cs : Codes) (sh : Params.ReqShape)
    (ly : Params.ReqLayout) (N : Numbers) (rest : Pp × S → Bool) (Mg : Meaning Pp W) {nR : ℕ}
    (rw : Pp × S → W → Wit GE nR P.lin.kCol) : Prop where
  pile : ∀ x y w, Mg.pile x y w ↔ RowsTrue (rw x) x.2 w
  pileOne : ∀ x y w, Mg.pileOne x y w ↔ RowsTrue (rw x) x.2 w
  frontOk : ∀ x, Mg.pub .frontOk x = frontOkB P x.2
  evalLaid : ∀ x, Mg.pub .evalLaid x = evalLaidB P x.2
  wSits : ∀ x, Mg.pub wSitsItem x = (wSitsB cs P x.2 && wSeatB N.w x.2)
  indexIs : ∀ x, Mg.pub .indexIs x = K1.indexIsB N.indexNo x.2
  indexThere : ∀ x, Mg.pub .indexThere x = K1.indexThereB x.2
  /-- "in order" is what other layers say of it (rest) and our test -/
  inOrder : ∀ x, Mg.inOrder x = (rest x && inOrderK13 cs sh ly x.2)
  pubP : ∀ q, q = .frontOk ∨ q = .evalLaid ∨ q = wSitsItem → ∀ x, Mg.pubP q x

/-- They hang on these values of the filling alone. -/
theorem Sentences.of_agree {Pp W : Type} {P : Where} {cs : Codes} {sh : Params.ReqShape}
    {ly : Params.ReqLayout} {N : Numbers} {rest : Pp × S → Bool} {Mg Mg' : Meaning Pp W} {nR : ℕ}
    {rw : Pp × S → W → Wit GE nR P.lin.kCol} (h : Sentences P cs sh ly N rest Mg rw)
    (h1 : Mg'.pile = Mg.pile) (h2 : Mg'.pileOne = Mg.pileOne) (h3 : Mg'.inOrder = Mg.inOrder)
    (h4 : ∀ q, k13ItemC q = true → Mg'.pub q = Mg.pub q)
    (h5 : ∀ q, q = .frontOk ∨ q = .evalLaid ∨ q = wSitsItem → ∀ x, Mg.pubP q x → Mg'.pubP q x) :
    Sentences P cs sh ly N rest Mg' rw where
  pile := fun x y w => by rw [h1]; exact h.pile x y w
  pileOne := fun x y w => by rw [h2]; exact h.pileOne x y w
  frontOk := fun x => by rw [h4 _ rfl]; exact h.frontOk x
  evalLaid := fun x => by rw [h4 _ rfl]; exact h.evalLaid x
  wSits := fun x => by rw [h4 _ rfl]; exact h.wSits x
  indexIs := fun x => by rw [h4 _ rfl]; exact h.indexIs x
  indexThere := fun x => by rw [h4 _ rfl]; exact h.indexThere x
  inOrder := fun x => by rw [h3]; exact h.inOrder x
  pubP := fun q hq x => h5 q hq x (h.pubP q hq x)

/-- **OUR LAYER HAS THE SENTENCES**, over whatever lies beneath it (Mg₀), if there `pubP` says
nothing at our three items. -/
theorem sentences_at_layer {Pp W : Type} {nR : ℕ} (D : DataK13 Pp W nR) (Mg₀ : Meaning Pp W)
    (hP : ∀ q, q = .frontOk ∨ q = .evalLaid ∨ q = wSitsItem → ∀ x, Mg₀.pubP q x) :
    Sentences D.P D.codes D.shape D.layout D.N Mg₀.inOrder (fillK13Plus D (fillK13 D Mg₀)) D.rw
    where
  pile := fun _ _ _ => Iff.rfl
  pileOne := fun _ _ _ => Iff.rfl
  frontOk := fun x => frontOkC_eq D.P x.2
  evalLaid := fun x => evalLaidC_eq D.P x.2
  wSits := fun x => by
    show (wSitsC D.codes D.P x.2 && wSeatC D.N.w x.2) = _
    rw [wSitsC_eq, wSeatC_eq]
  indexIs := fun x => indexIsC_eq D.N.indexNo x.2
  indexThere := fun x => indexThereC_eq x.2
  inOrder := fun _ => rfl
  pubP := hP

/-! ## 2 "In order" over our two steps -/

/-- "In order" (Tidy's test and three values of the record that are the plan's) goes on wherever
"tidy" does, the statement's codes stay, and the walk's own state of the calls stays. -/
theorem inOrderK13_rides {cs : Codes} {sh : Params.ReqShape} {ly : Params.ReqLayout} {s s' : S}
    (ht : Tidy s.st → Tidy s'.st) (hc : s'.st.codes = s.st.codes) (hk : s'.check = s.check)
    (h : inOrderK13 cs sh ly s = true) : inOrderK13 cs sh ly s' = true := by
  unfold inOrderK13 at h ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨⟨⟨t, c1⟩, c2⟩, c3⟩ := h
  exact ⟨⟨⟨tidy4B_iff.2 (ht (tidy4B_iff.1 t)), by rw [hc]; exact c1⟩, by rw [hk]; exact c2⟩,
    by rw [hk]; exact c3⟩

/-- K13's block leaves the codes and the walk's own state of the calls. -/
theorem plan_same_M3 {Pp Cl : Type} {P : Where} {x x' : Pp × S} (h : StepM3 Cl P x x') :
    x'.2.st.codes = x.2.st.codes ∧ x'.2.check = x.2.check := by
  obtain ⟨rs, gs, hd⟩ := h.2
  refine ⟨(atM3_same hd).1, ?_⟩
  obtain ⟨_, _, _, _, e⟩ := atM3_rec hd
  rw [e]

/-- So does W's commitment. -/
theorem plan_same_M4 {Pp Cl : Type} {P : Where} {P' : K1.Par} {x x' : Pp × S}
    (h : StepM4 Cl P P' x x') : x'.2.st.codes = x.2.st.codes ∧ x'.2.check = x.2.check := by
  obtain ⟨r₁, r₂, gs, hd⟩ := h.decide
  obtain ⟨s₁, g₁, rs₂, g₂, h1, h2⟩ := atM4_mid hd
  have c1 := (K1.sendAtS_kept P' x.2 s₁ _ g₁ h1).1
  have c2 := (rowsB_same h2).1
  have k1 : s₁.check = x.2.check := by
    unfold K1.sendAtS at h1
    dsimp only at h1
    split at h1
    · split at h1
      · obtain ⟨y, hy, rfl⟩ := (K1.map_ok _ _ _).1 h1
        obtain ⟨z, _, rfl⟩ := (K1.map_ok _ _ _).1 hy
        rfl
      · cases h1
    · cases h1
  obtain ⟨m₀, l, o, owed, _, _, _, e⟩ := rowsB_at h2
  refine ⟨c2.trans c1, ?_⟩
  rw [e]
  exact k1

/-! ## 3 The riders -/

/-- **A rider at K13's block**: over a bare step its Bool and its `pubP` go on. -/
def Rider3 {Pp W : Type} (Cl : Type) (P : Where) (Mg : Meaning Pp W) (q : Pub) : Prop :=
  ∀ x x', StepM3 Cl P x x' →
    (Mg.pub q x = true → Mg.pub q x' = true) ∧ (Mg.pubP q x → Mg.pubP q x')

/-- **A rider at W's commitment**: inside the promise in front its Bool holds behind, and its `pubP`
goes on. -/
def Rider4 {Pp W : Type} (Cl : Type) (P : Where) (P' : K1.Par) (N : Numbers) (Mg : Meaning Pp W)
    (Q : List Pub) (p : Option Place) (q : Pub) : Prop :=
  ∀ x x', StepM4 Cl P P' x x' → (∀ q' ∈ Q, Mg.pub q' x = true) → First.bookAt N p x.2 = true →
    Mg.pub q x' = true ∧ (Mg.pubP q x → Mg.pubP q x')

/-- **The general payer at K13's block**: an item whose letters do not turn when the record's
statement, its count of rows owed and its stand are replaced. -/
theorem rider3_blind {Pp W Cl : Type} {P : Where} {Mg : Meaning Pp W} {q : Pub}
    (h : ∀ (z : Pp) (s : S) (st : Statement) (ro : Option ℕ) (he : First.Here),
      Mg.pub q (z, { s with st := st, rowsOwed := ro, here := he }) = Mg.pub q (z, s) ∧
        (Mg.pubP q (z, s) → Mg.pubP q (z, { s with st := st, rowsOwed := ro, here := he }))) :
    Rider3 Cl P Mg q := by
  intro x x' hst
  obtain ⟨rs, gs, hd⟩ := hst.2
  obtain ⟨_, st', o, _, e⟩ := atM3_rec hd
  have ex : x' = (x.1, { x.2 with st := st', rowsOwed := none, here := .mem o }) :=
    Prod.ext hst.1 e
  obtain ⟨a, b⟩ := h x.1 x.2 st' none (.mem o)
  rw [ex]
  exact ⟨fun h0 => by rw [a]; exact h0, b⟩

theorem rider3_book {Pp W Cl : Type} {P : Where} {Mg : Meaning Pp W} {ft : ℕ}
    (hB : ∀ x, Mg.pub bookItem x = bookStepB ft x.2.book x.2.roots)
    (hP : ∀ x, Mg.pubP bookItem x) : Rider3 Cl P Mg bookItem := fun x x' h =>
  ⟨fun h0 => by
    rw [hB] at h0 ⊢
    rw [(core_same_M3 h).1, (core_same_M3 h).2]
    exact h0, fun _ => hP x'⟩

theorem rider3_seats {Pp W Cl : Type} {P : Where} {Mg : Meaning Pp W} {L : K12.Coin.Laid}
    (hSe : ∀ x, Mg.pub seatsItem x = K12.Coin.seatsPrefixB L x.2.book)
    (hP : ∀ x, Mg.pubP seatsItem x) : Rider3 Cl P Mg seatsItem := fun x x' h =>
  ⟨fun h0 => by
    rw [hSe] at h0 ⊢
    exact seats_ride_M3 L h h0, fun _ => hP x'⟩

/-- "The book in order" through a sending of kind K1, out of `K1.SeatedBy`. -/
theorem bookStep_seated {P' : K1.Par} {bk bk' : TreeBook} {n r n' r' : ℕ}
    (h : K1.SeatedBy P' bk n r bk' n' r') (h0 : BookStep P'.gp.firstTree bk r) :
    BookStep P'.gp.firstTree bk' r' := by
  obtain ⟨e, ho⟩ := h0
  refine ⟨by rw [h.roots, h.seated.size, e], fun z T hT => ?_⟩
  by_cases hz : z < bk.trees.size
  · rw [h.seated.trees z hz] at hT
    exact ho z T hT
  · have hz' : z < bk'.trees.size := by
      by_contra hn
      rw [Array.getElem?_eq_none (by omega)] at hT
      cases hT
    rw [h.seated.size] at hz'
    obtain ⟨t, ht, _, hnum, _⟩ := h.seated.made (z - bk.trees.size) (by omega)
    rw [show bk.trees.size + (z - bk.trees.size) = z by omega, hT] at ht
    obtain rfl := Option.some.inj ht
    rw [hnum, e]
    omega

/-- "K12.bookInOrder" at W's commitment: where it counts from the place's first tree. -/
theorem rider4_book {Pp W Cl : Type} {P : Where} {P' : K1.Par} {N : Numbers} {Mg : Meaning Pp W}
    {Q : List Pub} {p : Option Place} (hm : bookItem ∈ Q)
    (hB : ∀ x, Mg.pub bookItem x = bookStepB P'.gp.firstTree x.2.book x.2.roots)
    (hP : ∀ x, Mg.pubP bookItem x) : Rider4 Cl P P' N Mg Q p bookItem := fun x x' h hQ _ => by
  obtain ⟨r₁, r₂, gs, hd⟩ := h.decide
  have h0 := hQ _ hm
  rw [hB] at h0
  refine ⟨?_, fun _ => hP x'⟩
  rw [hB]
  exact (bookStep_iff _ _ _).2 (bookStep_seated (atM4_seated hd) ((bookStep_iff _ _ _).1 h0))

/-- "K12.seatsCarried" at W's commitment: where the plan's lists go on with what the place lays. -/
theorem rider4_seats {Pp W Cl : Type} {P : Where} {P' : K1.Par} {N : Numbers} {Mg : Meaning Pp W}
    {Q : List Pub} {p : Option Place} {L : K12.Coin.Laid} (hm : seatsItem ∈ Q)
    (hSe : ∀ x, Mg.pub seatsItem x = K12.Coin.seatsPrefixB L x.2.book)
    (hP : ∀ x, Mg.pubP seatsItem x)
    (hp : (L.places.drop (N.msgsAt p)).take P'.sent.size =
      K12.Coin.placesOf (N.treesAt p) P'.sent.size (K1.layOf P'))
    (hs : (L.shapes.drop (N.treesAt p)).take (K1.layOf P').shapes.size =
      (K1.layOf P').shapes.toList) : Rider4 Cl P P' N Mg Q p seatsItem := fun x x' h hQ hbk => by
  have h0 := hQ _ hm
  rw [hSe] at h0
  refine ⟨?_, fun _ => hP x'⟩
  rw [hSe]
  exact seats_ride_M4 N p L h h0 hbk hp hs

/-- K13's own item at W's commitment. y₀: any strings of any frame (the kind's condition `FrontOk`
is typed with them, and reads none). -/
theorem rider4_frontOk {Pp W Cl : Type} {P : Where} {P' : K1.Par} {cs : Codes}
    {sh : Params.ReqShape} {ly : Params.ReqLayout} {N : Numbers} {rest : Pp × S → Bool}
    {Mg : Meaning Pp W} {nR : ℕ} {rw : Pp × S → W → Wit GE nR P.lin.kCol} {Q : List Pub}
    {p : Option Place} {F : Frame}
    (y₀ : F.E.Str) (hS : Sentences P cs sh ly N rest Mg rw) (hm : Pub.frontOk ∈ Q) :
    Rider4 Cl P P' N Mg Q p .frontOk := fun x x' h hQ _ => by
  obtain ⟨r₁, r₂, gs, hd⟩ := h.decide
  have h0 := hQ _ hm
  rw [hS.frontOk] at h0
  refine ⟨?_, fun _ => hS.pubP _ (Or.inl rfl) x'⟩
  rw [hS.frontOk]
  exact (frontOkB_iff P _ y₀).2 (atM4_laid hd y₀ y₀ ((frontOkB_iff P _ y₀).1 h0)).2

/-! ## 4 What stays -/

/-- **What stays at K13's block**: other files' letters; the reader; `det`. -/
structure Others3 {Pp W : Type} (Cl : Type) (P : Where) (N : Numbers) (Mg : Meaning Pp W) {nR : ℕ}
    (rw : Pp × S → W → Wit GE nR P.lin.kCol) (Q : List Pub) : Prop where
  reader : ∀ x x' w, StepM3 Cl P x x' → RowsTrue (rw x') x'.2 w → RowsTrue (rw x) x'.2 w
  held : ∀ x x', StepM3 Cl P x x' → Mg.held N.index.1 N.index.2 x = true →
    Mg.held N.index.1 N.index.2 x' = true
  shown : ∀ y y', OldKept N.index.1 y y' → Mg.shown N.index.1 N.index.2 y →
    Mg.shown N.index.1 N.index.2 y'
  noColl : ∀ x x' y y', StepM3 Cl P x x' → OldKept N.index.1 y y' →
    Mg.noColl N.index.1 N.index.2 x y → Mg.noColl N.index.1 N.index.2 x' y'
  decodes : ∀ x x' y y', StepM3 Cl P x x' → y'.cell = y.cell → Mg.decodes x y → Mg.decodes x' y'
  pinWBack : ∀ x x' y y' w, StepM3 Cl P x x' → y'.cell = y.cell → Mg.pinW x' y' w → Mg.pinW x y w
  pinIBack : ∀ x x' y y' w, StepM3 Cl P x x' → OldKept N.index.1 y y' →
    Mg.pin N.index.1 N.index.2 x' y' w → Mg.pin N.index.1 N.index.2 x y w
  det : ∀ x y p w w', (∀ q ∈ Q, Mg.pub q x = true) → Mg.pub .indexIs x = true →
    Mg.pub .indexThere x = true →
    First.bookAt N p x.2 = true → Mg.inOrder x = true → Mg.decodes x y →
    Mg.held N.index.1 N.index.2 x = true →
    Mg.shown N.index.1 N.index.2 y → Mg.noColl N.index.1 N.index.2 x y →
    Mg.pinW x y w → Mg.pinW x y w' → Mg.pin N.index.1 N.index.2 x y w →
    Mg.pin N.index.1 N.index.2 x y w' → AgreeAt x.2.out.indexMasks (rw x w) (rw x w')

/-- More riders make it easier. -/
theorem Others3.mono {Pp W Cl : Type} {P : Where} {N : Numbers} {Mg : Meaning Pp W} {nR : ℕ}
    {rw : Pp × S → W → Wit GE nR P.lin.kCol} {Q Q' : List Pub} (hQ : ∀ q ∈ Q, q ∈ Q')
    (h : Others3 Cl P N Mg rw Q) : Others3 Cl P N Mg rw Q' :=
  { h with det := fun x y p w w' a => h.det x y p w w' fun q hq => a q (hQ q hq) }

/-- **What stays at W's commitment**: other files' letters; the reader. -/
structure Others4 {Pp W : Type} (Cl : Type) (P : Where) (P' : K1.Par) (N : Numbers)
    (Mg : Meaning Pp W) {nR : ℕ} (rw : Pp × S → W → Wit GE nR P.lin.kCol) (Q : List Pub)
    (p : Option Place) : Prop where
  reader : ∀ x x' w, StepM4 Cl P P' x x' → (∀ q ∈ Q, Mg.pub q x = true) →
    Mg.pub .indexIs x = true → Mg.pub .indexThere x = true → First.bookAt N p x.2 = true →
    RowsTrue (rw x') x'.2 w → RowsTrue (rw x) x'.2 w
  held : ∀ x x', StepM4 Cl P P' x x' → Mg.held N.index.1 N.index.2 x = true →
    Mg.held N.index.1 N.index.2 x' = true
  shown : ∀ y y', OldKept N.index.1 y y' → Mg.shown N.index.1 N.index.2 y →
    Mg.shown N.index.1 N.index.2 y'
  noColl : ∀ x x' y y', StepM4 Cl P P' x x' → Mg.held N.index.1 N.index.2 x = true →
    First.bookAt N p x.2 = true → OldKept N.index.1 y y' →
    Mg.noColl N.index.1 N.index.2 x y → Mg.noColl N.index.1 N.index.2 x' y'
  decodes : ∀ x x' y y', StepM4 Cl P P' x x' → y'.cell = y.cell → Mg.decodes x y →
    Mg.decodes x' y'
  pinWBack : ∀ x x' y y' w, StepM4 Cl P P' x x' → y'.cell = y.cell → Mg.pinW x' y' w →
    Mg.pinW x y w
  pinIBack : ∀ x x' y y' w, StepM4 Cl P P' x x' → Mg.held N.index.1 N.index.2 x = true →
    First.bookAt N p x.2 = true → OldKept N.index.1 y y' →
    Mg.pin N.index.1 N.index.2 x' y' w → Mg.pin N.index.1 N.index.2 x y w

/-- More riders make it easier. -/
theorem Others4.mono {Pp W Cl : Type} {P : Where} {P' : K1.Par} {N : Numbers} {Mg : Meaning Pp W}
    {nR : ℕ} {rw : Pp × S → W → Wit GE nR P.lin.kCol} {Q Q' : List Pub} {p : Option Place}
    (hQ : ∀ q ∈ Q, q ∈ Q') (h : Others4 Cl P P' N Mg rw Q p) : Others4 Cl P P' N Mg rw Q' p :=
  { h with reader := fun x x' w s a => h.reader x x' w s fun q hq => a q (hQ q hq) }

/-! ## 5 `FillM3`, `FillM4` at any list of riders -/

/-- **`FillM3` from the sentences**, at any list of riders. -/
theorem fillM3_of {Pp W Cl : Type} {P : Where} {cs : Codes} {sh : Params.ReqShape}
    {ly : Params.ReqLayout} {N : Numbers} {rest : Pp × S → Bool} {Mg : Meaning Pp W} {nR : ℕ}
    {rw : Pp × S → W → Wit GE nR P.lin.kCol} (Q : List Pub)
    (hS : Sentences P cs sh ly N rest Mg rw) (hO : Others3 Cl P N Mg rw Q)
    (hrest : ∀ x x', StepM3 Cl P x x' → rest x = true → rest x' = true)
    (hR : ∀ q ∈ Q, Rider3 Cl P Mg q) : FillM3 Cl P N Mg rw Q where
  pile := fun x y w _ _ h => (hS.pile x y w).2 h
  pileOne := fun _ x' y w _ h => (hS.pileOne x' y w).1 h
  reader := hO.reader
  frontOk := fun x h => by rw [hS.frontOk]; exact h
  frontOkP := fun x _ => hS.pubP _ (Or.inl rfl) x
  indexIs := fun x x' h h0 => by
    obtain ⟨rs, gs, hd⟩ := h.2
    rw [hS.indexIs] at h0 ⊢
    exact (atM3_index hd).1 _ h0
  indexThere := fun x x' h h0 => by
    obtain ⟨rs, gs, hd⟩ := h.2
    rw [hS.indexThere] at h0 ⊢
    exact (atM3_index hd).2.1 h0
  pubRide := fun x x' q h hq h0 => (hR q hq x x' h).1 h0
  pubPRide := fun x x' q h hq h0 => (hR q hq x x' h).2 h0
  inOrder := fun x x' h h0 => by
    rw [hS.inOrder, Bool.and_eq_true] at h0 ⊢
    exact ⟨hrest x x' h h0.1, inOrderK13_rides (stepM3_keeps groundQuiet_tidy h) (plan_same_M3 h).1
      (plan_same_M3 h).2 h0.2⟩
  held := hO.held
  shown := hO.shown
  noColl := hO.noColl
  decodes := hO.decodes
  pinWBack := hO.pinWBack
  pinIBack := hO.pinIBack
  det := hO.det

/-- **`FillM4` from the sentences**, at any list of riders; under the joined block's own test on the
plan. -/
theorem fillM4_of {Pp W Cl : Type} {P : Where} {P' : K1.Par} {sh : Params.ReqShape}
    {ly : Params.ReqLayout} {N : Numbers} {rest : Pp × S → Bool} {Mg : Meaning Pp W} {nR : ℕ}
    {rw : Pp × S → W → Wit GE nR P.lin.kCol} (Q : List Pub) (p : Option Place)
    (hS : Sentences P P'.codes sh ly N rest Mg rw) (hO : Others4 Cl P P' N Mg rw Q p)
    (hrest : ∀ x x', StepM4 Cl P P' x x' → rest x = true → rest x' = true)
    (hplan : (atM4 (Cl := Cl) P (K1.sendAtS P')).planOk = true)
    (hR : ∀ q ∈ Q, Rider4 Cl P P' N Mg Q p q) : FillM4 Cl P P' N Mg Q p where
  frontOk := fun x => by rw [hS.frontOk]
  frontOkP := fun x _ => hS.pubP _ (Or.inl rfl) x
  evalLaid := fun x h => by rw [hS.evalLaid]; exact h
  evalLaidP := fun x _ => hS.pubP _ (Or.inr (Or.inl rfl)) x
  wSits := fun x => by rw [hS.wSits, Bool.and_eq_true]
  wSitsP := fun x _ _ => hS.pubP _ (Or.inr (Or.inr rfl)) x
  indexIs := fun x x' h h0 => by
    obtain ⟨r₁, r₂, gs, hd⟩ := h.decide
    rw [hS.indexIs] at h0 ⊢
    exact (atM4_index hd).1 _ h0
  indexThere := fun x x' h h0 => by
    obtain ⟨r₁, r₂, gs, hd⟩ := h.decide
    rw [hS.indexThere] at h0 ⊢
    exact (atM4_index hd).2.1 h0
  pubRide := fun x x' q h hQ hbk hq => (hR q hq x x' h hQ hbk).1
  pubPRide := fun x x' q h hQ hbk hq h0 => (hR q hq x x' h hQ hbk).2 h0
  pileOne := fun x x' y y' w h hQ hi ht hb hw =>
    pileOne_back N Mg _ rw hS.pileOne p hO.reader x x' y y' w h hQ hi ht hb hw
  inOrder := fun x x' h h0 => by
    obtain ⟨ft, rs, cols, n, hst⟩ := h.2
    rw [hS.inOrder, Bool.and_eq_true] at h0 ⊢
    exact ⟨hrest x x' h h0.1,
      inOrderK13_rides (First.oursFirst_steps (.commitW P P') hplan ft _ rs cols _ n hst)
        (plan_same_M4 h).1 (plan_same_M4 h).2 h0.2⟩
  held := hO.held
  shown := hO.shown
  noColl := hO.noColl
  decodes := hO.decodes
  pinWBack := hO.pinWBack
  pinIBack := hO.pinIBack

/-! ## 6 At our layer; and the layer joined to the tie -/

section
variable {Pp W Cl : Type} {nR : ℕ}

/-- `FillM3` at our layer. -/
theorem fillM3_at_layer (D : DataK13 Pp W nR) (Mg₀ : Meaning Pp W) (Q : List Pub)
    (hP : ∀ q, q = .frontOk ∨ q = .evalLaid ∨ q = wSitsItem → ∀ x, Mg₀.pubP q x)
    (hO : Others3 Cl D.P D.N (fillK13Plus D (fillK13 D Mg₀)) D.rw Q)
    (hrest : ∀ x x', StepM3 Cl D.P x x' → Mg₀.inOrder x = true → Mg₀.inOrder x' = true)
    (hR : ∀ q ∈ Q, Rider3 Cl D.P (fillK13Plus D (fillK13 D Mg₀)) q) :
    FillM3 Cl D.P D.N (fillK13Plus D (fillK13 D Mg₀)) D.rw Q :=
  fillM3_of Q (sentences_at_layer D Mg₀ hP) hO hrest hR

/-- `FillM4` at our layer, where the layer's codes are the place's. -/
theorem fillM4_at_layer (D : DataK13 Pp W nR) (Mg₀ : Meaning Pp W) (P' : K1.Par) (Q : List Pub)
    (p : Option Place) (hcodes : D.codes = P'.codes)
    (hP : ∀ q, q = .frontOk ∨ q = .evalLaid ∨ q = wSitsItem → ∀ x, Mg₀.pubP q x)
    (hO : Others4 Cl D.P P' D.N (fillK13Plus D (fillK13 D Mg₀)) D.rw Q p)
    (hrest : ∀ x x', StepM4 Cl D.P P' x x' → Mg₀.inOrder x = true → Mg₀.inOrder x' = true)
    (hplan : (atM4 (Cl := Cl) D.P (K1.sendAtS P')).planOk = true)
    (hR : ∀ q ∈ Q, Rider4 Cl D.P P' D.N (fillK13Plus D (fillK13 D Mg₀)) Q p q) :
    FillM4 Cl D.P P' D.N (fillK13Plus D (fillK13 D Mg₀)) Q p :=
  fillM4_of Q p (hcodes ▸ sentences_at_layer D Mg₀ hP) hO hrest hplan hR

/-- **THE LAYER JOINED TO THE TIE AT K13's BLOCK**: the five ties at the piece that holds c, at our
layer over whatever lies beneath: Q is what the table computes there. -/
theorem k13_tied_at_layer (F : Frame) (D : DataK13 Pp W nR) (Mg₀ : Meaning Pp W) (base : ℕ)
    (dZ d0 : RDT) (ds : List RDT) (hD : Declared D.P dZ d0 ds) (c : Block S Cl)
    (hc : c.UnderR (atM3 D.P)) (z : Pp) (links : List ModelPart) (ps : List Place) (k : ℕ)
    (hT : RowM3 D.N (fillK13Plus D (fillK13 D Mg₀)).more links ps k)
    (hP : ∀ q, q = .frontOk ∨ q = .evalLaid ∨ q = wSitsItem → ∀ x, Mg₀.pubP q x)
    (hO : Others3 Cl D.P D.N (fillK13Plus D (fillK13 D Mg₀)) D.rw
      ((First.pubSets (fillK13Plus D (fillK13 D Mg₀)).more links ps)[k]?.getD []))
    (hrest : ∀ x x', StepM3 Cl D.P x x' → Mg₀.inOrder x = true → Mg₀.inOrder x' = true)
    (hR : ∀ q ∈ (First.pubSets (fillK13Plus D (fillK13 D Mg₀)).more links ps)[k]?.getD [],
      Rider3 Cl D.P (fillK13Plus D (fillK13 D Mg₀)) q)
    (hbase : D.N.index.1 < base) :
    TiedAt D.N (fillK13Plus D (fillK13 D Mg₀)) links ps (fun s : S => (z, s)) k
      ((pieceM3 (Cl := Cl) (W := W) F D.P base dZ d0 ds).seat c) :=
  k13_tied_seat F D.P base dZ d0 ds hD c hc z D.N (fillK13Plus D (fillK13 D Mg₀)) links ps k D.rw hT
    (fillM3_at_layer D Mg₀ _ hP hO hrest hR) hbase

end

end VerifiableInference.Desc.K13.Law
