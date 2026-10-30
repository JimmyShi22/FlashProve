-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/FrameTiedStep.lean: the general step for a block without a round at the table of
joints: a piece whose extractor is the identity, which turns the record by a relation rel over which
the table's letters ride (LettersRide, FrameTied.lean), at a row that closes and opens no class of
rows and no pin: TiedAt. The promise one border on goes by the table's own rule
(Johnson/Desc/Sound/PromiseRidesQ.lean: onQ_step_held); the tie is built of its eight parts
(Johnson/Desc/Sound/ChainOfPromises.lean), so that whatever rides is asked only where a tie asks it:
at a statement that bears no mark. In: what is known in front: a letter.

  shape_front, book_front   two Bools of the promise in front, at a record without a mark
  mem_pubStep, mem_pubOfItems_step   where a row makes and opens nothing the open public items
                  behind are among those in front: for whoever pays LettersRide's field "pub"
  pub_of_kept     so that field, from "each public item that is open in front rides"
  StepAt          what the step takes, as one bundle
  StepAt.on, .own, .frames, .mark, .dec   the promise one border on, and the four parts of a tie
  tied_of_rides   the tie, at In := the promise in front
  tied_of_ridesR  the tie in the form with a condition Rch beside the promise
                  (Johnson/Desc/Sound/ChainOfPromisesR.lean), at whatever In the promise and Rch
                  give

Limits: FrameTied.lean's: a rule over letters. No soundness statement.

-/
import Johnson.Top.H0.Walk.FrameTied
import Johnson.Desc.Sound.PromiseRidesQ
import Johnson.Desc.Sound.ChainOfPromisesR
import Iop.Compose

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open OnBytes OnBytes.Model
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Doomed)
open VerifiableInference.Desc (Place KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers Pub openSets pubSets pubStep pubRowM
  stepOpen rowOf shapeAt bookAt onAt start BlockRow PubRow sampledIn pubHeld pubOfItems quietRow
  openSets_succ pubSets_succ sampledIn_step rowsHeld_of_groups membersHeld_of_groups)

theorem bools_front {A P W : Type} {Fr : Frame} {N : Numbers} {Mg : Meaning P W} {links : List ModelPart}
    {ps : List Place} {get : A → P × S} {k : Nat} {a : A × Fr.E.Str}
    (ha : onQ N Mg links ps get k a) (hu : (get a.1).2.failed = none) :
    shapeAt links ps[k]? (get a.1).2 = true ∧ bookAt N ps[k]? (get a.1).2 = true := by
  unfold onQ onAt at ha
  rcases ha.2 with h | h
  · exact absurd hu h
  · have h1 := h.1
    simp only [Bool.and_eq_true] at h1
    exact ⟨h1.1.1.1.1.1, h1.2⟩

theorem mem_pubStep {Q : List Pub} {r : PubRow} {x : Pub} (hm : r.makes = [])
    (h : x ∈ pubStep Q r) : x ∈ Q := by
  simp only [pubStep, hm, List.filter_nil, List.append_nil] at h
  exact (List.mem_filter.1 h).1

theorem mem_stepOpen {O : List Item} {r : BlockRow} {i : Item} (ho : r.outs = [])
    (h : i ∈ stepOpen O r) : i ∈ O := by
  simp only [stepOpen, ho, List.filter_nil, List.append_nil] at h
  exact (List.mem_filter.1 h).1

theorem mem_pubOfItems_step {O : List Item} {r : BlockRow} {x : Pub} (ho : r.outs = [])
    (h : x ∈ pubOfItems (stepOpen O r)) : x ∈ pubOfItems O := by
  unfold pubOfItems at h ⊢
  obtain ⟨i, hi, e⟩ := List.mem_flatMap.1 h
  exact List.mem_flatMap.2 ⟨i, mem_stepOpen ho hi, e⟩

/-- For whoever pays LettersRide's field "pub": where the block's two rows make and open nothing, an
item that is open behind is open in front, and the promise in front has its Bool. -/
theorem pub_of_kept {P W : Type} {N : Numbers} {Mg : Meaning P W} {links : List ModelPart}
    {ps : List Place} {k : Nat} {pk : Place} (hk : ps[k]? = some pk)
    (ho : (rowOf links pk).outs = []) (hm : DoorIdle Mg links pk) {a : P × S}
    {y : VerifiableInference.Desc.Strs} (hu : a.2.failed = none) (hF : FrontAt N Mg links ps k a y)
    {x : Pub}
    (hx : x ∈ (pubSets Mg.more links ps)[k + 1]?.getD [] ++
      pubOfItems ((openSets links ps (start links))[k + 1]?.getD [])) : Mg.pub x a = true := by
  rw [openSets_succ links ps (start links) k pk hk, pubSets_succ Mg.more links ps k pk hk] at hx
  have h := hF
  unfold FrontAt onAt at h
  rcases h.2 with h' | h'
  · exact absurd hu h'
  · have h1 := h'.1
    simp only [Bool.and_eq_true] at h1
    have h2 := h1.1.2
    unfold pubHeld at h2
    rw [List.all_eq_true] at h2
    refine h2 x ?_
    rcases List.mem_append.1 hx with h3 | h3
    · exact List.mem_append_left _ (mem_pubStep hm h3)
    · exact List.mem_append_right _ (mem_pubOfItems_step ho h3)

/-- What the general step takes: one bundle, so that the four parts and the tie can share it. -/
structure StepAt {A Cl P W : Type} {C : CK} {Fr : Frame} (N : Numbers) (Mg : Meaning P W)
    (links : List ModelPart) (ps : List Place) (get : A → P × S) (k : Nat) (pk : Place)
    (q : Piece C Fr A Cl W) (rel : S → S → Prop)
    (In : P × S → VerifiableInference.Desc.Strs → Prop) : Prop where
  hk : ps[k]? = some pk
  hq : quietRow (rowOf links pk) = true
  hrel : ∀ a τ b, q.ior.red.out a τ = some b →
    (get b.1).1 = (get a.1).1 ∧ rel (get a.1).2 (get b.1).2 ∧
      Stays q.base (strsOf Fr a.2) (strsOf Fr b.2)
  hE : LaysNothing q
  hfail : ∀ s t, rel s t → t.failed = s.failed
  hshape : ∀ s t, rel s t → shapeAt links ps[k]? s = true → shapeAt links ps[k + 1]? t = true
  hG : ∀ s t, rel s t → t.st.groups = s.st.groups
  hB : ∀ s t, rel s t → t.book.place = s.book.place
  hbook : ∀ s t, rel s t → bookAt N ps[k]? s = true → bookAt N ps[k + 1]? t = true
  hL : LettersRide N Mg rel q.base In
    ((openSets links ps (start links))[k + 1]?.getD []) ((pubSets Mg.more links ps)[k + 1]?.getD [])
    (openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) (k + 1))
  hins : ∀ p s t y y' w, rel s t → Stays q.base y y' → s.failed = none → In (p, s) y →
    (∀ i, outsQ links ps k i → i.holds N Mg (p, t) y' w) →
    ∀ i, insQ links ps k i → i.holds N Mg (p, s) y w

section
variable {A Cl P W : Type} {C : CK} {Fr : Frame} {N : Numbers} {Mg : Meaning P W}
  {links : List ModelPart} {ps : List Place} {get : A → P × S} {k : Nat} {pk : Place}
  {q : Piece C Fr A Cl W} {rel : S → S → Prop}
  {In : P × S → VerifiableInference.Desc.Strs → Prop}

theorem StepAt.pair (H : StepAt N Mg links ps get k pk q rel In) {a τ b}
    (hb : q.ior.red.out a τ = some b) : get b.1 = ((get a.1).1, (get b.1).2) :=
  Prod.ext (H.hrel a τ b hb).1 rfl

/-- The promise one border on. -/
theorem StepAt.on (H : StepAt N Mg links ps get k pk q rel In) {a τ b}
    (hb : q.ior.red.out a τ = some b) (ha : onQ N Mg links ps get k a)
    (hF : (get a.1).2.failed = none → In ((get a.1).1, (get a.1).2) (strsOf Fr a.2)) :
    onQ N Mg links ps get (k + 1) b := by
  have eO := openSets_succ links ps (start links) k pk H.hk
  have eQ := pubSets_succ Mg.more links ps k pk H.hk
  have eS := sampledIn_step N ((openSets links ps (start links))[k]?.getD []) (rowOf links pk) H.hq
  obtain ⟨_, hr, e2⟩ := H.hrel a τ b hb
  have eb := H.pair hb
  have hL := H.hL
  refine onQ_step_held N Mg links ps get k pk H.hk H.hq a b ha ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro h; rwa [H.hfail _ _ hr]
  · intro h; rw [eb]; exact hL.decodes _ _ _ _ _ hr e2 h
  · intro hu _; exact H.hshape _ _ hr (bools_front ha hu).1
  · intro _ _ h; rwa [rowsHeld_of_groups N _ _ _ (H.hG _ _ hr)]
  · intro _ _ h; rwa [membersHeld_of_groups N _ _ _ (H.hG _ _ hr) (H.hB _ _ hr)]
  · intro hu _ _; rw [eb]; exact hL.inOrder _ _ _ _ hr hu (hF hu)
  · intro hu _ _
    unfold pubHeld
    rw [List.all_eq_true]
    intro x hx
    rw [eb]
    exact hL.pub _ _ _ _ x hr hu (hF hu) (by rw [eO, eQ]; exact hx)
  · intro _ _ h; exact H.hbook _ _ hr h
  · intro hu _ _ x hx
    rw [eb]
    exact hL.pubP _ _ _ _ x hr hu (hF hu) (by rw [eQ]; exact hx)
  · intro hu _ x hx _
    rw [eb]
    exact hL.held _ _ _ _ x hr hu (hF hu) (by rw [eO, eS]; exact hx)
  · intro hu _ x hx _
    refine ⟨hL.shown _ _ _ _ _ x hr e2 hu (hF hu) (by rw [eO, eS]; exact hx), ?_⟩
    rw [eb]
    exact hL.noColl _ _ _ _ _ x hr e2 hu (hF hu) (by rw [eO, eS]; exact hx)

/-- An item that is open behind rides back. -/
theorem StepAt.back (H : StepAt N Mg links ps get k pk q rel In) {a τ b} (w : W) (i : Item)
    (hb : q.ior.red.out a τ = some b) (hu : (get a.1).2.failed = none)
    (hF : In ((get a.1).1, (get a.1).2) (strsOf Fr a.2))
    (hop : openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) (k + 1) i)
    (h : meansQ N Mg get i b w) : meansQ N Mg get i a (q.ext a τ w) := by
  obtain ⟨_, hr, e2⟩ := H.hrel a τ b hb
  rw [H.hE]
  unfold meansQ at h ⊢
  rw [H.pair hb] at h
  exact H.hL.items _ _ _ _ _ _ i hr e2 hu hF hop h

/-- (1) The row's own law at the table, where no mark is borne in front. -/
theorem StepAt.own (H : StepAt N Mg links ps get k pk q rel In) :
    q.Own (fun a => onQ N Mg links ps get k a ∧ (get a.1).2.failed = none ∧
        In ((get a.1).1, (get a.1).2) (strsOf Fr a.2))
      (onQ N Mg links ps get (k + 1)) (meansQ N Mg get) (insQ links ps k) (outsQ links ps k) := by
  intro a ⟨ha, hu, hF⟩
  refine Doomed.of_forall _ _ fun τ b hb => ⟨H.on hb ha fun _ => hF, fun w hw i hi' => ?_⟩
  obtain ⟨_, hr, e2⟩ := H.hrel a τ b hb
  rw [H.hE]
  unfold meansQ
  refine H.hins (get a.1).1 (get a.1).2 (get b.1).2 _ _ w hr e2 hu hF (fun j hj => ?_) i hi'
  have := hw j hj
  unfold meansQ at this
  rwa [H.pair hb] at this

/-- (2) What rides, where no mark is borne in front. -/
theorem StepAt.frames (H : StepAt N Mg links ps get k pk q rel In) :
    q.Frames (fun a => onQ N Mg links ps get k a ∧ (get a.1).2.failed = none ∧
        In ((get a.1).1, (get a.1).2) (strsOf Fr a.2))
      (onQ N Mg links ps get (k + 1)) (meansQ N Mg get)
      (openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k) (insQ links ps k) :=
  fun _ _ _ w i ha hb _ hop hn h => H.back w i hb ha.2.1 ha.2.2 (Or.inl ⟨hop, hn⟩) h

/-- (3) A mark stays. -/
theorem StepAt.mark (H : StepAt N Mg links ps get k pk q rel In) :
    ∀ a τ b, q.ior.red.out a τ = some b → (get a.1).2.failed ≠ none →
      (get b.1).2.failed ≠ none := by
  intro a τ b hb h
  rwa [H.hfail _ _ (H.hrel a τ b hb).2.1]

/-- (4) "Decodes" rides. -/
theorem StepAt.dec (H : StepAt N Mg links ps get k pk q rel In) :
    ∀ a τ b, q.ior.red.out a τ = some b → Mg.decodes (get a.1) (strsOf Fr a.2) →
      Mg.decodes (get b.1) (strsOf Fr b.2) := by
  intro a τ b hb h
  obtain ⟨_, hr, e2⟩ := H.hrel a τ b hb
  rw [H.pair hb]
  exact H.hL.decodes _ _ _ _ _ hr e2 h

/-- **A piece that turns the record by rel, over which the table's letters ride: tied.** -/
theorem tied_of_rides (H : StepAt N Mg links ps get k pk q rel (FrontAt N Mg links ps k)) :
    TiedAt N Mg links ps get k q :=
  ⟨_, _, _, _, H.own, fun _ ha hm => ⟨ha, Classical.not_not.1 hm, ha⟩,
    fun _ _ _ _ _ _ hb => hb, fun _ _ _ _ _ _ _ _ hO => hO, fun _ _ _ _ _ _ _ _ _ hR => hR,
    fun a τ b w i ha hm hb hon hall hi hin =>
      H.frames a τ b w i ⟨ha, Classical.not_not.1 hm, ha⟩ hb hon hi hin
        (hall i (Or.inl ⟨hi, hin⟩)),
    H.mark, H.dec⟩

/-- **The same in the form with a condition Rch beside the promise**
(Johnson/Desc/Sound/ChainOfPromisesR.lean): In: whatever the promise in front and Rch k give of a
statement that bears no mark: so a field's payer may spend a fact on every reached state. -/
theorem tied_of_ridesR {Rch : ℕ → A × Fr.E.Str → Prop}
    (H : StepAt N Mg links ps get k pk q rel In)
    (hI : ∀ a, onQ N Mg links ps get k a → Rch k a → (get a.1).2.failed = none →
      In ((get a.1).1, (get a.1).2) (strsOf Fr a.2)) :
    TiedAtR N Mg links ps get Rch k q :=
  ⟨_, _, _, _, H.own,
    fun a ha hr hm => ⟨ha, Classical.not_not.1 hm, hI a ha hr (Classical.not_not.1 hm)⟩,
    fun _ _ _ _ _ _ _ hb => hb, fun _ _ _ _ _ _ _ _ _ hO => hO,
    fun _ _ _ _ _ _ _ _ _ _ hR => hR,
    fun a τ b w i ha hr hm hb hon hall hi hin =>
      H.frames a τ b w i ⟨ha, Classical.not_not.1 hm, hI a ha hr (Classical.not_not.1 hm)⟩ hb hon
        hi hin (hall i (Or.inl ⟨hi, hin⟩)),
    H.mark, H.dec⟩

end

theorem book_across {N : Numbers} {ps : List Place} {k : Nat} {s t : S} (hn : NoneBetween N ps k)
    (h1 : t.book = s.book) (h2 : t.st.oracles.size = s.st.oracles.size)
    (h : bookAt N ps[k]? s = true) : bookAt N ps[k + 1]? t = true := by
  unfold bookAt at h ⊢
  rw [h1, h2, hn.1, hn.2]
  exact h

#print axioms tied_of_rides
#print axioms tied_of_ridesR
#print axioms StepAt.own
#print axioms StepAt.frames

end Johnson.Desc.First.Walk.Tied
