-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/KeepAtLater.lean: THE WHOLE PROMISE OF THE TABLE OF JOINTS BEHIND A LATER MOMENT's SENDING OF KIND K1 (a link's reads, its digits), FROM THE PROMISE IN FRONT: the premise hkeep of
the sending's five ties (K1.send_tied, Johnson/Desc/K1/Law/AtTable.lean). Definitions and statements with their proofs.
  StepL P g x x'    what a yes of such a block does to FOUR CLAUSES' PART of the state (where the chain stands · the open rows' lists · the groups' members · where the book stands): the public part
                    stays; the group g gains the new messages; the book and the number of messages grow by the place's; the mark stays; the chain stands where it stood; no count of rows waits; an
                    open link behind was open in front, under the same number. IT KEEPS NOTHING ELSE: so no clause on a letter of the meaning is asked over it
  stepL_commitAtS   **a yes of commitAtS is such a step**, where the state's frame's group is g
  YesOf B x x'      THE BLOCK's OWN YES on rounds that fit its declared rounds, the public part one: what the clauses on the letters range over
  InAt … k x y      the promise in front, whole, and no mark
  KeptBelow base    what a piece with that base leaves of the strings: the cells; every column of every older tree · keptBelow_out
  RowL              WHAT IS ASKED OF THE TABLE at (links, ps, k): m, t: the segment and the moment; nT, nM: the trees and messages that the place sends; T: public items that may come: tied ones, and
                    those that the door's filling makes at the place
  FillL St …        WHAT IS ASKED OF THE TABLE's LETTERS: each clause of the promise that reads a letter holds BEHIND a step St FROM INSIDE THE PROMISE IN FRONT, at what is open in front AND behind
  shapeAt_stepL · bookAt_stepL
  keep_later        **the promise behind**: PROVED HERE: shapeAt · rowsHeld · membersHeld · bookAt. BROUGHT DOWN TO FillL: "decodes" · "in order" · the public items · held | shown | no collision at
                    the tenants that stay open. BROUGHT DOWN TO new | newPub | newPubP: held | shown | no collision at this place's tenants; the public items that come.
What is not claimed. NO MEMBER OF RowL (see Johnson/Desc/K1/Law/RowLFull.lean) OR FillL IS SHOWN HERE. That the state's frame's group is the plan's (g = N.groupAt m): said by no clause of the promise in front. Nothing
on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.HeldAtLater
import Johnson.Desc.K13.Law.AtTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Flat OnBytes.Maker
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More)
open VerifiableInference.Desc.Sound (Frame Piece strsOf onQ)
open Run
open VerifiableInference.Desc.K13.Law (openAt OldKept oldKept_out out_imp)

variable {Cl Pp W : Type}

/-- **A step of a later moment's sending.** -/
structure StepL (P : Par) (g : Nat) (x x' : Pp × S) : Prop where
  pub : x'.1 = x.1
  joins : Joins x.2.st x'.2.st g (idsOf P x.2.st.oracles.size).toList
  booked : Booked P x.2.book x.2.st.oracles.size x'.2.book x'.2.st.oracles.size
  mark : x'.2.failed = x.2.failed
  stand : First.standOf x'.2 = First.standOf x.2
  waits : x'.2.noneWaits = true
  link : ∀ L', x'.2.link? = some L' → ∃ L, x.2.link? = some L ∧ L'.link = L.link

/-- **A yes of commitAtS is such a step.** -/
theorem stepL_commitAtS (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (s s' : S)
    (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s [r₁, r₂] gs = .ok s') (g : Nat)
    (hg : ∀ L, s.link? = some L → L.check.frame.group = g) (z : Pp) :
    StepL P g (z, s) (z, s') := by
  obtain ⟨L, hL, hJ⟩ := commitAtS_group P link moment arrays s s' r₁ r₂ gs h
  rw [hg L hL] at hJ
  obtain ⟨⟨L₀, L₁, a1, a2, a3⟩, hw, hh⟩ := commitAtS_here P link moment arrays s s' _ gs h
  obtain ⟨_, _, F', w, _, _, e⟩ := commitAtS_rec P link moment arrays s s' _ gs h
  refine ⟨rfl, hJ, commitAtS_booked P link moment arrays s s' r₁ r₂ gs h, ?_, ?_, ?_, ?_⟩
  · show s'.failed = s.failed
    rw [e]
    cases hs : s.here with
    | head a => by_cases ho : a.opened = true <;> simp [S.putFork, S.putLink, laid, hs, ho]
    | _ => simp [S.putFork, S.putLink, laid, hs]
  · show First.standOf s' = First.standOf s
    rcases hh with ⟨a, a', e1, e2⟩ | ⟨a, a', e1, e2⟩ | ⟨a, a', e1, e2, o1, o2⟩
    · simp [First.standOf, e1, e2]
    · simp [First.standOf, e1, e2]
    · simp [First.standOf, S.inLink, S.fork?, e1, e2, o1, o2]
  · show s'.noneWaits = true
    simp [S.noneWaits, hw]
  · intro L' hL'
    show ∃ L, s.link? = some L ∧ L'.link = L.link
    obtain rfl : L₁ = L' := Option.some.inj (a2.symm.trans hL')
    exact ⟨L₀, a1, a3⟩

/-- **What is asked of the table.** -/
structure RowL (N : Numbers) (M : More) (links : List ModelPart) (ps : List Place) (k m t nT nM : ℕ)
    (T : List Pub) : Prop where
  /-- the next block stands in the same segment, at a border at which the chain stands alike -/
  next : ∃ p p', ps[k]? = some p ∧ ps[k + 1]? = some p' ∧
    First.standAt links p' = First.standAt links p ∧ p'.link = p.link
  seg : ∀ m' ∈ First.rowSegs (openAt links ps (k + 1)), m' ∈ First.rowSegs (openAt links ps k)
  due : ∀ m', First.rowsDue N (openAt links ps (k + 1)) m' = First.rowsDue N (openAt links ps k) m'
  inl : ∀ m' c, Item.row m' c ∈ openAt links ps (k + 1) → c.inList = true →
    Item.row m' c ∈ openAt links ps k
  /-- the plan's numbers of the groups of the segments with an open class of rows part from m's -/
  inj : ∀ m' ∈ First.rowSegs (openAt links ps (k + 1)), N.groupAt m' = N.groupAt m → m' = m
  other : ∀ m', m' ≠ m → pinsOf N (openAt links ps (k + 1)) m' = pinsOf N (openAt links ps k) m'
  here : ∀ x, x ∈ pinsOf N (openAt links ps (k + 1)) m ↔
    (x ∈ pinsOf N (openAt links ps k) m ∨ x ∈ N.sent m t)
  /-- behind, the pins with a sample are those in front and this moment's -/
  sampled : ∀ x ∈ First.sampledIn N (openAt links ps (k + 1)),
    x ∈ First.sampledIn N (openAt links ps k) ∨ x ∈ N.sent m t
  /-- a public item that is asked behind was asked in front, or is one of T -/
  pubs : ∀ q ∈ (First.pubSets M links ps)[k + 1]?.getD [] ++
      First.pubOfItems (openAt links ps (k + 1)),
    q ∈ (First.pubSets M links ps)[k]?.getD [] ++ First.pubOfItems (openAt links ps k) ∨ q ∈ T
  /-- a named item that is open behind was open in front, or is one of T (FOURTH FORM: the door's filling may MAKE items at the place) -/
  pubsP : ∀ q ∈ (First.pubSets M links ps)[k + 1]?.getD [],
    q ∈ (First.pubSets M links ps)[k]?.getD [] ∨ q ∈ T
  trees : N.treesAt ps[k + 1]? = N.treesAt ps[k]? + nT
  msgs : N.msgsAt ps[k + 1]? = N.msgsAt ps[k]? + nM

/-- The block's own yes ON ROUNDS THAT FIT ITS DECLARED ROUNDS (as a step of the block hands them to its decision); the public part is one. («tidy in front,
tidy behind» goes through a sending by Keeps.Fits alone, which asks the fit.) -/
def YesOf (B : Block S Cl) (x x' : Pp × S) : Prop :=
  x'.1 = x.1 ∧ ∃ rs gs, roundsFit B.rounds rs = true ∧ B.decide x.2 (rs.map noDigest) gs = .ok x'.2

/-- The promise in front of block k, whole, and no mark. -/
def InAt (N : Numbers) (Mg : Meaning Pp W) (links : List ModelPart) (ps : List Place) (k : ℕ)
    (x : Pp × S) (y : Strs) : Prop :=
  First.onAt N Mg links ps[k]? (openAt links ps k) ((First.pubSets Mg.more links ps)[k]?.getD []) x y ∧
    x.2.failed = none

/-- What a piece with the base `base` leaves of the strings: the cells, and every older tree's columns. -/
def KeptBelow (base : ℕ) (y y' : Strs) : Prop := y'.cell = y.cell ∧ ∀ j, j < base → OldKept j y y'

theorem keptBelow_out {T C' W' : Type} {C : PQ.CK} {F : Frame} (p : Piece C F T C' W')
    {a b : T × F.E.Str} {τ : Iop.Tr (uLT C p.ds)} (h : p.ior.red.out a τ = some b) :
    KeptBelow p.base (strsOf F a.2) (strsOf F b.2) := by
  refine ⟨?_, fun j hj => oldKept_out p h hj⟩
  rw [out_imp p h]
  rfl

/-- **What is asked of the table's letters.** St: the block's own step. In: the promise in front. O, Q | O', Q': what is open in front | behind. -/
structure FillL (St : Pp × S → Pp × S → Prop) (In : Pp × S → Strs → Prop) (N : Numbers)
    (Mg : Meaning Pp W) (O : List Item) (Q : List Pub) (O' : List Item) (Q' : List Pub) : Prop where
  /-- at every step, marked or not, inside the promise or not: the tie's own last clause asks so -/
  decodes : ∀ x x' y y', St x x' → y'.cell = y.cell → Mg.decodes x y → Mg.decodes x' y'
  inOrder : ∀ x x' y, St x x' → In x y → Mg.inOrder x' = true
  pub : ∀ x x' y q, St x x' → In x y → q ∈ Q ++ First.pubOfItems O →
    q ∈ Q' ++ First.pubOfItems O' → Mg.pub q x' = true
  pubP : ∀ x x' y q, St x x' → In x y → q ∈ Q → q ∈ Q' → Mg.pubP q x'
  held : ∀ x x' y u, St x x' → In x y → u ∈ First.sampledIn N O → u ∈ First.sampledIn N O' →
    Mg.held u.1 u.2 x' = true
  shown : ∀ y y' u, u ∈ First.sampledIn N O → u ∈ First.sampledIn N O' → OldKept u.1 y y' →
    Mg.shown u.1 u.2 y → Mg.shown u.1 u.2 y'
  noColl : ∀ x x' y y' u, St x x' → In x y → u ∈ First.sampledIn N O →
    u ∈ First.sampledIn N O' → OldKept u.1 y y' → Mg.noColl u.1 u.2 x' y'

theorem shapeAt_stepL {P : Par} {g : Nat} {x x' : Pp × S} (h : StepL P g x x') (links : List ModelPart)
    (p p' : Place) (hs : First.standAt links p' = First.standAt links p) (hl : p'.link = p.link)
    (h0 : First.shapeAt links (some p) x.2 = true) : First.shapeAt links (some p') x'.2 = true := by
  unfold First.shapeAt at h0 ⊢
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at h0 ⊢
  obtain ⟨⟨a, _⟩, c⟩ := h0
  refine ⟨⟨by rw [h.stand, hs]; exact a, Or.inl h.waits⟩, ?_⟩
  cases hL : x'.2.link? with
  | none => rfl
  | some L' =>
    obtain ⟨L, e1, e2⟩ := h.link L' hL
    rw [e1] at c
    simp only [Option.all_some, beq_iff_eq] at c ⊢
    rw [hl, e2]
    exact c

theorem bookAt_stepL {P : Par} {g : Nat} {x x' : Pp × S} (h : StepL P g x x') (N : Numbers)
    (p p' : Option Place) (ht : N.treesAt p' = N.treesAt p + (layOf P).shapes.size)
    (hm : N.msgsAt p' = N.msgsAt p + P.sent.size) (h0 : First.bookAt N p x.2 = true) :
    First.bookAt N p' x'.2 = true := by
  unfold First.bookAt at h0 ⊢
  simp only [Bool.and_eq_true, beq_iff_eq] at h0 ⊢
  obtain ⟨⟨b1, b2⟩, b3⟩ := h0
  exact ⟨⟨by rw [h.booked.trees, b1, ht], h.booked.full b2⟩, by rw [h.booked.msgs, b3, hm]⟩

/-- **THE PROMISE BEHIND A LATER MOMENT's SENDING.** a, b: the chain's states with their strings in front and behind. new: held, shown and no collision at the tenants that this
place sends. -/
theorem keep_later {A : Type} {Fr : Frame} (N : Numbers) (Mg : Meaning Pp W) (links : List ModelPart)
    (ps : List Place) (get : A → Pp × S) (k m t : ℕ) (P : Par) (St : Pp × S → Pp × S → Prop)
    (base : ℕ) (T : List Pub)
    (hT : RowL N Mg.more links ps k m t (layOf P).shapes.size P.sent.size T)
    (hF : FillL St (InAt N Mg links ps k) N Mg (openAt links ps k)
      ((First.pubSets Mg.more links ps)[k]?.getD []) (openAt links ps (k + 1))
      ((First.pubSets Mg.more links ps)[k + 1]?.getD []))
    (hP : laterSeatsB N P m t (N.treesAt ps[k]?) = true)
    (hbase : ∀ u ∈ First.sampledIn N (openAt links ps k), u.1 < base)
    (a b : A × Fr.E.Str) (ha : onQ N Mg links ps get k a) (hm : (get a.1).2.failed = none)
    (hSt : St (get a.1) (get b.1))
    (hst : StepL P (N.groupAt m) (get a.1) (get b.1))
    (hR : KeptBelow base (strsOf Fr a.2) (strsOf Fr b.2))
    (new : ∀ u ∈ N.sent m t, Mg.held u.1 u.2 (get b.1) = true ∧ Mg.shown u.1 u.2 (strsOf Fr b.2) ∧
      Mg.noColl u.1 u.2 (get b.1) (strsOf Fr b.2))
    (newPub : ∀ q ∈ T, Mg.pub q (get b.1) = true)
    (newPubP : ∀ q ∈ T, q ∈ (First.pubSets Mg.more links ps)[k + 1]?.getD [] →
      Mg.pubP q (get b.1)) :
    onQ N Mg links ps get (k + 1) b := by
  obtain ⟨p, p', hp, hp', hs, hl⟩ := hT.next
  have hIn : InAt N Mg links ps k (get a.1) (strsOf Fr a.2) := ⟨ha, hm⟩
  unfold onQ First.onAt at ha ⊢
  obtain ⟨hd, hrest⟩ := ha
  rcases hrest with hx | ⟨h1, h2, h3, h4⟩
  · exact absurd hm hx
  simp only [Bool.and_eq_true] at h1
  obtain ⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩ := h1
  have c6' := c6
  unfold First.bookAt at c6'
  simp only [Bool.and_eq_true, beq_iff_eq] at c6'
  obtain ⟨⟨b1, b2⟩, _⟩ := c6'
  have hrows : First.rowsHeld N (openAt links ps (k + 1)) (get b.1).2 = true :=
    rowsHeld_open N _ _ _ hT.seg hT.due hT.inl (rowsHeld_joins N _ _ _ hst.joins c2)
  have hmem : First.membersHeld N (openAt links ps (k + 1)) (get b.1).2 = true :=
    membersHeld_joins P _ _ N _ _ m t hst.joins hst.booked hT.seg hT.inj b2 hT.other hT.here
      (by rw [b1]; exact hP) c3
  refine ⟨hF.decodes _ _ _ _ hSt hR.1 hd, Or.inr ⟨?_, ?_, ?_, ?_⟩⟩
  · simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨?_, hrows⟩, hmem⟩, hF.inOrder _ _ _ hSt hIn⟩, ?_⟩, ?_⟩
    · rw [hp']
      rw [hp] at c1
      exact shapeAt_stepL hst links p p' hs hl c1
    · unfold First.pubHeld
      rw [List.all_eq_true]
      intro q hq
      rcases hT.pubs q hq with hq' | hq'
      · exact hF.pub _ _ _ q hSt hIn hq' hq
      · exact newPub q hq'
    · exact bookAt_stepL hst N _ _ hT.trees hT.msgs c6
  · unfold First.samplesHeld
    rw [List.all_eq_true]
    intro u hu
    rcases hT.sampled u hu with hu' | hu'
    · exact hF.held _ _ _ u hSt hIn hu' hu
    · exact (new u hu').1
  · intro u hu
    rcases hT.sampled u hu with hu' | hu'
    · exact ⟨hF.shown _ _ u hu' hu (hR.2 _ (hbase u hu')) (h3 u hu').1,
        hF.noColl _ _ _ _ u hSt hIn hu' hu (hR.2 _ (hbase u hu'))⟩
    · exact (new u hu').2
  · intro q hq
    rcases hT.pubsP q hq with hq' | hq'
    · exact hF.pubP _ _ _ q hSt hIn hq' hq
    · exact newPubP q hq' hq

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.keep_later
#print axioms VerifiableInference.Desc.K1.stepL_commitAtS
#print axioms VerifiableInference.Desc.K1.shapeAt_stepL
#print axioms VerifiableInference.Desc.K1.bookAt_stepL
