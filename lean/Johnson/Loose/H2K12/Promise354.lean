-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.First.FoldFacts
import Johnson.Desc.Sound.BordersQ
import Johnson.Desc.Sound.MeaningSig
import Johnson.Desc.Sound.BookOrder
import Johnson.Desc.K12.SeatLaws
import Johnson.Desc.K1.Law.SeedIs
import Johnson.Desc.K12.Door.DoorGives
import Johnson.Desc.K12.Coin.WordAtMember
/-
Johnson/Loose/H2K12/Promise354.lean:
The proximity test (the kind K12) on the proof file's first chain (sub-protocol
number 354 of the table of joints): WHAT THE TEST's LAW SPENDS OF THE VERIFIER's STATE IN FRONT OF
IT, SORTED BY WHO SAYS IT: the table's own promise at the border · "reached" · the list of rounds.
Definitions, statements and proofs; no chance, no game, no witness. General in the border's number
k, the number n of the group's segment and the group's members. AT THE FULL SIZE the open pins'
tenants at that border hold ONE seat by an evaluation not shown here; nothing here reads that.
  `ListedAt ms places o x`: x is a member of the list ms, and the list of places gives the oracle
    message number o the seat of x. No state is read.
  `memOf ms places`, `listed_of_memOf`, `memOf_listed`:
    the laying of the messages' numbers onto members as a term: it lays x at o just where x is listed at o.
  `FactsK12 d N n cs ms s`: THE FACTS FROM "REACHED": a Lean structure, a field a fact; each field's
    docstring names the field of `FoldFacts` (Johnson/Desc/First/FoldFacts.lean) that gives it, or
    says that none does.
  `MemberTold`, `PublicK12`: THE FACTS ON THE LIST OF ROUNDS AND THE LIST OF MEMBERS: no state is read.
  `on_parts`: of the promise at an unmarked state: the test `membersHeld`, and "every leaf is shown"
    at every tenant whose pin is open.
  `members_placed`: so each member of the group has a place in the book, at a tenant of an open pin.
  `place_listed`, `tree_listed`, `bookOrd_of`: "the seats are carried", "the book is in order", as the
    laws take them (the first and the third: calls of Johnson/Desc/K12/Door/DoorGives.lean).
  `factsK12_of_fold`: `FactsK12` from `FoldFacts` and the two facts that it lacks.
  `member_listed`: each member of the group under test is listed at a member of ms, whose every leaf
    is shown.
What it is not. `FactsK12` and `PublicK12` are premises wherever they stand; no field is shown here;
TWO FIELDS OF `FactsK12` HAVE NO PAYER. No example. No soundness is claimed. Nothing on hiding.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12
open OnBytes OnBytes.Slice OnBytes.Maker Johnson.Pack
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Coin (ShapeIs MemberPub)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers onAt openSets start pubSets membersHeld
  sampledIn rowSegs sameMembers)

/-- x is a member of ms, and the list of places gives the message number o the seat of x. -/
def ListedAt (ms : List Mem) (places : List (ℕ × ℕ)) (o : ℕ) (x : Mem) : Prop :=
  x ∈ ms ∧ places[o]? = some (seatOf x)

/-- **The laying of messages' numbers onto members, as a term**: the member of ms that sits where the
list of places puts the message number o. No state is read. -/
def memOf (ms : List Mem) (places : List (ℕ × ℕ)) (o : ℕ) : Option Mem :=
  (places[o]?).bind fun q => ms.find? fun x => decide (seatOf x = q)

/-- What it lays is listed there. -/
theorem listed_of_memOf {ms : List Mem} {places : List (ℕ × ℕ)} {o : ℕ} {x : Mem}
    (h : memOf ms places o = some x) : ListedAt ms places o x := by
  obtain ⟨q, hq, hf⟩ := Option.bind_eq_some_iff.1 h
  have h1 : seatOf x = q :=
    of_decide_eq_true (List.find?_some (p := fun y => decide (seatOf y = q)) hf)
  exact ⟨List.mem_of_find?_eq_some hf, by rw [h1]; exact hq⟩

/-- Where no two members have one seat, it lays whatever is listed. -/
theorem memOf_listed {ms : List Mem} {places : List (ℕ × ℕ)} (hn : (ms.map seatOf).Nodup) {o : ℕ}
    {x : Mem} (h : ListedAt ms places o x) : memOf ms places o = some x := by
  unfold memOf
  rw [h.2]
  show (ms.find? fun y => decide (seatOf y = seatOf x)) = some x
  cases hf : ms.find? fun y => decide (seatOf y = seatOf x) with
  | none => exact absurd (decide_eq_true rfl) (List.find?_eq_none.1 hf x h.1)
  | some y =>
    have h1 : seatOf y = seatOf x :=
      of_decide_eq_true (List.find?_some (p := fun y => decide (seatOf y = seatOf x)) hf)
    rw [List.inj_on_of_nodup_map hn (List.mem_of_find?_eq_some hf) h.1 h1]

/-- The tenants of segment n whose pins are open: `membersHeld`'s own term. -/
def pinsOpen (N : Numbers) (O : List Item) (n : ℕ) : List (ℕ × ℕ) :=
  (List.range 3).flatMap fun t => if O.contains (.pin n t) then N.sent n t else []

/-- **The facts that the proximity test's law on the first chain takes from "reached"**, at a state
s without a mark. n: the number of the group's segment (the number of segments). -/
structure FactsK12 (d : First.FoldData) (N : Numbers) (n : ℕ) (cs : Codes) (ms : List Mem)
    (s : First.S) : Prop where
  /-- `FoldFacts.bookInOrder`. -/
  bookInOrder : K12.Door.atFirstBook d.ft s = true
  /-- `FoldFacts.seatsCarried`. -/
  seatsCarried : K12.Door.atFirstSeats d.L s = true
  /-- `FoldFacts.tidy`. -/
  tidy : OnBytes.Means.tidy4B s.st = true
  /-- `FoldFacts.codes`. -/
  codes : s.st.codes = d.sent.codes
  /-- No field of `FoldFacts`: a lemma along `RchAt`: UNPAID. At the finish the frame's group is the
  listed one. (`FoldFacts.groupIs` speaks at places inside a segment alone.) Its payer, by
  report: the code switch's files (the kind K2): the last switch's step lays it; the join
  in these letters is not typed. -/
  groupAtFinish : ∀ o, s.here = .fin o → o.fr.group = N.groupAt n
  /-- No field of `FoldFacts`: a lemma along `RchAt`: UNPAID. The sendings' invariant at each member
  of the group under test, at the listed shape: the message is marked as sampled and holds just the
  kind's one sample row, at an out-of-domain (OOD) seed whose factor reads as a unit, with an OOD
  answer. Its payer, by report: the code switch's files (kind K2): a lemma behind
  an accept of the last switch's step, to be stated there, carried on by `K1.SeedIs.travels`. -/
  seedIs : ∀ G0, s.st.groups[N.groupAt n]? = some G0 → ∀ o ∈ G0.members.toList,
    ∀ x, ListedAt ms d.L.places o x → ∃ ρ yv, K1.SeedIs cs (x.1.l.get x.2).1 s.st o ρ yv

/-- **`FactsK12` out of `FoldFacts`**, with the two facts that it lacks as named premises. -/
theorem factsK12_of_fold {X P : Type} {Rch : ℕ → X → Prop} {at_ : X → P × First.S}
    {d : First.FoldData} {reqW : P → Array UInt32} {links : List ModelPart} {ps : List Place}
    (hf : First.FoldFacts Rch at_ d reqW links ps) (N : Numbers) (n : ℕ) (cs : Codes)
    (ms : List Mem) (k : ℕ) (a : X) (hr : Rch k a) (hm : (at_ a).2.failed = none)
    (h5 : ∀ o, (at_ a).2.here = .fin o → o.fr.group = N.groupAt n)
    (h6 : ∀ G0, (at_ a).2.st.groups[N.groupAt n]? = some G0 → ∀ o ∈ G0.members.toList,
      ∀ x, ListedAt ms d.L.places o x →
        ∃ ρ yv, K1.SeedIs cs (x.1.l.get x.2).1 (at_ a).2.st o ρ yv) :
    FactsK12 d N n cs ms (at_ a).2 :=
  ⟨hf.bookInOrder k a hr hm, hf.seatsCarried k a hr hm, hf.tidy k a hr hm, hf.codes k a hr hm, h5,
    h6⟩

/-- The listed shape of the tree in which a member sits is what the IOP as written tells of it. -/
def MemberTold {Xi : Type} (G : FileDescription Xi) (shapes : List TreeShape) (x : Mem) : Prop :=
  ∀ u T, G.oracleAt (x.1.seat x.2).1 = some u → shapes[(x.1.seat x.2).1]? = some T → ShapeIs T u

/-- **The facts on the list of rounds and the list of members.** O: the items that are open at the
border. No state is read. -/
structure PublicK12 (cs : Codes) {Xi : Type} (G : FileDescription Xi) (Fr : Frame) (π : P12)
    (r : Fmt.M1.Stage → ℕ) (d : First.FoldData) (N : Numbers) (n : ℕ) (O : List Item)
    (ms : List Mem) : Prop where
  joh : H2K.Pub.johOk π r = true
  plan : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true
  own : π.nums.ownMask = false
  first : π.nums.firstTree = d.ft
  codes : d.sent.codes = cs
  /-- no two members of ms have one seat -/
  seatsOnce : (ms.map seatOf).Nodup
  /-- no two messages are listed at one place -/
  placesOnce : d.L.places.Nodup
  /-- a class of rows of segment n is open -/
  rowOpen : n ∈ rowSegs O
  member : ∀ x ∈ ms, seatOf x ∈ pinsOpen N O n → MemberPub cs G Fr π r x ∧ MemberTold G d.L.shapes x

section
variable {P W : Type} {Fr : Frame} (N : Numbers) (Mg : Meaning P W) (links : List ModelPart)
  (ps : List Place)

/-- **Of the promise at an unmarked state.** -/
theorem on_parts (k : ℕ) (a : (P × First.S) × Fr.E.Str)
    (h : onQ N Mg links ps (fun a => a) k a) (hm : a.1.2.failed = none) :
    membersHeld N ((openSets links ps (start links))[k]?.getD []) a.1.2 = true ∧
      ∀ x ∈ sampledIn N ((openSets links ps (start links))[k]?.getD []),
        Mg.shown x.1 x.2 (strsOf Fr a.2) := by
  obtain ⟨_, h | ⟨hb, _, hs, _⟩⟩ := h
  · exact absurd hm h
  · simp only [Bool.and_eq_true] at hb
    exact ⟨hb.1.1.1.2, fun x hx => (hs x hx).1⟩

end

/-- A tenant of an open pin is among the sampled tenants whose pin is open. -/
theorem pinsOpen_sampled (N : Numbers) (O : List Item) (n : ℕ) (q : ℕ × ℕ)
    (h : q ∈ pinsOpen N O n) : q ∈ sampledIn N O := by
  obtain ⟨t, _, ht⟩ := List.mem_flatMap.1 h
  have ht' : q ∈ (if O.contains (.pin n t) = true then N.sent n t else []) := ht
  by_cases hc : O.contains (.pin n t) = true
  · rw [if_pos hc] at ht'
    exact List.mem_flatMap.2 ⟨.pin n t, List.contains_iff_mem.1 hc, ht'⟩
  · rw [if_neg hc] at ht'
    cases ht'

/-- **Each member of the group has a place in the book, at a tenant of an open pin.** -/
theorem members_placed (N : Numbers) (O : List Item) (s : First.S) (n : ℕ) (hn : n ∈ rowSegs O)
    (h : membersHeld N O s = true) (G0 : OnBytes.Group) (hG : s.st.groups[N.groupAt n]? = some G0) :
    ∀ o ∈ G0.members.toList, ∃ q, s.book.place[o]? = some q ∧ q ∈ pinsOpen N O n := by
  unfold membersHeld at h
  have h1 := List.all_eq_true.1 h n hn
  rw [hG] at h1
  simp only [Bool.and_eq_true, sameMembers] at h1
  intro o ho
  have h2 := List.all_eq_true.1 h1.1 o ho
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 h2
  refine ⟨q, hq, ?_⟩
  have h3 := List.all_eq_true.1 h1.2.1 q (List.mem_filterMap.2 ⟨o, ho, hq⟩)
  exact List.contains_iff_mem.1 h3

/-- "The seats are carried": the book's place of a message is the listed one. -/
theorem place_listed (L : K12.Door.Laid) (s : First.S) (h : K12.Door.atFirstSeats L s = true)
    (o : ℕ) (q : ℕ × ℕ) (hq : s.book.place[o]? = some q) : L.places[o]? = some q := by
  have ho : o < s.book.place.size := (Array.getElem?_eq_some_iff.1 hq).1
  rw [← K12.Door.place_of_seats (show K12.Door.seatsCarriedB L s.book = true from h) o ho]
  exact hq

/-- And a tree's shape is the listed one. -/
theorem tree_listed (L : K12.Door.Laid) (s : First.S) (h : K12.Door.atFirstSeats L s = true)
    (z : ℕ) (T : Tree) (hT : s.book.trees[z]? = some T) : L.shapes[z]? = some T.shape := by
  unfold K12.Door.atFirstSeats K12.Door.seatsCarriedB at h
  simp only [Bool.and_eq_true] at h
  have e : s.book.trees.toList.map (·.shape) = L.shapes.take s.book.trees.size :=
    eq_of_beq h.1.2
  have hz : z < s.book.trees.size := (Array.getElem?_eq_some_iff.1 hT).1
  have e1 : (s.book.trees.toList.map (·.shape))[z]? = some T.shape := by
    rw [List.getElem?_map, Array.getElem?_toList, hT]
    rfl
  rw [e, List.getElem?_take_of_lt hz] at e1
  exact e1

/-- "The book is in order", as the laws take it. -/
theorem bookOrd_of (ft : ℕ) (s : First.S) (h : K12.Door.atFirstBook ft s = true) :
    BookOrd ft s.book := fun z T hT =>
  K12.Door.numbers_of_book (show K12.Door.bookInOrderB ft s.book s.roots = true from h) z T hT

/-- One message, one member; one member, one message. -/
theorem ListedAt.one {ms : List Mem} {places : List (ℕ × ℕ)} (h : (ms.map seatOf).Nodup) {o : ℕ}
    {x x' : Mem} (a : ListedAt ms places o x) (b : ListedAt ms places o x') : x = x' :=
  List.inj_on_of_nodup_map h a.1 b.1 (Option.some.inj (a.2.symm.trans b.2))

theorem ListedAt.inj {ms : List Mem} {places : List (ℕ × ℕ)} (h : places.Nodup) {o o' : ℕ}
    {x : Mem} (a : ListedAt ms places o x) (b : ListedAt ms places o' x) : o = o' := by
  obtain ⟨h1, e1⟩ := List.getElem?_eq_some_iff.1 a.2
  obtain ⟨h2, e2⟩ := List.getElem?_eq_some_iff.1 b.2
  exact (List.Nodup.getElem_inj_iff h).1 (e1.trans e2.symm)

section
variable {P W Xi : Type} {Fr : Frame} (cs : Codes) (G : FileDescription Xi) (N : Numbers)
  (Mg : Meaning P W) (links : List ModelPart) (ps : List Place) (ms : List Mem) (L : K12.Door.Laid)

/-- **Each member of the group under test is listed at a member of ms, at a tenant of an open pin,
and every leaf of its word is shown.** -/
theorem member_listed (n k : ℕ) (a : (P × First.S) × Fr.E.Str)
    (h : onQ N Mg links ps (fun a => a) k a) (hm : a.1.2.failed = none)
    (hsh : Mg.shown = shownJT cs G ms)
    (hn : n ∈ rowSegs ((openSets links ps (start links))[k]?.getD []))
    (hL : K12.Door.atFirstSeats L a.1.2 = true) (G0 : OnBytes.Group)
    (hG : a.1.2.st.groups[N.groupAt n]? = some G0) :
    ∀ o ∈ G0.members.toList, ∃ x, ListedAt ms L.places o x ∧
      a.1.2.book.place[o]? = some (seatOf x) ∧
      seatOf x ∈ pinsOpen N ((openSets links ps (start links))[k]?.getD []) n ∧
      ShownAt G cs x.1.l x.1.seat (strsOf Fr a.2) x.2 := by
  obtain ⟨h1, h2⟩ := on_parts N Mg links ps k a h hm
  intro o ho
  obtain ⟨q, hq, hp⟩ := members_placed N _ a.1.2 n hn h1 G0 hG o ho
  have h3 := h2 q (pinsOpen_sampled N _ n q hp)
  rw [hsh] at h3
  obtain ⟨⟨x, hx, hs⟩, h4⟩ := h3
  have e : seatOf x = q := hs
  exact ⟨x, ⟨hx, by rw [e]; exact place_listed L a.1.2 hL o q hq⟩, by rw [e]; exact hq,
    by rw [e]; exact hp, h4 x hx hs⟩

end

end H2K12

#print axioms H2K12.listed_of_memOf
#print axioms H2K12.memOf_listed
#print axioms H2K12.factsK12_of_fold
#print axioms H2K12.on_parts
#print axioms H2K12.members_placed
#print axioms H2K12.place_listed
#print axioms H2K12.tree_listed
#print axioms H2K12.bookOrd_of
#print axioms H2K12.ListedAt.one
#print axioms H2K12.ListedAt.inj
#print axioms H2K12.member_listed
