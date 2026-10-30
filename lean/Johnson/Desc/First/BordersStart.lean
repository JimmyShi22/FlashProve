-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/BordersStart.lean: THE TABLE OF JOINTS' PROMISE AT THE FIRST CHAIN's FIRST
BORDER, AT THE RECORD THAT State.lean's OWN START MAKES. Small lemmas; no Mathlib.

What is said. `startReq?_is`: a lawful start is `S.start codes c` with the request's words laid, for
some state c of the calls. `startReq?_reply`, `blank_reply`: AT THE START THE RECORD HOLDS NO REPLY,
lawful or not. `no_row_at_start`, `rowSegs_start`, `sampledIn_start`: of the items that are open at
the start none is a class of rows, none a pin with a sample. `rowsHeld_start`, `membersHeld_start`,
`samplesHeld_start`: so these three Bools say yes there at every record. `shapeAt_start`: the
book-keeping says yes at a lawful start. `IsStart`: a first record: the bare start with the
request's words laid, or the marked blank; `isStart_startReq?`, `isStart_if`: State.lean's own start
is one, and so is the same text with the start's value taken from elsewhere. `isStart_reply`.
**`onAt_start`: AT A FIRST RECORD THE PROMISE AT THE FIRST BORDER FOLLOWS FROM: the stored table
decodes; where the start is lawful, the statement is in order and every public item that is open at
the start holds (no reply is heard; no message is sent; a filling's), with what it says beside its
Bool (hpp); and the numbers count no tree and no message in front of the front block (hbk, hms). ONE
DIRECTION ALONE.** `openSets_head`,
`flatPlaces_head`: the first open set is the start's, the first place the front block's: so the
promise is the table's own at border 0.

Limits. (1) `decodes`, `inOrder` and `pub` are letters of `Meaning`: all three stay premises here.
(2) Of a chain with a front block (as both real plans have it). (3) Nothing on any later border.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open VerifiableInference.Desc OnBytes OnBytes.Model

/-- A start that passes the start's tests is the bare start at some state of the calls. -/
theorem start?_is {Pp : Par} {codes : Codes} {shape : Params.ReqShape}
    {layout : Params.ReqLayout} {s : S} (h : S.start? Pp codes shape layout = some s) :
    ∃ c, s = S.start codes c := by
  unfold S.start? S.startP at h
  split at h
  · refine ⟨(S.firstRecord codes shape layout).check, ?_⟩
    rw [← Option.some.inj h]
    rfl
  · cases h

/-- A lawful start: the bare start with the request's words laid. -/
theorem startReq?_is {Pp : Par} {codes : Codes} {shape : Params.ReqShape}
    {layout : Params.ReqLayout} {T V : Nat} {req : Array UInt32} {s : S}
    (h : S.startReq? Pp codes shape layout T V req = some s) :
    ∃ c, s = (S.start codes c).withReq req := by
  unfold S.startReq? S.startReqP at h
  obtain ⟨s0, h0, h1⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨c, rfl⟩ := start?_is (Pp := Pp) (shape := shape) (layout := layout) h0
  split at h1
  · exact ⟨c, (Option.some.inj h1).symm⟩
  · cases h1

/-- At a lawful start the record holds no reply. -/
theorem startReq?_reply {Pp : Par} {codes : Codes} {shape : Params.ReqShape}
    {layout : Params.ReqLayout} {T V : Nat} {req : Array UInt32} {s : S}
    (h : S.startReq? Pp codes shape layout T V req = some s) : s.out.reply = none := by
  obtain ⟨c, rfl⟩ := startReq?_is h
  rfl

/-- Nor does the marked blank. -/
theorem blank_reply : S.blank.out.reply = none := rfl

/-- The marked blank bears a mark. -/
theorem blank_marked : S.blank.failed ≠ none := by
  intro h
  cases h

/-- No class of rows is open at the start. -/
theorem no_row_at_start (links : List ModelPart) (m : Nat) (c : RowClass) :
    Item.row m c ∉ start links := by
  intro hi
  unfold start at hi
  rcases List.mem_append.1 hi with h | h
  · simp at h
  · obtain ⟨x, _, hx⟩ := List.mem_flatMap.1 h
    simp at hx

theorem rowSegs_start (links : List ModelPart) : rowSegs (start links) = [] := by
  unfold rowSegs
  rw [List.filterMap_eq_nil_iff.2 ?_]
  · rfl
  · intro i hi
    cases i <;> first | rfl | exact absurd hi (no_row_at_start links _ _)

section
variable {P W : Type} (N : Numbers)

theorem rowsHeld_start (links : List ModelPart) (s : S) : rowsHeld N (start links) s = true := by
  unfold rowsHeld
  rw [rowSegs_start]
  rfl

theorem membersHeld_start (links : List ModelPart) (s : S) :
    membersHeld N (start links) s = true := by
  unfold membersHeld
  rw [rowSegs_start]
  rfl

/-- No pin with a sample is open at the start. -/
theorem sampledIn_start (links : List ModelPart) : sampledIn N (start links) = [] := by
  unfold sampledIn
  apply List.flatMap_eq_nil_iff.2
  intro i hi
  unfold start at hi
  rcases List.mem_append.1 hi with h | h
  · simp at h
    rcases h with rfl | rfl | rfl <;> rfl
  · obtain ⟨x, _, hx⟩ := List.mem_flatMap.1 h
    simp at hx
    rcases hx with rfl | rfl | rfl | rfl <;> rfl

theorem samplesHeld_start (Mg : Meaning P W) (links : List ModelPart) (a : P × S) :
    samplesHeld N Mg (start links) a = true := by
  unfold samplesHeld
  rw [sampledIn_start]
  rfl

end

/-- The front block's place. -/
def frontPlace : Place := { chain := 1, link := none, piece := 0, kind := .frame }

theorem flatPlaces_head (links : List ModelPart) (several : Bool) :
    (flatPlaces true links several)[0]? = some frontPlace := by
  simp [flatPlaces, flatPlacesOf, frameAt, frontPlace]

theorem openSets_head (links : List ModelPart) (ps : List Place) (O : List Item) :
    (openSets links ps O)[0]?.getD [] = O := by
  cases ps <;> rfl

/-- The book-keeping says yes at a lawful start. -/
theorem shapeAt_start (links : List ModelPart) (codes : Codes) (c : ChainCheck)
    (req : Array UInt32) :
    shapeAt links (some frontPlace) ((S.start codes c).withReq req) = true := by
  rfl

/-- The book is empty at a lawful start. -/
theorem bookAt_start (N : Numbers) (codes : Codes) (c : ChainCheck) (req : Array UInt32)
    (h : N.treesAt (some frontPlace) = 0) (h' : N.msgsAt (some frontPlace) = 0) :
    bookAt N (some frontPlace) ((S.start codes c).withReq req) = true := by
  unfold bookAt
  rw [h, h']
  rfl

/-- A record is a first record: the bare start at some state of the calls with the request's words
laid, or the marked blank. -/
def IsStart (codes : Codes) (req : Array UInt32) (s : S) : Prop :=
  (∃ c, s = (S.start codes c).withReq req) ∨ s = S.blank

/-- State.lean's own start, "else the marked blank", is one. -/
theorem isStart_startReq? (Pp : Par) (codes : Codes) (shape : Params.ReqShape)
    (layout : Params.ReqLayout) (T V : Nat) (req : Array UInt32) :
    IsStart codes req ((S.startReq? Pp codes shape layout T V req).getD S.blank) := by
  cases e : S.startReq? Pp codes shape layout T V req with
  | none => exact Or.inr rfl
  | some s => exact Or.inl (startReq?_is e)

/-- So is the same text with the start's value taken from elsewhere: s₀ is what `S.start?` gave. -/
theorem isStart_if {Pp : Par} {codes : Codes} {shape : Params.ReqShape}
    {layout : Params.ReqLayout} {s₀ : S} (h0 : S.start? Pp codes shape layout = some s₀)
    (T V : Nat) (req : Array UInt32) :
    IsStart codes req (if (s₀.withReq req).reqOk T V then s₀.withReq req else S.blank) := by
  obtain ⟨c, rfl⟩ := start?_is h0
  split
  · exact Or.inl ⟨c, rfl⟩
  · exact Or.inr rfl

/-- **A first record holds no reply.** -/
theorem isStart_reply {codes : Codes} {req : Array UInt32} {s : S} (h : IsStart codes req s) :
    s.out.reply = none := by
  rcases h with ⟨c, rfl⟩ | rfl <;> rfl

/-- No public item is tied to an item that is open at the start. -/
theorem pubOfItems_start (links : List ModelPart) : pubOfItems (start links) = [] := by
  unfold pubOfItems
  apply List.flatMap_eq_nil_iff.2
  intro i hi
  unfold start at hi
  rcases List.mem_append.1 hi with h | h
  · simp at h
    rcases h with rfl | rfl | rfl <;> rfl
  · obtain ⟨x, _, hx⟩ := List.mem_flatMap.1 h
    simp at hx
    rcases hx with rfl | rfl | rfl | rfl <;> rfl

/-- At the start the public items ask what is open there: no reply is heard; no oracle message is
sent; and what a filling of the door lays open at the start. -/
theorem pubHeld_start {P W : Type} (Mg : Meaning P W) (links : List ModelPart) (a : P × S)
    (h : ∀ q ∈ pubStartM Mg.more, Mg.pub q a = true) :
    pubHeld Mg (start links) (pubStartM Mg.more) a = true := by
  unfold pubHeld
  rw [pubOfItems_start, List.append_nil]
  exact List.all_eq_true.2 h

theorem pubSets_head (M : More) (links : List ModelPart) (ps : List Place) :
    (pubSets M links ps)[0]?.getD [] = pubStartM M := by
  unfold pubSets
  cases ps <;> rfl

/-- **The promise at the first border, at a first record.** -/
theorem onAt_start {P W : Type} (N : Numbers) (Mg : Meaning P W) (links : List ModelPart) (a : P × S)
    (y : Strs) {codes : Codes} {req : Array UInt32} (ha : IsStart codes req a.2)
    (hd : Mg.decodes a y) (hin : a.2.failed = none → Mg.inOrder a = true)
    (hpub : a.2.failed = none → ∀ q ∈ pubStartM Mg.more, Mg.pub q a = true)
    (hpp : a.2.failed = none → ∀ q ∈ pubStartM Mg.more, Mg.pubP q a)
    (hbk : N.treesAt (some frontPlace) = 0) (hms : N.msgsAt (some frontPlace) = 0) :
    onAt N Mg links (some frontPlace) (start links) (pubStartM Mg.more) a y := by
  refine ⟨hd, ?_⟩
  rcases ha with ⟨c, hs⟩ | hs
  · right
    have hf : a.2.failed = none := by rw [hs]; rfl
    refine ⟨?_, samplesHeld_start N Mg links a, ?_, hpp hf⟩
    · rw [rowsHeld_start, membersHeld_start, hin hf, pubHeld_start Mg links a (hpub hf), hs,
        shapeAt_start, bookAt_start N codes c req hbk hms]
      rfl
    · intro x hx
      rw [sampledIn_start] at hx
      cases hx
  · left
    rw [hs]
    exact blank_marked

end VerifiableInference.Desc.First
