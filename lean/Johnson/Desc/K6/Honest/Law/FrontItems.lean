-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K6/Honest/Law/FrontItems.lean: WHAT THE TABLE's PROMISE SAYS OF THE VERIFIER's STATE IN
FRONT OF THE OUTPUT HEAD's OWN ROUNDS (border 341 of the full chain), AT THE COMPOSED MEANING
mgAll D Mg (Johnson/Desc/Sound/MgAll.lean), AS ONE STRUCTURE: so that a law on these rounds takes
its premises on the state in front by projection. One structure, statements with their proofs.
Over the library and Honest/Small/PromiseParts.lean.

What it is not. It speaks of the full chain alone. The items look 24 and lookOut 24 3 stand in the
structure as the composed meaning has them. Nothing says that the promise holds at any state.
Nothing on any property.

  `K6FrontItems D Mg a`   six clauses on the book-keeping; the twelve public items that are open
                          there (`open341`, Johnson/Desc/Kinds/Law/K6PubKept.lean), each as its own
                          test or sentence at the state; what every open public item says beside its
                          test
  `left_open341`          the item left 24 is open there: by evaluation in the kernel
  `frontItems_of_parts`   CONDITIONAL on the promise's clauses at 341 (`PartsAt`) and on "Mg adds no
                          extra public test"
  `K6FrontItems.noneWaits`   no count of rows waits
  `K6FrontItems.spells`      the public part's bytes spell a request
  `K6FrontItems.lookHead`, `.k6Left`   CONDITIONAL: the output head's segment is number 24
  `K6FrontItems.lookOutAt`   CONDITIONAL: piece 3 of segment 24 has the sort named
At the end: the forms in which three callers ask, each closed by a field as it stands.

Why. The library reads the same sentences out of its own promise (Kinds/Law/K6FrontSays.lean,
K6FrontShape.lean, K6WideFront.lean; Sound/K6Tied.lean: `k6_t1`), from a premise that holds "the
stored table decodes" and two clauses on the oracles' strings: on the honest side that premise is
not to be had: no oracle's strings are at hand. WHAT IS TYPED ANEW, AND WHY: the last lines of
`sentIs_front`, `treesAre_front`, `fresh_front`, `left_front`, `rows_front`, `k6_t1` and
`pubSays_mgAll`, behind `PartsAt` in the place of that premise (`k6_t1` is general in the meaning,
but it wants a frame, a member of its strings, the table's test `pubFit` and a structure of fits for
`pubSays_mgAll`; here one fact on the public parameters is enough). CALLED: `open341`,
`place341_full`, `mgAll_more_closed`, the lemmas `pubAll_…` of Johnson/Desc/First/PubAllAt.lean,
`wellLaidB_of_ledgerB`, `tokenB_of_heard`, and the three equivalences of Kinds/Law/K6OnB.lean.

-/
import Johnson.Desc.ProofFile.Honest.Small.PromiseParts
import Johnson.Desc.Kinds.Law.K6PubKept
import Johnson.Desc.Kinds.Law.K6FrontSays
import Johnson.Desc.Kinds.Law.K6AtMgAll
import Johnson.Desc.Sound.MgBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law
open VerifiableInference.Desc (Place Strs Wit)
open VerifiableInference.Desc.First (S Pub Meaning)
open VerifiableInference.Desc.Sound (openQ pubQ linksFull MgData mgAll mgMore MsgT CellsQ)
open VerifiableInference.Desc.Kinds.Head.Law.AtFold (placeK6)
open ProofFile.Honest.Small (PartsAt)

variable {Xi P Tok : Type} {rows cols nR : ℕ} {Wp : OnBytes.Model.Verify.Public}

/-- The written list of places, at the full chain. -/
local notation "PS" => First.flatPlacesOf linksFull true

/-- **What the table's promise says of the verifier's state in front of the output head's own
rounds** (border 341 of the full chain), at the composed meaning mgAll D Mg: the clauses on the
book-keeping, and each of the twelve public items that are open there as its own test or sentence at
the state. Two items (look 24, lookOut 24 3) stand as the composed meaning has them: what they
unfold to hangs on a fact on the public parameters. -/
structure K6FrontItems (D : MgData Xi P Tok rows cols nR Wp)
    (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT)) (a : P × S) : Prop where
  /-- the book-keeping -/
  shape : First.shapeAt linksFull (some placeK6) a.2 = true
  rows : First.rowsHeld D.N (openQ linksFull PS 341) a.2 = true
  members : First.membersHeld D.N (openQ linksFull PS 341) a.2 = true
  order : (mgAll D Mg).inOrder a = true
  book : First.bookAt D.N PS[341]? a.2 = true
  samples : ∀ x ∈ First.sampledIn D.N (openQ linksFull PS 341),
    smpHeld a.2.st a.2.book x.1 x.2 = true
  /-- the twelve -/
  tokenSmall : tokenHeardB Wp.hS (readsOf Wp) a.2 = true
  ledger : First.ledgerB a.2 = true
  linkFresh : VerifiableInference.OnPublicFiles.linkFreshB (D.sent.arrayOf.getD 24 #[]) a.2 = true
  freeAbove : ((D.pubD.nsOf 24).any fun n => First.freeAboveB n a.2) = true
  sentIs : First.FillSent.sentIsB D.pubD.dS 24 a.2 = true
  treesAre : First.FillSent.treesAreB D.pubD.dS 24 a.2 = true
  lookOut : (mgAll D Mg).pub (.lookOut 24 3) a = true
  look : (mgAll D Mg).pub (.look 24) a = true
  /-- what the item left 24 says beside its test, which is always true: the last field at that item
  -/
  left : VerifiableInference.OnPublicFiles.k3LeftItemAt Wp 24 a.2
  indexIs : K13.indexIsC D.N.indexNo a.2 = true
  indexThere : K13.indexThereC a.2 = true
  objects : ((D.runs 24 3 "objects").all fun p =>
    K9.formsInT (D.Rd 24) (D.N.sent 24 0) p.1 p.2 a.2) = true
  /-- what every open public item says beside its test -/
  sentences : ∀ q ∈ pubQ mgMore linksFull PS 341, (mgAll D Mg).pubP q a

/-- The item left 24 is among the public items that are open at border 341 of the full chain. -/
theorem left_open341 : Pub.left 24 ∈ pubQ mgMore linksFull PS 341 := by decide +kernel

/-- **From the promise's clauses at border 341 to the structure.** CONDITIONAL: Mg adds no extra
public test of its own. -/
theorem frontItems_of_parts (D : MgData Xi P Tok rows cols nR Wp)
    (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT)) (hM : Mg.more = {}) (a : P × S)
    (h : PartsAt D.N (mgAll D Mg) linksFull PS 341 a) : K6FrontItems D Mg a := by
  have hmore : (mgAll D Mg).more = mgMore := Sound.mgAll_more_closed D Mg hM
  have hp : PS[341]? = some placeK6 := Sound.place341_full
  have hpub : ∀ q ∈ [Pub.tokenSmall, .ledger 24, .linkFresh 24, .freeAbove 24,
      .more (some 24) "frame.sentIs", .more (some 24) "ledger.treesAre", .lookOut 24 3, .look 24,
      .left 24, .indexIs, .indexThere, .formsInT 24 3 "objects"],
      (mgAll D Mg).pub q a = true := fun q hq => h.pub q (by
    rw [hmore, AtTable.open341]
    exact hq)
  have hsh := h.shape
  rw [hp] at hsh
  exact
    { shape := hsh, rows := h.rows, members := h.members, order := h.order, book := h.book
      samples := h.samples
      tokenSmall := hpub .tokenSmall (by simp)
      ledger := hpub (.ledger 24) (by simp)
      linkFresh := hpub (.linkFresh 24) (by simp)
      freeAbove := hpub (.freeAbove 24) (by simp)
      sentIs := (First.pubAll_more_sentIs D.pubD Mg.pub 24 a).symm.trans
        (hpub (.more (some 24) "frame.sentIs") (by simp))
      treesAre := (First.pubAll_more_treesAre D.pubD Mg.pub 24 a).symm.trans
        (hpub (.more (some 24) "ledger.treesAre") (by simp))
      lookOut := hpub (.lookOut 24 3) (by simp)
      look := hpub (.look 24) (by simp)
      left := h.pubP (.left 24) (by
        rw [hmore]
        exact left_open341)
      indexIs := hpub .indexIs (by simp)
      indexThere := hpub .indexThere (by simp)
      objects := hpub (.formsInT 24 3 "objects") (by simp)
      sentences := fun q hq => h.pubP q (by
        rw [hmore]
        exact hq) }

variable {D : MgData Xi P Tok rows cols nR Wp} {Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT)}
  {a : P × S}

/-- No count of rows waits. -/
theorem K6FrontItems.noneWaits (R : K6FrontItems D Mg a) :
    First.Tape.RowsOwed.noneWaits a.2.rowsOwed = true := by
  have h := R.shape
  unfold First.shapeAt at h
  simp only [Bool.and_eq_true, Bool.or_eq_true] at h
  have hw : First.mayWait linksFull placeK6 = false := by decide
  have h1 : a.2.noneWaits = true := h.1.2.resolve_right (by
    rw [hw]
    exact Bool.false_ne_true)
  unfold First.S.noneWaits at h1
  cases e : a.2.rowsOwed with
  | none => rfl
  | some r =>
    rw [e] at h1
    exact h1

/-- The second half of "in order": the public part's bytes spell a request. -/
theorem K6FrontItems.spells (R : K6FrontItems D Mg a) :
    (_root_.Meaning.backReq (D.reqB a.1)).isSome = true := by
  have h := R.order
  rw [Sound.mgAll_inOrder_at, Bool.and_eq_true] at h
  exact h.2

/-- The item look 24, unfolded. CONDITIONAL: the output head's segment is number 24. -/
theorem K6FrontItems.lookHead (R : K6FrontItems D Mg a)
    (hH : VerifiableInference.OnPublicFiles.headLink Wp = 24) :
    lookHeadB Wp.hS (readsOf Wp) a.2 = true := by
  have h := R.look
  rw [Sound.mgAll_pub, First.pubAll_look_head D.pubD Mg.pub 24 (by
    show ((24 : ℕ) == VerifiableInference.OnPublicFiles.headLink Wp) = true
    rw [hH]
    rfl) a] at h
  exact h

/-- The item lookOut 24 3, unfolded. CONDITIONAL: piece 3 of segment 24 has the sort dg. -/
theorem K6FrontItems.lookOutAt (R : K6FrontItems D Mg a) (dg : Bool)
    (hK : First.Look.k3SortAt Wp 24 3 = some dg) :
    First.Look.lookOutC D.pubD.d3 24 dg a.2 = true := by
  have h := R.lookOut
  rw [Sound.mgAll_pub, First.pubAll_lookOut D.pubD Mg.pub 24 3 dg hK a] at h
  exact h

/-- **The ledger is well laid, the token heard is below the vocabulary's size, the lookup's last
claim is filled.** CONDITIONAL: the output head's segment is number 24. -/
theorem K6FrontItems.k6Left (R : K6FrontItems D Mg a)
    (hH : VerifiableInference.OnPublicFiles.headLink Wp = 24) : K6Left Wp a.2 :=
  ⟨(Came.wellLaidB_iff _).1 (wellLaidB_of_ledgerB Wp a.2 R.ledger),
    (Came.tokenB_iff _ _).1 (tokenB_of_heard Wp a.2 R.tokenSmall),
    (Came.cEndB_iff _ _).1 (R.lookHead hH)⟩

/-! ## The forms in which three callers ask: each is a field as it stands -/

example (R : K6FrontItems D Mg a) : First.shapeAt Sound.linksFull
    (some { chain := 1, link := some 24, piece := 4, kind := .K6 }) a.2 = true := R.shape
example (R : K6FrontItems D Mg a) : VerifiableInference.OnPublicFiles.k3LeftItemAt Wp 24 a.2 := R.left
example (R : K6FrontItems D Mg a) : tokenHeardB Wp.hS (readsOf Wp) a.2 = true := R.tokenSmall
example (R : K6FrontItems D Mg a) : tokenHeardB D.pubD.hShape D.pubD.iU3 a.2 = true := R.tokenSmall
example (R : K6FrontItems D Mg a) : First.FillSent.sentIsB D.pubD.dS 24 a.2 = true := R.sentIs
example (R : K6FrontItems D Mg a) :
    VerifiableInference.OnPublicFiles.linkFreshB (D.sent.arrayOf.getD 24 #[]) a.2 = true := R.linkFresh
example (R : K6FrontItems D Mg a) : First.Look.linkFreshC D.pubD.d3 24 a.2 = true := R.linkFresh
example (R : K6FrontItems D Mg a) : First.bookAt D.N PS[341]? a.2 = true := R.book
example (R : K6FrontItems D Mg a) : First.FillSent.treesAreB D.pubD.dS 24 a.2 = true := R.treesAre
example (R : K6FrontItems D Mg a) :
    ((D.pubD.nsOf 24).any fun n => First.freeAboveB n a.2) = true := R.freeAbove
example (R : K6FrontItems D Mg a) : First.ledgerB a.2 = true := R.ledger

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.left_open341
#print axioms VerifiableInference.Desc.Kinds.Head.Law.frontItems_of_parts
#print axioms VerifiableInference.Desc.Kinds.Head.Law.K6FrontItems.noneWaits
#print axioms VerifiableInference.Desc.Kinds.Head.Law.K6FrontItems.spells
#print axioms VerifiableInference.Desc.Kinds.Head.Law.K6FrontItems.lookHead
#print axioms VerifiableInference.Desc.Kinds.Head.Law.K6FrontItems.lookOutAt
#print axioms VerifiableInference.Desc.Kinds.Head.Law.K6FrontItems.k6Left
