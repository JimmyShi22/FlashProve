-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/AtTable.lean: KIND K13's JOINED BLOCK AT ITS ROW OF THE TABLE OF JOINTS: the
kind's law in its own words (`atM3_goodInA`, Johnson/Desc/K13/Law/PinA.lean) with its five ties to
the table's promise and items (`TiedAt`, Johnson/Desc/Sound/ChainOfPromises.lean). Definitions and
statements with their proofs.

OBJECT. `atM3 P` (Johnson/Desc/K13/AtS.lean): the front, the batching of the pending rows and the
quiet part, as one block; as a piece: `pieceM3`; as a chain holds it: any block c with
`c.UnderR (atM3 P)` (Johnson/Desc/Sound/SeatGuardChain.lean: the block's rounds; a yes of c is the
same yes of the block), by `Piece.seat` (Johnson/Desc/Sound/SeatedPiece.lean).
USER. `EachTied` | `chainOfPromises` (ChainOfPromises.lean) ask `TiedAt N Mg links ps get k q` at
each block's number: `k13_tied`, `k13_tied_seat` and `k13_tied_lift` end in that proposition, to the
letter.
LETTERS. The table's own: N, Mg, links, ps, get, k. The kind's: P (its numbers); rw (what the rows
on the table read of a witness: a matrix, and mask entries named by a message's NUMBER in the
statement and a place: A FAMILY IN THE TABLE's RECORD: a reader may go through what the record
holds).
FIELD. `first_chain_knows_means` (Johnson/Goal/Skeleton/ProofFile.lean), through `chainOfPromises`;
the step from that theorem's end into the field is other files' to show, and is not typed here.

THE NUMBER AND THE TENANT. The rows on the table name their mask entries by the number that the
record holds for the index masks' message (`S.out.indexMasks`; the block's front tests that they
name no other). The table's pin `pinI` speaks of a TENANT (`N.index`: a tree and a place in it).
`promise_index` reads off the promise in front the two public items that are tied to `pinI`, and
`bookAt`; `FillM3.det` is asked under them. MARK: BY THEIR DOCSTRINGS IN Borders.lean THESE THREE
TIE THE RECORD's NUMBER TO THE PLAN's NUMBER, AND SAY THAT THE MESSAGE IS THERE AND HOW MANY
PLACES THE BOOK HAS: NONE NAMES `N.index`. SO: AT A READER THAT
GOES FROM A NUMBER TO A TENANT BY THE RECORD's OWN BOOK, AND AT SENTENCES THAT SAY NO MORE THAN
THAT, `det` IS FALSE, `FillM3` HAS NO MEMBER, AND THE TIES BELOW ARE TRUE AND EMPTY. WHAT IS
WANTED: THE INDEX MASKS' SEAT: by the book the message of the record's number sits at `N.index`
(`K1.indexSeatB`, Johnson/Desc/K1/Law/IndexBools.lean, with its maker and keepers). `det` is
handed the Bool of EVERY public item that is open in front: so a filling of the table's door whose
item gives the seat (alone, or with these three and an equation on the plan) puts it in `det`'s
hand. At a reader that goes by a list of the plan `det` wants instead a test on the plan ("the
list has `N.index` at `N.indexNo`"), which has no code anywhere; and whoever closes the one claim
and the pin behind this chain wants the seat then. `det` ALSO FIXES THE FORM OF `Mg.pin`: only
"the decoder gives some m, and the witness's message is m" pays it: the promise gives "at most
one" (`noColl`) for a tenant, and "there is one" for the stored table alone.

Main names:
  `shape_behind`: the table's book-keeping (`shapeAt`) holds behind the block: by `atM3_rec`
    (Johnson/Desc/K13/Law/AtRecord.lean: what the block does to the record; `StepM3`: two records
    between which its own decision has said yes).
  `OldKept j`, `oldKept_out`: a piece leaves the stored table, and tree j if it was sent in front of
    the piece's stretch: in the table's plain strings.
  `RowM3`: WHAT IS ASKED OF THE TABLE at (M, links, ps, k), M a filling of the table's door:
    eleven facts on its rows, open sets and numbers: each can be evaluated at a given plan.
  `FillM3`: WHAT IS ASKED OF THE TABLE's LETTERS: seventeen clauses on `Meaning`'s fields and rw.
  `promise_front`, `promise_index`: what the promise in front gives at a record without a mark.
  `RelM3`: the kind's relation at both borders, in the table's letters: the stored table's and the
    index masks' pins, and all rows on the table (`S.rows`) are true.
  `inOrder_rides`: a step keeps every relation on statements that the ground's functions keep
    (`stepM3_keeps`): so `FillM3.inOrder` is paid wherever "in order" reads the statement by such a
    condition.
  `k13_tied`: **the five ties**, of any piece whose yes is a step of the block and that has the
    kind's law at these words. `k13_law_seat`: the piece that holds c has that law: by
    `atM3_goodInA`, which has one reader for all records, called statement by statement at the
    reader of the record in front. `k13_tied_seat`: **so it is tied**, where the chain's record is
    the carried record itself. `k13_tied_lift`: **and lifted** (`Piece.lift`,
    Johnson/Desc/Sound/LiftRule.lean), where the carried record is a part of the chain's record.

WHICH TIE IS PAID BY WHAT. t1: the kind's condition in front IS the table's promise without a mark.
t2: the book-keeping by `atM3_rec`; the open rows' lists and the members hold because no class of
rows is open behind (`RowM3.noRows`); "in order": `FillM3.inOrder`, which `inOrder_rides` pays by
`atM3_keeps` (Johnson/Desc/K13/Keeps.lean); `Pub.frontOk` by the law's own condition behind
(`FrontOk`, through `frontOkB_iff`); `bookAt` by `atM3_book` and `RowM3.trees` | `msgs`; the two
tied public items, whatever public item rides, the sample held, the leaves shown, no collision,
"decodes": `FillM3`'s clauses that these letters ride over a step. t3, t4: by `FillM3.pile` |
`pileOne` and the pins. t5: no open item rides past the block (`RowM3.noRider`).

What is not claimed. Members: in this file none. Of `RowM3`: at two lists of segments
(Johnson/Desc/K13/Law/AtTableRow.lean). Of `FillM3`: at a filling for a try alone, which reads no
oracle (Johnson/Desc/K13/Law/AtTableTry.lean); AT THE FILLING THAT IS MEANT: NONE.
`FillM3.det` wants more of rw than its type says: a pin fixes a message inside its own ranges alone,
and `AgreeAt` asks every place: so rw must read the matrix off what the stored table's pin fixes,
the mask entries off the message at the seat, and be constant beyond the message's ranges. At
`Mg.decodes` := never all is free and the conclusion says nothing. That a description's chain holds
such a block at place k, with this stretch, this record and this kind of challenges (`ckP .two`):
not here. `Declared` is a test on a plan's written rounds. Nothing on the errors' size. Nothing on
soundness, on an honest prover or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.AtRecord
import Johnson.Desc.Sound.ChainOfPromises
import Johnson.Desc.Sound.SeatedPiece
import Johnson.Desc.Sound.LiftRule

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice Iop Run
open OnBytes.Flat OnBytes.Maker
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers)
open VerifiableInference.Desc.Sound (Frame Piece strsOf onQ meansQ relQ insQ outsQ TiedAt relAt
  openAfter out_seat liftOut)
open VerifiableInference.Desc.Ground (GroundQuiet)

/-! ## 1 The record behind the block -/

section
variable {Cl : Type}

/-- The table's book-keeping holds behind: the chain stands at its end, no count of rows waits, no
segment is open. p: the place of the next block, or none. -/
theorem shape_behind {P : Where} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (atM3 (Cl := Cl) P).decide s rs gs = .ok s')
    (links : List ModelPart) (p : Option Place) (hp : ∀ p', p = some p' → First.standAt links p' = .mem) :
    First.shapeAt links p s' = true := by
  obtain ⟨_, _, _, _, rfl⟩ := atM3_rec h
  cases p with
  | none => simp [First.shapeAt, First.standOf, S.noneWaits]
  | some p' => simp [First.shapeAt, First.standOf, S.noneWaits, S.link?, hp p' rfl]

end

/-! ## 2 A step, and what a piece leaves of the oracles -/

/-- The stored table and the tree number j are as they were. -/
def OldKept (j : ℕ) (y y' : Strs) : Prop := y'.cell = y.cell ∧ ∀ x, y'.col j x = y.col j x

/-- A piece leaves the stored table, and a tree that was sent in front of its stretch. General in
the piece. -/
theorem oldKept_out {T Cl W : Type} {C : PQ.CK} {F : Frame} (p : Piece C F T Cl W)
    {a b : T × F.E.Str} {τ : Tr (uLT C p.ds)} (h : p.ior.red.out a τ = some b) {j : ℕ}
    (hj : j < p.base) : OldKept j (strsOf F a.2) (strsOf F b.2) := by
  rw [out_imp p h]
  refine ⟨rfl, fun x => ?_⟩
  show (colAt F (p.ior.imp a.2 τ) j x).getD [] = (colAt F a.2 j x).getD []
  rw [old_kept p a.2 τ j x hj]

/-- So "in order" rides over a step wherever it reads the statement by a condition that the
ground's functions keep. -/
theorem inOrder_rides {Pp W Cl : Type} {P : Where} (Mg : Meaning Pp W) (I : Statement → Prop)
    (hI : ∀ x, Mg.inOrder x = true ↔ I x.2.st) (H : GroundQuiet fun A B => I A → I B)
    (x x' : Pp × S) (h : StepM3 Cl P x x') (hx : Mg.inOrder x = true) : Mg.inOrder x' = true :=
  (hI x').2 (stepM3_keeps H h ((hI x).1 hx))

/-! ## 3 What is asked of the table, and of its letters -/

/-- The items that the table computes as open at border j. -/
def openAt (links : List ModelPart) (ps : List Place) (j : ℕ) : List Item :=
  (First.openSets links ps (First.start links))[j]?.getD []

/-- **What is asked of the table at (links, ps, k).** -/
structure RowM3 (N : Numbers) (M : First.More) (links : List ModelPart) (ps : List Place) (k : ℕ) :
    Prop where
  /-- the row closes or reads nothing else than the pile, the stored table's pin, the index masks'
  pin and "no mark" -/
  ins : ∀ i, insQ links ps k i → i = .pile ∨ i = .pinW ∨ i = .pinI ∨ i = .unmarked
  /-- it opens the one claim, and leaves the two pins open -/
  outs : outsQ links ps k .pileOne ∧ outsQ links ps k .pinW ∧ outsQ links ps k .pinI
  /-- nothing rides past the block -/
  noRider : ∀ i, openAfter (insQ links ps) (outsQ links ps) (· ∈ First.start links) k i →
    insQ links ps k i
  /-- behind the block the chain is to stand at its end -/
  next : ∀ p', ps[k + 1]? = some p' → First.standAt links p' = .mem
  /-- the index masks' pin is open in front -/
  pinIn : Item.pinI ∈ openAt links ps k
  /-- and it is the one pin with a sample that is open behind -/
  idxOnly : ∀ t ∈ First.sampledIn N (openAt links ps (k + 1)), t = N.index
  /-- no class of rows is open behind -/
  noRows : First.rowSegs (openAt links ps (k + 1)) = []
  /-- the one public item that comes at the block; whatever else is open behind was open in front
  (at the table's own rows: nothing; a filling of the door may have items that ride) -/
  pubs : ∀ q ∈ (First.pubSets M links ps)[k + 1]?.getD [],
    q = .frontOk ∨ q ∈ (First.pubSets M links ps)[k]?.getD []
  /-- and the two that are tied to an item open there: to the index masks' pin -/
  tied : ∀ q ∈ First.pubOfItems (openAt links ps (k + 1)), q = .indexIs ∨ q = .indexThere
  /-- by the plan the block sends nothing: as many trees and messages behind as in front -/
  trees : N.treesAt ps[k + 1]? = N.treesAt ps[k]?
  msgs : N.msgsAt ps[k + 1]? = N.msgsAt ps[k]?

/-- So the index masks' tenant's sample is asked in front. -/
theorem idx_of_pin (N : Numbers) {O : List Item} (h : Item.pinI ∈ O) :
    N.index ∈ First.sampledIn N O :=
  List.mem_flatMap.2 ⟨.pinI, h, List.mem_singleton.2 rfl⟩

/-- **What is asked of the table's letters at K13's place.** -/
structure FillM3 {Pp W : Type} (Cl : Type) (P : Where) (N : Numbers) (Mg : Meaning Pp W) {nR : ℕ}
    (rw : Pp × S → W → Wit GE nR P.lin.kCol) (Q : List Pub) : Prop where
  /-- in the finish "every pending row holds" is no more than: all rows on the table are true -/
  pile : ∀ x y w f, x.2.here = .fin f → RowsTrue (rw x) x.2 w → Mg.pile x y w
  /-- behind a step "the one claim holds" is no less -/
  pileOne : ∀ x x' y w, StepM3 Cl P x x' → Mg.pileOne x' y w → RowsTrue (rw x') x'.2 w
  /-- what the rows behind a step say at the reader behind, they say at the reader in front -/
  reader : ∀ x x' w, StepM3 Cl P x x' → RowsTrue (rw x') x'.2 w → RowsTrue (rw x) x'.2 w
  /-- the public item behind the block is no more than the kind's own test -/
  frontOk : ∀ x, frontOkB P x.2 = true → Mg.pub .frontOk x = true
  /-- and it says nothing beside its Bool (by the table's own terms `pubP` is True at this item:
  payable, and idle) -/
  frontOkP : ∀ x, frontOkB P x.2 = true → Mg.pubP .frontOk x
  /-- over a step the two public items that are tied to the index masks' pin ride -/
  indexIs : ∀ x x', StepM3 Cl P x x' → Mg.pub .indexIs x = true → Mg.pub .indexIs x' = true
  indexThere : ∀ x x', StepM3 Cl P x x' → Mg.pub .indexThere x = true →
    Mg.pub .indexThere x' = true
  /-- and so does every public item that is open in front (Q) -/
  pubRide : ∀ x x' q, StepM3 Cl P x x' → q ∈ Q → Mg.pub q x = true → Mg.pub q x' = true
  pubPRide : ∀ x x' q, StepM3 Cl P x x' → q ∈ Q → Mg.pubP q x → Mg.pubP q x'
  /-- over a step the statement stays in order -/
  inOrder : ∀ x x', StepM3 Cl P x x' → Mg.inOrder x = true → Mg.inOrder x' = true
  /-- over a step the record still holds the index masks' sample -/
  held : ∀ x x', StepM3 Cl P x x' → Mg.held N.index.1 N.index.2 x = true →
    Mg.held N.index.1 N.index.2 x' = true
  /-- "every leaf is shown" reads the tenant's own tree alone -/
  shown : ∀ y y', OldKept N.index.1 y y' → Mg.shown N.index.1 N.index.2 y →
    Mg.shown N.index.1 N.index.2 y'
  /-- "no collision" rides over a step that leaves the tenant's tree -/
  noColl : ∀ x x' y y', StepM3 Cl P x x' → OldKept N.index.1 y y' →
    Mg.noColl N.index.1 N.index.2 x y → Mg.noColl N.index.1 N.index.2 x' y'
  /-- "the stored table decodes with the record" rides over a step -/
  decodes : ∀ x x' y y', StepM3 Cl P x x' → y'.cell = y.cell → Mg.decodes x y → Mg.decodes x' y'
  /-- the stored table's pin goes back over a step -/
  pinWBack : ∀ x x' y y' w, StepM3 Cl P x x' → y'.cell = y.cell → Mg.pinW x' y' w → Mg.pinW x y w
  /-- so does the index masks' -/
  pinIBack : ∀ x x' y y' w, StepM3 Cl P x x' → OldKept N.index.1 y y' →
    Mg.pin N.index.1 N.index.2 x' y' w → Mg.pin N.index.1 N.index.2 x y w
  /-- inside the promise (every public item that is open in front; the two that are tied to the
  index masks' pin; the book stands where the plan says of some place p; "in order") the two pins
  fix what the rows read: the matrix, and the mask entries of the message with the record's
  number. SEE THE HEAD: false at a reader by the book unless one of these sentences, or several
  together, give the index masks' seat -/
  det : ∀ x y p w w', (∀ q ∈ Q, Mg.pub q x = true) → Mg.pub .indexIs x = true →
    Mg.pub .indexThere x = true →
    First.bookAt N p x.2 = true → Mg.inOrder x = true → Mg.decodes x y →
    Mg.held N.index.1 N.index.2 x = true →
    Mg.shown N.index.1 N.index.2 y → Mg.noColl N.index.1 N.index.2 x y →
    Mg.pinW x y w → Mg.pinW x y w' → Mg.pin N.index.1 N.index.2 x y w →
    Mg.pin N.index.1 N.index.2 x y w' → AgreeAt x.2.out.indexMasks (rw x w) (rw x w')

section
variable {A Pp Cl W : Type} {C : PQ.CK} {Fr : Frame} {nR : ℕ}

/-- **The kind's relation at both borders, in the table's letters.** -/
def RelM3 (N : Numbers) (Mg : Meaning Pp W) (get : A → Pp × S) {k : ℕ}
    (rw : Pp × S → W → Wit GE nR k) (a : A × Fr.E.Str) (w : W) : Prop :=
  (Mg.pinW (get a.1) (strsOf Fr a.2) w ∧
    Mg.pin N.index.1 N.index.2 (get a.1) (strsOf Fr a.2) w) ∧
    RowsTrue (rw (get a.1)) (get a.1).2 w

/-- What the table's promise in front gives at a record without a mark. -/
theorem promise_front (N : Numbers) (Mg : Meaning Pp W) (links : List ModelPart) (ps : List Place)
    (get : A → Pp × S) (k : ℕ) (hi : N.index ∈ First.sampledIn N (openAt links ps k))
    (a : A × Fr.E.Str) (ha : onQ N Mg links ps get k a) (hm : (get a.1).2.failed = none) :
    Mg.decodes (get a.1) (strsOf Fr a.2) ∧ Mg.inOrder (get a.1) = true ∧
      Mg.held N.index.1 N.index.2 (get a.1) = true ∧
      Mg.shown N.index.1 N.index.2 (strsOf Fr a.2) ∧
      Mg.noColl N.index.1 N.index.2 (get a.1) (strsOf Fr a.2) := by
  obtain ⟨hd, hr⟩ := ha
  obtain ⟨hB, hS, hA, _⟩ := hr.resolve_left (fun h => h hm)
  simp only [Bool.and_eq_true] at hB
  exact ⟨hd, hB.1.1.2, List.all_eq_true.1 hS _ hi, hA _ hi⟩

/-- **And, since the index masks' pin is open there: the two public items that are tied to it; and
where the book stands.** -/
theorem promise_index (N : Numbers) (Mg : Meaning Pp W) (links : List ModelPart) (ps : List Place)
    (get : A → Pp × S) (k : ℕ) (hp : Item.pinI ∈ openAt links ps k)
    (a : A × Fr.E.Str) (ha : onQ N Mg links ps get k a) (hm : (get a.1).2.failed = none) :
    Mg.pub .indexIs (get a.1) = true ∧ Mg.pub .indexThere (get a.1) = true ∧
      First.bookAt N ps[k]? (get a.1).2 = true ∧
      ∀ q ∈ (First.pubSets Mg.more links ps)[k]?.getD [],
        Mg.pub q (get a.1) = true ∧ Mg.pubP q (get a.1) := by
  obtain ⟨_, hr⟩ := ha
  obtain ⟨hB, _, _, hPP⟩ := hr.resolve_left (fun h => h hm)
  simp only [Bool.and_eq_true] at hB
  have hall := List.all_eq_true.1 hB.1.2
  have hmem : ∀ q, q = Pub.indexIs ∨ q = Pub.indexThere →
      q ∈ First.pubOfItems (openAt links ps k) := fun q hq =>
    List.mem_flatMap.2 ⟨.pinI, hp, by rcases hq with rfl | rfl <;> simp⟩
  exact ⟨hall _ (List.mem_append_right _ (hmem _ (Or.inl rfl))),
    hall _ (List.mem_append_right _ (hmem _ (Or.inr rfl))), hB.2,
    fun q hq => ⟨hall _ (List.mem_append_left _ hq), hPP q hq⟩⟩

/-- **THE FIVE TIES AT K13's ROW**, of any piece whose yes is a step of the joined block, whose
extractor is the identity, and that has the kind's law at these words. -/
theorem k13_tied (N : Numbers) (Mg : Meaning Pp W) (links : List ModelPart) (ps : List Place)
    (get : A → Pp × S) (k : ℕ) (q : Piece C Fr A Cl W) (P : Where)
    (rw : Pp × S → W → Wit GE nR P.lin.kCol) (hT : RowM3 N Mg.more links ps k)
    (hF : FillM3 Cl P N Mg rw ((First.pubSets Mg.more links ps)[k]?.getD []))
    (hbase : N.index.1 < q.base) (hext : ∀ a τ w, q.ext a τ w = w)
    (hyes : ∀ a τ b, q.ior.red.out a τ = some b → StepM3 Cl P (get a.1) (get b.1))
    (hlaw : q.GoodIn (fun a => onQ N Mg links ps get k a ∧ (get a.1).2.failed = none)
      (fun b => FrontOk P (((get b.1).2, b.2) : S × Fr.E.Str)) (RelM3 N Mg get rw)
      (RelM3 N Mg get rw)) :
    TiedAt N Mg links ps get k q := by
  refine ⟨_, _, _, _, hlaw, fun a ha hm => ⟨ha, not_not.1 hm⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- t2
    intro a τ b ha hm hb ho'
    obtain ⟨hd, hin, hh, hs, hn⟩ :=
      promise_front N Mg links ps get k (idx_of_pin N hT.pinIn) a ha (not_not.1 hm)
    obtain ⟨hii, hit, hbk, hQ⟩ :=
      promise_index N Mg links ps get k hT.pinIn a ha (not_not.1 hm)
    have hst := hyes a τ b hb
    have hold := oldKept_out q hb hbase
    obtain ⟨rs, gs, hdec⟩ := hst.2
    have hfo := (frontOkB_iff P _ b.2).2 ho'
    refine ⟨hF.decodes _ _ _ _ hst hold.1 hd, Or.inr ⟨?_, ?_, ?_, ?_⟩⟩
    · simp only [Bool.and_eq_true]
      refine ⟨⟨⟨⟨⟨shape_behind hdec links _ hT.next, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
      · show First.rowsHeld N (openAt links ps (k + 1)) (get b.1).2 = true
        unfold First.rowsHeld
        rw [hT.noRows]
        rfl
      · show First.membersHeld N (openAt links ps (k + 1)) (get b.1).2 = true
        unfold First.membersHeld
        rw [hT.noRows]
        rfl
      · exact hF.inOrder _ _ hst hin
      · refine List.all_eq_true.2 fun x hx => ?_
        rcases List.mem_append.1 hx with hx | hx
        · rcases hT.pubs x hx with rfl | hx'
          · exact hF.frontOk _ hfo
          · exact hF.pubRide _ _ x hst hx' (hQ x hx').1
        · rcases hT.tied x hx with rfl | rfl
          · exact hF.indexIs _ _ hst hii
          · exact hF.indexThere _ _ hst hit
      · obtain ⟨e1, e2⟩ := atM3_book hdec
        unfold First.bookAt at hbk ⊢
        rw [e1, e2, hT.trees, hT.msgs]
        exact hbk
    · refine List.all_eq_true.2 fun t ht => ?_
      rw [hT.idxOnly t ht]
      exact hF.held _ _ hst hh
    · intro t ht
      rw [hT.idxOnly t ht]
      exact ⟨hF.shown _ _ hold hs, hF.noColl _ _ _ _ hst hold hn⟩
    · intro x hx
      rcases hT.pubs x hx with rfl | hx'
      · exact hF.frontOkP _ hfo
      · exact hF.pubPRide _ _ x hst hx' (hQ x hx').2
  · -- t3
    intro a τ b w _ _ hb _ hO
    exact ⟨⟨hO .pinW hT.outs.2.1, hO .pinI hT.outs.2.2⟩,
      hF.pileOne _ _ _ _ (hyes a τ b hb) (hO .pileOne hT.outs.1)⟩
  · -- t4
    intro a τ b w _ hm hb _ _ hR i hi
    rw [hext] at hR ⊢
    obtain ⟨rs, gs, hdec⟩ := (hyes a τ b hb).2
    obtain ⟨f, _, _, hfin, _⟩ := atM3_rec hdec
    rcases hT.ins i hi with rfl | rfl | rfl | rfl
    · exact hF.pile _ _ _ f hfin hR.2
    · exact hR.1.1
    · exact hR.1.2
    · exact not_not.1 hm
  · -- t5
    intro a τ b w i _ _ _ _ _ hi hin
    exact absurd (hT.noRider i hi) hin
  · -- a mark stays
    intro a τ b hb hm
    obtain ⟨rs, gs, hdec⟩ := (hyes a τ b hb).2
    rw [atM3_failed hdec]
    exact hm
  · -- "decodes" rides
    intro a τ b hb hd
    exact hF.decodes _ _ _ _ (hyes a τ b hb) (oldKept_out q hb hbase).1 hd

/-- A yes of the bare block's piece is a step, at any one public part. -/
theorem step_piece (F : Frame) (P : Where) (base : ℕ) (dZ d0 : RDT) (ds : List RDT) (z : Pp)
    (a : S × F.E.Str) (τ : Tr (uLT (ckP .two) (dZ :: d0 :: ds))) (b : S × F.E.Str)
    (hb : (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).ior.red.out a τ = some b) :
    StepM3 Cl P ((z, a.1) : Pp × S) (z, b.1) := by
  obtain ⟨rs, gs, hdec⟩ := piece_ok _ hb
  exact ⟨rfl, rs, gs, hdec⟩

/-- **The piece that holds c has the kind's law at the table's words**: by `atM3_goodInA`. z: the
public part. -/
theorem k13_law_seat (F : Frame) (P : Where) (base : ℕ) (dZ d0 : RDT) (ds : List RDT)
    (hD : Declared P dZ d0 ds) (c : Block S Cl) (hc : c.UnderR (atM3 P)) (z : Pp) (N : Numbers)
    (Mg : Meaning Pp W) (links : List ModelPart) (ps : List Place) (k : ℕ)
    (rw : Pp × S → W → Wit GE nR P.lin.kCol) (hp : Item.pinI ∈ openAt links ps k)
    (hF : FillM3 Cl P N Mg rw ((First.pubSets Mg.more links ps)[k]?.getD []))
    (hbase : N.index.1 < base) :
    ((pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).seat c).GoodIn
      (fun a => onQ N Mg links ps (fun s : S => (z, s)) k a ∧ a.1.failed = none)
      (fun b => FrontOk P b) (RelM3 N Mg (fun s : S => (z, s)) rw)
      (RelM3 N Mg (fun s : S => (z, s)) rw) := by
  intro a ha
  have h0 := atM3_goodInA (Cl := Cl) F P base dZ d0 ds hD P.lin.kCol hD.len.symm (rw (z, a.1))
    (fun a' w => Mg.pinW (z, a'.1) (strsOf F a'.2) w ∧
      Mg.pin N.index.1 N.index.2 (z, a'.1) (strsOf F a'.2) w)
    (fun a' => a' = a)
    (fun a' w w' e h h' => by
      subst e
      obtain ⟨hd, hin, hh, hs, hn⟩ :=
        promise_front N Mg links ps (fun s : S => (z, s)) k (idx_of_pin N hp) a' ha.1 ha.2
      obtain ⟨hii, hit, hbk, hQ⟩ :=
        promise_index N Mg links ps (fun s : S => (z, s)) k hp a' ha.1 ha.2
      exact hF.det _ _ _ w w' (fun q hq => (hQ q hq).1) hii hit hbk hin hd hh hs hn h.1 h'.1 h.2
        h'.2)
    (fun a' τ b w hb hw =>
      ⟨hF.pinWBack _ _ _ _ w (step_piece F P base dZ d0 ds z a' τ b hb)
          (oldKept_out _ hb hbase).1 hw.1,
        hF.pinIBack _ _ _ _ w (step_piece F P base dZ d0 ds z a' τ b hb)
          (oldKept_out _ hb hbase) hw.2⟩) a rfl
  refine Doomed.mono _ _ ?_ h0
  intro τ hτ b hb
  have hb' := out_seat (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds) c hc a b τ hb
  obtain ⟨ho, hk⟩ := hτ b hb'
  exact ⟨ho, fun w hw =>
    hk w ⟨hw.1, hF.reader _ _ w (step_piece F P base dZ d0 ds z a τ b hb') hw.2⟩⟩

/-- **THE FIVE TIES AT THE PIECE THAT HOLDS c**, where the chain's record is the carried record
itself and the public part is one value z. -/
theorem k13_tied_seat (F : Frame) (P : Where) (base : ℕ) (dZ d0 : RDT) (ds : List RDT)
    (hD : Declared P dZ d0 ds) (c : Block S Cl) (hc : c.UnderR (atM3 P)) (z : Pp) (N : Numbers)
    (Mg : Meaning Pp W) (links : List ModelPart) (ps : List Place) (k : ℕ)
    (rw : Pp × S → W → Wit GE nR P.lin.kCol) (hT : RowM3 N Mg.more links ps k)
    (hF : FillM3 Cl P N Mg rw ((First.pubSets Mg.more links ps)[k]?.getD []))
    (hbase : N.index.1 < base) :
    TiedAt N Mg links ps (fun s : S => (z, s)) k
      ((pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).seat c) :=
  k13_tied N Mg links ps _ k _ P rw hT hF hbase (fun _ _ _ => rfl)
    (fun a τ b hb => step_piece F P base dZ d0 ds z a τ b
      (out_seat (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds) c hc a b τ hb))
    (k13_law_seat F P base dZ d0 ds hD c hc z N Mg links ps k rw hT.pinIn hF hbase)

/-- **THE SAME, LIFTED**: the carried record is a part of the chain's record (gt, st: what was laid
is got; what is laid last stays); pub: the table's public part, which laying the part leaves. -/
theorem k13_tied_lift (F : Frame) (P : Where) (base : ℕ) (dZ d0 : RDT) (ds : List RDT)
    (hD : Declared P dZ d0 ds) (c : Block S Cl) (hc : c.UnderR (atM3 P)) (gt : A → S)
    (st : A → S → A) (h1 : ∀ t s, gt (st t s) = s) (h2 : ∀ t s s', st (st t s) s' = st t s')
    (pub : A → Pp) (hpub : ∀ t s, pub (st t s) = pub t) (N : Numbers) (Mg : Meaning Pp W)
    (links : List ModelPart) (ps : List Place) (k : ℕ) (rw : Pp × S → W → Wit GE nR P.lin.kCol)
    (hT : RowM3 N Mg.more links ps k)
    (hF : FillM3 Cl P N Mg rw ((First.pubSets Mg.more links ps)[k]?.getD []))
    (hbase : N.index.1 < base) :
    TiedAt N Mg links ps (fun a : A => (pub a, gt a)) k
      (((pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).seat c).lift gt st) := by
  have hout := liftOut A S Cl W (ckP .two) F gt st
    ((pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).seat c) h1 h2
  refine k13_tied N Mg links ps _ k _ P rw hT hF hbase (fun _ _ _ => rfl) ?_ ?_
  · intro a τ b hb
    rw [hout a τ] at hb
    obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 hb
    obtain ⟨_, rs, gs, hdec⟩ := step_piece F P base dZ d0 ds (pub a.1) _ τ b₀
      (out_seat (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds) c hc _ b₀ τ hb₀)
    refine ⟨hpub _ _, rs, gs, ?_⟩
    show (atM3 (Cl := Cl) P).decide (gt a.1) rs gs = .ok (gt (st a.1 b₀.1))
    rw [h1]
    exact hdec
  · intro a ha
    refine Doomed.mono _ _ ?_ (k13_law_seat F P base dZ d0 ds hD c hc (pub a.1) N Mg links ps k
      rw hT.pinIn hF hbase (gt a.1, a.2) ha)
    intro τ hτ b hb
    rw [hout a τ] at hb
    obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 hb
    obtain ⟨ho, hk⟩ := hτ b₀ hb₀
    refine ⟨?_, fun w hw => hk w ?_⟩
    · show FrontOk P ((gt (st a.1 b₀.1), b₀.2) : S × F.E.Str)
      rw [h1]
      exact ho
    · have hw' : (Mg.pinW (pub (st a.1 b₀.1), gt (st a.1 b₀.1)) (strsOf F b₀.2) w ∧
          Mg.pin N.index.1 N.index.2 (pub (st a.1 b₀.1), gt (st a.1 b₀.1)) (strsOf F b₀.2) w) ∧
          RowsTrue (rw (pub (st a.1 b₀.1), gt (st a.1 b₀.1))) (gt (st a.1 b₀.1)) w := hw
      rw [hpub, h1] at hw'
      exact hw'

end

end VerifiableInference.Desc.K13.Law
