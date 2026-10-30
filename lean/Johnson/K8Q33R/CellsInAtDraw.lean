-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/K8Q33R/CellsInAtDraw.lean: THE SMALLNESS TEST AT THE TABLE OF JOINTS: A PAYMENT BENEATH THE
KIND's FROZEN CONDITION: THE SECOND HALF OF THE FIELD "alike" OF K8LeftT
(Johnson/P1K8R/TightAt.lean:126-134): "THE CELLS THAT THE TIE READS ARE THE COMMITTED MESSAGES'":
CellsIn AT EVERY REACHED STATE IN FRONT OF K8's DRAW, AT ALL 25 LINKS, FROM THE FACTS ALONG
"REACHED" (FoldFacts), THE PROMISE's TEST ON THE BOOK, AND CLOSED SENTENCES ON PUBLIC DATA. NO
SOUNDNESS.

Statements and proofs.
Main names:
  CellsPlan d ms own rad m t n: THE CLOSED SENTENCES, on public data alone: five: lengths, layoutOk,
    shapes, members: the clauses of these names of PlanFits
    (Johnson/Desc/First/Link/Law/PartFitsReached.lean), to the letter · radded: every member of ms
    bears the radius that rad gives its shape.
  cellsPlan_of_fits: PlanFits (at any number of slots) and radded give CellsPlan. raddedB,
    radded_of_B: radded as a test with code, and its tie. cellsPlanB, cellsPlan_of_B: the five as
    one test with code (PlanFitsB.lean's own shapesB and membersB among them), and its tie.
  named_at: a message of Named.msgs that the statement and the book have has a place in
    Named.listOf, with its shape, rad of its shape, and its seat. place_at: the same at lA | sA
    (Johnson/P1K8R/OwesAt.lean).
  **cellsIn_of_fold**: AT ONE REACHED STATE without a mark, at a place of segment l up to its piece
    11 (+ 2 at the head), with the open link L: FoldFacts, the promise's test on the book and
    CellsPlan give CellsIn d.sent.codes (lA rad s tl L) (sA rad s tl L) ms N l s t o at every array
    t of Named.arrays tl whose message has the number o.
  **cellsIn_at_draw**: the field's second half, to the letter, at the closed letters of the full
    size. How. The seat q that CellsIn hands over is the book's at o (seatAt's text); so o is below
    the book's size, which is the statement's (the promise's test on the book); the statement's
    shape at o is the plan's list's (msgShape_at under FoldFacts.msgShapes); the book's seat at o is
    the plan's list's (FoldFacts.seatsCarried); so the member y that find? returns has that shape
    (members) and rad of it (radded): it is alike the place that named_at gives. The blocks: by
    Second.K08.blockInMsg_at_member, whose premise on the shape comes from shapes at
    whereIs_reached's term. WHAT PARTS FROM THE STATEMENT AS ASKED: three premises less: hG, e3 and
    hRch are not spent (nor G, Xl).
Limits. CellsPlan is shown nowhere here; it reads no state. FoldFacts is a premise. Nothing on
soundness or on hiding. CellsIn asks nothing where the book has no seat of the link's group for the
message, or where no member of ms sits at that seat. This file does not shut these two cases
(seatsOwn_of_onQ, Johnson/Desc/First/K8/SeatsOwnPromise.lean, and GroupsSeated,
Johnson/Desc/Sound/ReadAt.lean, are meant for them): so "the cells that the tie reads are the
committed messages'" is said only where a member sits. L₀ is a free letter of cellsIn_at_draw:
CellsPlan speaks of public data alone only at L₀ := the value of At.laid? Zp, and whoever joins the
theorem has to take FoldFacts and CellsPlan at that same L₀. h is named in the statement and not
spent. cellsPlan_of_B goes one way, from the test to the sentences, and the test's yes can stand on
nothing (ms empty; a shape without links; a seat outside own). Where P5T.rowsAt? returns nothing,
every radius in At.ms and in At.rad3At is 0, and raddedB says yes on 0 = 0. Two of CellsPlan's
clauses (lengths, layoutOk) could be had by theorem from the public part's own tests; here they are
premises. verify() asks CellsPlan nowhere: it is a named condition here.
cellsIn_at_draw stands at OnBytes.secondHashFunction and at the full size's letters alone.

-/
import Johnson.P1K8R.SmallAtHead
import Johnson.Desc.First.K8.LawEarly
import Johnson.Second.K08.BlocksInMsg
import Johnson.Desc.First.Link.Law.PlanFitsB

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace K8Q33

open Iop
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj Johnson.Pack
open OnBytes.Tie.Pv.Tail (early)
open VerifiableInference.Desc (Chain Place Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Numbers Meaning FoldData FoldFacts momentAt shiftAt
  bookAt flatPlacesOf)
open VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.LinkJoin (whereD whereIs_reached PlanFits live_link shapesB membersB)
open VerifiableInference.Desc.K9 (seatAt)
open ProofFile (Cl)
open P5J (AtMgA mgAtAll)
open P1K8T (lA sA bookAt_of_onQ draw_place_full)

/-! ## 1 The closed sentences -/

/-- **THE CLOSED SENTENCES ON THE PLAN**: in segment m with t moments sent and n oracle messages
sent. -/
structure CellsPlan (d : FoldData) (ms : List Mem) (own : List (ℕ × ℕ)) (rad : OracleShape → ℕ)
    (m t n : ℕ) : Prop where
  lengths : d.sent.codes.lengthsOk = true
  layoutOk : reqLayoutOk d.sent.codes d.sent.shape d.sent.layout = true
  shapes : ∀ born j o msg, whereD d m t born j = some o →
    _root_.Meaning.messageAt d.sent.shape born j = some msg → o < n ∧ d.M[o]? = some msg.shape
  members : ∀ o x y sh, o < n → d.M[o]? = some sh → d.L.places[o]? = some x → x ∈ own →
    (ms.find? fun y => decide (seatOf y = x)) = some y → (y.1.l.get y.2).1 = sh
  radded : ∀ y ∈ ms, (y.1.l.get y.2).2 = rad (y.1.l.get y.2).1

/-- From PlanFits (Johnson/Desc/First/Link/Law/PartFitsReached.lean), at any number of slots. -/
theorem cellsPlan_of_fits {d : FoldData} {ms : List Mem} {own : List (ℕ × ℕ)}
    {rad : OracleShape → ℕ} {m t n ns : ℕ} (F : PlanFits d ms own m t n ns)
    (hr : ∀ y ∈ ms, (y.1.l.get y.2).2 = rad (y.1.l.get y.2).1) : CellsPlan d ms own rad m t n :=
  ⟨F.lengths, F.layoutOk, F.shapes, F.members, hr⟩

/-- "radded" as a test with code. -/
def raddedB (ms : List Mem) (rad : OracleShape → ℕ) : Bool :=
  ms.all fun y => (y.1.l.get y.2).2 == rad (y.1.l.get y.2).1

theorem radded_of_B {ms : List Mem} {rad : OracleShape → ℕ} (h : raddedB ms rad = true) :
    ∀ y ∈ ms, (y.1.l.get y.2).2 = rad (y.1.l.get y.2).1 := fun y hy =>
  eq_of_beq (List.all_eq_true.1 h y hy)

/-- The five closed sentences as one test with code: PlanFits' own tests for its four
(`shapesB`, `membersB`: Johnson/Desc/First/Link/Law/PlanFitsB.lean), and `raddedB`. PlanFits' three
further clauses (the mask's message, the answers, the ledger's room) are not asked. -/
def cellsPlanB (d : FoldData) (ms : List Mem) (own : List (ℕ × ℕ)) (rad : OracleShape → ℕ)
    (m t n : ℕ) : Bool :=
  d.sent.codes.lengthsOk && reqLayoutOk d.sent.codes d.sent.shape d.sent.layout &&
    shapesB d m t n && membersB d ms own n && raddedB ms rad

/-- **ITS YES GIVES CellsPlan.** (The two middle steps are `planFits_of_B`'s own.) -/
theorem cellsPlan_of_B {d : FoldData} {ms : List Mem} {own : List (ℕ × ℕ)} {rad : OracleShape → ℕ}
    {m t n : ℕ} (h : cellsPlanB d ms own rad m t n = true) : CellsPlan d ms own rad m t n := by
  unfold cellsPlanB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, ?_, ?_, radded_of_B h5⟩
  · intro born j o msg hw hm
    obtain ⟨L, hL, hj⟩ := Option.bind_eq_some_iff.1 hm
    have a1 := List.all_eq_true.1 h3 (L, born) (List.mem_zipIdx_iff_getElem?.2 hL)
    have a2 := List.all_eq_true.1 a1 (msg, j) (List.mem_zipIdx_iff_getElem?.2 hj)
    simp only [hw, Bool.and_eq_true, decide_eq_true_eq] at a2
    exact a2
  · intro o x y sh ho hM hP hx hy
    have a1 := List.all_eq_true.1 h4 o (List.mem_range.2 ho)
    simp only [hM, hP, hy, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at a1
    rcases a1 with a1 | a1
    · have : own.contains x = true := by simpa using hx
      rw [this] at a1
      cases a1
    · exact a1

/-! ## 2 The place in the state's list -/

/-- A message of the list of messages that the statement and the book have has a place in the list
of members. -/
theorem named_at (rad : OracleShape → ℕ) (St : Statement) (book : TreeBook) (tl : HTailF2)
    (L : LinkCtx) {o : ℕ} {X : Oracle} {q : ℕ × ℕ} (ho : o ∈ Named.msgs tl L)
    (hX : St.oracles[o]? = some X) (hq : book.place[o]? = some q) :
    ∃ i : Fin (Named.listOf rad St book tl L).length,
      (Named.listOf rad St book tl L).get i = (X.shape, rad X.shape) ∧
        Named.seatFn rad St book tl L i = q := by
  have hm : (o, (X.shape, q)) ∈ Named.members St book tl L := by
    unfold Named.members
    refine List.mem_filterMap.2 ⟨o, ho, ?_⟩
    unfold Named.memberAt
    rw [hX, hq]
    rfl
  obtain ⟨j, hj, e⟩ := List.getElem_of_mem hm
  have hl : j < (Named.listOf rad St book tl L).length := by
    unfold Named.listOf
    rw [List.length_map]
    exact hj
  refine ⟨⟨j, hl⟩, ?_, ?_⟩
  · show (Named.listOf rad St book tl L)[j] = _
    unfold Named.listOf
    rw [List.getElem_map, e]
  · unfold Named.seatFn
    show (Named.seatsOf St book tl L)[j]'_ = _
    unfold Named.seatsOf
    rw [List.getElem_map, e]

unseal lA sA in
/-- The same at the law's two letters. -/
theorem place_at (rad : OracleShape → ℕ) (s : S) (tl : HTailF2) (L : LinkCtx) {o : ℕ} {X : Oracle}
    {q : ℕ × ℕ} (ho : o ∈ Named.msgs tl L) (hX : s.st.oracles[o]? = some X)
    (hq : s.book.place[o]? = some q) :
    ∃ i : Fin (lA rad s tl L).length,
      (lA rad s tl L).get i = (X.shape, rad X.shape) ∧ sA rad s tl L i = q :=
  named_at rad s.st s.book tl L ho hX hq

/-! ## 3 At one reached state -/

/-- **CellsIn AT ONE REACHED STATE, OUT OF THE FACTS ALONG "REACHED".** -/
theorem cellsIn_of_fold {X P : Type} {Rch : ℕ → X → Prop} {at_ : X → P × S} {d : FoldData}
    {reqW : P → Array UInt32} {links : List ModelPart} {ps : List Place}
    (FF : FoldFacts Rch at_ d reqW links ps) (N : Numbers) (ms : List Mem) (rad : OracleShape → ℕ)
    {k : ℕ} {a : X} {p : Place} {l : ℕ} {L : LinkCtx} (tl : HTailF2) (hR : Rch k a)
    (hu : (at_ a).2.failed = none) (hp : ps[k]? = some p) (hlk : p.link = some l)
    (hpc : p.piece ≤ 11 + 2 * shiftAt links l) (hL : (at_ a).2.link? = some L)
    (hB : bookAt N ps[k]? (at_ a).2 = true)
    (T : CellsPlan d ms (N.group l) rad l (momentAt (shiftAt links l) p.piece) (N.msgsAt ps[k]?))
    {t o : ℕ} (ht : t ∈ Named.arrays tl) (ho : Named.msgNow L t = some o) :
    CellsIn d.sent.codes (lA rad (at_ a).2 tl L) (sA rad (at_ a).2 tl L) ms N l (at_ a).2 t o := by
  intro L' x ar q y hL' hx ha hq hy
  obtain rfl : L = L' := Option.some.inj (hL.symm.trans hL')
  obtain ⟨x', a', hx', ha', hwi⟩ := array_of_msgNow ho
  obtain rfl : x = x' := Option.some.inj (hx.symm.trans hx')
  obtain rfl : ar = a' := Option.some.inj (ha.symm.trans ha')
  -- the promise's test on the book
  unfold bookAt at hB
  simp only [Bool.and_eq_true, beq_iff_eq] at hB
  obtain ⟨⟨-, hb2⟩, hb3⟩ := hB
  -- the seat is the book's, and of the segment's group
  have hqo : q ∈ N.group l := VerifiableInference.Desc.K9.seatAt_mem _ _ _ _ hq
  have hpl0 : (at_ a).2.book.place[o]? = some q := by
    unfold seatAt at hq
    obtain ⟨z, hz, hz2⟩ := Option.bind_eq_some_iff.1 hq
    split at hz2
    · rw [hz, Option.some.inj hz2]
    · exact nomatch hz2
  have hoP : o < (at_ a).2.book.place.size := (Array.getElem?_eq_some_iff.1 hpl0).1
  have hoS : o < (at_ a).2.st.oracles.size := by rw [← hb2]; exact hoP
  have hon : o < N.msgsAt ps[k]? := by rw [← hb3]; exact hoS
  -- the statement's shape at o is the plan's
  have hX : (at_ a).2.st.oracles[o]? = some (at_ a).2.st.oracles[o] := Array.getElem?_eq_getElem hoS
  have hM : d.M[o]? = some ((at_ a).2.st.oracles[o]).shape := by
    rw [← VerifiableInference.Desc.K12.Door.msgShape_at (FF.msgShapes k a hR hu) o hoS, hX]
    rfl
  -- the book's seat at o is the plan's
  have hpl : d.L.places[o]? = some q := by
    have hS := FF.seatsCarried k a hR hu
    unfold VerifiableInference.Desc.K12.Door.atFirstSeats
      VerifiableInference.Desc.K12.Door.seatsCarriedB at hS
    simp only [Bool.and_eq_true, beq_iff_eq] at hS
    have e0 : (at_ a).2.book.place.toList = d.L.places.take (at_ a).2.book.place.size := hS.1.1.1
    have h3 := hpl0
    rw [← Array.getElem?_toList, e0, List.getElem?_take_of_lt hoP] at h3
    exact h3
  -- the member
  have hys : (y.1.l.get y.2).1 = ((at_ a).2.st.oracles[o]).shape :=
    T.members o q y _ hon hM hpl hqo hy
  have hyr := T.radded y (List.mem_of_find?_eq_some hy)
  have hseat : seatOf y = q := by
    have h5 := List.find?_some hy
    exact of_decide_eq_true h5
  obtain ⟨i, hi1, hi2⟩ := place_at rad (at_ a).2 tl L (Named.mem_msgs.2 ⟨t, ht, ho⟩) hX hpl0
  have hw : whereD d l (momentAt (shiftAt links l) p.piece) x.1 ar.message = some o :=
    (whereIs_reached FF hR hu hp hlk hpc hL x.1 ar.message).symm.trans hwi
  have hlay : OnBytes.reqArray d.sent.layout x.1 x.2 = some ar := by
    rw [← FF.liveLayout k a hR hu, live_link hL]
    exact ha
  refine ⟨i, ⟨?_, ?_⟩, ?_⟩
  · show y.1.l.get y.2 = (lA rad (at_ a).2 tl L).get i
    rw [hi1]
    exact Prod.ext hys (by rw [hyr, hys])
  · show y.1.seat y.2 = sA rad (at_ a).2 tl L i
    rw [hi2]
    exact hseat
  · rw [hi1]
    exact Second.K08.blockInMsg_at_member d.sent.codes _ (at_ a).2.st d.sent.shape d.sent.layout
      (FF.codes k a hR hu) T.lengths T.layoutOk x.1 x.2 ar hlay o _ hX rfl
      (fun Lk msg h1 h2 => by
        have hm : _root_.Meaning.messageAt d.sent.shape x.1 ar.message = some msg := by
          unfold _root_.Meaning.messageAt
          rw [h1]
          exact h2
        have h4 := (T.shapes x.1 ar.message o msg hw hm).2
        rw [hM] at h4
        exact Option.some.inj h4)

/-! ## 4 At the draw, at the closed letters of the full size -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **THE SECOND HALF OF THE FIELD "alike" OF K8LeftT, TO THE LETTER, FROM FoldFacts AND CLOSED
SENTENCES.** -/
theorem cellsIn_at_draw (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {Fr : Frame} {l : ℕ}
    (hl : l ≤ 24) {Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop}
    {L₀ : VerifiableInference.Desc.K12.Door.Laid}
    (FF : FoldFacts Rch (fun a => a.1) (P5J.At.foldD Zp cF L₀) P5J.At.reqW P5J.At.links P5J.At.ps)
    (T : CellsPlan (P5J.At.foldD Zp cF L₀) (P5J.At.ms Zp Z.lay) ((P5J.At.N Zp cF).group l)
      (P5J.At.rad3At Zp Z.lay) l 2
      ((P5J.At.N Zp cF).msgsAt (flatPlacesOf linksFull true)[drawAt l]?)) :
    ∀ (z : ProofFile.InstPub) (a : S × Fr.E.Str) (tl : HTailF2) (L : LinkCtx),
      onQ (P5J.At.N Zp cF) (mgAtAll h) linksFull (flatPlacesOf linksFull true)
        (fun s => (z, s)) (drawAt l) a →
      Rch (drawAt l) ((z, a.1), a.2) →
      a.1.failed = none → a.1.tl? = some tl → a.1.link? = some L →
      ∀ t r c o, early tl (.cell t r c) = true → Named.msgNow L t = some o →
        CellsIn (P5J.At.cs Zp) (lA (P5J.At.rad3At Zp Z.lay) a.1 tl L)
          (sA (P5J.At.rad3At Zp Z.lay) a.1 tl L) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) l a.1 t
          o := by
  intro z a tl L ha hr hm _ hL t r c o he ho
  obtain ⟨p, hp, hlk, hpc, hmo⟩ := draw_place_full l hl
  have hB := bookAt_of_onQ (P5J.At.N Zp cF) (mgAtAll h) linksFull (flatPlacesOf linksFull true)
    (fun s => (z, s)) (drawAt l) a ha hm
  rw [← hmo] at T
  exact cellsIn_of_fold FF (P5J.At.N Zp cF) (P5J.At.ms Zp Z.lay) (P5J.At.rad3At Zp Z.lay)
    (k := drawAt l) (a := ((z, a.1), a.2)) (p := p) (l := l) tl hr hm hp hlk hpc hL hB T
    ((early_iff_named tl t r c).1 he) ho

end

end K8Q33

#print axioms K8Q33.cellsPlan_of_fits
#print axioms K8Q33.radded_of_B
#print axioms K8Q33.cellsPlan_of_B
#print axioms K8Q33.named_at
#print axioms K8Q33.place_at
#print axioms K8Q33.cellsIn_of_fold
#print axioms K8Q33.cellsIn_at_draw
