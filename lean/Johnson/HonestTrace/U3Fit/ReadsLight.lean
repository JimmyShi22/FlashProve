-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HonestTrace/U3Fit/ReadsLight.lean

Under the head and the opening (the terms: Johnson/HonestTrace/U3Fit/SeatsAtHead.lean and
Johnson/HonestTrace/U3Fit/SortedAtHead.lean), "ReadsLight Zp Bs.G₀ ξ"
(Johnson/Desc/ProofFile/Honest/K2/Law/LightDebts.lean) follows from one premise: that "valsAt"
(Johnson/HonestTrace/U3Rows.lean) returns at each of the 25 segments, at the instance's covered
positions. Definitions and theorems. Public data alone. In no statement, and in no line of this
file's own text, is a SegVals opened or its field vec applied; five proofs unfold a sealed maker or
u3Vals, in whose body vec stands, and read of it the field n or size alone. Of "u3Vals" this file
reads the field "size" alone; "u3Rows" and "u3RowsOf" are handed whole to the light test, which asks
their field "lays" alone.

How. The light test "arraysLaidLight" (Johnson/Desc/ProofFile/Honest/K2/Law/LaidLight.lean) asks of
each array of a message that the datum lay an element at the first place of some laid block of it.
At a reads' message each array bears the name "U3", and a block of it begins at the array's element
(0, 0). "laidData" (Johnson/Desc/ProofFile/Honest/LaidData.lean) lays there where the values' size
is (1, n) with 0 < n, and "fitsSeg" refuses n = 0.

Where the texts come from. The body of "firstLaid" is the body of "arraysLaidLight", clause for
clause: its clause on the datum is gone, "msgFits" stands in front, and the name "U3" and the
element (0, 0) are asked besides. The walk of "readsBy" is the walk of "lightAt"
(Johnson/Desc/ProofFile/Honest/K2/Law/LightByAddress.lean), set under the places and the cut "take
p.link" of "ReadsLight"; "sortedBy" (Johnson/HonestTrace/U3Fit/SortedAtHead.lean) has it too. The
head and the opening are bound in the letters in which
Johnson/Desc/ProofFile/Honest/K2/Law/LightAtHead.lean binds them. The likeness is meant: the proof
of "light_of_first" unfolds "firstLaid" and "arraysLaidLight", that of "readsLight_of_vals" the two
walks.

Main definitions: "firstLaid": a test of closed letters at a segment's message: "msgFits" passes,
and each array of the message has a laid block, inside the rows and the length handed in, at whose
first place the layout's way back finds an array of the same name, which is "U3", at its element
(0, 0). "readsOne", "readsBy": "sortedOne" and "sortedBy" with "firstLaid", and l < 25, in the place
of the clause on the layout.

Main theorems:
* "readsBy_at_head": under the head and the opening the test says yes at the kind's own terms.
* "size_of_vals" (no head): where "valsAt" returns V at a segment of the shape, the values' size
  under "U3" is (1, V.n). "n_ne_zero" (no head): what "valsAt" returns has n ≠ 0.
* "light_of_first" (no head): from a seat's pair, the size (1, n) with n ≠ 0 and "firstLaid": the
  light test at "u3Rows".
* "readsLight_of_vals": the end. The covered positions are named through "covOf", as "u3RowsOf"
  names them: the default where "covOf" rejects.
Helpers: "lookup_graph", "bind_ok", "fitsSeg_n"; "layersVals_n", "attVals_n", "headVals_n": what the
maker of that name returns has n ≠ 0.

Limits. Head and opening are premises: the full size and the format's second hash function alone. Two closed
facts, "readsW" and "readsW_can_fail", are shown by "decide +kernel", each under "set_option
maxRecDepth 1000000", which raises the elaborator's depth of recursion. The second holds three
controls: one takes the seats of "U3" away, one lets arrays of another name fall to the fourth
clause, one makes "msgFits" fail. Bent by no control: both bounds at a block's first row and place;
that the array found has the name of the array asked for; the element (0, 0); the bound 25 on l;
clauses one and two of "readsOne". Two small facts are evaluated by plain "decide" inside proofs:
the written shape's 25 links, and that "U3" is "U3". That "readsBy" walks as "lightAt" walks stands
by the two texts, and by the proof of "readsLight_of_vals". The light test goes one way, as its own
file says: a no of it would mean nothing. Where the layout lays no array into a message, "firstLaid"
is "msgFits" alone and the light test says yes: that a reads' message has an array is shown in
Johnson/HonestTrace/U3Fit/SortedAtHead.lean, not here. Where "covOf" rejects and the plan has a
position, "headVals" refuses the default, so the premise fails at segment 24 and the end says
nothing; Johnson/HonestTrace/U3Fit/ReadsDebt.lean asks "okStart" for that.
Not claimed: that "valsAt" returns: it is the premise here. Anything on "ready" or on values. No
property of a release, of a verifier or of a prover is claimed.
-/
import Johnson.HonestTrace.U3Fit.SortedAtHead
import Johnson.HonestTrace.U3Fit.ValsGeneral
import Johnson.Desc.ProofFile.Honest.K2.Law.LightDebts

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace.U3.Fit

open OnBytes OnBytes.Model
open ProofFile (Pub Ground)
open ProofFile.Honest (Addr MsgAddr msgFits laidBack)
open ProofFile.Honest.K2 (SwitchPlace SegmentPub switchPlaces segmentsOf switchSeat ownSeats
  arraysLaidLight lightAt mineReads mineSwitch)
open ProofFile.Honest.K2.Law (placesW segsW places_at_head segments_at_head ReadsLight)
open OnBytes.Params (ReqLayout ReqShape)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.PlanWritten (proofSizedFull)
open Johnson.G (codesFull2 layoutFull)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

/-! ## 1 The closed half -/

/-- **A TEST at message m of segment l**: "msgFits"; and each array of the message has a laid block,
inside the two bounds, at whose first place the way back finds an array of the same name, "U3", at
(0, 0). The body is that of "arraysLaidLight" (Johnson/Desc/ProofFile/Honest/K2/Law/LaidLight.lean)
without the clause on the datum. cG: the ground's codes; codes, s: the codes and the shape that the
light test is handed. -/
def firstLaid (cG : OnBytes.Codes) (shape : ReqShape) (lay : ReqLayout) (codes : OnBytes.Codes)
    (s : OnBytes.OracleShape) (l m : Nat) : Bool :=
  msgFits cG shape lay l m &&
    ((lay.link.getD l []).filter fun A => A.message == m).all fun A =>
      A.blocks.any fun b =>
        decide (b.firstRow < s.mainRows) &&
          decide (b.firstPlace < (codes.base.getD s.code default).ell) &&
          (laidBack lay l m b.firstRow b.firstPlace).any fun x =>
            x.1.name == A.name && x.1.name == "U3" && x.2.1 == 0 && x.2.2 == 0

/-- At one address a of the own message number m, of shape s, of segment l. -/
def readsOne (own : List (Addr × Nat × Nat)) (cG : OnBytes.Codes) (shape : ReqShape)
    (lay : ReqLayout) (u3 bz : List Seat) (codes : OnBytes.Codes) (s : OnBytes.OracleShape)
    (l m : Nat) (a : MsgAddr) : Bool :=
  (ProofFile.Honest.K2.seatBy shape own a).isSome || a.sender == ProofFile.Honest.K1.firstAddr ||
    mineOf bz a ||
    (pairOf u3 a == some (l, m) && decide (l < 25) && firstLaid cG shape lay codes s l m)

/-- **THE TEST**: at each place it walks as "lightAt"
(Johnson/Desc/ProofFile/Honest/K2/Law/LightByAddress.lean) walks. -/
def readsBy (own : List (Addr × Nat × Nat)) (places : List SwitchPlace) (segs : List SegmentPub)
    (cG : OnBytes.Codes) (shape : ReqShape) (lay : ReqLayout) (u3 bz : List Seat) : Bool :=
  places.all fun p =>
    (segs.take p.link).zipIdx.all fun y =>
      (y.1.ownShapes (y.2 == 0)).zipIdx.all fun s =>
        (p.addrs y.2 s.2).all (readsOne own cG shape lay u3 bz y.1.sizes.codes s.1 y.2 s.2)

set_option maxRecDepth 1000000 in
/-- The test says yes at the written values. -/
theorem readsW : readsBy ownW placesW segsW codesFull2 proofSizedFull.request layoutFull
    (seatsW "U3") (seatsW "BZ") = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Controls: without the seats of "U3" · with the seats of "BZ" laid behind those of "U3" and none
handed in for "BZ" (the digits' arrays are not "U3") · at a ground's codes without a code
("msgFits" fails; the bound of "firstLaid" takes its length of the segments' codes,
which stay): the test says no. -/
theorem readsW_can_fail :
    (readsBy ownW placesW segsW codesFull2 proofSizedFull.request layoutFull [] (seatsW "BZ") ||
      readsBy ownW placesW segsW codesFull2 proofSizedFull.request layoutFull
        (seatsW "U3" ++ seatsW "BZ") [] ||
      readsBy ownW placesW segsW {} proofSizedFull.request layoutFull (seatsW "U3")
        (seatsW "BZ")) = false := by decide +kernel

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}
  {base : List (Block S ProofFile.Cl)}

/-- Under the head and the opening the test says yes at the kind's own terms. -/
theorem readsBy_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    readsBy (ownSeats Zp Bs.G₀) (switchPlaces Zp Bs.G₀) (segmentsOf Zp Bs.G₀) Bs.G₀.first.codes
      Bs.G₀.first.shape Bs.G₀.first.layout (seatsOf Zp Bs.G₀ "U3") (seatsOf Zp Bs.G₀ "BZ") =
      true := by
  obtain ⟨e1, e2, e3⟩ := first_at_head h O.blank
  unfold ownSeats
  rw [places_at_head h.toAtMg O, segments_at_head h.toAtMg O, e1, e2, e3,
    seats_at_head h O.blank, seats_at_head h O.blank]
  exact readsW

/-! ## 2 The general half -/

/-- A helper: a look-up in the graph of a function over a list that holds the key. -/
theorem lookup_graph {β : Type} (f : Nat → β) (L : List Nat) (k : Nat) (hk : k ∈ L) :
    (L.map fun l => (l, f l)).lookup k = some (f k) := by
  induction L with
  | nil => cases hk
  | cons a L ih =>
    rw [List.map_cons, List.lookup_cons]
    by_cases e : k = a
    · subst e
      rw [beq_self_eq_true]
    · have e' : (k == a) = false := by simpa using e
      rw [e']
      exact ih (by
        cases hk with
        | head => exact absurd rfl e
        | tail _ t => exact t)

/-- **GENERAL: where the maker returns V at a segment of the shape, the values' size under "U3" is
(1, V.n).** -/
theorem size_of_vals {Z : Pub} {G : Ground} {cov : Head.Covered} {l : Nat} {V : SegVals}
    (hl : l < G.first.shape.link.length) (hV : valsAt Z G cov l = .ok V) :
    (u3Vals Z G cov).size l "U3" = some (1, V.n) := by
  unfold u3Vals
  dsimp only
  have e : ("U3" == "U3") = true := by decide
  rw [if_pos e, lookup_graph _ _ _ (List.mem_range.2 hl), hV]
  rfl

/-- **GENERAL: from a seat's pair, the size and the closed test: the light test at "u3Rows".** -/
theorem light_of_first {Z : Pub} {G : Ground} {cov : Head.Covered} {codes : OnBytes.Codes}
    {s : OnBytes.OracleShape} {l m n : Nat} {a : MsgAddr}
    (hp : pairOf (u3Seats Z G) a = some (l, m))
    (hz : (u3Vals Z G cov).size l "U3" = some (1, n)) (hn : n ≠ 0)
    (hf : firstLaid G.first.codes G.first.shape G.first.layout codes s l m = true) :
    arraysLaidLight (u3Rows Z G cov) G.first.layout codes s l m a = true := by
  unfold firstLaid at hf
  rw [Bool.and_eq_true] at hf
  obtain ⟨hm, hA⟩ := hf
  unfold arraysLaidLight
  refine List.all_eq_true.2 fun A hAm => ?_
  obtain ⟨b, hb, hbb⟩ := List.any_eq_true.1 (List.all_eq_true.1 hA A hAm)
  refine List.any_eq_true.2 ⟨b, hb, ?_⟩
  rw [Bool.and_eq_true, Bool.and_eq_true] at hbb
  obtain ⟨⟨h1, h2⟩, h3⟩ := hbb
  cases hlb : laidBack G.first.layout l m b.firstRow b.firstPlace with
  | none =>
    rw [hlb] at h3
    cases h3
  | some y =>
    rw [hlb] at h3
    change (y.1.name == A.name && y.1.name == "U3" && y.2.1 == 0 && y.2.2 == 0) = true at h3
    simp only [Bool.and_eq_true, beq_iff_eq] at h3
    obtain ⟨⟨⟨n1, n2⟩, n3⟩, n4⟩ := h3
    have hlay : (u3Rows Z G cov).lays a b.firstRow b.firstPlace = true := by
      show (match pairOf (u3Seats Z G) a with
        | some (l, m) =>
          msgFits G.first.codes G.first.shape G.first.layout l m &&
            (laidBack G.first.layout l m b.firstRow b.firstPlace).any fun x =>
              ((u3Vals Z G cov).size l x.1.name).any fun z => decide (x.2.1 < z.1 ∧ x.2.2 < z.2)
        | none => false) = true
      rw [hp]
      show (msgFits G.first.codes G.first.shape G.first.layout l m &&
        (laidBack G.first.layout l m b.firstRow b.firstPlace).any fun x =>
          ((u3Vals Z G cov).size l x.1.name).any fun z => decide (x.2.1 < z.1 ∧ x.2.2 < z.2)) = true
      rw [hm, hlb]
      show (((u3Vals Z G cov).size l y.1.name).any fun z => decide (y.2.1 < z.1 ∧ y.2.2 < z.2)) =
        true
      rw [n2, hz, n3, n4]
      show decide (0 < 1 ∧ 0 < n) = true
      exact decide_eq_true ⟨Nat.one_pos, Nat.pos_of_ne_zero hn⟩
    rw [h1, h2, hlay]
    show (y.1.name == A.name) = true
    exact beq_iff_eq.2 n1

/-- A helper: two steps that return. -/
theorem bind_ok {α β : Type} {x : Except String α} {f : α → Except String β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- Where "fitsSeg" returns, n is not 0. -/
theorem fitsSeg_n {Z : Pub} {G : Ground} {seg : Nat} {hh : Forest.Shape} {look0 own0 n : Nat}
    {mats : Array TMat} (h : fitsSeg Z G seg hh look0 own0 n mats = .ok ()) : n ≠ 0 := by
  have k := fitsSeg_halves Z G seg hh look0 own0 n mats
  rw [h] at k
  have k' : (fitsLook Z hh look0 own0 && n != 0 && fitsMats G.W seg mats) = true := k.symm
  rw [Bool.and_eq_true, Bool.and_eq_true] at k'
  exact bne_iff_ne.1 k'.1.2

theorem layersVals_n {Z : Pub} {G : Ground} {sps : List ProofFile.Spot} {seg g : Nat} {V : SegVals}
    (h : layersVals Z G sps seg g = .ok V) : V.n ≠ 0 := by
  unfold layersVals at h
  dsimp only at h
  obtain ⟨hp, -, h⟩ := bind_ok h
  obtain ⟨k4, -, h⟩ := bind_ok h
  obtain ⟨k3, -, h⟩ := bind_ok h
  obtain ⟨-, -, h⟩ := bind_ok h
  obtain ⟨-, -, h⟩ := bind_ok h
  obtain ⟨-, -, h⟩ := bind_ok h
  obtain ⟨-, -, h⟩ := bind_ok h
  obtain ⟨y, -, h⟩ := bind_ok h
  obtain ⟨-, -, h⟩ := bind_ok h
  obtain ⟨⟨⟩, hf, h⟩ := bind_ok h
  cases h
  exact fitsSeg_n hf

theorem attVals_n {Z : Pub} {G : Ground} {sps : List ProofFile.Spot} {seg g : Nat} {V : SegVals}
    (h : attVals Z G sps seg g = .ok V) : V.n ≠ 0 := by
  unfold attVals at h
  dsimp only at h
  obtain ⟨A, -, h⟩ := bind_ok h
  obtain ⟨k5, -, h⟩ := bind_ok h
  obtain ⟨k3, -, h⟩ := bind_ok h
  obtain ⟨-, -, h⟩ := bind_ok h
  obtain ⟨-, -, h⟩ := bind_ok h
  obtain ⟨⟨⟩, hf, h⟩ := bind_ok h
  cases h
  exact fitsSeg_n hf

theorem headVals_n {Z : Pub} {G : Ground} {cov : Head.Covered} {sps : List ProofFile.Spot} {seg : Nat}
    {V : SegVals} (h : headVals Z G cov sps seg = .ok V) : V.n ≠ 0 := by
  unfold headVals at h
  dsimp only at h
  obtain ⟨k6, -, h⟩ := bind_ok h
  obtain ⟨k3, -, h⟩ := bind_ok h
  obtain ⟨-, -, h⟩ := bind_ok h
  obtain ⟨-, -, h⟩ := bind_ok h
  obtain ⟨-, -, h⟩ := bind_ok h
  obtain ⟨⟨⟩, hf, h⟩ := bind_ok h
  cases h
  exact fitsSeg_n hf

/-- **GENERAL: what "valsAt" returns has n ≠ 0**: each of the three makers asks "fitsSeg" at the n
that it returns. -/
theorem n_ne_zero {Z : Pub} {G : Ground} {cov : Head.Covered} {l : Nat} {V : SegVals}
    (hV : valsAt Z G cov l = .ok V) : V.n ≠ 0 := by
  unfold valsAt at hV
  obtain ⟨sps, -, hV⟩ := bind_ok hV
  obtain ⟨Y, -, hV⟩ := bind_ok hV
  obtain ⟨-, -, hV⟩ := bind_ok hV
  obtain ⟨-, -, hV⟩ := bind_ok hV
  split at hV
  · exact layersVals_n hV
  · split at hV
    · exact attVals_n hV
    · split at hV
      · exact headVals_n hV
      · cases hV

/-! ## 3 From the returns to "ReadsLight" -/

/-- **UNDER THE HEAD AND THE OPENING: WHERE THE MAKER RETURNS AT EACH OF THE 25 SEGMENTS, AT THE
INSTANCE's COVERED POSITIONS: "ReadsLight".** -/
theorem readsLight_of_vals (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) (ξ : ProofFile.Inst)
    (hv : ∀ l < 25, ∃ V, valsAt Zp Bs.G₀ ((covOf Zp Bs.G₀ ξ).toOption.getD default) l = .ok V) :
    ReadsLight Zp Bs.G₀ ξ := by
  intro p hp
  have k := readsBy_at_head h O
  unfold readsBy at k
  have k1 := List.all_eq_true.1 k p hp
  have e2 := (first_at_head h O.blank).2.1
  have hlen : Bs.G₀.first.shape.link.length = 25 := by
    rw [e2]
    decide
  unfold lightAt
  refine List.all_eq_true.2 fun y hy => List.all_eq_true.2 fun s hs => ?_
  have k2 := List.all_eq_true.1 (List.all_eq_true.1 k1 y hy) s hs
  cases ha : p.addrs y.2 s.2 with
  | none => rfl
  | some a =>
    rw [ha] at k2
    change readsOne (ownSeats Zp Bs.G₀) Bs.G₀.first.codes Bs.G₀.first.shape Bs.G₀.first.layout
      (seatsOf Zp Bs.G₀ "U3") (seatsOf Zp Bs.G₀ "BZ") y.1.sizes.codes s.1 y.2 s.2 a = true at k2
    show (!mineReads Zp Bs.G₀ a ||
      arraysLaidLight (u3RowsOf Zp Bs.G₀ ξ) Bs.G₀.first.layout y.1.sizes.codes s.1 y.2 s.2 a) = true
    cases hm : mineReads Zp Bs.G₀ a with
    | false => rfl
    | true =>
      unfold mineReads mineSwitch at hm
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true',
        Bool.not_eq_true'] at hm
      obtain ⟨⟨n1, n2⟩, n3⟩ := hm
      unfold readsOne at k2
      have n1' : (ProofFile.Honest.K2.seatBy Bs.G₀.first.shape (ownSeats Zp Bs.G₀) a).isSome = false := n1
      rw [n1', n2, n3, Bool.false_or, Bool.false_or, Bool.false_or, Bool.and_eq_true,
        Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at k2
      obtain ⟨⟨q1, q2⟩, q3⟩ := k2
      obtain ⟨V, hV⟩ := hv y.2 q2
      exact light_of_first q1 (size_of_vals (by rw [hlen]; exact q2) hV) (n_ne_zero hV) q3

end OnBytes.HonestTrace.U3.Fit

-- Lean's own words on each theorem of this file: its statement and its axioms: each line
-- «depends on axioms» should name no more than propext, Classical.choice and Quot.sound.
#check @OnBytes.HonestTrace.U3.Fit.readsW
#check @OnBytes.HonestTrace.U3.Fit.readsW_can_fail
#check @OnBytes.HonestTrace.U3.Fit.readsBy_at_head
#check @OnBytes.HonestTrace.U3.Fit.lookup_graph
#check @OnBytes.HonestTrace.U3.Fit.size_of_vals
#check @OnBytes.HonestTrace.U3.Fit.light_of_first
#check @OnBytes.HonestTrace.U3.Fit.bind_ok
#check @OnBytes.HonestTrace.U3.Fit.fitsSeg_n
#check @OnBytes.HonestTrace.U3.Fit.layersVals_n
#check @OnBytes.HonestTrace.U3.Fit.attVals_n
#check @OnBytes.HonestTrace.U3.Fit.headVals_n
#check @OnBytes.HonestTrace.U3.Fit.n_ne_zero
#check @OnBytes.HonestTrace.U3.Fit.readsLight_of_vals
#print axioms OnBytes.HonestTrace.U3.Fit.readsW
#print axioms OnBytes.HonestTrace.U3.Fit.readsW_can_fail
#print axioms OnBytes.HonestTrace.U3.Fit.readsBy_at_head
#print axioms OnBytes.HonestTrace.U3.Fit.lookup_graph
#print axioms OnBytes.HonestTrace.U3.Fit.size_of_vals
#print axioms OnBytes.HonestTrace.U3.Fit.light_of_first
#print axioms OnBytes.HonestTrace.U3.Fit.bind_ok
#print axioms OnBytes.HonestTrace.U3.Fit.fitsSeg_n
#print axioms OnBytes.HonestTrace.U3.Fit.layersVals_n
#print axioms OnBytes.HonestTrace.U3.Fit.attVals_n
#print axioms OnBytes.HonestTrace.U3.Fit.headVals_n
#print axioms OnBytes.HonestTrace.U3.Fit.n_ne_zero
#print axioms OnBytes.HonestTrace.U3.Fit.readsLight_of_vals
