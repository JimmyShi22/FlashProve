-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/LotLaid.lean: CONDITIONAL: from "the honest side of the lot of
the attention segments' own rounds (kind K5) is laid" to the half that the fold finds at the kind's
place of each group of layers; and the member's debts under that premise.

The lot's honest side (`k5Lot`, Honest/K5/Row.lean) lays a half at every attention segment of the
ground at which the maker of the place's public data (`seatAt`) yields, and none, without a word,
where one of that maker's tests fails. In scope the ground's attention segments are the twelve
(2 g + 1, "A‹g›", g) (`k5Places_scope`, Johnson/Desc/First/Att/Row/K5RowSeat.lean).
GENERAL IN THE MAKER: every statement takes a maker mk (of a segment's number, its name and its
group) and the list `halvesBy mk cells G` that a lot over mk lays: so it serves a lot whose maker
asks more tests than `seatAt`, wherever what that maker yields `seatAt` yields too.

  `find_none`, `find_filterMap`   GENERAL: the first member with a mark, in a list that is made
                   member by member, where the mark tells the maker's argument
  `halvesBy`       the list that a lot over the maker mk lays; `halves_k5Lot`, `halves_k5LotK`: the
                   list of `k5Lot` is that at `seatAt`, the list of `k5LotK`
                   (Honest/K5/KeysFit.lean), which asks a third test, that at `seatAtK`
  `lot_find`       CONDITIONAL: what that list holds at the kind's place of group g: the half at
                   what the maker yields there; nothing where it yields nothing
  `LotLaid`        a premise's form on the list of halves: at each place of the kind the first half
                   is the first of the lot's own list there
  `lotLaid_first`  GENERAL in the lots: `LotLaid` at the frame's own list of the first chain's
                   halves (`firstOf`, Honest/Frame.lean), where the lot is among the lots and no
                   other lot lays a half at a place of the kind
  `half_laid`      CONDITIONAL: **either the maker yields and the fold finds the kind's half at what
                   it yields, or it yields nothing and the fold finds no half there**
  `k5_owes_laid`   CONDITIONAL: the member's debts (`k5_owes_head`, Honest/K5/Law/OwesAtHead.lean)
                   with `LotLaid` in the stead of "the list holds the kind's half"
  `k5_owes_laidK`  CONDITIONAL: the same at the maker `seatAtK`: the lot that is meant to be laid

WHAT IS LEFT ON THE PUBLIC SIDE: "the maker yields at the real public files": its tests with code
say yes there. They are not evaluated there. It stays a premise (hY). Where it yields nothing no
half stands at the place, and nothing is said here of the member's debts.
WHICH GROUND. Every statement takes the ground G with hG: G is what the description's maker makes of
the public part. The frame's `firstOf` takes the ground as an argument, and no text calls it yet:
whoever lays the first chain's list of halves is meant to hand it that ground.

Limits. Every theorem is conditional; the hypothesis `P5J.AtMgA` is not shown here.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.OwesAtHead
import Johnson.Desc.First.Att.Row.K5RowSeat
import Johnson.Desc.ProofFile.Honest.K5.KeysFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Block Strs Chain Place KindName)
open H2K5.Honest (K5Keeps)
open ProofFile.Honest.FirstThread (Script WtF)
open P5J (AtMgA TS CellsM)

/-! ## 1 General -/

section
variable {ι α : Type} {f : ι → Option α} {p : α → Bool} {i : ι}

/-- Where the maker yields nothing at i, no member bears i's mark. CONDITIONAL: hp: a member bears
the mark just if it is made at i. -/
theorem find_none (hp : ∀ j x, f j = some x → (p x = true ↔ j = i)) (hn : f i = none)
    (l : List ι) : (l.filterMap f).find? p = none := by
  rw [List.find?_eq_none]
  intro x hx hpx
  obtain ⟨j, -, hj⟩ := List.mem_filterMap.1 hx
  obtain rfl := (hp j x hj).1 hpx
  rw [hn] at hj
  cases hj

/-- The first member that bears i's mark is what the maker yields at i. CONDITIONAL: hp, as above; i
is in the list. -/
theorem find_filterMap (hp : ∀ j x, f j = some x → (p x = true ↔ j = i)) :
    ∀ l : List ι, i ∈ l → (l.filterMap f).find? p = f i
  | [], h => by cases h
  | j :: l, h => by
    cases hj : f j with
    | none =>
      rw [List.filterMap_cons_none hj]
      by_cases e : j = i
      · subst e
        rw [hj]
        exact find_none hp hj l
      · exact find_filterMap hp l ((List.mem_cons.1 h).resolve_left fun e' => e e'.symm)
    | some x =>
      rw [List.filterMap_cons_some hj]
      cases hpx : p x with
      | true =>
        obtain rfl := (hp j x hj).1 hpx
        rw [List.find?_cons_of_pos hpx, hj]
      | false =>
        have e : j ≠ i := fun e => by
          have h1 := (hp j x hj).2 e
          rw [hpx] at h1
          cases h1
        rw [List.find?_cons_of_neg (by rw [hpx]; exact Bool.false_ne_true)]
        exact find_filterMap hp l ((List.mem_cons.1 h).resolve_left fun e' => e e'.symm)

end

/-! ## 2 The lot's own list -/

/-- The kind's place of group g. -/
abbrev placeOf (g : Nat) : Place := ⟨1, some (2 * g + 1), 3, .K5⟩

/-- **The list that a lot over the maker mk lays**: a half at every attention segment of the ground
at which mk yields. -/
def halvesBy {W₀ Rc Tr X : Type} (mk : Nat → String → Nat → Option Seat5) (cells : Tr → Cells)
    (G : Ground) : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X) :=
  (H2K5.k5Places G).filterMap fun y => (mk y.1 y.2.1 y.2.2).map (k5Half cells)

/-- The list of `k5Lot` is that at `seatAt`. No premise: by unfolding. -/
theorem halves_k5Lot {W₀ Rc Tr X : Type} (cells : Tr → Cells)
    (keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array OnBytes.E)) (Zp : ProofFile.Pub)
    (G : Ground) :
    (k5Lot (W₀ := W₀) (Rc := Rc) (Xi := ProofFile.Inst) (X := X) cells keyOf).halves Zp G =
      halvesBy (seatAt keyOf Zp G) cells G := rfl

/-- The list of `k5LotK` is that at `seatAtK`. No premise: by unfolding. -/
theorem halves_k5LotK {W₀ Rc Tr X : Type} (cells : Tr → Cells)
    (keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array OnBytes.E)) (Zp : ProofFile.Pub)
    (G : Ground) :
    (k5LotK (W₀ := W₀) (Rc := Rc) (Xi := ProofFile.Inst) (X := X) cells keyOf).halves Zp G =
      halvesBy (seatAtK keyOf Zp G) cells G := rfl

/-- What `seatAt` yields at a segment bears that segment's number. CONDITIONAL: it yields. -/
theorem seatAt_link {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array OnBytes.E)}
    {Zp : ProofFile.Pub} {G : Ground} (l : Nat) (nm : String) (j : Nat) (Y : Seat5)
    (hY : seatAt keyOf Zp G l nm j = some Y) : Y.link = l := by
  obtain ⟨A, base, -, -, rfl, -, -⟩ := seatAt_spec hY
  rfl

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {W₀ Rc Tr X : Type}
include h

/-- **What the list of a lot over the maker mk holds at the kind's place of group g.** CONDITIONAL:
under the hypothesis h; g is below 12; hG: G is the ground that the description's maker makes; hl:
what the maker yields at a segment bears that segment's number. -/
theorem lot_find {g : Nat} (hg : g < 12) (mk : Nat → String → Nat → Option Seat5)
    (hl : ∀ l nm j Y, mk l nm j = some Y → Y.link = l) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) (cells : Tr → Cells) :
    (halvesBy (W₀ := W₀) (Rc := Rc) (X := X) mk cells G).find? (fun q => q.place == placeOf g) =
      (mk (2 * g + 1) ("A" ++ toString g) g).map (k5Half cells) := by
  unfold halvesBy
  rw [H2K5.Row.k5Places_scope h.scope h.reads h.laid.pub hG, List.filterMap_map]
  refine find_filterMap (i := g) (fun j q hq => ?_) _ (List.mem_range.2 hg)
  obtain ⟨Y, hY, rfl⟩ := Option.map_eq_some_iff.1 hq
  have e0 : Y.link = 2 * j + 1 := hl _ _ _ _ hY
  show ((⟨1, some Y.link, 3, .K5⟩ : Place) == placeOf g) = true ↔ j = g
  rw [e0, beq_iff_eq]
  constructor
  · intro e
    have e1 : (2 * j + 1 : Nat) = 2 * g + 1 := Option.some.inj (congrArg Place.link e)
    omega
  · rintro rfl
    rfl

end

/-! ## 3 The list of halves -/

/-- **The lot's honest side is laid, and no other half stands in front of it at the kind's places**:
at each place of the kind the first half of the list is the first of the lot's own list there. It is
a definition: a premise's form. Nothing is claimed of it. -/
def LotLaid {W₀ Rc Tr X : Type}
    (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
    (mk : Nat → String → Nat → Option Seat5) (cells : Tr → Cells) (G : Ground) : Prop :=
  ∀ pl : Place, pl.kind = .K5 →
    hs.find? (fun q => q.place == pl) = (halvesBy mk cells G).find? fun q => q.place == pl

/-- **`LotLaid` at the frame's own list of the first chain's halves.** General in the lots and in
the maker. CONDITIONAL: a lot L₀ whose list is that over mk stands among the lots; no other lot lays
a half at a place of the kind. -/
theorem lotLaid_first {W₀ Rc Tr X : Type} (Zp : ProofFile.Pub) (G : Ground) (cells : Tr → Cells)
    (mk : Nat → String → Nat → Option Seat5)
    (L₀ : HLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X)
    (h₀ : L₀.halves Zp G = halvesBy mk cells G)
    (l₁ l₂ : List (HLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
    (hno : ∀ L ∈ l₁ ++ l₂, ∀ q ∈ L.halves Zp G, q.place.kind ≠ .K5) :
    LotLaid (firstOf Zp G (l₁ ++ L₀ :: l₂)) mk cells G := by
  intro pl hk
  have none_of : ∀ l : List (HLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X),
      (∀ L ∈ l, ∀ q ∈ L.halves Zp G, q.place.kind ≠ .K5) →
      (l.flatMap fun L => L.halves Zp G).find? (fun q => q.place == pl) = none := by
    intro l hl
    rw [List.find?_eq_none]
    intro q hq hp
    obtain ⟨L, hL, hqL⟩ := List.mem_flatMap.1 hq
    exact hl L hL q hqL (by rw [beq_iff_eq.1 hp]; exact hk)
  unfold firstOf
  rw [List.flatMap_append, List.flatMap_cons, List.find?_append, List.find?_append,
    none_of l₁ fun L hL => hno L (List.mem_append_left _ hL),
    none_of l₂ fun L hL => hno L (List.mem_append_right _ hL), h₀]
  simp

/-! ## 4 At the first chain's `Thread` at the library's own letters -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
    VerifiableInference.Desc.Sound.MsgT)
  (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
  (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
  (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
  (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (keeps : Nat → TS → TS → Prop)

include h in
/-- **EITHER THE MAKER OF THE PLACE's PUBLIC DATA YIELDS AND THE FOLD FINDS THE KIND's HALF AT WHAT
IT YIELDS, OR IT YIELDS NOTHING AND THE FOLD FINDS NO HALF THERE.** CONDITIONAL: under the
hypothesis h; g is below 12; hl: what the maker yields bears the segment's number; hG; `LotLaid`. -/
theorem half_laid {g : Nat} (hg : g < 12) {mk : Nat → String → Nat → Option Seat5}
    (hl : ∀ l nm j Y, mk l nm j = some Y → Y.link = l) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {cells : Tr → Cells}
    (hL : LotLaid hs mk cells G) :
    (∃ Z5, mk (2 * g + 1) ("A" ++ toString g) g = some Z5 ∧
        hs.find? (fun q => q.place == Z5.place) = some (k5Half cells Z5)) ∨
      (mk (2 * g + 1) ("A" ++ toString g) g = none ∧
        hs.find? (fun q => q.place == placeOf g) = none) := by
  have e := (hL (placeOf g) rfl).trans (lot_find h hg mk hl hG cells)
  cases hY : mk (2 * g + 1) ("A" ++ toString g) g with
  | none =>
    rw [hY] at e
    exact Or.inr ⟨rfl, e⟩
  | some Z5 =>
    rw [hY] at e
    have e0 : Z5.place = placeOf g := by
      show (⟨1, some Z5.link, 3, .K5⟩ : Place) = _
      rw [hl _ _ _ _ hY]
    exact Or.inl ⟨Z5, rfl, by rw [e0]; exact e⟩

/-- **THE MEMBER's DEBTS UNDER "THE LOT's HONEST SIDE IS LAID"**: it plays; behind its yes; the
exchange; it is accepted, for every fall. CONDITIONAL: as `k5_owes_head`, with `LotLaid` in the
stead of "the list holds the kind's half"; hmk: what the maker mk yields `seatAt` yields. hY, "the
maker yields", is the one premise on the public files beside the hypothesis h: its tests are not
evaluated there.
`SayOwed`, `JoinOwed` HOLD THE CLAUSES ON VALUES of two of the six items owed. -/
theorem k5_owes_laid {n g : Nat} (hg : g < 12)
    {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array OnBytes.E)} {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    {mk : Nat → String → Nat → Option Seat5}
    (hmk : ∀ l nm j Y, mk l nm j = some Y → seatAt keyOf Zp G l nm j = some Y) {Z5 : Seat5}
    (hY : mk (2 * g + 1) ("A" ++ toString g) g = some Z5)
    (hK : KeySizes Z5) {cells : Tr → Cells} (hL : LotLaid hs mk cells G)
    (hfit : (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).fits n = true)
    (hb : borderOf g < n)
    (Kp : ∀ s s', K5Keeps s s' → keeps (borderOf g) s s')
    (Rd : ∀ w s s', rides (borderOf g) w s → K5Keeps s s' → rides (borderOf g + 1) w s')
    (hans : AnsReadsRest ans ((P5J.At.N Zp cF).sent (2 * g + 1) 0))
    (hSay : ∀ a, (P5J.At.X Zp).A[g]? = some a →
      SayOwed h hs Q stored ans test carryX item n₁ n₂ valid rides keeps g a)
    (hJ : ∀ a, (P5J.At.X Zp).A[g]? = some a →
      JoinOwed h hs Q stored ans test carryX item n₁ n₂ valid rides keeps g a) :
    Plays (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g) ∧
      Behind (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g) ∧
      Exchange (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g) ∧
      ∀ fall, Accepted (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) fall
        (borderOf g) := by
  rcases half_laid h hs hg (fun l nm j Y e => seatAt_link l nm j Y (hmk l nm j Y e)) hG hL with
    ⟨Z5', hY', hh⟩ | ⟨hY', -⟩
  · obtain rfl : Z5' = Z5 := Option.some.inj (hY'.symm.trans hY)
    exact k5_owes_head h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg hG
      (hmk _ _ _ _ hY) hK hh hfit hb Kp Rd hans hSay hJ
  · rw [hY] at hY'
    cases hY'

/-- **THE SAME AT THE MAKER WITH THE THIRD TEST** (`seatAtK`), whose lot `k5LotK` is the one that is
meant to be laid. CONDITIONAL: as `k5_owes_laid`; what `seatAtK` yields `seatAt` yields
(`seatAtK_spec`). `SayOwed`, `JoinOwed` HOLD THE CLAUSES ON VALUES of two of the six items owed. -/
theorem k5_owes_laidK {n g : Nat} (hg : g < 12)
    {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array OnBytes.E)} {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {Z5 : Seat5}
    (hY : seatAtK keyOf Zp G (2 * g + 1) ("A" ++ toString g) g = some Z5)
    (hK : KeySizes Z5) {cells : Tr → Cells} (hL : LotLaid hs (seatAtK keyOf Zp G) cells G)
    (hfit : (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).fits n = true)
    (hb : borderOf g < n)
    (Kp : ∀ s s', K5Keeps s s' → keeps (borderOf g) s s')
    (Rd : ∀ w s s', rides (borderOf g) w s → K5Keeps s s' → rides (borderOf g + 1) w s')
    (hans : AnsReadsRest ans ((P5J.At.N Zp cF).sent (2 * g + 1) 0))
    (hSay : ∀ a, (P5J.At.X Zp).A[g]? = some a →
      SayOwed h hs Q stored ans test carryX item n₁ n₂ valid rides keeps g a)
    (hJ : ∀ a, (P5J.At.X Zp).A[g]? = some a →
      JoinOwed h hs Q stored ans test carryX item n₁ n₂ valid rides keeps g a) :
    Plays (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g) ∧
      Behind (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g) ∧
      Exchange (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g) ∧
      ∀ fall, Accepted (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) fall
        (borderOf g) :=
  k5_owes_laid h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg hG
    (fun _ _ _ _ e => (seatAtK_spec e).1) hY hK hL hfit hb Kp Rd hans hSay hJ

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.find_none
#print axioms ProofFile.Honest.K5.find_filterMap
#print axioms ProofFile.Honest.K5.halves_k5Lot
#print axioms ProofFile.Honest.K5.halves_k5LotK
#print axioms ProofFile.Honest.K5.seatAt_link
#print axioms ProofFile.Honest.K5.lot_find
#print axioms ProofFile.Honest.K5.lotLaid_first
#print axioms ProofFile.Honest.K5.half_laid
#print axioms ProofFile.Honest.K5.k5_owes_laid
#print axioms ProofFile.Honest.K5.k5_owes_laidK
