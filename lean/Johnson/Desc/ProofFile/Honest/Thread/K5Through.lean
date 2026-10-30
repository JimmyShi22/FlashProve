-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/K5Through.lean: ONE KIND THROUGH: ALL THE DEBTS OF THE TWELVE
MEMBERS OF KIND K5 (an attention segment's own rounds) AT THE FIRST CHAIN's THREAD AT THE LIBRARY's
HEAD (`lettersHead`, Honest/Thread/FirstHead.lean), IN THE FORMS THAT THE FILE's RULE ASKS (`OwesS`'
four conjuncts and `YesS`' one: Honest/Thread/PaysS.lean), FROM ONE HEAD (`AtHonest`,
Honest/AtHonest.lean) AND NAMED PREMISES. A joining: it pays nothing on a value. What it is for:
every lot's piece meets here at one place: where one does not fit, Lean says so. One definition: a
list of tests; three helpers; two theorems.

  `k5Asks`   the tests with code that the kind's laws take at the head, each with a name
  `k5Keeps_st_out`   the kind's clause leaves the statement and the output
  `ansReadsRest_head`, `ansOn_head`   two sentences on the letter ans, at the laid pin
  `k5_through`   THE THEOREM, AT ONE INPUT w
  `k5_through_all`   the same at every input: the form that the rule's premises take

THE TESTS. `k5Asks` is meant for `AtHonest`'s list more. IT HOLDS FOUR SORTS OF TEST: a closed Bool
on the written lists (the forward rows' one pass) · one on the OnlineProverParts's other lots · one on the
thread's letter b₀ (the reply is not laid right behind a member of the kind) · twelve on the
letter keyOf.

THE TWO HELPERS ON ans hold at the pin that `lettersHead` lays (`ansJT`, Honest/Thread/Ans.lean),
with no premise: that pin reads no oracle and, of the state, the statement alone, which `K5Keeps`
leaves (the seal's `rest_st`). THEY ARE TWINS OF THE HOUSE's OWN ansReadsRest_JT AND ansOn_JT (its
pack), WHICH STAY: this file does not stand over that pack. They are lemmas
for no house.

WHOSE PIECES MEET. H2's (the kind's house): `k5_owes_all_T`, `k5AtT_thrAt`, `k5RidersT_thrAt`,
`k5_seated_keys`, `lotLaid_first` · the frame's keeper's: `AtHonest`, `atPure_ok` (the prover's
halves are the lots' own, at the blank ground) · the pen of the threads': `lettersHead`,
`head_keepsAt`, `head_reply_next`, `riders_next`, `ansJT_rows`, the five lemmas from a debt to its
twin at the pair · this pen's: `fits_head`.

THE PREMISES, BY CLASS.
  THE HEAD: a : `AtHonest` …, with the fifteen tests of `k5Asks` in its list more (hmore).
     THE HEAD IS ASKED WHOLE; SPENT ARE its fields head and made and its lemmas isTerm and asked.
     So the theorem cannot be called at a OnlineProverParts at which another field fails, though its proof
     wants none of these.
  THE SCRIPT's TIES, BY NAME: hfix (a tree that is at hand is fixed by the rounds in front) ·
     Sc (`K5Script`: maskTie · cellsTie · keyTie). Sc IS ASKED AT THE THREAD; ITS THIRD FIELD
     NAMES NO LETTER OF THE SCRIPT.
  Vd's CLAUSES, BY NAME: hI (`IdnOwed`), asked AT THE INPUT w ALONE.
  AND FOUR THAT ARE OF NONE OF THESE THREE CLASSES, KEPT BY NAME SO THAT THEY SHOW: hlots (the
     OnlineProverParts's lots hold the kind's lot) · hKp (the letter Kp at the kind's places IS `K5Keeps`) ·
     hcs (no clause of the riders' list begins right behind a member of the kind, and each that
     spans one stays under `K5Keeps`) · hK (`KeySizes`: on the letter keyOf).
hKp AND hcs ARE MET AT `K5Keeps` ALONE. At a stricter clause (with "no mark behind"
inside) hKp's forward half is false: there this theorem cannot be called.

Limits. THE FULL SIZE ALONE, and the format's second hash function alone. No member of `AtHonest` is shown.
Its field head, the library's own head, has a member at the name under four premises on the public
files (the seal's `P5J.head_exists_at_name`); this file does not call it; no member of that head
together with the thread's sentence is shown. NONE OF Sc, hI, hK, hfix IS SHOWN. NO PREMISE BARS
THAT THE THREAD HOLDS OF NOTHING: every premise can hold, and the statement then says nothing, at a
Vd that the input does not meet; at a list cs with a clause whose sentence is false on a span over
the border; at a Script whose tables no half sends, or at whose witness an open item fails. OF THE
THREAD's LETTERS item, n₁, n₂, test AND carryX, AND OF Said, THE PROOF READS NOTHING (our attacker's
reading): they are handed through. The reader cells of the trace is tied to the OnlineProverParts's
readers by nothing here (at the filling: `k5_readers_now`, Honest/Thread/K5ThroughNow.lean).
`lettersHead` IS WITHOUT CODE: NO TEST WITH CODE REACHES THE THREAD ITSELF: the tests of `k5Asks`
are on written lists, the OnlineProverParts, one number and the letter keyOf. Twelve members of 358. None is
one of the library's goals. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.Thread.FitsHead
import Johnson.Desc.ProofFile.Honest.Thread.HeadForm
import Johnson.Desc.ProofFile.Honest.Thread.RidersAnd
import Johnson.Desc.ProofFile.Honest.Thread.PaysS
import Johnson.Desc.ProofFile.Honest.AtHonest
import Johnson.Desc.ProofFile.Honest.K5.Law.RidesT
import Johnson.Desc.ProofFile.Honest.K5.Law.Whole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place Block)
open VerifiableInference.Desc.First (start)
open VerifiableInference.Desc.First.Att.P (rest_st rest_out)
open VerifiableInference.Desc.Sound (MsgT seatTab)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open H2K5.Honest (K5Keeps)
open FirstRows (opens rowAt)

variable {W₀ Rc Tr X₀ X : Type}

/-! ## 1 The tests by name -/

/-- **The tests with code that K5's laws take at the head**, each with a name: for `AtHonest`'s list
more. others: the OnlineProverParts's lots but the kind's own. It is a definition: a list of tests. -/
def k5Asks (Zp : ProofFile.Pub) (G : Ground) (cF : Chain TS ProofFile.Cl)
    (keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array OnBytes.E))
    (others : List (HLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X)) (b₀ : Nat) :
    List (String × Bool) :=
  [("the first chain's forward rows pass the test in one pass",
      ((opens P5J.At.links P5J.At.ps (start P5J.At.links)).zip P5J.At.ps).all fun x =>
        ((rowAt P5J.At.links x.2).asks ++ (rowAt P5J.At.links x.2).shuts).all x.1.contains),
   ("no other lot lays a half of kind K5",
      others.all fun L => (L.halves Zp G).all fun q => q.place.kind != .K5),
   ("the reply is not laid right behind an attention segment's own rounds",
      (List.range 12).all fun g => b₀ != K5.borderOf g + 1)] ++
  (List.range 12).map fun g => (s!"the key points fit at group {g}",
    ((P5J.At.X Zp).A[g]?).all fun a => (K5.seatOf keyOf Zp G cF g a).keysFit
      (K5.blankDraws (Zp.D.1.take (roundsTo cF.blocksInOrder (K5.borderOf g)))))

/-! ## 2 Helpers -/

/-- **The kind's clause leaves the statement and the output.** -/
theorem k5Keeps_st_out {s s' : TS} (h : K5Keeps s s') : s'.st = s.st ∧ s'.out = s.out :=
  ⟨rest_st s' s h.1, rest_out s' s h.1⟩

/-- **What the laid pin says of a state it says of every state that `K5Keeps` ties to it.** A
helper. -/
theorem ansReadsRest_head (Zp : ProofFile.Pub) (lay : ByteArray) (L : List (Nat × Nat)) :
    K5.AnsReadsRest (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp) (P5J.At.ms Zp lay) :
      Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) L := by
  intro z _ π s s' y v hK h0
  have e : s'.st = s.st := (k5Keeps_st_out hK).1
  exact ansJT_rows (P5J.At.cs Zp) (P5J.At.arr Zp) (seats := P5J.At.seats Zp)
    (fun x _ _ => by rw [e]) h0

/-- **The like at whatever strings**: the pin reads no oracle. A helper. -/
theorem ansOn_head (Zp : ProofFile.Pub) (lay : ByteArray) (z : Nat × Nat) (n : Nat) :
    K5.AnsOn (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp) (P5J.At.ms Zp lay) :
      Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) z n := by
  intro π s s' y y' v _ hK h0
  have e : s'.st = s.st := (k5Keeps_st_out hK).1
  exact ansJT_rows (P5J.At.cs Zp) (P5J.At.arr Zp) (seats := P5J.At.seats Zp)
    (fun x _ _ => by rw [e]) h0

/-! ## 3 The kind, through -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
  {G : Sides A.F A.B W₀ Rc OnBytes.TableKey Tr X₀ X} {more : List (String × Bool)}

/-- **ALL THE DEBTS OF K5's TWELVE MEMBERS AT THE HEAD's FIRST THREAD, FROM THE PAIR, AT ONE
INPUT.** A conditional lemma on these definitions. It is none of the library's
goals. -/
theorem k5_through (a : AtHonest OnBytes.secondHashFunction Z D r Zp Np cF x P A G more)
    (Q : Script A.B (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : (Local W₀ Rc ProofFile.Inst Tr) → Prop) (cs : List (RiderCl (Local W₀ Rc ProofFile.Inst Tr) TS))
    (Kp : Place → TS → TS → Prop) (w : (Local W₀ Rc ProofFile.Inst Tr))
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {cells : Tr → Cells}
    {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array OnBytes.E)}
    {l₁ l₂ : List (HLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X)}
    (hlots : P.lots = l₁ ++ K5.k5LotK cells keyOf :: l₂)
    (hmore : ∀ t ∈ k5Asks Zp A.G cF keyOf (l₁ ++ l₂) b₀, t ∈ more)
    (hKp : ∀ g, g < 12 → ∀ s s', Kp (K5.placeOf g) s s' ↔ K5Keeps s s')
    (hcs : ∀ g, g < 12 → ∀ c ∈ cs, c.lo ≠ K5.borderOf g + 1 ∧
      (c.lo ≤ K5.borderOf g → K5.borderOf g + 1 ≤ c.hi → ∀ v s s', K5Keeps s s' →
        c.prop (K5.borderOf g) v s → c.prop (K5.borderOf g + 1) v s'))
    (hK : ∀ g p, (P5J.At.X Zp).A[g]? = some p → K5.KeySizes (K5.seatOf keyOf Zp A.G cF g p))
    (hfix : ∀ b, b ≤ cF.blocksInOrder.length → ∀ j, j < treesTo cF.blocksInOrder b →
      Q.fixed (.own j) ≤ roundsTo cF.blocksInOrder b)
    (Sc : ∀ g p blk, g < 12 → (P5J.At.X Zp).A[g]? = some p →
      cF.blocksInOrder[K5.borderOf g]? = some blk →
      K5.K5Script (lettersHead a.head A.H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w).thread
        (K5.borderOf g) cells (K5.seatOf keyOf Zp A.G cF g p) p blk
        (a.head.𝔇.pubD.N.sent (2 * g + 1) 0) (seatTab a.head.𝔇.cs a.head.𝔇.arr a.head.𝔇.ms))
    (hI : ∀ g p, (P5J.At.X Zp).A[g]? = some p →
      K5.IdnOwed (fun v => v = w ∧ Vd v) cells (K5.seatOf keyOf Zp A.G cF g p)) :
    ∀ g, g < 12 →
      (PlaysS (lettersHead a.head A.H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w).thread
          Said (K5.borderOf g) ∧
        BehindS (lettersHead a.head A.H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w).thread
          Said (K5.borderOf g) ∧
        ExchangeS (lettersHead a.head A.H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w).thread
          Said (K5.borderOf g) ∧
        RidesPastS (lettersHead a.head A.H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w).thread
          Said (K5.borderOf g)) ∧
      ∀ fl, AcceptedS
        (lettersHead a.head A.H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w).thread
        Said fl (K5.borderOf g) := by
  intro g hg
  have h := a.head
  obtain ⟨-, hG, -, -, -, -, -, hfirst, -⟩ := atPure_ok a.made
  rw [a.isTerm.1] at hG hfirst
  -- the tests by name
  have hm : ∀ t ∈ k5Asks Zp A.G cF keyOf (l₁ ++ l₂) b₀, t.2 = true :=
    fun t ht => a.asked (hmore t ht)
  unfold k5Asks at hm
  have tOne := hm _ (List.mem_append_left _ List.mem_cons_self)
  have tNo := hm _ (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have tB := hm _ (List.mem_append_left _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have tKey := hm _ (List.mem_append_right _ (List.mem_map.2 ⟨g, List.mem_range.2 hg, rfl⟩))
  dsimp only at tOne tNo tB
  have hb₀ : b₀ ≠ K5.borderOf g + 1 :=
    bne_iff_ne.1 (List.all_eq_true.1 tB g (List.mem_range.2 hg))
  have hno : ∀ L ∈ l₁ ++ l₂, ∀ q ∈ L.halves Zp A.G, q.place.kind ≠ .K5 := fun L hL q hq =>
    bne_iff_ne.1 (List.all_eq_true.1 (List.all_eq_true.1 tNo L hL) q hq)
  have hKey : ∀ p, (P5J.At.X Zp).A[g]? = some p → (K5.seatOf keyOf Zp A.G cF g p).keysFit
      (K5.blankDraws (Zp.D.1.take (roundsTo cF.blocksInOrder (K5.borderOf g)))) = true := by
    intro p hp
    have t := tKey
    simp only [hp, Option.all_some] at t
    exact t
  -- the half in the thread's letter hs
  have hL : K5.LotLaid A.H.first (K5.seatAtK keyOf Zp A.G) cells A.G := by
    rw [hfirst, hlots]
    exact K5.lotLaid_first Zp A.G cells (K5.seatAtK keyOf Zp A.G) (K5.k5LotK cells keyOf)
      (K5.halves_k5LotK cells keyOf Zp A.G) l₁ l₂ hno
  obtain ⟨blk, p, hp, Hs⟩ := K5.k5_seated_keys h A.H.first Q (fun v => A.H.storedWords v.w₀ v.rc)
      (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp) (P5J.At.ms Zp Z.lay)) test carryX
      item n₁ n₂ (fun v => v = w ∧ Vd v)
      (fun b v s => (b₀ ≤ b → s.out.reply = some v.x.asked) ∧ ridersOf cs b v s)
      (fun b s s' => ∀ p, P5J.At.ps[b]? = some p → Kp p s s')
      hg hG hKey (hK g) hL
  -- keeps at the member is the clause of its own place
  have hplace : blk.place = K5.placeOf g := Hs.place
  have hk : ∀ s s', (∀ q, P5J.At.ps[K5.borderOf g]? = some q → Kp q s s') ↔
      Kp (K5.placeOf g) s s' := fun s s' => by
    rw [← hplace]
    exact head_keepsAt h A.H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w Hs.member s s'
  -- the rider, one border on
  have hRd : ∀ v s s', ((b₀ ≤ K5.borderOf g → s.out.reply = some v.x.asked) ∧
        ridersOf cs (K5.borderOf g) v s) → K5Keeps s s' →
      ((b₀ ≤ K5.borderOf g + 1 → s'.out.reply = some v.x.asked) ∧
        ridersOf cs (K5.borderOf g + 1) v s') := fun v s s' hr hKK =>
    ⟨head_reply_next (asked := fun u : (Local W₀ Rc ProofFile.Inst Tr) => u.x.asked) hr.1
        (fun e => absurd e hb₀) fun _ => by rw [(k5Keeps_st_out hKK).2],
      riders_next hr.2 (fun c hc hl hh hq => (hcs g hg c hc).2 hl hh v s s' hKK hq)
        fun c hc e => absurd e (hcs g hg c hc).1⟩
  obtain ⟨⟨p1, p2, p3, p4⟩, p5⟩ := K5.k5_owes_all_T h
    (K5.k5AtT_thrAt h A.H.first Q (fun v => A.H.storedWords v.w₀ v.rc)
      (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp) (P5J.At.ms Zp Z.lay)) test carryX
      item n₁ n₂ (fun v => v = w ∧ Vd v)
      (fun b v s => (b₀ ≤ b → s.out.reply = some v.x.asked) ∧ ridersOf cs b v s)
      (fun b s s' => ∀ p, P5J.At.ps[b]? = some p → Kp p s s') hg)
    (K5.k5RidersT_thrAt h A.H.first Q (fun v => A.H.storedWords v.w₀ v.rc)
      (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp) (P5J.At.ms Zp Z.lay)) test carryX
      item n₁ n₂ (fun v => v = w ∧ Vd v)
      (fun b v s => (b₀ ≤ b → s.out.reply = some v.x.asked) ∧ ridersOf cs b v s)
      (fun b s s' => ∀ p, P5J.At.ps[b]? = some p → Kp p s s') hg
      fun s s' hh => (hKp g hg s s').1 ((hk s s').1 hh))
    hg hp Hs
    (fits_head h A.H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w tOne hfix)
    (lt_of_member _ Hs.member)
    (fun s s' hh => (hk s s').2 ((hKp g hg s s').2 hh)) hRd
    (ansReadsRest_head Zp Z.lay _) (ansOn_head Zp Z.lay _ _)
    (Sc g p blk hg hp Hs.member) rfl (hI g p hp)
  exact ⟨⟨playsS_of _ _ p1, behindS_of _ _ p2, exchangeS_of _ _ p3, ridesPastS_of _ _ p4⟩,
    fun fl => acceptedS_of _ _ (p5 fl)⟩

/-- **THE SAME AT EVERY INPUT**: the form that the rule's premises take. -/
theorem k5_through_all (a : AtHonest OnBytes.secondHashFunction Z D r Zp Np cF x P A G more)
    (Q : Script A.B (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : (Local W₀ Rc ProofFile.Inst Tr) → Prop) (cs : List (RiderCl (Local W₀ Rc ProofFile.Inst Tr) TS))
    (Kp : Place → TS → TS → Prop)
    (Said : (Local W₀ Rc ProofFile.Inst Tr) → Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {cells : Tr → Cells}
    {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array OnBytes.E)}
    {l₁ l₂ : List (HLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X)}
    (hlots : P.lots = l₁ ++ K5.k5LotK cells keyOf :: l₂)
    (hmore : ∀ t ∈ k5Asks Zp A.G cF keyOf (l₁ ++ l₂) b₀, t ∈ more)
    (hKp : ∀ g, g < 12 → ∀ s s', Kp (K5.placeOf g) s s' ↔ K5Keeps s s')
    (hcs : ∀ g, g < 12 → ∀ c ∈ cs, c.lo ≠ K5.borderOf g + 1 ∧
      (c.lo ≤ K5.borderOf g → K5.borderOf g + 1 ≤ c.hi → ∀ v s s', K5Keeps s s' →
        c.prop (K5.borderOf g) v s → c.prop (K5.borderOf g + 1) v s'))
    (hK : ∀ g p, (P5J.At.X Zp).A[g]? = some p → K5.KeySizes (K5.seatOf keyOf Zp A.G cF g p))
    (hfix : ∀ b, b ≤ cF.blocksInOrder.length → ∀ j, j < treesTo cF.blocksInOrder b →
      Q.fixed (.own j) ≤ roundsTo cF.blocksInOrder b)
    (Sc : ∀ w g p blk, g < 12 → (P5J.At.X Zp).A[g]? = some p →
      cF.blocksInOrder[K5.borderOf g]? = some blk →
      K5.K5Script (lettersHead a.head A.H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w).thread
        (K5.borderOf g) cells (K5.seatOf keyOf Zp A.G cF g p) p blk
        (a.head.𝔇.pubD.N.sent (2 * g + 1) 0) (seatTab a.head.𝔇.cs a.head.𝔇.arr a.head.𝔇.ms))
    (hI : ∀ g p, (P5J.At.X Zp).A[g]? = some p →
      K5.IdnOwed Vd cells (K5.seatOf keyOf Zp A.G cF g p)) :
    ∀ w g, g < 12 →
      (PlaysS (lettersHead a.head A.H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w).thread
          (Said w) (K5.borderOf g) ∧
        BehindS (lettersHead a.head A.H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w).thread
          (Said w) (K5.borderOf g) ∧
        ExchangeS (lettersHead a.head A.H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w).thread
          (Said w) (K5.borderOf g) ∧
        RidesPastS (lettersHead a.head A.H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w).thread
          (Said w) (K5.borderOf g)) ∧
      ∀ fl, AcceptedS
        (lettersHead a.head A.H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w).thread
        (Said w) fl (K5.borderOf g) :=
  fun w => k5_through a Q test carryX item n₁ n₂ b₀ Vd cs Kp w (Said w) hlots hmore hKp hcs hK hfix
    (Sc w) fun g p hp v hv => hI g p hp v hv.2

end

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.k5Keeps_st_out
#print axioms ProofFile.Honest.FirstThread.ansReadsRest_head
#print axioms ProofFile.Honest.FirstThread.ansOn_head
#print axioms ProofFile.Honest.FirstThread.k5_through
#print axioms ProofFile.Honest.FirstThread.k5_through_all
