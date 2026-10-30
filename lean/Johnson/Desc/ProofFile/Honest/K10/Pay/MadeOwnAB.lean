-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/MadeOwnAB.lean: the closing of a segment (K10): the test `ownHeard` (Honest/K2/AtPlan.lean)
on what was heard, at the filling `withSwitchData S (K1.lotData S)`, split by the four fillings that the address picks. Two of
the four read no challenge: the switches' own messages and the opening.

  `OwnAddr`           an address of an own message of these segments
  `ownHeard_of_ready` the test says yes where each such address is ready
  `ownHeard_of_four`  the test from one premise for each of the four fillings
  `allFit`            a test on public data: the layout has a list for each segment and every message fits
  `laid_ready`        a filling of cells is ready at every list of challenges, at a seat into the messages of a shape that
                      passes `allFit`
  `switch_ready`, `first_ready`   so the switches' own messages and the opening are ready
  `ownHeard_of_two`   the test from the two premises on the digits and the reads

Limits. Nothing here shows the premises on the digits and the reads at any list of challenges. `allFit` is a premise here.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.MadeParts
import Johnson.Desc.ProofFile.Honest.K2.Law.LightByAddress

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes.HonestTrace (Sz seatsOf mineOf)
open OnBytes.HonestTrace.U3 (u3RowsOf)
open OnBytes.Params (ReqShape ReqLayout)
open ProofFile.Honest.K2 (SegmentPub ownHeard withSwitchData switchData switchSeat seatBy mineSwitch mineFirst mineDigits mineReads)

/-- An address of an own message of these segments. -/
def OwnAddr (addrs : Nat → Nat → Option MsgAddr) (segs : List SegmentPub) (a : MsgAddr) : Prop :=
  ∃ y ∈ segs.zipIdx, ∃ s ∈ (y.1.ownShapes (y.2 == 0)).zipIdx, addrs y.2 s.2 = some a

/-- The test says yes where each address of an own message is ready. -/
theorem ownHeard_of_ready {D : RowData} {addrs : Nat → Nat → Option MsgAddr} {segs : List SegmentPub}
    {heard : List Fmt.Drawn} (h : ∀ a, OwnAddr addrs segs a → D.readyAt heard a = true) :
    ownHeard D (askPlace addrs) segs heard = true := by
  unfold ownHeard
  refine List.all_eq_true.2 fun y hy => List.all_eq_true.2 fun s hs => ?_
  show ((addrs y.2 s.2).map (D.readyAt heard)).getD true = true
  cases e : addrs y.2 s.2 with
  | none => rfl
  | some a => exact h a ⟨y, hy, s, hs, e⟩

/-- What `RowData.join` is ready at: the chosen part's. -/
theorem join_ready (mine : MsgAddr → Bool) (A B : RowData) (hd : List Fmt.Drawn) (a : MsgAddr) :
    (RowData.join mine A B).readyAt hd a = if mine a then A.readyAt hd a else B.readyAt hd a := by
  unfold RowData.readyAt RowData.heardOk RowData.join
  cases h : mine a <;> simp [h]

/-- **The test from one premise for each of the four fillings.** -/
theorem ownHeard_of_four {S : Sz} {Z : ProofFile.Pub} {G : ProofFile.Ground} {x : ProofFile.Inst}
    {addrs : Nat → Nat → Option MsgAddr} {segs : List SegmentPub} {heard : List Fmt.Drawn}
    (h1 : ∀ a, OwnAddr addrs segs a → mineSwitch Z G a = true → (switchData S Z G).readyAt heard a = true)
    (h2 : ∀ a, OwnAddr addrs segs a → mineFirst Z G a = true → (K1.firstFill S G.first).readyAt heard a = true)
    (h3 : ∀ a, OwnAddr addrs segs a → mineDigits Z G a = true →
      (K1.digitsFill Z G (K3.matsOwn G.W)).readyAt heard a = true)
    (h4 : ∀ a, OwnAddr addrs segs a → mineReads Z G a = true → (u3RowsOf Z G x).readyAt heard a = true) :
    ownHeard (withSwitchData S (K1.lotData S) Z G x) (askPlace addrs) segs heard = true := by
  refine ownHeard_of_ready fun a ha => ?_
  show (RowData.join (fun a => (switchSeat Z G a).isSome) (switchData S Z G) (K1.lotData S Z G x)).readyAt heard a = true
  rw [join_ready]
  cases c1 : (switchSeat Z G a).isSome with
  | true =>
    exact h1 a ha c1
  | false =>
    have n1 : mineSwitch Z G a = false := c1
    show (K1.lotData S Z G x).readyAt heard a = true
    show (RowData.join (fun a => a.sender == K1.firstAddr) (K1.firstFill S G.first)
      (RowData.join (mineOf (seatsOf Z G "BZ")) (K1.digitsFill Z G (K3.matsOwn G.W)) (u3RowsOf Z G x))).readyAt
        heard a = true
    rw [join_ready]
    cases c2 : (a.sender == K1.firstAddr) with
    | true =>
      exact h2 a ha (by unfold mineFirst; rw [n1, c2]; rfl)
    | false =>
      show (RowData.join (mineOf (seatsOf Z G "BZ")) (K1.digitsFill Z G (K3.matsOwn G.W))
        (u3RowsOf Z G x)).readyAt heard a = true
      rw [join_ready]
      cases c3 : mineOf (seatsOf Z G "BZ") a with
      | true =>
        exact h3 a ha (by unfold mineDigits; rw [n1, c2, c3]; rfl)
      | false =>
        exact h4 a ha (by unfold mineReads; rw [n1, c2, c3]; rfl)

/-- The layout has a list for each segment, and every message of every segment fits. -/
def allFit (codes : OnBytes.Codes) (s : ReqShape) (lay : ReqLayout) : Bool :=
  layFits s lay && (List.range s.link.length).all fun l =>
    (List.range (s.link.getD l default).messages.length).all fun m => msgFits codes s lay l m

/-- The number that `msgNo` returns is that of a message of the segment. -/
theorem msgNo_fit {codes : OnBytes.Codes} {s : ReqShape} {lay : ReqLayout} (hf : allFit codes s lay = true)
    {l t k m : Nat} (h : msgNo s l t k = some m) : msgFits codes s lay l m = true := by
  unfold allFit at hf
  rw [Bool.and_eq_true] at hf
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 h
  have hy' := List.mem_of_getElem? hy
  have hz := (List.mem_filter.1 hy').1
  have hm : y.2 < (s.link.getD l default).messages.length := by
    have := (List.mem_zipIdx_iff_getElem?.1 hz)
    exact (List.getElem?_eq_some_iff.1 this).1
  have hl : l < s.link.length := by
    by_contra c
    have e : s.link.getD l default = default := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
    rw [e] at hm
    exact absurd hm (by simp [show (default : OnBytes.Params.ReqLink).messages = [] from rfl])
  exact List.all_eq_true.1 (List.all_eq_true.1 hf.2 l (List.mem_range.2 hl)) y.2 (List.mem_range.2 hm)

/-- **A filling of cells is ready at every list of challenges**, at a seat into the messages of a shape that passes
`allFit`. -/
theorem laid_ready {S : Sz} {codes : OnBytes.Codes} {s : ReqShape} {lay : ReqLayout}
    {seat : MsgAddr → Option (Nat × Nat)} (hf : allFit codes s lay = true)
    (hs : ∀ a l m, seat a = some (l, m) → ∃ t k, msgNo s l t k = some m) (hd : List Fmt.Drawn) (a : MsgAddr) :
    (K1.firstData S codes s lay seat fun _ => 0).readyAt hd a = true := by
  have hl : layFits s lay = true := (Bool.and_eq_true _ _ ▸ hf).1
  show (decide (0 ≤ hd.length) && (seat a).all (fun x => layFits s lay && msgFits codes s lay x.1 x.2 && true)) = true
  cases e : seat a with
  | none => simp
  | some x =>
    obtain ⟨l, m⟩ := x
    obtain ⟨t, k, hk⟩ := hs a l m e
    simp [hl, msgNo_fit hf hk]

/-- The seat of a moment names a message of the shape. -/
theorem moment_seat {s : ReqShape} {sender : Addr} {l₀ t fr : Nat} {a : MsgAddr} {l m : Nat}
    (h : K1.momentSeat s sender l₀ t fr a = some (l, m)) : ∃ t k, msgNo s l t k = some m := by
  unfold K1.momentSeat at h
  split at h
  · obtain ⟨m', hm, e⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    exact ⟨_, _, hm⟩
  · cases h

/-- **The switches' own messages are ready at every list of challenges.** -/
theorem switch_ready {S : Sz} {Z : ProofFile.Pub} {G : ProofFile.Ground}
    (hf : allFit G.first.codes G.first.shape G.first.layout = true) (hd : List Fmt.Drawn) (a : MsgAddr) :
    (switchData S Z G).readyAt hd a = true := by
  refine laid_ready hf (fun a l m e => ?_) hd a
  obtain ⟨x, -, hx⟩ := List.exists_of_findSome?_eq_some e
  exact moment_seat hx

/-- **The opening is ready at every list of challenges.** -/
theorem first_ready {S : Sz} {q : OnBytes.Params.First} (hf : allFit q.codes q.shape q.layout = true)
    (hd : List Fmt.Drawn) (a : MsgAddr) : (K1.firstFill S q).readyAt hd a = true :=
  laid_ready hf (fun _ _ _ e => moment_seat e) hd a

/-- **The test from the two premises on the digits and the reads.** -/
theorem ownHeard_of_two {S : Sz} {Z : ProofFile.Pub} {G : ProofFile.Ground} {x : ProofFile.Inst}
    {addrs : Nat → Nat → Option MsgAddr} {segs : List SegmentPub} {heard : List Fmt.Drawn}
    (hf : allFit G.first.codes G.first.shape G.first.layout = true)
    (h3 : ∀ a, OwnAddr addrs segs a → mineDigits Z G a = true →
      (K1.digitsFill Z G (K3.matsOwn G.W)).readyAt heard a = true)
    (h4 : ∀ a, OwnAddr addrs segs a → mineReads Z G a = true → (u3RowsOf Z G x).readyAt heard a = true) :
    ownHeard (withSwitchData S (K1.lotData S) Z G x) (askPlace addrs) segs heard = true :=
  ownHeard_of_four (fun a _ _ => switch_ready hf heard a) (fun a _ _ => first_ready hf heard a) h3 h4

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.OwnAddr
#print axioms ProofFile.Honest.K10.ownHeard_of_ready
#print axioms ProofFile.Honest.K10.join_ready
#print axioms ProofFile.Honest.K10.ownHeard_of_four
#print axioms ProofFile.Honest.K10.allFit
#print axioms ProofFile.Honest.K10.msgNo_fit
#print axioms ProofFile.Honest.K10.laid_ready
#print axioms ProofFile.Honest.K10.moment_seat
#print axioms ProofFile.Honest.K10.switch_ready
#print axioms ProofFile.Honest.K10.first_ready
#print axioms ProofFile.Honest.K10.ownHeard_of_two
