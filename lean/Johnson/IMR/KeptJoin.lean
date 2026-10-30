-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/KeptJoin.lean: THE OLD MESSAGES THAT THE CODE SWITCHING INTO GROUP l
KEEPS ARE THE WRITTEN NUMBERS oldsAt l (Johnson/Top/H0/K2Hears/PlaceNums.lean): A LAW WITH TWO NAMED
PREMISES: at the links' code switchings, 1 ≤ l ≤ 23.
  sgain, ogain, gain_eq: kind K2's two lists as functions of the number of messages, the
    target and the link's messages of moment 0.
  keptNums sh l n₀, keptZero sh n₀: the numbers with a true flag, as functions of the request's
    shape: what Johnson/IMR/GroupKept.lean's kept_next and Johnson/IMR/GroupZero.lean's kept_one end
      in.
  kept_values, kept_value_zero: THE CLOSED HALF, by Lean's kernel: at the written shape
    (proofSizedFull.request) and the written numbers of messages (n0At l):
    keptNums … l (n0At l) = oldsAt (l + 1) at l = 1 … 23; keptZero … (n0At 0) = oldsAt 1.
  kept_can_fail: a negative test.
  start_msgs: the first state has no message.
  kept_rows: WITHOUT EITHER PREMISE, from the fold's return alone: in front of the first
    sub-protocol of link l + 1, 1 ≤ l < 24: (switchKept ‹the walk's frame's carried rows›).toList =
    keptNums ‹the public shape› l ‹the number of messages in front of link l's code switching›.
  olds_rows: in front of the first sub-protocol of link l, 2 ≤ l ≤ 24: of the walk's frame's carried
    rows: (switchKept …).toList = oldsAt l. (At l = 24 that is the cut 338, in front of "H:1".)
  olds_at_link: THE TOP, 2 ≤ l ≤ 23: at the front fx that the text makes of the state in front of
    the code switching into group l: (switchKept fx.f.rows).toList = oldsAt l.
  olds_at_one: the like at l = 1.
THE TWO PREMISES: hsh: the public shape is the written one; hn: the number of messages in front of
the code switching into group l - 1 is n0At (l - 1) (at l = 1 no such premise: the first state has
none). NEITHER IS SHOWN HERE.
NOT HERE: the head's (l = 24) and the finish's (l = 25) fronts: that the head's own copy of the
frame takes the walk's frame's carried rows over.
OBJECT: ProofFile.onlineDescription's value at OnBytes.secondHashFunction, in scope. USER: kind K2's files.
The premises are laws' premises: that a fold returns is shown of no proof here. No soundness.
-/
import Johnson.IMR.GroupZero
import Johnson.Top.H0.K2Hears.PlaceNums

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open OnBytes.Params (ReqShape ReqMessage)
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.PlanWritten (proofSizedFull)
open ProofFile (Cl)

/-- The code switching's main message and kept copies, with their flags. -/
def sgain (n : Nat) (T : SwitchTarget) : List (Nat × Bool) :=
  (n, false) ::
    (((List.range T.kept.size).map (· + (n + 1))).zip T.kept.toList).map
      fun p => (p.1, p.2.keptAgain)

/-- The link's own messages of moment 0, with their flags. -/
def ogain (n K : Nat) (own : List ReqMessage) : List (Nat × Bool) :=
  (own.zip ((List.range own.length).map (· + (n + (1 + K))))).map
    fun y => (y.2, decide (0 < y.1.life))

theorem gain_eq (x : _root_.Tw.K2.Front) :
    K2.switchGain x ++ K2.ownGain x =
      sgain x.st.oracles.size x.T ++ ogain x.st.oracles.size x.T.kept.size x.own := rfl

/-- What the code switching into group l + 1 keeps, l ≥ 1, of the shape and the number of messages
in front of the switching into group l. -/
def keptNums (sh : ReqShape) (l n₀ : Nat) : List Nat :=
  ((sgain n₀ (K2.targetAt sh l) ++
    ogain n₀ (K2.targetAt sh l).kept.size ((K2.frameAtLink sh l).atMoment 0)).filter (·.2)).map
      (·.1)

/-- What the code switching into group 1 keeps. -/
def keptZero (sh : ReqShape) (n₀ : Nat) : List Nat :=
  ((((List.range ((K2.frameAtLink sh 0).atMoment 0).length).map (· + n₀)).zip
    (((K2.frameAtLink sh 0).atMoment 0).map fun x => decide (0 < x.life))).filter (·.2)).map (·.1)

set_option maxRecDepth 1000000 in
/-- **THE CLOSED HALF.** -/
theorem kept_values : ((List.range' 1 23).all fun l =>
    decide (keptNums proofSizedFull.request l (K2.n0At l) = K2.oldsAt (l + 1))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem kept_value_zero : keptZero proofSizedFull.request (K2.n0At 0) = K2.oldsAt 1 := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: at a number of messages one higher the equation is false. -/
theorem kept_can_fail : keptNums proofSizedFull.request 1 (K2.n0At 1 + 1) ≠ K2.oldsAt 2 := by
  decide +kernel

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- The first state has no message. -/
theorem start_msgs {o : ProofFile.SecondHashFunctionArgument} {pol KL : ByteArray}
    (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z) (p : ProofFile.InstPub) :
    (ProofFile.startS Z p).st.oracles = #[] := by
  have e : Z.s₀.st.oracles = #[] := by
    have k := pub_start hZ
    unfold S.startP at k
    split at k
    · rw [← Option.some.inj k]
      rfl
    · cases k
  unfold ProofFile.startS
  dsimp only
  split
  · exact e
  · rfl

/-- **WITHOUT A PREMISE ON THE SHAPE OR A COUNT: THE WALK's FRAME's CARRIED ROWS IN FRONT OF THE
FIRST SUB-PROTOCOL OF LINK l + 1, 1 ≤ l < 24**: what they keep, as a function of the public shape
and of the number of messages in front of link l's code switching. -/
theorem kept_rows (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h1 : 1 ≤ l)
    (h24 : l < 24) {p : ProofFile.InstPub}
    {R R₀ R₂ : List Fmt.RoundView} {C C₀ C₂ : List VerifiableInference.Desc.OpenedColumn} {t₀ t₂ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 2)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀))
    (f₂ : foldBlocks 0 (c.blocksInOrder.take (14 * (l + 1) + 2)) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂)) :
    (switchKept t₂.check.frame.rows).toList = keptNums Z.first.shape l t₀.st.oracles.size := by
  obtain ⟨x, hx, ek⟩ := kept_next hS hR O h1 h24 f₀ f₂
  obtain ⟨hB, hk⟩ := laid_at hS hR O (by omega : l < 25) f₀
  have Rr : RecAll Z.first.codes Z.first.shape t₀ := open_recAll hS hR O (by omega)
    (by have k := draw_in_front hS hR O (l := l) (i := 0) (by omega) (by decide); omega) f₀
  obtain ⟨-, -, c2, -⟩ := K2.link_front hx
  obtain ⟨n1, -, -⟩ := K2.link_notices hx Rr.walk hk
  obtain ⟨L0, G0, S0, g, a⟩ := (_root_.Tw.K2.firstFront_iff _ _ _).1 hx
  have eo : x.own = (K2.frameAtLink Z.first.shape l).atMoment 0 := by
    rw [a.out]
    exact K2.atMoment_pub Rr.walk hk 0
  rw [ek, gain_eq, n1, eo, c2]
  rfl

/-- **THE SAME AT THE WRITTEN SHAPE AND COUNT.** -/
theorem olds_rows (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h1 : 1 ≤ l)
    (h24 : l < 24) (hsh : Z.first.shape = proofSizedFull.request) {p : ProofFile.InstPub}
    {R R₀ R₂ : List Fmt.RoundView} {C C₀ C₂ : List VerifiableInference.Desc.OpenedColumn} {t₀ t₂ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 2)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀))
    (hn : t₀.st.oracles.size = K2.n0At l)
    (f₂ : foldBlocks 0 (c.blocksInOrder.take (14 * (l + 1) + 2)) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂)) :
    (switchKept t₂.check.frame.rows).toList = K2.oldsAt (l + 1) := by
  rw [kept_rows hS hR O h1 h24 f₀ f₂, hn, hsh]
  have k := List.all_eq_true.1 kept_values l (by rw [List.mem_range'_1]; omega)
  exact of_decide_eq_true k

/-- **AT THE CODE SWITCHING INTO GROUP l + 1, 1 ≤ l < 23.** -/
theorem olds_at_link (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h1 : 1 ≤ l)
    (h23 : l < 23) (hsh : Z.first.shape = proofSizedFull.request) {p : ProofFile.InstPub}
    {R R₀ R₂ : List Fmt.RoundView} {C C₀ C₂ : List VerifiableInference.Desc.OpenedColumn} {t₀ t₂ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 2)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀))
    (hn : t₀.st.oracles.size = K2.n0At l)
    (f₂ : foldBlocks 0 (c.blocksInOrder.take (14 * (l + 1) + 2)) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂))
    {q : K2.P2} (hq : q.stands = .link) {fx : _root_.Tw.K2.Front}
    (h : K2.frontAt q t₂ = some fx) : (switchKept fx.f.rows).toList = K2.oldsAt (l + 1) := by
  obtain ⟨-, -, -, -, -, er, -⟩ := front_pin_link hS hR O (by omega : 1 ≤ l + 1) (by omega) f₂ hq h
  rw [er]
  exact olds_rows hS hR O h1 (by omega) hsh f₀ hn f₂

/-- **AT THE CODE SWITCHING INTO GROUP 1.** -/
theorem olds_at_one (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hsh : Z.first.shape = proofSizedFull.request) {p : ProofFile.InstPub}
    {R R₂ : List Fmt.RoundView} {C C₂ : List VerifiableInference.Desc.OpenedColumn} {t₂ : S}
    (f₂ : foldBlocks 0 (c.blocksInOrder.take (14 * (0 + 1) + 2)) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂))
    {q : K2.P2} (hq : q.stands = .link) {fx : _root_.Tw.K2.Front}
    (h : K2.frontAt q t₂ = some fx) : (switchKept fx.f.rows).toList = K2.oldsAt 1 := by
  obtain ⟨-, -, -, -, -, er, -⟩ := front_pin_link hS hR O (by omega : 1 ≤ 0 + 1) (by omega) f₂ hq h
  have ek := kept_one hS hR O f₂
  obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_cut (k := 14 * 0 + 2) 14 f₂
  have e0s := laid_is_start hS hR O f₀
  obtain ⟨hB, hk⟩ := laid_at hS hR O (by omega : 0 < 25) f₀
  have Rr : RecAll Z.first.codes Z.first.shape t₀ := open_recAll hS hR O (by omega)
    (by have k := draw_in_front hS hR O (l := 0) (i := 0) (by omega) (by decide); omega) f₀
  have eo : (ProofFile.startS Z p).check.frame.atMoment 0 =
      (K2.frameAtLink Z.first.shape 0).atMoment 0 := by
    rw [← e0s]
    exact K2.atMoment_pub Rr.walk hk 0
  rw [er, ek, eo, start_msgs O.pub p, hsh]
  exact kept_value_zero

end

#print axioms kept_values
#print axioms kept_value_zero
#print axioms kept_can_fail
#print axioms kept_rows
#print axioms olds_rows
#print axioms olds_at_link
#print axioms olds_at_one

end Meaning.K2
