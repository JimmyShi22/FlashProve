-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/KeptAnswers.lean: the kind "the code switch" (K2): WHERE THE
THREAD's INVARIANT HOLDS IN FRONT OF A SWITCH, EACH KEPT MESSAGE OF THE CLOSED GROUP HAS, IN THE
WITNESS's WORDS, THE ANSWERS OF THE SAMPLE THAT THE STATEMENT HOLDS: the premise hAns of
`stored_of_answers` (StoredOfAnswers.lean of this folder), paid out of the thread's open item
"pinKept". A definition: a public test. Closed facts by Lean's kernel, with controls; statements
with their proofs.

WHICH SLOT IT IS FOR. The field stored of the record `MadeAsks` (ExchangeAtMade.lean), through
`stored_of_answers`.

  `keptSeatsB`, `keptSeatsW`, `keptSeatsW_can_fail`   THE WRITTEN PLAN: at each link l below 25,
                    each member of the written list with the flag "kept" has a seat in the table's
                    list of link l's kept seats, and the plan has at that seat a sampled entry of
                    that member's shape; at the table's next list: no
  `k2_pinKept_open`, `k2_pinKept_at`   the item "pinKept (p.link - 1)" is open in front of each of
                    the 25 numbers; a control: "pinKept p.link" in front of none
  `kept_index`      a kept message of the carried rows is a member of the written list with its flag
  `ans_move`        the same sample's equation at a second spelling of the codes, the shape and the
                    statement
  `kept_answers`    THE END

By: `P5T.memsSame_atR` (Johnson/P5T/MembersByMake.lean) · `smpNamed_at`, `smpAt_congr`
(Johnson/Desc/Sound/) · `AtMg.seats`, `AtMg.N_six` (Johnson/P5T/CoreAtMg.lean) · `FrontFacts`
(LockAsksAtArms.lean of this folder).

Limits. hT IS A PREMISE: that the thread stands in front of the switch; and so that the item is open
there with its meaning: what pays it is the closing's exchange, upstream of this file. F, hN and hst
ARE PREMISES: `head_frontFacts`, `fin_frontFacts` give F at the two arms; no value at a link's front
is made here. One run's coins: the witness's words at them: never quoted for a law. The full size;
the format's second hash function. CLOSED FACTS BY LEAN's KERNEL, REPLAYED BY NO INDEPENDENT CHECKER.
NOT IN FRONT OF A LAW OVER COINS. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.StoredOfAnswers
import Johnson.Desc.ProofFile.Honest.K2.Law.LockAsksAtArms
import Johnson.Desc.ProofFile.Honest.K2.Law.ExchangeByKind
import Johnson.Desc.Sound.SmpShared
import Johnson.P5T.MembersByMake
import Johnson.P5T.CoreAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K2.Law
open OnBytes
open OnBytes.Slice (GE)
open OnBytes.Means (Words)
open Johnson.Pack (portOmZ portCode partZ locZ)
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.First (Item start)
open VerifiableInference.Desc.First.Close (seatK10 noK10)
open VerifiableInference.Desc.LinkJoin (loAt kbW)
open VerifiableInference.Desc.K1 (smpAt)
open VerifiableInference.Desc.K2.Honest (GroupMember membersTrue)
open VerifiableInference.Desc.Sound (MsgT SitsAt msgsOf numAt smpNamed_at wordsFirst smpAt_congr)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script lettersHead head_pin)

/-- A PUBLIC TEST ON THE WRITTEN PLAN. d: 0 is the test; 1 asks at the next list, for a control. -/
def keptSeatsB (d : Nat) : Bool :=
  (List.range 25).all fun l =>
    (VerifiableInference.Desc.First.Close.membersOf (loAt l)).all fun i =>
      !kbW l i || (((P5T.N0Full.keptOf (l + d)).contains (seatK10 (loAt l) P5T.psFull l i)) &&
        P5T.psFull.any fun p => p.smpd && p.seat == seatK10 (loAt l) P5T.psFull l i &&
          decide (p.shape = ((loAt l).get i).1))

set_option maxRecDepth 1000000 in
/-- BY LEAN's KERNEL. -/
theorem keptSeatsW : keptSeatsB 0 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control. -/
theorem keptSeatsW_can_fail : keptSeatsB 1 = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- BY LEAN's KERNEL: the item is open in front of each of the 25 numbers, and each has a link from
1 to 25; a control: the next link's item is open in front of none. -/
theorem k2_pinKept_open :
    (placesW.all fun p =>
      (fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps) (switchNo p)).contains
        (Item.pinKept (p.link - 1)) && decide (1 ≤ p.link) && decide (p.link ≤ 25)) = true ∧
    (placesW.any fun p =>
      (fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps) (switchNo p)).contains
        (Item.pinKept p.link)) = false := by
  decide +kernel

theorem k2_pinKept_at {p : SwitchPlace} (hp : p ∈ placesW) :
    Item.pinKept (p.link - 1) ∈
        fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps) (switchNo p) ∧
      1 ≤ p.link ∧ p.link ≤ 25 := by
  have t := List.all_eq_true.1 k2_pinKept_open.1 p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at t
  exact ⟨List.contains_iff_mem.1 t.1.1, t.1.2, t.2⟩

/-- **A kept message of the carried rows is a member of the written list with its flag.** no: the
members' numbers. -/
theorem kept_index {S : Statement} {old : SingleRows} {l : Nat}
    {no : Fin (loAt l).length → Nat}
    (hN : old.layout.members.toList =
      (VerifiableInference.Desc.First.Close.membersOf (loAt l)).map no)
    (hT : membersTrue S old = (VerifiableInference.Desc.First.Close.membersOf (loAt l)).map fun i =>
      (⟨((loAt l).get i).1, kbW l i⟩ : GroupMember))
    {o : Nat} (ho : o ∈ (switchKept old).toList) :
    ∃ i ∈ VerifiableInference.Desc.First.Close.membersOf (loAt l), kbW l i = true ∧ no i = o := by
  unfold switchKept at ho
  rw [Array.toList_map, Array.toList_filter] at ho
  obtain ⟨pr, hpr, rfl⟩ := List.mem_map.1 ho
  obtain ⟨hz, hk⟩ := List.mem_filter.1 hpr
  obtain ⟨w', hw⟩ := List.getElem?_of_mem hz
  have h1 : (membersTrue S old)[w']? =
      some (⟨(S.oracles.getD pr.1 default).shape, pr.2⟩ : GroupMember) := by
    unfold membersTrue
    rw [List.getElem?_map, hw]
    rfl
  rw [hT, List.getElem?_map] at h1
  cases hi : (VerifiableInference.Desc.First.Close.membersOf (loAt l))[w']? with
  | none =>
    rw [hi] at h1
    cases h1
  | some i =>
    rw [hi] at h1
    have e2 : kbW l i = pr.2 := congrArg GroupMember.kept (Option.some.inj h1)
    refine ⟨i, List.mem_of_getElem? hi, e2.trans (by simpa using hk), ?_⟩
    rw [Array.toList_zip, List.getElem?_zip_eq_some] at hw
    have h2 := hw.1
    rw [hN, List.getElem?_map, hi] at h2
    exact Option.some.inj h2

/-- **The same sample's equation, at a second spelling of the codes, the shape and the statement.**
-/
theorem ans_move {cs cs' : Codes} (hc : cs' = cs) {sh sh' : OracleShape} (hs : sh' = sh) {e : Nat}
    {St St' : Statement} {o : Nat} (hst : St'.oracles = St.oracles)
    {z : (portOmZ cs sh e).Smp} (hz : smpAt cs sh e St o = some z)
    {m : (portCode cs sh).J → GE} (hv : (portOmZ cs sh e).Z.val z.1 m = z.2)
    {wd : OnBytes.Part → Nat → GE} (hm : ∀ j, m j = wd (partZ cs sh j) (locZ cs sh j)) :
    ∃ z' : (portOmZ cs' sh' e).Smp, smpAt cs' sh' e St' o = some z' ∧
      (portOmZ cs' sh' e).Z.val z'.1 (fun j => wd (partZ cs' sh' j) (locZ cs' sh' j)) = z'.2 := by
  subst hc hs
  refine ⟨z, ?_, ?_⟩
  · rw [smpAt_congr cs' sh' e St St' o (by rw [hst])]
    exact hz
  · have e' : m = fun j => wd (partZ cs' sh' j) (locZ cs' sh' j) := funext hm
    subst e'
    exact hv

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}

/-- hT, F, hN AND hst ARE PREMISES; it stands under the head's premise too. One run's coins: never
quoted for a law. **Each kept message has, in the witness's words, the answers of the sample that
the statement holds.** The end is the premise hAns of `stored_of_answers`, at S := fx.st. -/
theorem kept_answers (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → ProofFile.Honest.FirstThread.WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr) {p : SwitchPlace} (hp : p ∈ placesW) {k : Coins Bk} {s : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (switchNo p) k s m E)
    {book : TreeBook} {fx : _root_.Tw.K2.Front} (F : FrontFacts Zp (p.link - 1) book fx)
    (hN : membersTrue fx.st fx.f.rows =
      (VerifiableInference.Desc.First.Close.membersOf (loAt (p.link - 1))).map fun i =>
      (⟨((loAt (p.link - 1)).get i).1, kbW (p.link - 1) i⟩ : GroupMember))
    (hst : fx.st.oracles = s.st.oracles) (ds : List Fmt.Drawn)
    {o : Nat} (ho : o ∈ (switchKept fx.f.rows).toList) (xo : Oracle)
    (hxo : fx.st.oracles[o]? = some xo) :
    ∃ (e : Nat) (z : (portOmZ fx.st.codes xo.shape e).Smp),
      smpAt fx.st.codes xo.shape e fx.st o = some z ∧
      (portOmZ fx.st.codes xo.shape e).Z.val z.1
        (fun j => wordsFirst (P5J.At.arr Zp) fx.st book (Q.wit k m.st.input (m.st.heard ++ ds)) o
          (partZ fx.st.codes xo.shape j) (locZ fx.st.codes xo.shape j)) = z.2 := by
  obtain ⟨hopen, h1, h25⟩ := k2_pinKept_at hp
  obtain ⟨i, hi, hk, rfl⟩ := kept_index F.numbered hN ho
  have hseats : P5J.At.pseats Zp = P5T.psFull := h.toAtMg.seats
  have hK : (P5J.At.N Zp cF).keptOf = P5T.N0Full.keptOf := h.toAtMg.N_six.2.1
  have t := List.all_eq_true.1 (List.all_eq_true.1 keptSeatsW (p.link - 1)
    (List.mem_range.2 (by omega))) i hi
  rw [hk] at t
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, Nat.add_zero] at t
  obtain ⟨c1, c2⟩ := t
  obtain ⟨p₁, hp₁, hq⟩ := List.any_eq_true.1 c2
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hq
  obtain ⟨⟨s1, s2⟩, s3⟩ := hq
  rw [← hseats] at s2 c1
  have hmem : seatK10 (loAt (p.link - 1)) (P5J.At.pseats Zp) (p.link - 1) i ∈
      (P5J.At.N Zp cF).keptOf (p.link - 1) := by
    rw [hK]
    exact List.contains_iff_mem.1 c1
  have hI : ∀ q ∈ (P5J.At.N Zp cF).keptOf (p.link - 1),
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mg m.st.input).pin q.1 q.2
        ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.seat k m s)
        ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E)
        (Q.wit k m.st.input (m.st.heard ++ ds)) :=
    hT.2.2.2.1 ds (Item.pinKept (p.link - 1)) hopen
  have hA := hI _ hmem
  rw [head_pin] at hA
  have hy : (p₁.shape, p₁.seat) ∈ ((P5T.planSeats Zp Zp.D.1).filter (·.smpd)).map
      fun q => (q.shape, q.seat) :=
    List.mem_map.2 ⟨p₁, List.mem_filter.2 ⟨by rw [h.toAtMg.seats]; exact hp₁, s1⟩, rfl⟩
  obtain ⟨y, hy₁, ey⟩ := List.mem_map.1 ((P5T.memsSame_atR Zp (P5J.At.rad Zp Z.lay) _).2 hy)
  have e1 : (y.1.l.get y.2).1 = p₁.shape := congrArg Prod.fst ey
  have e2 : VerifiableInference.Desc.Sound.seatOf y = p₁.seat := congrArg Prod.snd ey
  have eq₁ : VerifiableInference.Desc.Sound.seatOf y =
      seatK10 (loAt (p.link - 1)) (P5J.At.pseats Zp) (p.link - 1) i := e2.trans s2
  obtain ⟨z, hz, hv⟩ := hA.2 y hy₁ eq₁
  have hsq : y.1.seat y.2 ∈ P5J.At.seats Zp := by
    show VerifiableInference.Desc.Sound.seatOf y ∈
      (P5J.At.pseats Zp).map fun q => (q.j, q.t)
    rw [e2, hseats]
    exact List.mem_map.2 ⟨p₁, hp₁, rfl⟩
  have hz' : smpAt (P5J.At.cs Zp) (y.1.l.get y.2).1 (y.1.l.get y.2).2 s.st
      (noK10 (P5J.At.seats Zp) (loAt (p.link - 1)) (P5J.At.pseats Zp) (p.link - 1) i) =
        some z := by
    have e3 := smpNamed_at (P5J.At.cs Zp) (P5J.At.seats Zp)
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.seat k m s) y.1 y.2 hsq
    have e4 : numAt (P5J.At.seats Zp) ⟨y.1, y.2⟩ =
        noK10 (P5J.At.seats Zp) (loAt (p.link - 1)) (P5J.At.pseats Zp) (p.link - 1) i := by
      show (P5J.At.seats Zp).idxOf (VerifiableInference.Desc.Sound.seatOf y) = _
      rw [eq₁]
      rfl
    rw [e4] at e3
    exact e3.symm.trans hz
  have hsh : xo.shape = (y.1.l.get y.2).1 := by
    have g : fx.st.oracles.getD
        (noK10 (P5J.At.seats Zp) (loAt (p.link - 1)) (P5J.At.pseats Zp) (p.link - 1) i) default =
        xo := by
      rw [Array.getD_eq_getD_getElem?, hxo]
      rfl
    have := F.shape i hi
    rw [g] at this
    rw [this, e1, s3]
  have hc : fx.st.codes = P5J.At.cs Zp := F.ties.codes
  have key : ∀ (part : OnBytes.Part) (b c : Nat), b < (y.1.l.get y.2).1.rows part →
      (Q.wit k m.st.input (m.st.heard ++ ds)).tab (P5J.At.cs Zp) (y.1.l.get y.2).1
        (P5J.At.arr Zp (y.1.seat y.2).1 (y.1.seat y.2).2) (y.1.seat y.2).1 (y.1.seat y.2).2
        (part == .mask) b c =
      wordsFirst (P5J.At.arr Zp) fx.st book (Q.wit k m.st.input (m.st.heard ++ ds))
        (noK10 (P5J.At.seats Zp) (loAt (p.link - 1)) (P5J.At.pseats Zp) (p.link - 1) i) part
        (b + 2 ^ ceilLog2 ((y.1.l.get y.2).1.rows part) * c) := by
    intro part b c hb
    have es : (y.1.l.get y.2).1 = ((loAt (p.link - 1)).get i).1 := e1.trans s3
    rw [es] at hb ⊢
    have := F.word i hi (P5J.At.arr Zp) (Q.wit k m.st.input (m.st.heard ++ ds)) part hb c
    rw [Nat.mul_comm c, hc] at this
    show _ = _
    rw [this]
    have e5 : y.1.seat y.2 = seatK10 (loAt (p.link - 1)) (P5J.At.pseats Zp) (p.link - 1) i := eq₁
    rw [e5]
  exact ⟨(y.1.l.get y.2).2, ans_move hc hsh hst hz' hv (fun j => by
    rcases j with q | q
    · exact key .main q.1.val q.2.val q.1.isLt
    · exact key .mask q.1.val q.2.val q.1.isLt)⟩

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.keptSeatsB
#print axioms ProofFile.Honest.K2.Law.keptSeatsW
#print axioms ProofFile.Honest.K2.Law.keptSeatsW_can_fail
#print axioms ProofFile.Honest.K2.Law.k2_pinKept_open
#print axioms ProofFile.Honest.K2.Law.k2_pinKept_at
#print axioms ProofFile.Honest.K2.Law.kept_index
#print axioms ProofFile.Honest.K2.Law.ans_move
#print axioms ProofFile.Honest.K2.Law.kept_answers
