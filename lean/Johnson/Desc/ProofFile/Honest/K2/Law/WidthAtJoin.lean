-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/WidthAtJoin.lean: the kind "the code switch" (K2): ONE CLAUSE
OF "THE WIDTHS" (the premise hW of `switch_playsS`, Honest/K2/Law/PlaysScript.lean) WITHOUT
`PlayedTo`: at the first thread's letters at the library's head where the Script is the joined one
(`joinQ`), AT EACH SWITCH BUT THE FIRST (links 2 to 23, the head's switch, the last), AT THE TREE
THAT THE SWITCH IN FRONT SENT: the thread's table has the width that the numbers' list `read`
states. Three definitions; two closed facts by evaluation in Lean's kernel, each with a control
(`rootsFrontB` has none); four laws: joins of calls.

  `frontPairsW`     the 24 pairs, written: the switch in front, the later switch, the member
  `rootsFrontB`, `readFrontB`, `readFrontW`   THE TESTS, BY LEAN's KERNEL, at each pair: the switch
                    in front has a root, and one oracle message a root; each of its trees stands
                    once in the later switch's list, with that message's width: so no pair is
                    idle; a control of `readFrontB` alone: every width raised by one: no
  `frontSeatsW`     BY LEAN's KERNEL: at each pair one written place stands at the link in front, at
                    that number
  `roots_at_front`, `read_at_front`   these tests under the head
  `ownTreesAt_at_join`   the frame's form `OwnTreesAt` at the switch in front, at every `Said`
  `width_at_join`   THE CLAUSE, at that tree

By, ours: `share_trees_fit` (Honest/K2/JoinShare.lean) · `words_of_ownAt`
(Honest/K2/Law/WidthsOwn.lean) · `switchTable_at_plan` (TableWords.lean) · `borders_apart_at_head`,
`k2_member_at_head`, `k2_block_at_head` · `numsW_at_head`, `serves_at_head`, `roomy_at_head`,
`fits_at_head` (PublicAtHead.lean); of other authors: `ownTreesAt_of_own`
(Honest/Thread/ScriptLots.lean) · `borderNo_written` (Honest/K1/Law/MembersByBorder.lean); sealed,
ours: `places_at_head`, `treesTo_at_head` (PlacesWritten.lean). Of the other files named in this
head Honest/Thread/ScriptLots.lean and Honest/Small/WidthByPlay.lean alone are sealed. Kin, ours:
`link_width_own` (WidthsOwn.lean) · `readOwnW` (ReadOwn.lean): the links alone. Kin, of other
authors: `width_by_play`, `width_by_play_below` (Honest/Small/WidthByPlay.lean): the like end under
`PlayedTo`.

Limits. THE HEAD AND THE OPENING ARE HYPOTHESES: THIS FILE SHOWS THEM MET BY NOTHING: WHERE NOTHING
MEETS THEM THE LAWS THAT NAME THEM HOLD EMPTILY. F (the list is fit) AND hin (it holds the kind's
share) ARE PREMISES. ONE TREE OF THE THREE THAT A SWITCH READS: of the other two nothing is said
here. Premises here: at a stand: the book lends the part its coins · `publicOk` at the input's
public instance; on the plan: `closingOk` at the switch in front. NOT AT THE SWITCH AT LINK 1, which
reads no switch's tree. TWO CLOSED FACTS BY LEAN's KERNEL, REPLAYED BY NO INDEPENDENT CHECKER. On a
table's width: nothing on what it holds. A run's coins stand under "for all" and go whole to the
kind's table. NOT IN FRONT OF A LAW OVER COINS. The full size and the format's second hash function alone.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.ScriptAtJoin
import Johnson.Desc.ProofFile.Honest.K2.Law.WidthsOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place Strs)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First (treesTold)
open VerifiableInference.Desc.First.K2Ties (toldFull)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open IM (k2P)
open _root_.Desc.K14.Law (seatZ secondAt)
open ProofFile.Honest.FirstThread

/-- The switches, written as pairs: the link of the switch in front, the link of the later switch
(`none`: the last), the member's number of the switch in front. -/
def frontPairsW : List (Option Nat × Option Nat × Nat) :=
  (List.range 23).map (fun i => (some (i + 1), some (i + 2), 14 * (i + 1) + 2)) ++
    [(some 24, none, 339)]

/-- **A test at the switch in front**, at the written plan: it has a root, and one oracle message a
root. -/
def rootsFrontB : Bool :=
  frontPairsW.all fun x => (numsW x.1).any fun n' =>
    decide (0 < n'.roots) && (P1K2.oraclesAt n'.grp n'.codes n'.sent).length == n'.roots

/-- **The test**, at the written plan: each tree of the switch in front stands ONCE in the later
switch's list `read`, and there with that tree's width. shift: 0 is the test; another number is a
control. -/
def readFrontB (shift : Nat) : Bool :=
  frontPairsW.all fun x =>
    (numsW x.1).any fun n' => (numsW x.2.1).any fun n =>
      (List.range n'.roots).all fun j =>
        (n.read.filter fun t => t.1 == treesTold toldFull x.2.2 + j).length == 1 &&
        n.read.all fun t => t.1 != treesTold toldFull x.2.2 + j ||
          ((P1K2.oraclesAt n'.grp n'.codes n'.sent)[j]?).any fun o => o.words + shift == t.2.2

set_option maxRecDepth 1000000 in
/-- **Their yes, and a control**: with every width raised by one the second says no. -/
theorem readFrontW : rootsFrontB = true ∧ readFrontB 0 = true ∧ readFrontB 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **At each pair just one written place stands at the link in front, and it has that member's
number**; a control: at a number one further the like test says no. -/
theorem frontSeatsW : (frontPairsW.all fun x =>
      ((placesW.filter fun p => p.place.link == x.1).map switchNo) == [x.2.2]) = true ∧
    (frontPairsW.all fun x =>
      ((placesW.filter fun p => p.place.link == x.1).map switchNo) == [x.2.2 + 1]) = false := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : First.Look.Place} {Bs : ProofFile.PureBase}
  {base : List (Block TS ProofFile.Cl)} {p' : SwitchPlace}
  {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X Xj Xo : Type}
  {wit : Local W₀ Rc ProofFile.Inst Tr → K1.PlaceIn Xj} {own₀ : Xo}
  {jobs : List (Nat × K1.SendJob (K1.PlaceIn Xj) Xo)}
  {Oth : Others Bk (Local W₀ Rc ProofFile.Inst Tr)} {D : RowDataOf ProofFile.Inst}
  {readers : Local W₀ Rc ProofFile.Inst Tr → Readers}
  {rest : Nat → TreeLot Bk (Local W₀ Rc ProofFile.Inst Tr)}

/-- **Under the head: one oracle message a root at the switch in front.** -/
theorem roots_at_front (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {x : Option Nat × Option Nat × Nat} (hx : x ∈ frontPairsW)
    {Pp : P1K2.Prep} {n' : P1K2.Nums} (hP : P1K2.prepOf Zp Bs.G₀ = some Pp)
    (hn' : P1K2.numsAt Pp x.1 = some n') :
    (P1K2.oraclesAt n'.grp n'.codes n'.sent).length = n'.roots := by
  have w := List.all_eq_true.1 readFrontW.1 x hx
  rw [numsW_at_head h O hP, hn'] at w
  simp only [Option.any_some, Bool.and_eq_true] at w
  exact beq_iff_eq.1 w.2

/-- **THE LAW ON THE NUMBERS UNDER THE HEAD.** x: a pair; n': the numbers of the switch in front; n:
of the later switch. -/
theorem read_at_front (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {x : Option Nat × Option Nat × Nat} (hx : x ∈ frontPairsW)
    {Pp : P1K2.Prep} {n' n : P1K2.Nums} (hP : P1K2.prepOf Zp Bs.G₀ = some Pp)
    (hn' : P1K2.numsAt Pp x.1 = some n') (hn : P1K2.numsAt Pp x.2.1 = some n)
    {t : Nat × Nat × Nat} (ht : t ∈ n.read) {j : Nat} (hj : j < n'.roots)
    (e : t.1 = treesTo cF.blocksInOrder x.2.2 + j) :
    ∃ o, (P1K2.oraclesAt n'.grp n'.codes n'.sent)[j]? = some o ∧ o.words = t.2.2 := by
  have w := List.all_eq_true.1 readFrontW.2.1 x hx
  rw [numsW_at_head h O hP, numsW_at_head h O hP, hn', hn] at w
  simp only [Option.any_some] at w
  have w1 := List.all_eq_true.1 w j (List.mem_range.2 hj)
  simp only [Bool.and_eq_true] at w1
  have w2 := List.all_eq_true.1 w1.2 t ht
  simp only [Bool.or_eq_true] at w2
  rw [treesTo_at_head h O] at e
  rcases w2 with a | a
  · exact absurd e (bne_iff_ne.1 a)
  · cases ho : (P1K2.oraclesAt n'.grp n'.codes n'.sent)[j]? with
    | none =>
      rw [ho] at a
      cases a
    | some o =>
      rw [ho] at a
      simp only [Option.any_some, beq_iff_eq, Nat.add_zero] at a
      exact ⟨o, rfl, a⟩

/-- **`OwnTreesAt` AT THE SWITCH IN FRONT, AT EVERY `Said`**, where the Script is the joined one. x:
a pair of `frontPairsW`. -/
theorem ownTreesAt_at_join (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {x : Option Nat × Option Nat × Nat} (hx : x ∈ frontPairsW)
    (hp' : p' ∈ switchPlaces Zp Bs.G₀) (hl : p'.place.link = x.1)
    (F : JoinFit cF.blocksInOrder 0 (P5J.At.arr Zp) (P5J.At.seats Zp) wit own₀ jobs Oth)
    (hin : ShareIn (switchShareAt Bk cF.blocksInOrder 0 Zp Bs.G₀ D readers rest) Oth)
    (cells : Local W₀ Rc ProofFile.Inst Tr → CellsM OnBytes.Flat.numsFull)
    (tok : Local W₀ Rc ProofFile.Inst Tr → P5J.At.Tok)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X) (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {Pp : P1K2.Prep} {n' : P1K2.Nums} (hP : P1K2.prepOf Zp Bs.G₀ = some Pp)
    (hn' : P1K2.numsAt Pp x.1 = some n') :
    OwnTreesAt (lettersHead h H
        (joinQ cF.blocksInOrder 0 cells tok (P5J.At.arr Zp) wit own₀ jobs Oth) test carryX item n₁ n₂ b₀ Vd
        Rd Kp w).thread Said x.2.2 n'.roots fun j k v hd =>
      (p'.place, switchTableAt Bk 0 (coreSender freshTable) D readers
        (lotClosingAt Bs.G₀.first.layout (segmentsOf Zp Bs.G₀)) p' k v hd j) := by
  obtain ⟨blk, member, -⟩ := k2_member_at_head h O hp'
  obtain ⟨Pp₁, n₁', nm', st', -, -, hP₁, hn₁, -, ⟨-, -, ho⟩, -, -⟩ :=
    k2_block_at_head h O hp' member
  obtain rfl : Pp₁ = Pp := Option.some.inj (hP₁.symm.trans hP)
  rw [hl] at hn₁
  obtain rfl : n₁' = n' := Option.some.inj (hn₁.symm.trans hn')
  have hpW : p' ∈ placesW := by
    rw [← places_at_head h.toAtMg O]
    exact hp'
  have hno : switchNo p' = x.2.2 := by
    have a := beq_iff_eq.1 (List.all_eq_true.1 frontSeatsW.1 x hx)
    have m : switchNo p' ∈ (placesW.filter fun p => p.place.link == x.1).map switchNo :=
      List.mem_map.2 ⟨p', List.mem_filter.2 ⟨hpW, beq_iff_eq.2 hl⟩, rfl⟩
    rw [a] at m
    exact List.mem_singleton.1 m
  have eb : borderNo cF.blocksInOrder p'.place = x.2.2 := (K1.borderNo_written h p'.place).trans hno
  have hin' := hin
  unfold switchShareAt at hin'
  have OT := share_trees_fit (F := F) (hin := hin') (cells := cells) (tok := tok)
    (T := (lettersHead h H (joinQ cF.blocksInOrder 0 cells tok (P5J.At.arr Zp) wit own₀ jobs Oth) test
      carryX item n₁ n₂ b₀ Vd Rd Kp w).thread) (hbs := rfl) (hfr := rfl) (htab := rfl)
    (hfix := rfl) (hnd := borders_apart_at_head h O) (hp := hp') (blk := blk)
    (hblk := by rw [K1.borderNo_written h p'.place]; exact member)
  rw [eb] at OT
  have hr := roots_at_front h.toAtMg O hx hP hn'
  have hle : n₁'.roots ≤ (blk.oracles.flatMap id).length := by
    rw [ho]
    show n₁'.roots ≤ _
    simp
    exact Nat.le_of_eq hr.symm
  exact fun j hj => ownTreesAt_of_own OT Said j (Nat.lt_of_lt_of_le hj hle)

/-- **THE CLAUSE OF "THE WIDTHS" AT THE TREE THAT THE SWITCH IN FRONT SENT**, where the Script is
the joined one, at each pair of `frontPairsW`: no `PlayedTo` is asked. -/
theorem width_at_join (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {x : Option Nat × Option Nat × Nat} (hx : x ∈ frontPairsW)
    (hp' : p' ∈ switchPlaces Zp Bs.G₀) (hl : p'.place.link = x.1)
    (F : JoinFit cF.blocksInOrder 0 (P5J.At.arr Zp) (P5J.At.seats Zp) wit own₀ jobs Oth)
    (hin : ShareIn (switchShareAt Bk cF.blocksInOrder 0 Zp Bs.G₀ D readers rest) Oth)
    (cells : Local W₀ Rc ProofFile.Inst Tr → CellsM OnBytes.Flat.numsFull)
    (tok : Local W₀ Rc ProofFile.Inst Tr → P5J.At.Tok)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X) (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {Pp : P1K2.Prep} {n' n : P1K2.Nums} (hP : P1K2.prepOf Zp Bs.G₀ = some Pp)
    (hn' : P1K2.numsAt Pp x.1 = some n') (hn : P1K2.numsAt Pp x.2.1 = some n)
    {t : Nat × Nat × Nat} (ht : t ∈ n.read) {j : Nat} (hj : j < n'.roots)
    (e : t.1 = treesTo cF.blocksInOrder x.2.2 + j)
    {b : Nat} {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hb : x.2.2 < b)
    (hT : ThrS (lettersHead h H
      (joinQ cF.blocksInOrder 0 cells tok (P5J.At.arr Zp) wit own₀ jobs Oth) test carryX item n₁ n₂ b₀ Vd
      Rd Kp w).thread Said b k s m E)
    (c₀ : SwitchCoins p'.sizes p'.others p'.foldVars p'.carries)
    (hc : lendPart Bk (Bk.rowsOf 0) (k.look 0) ⟨p'.place, 0⟩
      (switchPart (coreSender freshTable) p'.sizes p'.others p'.foldVars p'.carries) = .ok c₀)
    (hcl : closingOk freshTable ((segmentsOf Zp Bs.G₀).take p'.link) p' = true)
    (hv : publicOk D Bs.G₀.first.layout p' ((segmentsOf Zp Bs.G₀).take p'.link)
      m.st.input.x = true) :
    ((lettersHead h H (joinQ cF.blocksInOrder 0 cells tok (P5J.At.arr Zp) wit own₀ jobs Oth) test carryX
      item n₁ n₂ b₀ Vd Rd Kp w).thread.tableAt (.own t.1) k m).2.words = t.2.2 := by
  have hO := ownTreesAt_at_join h O hx hp' hl F hin cells tok H test carryX item n₁ n₂ b₀ Vd Rd Kp w
    Said hP hn'
  obtain ⟨o, ho, e1⟩ := read_at_front h.toAtMg O hx hP hn' hn ht hj e
  rw [e]
  refine (words_of_ownAt hO hj hb hT).trans ?_
  exact (congrArg Prod.snd (switchTable_at_plan hP hp' (by rw [hl]; exact hn') Bk 0 D readers
    Bs.G₀.first.layout (segmentsOf Zp Bs.G₀) k m.st.input _ c₀ hc
    (serves_at_head h.toAtMg O p' hp') (roomy_at_head h.toAtMg O p' hp')
    (fits_at_head h.toAtMg O p' hp') hcl hv j o ho)).trans e1

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.frontPairsW
#print axioms ProofFile.Honest.K2.Law.rootsFrontB
#print axioms ProofFile.Honest.K2.Law.readFrontB
#print axioms ProofFile.Honest.K2.Law.readFrontW
#print axioms ProofFile.Honest.K2.Law.frontSeatsW
#print axioms ProofFile.Honest.K2.Law.roots_at_front
#print axioms ProofFile.Honest.K2.Law.read_at_front
#print axioms ProofFile.Honest.K2.Law.ownTreesAt_at_join
#print axioms ProofFile.Honest.K2.Law.width_at_join
