-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/SymbolsAtJoin.lean: what a code switch's front holds, and one member of the closed
group as the records of SymbolsOfMembers.lean ask it.

  place_of_seat        where each tree's number is its place, a seat read by number is the book's
  ArmAt, link_arm, head_arm, fin_arm   what the three sorts of front hold in common
  memberCodesB, freshCodesB, member_codes_written, fresh_codes_written, member_codes, member_logs
                       by Lean's kernel, with controls: the codes and tree lengths of the members
  tree_in_plan, numbers_at, single_member, single_fresh   small laws on plans, books and the list of
                       messages to open
  member_sent_at, fresh_at   a member and the fresh mask, from the sender, the seat and the table
  switch_table_at_join the thread's table of a tree of the switch in front
  positions_below      the positions of a switch's second round lie below the tree's length

Limits. The head, the opening and the yes are premises. Nothing on any property.
-/
import AtFullSide.K2.SymbolsOfSenders
import AtFullSide.K2.JoinSenders
import AtFullSide.K2.OpenerAtJoin
import Johnson.Desc.ProofFile.Honest.K2.Law.StoredAtYes
import Johnson.Desc.ProofFile.Honest.K2.Law.LockAsksAtArms
import Johnson.Desc.ProofFile.Honest.K2.Law.SizesAtYes
import Johnson.Desc.K2.Honest.Returns.FreshNumbered
import Johnson.Top.H0.StepLaws.StepLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K2
open OnBytes
open OnBytes.Slice (GE readE)
open Johnson.Prover.Send (shapeAt)
open VerifiableInference.Desc (Block Chain Strs roundsFit)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 AtYes frontAt finishFrontQ finishFrontQ_book rounds)
open VerifiableInference.Desc.First.Close (membersOf seatK10 maskTree maskPart noK10 maskNo)
open VerifiableInference.Desc.LinkJoin (loAt)
open VerifiableInference.Desc.K1 (parL noL firstPar gpOf)
open VerifiableInference.Desc.K2.Honest (Left Sizes GroupMember SymbolsAre sizesAt membersTrue
  groupLayout_true keptNo zeroG carryExact)
open VerifiableInference.PlanWritten (proofSizedFull)
open VerifiableInference.Desc.K13.Law (LFull)
open VerifiableInference.Desc.K2.Honest.Returns (ClosedBehind FrontTies link_door head_door fin_door
  link_member_stated head_member_stated fin_member_stated link_closedBehind head_closedBehind
  fin_closedBehind listed_reached fresh_of_closedBehind seat_reached)
open VerifiableInference.Desc.Sound (MsgT allOf EAll noFirst)
open Johnson.Desc.First.Walk.Tied (reach_raw)
open OnBytes.HonestTrace (Sz)
open OnBytes.Maker (WholeD)
open OnBytes.SendSim.Seat (wJobs)
open P5J (AtMgA CellsM TS F0T)
open _root_.Desc.K14.Law (secondAt seatZ shownGroups)
open ProofFile.Honest
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K1 (seatAtMember treeTables)
open ProofFile.Honest.K2
open ProofFile.Honest.K2.Law

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}
  {base : List (Block TS ProofFile.Cl)}

/-- **Where each tree's number is its place, a seat read by number is the book's own.** -/
theorem place_of_seat {B : TreeBook} {o : Nat} {q : Nat × Nat}
    (hN : ∀ (j : Nat) (t : Tree), B.trees[j]? = some t → t.number = j)
    (hs : VerifiableInference.Desc.Sound.seatBy noFirst B o = some q) :
    B.place[o]? = some q := by
  unfold VerifiableInference.Desc.Sound.seatBy at hs
  cases hp : B.place[o]? with
  | none =>
    rw [hp] at hs
    cases hs
  | some q' =>
    rw [hp, Option.bind_some] at hs
    obtain ⟨t, ht, e⟩ := Option.map_eq_some_iff.1 hs
    have e1 := hN _ _ ht
    have e2 : (t.number, q'.2) = q := e
    rw [e1] at e2
    rw [← e2]

/-- **What a front holds, whichever of the three sorts it is.** m: the closed group's link. nb: the
border. a: the state reached there. s₁: the state at which the kind's decision stands. x: the front.
-/
structure ArmAt (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) (m nb : Nat)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D₀.at OnBytes.Slice.frS.P.T.a) (allOf (D₀.at OnBytes.Slice.frS.P.T.a))).Str)
    (s₁ : TS) (x : _root_.Tw.K2.Front) : Prop where
  rch : h.toAtMg.rch nb a
  le : nb ≤ 353
  below : m < 25
  failed : a.1.2.failed = none
  book : s₁.book = a.1.2.book
  oracles : x.st.oracles = a.1.2.st.oracles
  facts : FrontFacts Zp m s₁.book x
  stated : ∀ i ∈ membersOf (loAt m),
    noK10 (P5J.At.seats Zp) (loAt m) (P5J.At.pseats Zp) m i < a.1.2.st.oracles.size
  closed : ClosedBehind h m a.1.1 x.f.rows a.1.2.st
  lay : ∀ T, FrontLay (sizesAt x.st x.f.rows T) (membersTrue x.st x.f.rows)
    (x.f.rows.gamma.map readE) x.f.rows
  last : ∀ {own : Nat → Nat → Nat → Nat → Cb.Gl.E} {heard : List Fmt.Drawn}
    {k : Nat → Except String ProofFile.Honest.K2.Stretch} {y : Option (Left × List OracleShape) × Nat},
    closingFrom freshTable own heard k (segsW.take (m + 1)) 0 0 none = .ok y →
    LastStep freshTable own heard k m y (membersTrue x.st x.f.rows)
  gamma : ∀ {zp : ProofFile.InstPub} {Rr R₀ : List Fmt.RoundView} {C C₀ : List VerifiableInference.Desc.OpenedColumn}
    {Sg : SegmentPub}, VerifiableInference.Desc.foldBlocks 0 (cF.blocksInOrder.take nb) (ProofFile.startS Zp zp) Rr C
      = .ok (a.1.2, R₀, C₀) → segsW[m]? = some Sg →
    challengesOr0 (Rr.map (·.drawn)) Sg.gamma = x.f.rows.gamma.map readE

/-- At a segment's first place. -/
theorem link_arm (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {m : Nat} (h23 : m < 23)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D₀.at OnBytes.Slice.frS.P.T.a) (allOf (D₀.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch (14 * (m + 1) + 2) a) {x : _root_.Tw.K2.Front}
    (hf : frontAt (ProofFile.pAtK2 Zp m) a.1.2 = some x) :
    ArmAt h m (14 * (m + 1) + 2) a a.1.2 x := by
  have hq := (link_door h h23 a hr).1
  obtain ⟨hu, hst⟩ := link_member_stated h h23 a hr
  obtain ⟨F, ho⟩ := link_front_facts h h23 a hr hq hf
  exact ⟨hr, by omega, by omega, hu, rfl, ho, F, hst, link_closedBehind h h23 a hr hq hf,
    fun T => link_frontLay h h23 a hr hq hf T, fun hy => link_lastStep h h23 a hr hq hf hy,
    fun f₀ hSg => link_gamma_heard h h23 a hr hq hf f₀ hSg⟩

/-- At the output head's front. -/
theorem head_arm (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D₀.at OnBytes.Slice.frS.P.T.a) (allOf (D₀.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch 339 a) {x : _root_.Tw.K2.Front}
    (hf : frontAt (ProofFile.pAtK2 Zp 23) a.1.2 = some x) :
    ArmAt h 23 339 a a.1.2 x := by
  have hq := (head_door h a hr).1
  obtain ⟨hu, hst⟩ := head_member_stated h a hr
  obtain ⟨Bs', base', O'⟩ := h.laid.opened
  obtain ⟨-, R', C', f⟩ := (reach_raw (h.toAtMg.rch_is_reach _ a hr)).fold
  obtain ⟨-, a2, -⟩ := Meaning.K2.front_pin_head h.scope h.reads O' f hq hf
  exact ⟨hr, by omega, by omega, hu, rfl, by rw [a2], head_frontFacts h a hr hq hf, hst,
    head_closedBehind h a hr hq hf, fun T => head_frontLay h a hr hq hf T,
    fun hy => head_lastStep h a hr hq hf hy, fun f₀ hSg => head_gamma_heard h a hr hq hf f₀ hSg⟩

/-- At the front behind the last segment. -/
theorem fin_arm (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D₀.at OnBytes.Slice.frS.P.T.a) (allOf (D₀.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch 353 a) {t : TS} (he : finishFrontQ a.1.2 = .ok t) {x : _root_.Tw.K2.Front}
    (hf : frontAt (ProofFile.pAtK2 Zp 24) t = some x) :
    ArmAt h 24 353 a t x := by
  have hq := (fin_door h a hr he).1
  obtain ⟨hu, hst⟩ := fin_member_stated h a hr
  obtain ⟨Bs', base', O'⟩ := h.laid.opened
  obtain ⟨-, R', C', f⟩ := (reach_raw (h.toAtMg.rch_is_reach _ a hr)).fold
  obtain ⟨-, -, -, a4, -⟩ := Meaning.K2.front_nums_fin h.scope h.reads O' f he hq hf
  exact ⟨hr, by omega, by omega, hu, (finishFrontQ_book he).1, by rw [a4],
    fin_frontFacts h a hr he hq hf, hst, fin_closedBehind h a hr he hq hf,
    fun T => fin_frontLay h a hr he hq hf T, fun hy => fin_lastStep h a hr he hq hf hy,
    fun f₀ hSg => fin_gamma_heard h a hr he hq hf f₀ hSg⟩

/-- The test on a closed group's members: a member with main rows has the request's code plus sh,
and a member with mask rows its mask code plus sh. sh is 0, but for a control. -/
def memberCodesB (sh : Nat) : Bool :=
  (List.range 25).all fun l => (membersOf (loAt l)).all fun i =>
    (((loAt l).get i).1.mainRows == 0 ||
      ((loAt l).get i).1.code == proofSizedFull.request.code + sh) &&
    (((loAt l).get i).1.maskRows == 0 ||
      ((loAt l).get i).1.maskCode == proofSizedFull.request.maskCode + sh)

/-- The test on the fresh masks, likewise. -/
def freshCodesB (sh : Nat) : Bool :=
  segsW.all fun Sg =>
    ((Sg.sent.headD #[]).getD ((Sg.sent.headD #[]).size - 1) default).shape.maskRows == 0 ||
      ((Sg.sent.headD #[]).getD ((Sg.sent.headD #[]).size - 1) default).shape.maskCode ==
        proofSizedFull.request.maskCode + sh

set_option maxRecDepth 1000000 in
/-- **The codes of a closed group's members**, on the written lists; a control: one further, no. -/
theorem member_codes_written : memberCodesB 0 = true ∧ memberCodesB 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **The code of each fresh mask**, on the written lists; a control: one further, no. -/
theorem fresh_codes_written : freshCodesB 0 = true ∧ freshCodesB 1 = false := by
  decide +kernel

/-- What the written facts say of one member, at a member of the link's list. -/
theorem member_codes {l : Nat} (hl : l < 25) {i : Fin (loAt l).length}
    (hi : i ∈ membersOf (loAt l)) :
    (((loAt l).get i).1.mainRows ≠ 0 → ((loAt l).get i).1.code = proofSizedFull.request.code) ∧
      (((loAt l).get i).1.maskRows ≠ 0 →
        ((loAt l).get i).1.maskCode = proofSizedFull.request.maskCode) := by
  have a := List.all_eq_true.1 (List.all_eq_true.1 member_codes_written.1 l (List.mem_range.2 hl)) i hi
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Nat.add_zero] at a
  exact ⟨fun h => a.1.resolve_left h, fun h => a.2.resolve_left h⟩

/-- The trees' lengths at a member, from the written facts. -/
theorem member_logs {l : Nat} (hl : l < 25) {i : Fin (loAt l).length}
    (hi : i ∈ membersOf (loAt l)) {t : TreeShape}
    (ht : LFull.shapes[(seatK10 (loAt l) P5T.psFull l i).1]? = some t) :
    (((loAt l).get i).1.mainRows ≠ 0 →
        t.logN = (Johnson.G.codesFull2.base.getD proofSizedFull.request.code default).logN) ∧
      (((loAt l).get i).1.maskRows ≠ 0 →
        (OnBytes.Slice.codeOf (Johnson.G.codesFull2.mask.getD proofSizedFull.request.maskCode
          default)).a ≤ t.logN) := by
  have a := List.all_eq_true.1 (List.all_eq_true.1 member_trees_written l (List.mem_range.2 hl)) i hi
  rw [ht] at a
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Option.any_some,
    decide_eq_true_eq] at a
  exact ⟨fun h => a.1.resolve_left h, fun h => a.2.resolve_left h⟩

/-- Behind a test on the plan each message lies in one of the plan's trees. -/
theorem tree_in_plan {P : VerifiableInference.Desc.K1.Par}
    (hP : VerifiableInference.Desc.K1.planOkOwn P = true) {kn : Nat} (hk : kn < P.sent.size) :
    ((VerifiableInference.Desc.Own.treesMade P.codes P.sent).getD {}).tree.getD kn 0 <
        ((VerifiableInference.Desc.Own.treesMade P.codes P.sent).getD {}).shapes.size ∧
      ((VerifiableInference.Desc.Own.treesMade P.codes P.sent).getD {}).tree.getD kn 0 <
        P.trees.length := by
  obtain ⟨Ly, hL, -⟩ := Johnson.Prover.Send.lay_some P hP
  have hm : VerifiableInference.Desc.Own.treesMade P.codes P.sent = some Ly := by
    rw [VerifiableInference.Desc.Own.treesMade_eq]
    exact hL
  have ht : P.trees = Ly.shapes.toList := by
    unfold VerifiableInference.Desc.K1.Par.trees
    rw [hm]
    rfl
  have e := (VerifiableInference.Desc.Own.treesMade_gives hm).2.1 kn hk
  rw [hm, ht]
  exact ⟨e, by simpa using e⟩

/-- Each tree's number is its place in the book of a reached state. -/
theorem numbers_at (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {nb : Nat}
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D₀.at OnBytes.Slice.frS.P.T.a) (allOf (D₀.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch nb a) (hle : nb ≤ 353) :
    ∀ (j : Nat) (t : Tree), a.1.2.book.trees[j]? = some t → t.number = j := by
  have N := Meaning.K2.bookInOrder_reached O (reach_raw (h.toAtMg.rch_is_reach _ a hr))
    (by
      rw [Meaning.Carry.front_len h.scope h.reads O]
      exact hle)
  intro j t ht
  have e := (N.2 j t ht).1
  omega

/-- The message number w to open, below the members, is the layout's member number w. -/
theorem single_member {old : SingleRows} (hm : old.masks = 2) {w : Nat}
    (hw : w < old.layout.members.size) (hw' : w < (singleRowsOracles old).size) :
    (singleRowsOracles old)[w] = old.layout.members.getD w noId := by
  have e : singleRowsOracles old = old.layout.members.push old.fresh := by
    unfold singleRowsOracles
    rw [hm]
    rfl
  simp only [e, Array.getElem_push, hw, dite_true, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem hw, Option.getD_some]

/-- The last message to open is the fresh mask. -/
theorem single_fresh {old : SingleRows} (hm : old.masks = 2)
    (hw' : old.layout.members.size < (singleRowsOracles old).size) :
    (singleRowsOracles old)[old.layout.members.size] = old.fresh := by
  have e : singleRowsOracles old = old.layout.members.push old.fresh := by
    unfold singleRowsOracles
    rw [hm]
    rfl
  simp only [e, Array.getElem_push, Nat.lt_irrefl, dite_false]

variable {Bk : ProverCoinCounts} {W₀ Rc Tr X Y : Type}

/-- **A member of the closed group, from its sender, its seat and the table of its tree.** -/
theorem member_sent_at (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {m nb : Nat}
    {a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D₀.at OnBytes.Slice.frS.P.T.a) (allOf (D₀.at OnBytes.Slice.frS.P.T.a))).Str}
    {s₁ t : TS} {x : _root_.Tw.K2.Front} (Ar : ArmAt h m nb a s₁ x) {q : P2} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {z : _root_.Tw.K2.Sent} {S3 : Statement} {Yv : Array E}
    {rows : List OnBytes.Row} {G : Group} {cd : Code}
    (A : AtYes q s₁ t r₁ r₂ gs x z S3 Yv rows G cd) (hft : q.firstTree = 0)
    (hlog : cd.logN = (Johnson.G.codesFull2.base.getD proofSizedFull.request.code default).logN)
    (hmk : x.f.rows.masks = 2) {Wl V X' Pb : Type} (T : Thread Bk TS ProofFile.Cl V Wl X' Pb)
    (hbs : T.bs = cF.blocksInOrder) (k : Coins Bk) (mm : Mid Wl X') (Zs : Sizes)
    (hcodes : Zs.codes = Johnson.G.codesFull2) (hcode : Zs.code = proofSizedFull.request.code)
    (hmask : Zs.maskCode = proofSizedFull.request.maskCode)
    {P : VerifiableInference.Desc.K1.Par} {b : Nat} (hP : SenderAt Zp Bs P b) (hb : b < nb)
    {blk : Block TS ProofFile.Cl} (hblk : cF.blocksInOrder[b]? = some blk)
    (hcount : (blk.oracles.flatMap id).length = P.trees.length)
    (plan : VerifiableInference.Desc.K1.planOkOwn P = true) (hpc : P.codes = Johnson.G.codesFull2)
    {w kn : Nat} (hbelow : kn < P.sent.size) {i : Fin (loAt m).length}
    (hi : (membersOf (loAt m))[w]? = some i)
    (hseat : seatK10 (loAt m) P5T.psFull m i = seatAtMember cF.blocksInOrder b P kn)
    (hshape : ((loAt m).get i).1 = shapeAt P kn) (R : GroupRows) (ms : List GroupMember)
    (hms : VerifiableInference.Desc.K2.Honest.shapeOf ms w = ((loAt m).get i).1)
    (Vr : Nat → Johnson.Prover.Send.Rows)
    (table : (treeTables P Vr)[((VerifiableInference.Desc.Own.treesMade P.codes P.sent).getD
        {}).tree.getD kn 0]? =
      some (T.tableAt (.own (treesTo cF.blocksInOrder b +
        ((VerifiableInference.Desc.Own.treesMade P.codes P.sent).getD {}).tree.getD kn 0)) k mm).2)
    (hrow : R.rows.getD w zeroMessage = Vr kn) :
    ∃ (Xo : Oracle) (tr : Tree),
      MemberSent T nb k mm q Zs x.f.rows z w P Vr kn Xo (seatAtMember cF.blocksInOrder b P kn) tr ∧
      MemberRow q Zs ms R w P Vr kn tr := by
  obtain ⟨hw, eo, -⟩ := member_at_facts Ar.facts hi
  have hmem : i ∈ membersOf (loAt m) := List.mem_of_getElem? hi
  have hst := Ar.stated i hmem
  obtain ⟨hs0, hsh0⟩ := listed_reached h (by have := Ar.le; omega) a Ar.rch Ar.failed Ar.below i hst
  have hN := numbers_at h O a Ar.rch Ar.le
  have hs : P5J.At.pseats Zp = P5T.psFull := h.toAtMg.seats
  have eK : seatK10 (loAt m) (P5J.At.pseats Zp) m i = seatAtMember cF.blocksInOrder b P kn := by
    rw [hs]
    exact hseat
  have hpl := place_of_seat hN hs0
  rw [eK] at hpl
  have hz : z.book.place[noK10 (P5J.At.seats Zp) (loAt m) (P5J.At.pseats Zp) m i]? =
      some (seatAtMember cF.blocksInOrder b P kn) := by
    rw [place_at_yes A (by rw [Ar.book]; exact (Array.getElem?_eq_some_iff.1 hpl).1), Ar.book, hpl]
  have hXo : z.st.oracles[noK10 (P5J.At.seats Zp) (loAt m) (P5J.At.pseats Zp) m i]? =
      some a.1.2.st.oracles[noK10 (P5J.At.seats Zp) (loAt m) (P5J.At.pseats Zp) m i] := by
    rw [A.sent.old _ (by rw [Ar.oracles]; exact hst), Ar.oracles]
    exact Array.getElem?_eq_getElem hst
  have hsh1 : a.1.2.st.oracles[noK10 (P5J.At.seats Zp) (loAt m) (P5J.At.pseats Zp) m i].shape =
      ((loAt m).get i).1 := by
    rw [Array.getElem?_eq_getElem hst] at hsh0
    exact Option.some.inj hsh0
  obtain ⟨hτ, hτ'⟩ := tree_in_plan plan hbelow
  have hmc := member_codes Ar.below hmem
  obtain ⟨tr, M, eL⟩ := memberSent_of h O a Ar.rch Ar.book A T hbs hft k mm Zs x.f.rows w hP hb
    Vr kn _ plan hbelow (hsh1.trans hshape)
    (fun h0 => by
      rw [hpc, hcodes, hmask, ← hshape, (hmc.2 (by rw [hshape]; exact h0))])
    (fun hw' => by
      rw [single_member hmk hw hw', eo]
      exact hz)
    (fun hw' => by
      rw [single_member hmk hw hw', eo]
      exact hXo)
    hτ
    (fun t ht h0 => by
      rw [hcodes, hmask]
      have ht' : LFull.shapes[(seatK10 (loAt m) P5T.psFull m i).1]? = some t := by
        rw [hseat]
        exact ht
      exact (member_logs Ar.below hmem ht').2 (by rw [hshape]; exact h0))
    (n₀ := nb)
    (by
      rw [hbs]
      exact tree_front hblk hb (by rw [hcount]; exact hτ'))
    table
  refine ⟨_, tr, M, hms.trans hshape, fun h0 => ?_, fun h0 => ?_, hrow⟩
  · rw [hpc, hcodes, hcode, ← hshape, (hmc.1 (by rw [hshape]; exact h0))]
  · have ht' : LFull.shapes[(seatK10 (loAt m) P5T.psFull m i).1]? = some tr.shape := by
      rw [hseat]
      exact eL
    rw [(member_logs Ar.below hmem ht').1 (by rw [← hms]; exact h0), hlog.symm]
    exact A.logN

/-- **The fresh mask of the closed group, from its sender, its seat and the table of its tree.** -/
theorem fresh_at (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {m nb : Nat}
    {a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D₀.at OnBytes.Slice.frS.P.T.a) (allOf (D₀.at OnBytes.Slice.frS.P.T.a))).Str}
    {s₁ t : TS} {x : _root_.Tw.K2.Front} (Ar : ArmAt h m nb a s₁ x) {q : P2} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {z : _root_.Tw.K2.Sent} {S3 : Statement} {Yv : Array E}
    {rows : List OnBytes.Row} {G : Group} {cd : Code}
    (A : AtYes q s₁ t r₁ r₂ gs x z S3 Yv rows G cd) (hft : q.firstTree = 0)
    (hmk : x.f.rows.masks = 2) {Wl V X' Pb : Type} (T : Thread Bk TS ProofFile.Cl V Wl X' Pb)
    (hbs : T.bs = cF.blocksInOrder) (k : Coins Bk) (mm : Mid Wl X') (Zs : Sizes)
    (hcodes : Zs.codes = Johnson.G.codesFull2)
    (hmask : Zs.maskCode = proofSizedFull.request.maskCode)
    {P : VerifiableInference.Desc.K1.Par} {b : Nat} (hP : SenderAt Zp Bs P b) (hb : b < nb)
    {blk : Block TS ProofFile.Cl} (hblk : cF.blocksInOrder[b]? = some blk)
    (hcount : (blk.oracles.flatMap id).length = P.trees.length)
    (plan : VerifiableInference.Desc.K1.planOkOwn P = true) (hpc : P.codes = Johnson.G.codesFull2)
    {kn : Nat} (hbelow : kn < P.sent.size)
    (hseat : (maskTree m, maskPart m) = seatAtMember cF.blocksInOrder b P kn)
    (hshape : (a.1.2.st.oracles.getD x.f.rows.fresh default).shape = shapeAt P kn)
    (hfc : (shapeAt P kn).maskRows ≠ 0 →
      (shapeAt P kn).maskCode = proofSizedFull.request.maskCode)
    (Vr : Nat → Johnson.Prover.Send.Rows)
    (table : (treeTables P Vr)[((VerifiableInference.Desc.Own.treesMade P.codes P.sent).getD
        {}).tree.getD kn 0]? =
      some (T.tableAt (.own (treesTo cF.blocksInOrder b +
        ((VerifiableInference.Desc.Own.treesMade P.codes P.sent).getD {}).tree.getD kn 0)) k mm).2) :
    ∃ (Xo : Oracle) (tr : Tree),
      MemberSent T nb k mm q Zs x.f.rows z x.f.rows.layout.members.size P Vr kn Xo
        (seatAtMember cF.blocksInOrder b P kn) tr ∧
      2 ^ x.f.rows.layout.h ≤ (shapeAt P kn).maskRows := by
  obtain ⟨e1, e2, e3⟩ := fresh_of_closedBehind h Ar.below Ar.rch.2 a.2 Ar.closed
  have hs0 : VerifiableInference.Desc.Sound.seatBy noFirst a.1.2.book x.f.rows.fresh =
      some (maskTree m, maskPart m) :=
    seat_reached h (by have := Ar.le; omega) a Ar.rch Ar.failed e2
      (by rw [e1]; exact (h.toAtMg.mask_letters_at m Ar.below).1)
  have hpl := place_of_seat (numbers_at h O a Ar.rch Ar.le) hs0
  rw [hseat] at hpl
  have hz : z.book.place[x.f.rows.fresh]? = some (seatAtMember cF.blocksInOrder b P kn) := by
    rw [place_at_yes A (by rw [Ar.book]; exact (Array.getElem?_eq_some_iff.1 hpl).1), Ar.book, hpl]
  have hXo : z.st.oracles[x.f.rows.fresh]? = some a.1.2.st.oracles[x.f.rows.fresh] := by
    rw [A.sent.old _ (by rw [Ar.oracles]; exact e2), Ar.oracles]
    exact Array.getElem?_eq_getElem e2
  have hsh1 : a.1.2.st.oracles[x.f.rows.fresh].shape = shapeAt P kn := by
    rw [← hshape, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem e2]
    rfl
  obtain ⟨hτ, hτ'⟩ := tree_in_plan plan hbelow
  obtain ⟨tr, M, -⟩ := memberSent_of h O a Ar.rch Ar.book A T hbs hft k mm Zs x.f.rows
    x.f.rows.layout.members.size hP hb Vr kn _ plan hbelow hsh1
    (fun h0 => by rw [hpc, hcodes, hmask, hfc h0])
    (fun hw' => by
      rw [single_fresh hmk hw']
      exact hz)
    (fun hw' => by
      rw [single_fresh hmk hw']
      exact hXo)
    hτ
    (fun t ht _ => by
      rw [hcodes, hmask]
      have ht' : LFull.shapes[maskTree m]? = some t := by
        rw [show maskTree m = (maskTree m, maskPart m).1 from rfl, hseat]
        exact ht
      have w := List.all_eq_true.1 fresh_trees_written m (List.mem_range.2 Ar.below)
      have e : VerifiableInference.Desc.First.Close.maskShape m = t := by
        unfold VerifiableInference.Desc.First.Close.maskShape
        rw [ht']
        rfl
      rw [e] at w
      exact of_decide_eq_true w)
    (n₀ := nb)
    (by
      rw [hbs]
      exact tree_front hblk hb (by rw [hcount]; exact hτ'))
    table
  exact ⟨_, tr, M, by rw [← hshape, e3]⟩

/-- **A tree of the switch in front, at the joined Script**: the thread's table is the one of the
sending that that switch's rows make. -/
theorem switch_table_at_join (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Wt : Type} {Rt : Type} {Tt : Type} {Xj Xo Cells Tok V X' Pb : Type}
    {wit : Local Wt Rt ProofFile.Inst Tt → K1.PlaceIn Xj} {own₀ : Xo}
    {jobs : List (Nat × K1.SendJob (K1.PlaceIn Xj) Xo)}
    {Oth : Others Bk (Local Wt Rt ProofFile.Inst Tt)} {D : RowDataOf ProofFile.Inst}
    {readers : Local Wt Rt ProofFile.Inst Tt → Readers}
    {rest : Nat → TreeLot Bk (Local Wt Rt ProofFile.Inst Tt)}
    (F : JoinFit cF.blocksInOrder 0 (P5J.At.arr Zp) (P5J.At.seats Zp) wit own₀ jobs Oth)
    (hin : ShareIn (switchShareAt Bk cF.blocksInOrder 0 Zp Bs.G₀ D readers rest) Oth)
    (cells : Local Wt Rt ProofFile.Inst Tt → Cells) (tok : Local Wt Rt ProofFile.Inst Tt → Tok)
    (T : Thread Bk TS ProofFile.Cl V (Local Wt Rt ProofFile.Inst Tt) X' Pb) (hbs : T.bs = cF.blocksInOrder)
    (hfr : T.front = 0)
    (htab : T.table = (joinQ cF.blocksInOrder 0 cells tok (P5J.At.arr Zp) wit own₀ jobs Oth).table)
    (hfix : T.fixed = (joinQ cF.blocksInOrder 0 cells tok (P5J.At.arr Zp) wit own₀ jobs Oth).fixed)
    {p₀ : SwitchPlace} (hp₀ : p₀ ∈ switchPlaces Zp Bs.G₀) (k : Coins Bk)
    (mm : Mid (Local Wt Rt ProofFile.Inst Tt) X')
    (c₀ : SwitchCoins p₀.sizes p₀.others p₀.foldVars p₀.carries)
    (hc : lendPart Bk (Bk.rowsOf 0) (k.look 0) ⟨p₀.place, 0⟩
      (switchPart (coreSender freshTable) p₀.sizes p₀.others p₀.foldVars p₀.carries) = .ok c₀)
    {V₀ : Nat → Johnson.Prover.Send.Rows}
    (hV : switchRowsLaid D readers (lotClosingAt Bs.G₀.first.layout (segmentsOf Zp Bs.G₀)) p₀ c₀
      mm.st.input (mm.st.heard.take (0 + roundsTo cF.blocksInOrder (switchNo p₀))) = .ok V₀)
    {blk : Block TS ProofFile.Cl} (hblk : cF.blocksInOrder[switchNo p₀]? = some blk) {τ : Nat}
    (hτ : τ < (blk.oracles.flatMap id).length)
    (hτ' : τ < (treeTables (switchPar p₀) V₀).length) :
    (treeTables (switchPar p₀) V₀)[τ]? =
      some (T.tableAt (.own (treesTo cF.blocksInOrder (switchNo p₀) + τ)) k mm).2 := by
  have hin' := hin
  unfold switchShareAt at hin'
  have eb : borderNo cF.blocksInOrder p₀.place = switchNo p₀ := K1.borderNo_written h p₀.place
  have OT := share_trees_fit (F := F) (hin := hin') (cells := cells) (tok := tok) (T := T)
    (hbs := hbs) (hfr := hfr) (htab := htab) (hfix := hfix) (hnd := borders_apart_at_head h O)
    (hp := hp₀) (blk := blk) (hblk := by rw [eb]; exact hblk)
  rw [eb] at OT
  have e2 := OT.fixed τ hτ
  rw [hbs, hfr] at e2
  have e1 := OT.table τ hτ k mm.st.input (mm.st.heard.take (0 + roundsTo cF.blocksInOrder (switchNo p₀)))
  rw [hbs] at e1
  unfold Thread.tableAt
  rw [e2, Nat.add_zero, e1]
  exact switch_table_is 0 D readers _ p₀ k mm.st.input _ c₀ hc hV hτ'

/-- **The positions that a switch's second round draws lie below the tree's length.** -/
theorem positions_below {q : P2} {r₁ r₂ : Fmt.RoundView} (h : roundsFit (rounds q) [r₁, r₂] = true) :
    ∀ j, j < (Positions.ofDraws q.logN r₂.drawn.poss).all.size →
      (Positions.ofDraws q.logN r₂.drawn.poss).all.getD j 0 < 2 ^ q.logN := by
  intro j hj
  have hp : ∀ y ∈ r₂.drawn.poss, y < 2 ^ q.logN := by
    simp only [rounds, roundsFit, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    exact h.2.1.1.1.2
  have hm : (Positions.ofDraws q.logN r₂.drawn.poss).all.getD j 0 ∈
      (Positions.ofDraws q.logN r₂.drawn.poss).all.toList := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj]
    exact Array.getElem_mem_toList hj
  exact hp _ (VerifiableInference.Desc.K2.Honest.Returns.ofDraws_all _ _ _ hm)

end AtFullSide.K2

#print axioms AtFullSide.K2.place_of_seat
#print axioms AtFullSide.K2.link_arm
#print axioms AtFullSide.K2.head_arm
#print axioms AtFullSide.K2.fin_arm
#print axioms AtFullSide.K2.member_codes_written
#print axioms AtFullSide.K2.fresh_codes_written
#print axioms AtFullSide.K2.member_codes
#print axioms AtFullSide.K2.member_logs
#print axioms AtFullSide.K2.tree_in_plan
#print axioms AtFullSide.K2.single_member
#print axioms AtFullSide.K2.single_fresh
#print axioms AtFullSide.K2.numbers_at
#print axioms AtFullSide.K2.member_sent_at
#print axioms AtFullSide.K2.fresh_at
#print axioms AtFullSide.K2.switch_table_at_join
#print axioms AtFullSide.K2.positions_below
