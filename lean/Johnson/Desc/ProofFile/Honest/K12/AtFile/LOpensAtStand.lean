-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LOpensAtStand.lean: THE FIELD `opens` OF `FrontAtT`
(ClosingAtL.lean) AT A STAND OF THE FIRST CHAIN's THREAD AT THE CLOSING PROXIMITY TEST, under the
library's head (`P5J.AtMgA` at `OnBytes.secondHashFunction`), at the job `jobL` with the row data and the
closing at which the wider filling lays it (`proxLotOf`, Honest/AtPureWiderK12.lean) where its sizes
are `Sz.ref` (the readers and the door are free letters), at the coins that the run's book lends the
test's two parts.

  `sendingTest`, `sendingFits_of_test`   `SendingFits` (LOpensRows.lean), the width's test
                        (LOpensTable.lean), the three public tests under which the finish's rows are
                        laid, and that the column has a word (a witness, not spent), as one Bool
  `sending_written`, `sending_written_no`   A CLOSED LINE at the written finish and the written
                        place's first stage, and three controls
  `sending_at_head`     the closed line at the finish that is there, under the head
  `finishRows_laid`     the finish's rows are laid, at every input whose instance passes the test on
                        the instance
  `heard_at_stand`      at a stand at 354, under hFixed: the challenges at which the thread reads
                        its table at own 76 are all but the last two
  `closingColumns_at_stand`   the columns: the premise hColumns of `opens_at_stand`
                        (LOpensLines.lean)
  `opens_at_thread`     THE END

The premises.
  h, hG, hf   the head; G is the blank ground; pl is the finish that `finishAt` returns there
  hbs         the thread's list is the head's chain
  hFixed      the thread's table at tree own 76 changes no more behind the challenges in front of
              member 353: the field `fixed` of `K2Seated` (Honest/K2/Seated.lean) at that member
  hSame       AT THE STAND, the thread's table at tree own 76 shows what table 0 of the finish's
              sending shows: the second half of `OwnTreesAt` (Honest/Thread/ScriptLots.lean) at
              member 353, tree 0. It is not asked as an equation at all coins, inputs and
              challenges: such a one fails at a letter whose table is read off a play (argued:
              the head of Honest/Thread/ScriptLots.lean)
  hHanded     the frame hands the finish's part something, at all coins
  hBook       the public test `closingBookTest` (LOpensBook.lean) on the book
  hValid      the thread's valid inputs pass the description's test on the instance
  hT, hLend   the stand; the coins c are those that the book lends the two parts there

Limits.
- hFixed, hSame, hHanded, hBook and hValid are premises. None is shown here of any letter or book.
- It compares what the prover's side holds at hand with what the job computes. Nothing on what the
  verifier accepts.
- At the sizes `Sz.ref` alone. The full size; at `OnBytes.secondHashFunction`.
- Nothing on completeness, on soundness or on hiding.
NOT IN FRONT OF A LAW OVER COINS: `closingColumns_at_stand` and `opens_at_thread` bear this label;
the rule is at its home, the head of Johnson/Bind/ForProver/FiveFieldsAt.lean. Their ground: the
thread from `Thr` as a premise; hLend ties the letter c to the run's coins; hValid is on the letter
for "valid".
Terms: the head of LShapeTest.lean; Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LOpensLines
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LOpensTable
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LOpensBook
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LReturnsClosing
import Johnson.Desc.ProofFile.Honest.K12.AtProof.CutAtL
import Johnson.Desc.ProofFile.Honest.Thread.ScriptLots
import Johnson.Desc.ProofFile.Honest.Law.Along
import Johnson.Desc.ProofFile.Honest.K2.Law.PlanAsks
import Johnson.Desc.ProofFile.Honest.K2.Law.Laid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc (Chain Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open OnBytes.HonestTrace (Sz)
open OnBytes.Slice (codeOf)
open H2K.Member (piLFull)
open ProofFile.Honest.K12 (TestJob atStand firstPart restPart restCoins OpensFit OldAt stA colAt)
open ProofFile.Honest.K12.Light (lendRow_snd)
open P5J (AtMgA F0T)

local notation "Rows" => Johnson.Prover.Send.Rows

/-- **The public facts on the finish's place and the test's first stage, as one Bool.** -/
def sendingTest (p : K2.SwitchPlace) (s : Fmt.M1.Stage) : Bool :=
  decide ((sentL p).size = 2) && K2.noWord (sentL p) &&
  decide ((freshShapeL p).mainRows = 0) && decide ((freshShapeL p).maskRows = 2 ^ s.h) &&
  decide (OnBytes.ceilLog2 (freshShapeL p).maskRows = s.h) && decide (p.foldVars = s.k) &&
  decide (s.h ≤ s.k) && decide (s.h + 2 * (s.k - s.h) + 1 ≤ s.Z.l) &&
  decide (codeOf (p.sizes.codes.mask.getD (freshShapeL p).maskCode default) = s.Z) &&
  decide (K2.messageDue p.sizes.codes (freshShapeL p) (some p.foldVars) = ⟨0, dueFresh s⟩) &&
  widthTest (K2.sendingPar p.sizes.codes (sentL p)) 0 &&
  decide (((K2.sendingPar p.sizes.codes (sentL p)).trees[0]?).map (·.logN) = some 23) &&
  p.sizes.serves && p.sizes.roomy && K2.placeFits p &&
  decide (0 < columnLength (K2.sendingPar p.sizes.codes (sentL p)) 0)

theorem sendingFits_of_test {p : K2.SwitchPlace} {s : Fmt.M1.Stage}
    (h : sendingTest p s = true) : SendingFits p s ∧
      widthTest (K2.sendingPar p.sizes.codes (sentL p)) 0 = true ∧
      ((K2.sendingPar p.sizes.codes (sentL p)).trees[0]?).map (·.logN) = some 23 ∧
      p.sizes.serves = true ∧ p.sizes.roomy = true ∧ K2.placeFits p = true := by
  unfold sendingTest at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩, a11⟩, a12⟩, a13⟩, a14⟩,
    a15⟩, -⟩ := h
  exact ⟨⟨a1, K2.noWord_yes a2, a3, a4, a5, a6, a7, a8, a9, a10⟩, a11, a12, a13, a14, a15⟩

set_option maxRecDepth 1000000 in
/-- **The closed line**: at the written finish and the first stage of the written place. -/
theorem sending_written : finishW.any (fun p => sendingTest p (stA piLFull)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Controls: the first stage with one fold round more · with one mask variable more · with a mask
code whose message is longer by one. Alone a "false" could come of a lacking finish;
`sending_written` shows that one is there. -/
theorem sending_written_no :
    (finishW.any (fun p => sendingTest p { stA piLFull with k := (stA piLFull).k + 1 }) ||
      finishW.any (fun p => sendingTest p { stA piLFull with h := (stA piLFull).h + 1 }) ||
      finishW.any (fun p => sendingTest p { stA piLFull with
        Z := { (stA piLFull).Z with l := (stA piLFull).Z.l + 1 } })) = false := by
  decide +kernel

variable {W₀ Rc Tr X : Type}
variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The closed line at the finish that is there, under the head. -/
theorem sending_at_head (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {pl : K2.SwitchPlace}
    (hf : finishAt Zp G = some pl) : sendingTest pl (stA piLFull) = true := by
  have eF : finishAt Zp G = finishW := by
    unfold finishAt finishW
    rw [places_head h.toAtMg hG]
  have k := sending_written
  rw [← eF, hf] at k
  exact k

/-- **The finish's rows are laid**, at every input whose instance passes the description's test on
the instance, at all coins and challenges. -/
theorem finishRows_laid (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {pl : K2.SwitchPlace}
    (hf : finishAt Zp G = some pl) (readers : Local W₀ Rc ProofFile.Inst Tr → Readers)
    (w : Local W₀ Rc ProofFile.Inst Tr) (hStart : (F0T OnBytes.secondHashFunction Zp Np cF).okStart w.x = true)
    (hd : List Fmt.Drawn) (cK : K2.Law.SwitchCoins pl.sizes pl.others pl.foldVars pl.carries) :
    ∃ V, K2.switchRowsLaid (K2.withSwitchData Sz.ref (K1.lotData Sz.ref) Zp G) readers
      (K2.lotClosingAt G.first.layout (K2.segmentsOf Zp G)) pl cK w hd = .ok V := by
  obtain ⟨-, -, -, hs, hr, hp⟩ := sendingFits_of_test (sending_at_head h hG hf)
  have hok := closingOk_at_finish h hG hf
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  have hm : pl ∈ K2.switchPlaces Zp Bs.G₀ := List.mem_of_find?_eq_some hf
  have hpub := OnBytes.HonestTrace.U3.Fit.publicOk_of_okStart h O hStart pl hm
  have e := K2.Law.returnsLaw (K2.withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀) readers
    Bs.G₀.first.layout (K2.segmentsOf Zp Bs.G₀) pl hok w (hd.take (hd.length - 0)) cK.2.2
  rw [hpub] at e
  unfold K2.switchRowsLaid
  rw [hs, hr]
  simp only [Bool.not_true, Bool.false_eq_true, if_false]
  unfold K2.switchRowsAt
  cases hcl : K2.lotClosingAt Bs.G₀.first.layout (K2.segmentsOf Zp Bs.G₀) pl
      ((K2.withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀) w.x) (readers w)
      (hd.take (hd.length - 0)) (K2.Stretch.carried pl.carries cK.2.2) with
  | error t =>
    rw [hcl] at e
    cases e
  | ok Wl =>
    have hcl' : (K2.switchWit (K2.withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀) readers
        (K2.lotClosingAt Bs.G₀.first.layout (K2.segmentsOf Zp Bs.G₀)) pl w).left
        (hd.take (hd.length - 0)) (K2.Stretch.carried pl.carries cK.2.2) = .ok Wl := hcl
    dsimp only
    rw [hcl']
    exact K2.rowsAll_returns hp K2.freshTable _ cK.1

variable {Bk : ProverCoinCounts} {P Cells Tok M : Type}

/-- **At a stand at 354 the challenges in front of the finish are all but the last two.** -/
theorem heard_at_stand (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (L : ProofFile.Honest.FirstThread.Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X P Cells Tok M)
    (hbs : L.bs = cF.blocksInOrder) (hFixed : L.thread.fixed (.own 76) = roundsTo cF.blocksInOrder 353)
    {k : Coins Bk} {s : S} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : Thr L.thread 354 k s m E) :
    m.st.heard.take (L.thread.fixed (.own 76)) = heardL (frontOf m) := by
  obtain ⟨-, hFit, -⟩ := hT
  have hlen : m.st.heard.length = roundsTo cF.blocksInOrder 354 := by
    have e := drawsFit_length _ _ hFit
    have e' : m.st.heard.length = (declsTo L.bs 354).length := e
    rw [e', hbs]
    rfl
  obtain ⟨b, hb⟩ : ∃ b, cF.blocksInOrder[353]? = some b := by
    have e : (cF.blocksInOrder.map (·.rounds.length))[353]? = some 2 := by
      rw [lens_at_head h.toAtMg]
      exact written_353
    rw [List.getElem?_map] at e
    obtain ⟨b, hb, -⟩ := Option.map_eq_some_iff.1 e
    exact ⟨b, hb⟩
  have h2 := finish_two_rounds h.toAtMg hb
  have hs : roundsTo cF.blocksInOrder 354 = roundsTo cF.blocksInOrder 353 + 2 := by
    rw [ProofFile.Honest.FirstThread.roundsTo_succ hb, h2]
  show _ = m.st.heard.take (m.st.heard.length - 2)
  rw [hFixed, hlen, hs]
  rfl

/-- **The columns**: at a stand of the thread at 354, at the coins that the book lends the test's
two parts: below 2 ^ 23 the column at hand of tree own 76 is the column of the job's one tree. -/
theorem closingColumns_at_stand (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {pl : K2.SwitchPlace}
    (hf : finishAt Zp G = some pl) (door : Local W₀ Rc ProofFile.Inst Tr → Front X → T12)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers)
    (L : ProofFile.Honest.FirstThread.Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X P Cells Tok M)
    (hbs : L.bs = cF.blocksInOrder)
    (hFixed : L.thread.fixed (.own 76) = roundsTo cF.blocksInOrder 353)
    (hHanded : ∀ k : Coins Bk, (K2.handed 0 pl k).isSome = true)
    (hBook : closingBookTest Bk pl ⟨(H2U.p12OfMade Zp.made).place, 1⟩ = true)
    (hValid : ∀ w, L.valid w → (F0T OnBytes.secondHashFunction Zp Np cF).okStart w.x = true)
    {k : Coins Bk} {s : S} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : Thr L.thread 354 k s m E)
    (hSame : (L.thread.tableAt (.own 76) k m).2.same
      (K2.switchTableAt Bk 0 (K2.coreSender K2.freshTable)
        (K2.withSwitchData Sz.ref (K1.lotData Sz.ref) Zp G) readers
        (K2.lotClosingAt G.first.layout (K2.segmentsOf Zp G)) pl k m.st.input
        (m.st.heard.take (L.thread.fixed (.own 76))) 0) = true)
    (T : T12) (J' : TestJob (Local W₀ Rc ProofFile.Inst Tr) X)
    (hJ : J' = atStand (jobL (H2U.p12OfMade Zp.made) door
      (K2.withSwitchData Sz.ref (K1.lotData Sz.ref) Zp G) readers
      (K2.lotClosingAt G.first.layout (K2.segmentsOf Zp G)) pl) m.st.input (frontOf m) T)
    (c : RowCoins [(firstPart J' : Part (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X),
      restPart J'])
    (hLend : lendRow Bk (Bk.rowsOf 0) (k.look 0) J'.p.place
      [(firstPart J' : Part (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X),
        restPart J'] 0 = .ok c) :
    ∀ y, y < 2 ^ 23 → colAt E.tree (.own 76) y =
      ((J'.trees₀ m.st.input (frontOf m) (restCoins J' c.2.1).mem
        (J'.first m.st.input (frontOf m) (restCoins J' c.2.1))).getD 0 (0, fun _ => [])).2 y := by
  subst hJ
  have e : H2U.p12OfMade Zp.made = piLFull := Johnson.AtFull.Shape.p12_at_head h.toAtMg
  obtain ⟨F, hw, hlog, -, -, -⟩ := sendingFits_of_test (sending_at_head h hG hf)
  obtain ⟨cK, hcK⟩ := Option.isSome_iff_exists.1 (hHanded k)
  have hK : lendPart Bk (Bk.rowsOf 0) (k.look 0) ⟨pl.place, 0⟩
      (K2.switchPart (K2.coreSender K2.freshTable) pl.sizes pl.others pl.foldVars pl.carries) =
      .ok cK := by
    unfold K2.handed at hcK
    cases hl : lendPart Bk (Bk.rowsOf 0) (k.look 0) ⟨pl.place, 0⟩
        (K2.switchPart (K2.coreSender K2.freshTable) pl.sizes pl.others pl.foldVars
          pl.carries) with
    | error t =>
      rw [hl] at hcK
      cases hcK
    | ok c₀ =>
      rw [hl] at hcK
      exact congrArg Except.ok (Option.some.inj hcK)
  have hStart := hValid _ hT.2.2.2.2.2.2
  obtain ⟨V, hV⟩ := finishRows_laid h hG hf readers m.st.input hStart (heardL (frontOf m)) cK
  have hin : Fmt.TreeSource.own 76 ∈ L.thread.hand 354 := by
    show _ ∈ [] ++ (List.range (treesTo L.bs 354)).map Fmt.TreeSource.own
    rw [hbs, ProofFile.Honest.K12.treesTo_354 h.toAtMg]
    exact List.mem_append_right _ (List.mem_map.2 ⟨76, List.mem_range.2 (by omega), rfl⟩)
  obtain ⟨t, ht, hcol⟩ := columnAtHand_is_sent L.thread hin 0 _ readers _ pl 0 hT hSame hcK
    (by rw [heard_at_stand h L hbs hFixed hT]; exact hV) hw
  have ht23 : t.logN = 23 := by
    have q : ((K2.sendingPar pl.sizes.codes (sentL pl)).trees[0]?).map (·.logN) = some t.logN := by
      have ht' : (K2.sendingPar pl.sizes.codes (sentL pl)).trees[0]? = some t := ht
      rw [ht']
      rfl
    rw [hlog] at q
    exact (Option.some.inj q).symm
  have hTie := coinsTied_of_book Bk (Bk.rowsOf 0) (k.look 0) pl _ _ cK hK c.2.1
    (lendRow_snd Bk _ _ _ _ _ c hLend) hBook
  intro y hy
  rw [hcol y (by rw [ht23]; exact hy)]
  refine closingColumn_is_sent _ readers _ pl m.st.input (frontOf m) cK hV
    (stA (H2U.p12OfMade Zp.made)) (by rw [e]; exact F) _ hTie _ ?_ ?_ y
  · show _ = Johnson.Prover.Link.packedN _ (hideAt _ _)
    have hl : (membersL pl).length = pl.front.length + 1 := by simp [membersL]
    show Johnson.Prover.Link.packedN _ (hideAt _ (stretches _ c.2.1.2.2 (membersL pl).length).e) = _
    rw [hl]
    rfl
  · have hl : (membersL pl).length = pl.front.length + 1 := by simp [membersL]
    show tailsIn _ (stretches _ c.2.1.2.2 (membersL pl).length).e = _
    rw [hl]
    rfl

/-- **THE END: the field `opens` of `FrontAtT`** at a stand of the thread, at the lent coins. -/
theorem opens_at_thread (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {pl : K2.SwitchPlace}
    (hf : finishAt Zp G = some pl) (door : Local W₀ Rc ProofFile.Inst Tr → Front X → T12)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers)
    (L : ProofFile.Honest.FirstThread.Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X P Cells Tok M)
    (hbs : L.bs = cF.blocksInOrder)
    (hFixed : L.thread.fixed (.own 76) = roundsTo cF.blocksInOrder 353)
    (hHanded : ∀ k : Coins Bk, (K2.handed 0 pl k).isSome = true)
    (hBook : closingBookTest Bk pl ⟨(H2U.p12OfMade Zp.made).place, 1⟩ = true)
    (hValid : ∀ w, L.valid w → (F0T OnBytes.secondHashFunction Zp Np cF).okStart w.x = true)
    {k : Coins Bk} {s : S} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : Thr L.thread 354 k s m E)
    (hSame : (L.thread.tableAt (.own 76) k m).2.same
      (K2.switchTableAt Bk 0 (K2.coreSender K2.freshTable)
        (K2.withSwitchData Sz.ref (K1.lotData Sz.ref) Zp G) readers
        (K2.lotClosingAt G.first.layout (K2.segmentsOf Zp G)) pl k m.st.input
        (m.st.heard.take (L.thread.fixed (.own 76))) 0) = true)
    (T : T12) (J' : TestJob (Local W₀ Rc ProofFile.Inst Tr) X)
    (hJ : J' = atStand (jobL (H2U.p12OfMade Zp.made) door
      (K2.withSwitchData Sz.ref (K1.lotData Sz.ref) Zp G) readers
      (K2.lotClosingAt G.first.layout (K2.segmentsOf Zp G)) pl) m.st.input (frontOf m) T)
    (c : RowCoins [(firstPart J' : Part (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X),
      restPart J'])
    (hLend : lendRow Bk (Bk.rowsOf 0) (k.look 0) J'.p.place
      [(firstPart J' : Part (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X),
        restPart J'] 0 = .ok c) :
    ∃ depths src₀,
      (J'.trees₀ m.st.input (frontOf m) (restCoins J' c.2.1).mem
        (J'.first m.st.input (frontOf m) (restCoins J' c.2.1))).map (·.1) = depths ∧
      OpensFit J' (proximityTestKind guardedProximityTestParts J'.p : Block T12 Unit).rounds depths src₀ E.sent ∧
      OldAt E (J'.trees₀ m.st.input (frontOf m) (restCoins J' c.2.1).mem
        (J'.first m.st.input (frontOf m) (restCoins J' c.2.1))) src₀ :=
  opens_at_stand h.toAtMg hG hf door _ readers _ L hbs hT T J' hJ c
    (closingColumns_at_stand h hG hf door readers L hbs hFixed hHanded hBook hValid hT hSame T J'
      hJ c hLend)

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.heard_at_stand
#print axioms ProofFile.Honest.K12.AtProof.closingColumns_at_stand
#print axioms ProofFile.Honest.K12.AtProof.opens_at_thread
#print axioms ProofFile.Honest.K12.AtProof.sending_at_head
#print axioms ProofFile.Honest.K12.AtProof.finishRows_laid
#print axioms ProofFile.Honest.K12.AtProof.sendingTest
#print axioms ProofFile.Honest.K12.AtProof.sendingFits_of_test
#print axioms ProofFile.Honest.K12.AtProof.sending_written
#print axioms ProofFile.Honest.K12.AtProof.sending_written_no
