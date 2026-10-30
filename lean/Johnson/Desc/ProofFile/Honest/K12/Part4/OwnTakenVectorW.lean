--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/Part4/OwnTakenVectorW.lean: THE KEY FILE's OWN PROXIMITY TEST: TREE
NUMBER 1 OF THE JOB IS THE TABLE OF W's SENDING, WITH THE FIRST FRESH TABLE THAT RIDES IN IT: the
proof of `TakenVectorW` (K12/Part4/OwnTakenStatements.lean).

WHAT IT IS NOT. All that the head of the statements' file says it is not. NOT IN FRONT OF A LAW OVER
COINS. Under `OwnTestGround`, whose fields on letters can be false at a filling: here `wReads` is
spent: W's data is a letter, and nothing is said of what it yields. The closed lines are evaluations
by Lean's kernel at written values. Nothing on completeness, on soundness or on what is hidden.

  `ride_fresh`   a riding table's rows, as K1's `rowsR` lays them of the sender's coins, are the
                 packing and the tails that a test's first state has, where the test's stretch
                 reads the sender's coins from the message's start on. General
  `wBookB`, `wBook_full`   the key file's book at the written sizes: the second and the fourth entry
                 that the test's second part carries are the sender's coins 0 + 403 and 403 + 109
                 of 512; the sender has a row in the first chain alone
  `WFacts`, `wFacts_written`   the public facts of the member, general in the parameters; and at the
                 written values, field by field by Lean's kernel
  `takenVectorW`   the statement

CALLED: `packing_sent` (K12/PackingAt.lean) · `hideAt_congr` (K12/HideCongr.lean) · `rowIdx_lt`
(K12/RowsCongr.lean) · `member_held` (K12/AtProof/HandedW.lean) · `rowsR_csAt`
(K12/AtProof/JobW.lean) · `column_three`, `depth_three`, `first_three` (K12/AtFile/WJointTree.lean) ·
`wordsAt_append` (K12/TreeIsColumnAt.lean) · `cut_of_due` (K12/DepthsOfText.lean) · this folder's
files. `ride_fresh`'s second half follows the last lines of `coinsTie_of_book`
(K12/CoinsTieBook.lean).
-/
import Johnson.Desc.ProofFile.Honest.K12.Part4.OwnTakenIndexMasks
import Johnson.Desc.ProofFile.Honest.K12.PackingAt
import Johnson.Desc.ProofFile.Honest.K12.HideCongr

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.Part4
open VerifiableInference.Desc.Key (Source LaterPlaces descriptionFromSource)
open H2K.Member (piKWFull)
open H2K.Pub (sgOf)
open OnBytes.Slice (GE GF codeOf)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub atFull rideW)
open AtPublicFiles.KeyFile (KeyParts In1 In2 randK14)
open AtPublicFiles.KeyLay (jobKWAt parIK parWK pWK)
open AtPublicFiles.KeyThread (fixedLast)
open AtPublicFiles.KeyTest (sIdx sW)
open AtPublicFiles.AtFiles.Full (QK)
open Johnson.Prover.Send (col mainSyms maskSyms)
open Johnson.Prover.Link (packedN)
open ProofFile.Honest.K14 (jobOmega)
open ProofFile.Honest.K12.Light
open ProofFile.Honest.K12.AtProof (memK1 csAt rowsR_csAt member_held)
open ProofFile.Honest.K12.AtFile (TakenIs)

/-- **A riding table's rows are the packing and the tails of a test's first state.** S: the test's
stretch. -/
theorem ride_fresh (s : Fmt.M1.Stage) (P : VerifiableInference.Desc.K1.Par)
    (ride : ℕ → Option K1.Ride) (data : ℕ → ℕ → ℕ → Option (GF ⊕ GE)) (c : Cs (K1.dueR P ride))
    (k : ℕ) (S : ℕ → GE) (hR : ride k = some ⟨(sgOf s).h + (sgOf s).g, (sgOf s).h⟩)
    (hk : s.k = (sgOf s).h + (sgOf s).g) (hl : (sgOf s).h + 2 * (sgOf s).g + 1 ≤ (sgOf s).Z.l)
    (hdeg : ((Johnson.Prover.Send.shapeAt P k).mainDeg == 3) = false)
    (hrows : (Johnson.Prover.Send.shapeAt P k).maskRows = 2 ^ s.h)
    (hcode : codeOf (P.codes.mask.getD (Johnson.Prover.Send.shapeAt P k).maskCode default) = s.Z)
    (held : ∀ i, i < dueFresh s → K1.ce c ((K1.startR P ride k).e + i) = S i) :
    (∀ b < 2 ^ s.h, ∀ j < s.Z.l,
      packedN (sgOf s) (hideAt ((sgOf s).h + (sgOf s).g) S) b j =
        (K1.rowsR P ride data c k).mask b j) ∧
    ∀ b < 2 ^ s.h, ∀ q < s.Z.r, tailsIn s S b q = (K1.rowsR P ride data c k).maskTl b q := by
  have hell : (P.codes.mask.getD (Johnson.Prover.Send.shapeAt P k).maskCode default).ell = s.Z.l :=
    congrArg Fmt.M1.Code.l hcode
  have hr0 : (P.codes.mask.getD (Johnson.Prover.Send.shapeAt P k).maskCode default).r = s.Z.r :=
    congrArg Fmt.M1.Code.r hcode
  refine ⟨fun b hb j hj => ?_, fun b hb q hq => ?_⟩
  · rw [packing_sent (sgOf s) hl P ride data c k b j hR (by rw [hrows]; exact hb)
      (by rw [hell]; exact hj)]
    refine congrFun (congrFun (congrArg (packedN (sgOf s)) (hideAt_congr _ _ _ fun i hi => ?_)) b) j
    rw [if_pos hi, hdeg]
    simp only [Bool.false_eq_true, if_false, Nat.add_zero]
    refine (held i ?_).symm
    unfold dueFresh
    omega
  · have hb' := rowIdx_lt hb hq
    unfold tailsIn
    rw [← held _ (by unfold dueFresh; omega)]
    simp only [K1.rowsR]
    rw [if_pos ⟨by rw [hrows]; exact hb, by rw [hr0]; exact hq⟩, hdeg, hr0]
    have hm : (K1.stepsOf P.codes (Johnson.Prover.Send.shapeAt P k) (ride k)).mask =
        2 * s.k + 1 := by
      unfold K1.stepsOf
      rw [hR, hk]
      rfl
    rw [hm]
    simp only [Bool.false_eq_true, if_false, Nat.add_zero]
    congr 1
    omega

/-- A main row over the extension field. -/
theorem main_overE (R : Johnson.Prover.Send.Rows) (r : ℕ) : R.main true r = R.mainE r := by
  funext j
  simp [Johnson.Prover.Send.Rows.main]

/-- Its tail. -/
theorem mainTl_overE (R : Johnson.Prover.Send.Rows) (r : ℕ) : R.mainTl true r = R.mainTlE r := by
  funext j
  simp [Johnson.Prover.Send.Rows.mainTl]

/-- The book's lines at W's member and at the riding table. -/
def wBookB (K : KeyPub) : Bool :=
  (((carryE (keyBook K) ⟨piKWFull.place, 1⟩)[1]?).map fun e => (e.owner, e.start, e.count)) ==
      some (sW, ⟨0, 0⟩, ⟨0, 403⟩) &&
    (((carryE (keyBook K) ⟨piKWFull.place, 1⟩)[3]?).map fun e => (e.owner, e.start, e.count)) ==
      some (sW, ⟨0, 403⟩, ⟨0, 109⟩) &&
    dueAt (keyBook K).first sW == ⟨0, 512⟩ &&
    !((keyBook K).shared.any fun r => r.1 == sW) &&
    !((keyBook K).second.any fun r => r.1 == sW)

/-- **The book's lines hold at the written sizes.** By Lean's kernel. -/
theorem wBook_full : atFull wBookB = true := by decide +kernel

/-- **The public facts of W's member and of the riding table.** -/
structure WFacts (PI PW : VerifiableInference.Desc.K1.Par) (first : List (Option ℕ × Option ℕ))
    (ride : ℕ → Option K1.Ride) (q : VerifiableInference.Desc.K12.P12) : Prop where
  size : PW.sent.size = 2
  stage : (q.nums.stages.headD default).h ≤ (q.nums.stages.headD default).k
  overE : ((Johnson.Prover.Send.shapeAt PW 0).mainDeg == 3) = true
  base : ((Johnson.Prover.Send.shapeAt PW 0).mainDeg == 1) = false
  noMain₁ : (Johnson.Prover.Send.shapeAt PW 1).mainRows = 0
  notE₁ : ((Johnson.Prover.Send.shapeAt PW 1).mainDeg == 3) = false
  rows₁ : (Johnson.Prover.Send.shapeAt PW 1).maskRows = 2 ^ (q.nums.stages.headD default).h
  codeC : codeOf (PW.codes.base.getD (Johnson.Prover.Send.shapeAt PW 0).code default) =
    (q.nums.stages.headD default).C
  codeZ₀ : codeOf (PW.codes.mask.getD (Johnson.Prover.Send.shapeAt PW 0).maskCode default) =
    (q.nums.stages.headD default).Z
  codeZ₁ : codeOf (PW.codes.mask.getD (Johnson.Prover.Send.shapeAt PW 1).maskCode default) =
    (q.nums.stages.headD default).Z
  roomMain : (first.getD 1 (none, none)).1.getD 0 +
    (Johnson.Prover.Send.shapeAt PW 0).mainRows ≤ 2 ^ (q.nums.stages.headD default).k
  roomMask : (first.getD 1 (none, none)).2.getD 0 +
    (Johnson.Prover.Send.shapeAt PW 0).maskRows ≤ 2 ^ (q.nums.stages.headD default).h
  clearMain : (Johnson.Prover.Send.shapeAt PI 0).mainRows = 0
  clearMask : (first.getD 0 (none, none)).2.getD 0 +
    (Johnson.Prover.Send.shapeAt PI 0).maskRows ≤ (first.getD 1 (none, none)).2.getD 0
  plan : VerifiableInference.Desc.K1.planOkOwn PW = true
  trees : 0 < PW.trees.length
  logN : (PW.trees.getD 0 {}).logN = 22
  width : (PW.trees.getD 0 {}).mainWidth + (PW.trees.getD 0 {}).maskWidth = 12
  mine : ((List.range PW.sent.size).filter fun k =>
    ((VerifiableInference.Desc.Own.treesMade PW.codes PW.sent).getD {}).tree[k]? == some 0) =
      [0, 1]
  depth : Light.depthOf q 1 = 22
  start₀ : K1.startR PW ride 0 = ⟨0, 0⟩
  count₀ : K1.dueMsg PW.codes (Johnson.Prover.Send.shapeAt PW 0) (ride 0) = ⟨0, 403⟩
  start₁ : K1.startR PW ride 1 = ⟨0, 403⟩
  count₁ : K1.dueMsg PW.codes (Johnson.Prover.Send.shapeAt PW 1) (ride 1) = ⟨0, 109⟩
  fresh : dueFresh (q.nums.stages.headD default) = 109
  due : K1.dueR PW ride = ⟨0, 512⟩
  rides : ride 1 = some ⟨(sgOf (q.nums.stages.headD default)).h +
    (sgOf (q.nums.stages.headD default)).g, (sgOf (q.nums.stages.headD default)).h⟩
  split : (q.nums.stages.headD default).k = (sgOf (q.nums.stages.headD default)).h +
    (sgOf (q.nums.stages.headD default)).g
  pack : (sgOf (q.nums.stages.headD default)).h + 2 * (sgOf (q.nums.stages.headD default)).g + 1 ≤
    (sgOf (q.nums.stages.headD default)).Z.l

/-- **They hold at the written values.** Field by field, by Lean's kernel. -/
theorem wFacts_written :
    WFacts parIK parWK (firstRows parIK parWK (jobOmega ⟨QK, 0⟩)) rideW piKWFull where
  size := by decide +kernel
  stage := by decide +kernel
  overE := by decide +kernel
  base := by decide +kernel
  noMain₁ := by decide +kernel
  notE₁ := by decide +kernel
  rows₁ := by decide +kernel
  codeC := by decide +kernel
  codeZ₀ := by decide +kernel
  codeZ₁ := by decide +kernel
  roomMain := by decide +kernel
  roomMask := by decide +kernel
  clearMain := by decide +kernel
  clearMask := by decide +kernel
  plan := by decide +kernel
  trees := by decide +kernel
  logN := by decide +kernel
  width := by decide +kernel
  mine := by decide +kernel
  depth := by decide +kernel
  start₀ := by decide +kernel
  count₀ := by decide +kernel
  start₁ := by decide +kernel
  count₁ := by decide +kernel
  fresh := by decide +kernel
  due := by decide +kernel
  rides := by decide +kernel
  split := by decide +kernel
  pack := by decide +kernel

/-- The facts read of the two sendings their codes and messages alone. -/
theorem WFacts.alike {PI' PI PW' PW : VerifiableInference.Desc.K1.Par}
    {first : List (Option ℕ × Option ℕ)} {ride : ℕ → Option K1.Ride}
    {q : VerifiableInference.Desc.K12.P12} (F : WFacts PI PW first ride q)
    (hI : PI'.sent = PI.sent) (hc : PW'.codes = PW.codes) (hW : PW'.sent = PW.sent) :
    WFacts PI' PW' first ride q :=
  { size := by rw [hW]; exact F.size
    stage := F.stage
    overE := by rw [shapeAt_alike hW]; exact F.overE
    base := by rw [shapeAt_alike hW]; exact F.base
    noMain₁ := by rw [shapeAt_alike hW]; exact F.noMain₁
    notE₁ := by rw [shapeAt_alike hW]; exact F.notE₁
    rows₁ := by rw [shapeAt_alike hW]; exact F.rows₁
    codeC := by rw [hc, shapeAt_alike hW]; exact F.codeC
    codeZ₀ := by rw [hc, shapeAt_alike hW]; exact F.codeZ₀
    codeZ₁ := by rw [hc, shapeAt_alike hW]; exact F.codeZ₁
    roomMain := by rw [shapeAt_alike hW]; exact F.roomMain
    roomMask := by rw [shapeAt_alike hW]; exact F.roomMask
    clearMain := by rw [shapeAt_alike hI]; exact F.clearMain
    clearMask := by rw [shapeAt_alike hI]; exact F.clearMask
    plan := by rw [planOwn_congr PW' PW hc hW]; exact F.plan
    trees := by rw [trees_alike hc hW]; exact F.trees
    logN := by rw [trees_alike hc hW]; exact F.logN
    width := by rw [trees_alike hc hW]; exact F.width
    mine := by rw [hc, hW]; exact F.mine
    depth := F.depth
    start₀ := by rw [startR_alike hc hW]; exact F.start₀
    count₀ := by rw [hc, shapeAt_alike hW]; exact F.count₀
    start₁ := by rw [startR_alike hc hW]; exact F.start₁
    count₁ := by rw [hc, shapeAt_alike hW]; exact F.count₁
    fresh := F.fresh
    due := by rw [dueR_alike hc hW]; exact F.due
    rides := F.rides, split := F.split, pack := F.pack }

section
variable {S Cl V Pb W₀ Rc X₀ X Wk : Type} {K₀ : KeyPub}
  {T : Thread (keyBook K₀) S Cl V (In1 W₀ Rc) X Pb} {K : KeyParts W₀ Rc X₀ X Wk} {Xs : Source}
  {Nr : H2U.PlaceNums} {Pl : LaterPlaces} {toCommon : In1 W₀ Rc → In2 W₀ Rc}

/-- The public facts at the parts. -/
theorem w_facts_at (G : OwnTestGround T K Xs Nr Pl toCommon) :
    WFacts K.idx.P K.w.P (firstRows K.idx.P K.w.P (omegaMoved K Xs Nr Pl)) K.w.ride (pWK Pl) := by
  rw [firstRows_moved _ _ _ _ 0, firstRows_alike G.senders.idxSent G.senders.wSent,
    G.senders.wRide, G.senders.sendPar, G.place]
  exact wFacts_written.alike G.senders.idxSent G.senders.wCodes G.senders.wSent

/-- The book's lines at the book of the ground. -/
theorem w_book_at (G : OwnTestGround T K Xs Nr Pl toCommon) :
    ∃ e₁ e₃, (carryE (keyBook K₀) ⟨(ownTestJob K Xs Nr Pl).p.place, 1⟩)[1]? = some e₁ ∧
      e₁.owner = sW ∧ e₁.start = ⟨0, 0⟩ ∧ e₁.count = ⟨0, 403⟩ ∧
      (carryE (keyBook K₀) ⟨(ownTestJob K Xs Nr Pl).p.place, 1⟩)[3]? = some e₃ ∧
      e₃.owner = sW ∧ e₃.start = ⟨0, 403⟩ ∧ e₃.count = ⟨0, 109⟩ ∧
      dueAt (keyBook K₀).first sW = ⟨0, 512⟩ ∧
      ((keyBook K₀).shared.any fun r => r.1 == sW) = false ∧
      ((keyBook K₀).second.any fun r => r.1 == sW) = false := by
  have hB : wBookB K₀ = true := by
    have h := wBook_full
    unfold atFull at h
    rw [G.book] at h
    exact h
  unfold wBookB at hB
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hB
  obtain ⟨⟨⟨⟨hE₁, hE₃⟩, hdue⟩, hshared⟩, hsecond⟩ := hB
  obtain ⟨e₁, he₁, q₁⟩ := Option.map_eq_some_iff.1 hE₁
  obtain ⟨e₃, he₃, q₃⟩ := Option.map_eq_some_iff.1 hE₃
  obtain ⟨o₁, s₁, c₁⟩ : e₁.owner = sW ∧ e₁.start = ⟨0, 0⟩ ∧ e₁.count = ⟨0, 403⟩ := by
    simpa [Prod.mk.injEq] using q₁
  obtain ⟨o₃, s₃, c₃⟩ : e₃.owner = sW ∧ e₃.start = ⟨0, 403⟩ ∧ e₃.count = ⟨0, 109⟩ := by
    simpa [Prod.mk.injEq] using q₃
  refine ⟨e₁, e₃, ?_, o₁, s₁, c₁, ?_, o₃, s₃, c₃, hdue, hshared, hsecond⟩
  · show (carryE (keyBook K₀) ⟨(pWK Pl).place, 1⟩)[1]? = some e₁
    rw [G.place]
    exact he₁
  · show (carryE (keyBook K₀) ⟨(pWK Pl).place, 1⟩)[3]? = some e₃
    rw [G.place]
    exact he₃

/-- **The sender's own coins are there, and the two stretches that the test carries read them.** -/
theorem w_coins (G : OwnTestGround T K Xs Nr Pl toCommon) {k : Coins (keyBook K₀)}
    {c : OwnTestCoins V K Xs Nr Pl} (hl : Lent T K Xs Nr Pl k c) :
    ∃ c₀ : Cs (K1.dueR K.w.P K.w.ride),
      K1.lentCut k 0 ⟨K.w.P.place, 0⟩ (K1.dueR K.w.P K.w.ride) = some c₀ ∧
      ((∀ i, i < (K1.dueMsg K.w.P.codes (Johnson.Prover.Send.shapeAt K.w.P 0) (K.w.ride 0)).f →
        K1.cf c₀ ((K1.startR K.w.P K.w.ride 0).f + i) =
          ((restCoins (ownTestJob K Xs Nr Pl).toRun.toTest c.2.1).mem 1).f i) ∧
      ∀ i, i < (K1.dueMsg K.w.P.codes (Johnson.Prover.Send.shapeAt K.w.P 0) (K.w.ride 0)).e →
        K1.ce c₀ ((K1.startR K.w.P K.w.ride 0).e + i) =
          ((restCoins (ownTestJob K Xs Nr Pl).toRun.toTest c.2.1).mem 1).e i) ∧
      ∀ i, i < (K1.dueMsg K.w.P.codes (Johnson.Prover.Send.shapeAt K.w.P 1) (K.w.ride 1)).e →
        K1.ce c₀ ((K1.startR K.w.P K.w.ride 1).e + i) =
          ((restCoins (ownTestJob K Xs Nr Pl).toRun.toTest c.2.1).mem 3).e i := by
  have F := w_facts_at G
  obtain ⟨e₁, e₃, he₁, o₁, s₁, c₁, he₃, o₃, s₃, c₃, hdue, hshared, hsecond⟩ := w_book_at G
  have hplace : (⟨K.w.P.place, 0⟩ : Addr) = sW := by
    rw [G.wPlace]
    rfl
  obtain ⟨c₀, hc₀⟩ := Option.isSome_iff_exists.1 (cut_of_due k 0 (Nat.zero_le 1) sW
    (K1.dueR K.w.P K.w.ride) (by
      show _ ≤ (dueAt (keyBook K₀).first sW).f ∧ _ ≤ (dueAt (keyBook K₀).first sW).e
      rw [F.due, hdue]
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩))
  refine ⟨c₀, by rw [hplace]; exact hc₀,
    member_held k (lent_second G hl) he₁ K.w.P K.w.ride 0 (by rw [F.size]; decide)
      (by rw [s₁, F.start₀]) (by rw [c₁, F.count₀]) (by rw [o₁, hdue, F.due])
      (by rw [o₁]; exact hshared) (by rw [o₁]; exact hsecond) (by rw [o₁]; exact hc₀),
    (member_held k (lent_second G hl) he₃ K.w.P K.w.ride 1 (by rw [F.size]; decide)
      (by rw [s₃, F.start₁]) (by rw [c₃, F.count₁]) (by rw [o₃, hdue, F.due])
      (by rw [o₃]; exact hshared) (by rw [o₃]; exact hsecond) (by rw [o₃]; exact hc₀)).2⟩

/-- The member's rows, of the stretch that the test carries. -/
abbrev wRows (K : KeyParts W₀ Rc X₀ X Wk) (Xs : Source) (Nr : H2U.PlaceNums)
    (Pl : LaterPlaces) (m : Mid (In1 W₀ Rc) X) (c : OwnTestCoins V K Xs Nr Pl) :
    Johnson.Prover.Send.Rows :=
  K1.rowsR K.w.P K.w.ride (K.w.data (id m.st.input) (frontOf m))
    (csAt _ (K1.startR K.w.P K.w.ride 0)
      ((restCoins (ownTestJob K Xs Nr Pl).toRun.toTest c.2.1).mem 1)) 0

/-- **They are the rows that the sender lays**, at the challenges that the table reads. -/
theorem w_rows (G : OwnTestGround T K Xs Nr Pl toCommon) (m : Mid (In1 W₀ Rc) X)
    {c : OwnTestCoins V K Xs Nr Pl} (c₀ : Cs (K1.dueR K.w.P K.w.ride))
    (hf : ∀ i, i < (K1.dueMsg K.w.P.codes (Johnson.Prover.Send.shapeAt K.w.P 0) (K.w.ride 0)).f →
      K1.cf c₀ ((K1.startR K.w.P K.w.ride 0).f + i) =
        ((restCoins (ownTestJob K Xs Nr Pl).toRun.toTest c.2.1).mem 1).f i)
    (he : ∀ i, i < (K1.dueMsg K.w.P.codes (Johnson.Prover.Send.shapeAt K.w.P 0) (K.w.ride 0)).e →
      K1.ce c₀ ((K1.startR K.w.P K.w.ride 0).e + i) =
        ((restCoins (ownTestJob K Xs Nr Pl).toRun.toTest c.2.1).mem 1).e i) :
    K1.rowsLaid K.w K.own₀ c₀ (id m.st.input) (m.st.heard.take (T.fixed (.taken 0 5))) 0 =
      wRows K Xs Nr Pl m c := by
  have F := w_facts_at G
  unfold wRows K1.rowsLaid
  rw [rowsR_csAt K.w.P K.w.ride _ 0 (by rw [F.size]; decide) _ c₀ hf he,
    G.wReads (id m.st.input) _ (frontOf m) (by
      show (m.st.heard.take (T.fixed (.taken 0 5))).take _ = m.st.heard.take _
      rw [G.tables.fixed _ (by simp [AtKey.takenOwn]), List.take_take, Nat.min_self])]

/-- **The job's column of tree 1, the first rows of the blocks as letters.** R₁: the riding table's
rows. -/
theorem w_column (G : OwnTestGround T K Xs Nr Pl toCommon) (m : Mid (In1 W₀ Rc) X)
    (c : OwnTestCoins V K Xs Nr Pl) (fs0 fs1 fs2 : Option ℕ × Option ℕ)
    (hm : (ownTestJob K Xs Nr Pl).mems =
      [memK1 K.idx id sIdx 0 fs0, memK1 K.w id sW 0 fs1,
        memOfSending (omegaMoved K Xs Nr Pl) AtProof.senderO 0 fs2 (askAt K) none])
    (roomMain : fs1.1.getD 0 + (Johnson.Prover.Send.shapeAt K.w.P 0).mainRows ≤
      2 ^ ((pWK Pl).nums.stages.headD default).k)
    (roomMask : fs1.2.getD 0 + (Johnson.Prover.Send.shapeAt K.w.P 0).maskRows ≤
      2 ^ ((pWK Pl).nums.stages.headD default).h)
    (clearMask : fs0.2.getD 0 + (Johnson.Prover.Send.shapeAt K.idx.P 0).maskRows ≤ fs1.2.getD 0)
    (R₁ : Johnson.Prover.Send.Rows)
    (em : ∀ b < 2 ^ ((pWK Pl).nums.stages.headD default).h,
      ∀ j < ((pWK Pl).nums.stages.headD default).Z.l,
      ((ownTestJob K Xs Nr Pl).toRun.toTest.first m.st.input (frontOf m)
        (restCoins (ownTestJob K Xs Nr Pl).toRun.toTest c.2.1)).fM b j = R₁.mask b j)
    (et : ∀ b < 2 ^ ((pWK Pl).nums.stages.headD default).h,
      ∀ q < ((pWK Pl).nums.stages.headD default).Z.r,
      ((ownTestJob K Xs Nr Pl).toRun.toTest.first m.st.input (frontOf m)
        (restCoins (ownTestJob K Xs Nr Pl).toRun.toTest c.2.1)).fT b q = R₁.maskTl b q) (x : ℕ) :
    ((ownTestTrees K Xs Nr Pl m c).getD 1 (0, fun _ => [])).2 x =
      ((List.range (Johnson.Prover.Send.shapeAt K.w.P 0).mainRows).flatMap fun r =>
        Johnson.Prover.Link.words3 (OnBytes.Slice.ofE (Johnson.Prover.Link.symG
          ((pWK Pl).nums.stages.headD default).C x
          ((wRows K Xs Nr Pl m c).main ((Johnson.Prover.Send.shapeAt K.w.P 0).mainDeg == 3) r)
          ((wRows K Xs Nr Pl m c).mainTl
            ((Johnson.Prover.Send.shapeAt K.w.P 0).mainDeg == 3) r)))) ++
      (((List.range (Johnson.Prover.Send.shapeAt K.w.P 0).maskRows).flatMap fun r =>
        Johnson.Prover.Link.words3 (OnBytes.Slice.ofE (Johnson.Prover.Link.symG
          ((pWK Pl).nums.stages.headD default).Z
          (x % 2 ^ ((pWK Pl).nums.stages.headD default).Z.a)
          ((wRows K Xs Nr Pl m c).mask r) ((wRows K Xs Nr Pl m c).maskTl r)))) ++
      (List.range (2 ^ ((pWK Pl).nums.stages.headD default).h)).flatMap fun r =>
        Johnson.Prover.Link.words3 (OnBytes.Slice.ofE (Johnson.Prover.Link.symG
          ((pWK Pl).nums.stages.headD default).Z
          (x % 2 ^ ((pWK Pl).nums.stages.headD default).Z.a) (R₁.mask r) (R₁.maskTl r)))) := by
  have F := w_facts_at G
  obtain ⟨t1, t2⟩ := first_three (ownTestJob K Xs Nr Pl) _ _ _ hm m.st.input (frontOf m)
    (restCoins (ownTestJob K Xs Nr Pl).toRun.toTest c.2.1)
  obtain ⟨t3, t4⟩ := first_three_mask (ownTestJob K Xs Nr Pl) _ _ _ hm m.st.input (frontOf m)
    (restCoins (ownTestJob K Xs Nr Pl).toRun.toTest c.2.1)
  rw [column_three (ownTestJob K Xs Nr Pl) _ _ _ hm m.st.input (frontOf m) _ _ 1
    (Light.depthOf (pWK Pl) 1) [.main 1, .mask 1, .fresh] rfl x]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [wordsAt_append, wordsAt_append,
    main_piece_second (ownTestJob K Xs Nr Pl).s₀ F.stage _ _ _ _ _ _
      ((wRows K Xs Nr Pl m c).main ((Johnson.Prover.Send.shapeAt K.w.P 0).mainDeg == 3))
      ((wRows K Xs Nr Pl m c).mainTl ((Johnson.Prover.Send.shapeAt K.w.P 0).mainDeg == 3))
      (Johnson.Prover.Send.shapeAt K.w.P 0).mainRows _ x
      (by
        rw [stage_own, ← F.codeC]
        rfl)
      (by
        rw [stage_own, ← F.codeC]
        rfl)
      (by rw [shape_ofK1])
      (by
        rw [shape_ofK1]
        exact F.base)
      (by
        rw [shape_ofK1, stage_own]
        exact roomMain)
      (fun r _ => by
        rw [shape_ofK1, shape_ofK1]
        show ¬ (fs0.1.getD 0 ≤ fs1.1.getD 0 + r ∧ fs1.1.getD 0 + r < fs0.1.getD 0 +
          (Johnson.Prover.Send.shapeAt K.idx.P 0).mainRows)
        rw [F.clearMain]
        omega) t1 t2,
    mask_piece_second (ownTestJob K Xs Nr Pl).s₀ _ _ _ _ _ _ (wRows K Xs Nr Pl m c).mask
      (wRows K Xs Nr Pl m c).maskTl (Johnson.Prover.Send.shapeAt K.w.P 0).maskRows _ x
      (by
        rw [stage_own, ← F.codeZ₀]
        rfl)
      (by
        rw [stage_own, ← F.codeZ₀]
        rfl)
      (by rw [shape_ofK1])
      (by
        rw [shape_ofK1, stage_own]
        exact roomMask)
      (fun r _ => by
        rw [shape_ofK1, shape_ofK1]
        show ¬ (fs0.2.getD 0 ≤ fs1.2.getD 0 + r ∧ fs1.2.getD 0 + r < fs0.2.getD 0 +
          (Johnson.Prover.Send.shapeAt K.idx.P 0).maskRows)
        omega) t3 t4,
    fresh_stretch (ownTestJob K Xs Nr Pl).s₀ _ R₁.mask R₁.maskTl _ x em et, stage_own]

end

theorem takenVectorW : TakenVectorW := by
  intro S Cl V Pb W₀ Rc X₀ X Wk K₀ T K Xs Nr Pl toCommon G k m c hl
  have F := w_facts_at G
  have FI := index_facts_at G
  obtain ⟨c₀, hcut, ⟨hf, he⟩, h₁⟩ := w_coins G hl
  obtain ⟨td, -, tc⟩ := treeTbl_at 0 id K.w K.own₀ 0 k c₀ hcut F.plan F.trees m.st.input
    (m.st.heard.take (T.fixed (.taken 0 5)))
  have hk0 : K.idx.P.sent.size - 1 = 0 := by rw [FI.size]
  have hm := members_own K Xs Nr Pl
  rw [hk0] at hm
  obtain ⟨em, et⟩ := ride_fresh ((pWK Pl).nums.stages.headD default) K.w.P K.w.ride
    (K.w.data (id m.st.input)
      (⟨m.st.heard.take (T.fixed (.taken 0 5)), K.own₀, .bare []⟩ : Front X)) c₀ 1
    ((restCoins (ownTestJob K Xs Nr Pl).toRun.toTest c.2.1).mem 3).e F.rides F.split F.pack F.notE₁
    F.rows₁ F.codeZ₁ (fun i hi => h₁ i (by
      rw [F.count₁]
      rw [F.fresh] at hi
      exact hi))
  refine ⟨?_, fun x _ => ?_⟩
  · rw [depth_three (ownTestJob K Xs Nr Pl) _ _ _ hm m.st.input (frontOf m) _ _ 1
      (Light.depthOf (pWK Pl) 1) [.main 1, .mask 1, .fresh] rfl, F.depth]
    show 22 = (T.table (.taken 0 5) k m.st.input _).2.logLength
    rw [G.tables.vectorW, td, F.logN]
  · show (T.table (.taken 0 5) k m.st.input (m.st.heard.take (T.fixed (.taken 0 5)))).2.col x = _
    rw [G.tables.vectorW, tc x, col_of_mine _ _ 0 x [0, 1] F.mine,
      w_column G m c _ _ _ hm F.roomMain F.roomMask F.clearMask
        (K1.rowsLaid K.w K.own₀ c₀ (id m.st.input) (m.st.heard.take (T.fixed (.taken 0 5))) 1)
        em et x]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have e1 : mainSyms K.w.P (K1.rowsLaid K.w K.own₀ c₀ (id m.st.input)
        (m.st.heard.take (T.fixed (.taken 0 5)))) 1 x = [] := by
      unfold mainSyms
      simp only [F.noMain₁, List.range_zero, List.flatMap_nil]
    rw [e1, List.append_nil]
    unfold mainSyms maskSyms
    simp only [w_rows G m c₀ hf he, F.codeC, F.codeZ₀, F.codeZ₁, F.overE, F.rows₁, if_true,
      main_overE, mainTl_overE]

end ProofFile.Honest.K12.Part4

#print axioms ProofFile.Honest.K12.Part4.ride_fresh
#print axioms ProofFile.Honest.K12.Part4.wBook_full
#print axioms ProofFile.Honest.K12.Part4.wFacts_written
#print axioms ProofFile.Honest.K12.Part4.WFacts.alike
#print axioms ProofFile.Honest.K12.Part4.w_facts_at
#print axioms ProofFile.Honest.K12.Part4.w_book_at
#print axioms ProofFile.Honest.K12.Part4.w_coins
#print axioms ProofFile.Honest.K12.Part4.w_rows
#print axioms ProofFile.Honest.K12.Part4.w_column
#print axioms ProofFile.Honest.K12.Part4.takenVectorW
