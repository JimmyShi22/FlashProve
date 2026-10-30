-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/K11R/LawAtMg.lean: THE KIND K11's OWN SENTENCE (the merge of the claims on the committed
table): «NAMED CONDITIONS GIVE THE KIND's SHARE OF THE CHAIN OF PROMISES», AT THE COMPOSED MEANING's
CLOSED CONSTANT `mgAtAll h` (Johnson/P5J/MgAtAll.lean). One
abbreviation, one structure, a closed fact, one theorem: a joining. It proves nothing of any
sub-protocol that the files beneath do not.

What is said.
  `K11Cond h Bs Rch xM xI posI ni R Wa`: FOURTEEN NAMED CONDITIONS, by sort: four closed tests with
    code, off the public parameters alone (nums, oneClaim, pendAll, low: the fence); digThere: the
    public parameters give segment 24 a lookup on the digits; the reading of the two members' mask
    tables (niPos, inM, inI); weights: the lemma that joins the two sentences for "weights"; three
    facts at a reached state with the table's condition and no mark (front, frontWa, behindIdx); two
    tests with code at such a state (speaks: FIVE-FOLD: `Speaks`,
    Johnson/Top/H0/MergeLaw/RunsAre.lean; leaves: `leavesLenB`, RunsLate.lean). No field is a clause
    of a tie BY FORM. BY WEIGHT weights IS THE HEAVIEST: it ends in the whole sentence of the one
    item that the merge closes in front: the law proves the merge's own sentence in front; the step
    from it to the constant's sentence is the field.
  `makes346`: the merge's row makes no public item anew: by the kernel.
  `k11_law_atMg`: from the constant's own head h, an opening O at its letters, the description's
    data and its test on the plan, the three lists' heads, ONE MORE CLOSED TEST tm (`k11AtRB`: the
    two members are there), hc: the first chain's rows are the written rows, and K: «at the two
    members that tm gives there are posI, ni, R, Wa with `K11Cond`»: `KindTiedR h.𝔇.N (mgAtAll h)
    linksFull … Rch (the table's own extractor) (the first row of the three rows of pieces with the
    cap) K11`: the name in which the counted laws end (Johnson/Desc/Sound/TiedR.lean).

By what. `k11_law_atThree` (LawAtThree.lean); `mergeFill_atAll`, `members_atAll` (AtAll.lean);
`merge_tied_full` (Johnson/Top/H0/MergeLaw/TiedFull.lean); `blind_decT`, `blind_smp`
(BlindAtAll.lean); `merge_at_linkAt` (Johnson/ToldDescR/MergeAtLinkAt.lean); `fence_at_merge`
(FenceAtMerge.lean) and `fence_at_three` (FenceAtBaseThree.lean): the
fence at the base of the piece at 346, in the law's two forms, from hc and the closed test low;
`htr_hms_at` (ToldAt.lean): the numbers of trees and of messages at the two places; `runs_in_frame`
(RunsPassAtMerge.lean) at `runsAre_at_link24` (RunsAreAtLink.lean) and `linkAt_of_open`
(Johnson/ToldDescR/PureChainOfOpen.lean): `RunsPass` at nine runs, from
speaks and leaves; from it `keep_at_merge_on` (KeepAtMerge.lean) and `fwd_of_runsPass`
(RunsAtMerge.lean): the eight public tests and `Fwd` at ten runs; `worth_at_merge`
(WorthAtMerge.lean): the two items "worth", from digThere.

Limits. A MEMBER OF THE HEAD IS PROVED AT `storedPublicFiles` AND `zGap` ALONE (AT secondHashFunction; SIDE LIBRARY
AtFullSide/Top/). NO CONDITION OF `K11Cond`
IS SHOWN HERE; that they can be met together is shown nowhere. Rch is a letter: at "never" the end
is free and says nothing. The rows' extractors, c₀ and tokOf are letters. Nothing on soundness.

-/
import Johnson.K11R.LawAtThree
import Johnson.K11R.AtAll
import Johnson.Top.H0.MergeLaw.TiedFull
import Johnson.Top.H0.MergeLaw.BlindAtAll
import Johnson.Top.H0.MergeLaw.FenceAtBaseThree
import Johnson.Top.H0.MergeLaw.RunsAtMerge
import Johnson.Top.H0.MergeLaw.WorthAtMerge
import Johnson.Top.H0.MergeLaw.RunsPassAtMerge
import Johnson.Top.H0.MergeLaw.RunsAreAtLink
import Johnson.ToldDescR.PureChainOfOpen
import Johnson.K11R.ToldAt
import Johnson.Goal.Meaning.PlanShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace K11

open Iop
open OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj
open _root_.Run (ckP)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName Wit Claim)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S HeadOwn ModelPart Item Pub Meaning Numbers start flatPlacesOf
  openSets pubSets pubRowM sampledIn)
open VerifiableInference.Desc.First.MergeLaw
open VerifiableInference.Reads.Pass (Fwd)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide)
open VerifiableInference.Desc.Sound.MgAt (mergeAt behindAt)
open P5J (AtMgA mgAtAll TS)
open ProofFile (Cl)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {F : FileDescription ProofFile.Inst} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- The witness's type at the constant. -/
abbrev WAt : Type :=
  Wit (CellsQ OnBytes.Flat.numsFull.rows (P5J.colsAt OnBytes.Flat.numsFull)) P5J.At.Tok MsgT

/-- **THE NAMED CONDITIONS UNDER WHICH THE KIND K11's LAW HOLDS AT THE COMPOSED MEANING's CLOSED
CONSTANT.** Fr: the first chain's frame; Rch: "reached". -/
structure K11Cond (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bs : ProofFile.PureBase) {Fr : Frame}
    (Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop)
    (xM xI : Mem) (posI : ℕ → Bool × ℕ × ℕ) (ni R : ℕ) (Wa : S → Prop) : Prop where
  /-- closed tests, with code, off the public parameters alone -/
  nums : numsB Zp 24 OnBytes.Flat.numsFull.rows = true
  oneClaim : nclB Zp 24 1 = true
  pendAll : pendAllB (parOf Zp Bs.G₀).lay h.𝔇.d1.lin = true
  /-- the reading of the two oracle messages' mask tables -/
  niPos : 0 < ni
  inM : ∀ j, j < (parOf Zp Bs.G₀).nMsg → InMsg h.𝔇.cs (xM.1.l.get xM.2).1 (posMask R j).1
    (posMask R j).2.1 (posMask R j).2.2
  inI : ∀ j, j < ni → InMsg h.𝔇.cs (xI.1.l.get xI.2).1 (posI j).1 (posI j).2.1 (posI j).2.2
  /-- the fence: a closed test: every sampled place that is open at 346 has its tree among those
  that the written rows in front of 346 tell -/
  low : lowAtB h.𝔇.N open346 (treesInFront VerifiableInference.PlanWritten.cutFirstFull 346) = true
  /-- the lemma that joins the two sentences for "weights" -/
  weights : ∀ a y w, Wa a.2 → VerifiableInference.Desc.First.FillP1.wtP1 (parOf Zp Bs.G₀) ni
    (fun w => VerifiableInference.Desc.K13.Law.cellAtNo w.cells)
    (maskRowAt h.𝔇.cs h.𝔇.arr h.𝔇.ms h.𝔇.N 24) a y w → h.𝔇.wt 24 a y w
  /-- facts on a reached state in front of the merge -/
  front : ∀ (z : ProofFile.InstPub) (a : S × Fr.E.Str),
    onQ h.𝔇.N (mgAtAll h) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346 a →
    Rch 346 ((z, a.1), a.2) → ¬ a.1.failed ≠ none → MergeFront (h.𝔇.N.group 24) xM R ni a.1
  frontWa : ∀ (z : ProofFile.InstPub) (a : S × Fr.E.Str),
    onQ h.𝔇.N (mgAtAll h) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346 a →
    Rch 346 ((z, a.1), a.2) → ¬ a.1.failed ≠ none → Wa a.1
  behindIdx : ∀ (z : ProofFile.InstPub) (a b : S × Fr.E.Str),
    onQ h.𝔇.N (mgAtAll h) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346 a →
    Rch 346 ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
    (∃ rs, headMergeDecide (parOf Zp Bs.G₀) a.1 rs = .ok b.1) → idxAt h.𝔇 ni posI xI b.1
  /-- tests with code at a reached state in front of the merge: at five runs of claims of the head's
  segment the stated run's own reader answers; the leaves' walk has the shape's length -/
  speaks : ∀ l, cF.links[24]? = some l → ∀ (z : ProofFile.InstPub) (a : S × Fr.E.Str),
    onQ h.𝔇.N (mgAtAll h) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346 a →
    Rch 346 ((z, a.1), a.2) → ¬ a.1.failed ≠ none → Speaks l a.1
  leaves : ∀ (z : ProofFile.InstPub) (a : S × Fr.E.Str),
    onQ h.𝔇.N (mgAtAll h) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346 a →
    Rch 346 ((z, a.1), a.2) → ¬ a.1.failed ≠ none → leavesLenB a.1 = true
  /-- the public parameters give segment 24 a lookup on the digits -/
  digThere : ∃ xd tl, VerifiableInference.Desc.First.Look.digAt (P5J.At.X Zp) 24 = some (xd, tl)

/-- The merge's row makes no public item anew. -/
theorem makes346 : (pubRowM moreAll linksFull mergeAt).makes = [] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **THE KIND K11's OWN SENTENCE: THE NAMED CONDITIONS GIVE ITS SHARE OF THE CHAIN OF PROMISES, AT
THE CLOSED CONSTANT, THE WRITTEN LIST, THE TABLE's OWN EXTRACTOR AND THE THREE ROWS OF PIECES WITH
THE CAP.** -/
theorem k11_law_atMg (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A B)
    {D' : WholeD} {file : String} (hD : (FD Zp A B cF).data file = .ok D')
    (hp : (FD Zp A B cF).planOk = true)
    {b₁ : Block (FD Zp A B cF).S₁ (FD Zp A B cF).Cl}
    {l₁ : List (Block (FD Zp A B cF).S₁ (FD Zp A B cF).Cl)}
    {b₂ : Block (FD Zp A B cF).S₂ (FD Zp A B cF).Cl}
    {l₂ : List (Block (FD Zp A B cF).S₂ (FD Zp A B cF).Cl)}
    {b₃ : Block (FD Zp A B cF).S₃ (FD Zp A B cF).Cl}
    {l₃ : List (Block (FD Zp A B cF).S₃ (FD Zp A B cF).Cl)}
    (q₁ : (FD Zp A B cF).first.blocksInOrder = b₁ :: l₁) (q₂ : (FD Zp A B cF).shared.blocksInOrder = b₂ :: l₂)
    (q₃ : (FD Zp A B cF).second.blocksInOrder = b₃ :: l₃)
    (e₁ : (i : ℕ) → (ds : List RDT) →
      ((FD Zp A B cF).XiPub × (FD Zp A B cF).S₁) × (frameAt D' (allOf D') D'.key₁ 0).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → WAt → WAt)
    (e₂ : (i : ℕ) → (ds : List RDT) →
      (((FD Zp A B cF).XiPub × (FD Zp A B cF).S₁) × (FD Zp A B cF).S₂) ×
        (frameAt D' (allOf D') D'.key₂ 0).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → WAt → WAt)
    (e₃ : (i : ℕ) → (ds : List RDT) →
      (((FD Zp A B cF).XiPub × (FD Zp A B cF).S₁ × (FD Zp A B cF).S₂) × (FD Zp A B cF).S₃) ×
        (frameAt D' (allOf D') D'.key₃ (FD Zp A B cF).lastChainFirstTreeNumber).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → WAt → WAt)
    (dW wEnd : WAt)
    (c₀ : CellsQ OnBytes.Flat.numsFull.rows (P5J.colsAt OnBytes.Flat.numsFull))
    (tokOf : ProofFile.InstPub × S → P5J.At.Tok)
    (Rch : ℕ → (ProofFile.InstPub × S) × (frameAt D' (allOf D') D'.key₁ 0).E.Str → Prop)
    (tm : k11AtRB Zp 24 = true)
    (hc : VerifiableInference.PlanWritten.cutOf (FD Zp A B cF).first.blocksInOrder =
      VerifiableInference.PlanWritten.cutFirstFull)
    (K : ∀ (pM : ℕ × ℕ) (xM xI : Mem),
      maskPlace (P5T.planSeats Zp Zp.D.1) Zp.first.shape 24 = some pM →
      xAt (P5J.At.ms Zp Z.lay) pM = some xM →
      xAt (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF).index = some xI →
      ∃ (posI : ℕ → Bool × ℕ × ℕ) (ni R : ℕ) (Wa : S → Prop),
        K11Cond h Bs Rch xM xI posI ni R Wa) :
    KindTiedR h.𝔇.N (mgAtAll h) linksFull (flatPlacesOf linksFull true) Rch
      (fun i => extQAt h.𝔇.cs h.𝔇.G h.𝔇.arr h.𝔇.smp h.𝔇.ms h.𝔇.decT c₀ tokOf h.𝔇.N linksFull
        (flatPlacesOf linksFull true) (fun a => a) i)
      ((threeCap (FD Zp A B cF) D' b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ dW wEnd).p₁ ::
        (threeCap (FD Zp A B cF) D' b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ dW wEnd).l₁) KindName.K11 := by
  obtain ⟨pM, xM, xI, hpM, hM, hI, hsent⟩ := members_atAll Zp cF Z.lay tm
  obtain ⟨posI, ni, R, Wa, C⟩ := K pM xM xI hpM hM hI
  refine k11_law_atThree h.scope h.reads O hD hp q₁ q₂ q₃ h.𝔇 e₁ e₂ e₃ dW wEnd c₀ tokOf Rch ?_
  intro q hq herr hback he hkd hseat
  obtain ⟨b, hS, hqb⟩ := hseat
  have hlow := (fence_at_three hD hp q₁ q₂ q₃ e₁ e₂ e₃ dW wEnd hc h.𝔇.N [] C.low rfl q hq).1
  obtain ⟨s₀, p3, lkW, hw, hn, M⟩ := mergeFill_atAll h O C.nums C.oneClaim pM xM xI hM hI hsent
    posI ni R Wa C.weights
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some Bs.G₀ := (IM.base_made O.made).2.2.1
  have eM : seatOf xM = pM :=
    of_decide_eq_true (List.find?_some (p := fun y => decide (seatOf y = pM)) hM)
  have eI : seatOf xI = (P5J.At.N Zp cF).index := of_decide_eq_true
    (List.find?_some (p := fun y => decide (seatOf y = (P5J.At.N Zp cF).index)) hI)
  have hfen : Fenced q.base [xM, xI] := by
    have f := fence_at_merge h.𝔇.N q.base hlow [xM, xI]
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact f pM (List.mem_cons_of_mem _ hsent) y (by simp) eM y (List.mem_singleton.2 rfl)
    · obtain rfl := List.mem_singleton.1 hy
      exact f _ (List.mem_cons_self ..) y (by simp) eI y (List.mem_singleton.2 rfl)
  have hmk : ∀ (z : ProofFile.InstPub) (b : S × (frameAt D' (allOf D') D'.key₁ 0).E.Str),
      ∀ p ∈ (pubRowM (mgAtAll h).more linksFull mergeAt).makes,
      p ∉ (pubSets (mgAtAll h).more linksFull (flatPlacesOf linksFull true))[346]?.getD [] →
      (mgAtAll h).pubP p (z, b.1) := by
    intro z b p hp
    have e : (mgAtAll h).more = moreAll := (mgAll_more_base h.𝔇).trans mgMore_is
    rw [e, makes346] at hp
    cases hp
  obtain ⟨l, name, rr, hlk, hst, hr⟩ := ToldDesc.merge_at_linkAt h.scope h.reads O
  obtain ⟨htr, hms⟩ := htr_hms_at h.toAtMg
  have hH : VerifiableInference.OnPublicFiles.headLink (P5J.At.X Zp) = 24 := by
    obtain ⟨p4, ng, -⟩ := Meaning.scope_plans h.scope h.reads h.pubOne
    unfold VerifiableInference.OnPublicFiles.headLink
    rw [p4, ng]
    rfl
  obtain ⟨Lk, iU3, lm, hLk, -, -, HR⟩ := runsAre_at_link24 h.scope h.reads O
  have hlk24 : h.𝔇.lk 24 = some Lk := (ToldDesc.linkAt_of_open O 24).trans hLk
  have HR' : RunsAre Lk (P5J.At.X Zp) iU3 lm := by
    have e := HR
    rw [O.W] at e
    exact e
  have hruns := runs_in_frame h.𝔇 mgBase rfl hH (parOf Zp Bs.G₀) h.𝔇.N Rch hlk24 HR'
    (C.speaks Lk hLk) C.leaves
  have hkeep : ∀ (z : ProofFile.InstPub) (a b : S × (frameAt D' (allOf D') D'.key₁ 0).E.Str),
      onQ h.𝔇.N (mgAtAll h) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346 a →
      Rch 346 ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
      (∃ rs, headMergeDecide (parOf Zp Bs.G₀) a.1 rs = .ok b.1) →
      ∀ p ∈ keep24, (mgAtAll h).pub p (z, a.1) = true → (mgAtAll h).pub p (z, b.1) = true := by
    intro z a b ha hR hm hy
    obtain ⟨rs, hyes⟩ := hy
    exact keep_at_merge_on h.𝔇 mgBase rfl rfl hH (parOf Zp Bs.G₀) h.𝔇.N z a b ha
      (Classical.not_not.1 hm) hyes (hruns z a b ha hR hm ⟨rs, hyes⟩)
  have hfwd : ∀ (z : ProofFile.InstPub) (a b : S × (frameAt D' (allOf D') D'.key₁ 0).E.Str),
      onQ h.𝔇.N (mgAtAll h) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346 a →
      Rch 346 ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
      (∃ rs, headMergeDecide (parOf Zp Bs.G₀) a.1 rs = .ok b.1) →
      ∀ y ∈ sixNames, ∀ p ∈ h.𝔇.runs 24 y.1 y.2, Fwd (h.𝔇.Rd 24) p.1 p.2 a.1 b.1 := by
    intro z a b ha hR hm hy
    obtain ⟨rs, hyes⟩ := hy
    exact fwd_of_runsPass h.𝔇 rfl (parOf Zp Bs.G₀) hyes (hruns z a b ha hR hm ⟨rs, hyes⟩)
  have hworth : ∀ (z : ProofFile.InstPub) (a b : S × (frameAt D' (allOf D') D'.key₁ 0).E.Str) w,
      onQ h.𝔇.N (mgAtAll h) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346 a →
      Rch 346 ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
      (∃ rs, headMergeDecide (parOf Zp Bs.G₀) a.1 rs = .ok b.1) →
      ∀ j ∈ worthAtMerge, meansQ h.𝔇.N (mgAtAll h) (fun s => (z, s)) j b w →
        meansQ h.𝔇.N (mgAtAll h) (fun s => (z, s)) j a w := by
    intro z a b w ha _ hm hy
    obtain ⟨rs, hyes⟩ := hy
    obtain ⟨xd, tl, hx⟩ := C.digThere
    exact worth_at_merge h.𝔇 hH hx (parOf Zp Bs.G₀) h.𝔇.N z a b w ha (Classical.not_not.1 hm) hyes
  exact merge_tied_full h.𝔇 rfl q (parOf Zp Bs.G₀) b hS hqb Rch he hkd hback herr
    (fun c => VerifiableInference.Desc.K13.Law.cellAtNo c) xM xI posI ni R Wa hw hn C.niPos C.inM
    C.inI hfen M (hlay_at hG) (ncl_of_test C.oneClaim) (nums_of_test hG C.nums).1 C.pendAll l
    name rr hlk hst hr htr hms (blind_decT h) (blind_smp h) hlow C.front C.frontWa
    C.behindIdx hkeep hmk hfwd hworth

end K11

#print axioms K11.makes346
#print axioms K11.k11_law_atMg
