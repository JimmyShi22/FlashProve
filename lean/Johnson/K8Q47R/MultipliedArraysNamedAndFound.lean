--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/- Johnson/K8Q47R/MultipliedArraysNamedAndFound.lean: KIND K8, part 1's ROW K8-q47: WHAT ITS CLOSED TEST k8AllNowB
SAYS, AS A THEOREM UNDER THE HEAD: at each of the 25 links l, at the blank ground's built link Xl:
EVERY ARRAY THAT THE SMALLNESS TEST's MATRIX MULTIPLIES (`Named.arrays Xl.tl`: the matrices' arrays
and the vectors of reads') IS NAMED in Xl's list, LAID in the request's layout, LIES IN A MESSAGE OF
THE REQUEST's SHAPE, AND THAT MESSAGE IS FOUND at moment 2 of link l. NO CODING THEORY.
  planH2_U · public_U    the output head's plan names array 0 for the third vector of reads and none
                         for the other three (the walk is ReadsNamed.planH2_third's, ended by part
                         3's u3_made)
  built_plan             the ground's built link l has the plan's own structure tl of the smallness
                         test (IM.ground_tails)
  U_of_plan · reads_list so at every link the vectors' arrays are the list [0]
  u3AtB · u3WB · u3WB_all   THE CLOSED TEST AT THE WRITTEN VALUES, at all 25 links, by Lean's
                         kernel: the written layout has (l, "U3"); its message is in the written
                         shape; it is found in the written own list at moment 2
  u3_rejects             THREE BENDS, EACH REFUSED AT EACH OF THE 25 LINKS (blunt: a clause struck
                         whole)
  cutOwn · cutMsgs · u3TightB · u3_tight   TWO BENDS THAT BITE BY ONE ENTRY, at each of the 25:
                         with the own lists (the shape's lists of messages) cut behind the entry of
                         U3's message the test says yes; cut in front of it: no
  gt_len                 the written views have as many arrays of matrices as matrices
  **arrays_at**          under the head the list of arrays is the written view's list and [0]: so it
                         is never empty
  **allNow_parts**       see its statement
Called: K8Q35.names_all · mats_at · mats_there · tail_at · lab_of_view · own2_congr
(Johnson/K8Q35R/) · P5J.K8N.u3_at_ground (Johnson/P5J/K8U3Named.lean) · planG_u3 · u3_made
(Johnson/Road/K4/Rec/) · K5Law.ofPlan_U · P1K8T.planAt_tlAt · IM.ground_tails.
WHERE IT HOLDS: FROM THE HEAD WITH THE THIRTEEN ENTRY TESTS: BOTH ROWS ON WRITTEN VALUES ARE SPENT:
made_accepts (the layout, the shape, the views of tl; that a matrix's number is below NM goes by the
written view too) and, through told_at_head, the written cut (the own list; and in mats_at). From
the goals' scope alone: the name at U3 and the list [0].
Limits. A MEMBER OF THE HEAD IS PROVED AT `storedPublicFiles` AND `zGap` ALONE (AT secondHashFunction; SIDE LIBRARY
AtFullSide/Top/). At OnBytes.secondHashFunction and the full size alone. The test asks
"found", not "found in front of the draw": at U3 nobody says the latter here. hL serves mats_at
alone. u3_rejects and u3_tight bend u3AtB, not k8AllNowB (bent twins of that: not in this file).
u3_tight ADDS NO FACT ON THE WRITTEN DATA: its two refusals are forced by the test's text at any
data, its two accepts by u3WB_all: it shows that the test hangs on the presence of that one entry.
That the moment is 2 and not 1 is shown by no bend. arrays_at is called by nobody yet. Nothing on
soundness.
-/
import Johnson.K8Q35R.MatsAtHead
import Johnson.P5J.K8U3Named
import Johnson.Road.K4.Rec.U3Tree
import Johnson.Desc.First.Att.Claims.OfPlan
import Johnson.Desc.Kinds.Law.ReadsNamed
import Johnson.IMR.K8Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace K8Q47

open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj Johnson.Pack
open OnBytes.Params (ReqArray ReqMessage)
open OnBytes.Model.Stages (LinkH)
open Johnson.G (xShapeFull layoutFull)
open Iop
open VerifiableInference.Desc (Block Chain Place Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.ReqLit (shapeFull)
open VerifiableInference.Desc.First (S ModelPart Numbers FoldData FoldFacts flatPlacesOf toldCut msgsTold)
open VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.LinkJoin (whereD)
open VerifiableInference.Desc.K13.Law (LFull MFull)
open VerifiableInference.PlanWritten (TailView tailView)
open ProofFile (Cl)
open P5J (AtMg AtMgA)
open P1K8T
open K8Q35

/-! ## 1 The vectors of reads' arrays -/

section
open OnBytes.Model.HTailF2 Fo Fo.Pub Fo.ZPlan
open Fo.BatRows (bindE_ok ite_ok)

/-- The output head's plan: array 0 for the third vector of reads, none for the other three. -/
theorem planH2_U (g : Settings) (h : Head.Shape) (L : Head.HL) (b : Head.Border)
    (O : Head.Owner) (NGr lkW : Nat) (hp : Head.HPlanH2)
    (e : Head.planH2 g h L b O NGr lkW = .ok hp) :
    hp.tl.ix.U = #[none, none, some 0, none] := by
  unfold Head.planH2 at e
  repeat obtain ⟨_, _, e⟩ := bindE_ok e
  dsimp only at e
  split at e
  · obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨tl, hS, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨⟨tl1, Fp, Tp⟩, hA, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨tl2, hO, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    cases e
    exact (OnBytes.Road.K4.Rec.u3_made hS hA (ownerHeld_sameP hO)).1
  · obtain ⟨_, hx, _⟩ := bindE_ok e
    cases hx

theorem public_U {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) : X.H.tl.ix.U = #[none, none, some 0, none] := by
  obtain ⟨H0, h0, e⟩ := public_H h
  rw [e]
  exact planH2_U _ _ _ _ _ _ _ H0 h0

end

/-- **The ground's built link l has the plan's own structure tl of the smallness test.** -/
theorem built_plan {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub}
    {G : ProofFile.Ground} (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G) {l : ℕ} (hl : l ≤ 24) {Xl : LinkH}
    (e3 : G.built[l]? = some Xl) : P1K8S.PlanAt G.W l Xl.tl := by
  obtain ⟨hT, Xh, eh, th, -⟩ := IM.ground_tails hS hR hZ hG
  rcases Nat.lt_or_ge l 24 with h24 | h24
  · rcases Nat.even_or_odd' l with ⟨g, rfl | rfl⟩
    · obtain ⟨hp, a, x, x', eG, eA, ex, tx, -, -, -, -, ex', tx', -⟩ := hT g (by omega)
      obtain rfl : x = Xl := Option.some.inj (ex.symm.trans e3)
      exact Or.inr (Or.inl ⟨g, hp, by omega, rfl, eG, tx⟩)
    · obtain ⟨hp, a, x, x', eG, eA, ex, tx, -, -, -, -, ex', tx', -⟩ := hT g (by omega)
      obtain rfl : x' = Xl := Option.some.inj (ex'.symm.trans e3)
      exact Or.inr (Or.inr ⟨g, a, by omega, rfl, eA, tx'⟩)
  · obtain rfl : l = 24 := by omega
    obtain rfl : Xh = Xl := Option.some.inj (eh.symm.trans e3)
    exact Or.inl ⟨rfl, th⟩

/-- In every plan's structure tl the vectors' arrays are: none, none, array 0, none. -/
theorem U_of_plan {pol KL : ByteArray} {layout : Option ByteArray} {W : Verify.Public}
    (hX : Verify.publicOf pol KL layout = .ok W) {l : ℕ} {tl : HTailF2}
    (h : P1K8S.PlanAt W l tl) : tl.ix.U = #[none, none, some 0, none] := by
  rcases h with ⟨-, rfl⟩ | ⟨g, hp, -, -, e, rfl⟩ | ⟨g, a, -, -, e, rfl⟩
  · exact public_U hX
  · exact (OnBytes.Road.K4.Rec.planG_u3 _ _ _ _ (Fo.Pub.public_G hX g hp e)).1
  · exact K5Law.ofPlan_U (K5Law.public_ofPlan hX g a e)

theorem reads_list {tl : HTailF2} (h : tl.ix.U = #[none, none, some 0, none]) :
    ((List.range 4).filterMap fun n => tl.ix.U.getD n none) = [0] := by
  rw [h]
  rfl

/-! ## 2 The closed tests at the written values -/

/-- The test at link l, at any layout, shape and data. -/
def u3AtB (lay : OnBytes.Params.ReqLayout) (d : FoldData) (l : ℕ) : Bool :=
  match OnBytes.reqArray lay l "U3" with
  | some A =>
    (_root_.Meaning.messageAt d.sent.shape l A.message).isSome && (whereD d l 2 l A.message).isSome
  | none => false

/-- **THE CLOSED TEST AT LINK l.** -/
def u3WB (l : ℕ) : Bool := u3AtB layoutFull dW l

set_option maxRecDepth 1000000 in
/-- **IT ACCEPTS AT ALL 25 LINKS**: by an evaluation in Lean's kernel. -/
theorem u3WB_all : ((List.range 25).all u3WB) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **THREE BENDS, EACH REFUSED AT EACH OF THE 25 LINKS**: no layout · no message in the shape · no
own message at any moment. -/
theorem u3_rejects : ((List.range 25).any fun l =>
    u3AtB { layoutFull with link := [] } dW l ||
      u3AtB layoutFull
        { dW with sent := { dW.sent with shape := { shapeFull with link := [] } } } l ||
      u3AtB layoutFull { dW with ownAt := fun _ _ => #[] } l) = false := by
  decide +kernel

/-- The written data with every own list cut behind its first k entries. -/
def cutOwn (k : ℕ) : FoldData :=
  { dW with ownAt := fun m t => ((dW.ownAt m t).toList.take k).toArray }

/-- The written data with every link's list of messages in the shape cut behind its first k. -/
def cutMsgs (k : ℕ) : FoldData :=
  { dW with sent := { dW.sent with shape := { shapeFull with
      link := shapeFull.link.map fun L => { L with messages := L.messages.take k } } } }

/-- Two bends that bite by one entry, at link l, j the number of U3's message: the own lists cut
behind entry j: yes; in front of it: no. The like of the shape's lists of messages. -/
def u3TightB (l : ℕ) : Bool :=
  match OnBytes.reqArray layoutFull l "U3" with
  | some A =>
    u3AtB layoutFull (cutOwn (A.message + 1)) l && !u3AtB layoutFull (cutOwn A.message) l &&
      u3AtB layoutFull (cutMsgs (A.message + 1)) l && !u3AtB layoutFull (cutMsgs A.message) l
  | none => false

set_option maxRecDepth 1000000 in
/-- **THE TEST HANGS ON JUST THAT ENTRY, AT EACH OF THE 25 LINKS.** -/
theorem u3_tight : ((List.range 25).all u3TightB) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The written views have as many arrays of matrices as matrices. -/
theorem gt_len : ((List.range 25).all fun l => decide ((tvW l).2.2.length = nmW l)) = true := by
  decide +kernel

/-! ## 3 Under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **UNDER THE HEAD THE ARRAYS ARE THE WRITTEN VIEW's LIST AND [0].** From the head with the
thirteen entry tests (made_accepts is spent). -/
theorem arrays_at (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : ℕ} (hl : l ≤ 24) {Xl : LinkH}
    (e3 : G.built[l]? = some Xl) : Named.arrays Xl.tl = (tvW l).2.2 ++ [0] := by
  have hy := h.toAtMg.made_accepts
  obtain ⟨pp, hR⟩ := IM.reads_of_scope h.scope
  have hpub : Verify.publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X := by
    rw [← VerifiableInference.PlanWritten.publicOfO_older]
    exact ProofFile.Law.pub_public h.laid.pub
  have eTV := tail_at h.scope hR hpub
    (VerifiableInference.PlanWritten.Joined.xShape_in_scope h.scope h.laid.pub hy) hl
  have hP := built_plan h.scope hR h.laid.pub hG hl e3
  rw [ProofFile.Law.blankBy_W hG] at hP
  have etl : Xl.tl = Meaning.tlAt (P5J.At.X Zp) l := planAt_tlAt hP
  have eGT : (Meaning.tlAt (P5J.At.X Zp) l).gtTree.toList = (tvW l).2.2 := congrArg (·.2.2) eTV
  unfold Named.arrays
  rw [reads_list (U_of_plan hpub hP), etl, eGT]

/-- **EVERY ARRAY THAT THE MATRIX MULTIPLIES IS NAMED, LAID, IN A MESSAGE OF THE SHAPE, FOUND.**
From the head with the thirteen entry tests: both rows on written values are spent. -/
theorem allNow_parts (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    {L₀ : VerifiableInference.Desc.K12.Door.Laid} (hL : P5J.At.laid? Zp = some L₀)
    {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : ℕ} (hl : l ≤ 24)
    {Xl : LinkH} (e3 : G.built[l]? = some Xl) :
    ∀ t ∈ Named.arrays Xl.tl, ∃ (x : ℕ × String) (a : ReqArray) (m : ReqMessage) (o : ℕ),
      Xl.arrayOf[t]? = some x ∧ OnBytes.reqArray (P5J.At.layout Zp) x.1 x.2 = some a ∧
      _root_.Meaning.messageAt (P5J.At.foldD Zp cF L₀).sent.shape x.1 a.message = some m ∧
      whereD (P5J.At.foldD Zp cF L₀) l 2 x.1 a.message = some o := by
  intro t ht
  have hy := h.toAtMg.made_accepts
  obtain ⟨pp, hR⟩ := IM.reads_of_scope h.scope
  have hpub : Verify.publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X := by
    rw [← VerifiableInference.PlanWritten.publicOfO_older]
    exact ProofFile.Law.pub_public h.laid.pub
  have eF := VerifiableInference.PlanWritten.Joined.first_written_in_scope h.scope h.laid.pub hy
  have eSh : P5J.At.shape Zp = shapeFull :=
    eF.2.2.1.trans VerifiableInference.PlanWritten.request_shape_written
  have eLy : P5J.At.layout Zp = layoutFull := eF.2.2.2.2.2
  have eT := h.toAtMg.told_at_head
  have eTV := tail_at h.scope hR hpub
    (VerifiableInference.PlanWritten.Joined.xShape_in_scope h.scope h.laid.pub hy) hl
  have eW : G.W = Zp.p.X := ProofFile.Law.blankBy_W hG
  have hP := built_plan h.scope hR h.laid.pub hG hl e3
  rw [eW] at hP
  have etl : Xl.tl = Meaning.tlAt (P5J.At.X Zp) l := planAt_tlAt hP
  have eU := U_of_plan hpub hP
  have hl' : l ∈ List.range 25 := List.mem_range.2 (Nat.lt_succ_of_le hl)
  unfold Named.arrays at ht
  rw [reads_list eU] at ht
  rcases List.mem_append.1 ht with ht | ht
  · rw [etl] at ht
    obtain ⟨μ, hμ, rfl⟩ := List.mem_iff_getElem.1 ht
    have eGT : (Meaning.tlAt (P5J.At.X Zp) l).gtTree.toList = (tvW l).2.2 := congrArg (·.2.2) eTV
    have eNM : (Meaning.tlAt (P5J.At.X Zp) l).NM = nmW l := congrArg (·.1) eTV
    have hNM : μ < (Meaning.tlAt (P5J.At.X Zp) l).NM := by
      have c := of_decide_eq_true (List.all_eq_true.1 gt_len l hl')
      rw [eNM, ← c, ← eGT]
      exact hμ
    have e0 : (Meaning.tlAt (P5J.At.X Zp) l).gtTree.getD μ 0 =
        (Meaning.tlAt (P5J.At.X Zp) l).gtTree.toList[μ] := by
      rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, List.getElem?_eq_getElem hμ]
      rfl
    have hn := names_all h hG hl e3 μ hNM
    rw [e0] at hn
    have eLab : Meaning.labAt (P5J.At.X Zp) l μ = labW l μ := by
      unfold labW
      rw [← eTV]
      exact (lab_of_view _ μ).symm
    have hth := List.all_eq_true.1 mats_there l hl'
    rw [Bool.and_eq_true] at hth
    have hA0 := List.all_eq_true.1 hth.2 μ (List.mem_range.2 (eNM ▸ hNM))
    obtain ⟨A, hA⟩ := Option.isSome_iff_exists.1 hA0
    rw [← eLab, ← eLy] at hA
    obtain ⟨o, q, msg, ho, -, hm, -⟩ := mats_at h hL hl μ hNM A hA
    exact ⟨_, A, msg, o, hn, hA, hm, ho⟩
  · obtain rfl : t = 0 := List.mem_singleton.1 ht
    have hn := P5J.K8N.u3_at_ground h.laid.pub hG e3 0 (by rw [eU]; rfl)
    have c := List.all_eq_true.1 u3WB_all l hl'
    unfold u3WB u3AtB at c
    split at c
    · rename_i A hA
      rw [Bool.and_eq_true] at c
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 c.1
      obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 c.2
      have eMs : (P5J.At.N Zp cF).msgsAt = NW.msgsAt := by
        funext p
        show msgsTold (P5J.At.told cF) (VerifiableInference.Desc.First.borderOf P5J.At.ps p) =
          msgsTold toldCut (VerifiableInference.Desc.First.borderOf _ p)
        rw [eT]
        rfl
      have eOwn : (P5J.At.foldD Zp cF L₀).ownAt l 2 = dW.ownAt l 2 := by
        show VerifiableInference.Desc.First.FillSent.ownAt (P5J.At.shape Zp) (P5J.At.N Zp cF)
          P5J.At.links P5J.At.ps Zp.made.p.built.links l 2 = _
        rw [eSh]
        exact own2_congr shapeFull P5J.At.links P5J.At.ps Zp.made.p.built.links #[] eMs l
      refine ⟨(l, "U3"), A, m, o, hn, by rw [eLy]; exact hA, ?_, ?_⟩
      · show _root_.Meaning.messageAt (P5J.At.shape Zp) l A.message = some m
        rw [eSh]
        exact hm
      · unfold whereD at ho ⊢
        rw [if_pos (beq_self_eq_true l)] at ho ⊢
        rw [eOwn]
        exact ho
    · cases c

end K8Q47

#print axioms K8Q47.planH2_U
#print axioms K8Q47.public_U
#print axioms K8Q47.built_plan
#print axioms K8Q47.U_of_plan
#print axioms K8Q47.reads_list
#print axioms K8Q47.u3WB_all
#print axioms K8Q47.u3_rejects
#print axioms K8Q47.u3_tight
#print axioms K8Q47.gt_len
#print axioms K8Q47.arrays_at
#print axioms K8Q47.allNow_parts
