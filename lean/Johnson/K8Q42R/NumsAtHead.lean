-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/K8Q42R/NumsAtHead.lean: THE SMALLNESS TEST (K8): THE CLOSED TEST k8NumsB
(Johnson/P1K8R/ShareOfNums.lean) ACCEPTS UNDER THE HEAD, AT ALL 25 SEGMENTS, AT THE PLAN's TERM
k8NumsOf (Johnson/P1K8R/ShareAtDraw.lean). Definitions with code; theorems.
WHICH HEAD. The head over the entry tests'
rows: the rows that compare with written values are spent, as in
Johnson/K8Q35R/MatsAtHead.lean, whose written terms (tvW · nmW · labW · NW · dW) and ties are called
here, not typed anew. What is shown is a fact on the written values. THE ROAD, BY THE NAMED ARRAYS
(not by a wider form, at all numbers of the two frames' lists: that form is not evaluated and very
likely fails: an evaluation of a sister test, on every tenant of the named
trees, said false at all 25: in each segment one laid message has no sample):
  `osW l`: the written numbers: over the matrices' labels of the written shape part, and over the
    four names "U1" to "U4" at segment l: the written layout's array of that name, and `whereD` at
    the written data.
  `k8NumsW`, `k8NumsW_asks`, `k8NumsW_control`, `k8NumsW_control_shape`, `k8NumsW_control_sample`:
    CLOSED FACTS BY THE KERNEL: k8NumsB accepts at osW l at every l < 25 · THE WRITTEN LIST osW l is
    empty nowhere (that the plan's term k8NumsOf is non-empty under the head is NOT said: only that
    it lies inside osW l) · THREE NEGATIVE TESTS, ONE FOR EACH COMPARISON OF THE TEST (its
    fourth way to say no, no place or no shape at a number, has none), each rejected
    at each l: every seat of the written plan one tenant higher (the seats) · every seat's shape
    with one main row more (the shapes) · no answer to a sample in any seat's and any listed shape
    ("has a sample" alone: shapes and seats still agree).

  `gtLenW`: by the kernel: the written view's list of trees is as long as its number of matrices.
  `whereD_congr`: whereD reads of the data ownAt m t, keptAt m and the request's shape alone.
  `built_tl`: the built segment's part for the smallness test is the public data's
    (`IM.ground_tails`; the kind's `planAt_built`, `planAt_tlAt`).
  `nums_in_written`: under the head every number of k8NumsOf lies in osW l: the trees' names by
    `K8Q35.names_all`, the vectors' by `P5J.K8N.un_at_ground`.
  `nums_at_head`.
Limits. The head AtMgA is a premise. At OnBytes.secondHashFunction. The full size alone. Nothing on soundness.

-/
import Johnson.P1K8R.ShareAtDraw
import Johnson.P1K8R.SmallAtDraw
import Johnson.K8Q35R.MatsAtHead
import Johnson.P5J.K8UNamed
import Johnson.P5J.AtMgRAtHead
import Johnson.Desc.First.Att.Door.Law.K5Written
import Johnson.Desc.First.Att.Door.Law.K5WrittenIsFull

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace K8Q42
open OnBytes OnBytes.Model OnBytes.Maker
open OnBytes.Model.Stages (LinkH)
open Johnson.G (layoutFull)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.ReqLit (shapeFull)
open VerifiableInference.Desc.First (S FoldData msgsTold borderOf toldCut)
open VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.LinkJoin (whereD)
open VerifiableInference.Desc.K12.Door (Laid)
open VerifiableInference.Desc.K13.Law (LFull MFull)
open VerifiableInference.PlanWritten (tailView)
open H2K5.Door (pseats_written pseatsW_is)
open P1K8T (k8NumsB k8NumsOf)
open K8Q35 (tvW nmW labW NW dW tail_at lab_of_view own2_congr kept_congr names_all)
open P5J (AtMgA)

/-! ## 1 The written side -/

/-- The number of the message in which the written layout's array (born, name) lies. -/
def msgNoW (l born : ℕ) (name : String) : Option ℕ :=
  (OnBytes.reqArray layoutFull born name).bind fun a => whereD dW l 2 born a.message

/-- **The written numbers at segment l.** -/
def osW (l : ℕ) : List ℕ :=
  ((List.range (nmW l)).filterMap fun μ =>
      msgNoW l (Meaning.ownerK (labW l μ)) (Meaning.nameOf (Meaning.ownerA (labW l μ)))) ++
    (List.range 4).filterMap fun n => msgNoW l l ("U" ++ toString (n + 1))

set_option maxRecDepth 1000000 in
/-- **THE CLOSED FACT.** -/
theorem k8NumsW : ((List.range 25).all fun l => k8NumsB P5T.psFull LFull MFull (osW l)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **It asks something everywhere.** -/
theorem k8NumsW_asks : ((List.range 25).all fun l => !(osW l).isEmpty) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **A negative test on the comparison of seats**: every seat of the written plan one tenant
higher: it rejects at each of the 25 segments. -/
theorem k8NumsW_control : ((List.range 25).any fun l =>
    k8NumsB (P5T.psFull.map fun q => { q with t := q.t + 1 }) LFull MFull (osW l)) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **A negative test on the comparison of shapes**: every seat's shape with one main row more (its
sample and its seat as they are): it rejects at each of the 25 segments. -/
theorem k8NumsW_control_shape : ((List.range 25).any fun l =>
    k8NumsB (P5T.psFull.map fun q =>
      { q with shape := { q.shape with mainRows := q.shape.mainRows + 1 } }) LFull MFull
      (osW l)) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **A negative test on "has a sample"**: no answer to a sample in any seat's shape AND in any
listed shape (so shapes and seats still agree): it rejects at each of the 25 segments. -/
theorem k8NumsW_control_sample : ((List.range 25).any fun l =>
    k8NumsB (P5T.psFull.map fun q => { q with shape := { q.shape with answers := 0 } }) LFull
      (MFull.map fun s => { s with answers := 0 }) (osW l)) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The written view's list of trees is as long as its number of matrices. -/
theorem gtLenW : ((List.range 25).all fun l => (tvW l).2.2.length == nmW l) = true := by
  decide +kernel

/-! ## 2 The ties -/

/-- whereD reads three parts of the data alone. -/
theorem whereD_congr {d d' : FoldData} {m t : ℕ} (e1 : d.ownAt m t = d'.ownAt m t)
    (e2 : d.keptAt m = d'.keptAt m) (e3 : d.sent.shape = d'.sent.shape) (born j : ℕ) :
    whereD d m t born j = whereD d' m t born j := by
  unfold whereD
  rw [e1, e2, e3]

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The built segment's part for the smallness test is the public data's.** -/
theorem built_tl (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : ℕ} (hl : l ≤ 24) {Xl : LinkH}
    (e3 : G.built[l]? = some Xl) : Xl.tl = Meaning.tlAt (P5J.At.X Zp) l := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  have eW : Bs.G₀.W = P5J.At.X Zp := ProofFile.Law.blankBy_W hG
  obtain ⟨hT, -⟩ := IM.ground_tails h.scope h.reads O.pub O.blank
  have key : ∃ tlP, P1K8S.PlanAt Bs.G₀.W l tlP := by
    by_cases h24 : l = 24
    · exact ⟨_, Or.inl ⟨h24, rfl⟩⟩
    · rcases Nat.even_or_odd' l with ⟨g, hg | hg⟩
      · obtain ⟨hp, -, -, -, e, -⟩ := hT g (by omega)
        exact ⟨_, Or.inr (Or.inl ⟨g, hp, by omega, hg, e, rfl⟩)⟩
      · obtain ⟨-, a, -, -, -, e, -⟩ := hT g (by omega)
        exact ⟨_, Or.inr (Or.inr ⟨g, a, by omega, hg, e, rfl⟩)⟩
  obtain ⟨tlP, hP⟩ := key
  rw [← P1K8S.planAt_built h.scope h.reads O e3 hP, ← eW]
  exact P1K8T.planAt_tlAt hP

/-- **Under the head every number of the plan's term is a written one.** -/
theorem nums_in_written (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : ℕ} (hl : l ≤ 24) {Xl : LinkH}
    (e3 : G.built[l]? = some Xl) {o : ℕ}
    (ho : o ∈ k8NumsOf (P5J.At.foldD Zp cF LFull) (P5J.At.layout Zp) Xl l) : o ∈ osW l := by
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
  have eNM : (Meaning.tlAt (P5J.At.X Zp) l).NM = nmW l := congrArg (·.1) eTV
  have eGT : (Meaning.tlAt (P5J.At.X Zp) l).gtTree.toList = (tvW l).2.2 := congrArg (·.2.2) eTV
  have eLen : (Meaning.tlAt (P5J.At.X Zp) l).gtTree.size = nmW l := by
    have e0 := List.all_eq_true.1 gtLenW l (List.mem_range.2 (by omega))
    rw [← Array.length_toList, eGT]
    exact eq_of_beq e0
  have eMs : (P5J.At.N Zp cF).msgsAt = NW.msgsAt := by
    funext p
    show msgsTold (P5J.At.told cF) (borderOf P5J.At.ps p) = msgsTold toldCut (borderOf _ p)
    rw [eT]
    rfl
  have eWh : ∀ born j, whereD (P5J.At.foldD Zp cF LFull) l 2 born j = whereD dW l 2 born j := by
    refine whereD_congr ?_ ?_ eSh
    · show VerifiableInference.Desc.First.FillSent.ownAt (P5J.At.shape Zp) (P5J.At.N Zp cF)
        P5J.At.links P5J.At.ps Zp.made.p.built.links l 2 = _
      rw [eSh]
      exact own2_congr shapeFull P5J.At.links P5J.At.ps Zp.made.p.built.links #[] eMs l
    · show VerifiableInference.Desc.First.FillSent.keptAt (P5J.At.shape Zp) (P5J.At.N Zp cF)
        P5J.At.links P5J.At.ps Zp.made.p.built.links l = _
      rw [eSh]
      exact kept_congr shapeFull P5J.At.links P5J.At.ps Zp.made.p.built.links #[] eMs l
  unfold k8NumsOf at ho
  obtain ⟨t, ht, hto⟩ := List.mem_filterMap.1 ho
  obtain ⟨y, hy1, hy2⟩ := Option.bind_eq_some_iff.1 hto
  rw [eLy] at hy2
  have hno : ∀ born name, y = (born, name) → msgNoW l born name = some o := by
    rintro born name rfl
    unfold msgNoW
    obtain ⟨a, ha, hw⟩ := Option.bind_eq_some_iff.1 hy2
    rw [show OnBytes.reqArray layoutFull born name = some a from ha]
    exact (eWh born a.message).symm.trans hw
  unfold Named.arrays at ht
  rw [built_tl h hG hl e3] at ht
  unfold osW
  rcases List.mem_append.1 ht with h1 | h1
  · obtain ⟨μ, hμ, rfl⟩ := List.mem_iff_getElem.1 h1
    have hμ' : μ < (Meaning.tlAt (P5J.At.X Zp) l).gtTree.size := by
      rwa [Array.length_toList] at hμ
    have eμ : (Meaning.tlAt (P5J.At.X Zp) l).gtTree.toList[μ] =
        (Meaning.tlAt (P5J.At.X Zp) l).gtTree.getD μ 0 := by
      rw [Array.getElem_toList, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hμ']
      rfl
    rw [eμ, names_all h hG hl e3 μ (by omega)] at hy1
    have eLab : Meaning.labAt (P5J.At.X Zp) l μ = labW l μ := by
      unfold labW
      rw [← eTV]
      exact (lab_of_view _ μ).symm
    rw [eLab] at hy1
    exact List.mem_append_left _ (List.mem_filterMap.2
      ⟨μ, List.mem_range.2 (by omega), hno _ _ (Option.some.inj hy1).symm⟩)
  · obtain ⟨n, hn, hU⟩ := List.mem_filterMap.1 h1
    have hn4 : n < 4 := List.mem_range.1 hn
    have hU' : Xl.tl.ix.U[n]? = some (some t) := by
      rw [built_tl h hG hl e3]
      rw [Array.getD_eq_getD_getElem?] at hU
      cases hq : (Meaning.tlAt (P5J.At.X Zp) l).ix.U[n]? with
      | none => rw [hq] at hU; exact absurd hU (by simp)
      | some v => rw [hq] at hU; exact congrArg some hU
    rw [P5J.K8N.un_at_ground h.laid.pub hG e3 n t hn4 hU'] at hy1
    exact List.mem_append_right _ (List.mem_filterMap.2
      ⟨n, hn, hno _ _ (Option.some.inj hy1).symm⟩)

/-- **k8NumsB UNDER THE HEAD, AT ALL 25 SEGMENTS.** -/
theorem nums_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {L₀ : Laid}
    (hL : P5J.At.laid? Zp = some L₀) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : ℕ} (hl : l ≤ 24) {Xl : LinkH}
    (e3 : G.built[l]? = some Xl) :
    k8NumsB (P5J.At.pseats Zp) L₀ (P5J.At.foldD Zp cF L₀).M
      (k8NumsOf (P5J.At.foldD Zp cF L₀) (P5J.At.layout Zp) Xl l) = true := by
  obtain rfl : LFull = L₀ := Option.some.inj (h.toAtMg.laid_at_head.symm.trans hL)
  have eP : P5J.At.pseats Zp = P5T.psFull :=
    (pseats_written h.toAtMg (P5J.madeRow_at_head h.toAtMg)).trans pseatsW_is
  have eM : (P5J.At.foldD Zp cF LFull).M = MFull := h.toAtMg.msgs_at_head
  rw [eP, eM]
  have hF := List.all_eq_true.1 k8NumsW l (List.mem_range.2 (by omega))
  unfold k8NumsB at hF ⊢
  exact List.all_eq_true.2 fun o ho =>
    List.all_eq_true.1 hF o (nums_in_written h hG hl e3 ho)

end K8Q42

#print axioms K8Q42.k8NumsW
#print axioms K8Q42.k8NumsW_asks
#print axioms K8Q42.k8NumsW_control
#print axioms K8Q42.k8NumsW_control_shape
#print axioms K8Q42.k8NumsW_control_sample
#print axioms K8Q42.gtLenW
#print axioms K8Q42.whereD_congr
#print axioms K8Q42.built_tl
#print axioms K8Q42.nums_in_written
#print axioms K8Q42.nums_at_head
