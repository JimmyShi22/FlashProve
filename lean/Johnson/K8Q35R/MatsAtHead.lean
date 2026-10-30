-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/K8Q35R/MatsAtHead.lean: THE THIRD CLOSED SENTENCE OF P1K8T.SmallPlan
(Johnson/P1K8R/SmallAtHead.lean), mats, AS A THEOREM UNDER THE HEAD; AND SO ALL THREE; AND SO kind
K8's FIELD small FROM THE HEAD AND THE FACTS ON REACHED STATES ALONE. A payment beneath kind K8's
frozen condition. IT IMPORTS ThirdParty/.

WHICH HEAD. THE HEAD OVER THE ENTRY TESTS' LIST OF THIRTEEN ROWS
(Johnson/Desc/Laid/ProofAsks.lean): both rows that compare with written values are spent
(AtMg.made_accepts, AtMg.cut_written, Johnson/P5J/NumbersAtHead.lean). Over eight rows nothing here
can be had. WHAT IS SHOWN IS A FACT ON THE WRITTEN VALUES: it holds under the head BECAUSE the
head's own field holds tests that compare with these values. It is no fact on what the maker of the
IOP as written in Lean makes of given public files. THE PRICE IS PAID IN WHETHER THE HEAD CAN BE
MET.
[The list has fourteen rows: the thirteen and one more
(Johnson/Desc/Laid/ProofAsks.lean): so the head says that much more.]

THE ROAD. MatPlan (Johnson/P1K8R/MatAtFold.lean) reads: of the data: ownAt l 2 · keptAt l · the
request's shape · the list of shapes M · the laying's places; the group's tenants; the two
numberings arr and num; a count of messages; and, of the public parameters, how many matrices a link
has and their labels. UNDER THE HEAD EACH IS A WRITTEN VALUE, by a theorem of another file each:
  the shape, the layout     first_written_in_scope (Johnson/Goal/Numbers/MadeInScope.lean)
  M                         AtMg.msgs_at_head (Johnson/P5J/PlanSitsCore.lean)
  the laying                AtMg.laid_at_head (the same file): LFull
  arr, num, the group       seats_written (Johnson/P5T/PlanSeatsTie.lean)
  the counts of messages    AtMg.told_at_head (Johnson/P5J/PlanSitsCore.lean)
  ownAt, keptAt             read of the numbers msgsAt alone, and no built link: own2_congr,
                            kept_congr
  the matrices, the labels  xShape_in_scope (MadeInScope.lean): the tail views: tail_at, lab_of_view

  matsAtB · matsWB      the test at any letters · at the written values
  **matsWB_all**        it accepts at all 25 links: AN EVALUATION IN LEAN's KERNEL
  mats_there            it asks something everywhere: each link has a matrix; every label has its
                        array
  mats_rejects          six bends, each refused at each of the 25 links
                        (weighed by hand: TWO of the six bear news: its docstring)
  mats_named            no silent yes: every matrix's key stands among the seats' keys; no default
                        label is read
  mats_of_written       the sentence at LFull from the test's yes, under the head
  **mats_at**           SmallPlan.mats TO THE LETTER, at any L₀ with At.laid? Zp = some L₀
  **smallPlan_at**      SmallPlan Zp cF L₀ l Xl, whole
  **small_at**          K8LeftT's field small, to the letter: the head · At.laid? Zp = some L₀ ·
                        hG · e3 · hRch · FoldFacts
Limits. The full size alone. A MEMBER OF THE HEAD IS PROVED AT storedPublicFiles AND zGap ALONE (AT secondHashFunction; SIDE
LIBRARY AtFullSide/Top/). FoldFacts IS NOT PAID: it is the other
weight of the field. (Where this and lean/THEOREM.md
differ, the page holds.) At OnBytes.secondHashFunction alone. No soundness statement. Nothing on hiding.
-/
import Johnson.K8Q35R.NamesAll
import Johnson.P1K8R.SmallPlanTest
import Johnson.P5J.PlanSitsCore
import Johnson.Desc.First.Look.K3PlanLetters
import Johnson.Desc.First.Look.DigitsShapeAt
import Johnson.Desc.Ok.PlanWritten.XShapeLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace K8Q35

open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj Johnson.Pack
open OnBytes.Params (ReqArray)
open OnBytes.Model.Stages (LinkH)
open Johnson.G (xShapeFull layoutFull codesFull2)
open Iop
open VerifiableInference.Desc (Block Chain Place Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.ReqLit (shapeFull)
open VerifiableInference.Desc.First (S ModelPart Numbers FoldData FoldFacts flatPlacesOf toldCut msgsTold
  borderOf)
open VerifiableInference.Desc.First.K8
open Johnson.Desc.First.Walk.Tied (RchAt)
open Desc.K14.Law (secondAt seatZ)
open VerifiableInference.Desc.LinkJoin (whereD)
open VerifiableInference.Desc.K13.Law (LFull MFull)
open VerifiableInference.PlanWritten (TailView tailView xShapeOf xShapeIs_of tail_of_is)
open ProofFile (Cl)
open P5J (AtMg AtMgA mgAtAll)
open P1K8T

/-! ## 1 The written side -/

/-- The default matrix's view. -/
def tm0 : ℕ × ℕ × ℕ := (({} : TMat).aId, ({} : TMat).m, ({} : TMat).k)

/-- Segment l's approximate range proof, as the written shape part has it. -/
def tvW (l : ℕ) : TailView := (xShapeFull.1.getD l none).getD (0, [], [])

/-- How many matrices; the label of matrix μ. -/
def nmW (l : ℕ) : ℕ := (tvW l).1
def labW (l μ : ℕ) : ℕ := ((tvW l).2.1.getD μ tm0).1

/-- The written numbers, as far as the sentence reads them. -/
def NW : Numbers := P5T.N0Full.withTold (flatPlacesOf linksFull true) toldCut

/-- The written data, as far as the sentence reads them. -/
def dW : FoldData where
  ft := 0
  L := LFull
  M := MFull
  sent := ⟨codesFull2, shapeFull, layoutFull, #[]⟩
  groupAt := id
  ownAt := VerifiableInference.Desc.First.FillSent.ownAt shapeFull NW linksFull
    (flatPlacesOf linksFull true) #[]
  keptAt := VerifiableInference.Desc.First.FillSent.keptAt shapeFull NW linksFull
    (flatPlacesOf linksFull true) #[]
  free0 := 0
  fvs := []

/-- The test at link l, at any data, groups, numberings and counts: at each matrix of the written
shape part whose label's array the written layout has: matPlanB (P1K8R/SmallPlanTest.lean). -/
def matsAtB (d : FoldData) (own : ℕ → List (ℕ × ℕ)) (arr num : ℕ → ℕ → ℕ) (n : ℕ → ℕ) (l : ℕ) :
    Bool :=
  (List.range (nmW l)).all fun μ =>
    match VerifiableInference.Desc.arrayOf layoutFull (Meaning.ownerK (labW l μ))
      (Meaning.nameOf (Meaning.ownerA (labW l μ))) with
    | some A => matPlanB d (own l) arr num l 2 (n l) (Meaning.ownerK (labW l μ)) A
    | none => true

/-- The written count of oracle messages in front of link l's draw. -/
def nW (l : ℕ) : ℕ := NW.msgsAt (flatPlacesOf linksFull true)[drawAt l]?

/-- **THE CLOSED TEST AT LINK l.** -/
def matsWB (l : ℕ) : Bool :=
  matsAtB dW NW.group (P5T.arrOf P5T.seatsAllFull) (P5T.numOfPlan P5T.seatsAllFull) nW l

set_option maxRecDepth 1000000 in
/-- **THE CLOSED TEST ACCEPTS AT ALL 25 LINKS**: by an evaluation in Lean's kernel. -/
theorem matsWB_all : ((List.range 25).all matsWB) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **IT ASKS SOMETHING EVERYWHERE**: each link has a matrix, and the written layout has the array
of every matrix's label: the arm "none" of the test is met nowhere. -/
theorem mats_there : ((List.range 25).all fun l => decide (0 < nmW l) &&
    (List.range (nmW l)).all fun μ =>
      (VerifiableInference.Desc.arrayOf layoutFull (Meaning.ownerK (labW l μ))
        (Meaning.nameOf (Meaning.ownerA (labW l μ)))).isSome) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **THE NEGATIVE TESTS: SIX BENDS, EACH REFUSED AT EACH OF THE 25 LINKS**: the list of seats
without its first · the list of shapes without its first · no message sent yet · no tenant in the
group · the second numbering one higher · every own and kept message's number one higher.
WEIGHED BY HAND: ONLY TWO OF THE SIX BEAR NEWS: the list of seats without its first
and the list of shapes without its first. The other four could not but be refused: "no message sent
yet" and "no tenant in the group" by the test's own text wherever it asks anything (mats_there);
"the second numbering one higher" by the test's yes at the written values (matsWB_all); the sixth
by the first bend's refusal with that yes: it reads each message's seat one further on, as the
first does. -/
theorem mats_rejects : ((List.range 25).any fun l =>
    matsAtB { dW with L := { LFull with places := LFull.places.drop 1 } } NW.group
        (P5T.arrOf P5T.seatsAllFull) (P5T.numOfPlan P5T.seatsAllFull) nW l ||
      matsAtB { dW with M := MFull.drop 1 } NW.group (P5T.arrOf P5T.seatsAllFull)
        (P5T.numOfPlan P5T.seatsAllFull) nW l ||
      matsAtB dW NW.group (P5T.arrOf P5T.seatsAllFull) (P5T.numOfPlan P5T.seatsAllFull)
        (fun _ => 0) l ||
      matsAtB dW (fun _ => []) (P5T.arrOf P5T.seatsAllFull) (P5T.numOfPlan P5T.seatsAllFull) nW
        l ||
      matsAtB dW NW.group (P5T.arrOf P5T.seatsAllFull)
        (fun b k => P5T.numOfPlan P5T.seatsAllFull b k + 1) nW l ||
      matsAtB { dW with ownAt := fun m t => (dW.ownAt m t).map (· + 1),
                        keptAt := fun m => (dW.keptAt m).map (· + 1) } NW.group
        (P5T.arrOf P5T.seatsAllFull) (P5T.numOfPlan P5T.seatsAllFull) nW l) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **NO SILENT YES**: arrOf beyond the list of seats and numOfPlan at an absent
key both answer the number of keys, so the sentence's last clause could hold of nothing. Here: at
every matrix of every link the second numbering answers BELOW the number of keys: the key is there.
And each written view lists as many matrices as it counts: the default label is read nowhere. -/
theorem mats_named : ((List.range 25).all fun l => decide (nmW l = (tvW l).2.1.length) &&
    (List.range (nmW l)).all fun μ =>
      match VerifiableInference.Desc.arrayOf layoutFull (Meaning.ownerK (labW l μ))
        (Meaning.nameOf (Meaning.ownerA (labW l μ))) with
      | some A => decide (P5T.numOfPlan P5T.seatsAllFull (Meaning.ownerK (labW l μ)) A.message <
          ((P5T.seatsAllFull.map P5T.keyOf).eraseDups).length)
      | none => false) = true := by decide +kernel

/-! ## 2 The tie: under the head all that the sentence reads is a written value -/

/-- The sentence reads of the data five parts alone. -/
theorem matPlan_congr {d d' : FoldData} {own : List (ℕ × ℕ)} {arr num : ℕ → ℕ → ℕ}
    {l t n born : ℕ} {A : ReqArray} (e1 : d.ownAt l t = d'.ownAt l t)
    (e2 : d.keptAt l = d'.keptAt l) (e3 : d.sent.shape = d'.sent.shape) (e4 : d.M = d'.M)
    (e5 : d.L = d'.L) (h : MatPlan d' own arr num l t n born A) :
    MatPlan d own arr num l t n born A := by
  unfold MatPlan whereD at h ⊢
  rw [e1, e2, e3, e4, e5]
  exact h

section
open VerifiableInference.Desc.First.FillSent
variable (shape : Params.ReqShape) {N N' : Numbers}
  (links : List VerifiableInference.Desc.First.ModelPart) (ps : List Place) (b b' : Array LinkH)

/-- The frame's list own at moment 2 reads of the numbers msgsAt alone, and no built link. -/
theorem own2_congr (e : N.msgsAt = N'.msgsAt) (m : ℕ) :
    ownAt shape N links ps b m 2 = ownAt shape N' links ps b' m 2 := by
  have b0 : baseAt N links ps = baseAt N' links ps := by
    funext k
    unfold baseAt
    rw [e]
  have b1 : base1At N links ps = base1At N' links ps := by
    funext k
    unfold base1At
    rw [e]
  show (sentDataOf shape (baseAt N links ps) (treesAt b)).own m ++
      secondNos shape (base1At N links ps) m =
    (sentDataOf shape (baseAt N' links ps) (treesAt b')).own m ++
      secondNos shape (base1At N' links ps) m
  rw [b0, b1]
  rfl

/-- Likewise the list keptBefore. -/
theorem kept_congr (e : N.msgsAt = N'.msgsAt) (m : ℕ) :
    keptAt shape N links ps b m = keptAt shape N' links ps b' m := by
  have b0 : baseAt N links ps = baseAt N' links ps := by
    funext k
    unfold baseAt
    rw [e]
  show (sentDataOf shape (baseAt N links ps) (treesAt b)).kept m =
    (sentDataOf shape (baseAt N' links ps) (treesAt b')).kept m
  rw [b0]
  rfl

end

set_option maxRecDepth 100000 in
/-- All 25 written tail views are there. -/
theorem tails_there : ((List.range 25).all fun l => (xShapeFull.1.getD l none).isSome) = true := by
  decide +kernel

/-- **The view of segment l's approximate range proof is the written one**, in the goals' scope,
where the shape part is the written one. -/
theorem tail_at {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
    {X : Verify.Public} (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (hpub : Verify.publicOf Pb.pol Pb.KL lay = .ok X) (hx : xShapeOf X = xShapeFull) {l : ℕ}
    (hl : l ≤ 24) : tailView (Meaning.tlAt X l) = tvW l := by
  have a := tail_of_is (xShapeIs_of hx) (k := l) (by omega)
  obtain ⟨h4, hN, -, -⟩ := Meaning.scope_plans hS hR hpub
  have s := List.all_eq_true.1 tails_there l (List.mem_range.2 (by omega))
  rw [List.getD_eq_getElem?_getD, a] at s
  have c : VerifiableInference.Desc.First.Look.tlAt X l = some (Meaning.tlAt X l) := by
    cases e : VerifiableInference.Desc.First.Look.tlAt X l with
    | none =>
      rw [e] at s
      cases s
    | some tl =>
      rcases Nat.lt_or_ge l 24 with h24 | h24
      · rw [VerifiableInference.Desc.First.Look.tlAt_is h4 hN h24 e]
      · obtain rfl : l = 24 := by omega
        have q := VerifiableInference.Desc.First.Look.tlAt_head X
        rw [if_pos h4, hN, e] at q
        have e24 : Meaning.tlAt X 24 = X.H.tl := by
          unfold Meaning.tlAt
          simp
        rw [e24]
        exact q
  unfold tvW
  rw [List.getD_eq_getElem?_getD, a, c]
  rfl

/-- A label off a view. -/
theorem lab_of_view (t : HTailF2) (μ : ℕ) :
    ((tailView t).2.1.getD μ tm0).1 = (t.mats.getD μ {}).aId := by
  show ((t.mats.toList.map fun x => (x.aId, x.m, x.k)).getD μ tm0).1 = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList,
    Array.getD_eq_getD_getElem?]
  cases t.mats[μ]? <;> rfl

section
variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **SmallPlan.mats AT THE WRITTEN LAYING, TO THE LETTER, UNDER THE HEAD, FROM THE CLOSED
TEST.** -/
theorem mats_of_written (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {l : ℕ} (hl : l ≤ 24)
    (hW : matsWB l = true) :
    ∀ μ, μ < (Meaning.tlAt (P5J.At.X Zp) l).NM → ∀ A,
    VerifiableInference.Desc.arrayOf (P5J.At.layout Zp)
      (Meaning.ownerK (Meaning.labAt (P5J.At.X Zp) l μ))
      (Meaning.nameOf (Meaning.ownerA (Meaning.labAt (P5J.At.X Zp) l μ))) = some A →
    MatPlan (P5J.At.foldD Zp cF LFull) ((P5J.At.N Zp cF).group l) (P5J.At.arr Zp) (P5J.At.num Zp) l
      2
      ((P5J.At.N Zp cF).msgsAt (flatPlacesOf linksFull true)[drawAt l]?)
      (Meaning.ownerK (Meaning.labAt (P5J.At.X Zp) l μ)) A := by
  intro μ hμ A hA
  have hy := h.toAtMg.made_accepts
  obtain ⟨pp, hR⟩ := IM.reads_of_scope h.scope
  have hpub : Verify.publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X := by
    rw [← VerifiableInference.PlanWritten.publicOfO_older]
    exact ProofFile.Law.pub_public h.laid.pub
  have eF := VerifiableInference.PlanWritten.Joined.first_written_in_scope h.scope h.laid.pub hy
  have eSh : P5J.At.shape Zp = shapeFull :=
    eF.2.2.1.trans VerifiableInference.PlanWritten.request_shape_written
  have eLy : P5J.At.layout Zp = layoutFull := eF.2.2.2.2.2
  have eM := h.toAtMg.msgs_at_head
  have eT := h.toAtMg.told_at_head
  have eAll := P5T.seats_written h.laid.pub
    (VerifiableInference.PlanWritten.Joined.sends_in_scope h.scope h.laid.pub hy) eSh
    h.toAtMg.plans_written
  have eTV := tail_at h.scope hR hpub
    (VerifiableInference.PlanWritten.Joined.xShape_in_scope h.scope h.laid.pub hy) hl
  have eNM : (Meaning.tlAt (P5J.At.X Zp) l).NM = nmW l := congrArg (·.1) eTV
  have eLab : Meaning.labAt (P5J.At.X Zp) l μ = labW l μ := by
    unfold labW
    rw [← eTV]
    exact (lab_of_view _ μ).symm
  have eMs : (P5J.At.N Zp cF).msgsAt = NW.msgsAt := by
    funext p
    show msgsTold (P5J.At.told cF) (borderOf P5J.At.ps p) = msgsTold toldCut (borderOf _ p)
    rw [eT]
    rfl
  have eG : (P5J.At.N Zp cF).group l = NW.group l := by
    show (P5T.numbersOf (P5T.planSeats Zp Zp.D.1)).group l = P5T.N0Full.group l
    rw [eAll.2.2]
  rw [eLab, eLy] at hA
  rw [eLab, eG, eMs]
  have t := List.all_eq_true.1 hW μ (List.mem_range.2 (eNM ▸ hμ))
  simp only [hA] at t
  have P := matPlan_of_test t
  show MatPlan _ _ (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) (P5T.numOfPlan (P5T.planSeatsAll Zp Zp.D))
    _ _ _ _ _
  rw [eAll.2.1]
  refine matPlan_congr (d' := dW) ?_ ?_ eSh eM rfl P
  · show VerifiableInference.Desc.First.FillSent.ownAt (P5J.At.shape Zp) (P5J.At.N Zp cF)
      P5J.At.links P5J.At.ps Zp.made.p.built.links l 2 = _
    rw [eSh]
    exact own2_congr shapeFull P5J.At.links P5J.At.ps Zp.made.p.built.links #[] eMs l
  · show VerifiableInference.Desc.First.FillSent.keptAt (P5J.At.shape Zp) (P5J.At.N Zp cF)
      P5J.At.links P5J.At.ps Zp.made.p.built.links l = _
    rw [eSh]
    exact kept_congr shapeFull P5J.At.links P5J.At.ps Zp.made.p.built.links #[] eMs l

/-- **SmallPlan.mats, TO THE LETTER, UNDER THE HEAD, AT THE LISTED LAYING.** OVER THE THIRTEEN ROWS
ALONE: a fact on the written values, which the head's own tests compare with. -/
theorem mats_at (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    {L₀ : VerifiableInference.Desc.K12.Door.Laid} (hL : P5J.At.laid? Zp = some L₀) {l : ℕ}
    (hl : l ≤ 24) :
    ∀ μ, μ < (Meaning.tlAt (P5J.At.X Zp) l).NM → ∀ A,
    VerifiableInference.Desc.arrayOf (P5J.At.layout Zp)
      (Meaning.ownerK (Meaning.labAt (P5J.At.X Zp) l μ))
      (Meaning.nameOf (Meaning.ownerA (Meaning.labAt (P5J.At.X Zp) l μ))) = some A →
    MatPlan (P5J.At.foldD Zp cF L₀) ((P5J.At.N Zp cF).group l) (P5J.At.arr Zp) (P5J.At.num Zp) l 2
      ((P5J.At.N Zp cF).msgsAt (flatPlacesOf linksFull true)[drawAt l]?)
      (Meaning.ownerK (Meaning.labAt (P5J.At.X Zp) l μ)) A := by
  obtain rfl : LFull = L₀ := Option.some.inj (h.toAtMg.laid_at_head.symm.trans hL)
  exact mats_of_written h hl
    (List.all_eq_true.1 matsWB_all l (List.mem_range.2 (Nat.lt_succ_of_le hl)))

/-- **ALL THREE CLOSED SENTENCES, UNDER THE HEAD.** OVER THE THIRTEEN ROWS ALONE: the third is a
fact on the written values. -/
theorem smallPlan_at (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    {L₀ : VerifiableInference.Desc.K12.Door.Laid} (hL : P5J.At.laid? Zp = some L₀)
    {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : ℕ} (hl : l ≤ 24)
    {Xl : LinkH} (e3 : G.built[l]? = some Xl) : SmallPlan Zp cF L₀ l Xl :=
  smallPlan_of_mats h hG hl e3 (mats_at h hL hl)

/-- **THE FIELD small OF K8LeftT, TO THE LETTER, FROM THE HEAD AND FoldFacts AT THE LISTED
LAYING.** OVER THE THIRTEEN ROWS ALONE. FoldFacts is not paid. -/
theorem small_at (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    {L₀ : VerifiableInference.Desc.K12.Door.Laid} (hL : P5J.At.laid? Zp = some L₀) {Fr : Frame}
    {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : ℕ} (hl : l ≤ 24)
    {Xl : LinkH} (e3 : G.built[l]? = some Xl) {Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop}
    (hRch : ∀ k a, Rch k a → RchAt (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) k a)
    (FF : FoldFacts Rch (fun a => a.1) (P5J.At.foldD Zp cF L₀) P5J.At.reqW P5J.At.links P5J.At.ps) :
    ∀ (z : ProofFile.InstPub) (a : S × Fr.E.Str) w,
      onQ (P5J.At.N Zp cF) (mgAtAll h) linksFull (flatPlacesOf linksFull true)
        (fun s => (z, s)) (drawAt l) a →
      Rch (drawAt l) ((z, a.1), a.2) →
      ¬ a.1.failed ≠ none →
      TieAt (cellsAt (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) l
        (z, a.1)) a.1 w →
      (mgAtAll h).constr l .small (z, a.1) (strsOf Fr a.2) w :=
  small_of_plan h hG hl e3 hRch FF (smallPlan_at h hL hG hl e3)

end

end K8Q35

#print axioms K8Q35.matsWB_all
#print axioms K8Q35.mats_there
#print axioms K8Q35.mats_rejects
#print axioms K8Q35.mats_named
#print axioms K8Q35.matPlan_congr
#print axioms K8Q35.own2_congr
#print axioms K8Q35.kept_congr
#print axioms K8Q35.tails_there
#print axioms K8Q35.lab_of_view
#print axioms K8Q35.tail_at
#print axioms K8Q35.mats_of_written
#print axioms K8Q35.mats_at
#print axioms K8Q35.smallPlan_at
#print axioms K8Q35.small_at
