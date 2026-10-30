-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/SeatsK6AtAll.lean: THE TEST WITH CODE seatsK6C
(Johnson/Desc/Kinds/Law/K6SeatsTest.lean: the seats of the output head's matrices, of its mask row
and of its reads' array) ACCEPTS AT THE CLOSED CONSTANT (P5J.mgAtAll): the premise hC of mats_342,
matsP_342 and jHead3_342, in its own type, at L := LFull, M := MFull, num := At.num Zp.

HOW. The test is cut into its three parts; what each reads of the numbers, of the plan's side of
what stands sent and of the public parameters is made a letter (matSeatL, maskSeatL: equal to the
test's own parts by unfolding); at the written values Lean's kernel evaluates the parts; a bridge
carries the constant's letters to the written ones.
  seatsK6C_of_parts   the test from its three parts WITH EVERY MATRIX ASKED: so the bound NHf + 3,
                      which lets the later matrices by, is not read
  k6Two_written       all eight matrices and the mask row pass (the kernel) · k6Two_asks: each of
                      the eight has its array in the written layout: no arm is free
  k6Two_seats_rejects · k6Two_num_rejects · k6Two_count_rejects   NEGATIVE TESTS: the listed seats
                      shifted by one member · every number one more · the count of messages as it
                      stands in front of the segment's first sending: each rejects
  k6Reads_written     (24, "U3") is of the second sending; (24, "M0") is not
  tail24_written      the output head's plan's view (its number of matrices, their labels, rows and
                      columns, their symbol arrays) is the written one
  **hC_atAll**        the test accepts at the constant
UNDER WHICH PREMISES THE LETTERS ARE THE WRITTEN ONES.
  hP1 (the entry tests' first comparison's accept), in scope: arr, num (seats_in_scope: the seats
      of all three chains) · N.sent 24 0 · layout, cs, shape (first_written_in_scope) · the number
      of matrices and the labels (xShape_in_scope, with scope_plans: p4, twelve groups)
  hC (the first chain's cut): N.msgsAt, so the plan's side of what stands sent and the count
      (told_of_cut, Johnson/Desc/AtSeats/K13PlanM3At.lean)
  the head alone: the number of the reads' array is 0 (public_third)
  hU3: entry 0 of segment 24's list of arrays is (24, "U3"): A THEOREM
      (reads_named_at24 hA, Johnson/Desc/AtSeats/ReadsArrAtAll.lean), handed in: that file stands
      above kind K1's tree, which is not beneath this one: PAID AT THE CALL.
What is not claimed. That hA, hP1, hC can be met: NO MEMBER. Nothing on any state. Nothing on
soundness. The recursion limit is raised at the six kernel facts (maxRecDepth 1000000).

-/
import Johnson.Desc.AtSeats.FoldFactsAtAll
import Johnson.Desc.AtSeats.K13PlanM3At
import Johnson.Desc.Kinds.Law.K6SeatsTest
import Johnson.Desc.Kinds.Law.ReadsNamed
import Johnson.P5T.PlanSeatsTie
import Johnson.G.XShapeLit
import Johnson.Goal.Numbers.MadeInScope
import Johnson.Goal.Meaning.PlanShapes
import Johnson.Desc.First.SentTerms

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Maker Johnson.G
open VerifiableInference.Desc renaming arrayOf → arrayOfD
open VerifiableInference.Desc (Chain Place)
open VerifiableInference.Desc.First (S Numbers flatPlacesOf shift)
open VerifiableInference.Desc.First.FillSent
open VerifiableInference.Desc.Sound (linksFull)
open VerifiableInference.PlanWritten
open VerifiableInference.Desc.Kinds.Head.Law.AtFold
open ProofFile (Cl)

/-- matSeatC with what it reads of N, dS, Lp and the public parameters as letters. -/
def matSeatL (arr : ℕ → ℕ → ℕ) (own : List (ℕ × ℕ)) (lay6 : ReqLayout) (num : ℕ → ℕ → ℕ)
    (cs : OnBytes.Codes) (wh : ℕ → ℕ → Option ℕ) (places : List (ℕ × ℕ)) (M : List OracleShape)
    (n0 lab : ℕ) : Bool :=
  match arrayOfD lay6 (_root_.Meaning.ownerK lab)
      (_root_.Meaning.nameOf (_root_.Meaning.ownerA lab)) with
  | none => true
  | some A =>
    (wh (_root_.Meaning.ownerK lab) A.message).any fun o =>
      (M[o]?).any fun sh =>
        laidMatrixOk A (K9.rowBitsOf sh .main) (K9.placeBitsOf cs sh .main) &&
          seatC arr own places n0 o (num (_root_.Meaning.ownerK lab) A.message)

/-- maskSeatC, likewise. -/
def maskSeatL (arr : ℕ → ℕ → ℕ) (own : List (ℕ × ℕ)) (n rb : ℕ) (mk : Option ℕ)
    (places : List (ℕ × ℕ)) (M : List OracleShape) (n0 : ℕ) : Bool :=
  mk.any fun o => (M[o]?).any fun sh => K9.rowBitsOf sh .mask == rb && seatC arr own places n0 o n

theorem matSeatC_eq (arr : ℕ → ℕ → ℕ) (N : Numbers) (Wp : OnBytes.Model.Verify.Public)
    (lay6 : ReqLayout) (num : ℕ → ℕ → ℕ) (cs : OnBytes.Codes) (dS : SentData)
    (Lp : K12.Door.Laid) (M : List OracleShape) (n0 a : ℕ) :
    matSeatC arr N Wp lay6 num cs dS Lp M n0 a =
      matSeatL arr (N.sent 24 0) lay6 num cs (whereIsP dS 24) Lp.places M n0
        (_root_.Meaning.labAt Wp 24 a) := rfl

theorem maskSeatC_eq (arr : ℕ → ℕ → ℕ) (N : Numbers) (n rb : ℕ) (shape : ReqShape)
    (dS : SentData) (Lp : K12.Door.Laid) (M : List OracleShape) (n0 : ℕ) :
    maskSeatC arr N n rb shape dS Lp M n0 =
      maskSeatL arr (N.sent 24 0) n rb (maskP shape dS 24) Lp.places M n0 := rfl

/-- **The test from its three parts, with every matrix asked**: so the bound NHf + 3 is not read. -/
theorem seatsK6C_of_parts {arr : ℕ → ℕ → ℕ} {N : Numbers} {Wp : OnBytes.Model.Verify.Public}
    {lay6 : ReqLayout} {num : ℕ → ℕ → ℕ} {n rb : ℕ} {cs : OnBytes.Codes} {shape : ReqShape}
    {dS : SentData} {Lp : K12.Door.Laid} {M : List OracleShape} {arrs : Array (ℕ × String)}
    {n0 : ℕ}
    (h1 : ∀ a, a < (_root_.Meaning.sizesOf Wp 24).NM →
      matSeatC arr N Wp lay6 num cs dS Lp M n0 a = true)
    (h2 : maskSeatC arr N n rb shape dS Lp M n0 = true)
    (h3 : readsC Wp lay6 shape arrs = true) :
    seatsK6C arr N Wp lay6 num n rb cs shape dS Lp M arrs n0 = true := by
  unfold seatsK6C
  rw [Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true]
  exact ⟨⟨fun a ha => by rw [h1 a (List.mem_range.1 ha), Bool.or_true], h2⟩, h3⟩

/-! ## The written values -/

/-- The count of messages in front of a place, by the written cut. -/
def msgsK6W (p : Option Place) : ℕ :=
  First.msgsTold (cutFirstFull.map fun r => r.2.2.2.2.1.flatMap (·.2)) (First.borderOf P5J.At.ps p)

/-- The plan's side of what stands sent, off the written shape and that count. -/
def dSK6W : SentData :=
  sentDataOf proofSizedFull.request (fun m => msgsK6W ((flatPlacesOf linksFull true).find? fun p =>
    p.link == some m && p.piece == 1 + ((linksFull[m]?).map shift).getD 0)) fun _ => []

/-- The labels of the output head's eight matrices, off the written shape part. -/
def labsK6W : List ℕ := ((xShapeFull.1.getD 24 none).map fun t => t.2.1.map (·.1)).getD []

/-- The first two parts of the test at letters for the listed seats, the numbers and the count. -/
def k6TwoW (places : List (ℕ × ℕ)) (num : ℕ → ℕ → ℕ) (n0 : ℕ) : Bool :=
  ((List.range 8).all fun a =>
    matSeatL (P5T.arrOf P5T.seatsAllFull) (P5T.N0Full.sent 24 0) layoutFull num
      proofSizedFull.codes (whereIsP dSK6W 24) places K13.Law.MFull n0 (labsK6W.getD a 0)) &&
    maskSeatL (P5T.arrOf P5T.seatsAllFull) (P5T.N0Full.sent 24 0) (num 24 0) 0
      (maskP proofSizedFull.request dSK6W 24) places K13.Law.MFull n0

set_option maxRecDepth 1000000 in
/-- **The first two parts accept at the written values** (Lean's kernel): all eight matrices and the
mask row. -/
theorem k6Two_written : k6TwoW K13.Law.LFull.places (P5T.numOfPlan P5T.seatsAllFull)
    (msgsK6W (flatPlacesOf linksFull true)[342]?) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Each of the eight matrices has its array in the written layout: no arm of the test is free. -/
theorem k6Two_asks : ((List.range 8).all fun a =>
    (arrayOfD layoutFull (_root_.Meaning.ownerK (labsK6W.getD a 0))
      (_root_.Meaning.nameOf (_root_.Meaning.ownerA (labsK6W.getD a 0)))).isSome) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **A negative test**: the listed seats shifted by one member. -/
theorem k6Two_seats_rejects : k6TwoW (K13.Law.LFull.places.drop 1)
    (P5T.numOfPlan P5T.seatsAllFull) (msgsK6W (flatPlacesOf linksFull true)[342]?) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **A negative test**: every number, one more. -/
theorem k6Two_num_rejects : k6TwoW K13.Law.LFull.places
    (fun a b => P5T.numOfPlan P5T.seatsAllFull a b + 1)
    (msgsK6W (flatPlacesOf linksFull true)[342]?) = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **A negative test**: the count as it stands in front of the segment's first sending. -/
theorem k6Two_count_rejects : k6TwoW K13.Law.LFull.places (P5T.numOfPlan P5T.seatsAllFull)
    (msgsK6W (flatPlacesOf linksFull true)[338]?) = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The reads' array is of the second sending, by the written layout and shape; the first
sending's array M0 is not. -/
theorem k6Reads_written : secondC layoutFull proofSizedFull.request (24, "U3") = true ∧
    secondC layoutFull proofSizedFull.request (24, "M0") = false := by decide +kernel

/-! ## The bridge -/

/-- A list's view of an array's entry. -/
theorem getD_view {α β : Type} (f : α → β) (xs : Array α) (a : ℕ) (d : α) :
    (xs.toList.map f).getD a (f d) = f (xs.getD a d) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList,
    Array.getD_eq_getD_getElem?]
  cases xs[a]? <;> rfl

section
variable {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S Cl} {x₀ : First.Look.Place}
  (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
  (hP1 : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true)
include hA hP1

/-- The output head's plan's view is the written one. -/
theorem tail24_written :
    tailView (P5J.At.X Zp).H.tl = (xShapeFull.1.getD 24 none).getD (0, [], []) := by
  obtain ⟨p4, ng, -⟩ := _root_.Meaning.scope_plans hA.scope hA.reads hA.pubOne
  have hx := Joined.xShape_in_scope hA.scope hA.laid.pub hP1
  have h24 : (xShapeOf (P5J.At.X Zp)).1.getD 24 none = some (tailView (P5J.At.X Zp).H.tl) := by
    show (((List.range 25).map fun k => (First.Look.tlAt (P5J.At.X Zp) k).map tailView).getD 24
      none) = _
    have e : First.Look.tlAt (P5J.At.X Zp) 24 = some (P5J.At.X Zp).H.tl := by
      unfold First.Look.tlAt
      rw [p4, ng]
      rfl
    have h0 : (((List.range 25).map fun k =>
        (First.Look.tlAt (P5J.At.X Zp) k).map tailView).getD 24 none) =
        (First.Look.tlAt (P5J.At.X Zp) 24).map tailView := rfl
    rw [h0, e]
    rfl
  have hx' : xShapeOf (P5J.At.X Zp) = xShapeFull := hx
  rw [hx'] at h24
  rw [h24]
  rfl

/-- **hC at the closed constant**: the test seatsK6C accepts. -/
theorem hC_atAll (hC : cutOf (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = cutFirstFull)
    (hU3 : ((Zp.made.p.built.links.map (·.arrayOf)).getD 24 #[])[0]? = some (24, "U3")) :
    seatsK6C hA.𝔇.arr hA.𝔇.N (P5J.At.X Zp) hA.𝔇.layout (P5J.At.num Zp) (P5J.At.num Zp 24 0) 0
      hA.𝔇.cs hA.𝔇.shape hA.𝔇.pubD.dS K13.Law.LFull K13.Law.MFull
      (hA.𝔇.sent.arrayOf.getD 24 #[])
      (hA.𝔇.N.msgsAt (flatPlacesOf linksFull true)[342]?) = true := by
  have hl' := hA.laid.run ▸ LPFD.Full.laidPOf_of hA.laid.value hA.laid.planOk hA.laid.data
    hA.laid.asks
  obtain ⟨-, sAll, sN⟩ := P5T.seats_in_scope hA.scope hA.laid.pub hP1 hl'
  obtain ⟨fc, -, fs, -, -, fl⟩ := Joined.first_written_in_scope hA.scope hA.laid.pub hP1
  have eArr : hA.𝔇.arr = P5T.arrOf P5T.seatsAllFull := by
    show P5T.arrOf (P5T.planSeatsAll Zp Zp.D) = _
    rw [sAll]
  have eNum : P5J.At.num Zp = P5T.numOfPlan P5T.seatsAllFull := by
    show P5T.numOfPlan (P5T.planSeatsAll Zp Zp.D) = _
    rw [sAll]
  have eOwn : hA.𝔇.N.sent 24 0 = P5T.N0Full.sent 24 0 := by
    show (P5T.numbersOf (P5T.planSeats Zp Zp.D.1)).sent 24 0 = _
    rw [sN]
  have eLay : hA.𝔇.layout = layoutFull := fl
  have eCs : hA.𝔇.cs = proofSizedFull.codes := fc
  have eShp : hA.𝔇.shape = proofSizedFull.request := fs
  have eMs : hA.𝔇.N.msgsAt = msgsK6W := by
    show (fun p => First.msgsTold (P5J.At.told cF) (First.borderOf P5J.At.ps p)) = _
    rw [K13.Law.told_of_cut (cF := cF) hC]
    rfl
  have eWh : whereIsP hA.𝔇.pubD.dS 24 = whereIsP dSK6W 24 := by
    unfold dSK6W
    rw [← eMs, ← eShp]
    rfl
  have eMk : maskP hA.𝔇.shape hA.𝔇.pubD.dS 24 = maskP proofSizedFull.request dSK6W 24 := by
    unfold dSK6W
    rw [← eMs, ← eShp]
    rfl
  have hT := tail24_written hA hP1
  have eNM : (_root_.Meaning.sizesOf (P5J.At.X Zp) 24).NM = 8 := congrArg (·.1) hT
  have eLab : ∀ a, _root_.Meaning.labAt (P5J.At.X Zp) 24 a = labsK6W.getD a 0 := by
    intro a
    have h2 : (P5J.At.X Zp).H.tl.mats.toList.map (fun x => (x.aId, x.m, x.k)) =
        ((xShapeFull.1.getD 24 none).getD (0, [], [])).2.1 := congrArg (·.2.1) hT
    have h3 := getD_view (fun x : OnBytes.Model.TMat => x.aId) (P5J.At.X Zp).H.tl.mats a {}
    show ((P5J.At.X Zp).H.tl.mats.getD a {}).aId = _
    rw [← h3]
    have h4 : (P5J.At.X Zp).H.tl.mats.toList.map (fun x => x.aId) = labsK6W := by
      have := congrArg (List.map (·.1)) h2
      rw [List.map_map] at this
      exact this
    rw [h4]
  have hW := k6Two_written
  unfold k6TwoW at hW
  rw [Bool.and_eq_true, List.all_eq_true] at hW
  refine seatsK6C_of_parts (fun a ha => ?_) ?_ ?_
  · rw [matSeatC_eq, eArr, eNum, eOwn, eLay, eCs, eWh, eMs, eLab a]
    exact hW.1 a (List.mem_range.2 (eNM ▸ ha))
  · rw [maskSeatC_eq, eMk, eArr, eNum, eOwn, eMs]
    exact hW.2
  · have hrd : Kinds.Head.Law.readsOf (P5J.At.X Zp) = 0 := by
      unfold Kinds.Head.Law.readsOf
      rw [Kinds.Head.Law.ReadsNamed.public_third hA.pubOne]
      rfl
    unfold readsC
    rw [hrd]
    show (((Zp.made.p.built.links.map (·.arrayOf)).getD 24 #[])[0]?).any _ = true
    rw [hU3, eLay, eShp]
    exact k6Reads_written.1

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.seatsK6C_of_parts
#print axioms VerifiableInference.Desc.K1.k6Two_written
#print axioms VerifiableInference.Desc.K1.k6Two_asks
#print axioms VerifiableInference.Desc.K1.k6Two_seats_rejects
#print axioms VerifiableInference.Desc.K1.k6Two_num_rejects
#print axioms VerifiableInference.Desc.K1.k6Two_count_rejects
#print axioms VerifiableInference.Desc.K1.k6Reads_written
#print axioms VerifiableInference.Desc.K1.tail24_written
#print axioms VerifiableInference.Desc.K1.hC_atAll
