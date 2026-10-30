-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/K8Q35R/SeatedAtHead.lean: THE CLOSED TEST P1K8T.k8SeatedB (Johnson/P1K8R/SeatedAtDraw.lean)
AS A THEOREM UNDER THE HEAD, AT ALL 25 LINKS. A payment beneath kind K8's frozen condition (one
row; below, "the row": that test's yes at a link). IT IMPORTS ThirdParty/.

WHICH HEAD. THE HEAD OVER THE ENTRY TESTS' LIST OF THIRTEEN ROWS: both rows that compare
with written values are spent, as in Johnson/K8Q35R/MatsAtHead.lean.
[The list has fourteen rows: the thirteen and one more
(Johnson/Desc/Laid/ProofAsks.lean): so the head says that much more.]
WHAT IS SHOWN IS A FACT ON THE
WRITTEN VALUES: no fact on what the maker of the IOP as written in Lean makes of given public files.
THE PRICE IS PAID IN WHETHER THE HEAD CAN BE MET.

THE ROAD GOES BY A WIDER TEST. The test's list of numbers, k8NumsOf
(Johnson/P1K8R/ShareAtDraw.lean), reads the built link Xl: which arrays the matrix multiplies
(Xl.tl: the symbols' arrays and the vectors of reads) and how the link names them (Xl.arrayOf).
These are no written values by a theorem that is called here. BUT EVERY NUMBER OF THAT LIST IS
whereD's ANSWER AT SOME ARRAY OF THE LAYOUT (nums_sub), and the test asks the same of each number by
itself. So it follows from the same test at allNums: whereD's answers at ALL arrays of the written
layout, born at any link. THAT TEST ASKS MORE THAN THE ROW DOES: its yes gives the row; A NO OF IT
WOULD NOT HAVE REFUTED THE ROW, and would have been no find on the tie's reading of zeros.

THE MEMBERS. The test reads of a member its (tree, tenant) alone. That a member sits at a seat
follows from memsSame_atR (Johnson/P5T/MembersByMake.lean) at any radii: NO RADIUS IS READ:
member_at.

  allNums · nums_sub    whereD's answers at all arrays of a layout · k8NumsOf's numbers are among
                        them
  seatedWB              the wider test at the written values
  **seatedWB_all**      it accepts at all 25 links: AN EVALUATION IN LEAN's KERNEL
  seated_there          it asks something at each link: allNums is empty nowhere (allNums: NOT
                        k8NumsOf at the built link)
  seated_rejects        four bends, each refused at each of the 25 links; two of them bear news
  **seated_at_head**    the row: its conclusion to the letter; Xl any
Readers' marks that stand. At these values the group's tenants are seats of entries with a sample
already: the test's fourth clause (a member sits there) follows from the third and adds no
constraint here. The member that is found may bear a silent radius 0: no radius is read.
Limits. The full size alone. A MEMBER OF THE HEAD IS PROVED AT storedPublicFiles AND zGap ALONE (AT secondHashFunction; SIDE
LIBRARY AtFullSide/Top/). At OnBytes.secondHashFunction alone. That every early array HAS a message now is
another row's (k8AllNowB). No soundness statement. Nothing on hiding.
-/
import Johnson.K8Q35R.MatsAtHead
import Johnson.P1K8R.SeatedAtDraw
import Johnson.P5T.MembersByMake

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace K8Q35

open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj Johnson.Pack
open OnBytes.Params (ReqArray ReqLayout)
open OnBytes.Model.Stages (LinkH)
open Johnson.G (layoutFull)
open VerifiableInference.Desc (Chain Place)
open VerifiableInference.Desc.ReqLit (shapeFull)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S Numbers FoldData flatPlacesOf)
open VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.LinkJoin (whereD)
open VerifiableInference.Desc.K13.Law (LFull MFull)
open ProofFile (Cl)
open P5J (AtMg AtMgA)
open P1K8T

/-! ## 1 The wider list -/

/-- whereD's answers, in segment l with two moments sent, at ALL arrays of a layout. -/
def allNums (d : FoldData) (lay : ReqLayout) (l : ℕ) : List ℕ :=
  lay.link.zipIdx.flatMap fun x => x.1.filterMap fun a => whereD d l 2 x.2 a.message

/-- **The plan's numbers in front of the draw are among them**, whatever the built link. -/
theorem nums_sub (d : FoldData) (lay : ReqLayout) (Xl : LinkH) (l : ℕ) :
    ∀ o ∈ k8NumsOf d lay Xl l, o ∈ allNums d lay l := by
  intro o ho
  unfold k8NumsOf at ho
  obtain ⟨t, -, ht⟩ := List.mem_filterMap.1 ho
  obtain ⟨x, -, hx⟩ := Option.bind_eq_some_iff.1 ht
  obtain ⟨a, ha, hw⟩ := Option.bind_eq_some_iff.1 hx
  unfold OnBytes.reqArray at ha
  obtain ⟨arrs, hl, hf⟩ := Option.bind_eq_some_iff.1 ha
  unfold allNums
  refine List.mem_flatMap.2 ⟨(arrs, x.1), List.mem_zipIdx_iff_getElem?.2 hl, ?_⟩
  exact List.mem_filterMap.2 ⟨a, List.mem_of_find?_eq_some hf, hw⟩

/-- The test asks the same of each number by itself. -/
theorem seated_mono {Ld : VerifiableInference.Desc.K12.Door.Laid} {ms : List Mem}
    {own : List (ℕ × ℕ)} {n : ℕ} {os os' : List ℕ} (hs : ∀ o ∈ os, o ∈ os')
    (h : k8SeatedB Ld ms own n os' = true) : k8SeatedB Ld ms own n os = true := by
  unfold k8SeatedB at h ⊢
  exact List.all_eq_true.2 fun o ho => List.all_eq_true.1 h o (hs o ho)

/-! ## 2 The written side -/

/-- The seats of the written entries with a sample. -/
def smpSeatsW : List (ℕ × ℕ) := (P5T.psFull.filter (·.smpd)).map (·.seat)

/-- The wider test at link l, at any data, laying, group, count and list of members' seats. -/
def seatedAtB (d : FoldData) (Ld : VerifiableInference.Desc.K12.Door.Laid) (seats : List (ℕ × ℕ))
    (own : ℕ → List (ℕ × ℕ)) (n : ℕ → ℕ) (l : ℕ) : Bool :=
  (allNums d layoutFull l).all fun o => decide (o < n l) &&
    match Ld.places[o]? with
    | some q => (own l).contains q && seats.contains q
    | none => false

/-- **THE WIDER TEST AT THE WRITTEN VALUES.** -/
def seatedWB (l : ℕ) : Bool := seatedAtB dW LFull smpSeatsW NW.group nW l

set_option maxRecDepth 1000000 in
/-- **IT ACCEPTS AT ALL 25 LINKS**: by an evaluation in Lean's kernel. -/
theorem seatedWB_all : ((List.range 25).all seatedWB) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **IT ASKS SOMETHING AT EACH LINK.** -/
theorem seated_there :
    ((List.range 25).all fun l => !(allNums dW layoutFull l).isEmpty) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **THE NEGATIVE TESTS: FOUR BENDS, EACH REFUSED AT EACH OF THE 25 LINKS; TWO OF THEM BEAR NEWS.**
None is false by the test's text alone. FACTS OF THE WRITTEN DATA, FORCED BY NOTHING ELSE HERE: the
list of seats without its first · the count one lower (so the count is tight: the highest number is
the count less one). NO NEWS BESIDE THESE: every own and kept message's number one
higher: it follows from the two above with the accept · the group number l + 1 in the group's place
(at l = 24: the last test's group): it follows from the accept with a fact that is held already (no
two groups share a seat).
NOT BENT: the shape · the layout · the moment 2 · the list of the
entries' seats with a sample. -/
theorem seated_rejects : ((List.range 25).any fun l =>
    seatedAtB dW { LFull with places := LFull.places.drop 1 } smpSeatsW NW.group nW l ||
      seatedAtB { dW with ownAt := fun m t => (dW.ownAt m t).map (· + 1),
                          keptAt := fun m => (dW.keptAt m).map (· + 1) } LFull smpSeatsW NW.group
        nW l ||
      seatedAtB dW LFull smpSeatsW (fun k => NW.group (k + 1)) nW l ||
      seatedAtB dW LFull smpSeatsW NW.group (fun k => nW k - 1) l) = false := by decide +kernel

/-! ## 3 The tie -/

/-- whereD reads of the data three parts alone. -/
theorem whereD_congr {d d' : FoldData} {l t : ℕ} (e1 : d.ownAt l t = d'.ownAt l t)
    (e2 : d.keptAt l = d'.keptAt l) (e3 : d.sent.shape = d'.sent.shape) (born j : ℕ) :
    whereD d l t born j = whereD d' l t born j := by
  unfold whereD
  rw [e1, e2, e3]

/-- **A member sits at every seat of an entry with a sample**, at any radii. -/
theorem member_at (Z : ProofFile.Pub) (rad : ℕ → ℕ → ℕ) {q : ℕ × ℕ}
    (hq : q ∈ ((P5T.planSeats Z Z.D.1).filter (·.smpd)).map (·.seat)) :
    ((P5T.msAtR Z rad).find? fun y => decide (seatOf y = q)).isSome = true := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
  have a := (P5T.memsSame_atR Z rad (p.shape, p.seat)).2 (List.mem_map.2 ⟨p, hp, rfl⟩)
  obtain ⟨x, hx, e⟩ := List.mem_map.1 a
  exact List.find?_isSome.2 ⟨x, hx, decide_eq_true (congrArg Prod.snd e)⟩

section
variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **THE ROW: ITS CONCLUSION TO THE LETTER.** The row's premises hG and e3 on the built link
are dropped: Xl IS ANY LinkH: the list of numbers reads it, but NOTHING IS ASKED OF IT. At an Xl
whose list of numbers is empty the test is an "all" over nothing: that every early array has a
number is another row's. OVER THE THIRTEEN ROWS ALONE: a fact on the written values, which the
head's own tests compare with. -/
theorem seated_at_head (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    {L₀ : VerifiableInference.Desc.K12.Door.Laid} (hL : P5J.At.laid? Zp = some L₀) {l : ℕ}
    (hl : l ≤ 24) (Xl : LinkH) :
    k8SeatedB L₀ (P5J.At.ms Zp Z.lay) ((P5J.At.N Zp cF).group l)
      ((P5J.At.N Zp cF).msgsAt (flatPlacesOf linksFull true)[drawAt l]?)
      (k8NumsOf (P5J.At.foldD Zp cF L₀) (P5J.At.layout Zp) Xl l) = true := by
  obtain rfl : LFull = L₀ := Option.some.inj (h.toAtMg.laid_at_head.symm.trans hL)
  refine seated_mono (nums_sub _ _ Xl l) ?_
  have hy := h.toAtMg.made_accepts
  have eF := VerifiableInference.PlanWritten.Joined.first_written_in_scope h.scope h.laid.pub hy
  have eSh : P5J.At.shape Zp = shapeFull :=
    eF.2.2.1.trans VerifiableInference.PlanWritten.request_shape_written
  have eLy : P5J.At.layout Zp = layoutFull := eF.2.2.2.2.2
  have eT := h.toAtMg.told_at_head
  have eAll := P5T.seats_written h.laid.pub
    (VerifiableInference.PlanWritten.Joined.sends_in_scope h.scope h.laid.pub hy) eSh
    h.toAtMg.plans_written
  have eMs : (P5J.At.N Zp cF).msgsAt = NW.msgsAt := by
    funext p
    show VerifiableInference.Desc.First.msgsTold (P5J.At.told cF)
        (VerifiableInference.Desc.First.borderOf P5J.At.ps p) =
      VerifiableInference.Desc.First.msgsTold VerifiableInference.Desc.First.toldCut
        (VerifiableInference.Desc.First.borderOf _ p)
    rw [eT]
    rfl
  have eG : (P5J.At.N Zp cF).group l = NW.group l := by
    show (P5T.numbersOf (P5T.planSeats Zp Zp.D.1)).group l = P5T.N0Full.group l
    rw [eAll.2.2]
  have e1 : (P5J.At.foldD Zp cF LFull).ownAt l 2 = dW.ownAt l 2 := by
    show VerifiableInference.Desc.First.FillSent.ownAt (P5J.At.shape Zp) (P5J.At.N Zp cF)
      P5J.At.links P5J.At.ps Zp.made.p.built.links l 2 = _
    rw [eSh]
    exact own2_congr shapeFull P5J.At.links P5J.At.ps Zp.made.p.built.links #[] eMs l
  have e2 : (P5J.At.foldD Zp cF LFull).keptAt l = dW.keptAt l := by
    show VerifiableInference.Desc.First.FillSent.keptAt (P5J.At.shape Zp) (P5J.At.N Zp cF)
      P5J.At.links P5J.At.ps Zp.made.p.built.links l = _
    rw [eSh]
    exact kept_congr shapeFull P5J.At.links P5J.At.ps Zp.made.p.built.links #[] eMs l
  have eN : allNums (P5J.At.foldD Zp cF LFull) (P5J.At.layout Zp) l = allNums dW layoutFull l := by
    have eW : (fun x : List ReqArray × ℕ =>
        x.1.filterMap fun a => whereD (P5J.At.foldD Zp cF LFull) l 2 x.2 a.message) =
        fun x => x.1.filterMap fun a => whereD dW l 2 x.2 a.message :=
      funext fun x => congrArg (fun f => List.filterMap f x.1)
        (funext fun a => whereD_congr e1 e2 eSh x.2 a.message)
    unfold allNums
    rw [eLy, eW]
  rw [eN, eG, eMs]
  have W := List.all_eq_true.1 seatedWB_all l (List.mem_range.2 (Nat.lt_succ_of_le hl))
  unfold k8SeatedB
  refine List.all_eq_true.2 fun o ho => ?_
  have w := List.all_eq_true.1 W o ho
  obtain ⟨w1, w2⟩ := Eq.mp (Bool.and_eq_true _ _) w
  refine Bool.and_eq_true_iff.2 ⟨w1, ?_⟩
  cases hq : LFull.places[o]? with
  | none =>
    rw [hq] at w2
    cases w2
  | some q =>
    rw [hq] at w2
    obtain ⟨w3, w4⟩ := Eq.mp (Bool.and_eq_true _ _) w2
    refine Bool.and_eq_true_iff.2 ⟨w3, ?_⟩
    refine member_at Zp _ ?_
    rw [eAll.1]
    exact List.contains_iff_mem.1 w4

end

end K8Q35

#print axioms K8Q35.nums_sub
#print axioms K8Q35.seated_mono
#print axioms K8Q35.seatedWB_all
#print axioms K8Q35.seated_there
#print axioms K8Q35.seated_rejects
#print axioms K8Q35.whereD_congr
#print axioms K8Q35.member_at
#print axioms K8Q35.seated_at_head
