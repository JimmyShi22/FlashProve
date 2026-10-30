-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/Lots/K2Row.lean: THE CODE SWITCH's LOT's ROW (ProofFile.k2Pure,
Johnson/Desc/ProofFile/Lots/PureLots.lean) FOR «the proof file's written-out protocol at written
values»: the skeletons (ProofFile.Sk.skel, Johnson/Desc/ProofFile/Law/Skel/Skel.lean: a
block less its functions) of the lot's blocks are the written rows, AT HYPOTHESES BY FIELD on what
the lot reads of the public part and of the ground. NO OPENING, NO PIN «in scope», NO «blankBy» IS
SPENT. NO BLOCK IMPORTS THIS FILE.
  skSwitch · skMute · skAt · madeW · k2SkelOf   the lot's text
                                                (Johnson/Desc/ProofFile/Lot/K2.lean), arm for arm,
                                                on skeletons: plain data, with code
  k2_lot_skel      THE GENERAL LAW, without a hypothesis: ((k2Pure Z).blocks G).map skel =
                   k2SkelOf (spotsOf Z.cuts) (prepOf Z G) (fun l => (pureLetters G l).map
                   headPlanOk)
  prepW · prep_at  what prepOf returns, off the sizes alone, under the five equations of its own
                   test «tied»
  k2SkelOf_hd      the third argument is read at the places that stand at the head alone
  k2SkelW          THE WRITTEN ROWS: the rows of the kind in cutFirstFull
                   (Johnson/Desc/Ok/PlanWritten/CutLit.lean), with planOk := true and no runs of
                   claims
  standsK · skAtK · k2SkelOfK, with standsOf_eq · skAt_K · k2SkelOf_K   twins that the kernel
                                                                        bears (standsOf cuts a
                                                                        name by String.splitOn, at
                                                                        which the kernel's check
                                                                        sticks), and the general
                                                                        laws «twin = the routine»,
                                                                        over SpotsWritten.lean's
                                                                        headK and headOf_eq
  head_at_24 · k2_row_closed · k2_row_count    CLOSED FACTS, BY LEAN's KERNEL, at the written
                                               table of steps and the written sizes: decided once,
                                               at the written places (the names that end in S);
                                               the forms at the written table of steps follow by
                                               one rewriting with spots_written
                                               (Johnson/AtFull/Desc/SpotsWritten.lean), at the
                                               lasting constant Johnson.AtFull.Cut.cutWritten
  k2_row_no_head · k2_row_head_mute · k2_row_no_prep · k2_row_bent_trees   NEGATIVE FACTS, BY THE
                                                                           KERNEL: with the head's
                                                                           test on the plan
                                                                           rejecting · with the
                                                                           head's letters lacking
                                                                           · with no numbers ·
                                                                           with the first link's
                                                                           trees struck from the
                                                                           numbers: the rows are
                                                                           NOT the written ones ·
                                                                           k2_all_mute: general:
                                                                           without the numbers
                                                                           every place is mute
  k2_row_spots     THE ROW under «spotsOf Zq.cuts = some spotsWritten» · k2_lotSk_spots
  k2_row           THE ROW under hc: a call of it · k2_lot_count: so the lot has 25 blocks ·
                   k2_lotSk · k2_steady: the same on the form ProofFile.Sk.lotSk
WHAT STAYS OWED, BY FIELD: hc (the table of steps is the written one) · hz (the sizes are the
written ones) · t1 … t5 · hH: the head's link's letters are there and pass headPlanOk (three tests
on the planner's own output, for which no written value lies).
LIMITS. THE ROW IS «24 OF 25 UNDER WRITTEN VALUES; THE 25TH's planOk UNDER hH». That any public
part and ground meet the hypotheses together is shown nowhere here. The written rows were printed
off this very lot's description at a run (CutLit.lean's own head): they are no independent
witness. The full size alone. No soundness is claimed.
-/
import Johnson.Desc.ProofFile.Law.Skel.SkelEnd
import Johnson.Desc.ProofFile.Lots.PureLots
import Johnson.Desc.Ok.PlanWritten.CutLit
import Johnson.Desc.Ok.PlanWritten.SizedLit
import Johnson.AtFull.Cut.CutWrittenLit
import Johnson.AtFull.Desc.SpotsWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Lots.K2
open P1K2
open OnBytes OnBytes.Model OnBytes.Params OnBytes.Plan
open ProofFile (Pub Ground Spot spotsOf)
open ProofFile.Sk (Skel skel toldFrom lotSk LotSk Steady steady_none skel_retype)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 At codeSwitchKind increasing finishPlace headOpened headPlanOk)
open VerifiableInference.PlanWritten (cutFirstFull proofSizedFull)
open Johnson.AtFull.Cut (cutWritten)
open Johnson.AtFull.Desc (headK headOf_eq spotsWritten spots_written)

/-- The switch's skeleton at a place, off the lot's numbers. -/
def skSwitch (sp : Spot) (n : Nums) : Skel :=
  { name := sp.name, place := sp.place, nRounds := 2, nOracles := 2
    told := toldFrom 0 [oraclesAt n.grp n.codes n.sent, []]
    before := n.read.map fun r => (sp.place.chain, r.1)
    planOk := decide (0 < n.positions) && (oraclesAt n.grp n.codes n.sent).length == n.roots &&
      increasing (n.read.map (·.1)) && decide (n.logN ≤ 32)
    claims := [], after := [] }

/-- The skeleton of a place at which the block cannot be made. -/
def skMute (sp : Spot) : Skel :=
  { name := sp.name, place := sp.place, nRounds := 0, nOracles := 0, told := [], before := []
    planOk := false, claims := [], after := [] }

/-- pureAt on skeletons. hd: the head's link's letters' test on the plan, where the letters are. -/
def skAt (hd : Nat → Option Bool) (x : Spot × Nums) : Option Skel :=
  match standsOf x.1 with
  | .finish => some (skSwitch x.1 x.2)
  | .head => (x.1.place.link.bind hd).map fun ok =>
      { skSwitch x.1 x.2 with planOk := (skSwitch x.1 x.2).planOk && ok }
  | .link => x.1.place.link.map fun _ => skSwitch x.1 x.2

/-- p2All, with the lot's numbers in the place of a place's. -/
def madeW (sps : List Spot) (Pq : Option Prep) : List (Spot × Nums) :=
  match Pq with
  | none => []
  | some P => (sps.filter fun sp => sp.place.kind == .K2).filterMap fun sp =>
      (numsAt P sp.place.link).map fun n => (sp, n)

/-- pureTable on skeletons. -/
def k2SkelOf (sps : Option (List Spot)) (Pq : Option Prep) (hd : Nat → Option Bool) : List Skel :=
  ((sps.getD []).filter fun sp => sp.place.kind == .K2).map fun sp =>
    match ((sps.map fun l => madeW l Pq).getD []).find? fun x => x.1.name == sp.name with
    | none => skMute sp
    | some x => (skAt hd x).getD (skMute sp)

/-- p2With's value. -/
def p2Of (Z : Pub) (sp : Spot) (n : Nums) : P2 :=
  { name := sp.name, place := sp.place, stands := standsOf sp, grp := n.grp
    firstTree := Z.P.firstTree, samples := n.samples
    work₁ := n.work₁, roots := n.roots, seeds := n.seeds, nonZero := n.nonZero
    work₂ := n.work₂, answers := n.answers, positions := n.positions, logN := n.logN
    sent := oraclesAt n.grp n.codes n.sent, read := n.read }

theorem p2All_made (Z : Pub) (G : Ground) (sps : List Spot) :
    p2All Z G sps = (madeW sps (prepOf Z G)).map fun x => (x.1, p2Of Z x.1 x.2) := by
  unfold p2All madeW
  cases prepOf Z G with
  | none => rfl
  | some P =>
    simp only [List.map_filterMap]
    congr 1
    funext sp
    unfold p2With
    cases numsAt P sp.place.link <;> rfl

theorem mute_skel (sp : Spot) (why : String) :
    (skel (pureMute sp why)).retype = skMute sp := by
  simp [skel, Skel.retype, pureMute, skMute, toldFrom]

theorem pureAt_skel (Z : Pub) (G : Ground) (x : Spot × Nums) :
    (pureAt (fun _ _ => some none) G (x.1, p2Of Z x.1 x.2)).map (fun b => (skel b).retype) =
      skAt (fun l => (pureLetters G l).map headPlanOk) x := by
  unfold pureAt skAt
  have hs : (p2Of Z x.1 x.2).stands = standsOf x.1 := rfl
  simp only [hs]
  cases standsOf x.1 with
  | finish =>
    simp [skel, Skel.retype, finishPlace, Block.andThen, VerifiableInference.Desc.roundlessBlock, codeSwitchKind,
      VerifiableInference.Desc.First.K2.rounds, skSwitch, p2Of]
    rfl
  | head =>
    cases x.1.place.link with
    | none => rfl
    | some l =>
      simp only [Option.bind_some]
      cases pureLetters G l with
      | none => rfl
      | some HP =>
        simp [skel, Skel.retype, headOpened, Block.andThen, VerifiableInference.Desc.roundlessBlock,
          codeSwitchKind, VerifiableInference.Desc.First.K2.rounds, skSwitch, p2Of]
        rfl
  | link =>
    cases x.1.place.link with
    | none => rfl
    | some l =>
      simp [skel, Skel.retype, codeSwitchKind, VerifiableInference.Desc.First.K2.rounds, skSwitch, p2Of]
      rfl

/-- **THE GENERAL LAW.** -/
theorem k2_lot_skel (Z : Pub) (G : Ground) :
    ((ProofFile.k2Pure Z).blocks G).map skel =
      k2SkelOf (spotsOf Z.cuts) (prepOf Z G) (fun l => (pureLetters G l).map headPlanOk) := by
  have e : (ProofFile.k2Pure Z).blocks G =
      (pureTable (fun _ _ => some none) Z G).map (fun b => b.retype) ++ [] := rfl
  rw [e, List.append_nil, List.map_map]
  unfold pureTable k2SkelOf purePlaces pureSpots
  rw [List.map_map]
  refine List.map_congr_left fun sp _ => ?_
  simp only [Function.comp]
  rw [skel_retype]
  have hm : ((spotsOf Z.cuts).map (p2All Z G)).getD [] =
      (((spotsOf Z.cuts).map fun l => madeW l (prepOf Z G)).getD []).map
        fun x => (x.1, p2Of Z x.1 x.2) := by
    cases spotsOf Z.cuts with
    | none => rfl
    | some l => exact p2All_made Z G l
  rw [hm, List.find?_map]
  cases hf : (((spotsOf Z.cuts).map fun l => madeW l (prepOf Z G)).getD []).find?
      ((fun x : Spot × P2 => x.1.name == sp.name) ∘ fun x => (x.1, p2Of Z x.1 x.2)) with
  | none =>
    have hf' : (((spotsOf Z.cuts).map fun l => madeW l (prepOf Z G)).getD []).find?
        (fun x => x.1.name == sp.name) = none := hf
    rw [hf']
    exact mute_skel sp _
  | some x =>
    have hf' : (((spotsOf Z.cuts).map fun l => madeW l (prepOf Z G)).getD []).find?
        (fun x => x.1.name == sp.name) = some x := hf
    rw [hf']
    have k := pureAt_skel Z G x
    simp only [Option.map_some]
    cases hp : pureAt (fun _ _ => some none) G (x.1, p2Of Z x.1 x.2) with
    | none =>
      rw [hp] at k
      rw [← k]
      exact mute_skel sp _
    | some b =>
      rw [hp] at k
      rw [← k]
      rfl

/-- What prepOf returns, off the sizes alone. -/
def prepW (z : ProofSized) : Option Prep :=
  ((List.range z.request.link.length).mapM
    (treesOfLink z.codes { shape := z.request, groups := reqGroups z.request })).map fun trees =>
      ⟨z, framesFrom z 0 (reqGroups z.request).toList z.request.link
        (List.replicate z.request.link.length 1) z.link.group, trees⟩

theorem prep_at {Z : Pub} {G : Ground} {z : ProofSized}
    (hz : Z.p.chains.made.sized.proof = z) (t1 : z.request = G.first.shape)
    (t2 : z.codes = G.first.codes) (t3 : Z.s₀.st.codes = z.codes)
    (t4 : Z.s₀.check.frame.shape = z.request) (t5 : z.set.samples = Z.P.samples) :
    prepOf Z G = prepW z := by
  have ht : tied z G.first Z.s₀.st.codes Z.s₀.check.frame.shape Z.P.samples = true := by
    unfold tied
    simp [t1, t2, t3, t4, t5]
  unfold prepOf prepareAt prepW
  rw [hz]
  simp only [ht, Option.bind_eq_bind, Option.pure_def]
  rw [← t1]
  cases (List.range z.request.link.length).mapM
    (treesOfLink z.codes { shape := z.request, groups := reqGroups z.request }) <;> rfl

theorem skAt_hd {hd hd' : Nat → Option Bool} (x : Spot × Nums)
    (h : standsOf x.1 = .head → x.1.place.link.bind hd = x.1.place.link.bind hd') :
    skAt hd x = skAt hd' x := by
  unfold skAt
  cases hs : standsOf x.1 with
  | finish => rfl
  | link => rfl
  | head =>
    simp only
    rw [h hs]

theorem madeW_mem {sps : List Spot} {Pq : Option Prep} {x : Spot × Nums}
    (h : x ∈ madeW sps Pq) : x.1 ∈ sps := by
  unfold madeW at h
  cases Pq with
  | none => cases h
  | some P =>
    obtain ⟨sp, hsp, e⟩ := List.mem_filterMap.1 h
    obtain ⟨n, _, rfl⟩ := Option.map_eq_some_iff.1 e
    exact (List.mem_filter.1 hsp).1

theorem k2SkelOf_hd {sps : Option (List Spot)} {Pq : Option Prep} {hd hd' : Nat → Option Bool}
    (h : ∀ sp ∈ sps.getD [], standsOf sp = .head →
      sp.place.link.bind hd = sp.place.link.bind hd') :
    k2SkelOf sps Pq hd = k2SkelOf sps Pq hd' := by
  unfold k2SkelOf
  refine List.map_congr_left fun sp _ => ?_
  cases hf : ((sps.map fun l => madeW l Pq).getD []).find? fun x => x.1.name == sp.name with
  | none => rfl
  | some x =>
    have hx : x.1 ∈ sps.getD [] := by
      have hm := List.mem_of_find?_eq_some hf
      cases sps with
      | none => cases hm
      | some l => exact madeW_mem hm
    simp only
    rw [skAt_hd x (h x.1 hx)]

/-- **THE WRITTEN ROWS.** planOk := true in all 25: so `k2_row_closed` also says that the switch's
four
tests on the plan accept at all 25 places at the written sizes, and it spends «the head's test on
the plan accepts» at link 24. -/
def k2SkelW : List Skel :=
  (cutFirstFull.filter fun x => x.2.1.kind == .K2).map fun x =>
    ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2, true, [], []⟩

/-- The head's test on the plan accepts at link 24; no letters elsewhere. -/
def hdW (ok : Option Bool) : Nat → Option Bool := fun l => if l == 24 then ok else none

/-! ## Twins that the kernel bears: standsOf cuts a name by String.splitOn, at which it sticks -/

/-- standsOf over the twin of headOf. -/
def standsK (sp : Spot) : At :=
  let h := headK ((sp.cuts.head?.map (·.look)).getD "")
  if h == "F" then .finish else if h == "H" then .head else .link

theorem standsOf_eq (sp : Spot) : standsOf sp = standsK sp := by
  unfold standsOf standsK
  rw [headOf_eq]

/-- skAt over standsK. -/
def skAtK (hd : Nat → Option Bool) (x : Spot × Nums) : Option Skel :=
  match standsK x.1 with
  | .finish => some (skSwitch x.1 x.2)
  | .head => (x.1.place.link.bind hd).map fun ok =>
      { skSwitch x.1 x.2 with planOk := (skSwitch x.1 x.2).planOk && ok }
  | .link => x.1.place.link.map fun _ => skSwitch x.1 x.2

theorem skAt_K (hd : Nat → Option Bool) (x : Spot × Nums) : skAt hd x = skAtK hd x := by
  unfold skAt skAtK
  rw [standsOf_eq]

/-- k2SkelOf over skAtK. -/
def k2SkelOfK (sps : Option (List Spot)) (Pq : Option Prep) (hd : Nat → Option Bool) :
    List Skel :=
  ((sps.getD []).filter fun sp => sp.place.kind == .K2).map fun sp =>
    match ((sps.map fun l => madeW l Pq).getD []).find? fun x => x.1.name == sp.name with
    | none => skMute sp
    | some x => (skAtK hd x).getD (skMute sp)

theorem k2SkelOf_K (sps : Option (List Spot)) (Pq : Option Prep) (hd : Nat → Option Bool) :
    k2SkelOf sps Pq hd = k2SkelOfK sps Pq hd := by
  unfold k2SkelOf k2SkelOfK
  simp only [skAt_K]

/-! ## Closed facts, by the kernel: once, at the written places -/

set_option maxRecDepth 1000000 in
theorem head_at_24S : spotsWritten.all
    (fun sp => !(decide (standsOf sp = .head)) || sp.place.link == some 24) = true := by
  simp only [standsOf_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem k2_row_count : k2SkelW.length = 25 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem k2_row_closedS :
    k2SkelOf (some spotsWritten) (prepW proofSizedFull) (hdW (some true)) = k2SkelW := by
  rw [k2SkelOf_K]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem k2_row_no_headS :
    k2SkelOf (some spotsWritten) (prepW proofSizedFull) (hdW (some false)) ≠ k2SkelW := by
  rw [k2SkelOf_K]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem k2_row_head_muteS :
    k2SkelOf (some spotsWritten) (prepW proofSizedFull) (hdW none) ≠ k2SkelW := by
  rw [k2SkelOf_K]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem k2_row_no_prepS :
    k2SkelOf (some spotsWritten) none (hdW (some true)) ≠ k2SkelW := by
  rw [k2SkelOf_K]
  decide +kernel

/-- The written numbers with the first link's trees struck. -/
def bentTrees : Option Prep :=
  (prepW proofSizedFull).map fun P => { P with trees := [] :: P.trees.drop 1 }

set_option maxRecDepth 1000000 in
theorem k2_row_bent_treesS :
    k2SkelOf (some spotsWritten) bentTrees (hdW (some true)) ≠ k2SkelW := by
  rw [k2SkelOf_K]
  decide +kernel

/-! ## The same at the written table of steps: one rewriting each -/

theorem head_at_24 : ((spotsOf cutWritten).getD []).all
    (fun sp => !(decide (standsOf sp = .head)) || sp.place.link == some 24) = true := by
  rw [spots_written]
  exact head_at_24S

theorem k2_row_closed :
    k2SkelOf (spotsOf cutWritten) (prepW proofSizedFull) (hdW (some true)) = k2SkelW := by
  rw [spots_written]
  exact k2_row_closedS

theorem k2_row_no_head :
    k2SkelOf (spotsOf cutWritten) (prepW proofSizedFull) (hdW (some false)) ≠ k2SkelW := by
  rw [spots_written]
  exact k2_row_no_headS

theorem k2_row_head_mute :
    k2SkelOf (spotsOf cutWritten) (prepW proofSizedFull) (hdW none) ≠ k2SkelW := by
  rw [spots_written]
  exact k2_row_head_muteS

theorem k2_row_no_prep :
    k2SkelOf (spotsOf cutWritten) none (hdW (some true)) ≠ k2SkelW := by
  rw [spots_written]
  exact k2_row_no_prepS

theorem k2_row_bent_trees :
    k2SkelOf (spotsOf cutWritten) bentTrees (hdW (some true)) ≠ k2SkelW := by
  rw [spots_written]
  exact k2_row_bent_treesS

/-- Without the lot's numbers every place is mute: general. -/
theorem k2_all_mute (sps : Option (List Spot)) (hd : Nat → Option Bool) :
    k2SkelOf sps none hd = ((sps.getD []).filter fun sp => sp.place.kind == .K2).map skMute := by
  unfold k2SkelOf
  refine List.map_congr_left fun sp _ => ?_
  cases sps <;> rfl

/-- **THE ROW, under the places themselves.** -/
theorem k2_row_spots {Zq : Pub} {G : Ground} (hs : spotsOf Zq.cuts = some spotsWritten)
    (hz : Zq.p.chains.made.sized.proof = proofSizedFull)
    (t1 : proofSizedFull.request = G.first.shape) (t2 : proofSizedFull.codes = G.first.codes)
    (t3 : Zq.s₀.st.codes = proofSizedFull.codes)
    (t4 : Zq.s₀.check.frame.shape = proofSizedFull.request)
    (t5 : proofSizedFull.set.samples = Zq.P.samples)
    (hH : (pureLetters G 24).map headPlanOk = some true) :
    ((ProofFile.k2Pure Zq).blocks G).map skel = k2SkelW := by
  rw [k2_lot_skel, hs, prep_at hz t1 t2 t3 t4 t5]
  refine Eq.trans (k2SkelOf_hd fun sp hsp hs' => ?_) k2_row_closedS
  have k := List.all_eq_true.1 head_at_24S sp hsp
  rw [hs'] at k
  simp only [decide_true, Bool.not_true, Bool.false_or, beq_iff_eq] at k
  rw [k]
  exact hH

/-- **THE ROW.** -/
theorem k2_row {Zq : Pub} {G : Ground} (hc : Zq.cuts = cutWritten)
    (hz : Zq.p.chains.made.sized.proof = proofSizedFull)
    (t1 : proofSizedFull.request = G.first.shape) (t2 : proofSizedFull.codes = G.first.codes)
    (t3 : Zq.s₀.st.codes = proofSizedFull.codes)
    (t4 : Zq.s₀.check.frame.shape = proofSizedFull.request)
    (t5 : proofSizedFull.set.samples = Zq.P.samples)
    (hH : (pureLetters G 24).map headPlanOk = some true) :
    ((ProofFile.k2Pure Zq).blocks G).map skel = k2SkelW :=
  k2_row_spots (by rw [hc]; exact spots_written) hz t1 t2 t3 t4 t5 hH

/-- The lot's own count. -/
theorem k2_lot_count {Zq : Pub} {G : Ground} (hc : Zq.cuts = cutWritten)
    (hz : Zq.p.chains.made.sized.proof = proofSizedFull)
    (t1 : proofSizedFull.request = G.first.shape) (t2 : proofSizedFull.codes = G.first.codes)
    (t3 : Zq.s₀.st.codes = proofSizedFull.codes)
    (t4 : Zq.s₀.check.frame.shape = proofSizedFull.request)
    (t5 : proofSizedFull.set.samples = Zq.P.samples)
    (hH : (pureLetters G 24).map headPlanOk = some true) :
    ((ProofFile.k2Pure Zq).blocks G).length = 25 := by
  have k := congrArg List.length (k2_row hc hz t1 t2 t3 t4 t5 hH)
  rw [List.length_map, k2_row_count] at k
  exact k

theorem k2_steady (Z : Pub) (G : Ground) : Steady G (ProofFile.k2Pure Z) :=
  steady_none G _ fun _ => rfl

theorem k2_lotSk_spots {Zq : Pub} {G : Ground} (hs : spotsOf Zq.cuts = some spotsWritten)
    (hz : Zq.p.chains.made.sized.proof = proofSizedFull)
    (t1 : proofSizedFull.request = G.first.shape) (t2 : proofSizedFull.codes = G.first.codes)
    (t3 : Zq.s₀.st.codes = proofSizedFull.codes)
    (t4 : Zq.s₀.check.frame.shape = proofSizedFull.request)
    (t5 : proofSizedFull.set.samples = Zq.P.samples)
    (hH : (pureLetters G 24).map headPlanOk = some true) :
    lotSk G (ProofFile.k2Pure Zq) =
      { name := "the code switch", letters := false, still := [], blocks := k2SkelW
        batch := fun _ => none, each := fun _ => false, tests := fun _ => false } := by
  have k := k2_row_spots hs hz t1 t2 t3 t4 t5 hH
  unfold lotSk
  rw [k]
  rfl

theorem k2_lotSk {Zq : Pub} {G : Ground} (hc : Zq.cuts = cutWritten)
    (hz : Zq.p.chains.made.sized.proof = proofSizedFull)
    (t1 : proofSizedFull.request = G.first.shape) (t2 : proofSizedFull.codes = G.first.codes)
    (t3 : Zq.s₀.st.codes = proofSizedFull.codes)
    (t4 : Zq.s₀.check.frame.shape = proofSizedFull.request)
    (t5 : proofSizedFull.set.samples = Zq.P.samples)
    (hH : (pureLetters G 24).map headPlanOk = some true) :
    lotSk G (ProofFile.k2Pure Zq) =
      { name := "the code switch", letters := false, still := [], blocks := k2SkelW
        batch := fun _ => none, each := fun _ => false, tests := fun _ => false } := by
  have k := k2_row hc hz t1 t2 t3 t4 t5 hH
  unfold lotSk
  rw [k]
  rfl

end Johnson.AtFull.Lots.K2

#print axioms Johnson.AtFull.Lots.K2.p2All_made
#print axioms Johnson.AtFull.Lots.K2.mute_skel
#print axioms Johnson.AtFull.Lots.K2.pureAt_skel
#print axioms Johnson.AtFull.Lots.K2.k2_lot_skel
#print axioms Johnson.AtFull.Lots.K2.prep_at
#print axioms Johnson.AtFull.Lots.K2.skAt_hd
#print axioms Johnson.AtFull.Lots.K2.madeW_mem
#print axioms Johnson.AtFull.Lots.K2.k2SkelOf_hd
#print axioms Johnson.AtFull.Lots.K2.standsOf_eq
#print axioms Johnson.AtFull.Lots.K2.skAt_K
#print axioms Johnson.AtFull.Lots.K2.k2SkelOf_K
#print axioms Johnson.AtFull.Lots.K2.head_at_24S
#print axioms Johnson.AtFull.Lots.K2.k2_row_count
#print axioms Johnson.AtFull.Lots.K2.k2_row_closedS
#print axioms Johnson.AtFull.Lots.K2.k2_row_no_headS
#print axioms Johnson.AtFull.Lots.K2.k2_row_head_muteS
#print axioms Johnson.AtFull.Lots.K2.k2_row_no_prepS
#print axioms Johnson.AtFull.Lots.K2.k2_row_bent_treesS
#print axioms Johnson.AtFull.Lots.K2.head_at_24
#print axioms Johnson.AtFull.Lots.K2.k2_row_closed
#print axioms Johnson.AtFull.Lots.K2.k2_row_no_head
#print axioms Johnson.AtFull.Lots.K2.k2_row_head_mute
#print axioms Johnson.AtFull.Lots.K2.k2_row_no_prep
#print axioms Johnson.AtFull.Lots.K2.k2_row_bent_trees
#print axioms Johnson.AtFull.Lots.K2.k2_all_mute
#print axioms Johnson.AtFull.Lots.K2.k2_row_spots
#print axioms Johnson.AtFull.Lots.K2.k2_row
#print axioms Johnson.AtFull.Lots.K2.k2_lot_count
#print axioms Johnson.AtFull.Lots.K2.k2_steady
#print axioms Johnson.AtFull.Lots.K2.k2_lotSk_spots
#print axioms Johnson.AtFull.Lots.K2.k2_lotSk
