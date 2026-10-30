-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K03ReadersHeadOut.lean: the kind "lookup" (K3): what a segment's readers answer in front
of the lookup on the digits they answer behind it: at the output head's segment (number 24), under
the library's hypothesis `AtMgA`. Conditional: under three hypotheses that the asked form did not
name: two on the lookup on the calls, one on what the output head's own sub-protocol has heard. No
string of a file stands in any hypothesis beyond `AtMgA`'s own letters. After
Johnson/P5J/K03ReadersHeadLay.lean and K03ReadersHeadAtt.lean (the 24 segments below). One closed
test with code and ten theorems: four by the kernel's evaluation (two of them negative tests), two
small ones on the test's text, the others compositions of the library's theorems.

Terms. lean/GLOSSARY.md; the head of Johnson/P5J/K03ReadersHeadLay.lean.

What is shown.
  `k03_readers_out_runs`: at segment 24 eight runs go forward over the step: (2, "objects"), (2,
    "guests"), (2, "planes"), (3, "join"), (3, "norm"), (3, "policy"), (3, "logits"), (5,
    "K8.equations").
  `k03_readers_out_items`: so every run of the six items of `earlyOf .head`: "objects" has two runs,
    "planes" one, "join" one, "own" three, "weights" none, "small" one (`runs_head`,
    Johnson/Desc/Sound/MgAt/Runs.lean): at "weights" the conclusion is true of nothing, by the
    table.
  `outsOpenB`, `outsOpen_full`, `outsOpen_control`, `outsOpen_control2`: at the border: a sentence
    forms that is open in front and behind is of segment 24 and stands in the written list: by the
    kernel's evaluation; with an empty list the test says no; with another number for the segment's
    it says no.
  `outsOpen_six`: six sentences forms are open in front of the border and behind it: by the kernel's
    evaluation.
  `outsOpenB_def`, `open_cut`: the test's text; what such a test gives at a sentence that stands in
    both lists, general in the lists.
  `k3_digits_readers_out`: the last theorem but one. Its conclusion is the asked form's to the
    letter, and so are its binders on `h`, the sub-protocol at the border, ft, the step, the item,
    "open in front" and "open behind", at l := 24.
  `k3_digits_readers_out_below`: the same with `hK` shown from "reached by the sub-protocols with
    the test on the words in front".

Hypotheses that remain.
  `h`: the library's hypothesis `AtMgA`.
  `hb`: blk is the chain's sub-protocol at the border. `hy`: the step: blk accepts from s to s'
    (`IM.Yes`).
  `hx`: (in the last two theorems) the Boolean tests at the border (`IM.XK`, at any numbers and any
    further tests): the test on the shape alone is used. `hsh`: (in the two theorems on the runs)
    that test on the shape by itself.
  `hO`, `hL`: the two facts on the lookup on the calls of the same segment, as in the two files
    before.
  `hK`: K6HeardAt … s (Johnson/Desc/Kinds/Law/K6Claims.lean): what the output head's own
    sub-protocol has heard is read back at the state.
  `hreach`: (in `k3_digits_readers_out_below`, in `hK`'s stead) the state in front is reached by the
    sub-protocols with the test on the words in front (Reach 0 (cF.blocksInOrder.map below) …).
  `hin`: (in `k03_readers_out_items`) the item stands in the written list.
  `ho`, `ho'`: (in the last two theorems) the sentence forms is open in front of the border, and
    behind it. In `open_cut`: `hB`, `ho`, `ho'`: the test accepts; the sentence stands in both
    lists.
On `hK`. The library's theorem that shows it (`heardAt_345`, Johnson/P5J/K03ReadyAt345.lean) takes
"reached" by the sub-protocols with the test on the words in front, and uses that test (the
rounds of the output head's own sub-protocol are canonical: `heard_342`, Johnson/P4R/Head342.lean).
The asked form's "reached" is the bare one, which is the wider family: `hK` does not follow from it
by any theorem of the library that this file's writer knows. `hK` is of none of the four kinds of
hypothesis that the asked form offered. So `hK` stands as a hypothesis in the last theorem but one,
and the last theorem shows it from the narrower "reached". Of the test on the words the library's
proof uses one step's alone: the rounds of the step from border 341 to border 342 are canonical.
Nothing is asked of the state behind but the step. Not used, and so not asked: "no mark in front";
the test on the samples.

Who shows `hO` and `hL`. They are the composed meaning's own two public items at that border. By the
kernel's evaluation, at all 25 segments (`planesFront_mgMore`,
Johnson/Desc/Sound/MgAt/K3DigitsPlanesIt.lean): Pub.lookOut l (IM.k3Place l false).piece stands
among the items whose test holds in front of the digits' place, and Pub.leftOn l among those whose
sentence holds there. At mgAll the first's test is `hO`'s left side and the second's sentence is
`hL` (the fields lookOut and pLeftOn of `k3At_mgAll`). The library's `callsItems_front_dig`
(Johnson/Desc/Sound/MgAt/K3DigitsStaysBelow.lean) takes the two out of the promise with the files'
strings in just this way, and uses "no mark in front" for it: whoever draws `hO` and `hL` from a
promise will need that hypothesis there, though no theorem of this file asks it.

How the proof goes. It follows the library's `fwd_step_head_hole`
(Johnson/Desc/Sound/MgAt/K3RidesDigFwd3.lean) and `k03_head_pair`, `k03_fwd_own_head_front`,
`k03_fwd_join_head_front` (Johnson/P5J/K03HeadOwnAt.lean) step by step, with what each takes from
the promise with the files' strings in its place. That the runs "objects" and "guests" themselves
answer in front is not asked: at "objects" it follows from the hypothesis of `Fwd` itself
(`objects_hr_holesAt`, Johnson/Top/H/Keep/RunAnswers.lean), at "guests" from the open ledger
(`guests_hr`).

Options. `maxRecDepth` is raised to 100000 for the file and to 1000000 in front of four theorems;
`maxHeartbeats` to 4000000 in front of one theorem; the file is one `noncomputable section`. These
raise limits on Lean's own work or switch off a check on a notation's names: none loosens a check on
a proof.

Limits. Compositions. `h` is a hypothesis. An instance of it at each of the two named sets of public
files stands in the library's side files: `headMember_zFull` (AtFullSide/Top/HeadMemberAtFull.lean)
and `headMember_zGap` (AtFullSide/Top/HeadMemberAtGap.lean). No state is
shown at which the hypotheses hold together. Segment 24 alone. At OnBytes.secondHashFunction. The full size
alone. Of the files composed here the statements that are called and the
proofs of the four theorems named were read, no more; Johnson/P5J/K03HeadOwnAt.lean in another form.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.P5J.K03ReadersHeadAtt
import Johnson.P5J.K03HeadOwnAt
import Johnson.P5J.K03RidesDigHeadHole

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open Inst.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit Link Block)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item runsOf shapeAt Numbers)
open VerifiableInference.Desc.First.Look (placeAt k3OnOutAt)
open VerifiableInference.Desc.K3 (seatCalls unpaid)
open VerifiableInference.Desc.K9 (statesOfLink holesAt smallReader readersOfLink readerOf)
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law
open VerifiableInference.Reads.Pass (Fwd)
open Johnson.Desc.First.Walk.Tied (Reach)

local notation "PS" => VerifiableInference.Desc.First.flatPlacesOf linksFull true

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

set_option maxHeartbeats 4000000 in
/-- **The eight runs at the output head's segment.** -/
theorem k03_readers_out_runs (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    {blk : Block S ProofFile.Cl} (hb : cF.blocksInOrder[k3K 24 true]? = some blk) (ft : ℕ) {s s' : S}
    (hsh : shapeAt linksFull (PS)[k3K 24 true]? s = true)
    (hO : k3OnOutAt (At.X Zp) 24 false s = true) (hL : k3LeftOnItemAt (At.X Zp) 24 s)
    (hK : K6HeardAt (At.X Zp).hS (readsOf (At.X Zp)) (parOf (At.X Zp).hS (workOf (At.X Zp))) s)
    (hy : IM.Yes ft blk s s') :
    ∀ p ∈ [(2, "objects"), (2, "guests"), (2, "planes"), (3, "join"), (3, "norm"), (3, "policy"),
        (3, "logits"), (5, "K8.equations")],
      Fwd (h.𝔇.Rd 24) p.1 p.2 s s' := by
  intro p hp
  have hl : 24 < 25 := by omega
  obtain ⟨b', hb', hOk, hstep⟩ := k03_yes_stepRel h hl hb
  obtain ⟨rs, gs, hd⟩ := hstep ft s s' hy
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hW : Bs.G₀.W = At.X Zp := O.W
  have hsub : linksFull[24]? = some ModelPart.head := by decide +kernel
  -- the two facts on the lookup on the calls
  obtain ⟨pc, hpcAt, hLf⟩ := hL
  have hOo : VerifiableInference.Desc.K3.k3OnOut pc s = true := by
    unfold k3OnOutAt at hO
    rw [hpcAt] at hO
    exact hO
  have hdc : pc.digits = false := by
    unfold placeAt at hpcAt
    obtain ⟨y, -, rfl⟩ := Option.map_eq_some_iff.1 hpcAt
    rfl
  -- the state in front
  obtain ⟨F, hF, hSz⟩ := k03_onOut_ledger hdc hOo hLf
  obtain ⟨o, ho⟩ := VerifiableInference.Desc.K1.here_head_of_stand
    (k03_stand_of_shape hl hsub hsh)
  -- across the whole acceptance at the seat
  have hpc := k03_pieceAt_dig h.toAtMg 24
  obtain ⟨G, Q⟩ := k3_digits_step_pass K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp)
    Zp.first.codes Zp.first.shape (IM.k3Place 24 true) b' hb' hOk 24 rfl hpc s s' rs gs hd hF hSz
  have A := k3_digits_step_samePlanes K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp)
    Zp.first.codes Zp.first.shape (IM.k3Place 24 true) b' hb' hOk 24 rfl hpc s s' rs gs hd
  have HS := k3_digits_step_headStays K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp)
    Zp.first.codes Zp.first.shape (IM.k3Place 24 true) b' hb' hOk 24 rfl hpc s s' rs gs hd
  obtain ⟨-, -, -, -, hLk, -, -⟩ := k3_digits_step_leaves K3Lot.ofForm
    (K3Lot.readersAt (At.X Zp)) (At.X Zp) Zp.first.codes Zp.first.shape (IM.k3Place 24 true) b' hb'
    hOk 24 rfl hpc s s' rs gs hd
  have hob : ∀ i, unpaid G i = true → unpaid F i = true :=
    k3_digits_step_hob K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp) Zp.first.codes
      Zp.first.shape (IM.k3Place 24 true) b' hb' hOk 24 rfl hpc s s' rs gs hd Q
  have hsq : ∀ o', s'.here = .head o' → o'.squaresP = o.squaresP := by
    intro o' h'
    obtain ⟨a', ha', hkp⟩ := HS o ho
    obtain rfl : a' = o' := by
      have e := ha'.symm.trans h'
      simpa using e
    rw [hkp.eq]
  have hop : o.opened = true := by
    cases hc : o.opened with
    | true => rfl
    | false =>
      have hf := hF
      simp [S.fork?, ho, hc] at hf
  have eF : o.F = F := by
    have hf := hF
    simpa [S.fork?, ho, hop] using hf
  have a := alike_of_pass A Q ho hsq
  have hReady : ∀ zz U, Sees s zz U → K6Ready (At.X Zp).hS (readsOf (At.X Zp))
      (parOf (At.X Zp).hS (workOf (At.X Zp))) zz U := by
    intro zz U hs
    obtain ⟨g, H, F0, G0, rs0, hg, hH, hWd, hh0, hLa⟩ := hK
    refine ⟨s, g, H, F0, G0, rs0, hs, hg, hH, hWd, hh0, ?_⟩
    obtain ⟨o2, ho2, rfl, -⟩ := hs
    obtain rfl : o = o2 := by
      have e := ho.symm.trans ho2
      simpa using e
    have eL : (seatAt (At.X Zp).hS (readsOf (At.X Zp))).ledger s = F := by
      show s.fork?.getD {} = F
      rw [hF]
      rfl
    rw [eF, ← eL]
    exact hLa
  -- the link, its readers, its holes, the finds
  have h24 : headLink (At.X Zp) = 24 := headLink_in_scope h.scope h.reads h.pubOne
  have hm' : (24 == headLink (At.X Zp)) = true := by rw [h24]; rfl
  have hU : (At.X Zp).H.tl.ix.U.getD 2 none = some 0 :=
    VerifiableInference.Desc.Kinds.Head.Law.ReadsNamed.public_third h.pubOne
  have hrd : K3Lot.readersAt (At.X Zp) 24 = some (callerReaders (planesAt 0)) := by
    obtain ⟨p4, ng, -⟩ := _root_.Meaning.scope_plans h.scope h.reads h.pubOne
    unfold K3Lot.readersAt VerifiableInference.Desc.K3.isHead
    rw [p4, ng, hU]
    rfl
  obtain ⟨Lk, hLk0, hOb⟩ := k03_objects_raw h.scope h.reads O 24 hl false
  obtain ⟨L2, e2, hGu⟩ := k03_guests_raw h.scope h.reads O 24 hl false
  obtain ⟨L3, pp, e3, -, hPl⟩ := k03_planes_raw h.scope h.reads O 24 hl
    (callerReaders (planesAt 0)) (by rw [hW]; exact hrd)
  obtain rfl : Lk = L2 := Option.some.inj (hLk0.symm.trans e2)
  obtain rfl : Lk = L3 := Option.some.inj (hLk0.symm.trans e3)
  have hk : (h.toAtMg.𝔇 h.𝔇).lk 24 = some Lk := (h.laid.linkAt 24).trans hLk0
  have hfO : ∀ n r, (statesOfLink Lk 2).find? (fun x => x.1 == "objects") = some (n, r) →
      r = objectsRun (seatCalls K3Lot.ofForm) :=
    fun n r e => (Prod.mk.inj (Option.some.inj (hOb.symm.trans e))).2.symm
  have hRd : h.𝔇.Rd 24 = readersOfLink (holesAt (At.X Zp) (headLink (At.X Zp)) 24 Lk) Lk :=
    k03_hlink h 24 Lk hLk0
  rw [hRd]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro R hR
    exact fwd_of_noSilent _ Lk 2 (by decide)
      (objects_hr_holesAt (At.X Zp) (headLink (At.X Zp)) 24 Lk 2 K3Lot.ofForm k03_atS2_calls hfO hR)
      (objects_fwd (noSilent _) Lk 2 (seatCalls K3Lot.ofForm) k03_atS2_calls Q hLk rfl hfO) R hR
  · exact fwd_of_noSilent _ Lk 2 (by decide)
      (guests_hr Lk 2 (fun _ _ => True) (fun _ => trivial) ⟨_, _, hGu, fun _ _ _ hr _ => hr⟩ hF)
      (guests_fwd (noSilent _) Lk 2 Q rfl
        (fun n r e => (Prod.mk.inj (Option.some.inj (hGu.symm.trans e))).2.symm))
  · exact planes_fwd_head (At.X Zp) (headLink (At.X Zp)) 24 hm' Lk 2 K3Lot.ofForm k03_atS2_calls Q A
      hLk hob pp.lm 0 (hwin_of_onOut hdc hF hOo hLf)
      (fun n r e => (Prod.mk.inj (Option.some.inj (hPl.symm.trans e))).2.symm) ho
  · exact join_fwd_seat (At.X Zp) _ 24 hm' Lk 3 _ _ 24 4 _ Q A a (k03_six_K h hk) hReady
      (k03_six_hBj h hk) atS2_calls_ofForm hLk hob
  · exact own_fwd_seat (At.X Zp) _ 24 hm' Lk 3 _ _ 24 4 _ Q A a (k03_six_K h hk) hReady
      (k03_six_hBo h hk) (Or.inl rfl)
  · exact own_fwd_seat (At.X Zp) _ 24 hm' Lk 3 _ _ 24 4 _ Q A a (k03_six_K h hk) hReady
      (k03_six_hBo h hk) (Or.inr (Or.inl rfl))
  · exact own_fwd_seat (At.X Zp) _ 24 hm' Lk 3 _ _ 24 4 _ Q A a (k03_six_K h hk) hReady
      (k03_six_hBo h hk) (Or.inr (Or.inr rfl))
  · exact small_fwd _ Lk 5 (fun R hR => by
      show smallReader s' = some R
      rw [k3_digits_step_smallReader K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp)
        Zp.first.codes Zp.first.shape (IM.k3Place 24 true) b' hb' hOk 24 rfl hpc s s' rs gs hd]
      exact hR)

/-- **Every run of the six items of the written list.** -/
theorem k03_readers_out_items (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    {blk : Block S ProofFile.Cl} (hb : cF.blocksInOrder[k3K 24 true]? = some blk) (ft : ℕ) {s s' : S}
    (hsh : shapeAt linksFull (PS)[k3K 24 true]? s = true)
    (hO : k3OnOutAt (At.X Zp) 24 false s = true) (hL : k3LeftOnItemAt (At.X Zp) 24 s)
    (hK : K6HeardAt (At.X Zp).hS (readsOf (At.X Zp)) (parOf (At.X Zp).hS (workOf (At.X Zp))) s)
    (hy : IM.Yes ft blk s s') (k : ℕ) (ρ : String) (hin : (k, ρ) ∈ earlyOf .head) :
    ∀ p ∈ h.𝔇.runs 24 k ρ, Fwd (h.𝔇.Rd 24) p.1 p.2 s s' := by
  intro p hp
  have hsub : linksFull[24]? = some ModelPart.head := by decide +kernel
  have e : h.𝔇.runs 24 k ρ = runsOf .head k ρ := runsAt_of linksFull 24 .head hsub k ρ
  rw [e] at hp
  have H := k03_readers_out_runs h hb ft hsh hO hL hK hy p
  simp only [earlyOf, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hin
  rcases hin with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [runs_head.1] at hp
    exact H (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp ⊢
      rcases hp with rfl | rfl <;> simp)
  · rw [runs_head.2.1] at hp
    exact H (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp ⊢
      subst hp
      simp)
  · rw [runs_head.2.2.1] at hp
    exact H (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp ⊢
      subst hp
      simp)
  · rw [runs_head.2.2.2.1] at hp
    exact H (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp ⊢
      rcases hp with rfl | rfl | rfl <;> simp)
  · rw [runs_head.2.2.2.2.1] at hp
    cases hp
  · rw [runs_head.2.2.2.2.2.1] at hp
    exact H (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp ⊢
      subst hp
      simp)

/-- At the border: a sentence forms that is open in front and behind bears the number 24 + off and
stands in the list E. -/
def outsOpenB (E : List (ℕ × String)) (off : ℕ) : Bool :=
  (IM.openAt IM.linksW IM.placesW (k3K 24 true)).all fun i =>
    match i with
    | .forms m k ρ =>
      !((IM.openAt IM.linksW IM.placesW (k3K 24 true + 1)).contains (.forms m k ρ)) ||
        (m == 24 + off && E.contains (k, ρ))
    | _ => true

set_option maxRecDepth 1000000 in
theorem outsOpen_full : outsOpenB (earlyOf .head) 0 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **A negative test**: with an empty list the test says no. -/
theorem outsOpen_control : outsOpenB [] 0 = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **A second negative test**: with another number for the segment's it says no. -/
theorem outsOpen_control2 : outsOpenB (earlyOf .head) 1 = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- There are six. -/
theorem outsOpen_six : ((ridersAt (k3K 24 true)).length == 6) = true := by decide +kernel

/-- The test's text. -/
theorem outsOpenB_def (E : List (ℕ × String)) (off : ℕ) :
    outsOpenB E off = (IM.openAt IM.linksW IM.placesW (k3K 24 true)).all fun i =>
      match i with
      | .forms m k ρ =>
        !((IM.openAt IM.linksW IM.placesW (k3K 24 true + 1)).contains (.forms m k ρ)) ||
          (m == 24 + off && E.contains (k, ρ))
      | _ => true := rfl

/-- What such a test gives at a sentence forms that stands in both lists: general in the lists. -/
theorem open_cut {L L' : List Item} {E : List (ℕ × String)} {n : ℕ}
    (hB : (L.all fun i =>
      match i with
      | .forms m k ρ => !(L'.contains (.forms m k ρ)) || (m == n && E.contains (k, ρ))
      | _ => true) = true) {m k : ℕ} {ρ : String} (ho : Item.forms m k ρ ∈ L)
    (ho' : Item.forms m k ρ ∈ L') : m = n ∧ (k, ρ) ∈ E := by
  have h2 : (!(L'.contains (Item.forms m k ρ)) || (m == n && E.contains (k, ρ))) = true :=
    List.all_eq_true.1 hB _ ho
  rw [List.contains_iff_mem.2 ho'] at h2
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at h2
  exact ⟨h2.1, List.contains_iff_mem.1 h2.2⟩

-- from here on the closed lists are not unfolded
attribute [local irreducible] IM.openAt VerifiableInference.Desc.First.flatPlacesOf

/-- **The last theorem but one, at l := 24**: the tests at the border, at any numbers and any
further tests; the two facts on the lookup on the calls; what the output head's own sub-protocol has
heard is read back; the step. -/
theorem k3_digits_readers_out (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    {blk : Block S ProofFile.Cl} (hb : cF.blocksInOrder[k3K 24 true]? = some blk) (N : Numbers)
    (E : ℕ → S → Bool) (ft : ℕ) {s s' : S}
    (hx : IM.XK N IM.linksW IM.placesW E (k3K 24 true) s = true)
    (hO : k3OnOutAt (At.X Zp) 24 false s = true) (hL : k3LeftOnItemAt (At.X Zp) 24 s)
    (hK : K6HeardAt (At.X Zp).hS (readsOf (At.X Zp)) (parOf (At.X Zp).hS (workOf (At.X Zp))) s)
    (hy : IM.Yes ft blk s s') (m k : ℕ) (ρ : String)
    (ho : Item.forms m k ρ ∈ IM.openAt IM.linksW IM.placesW (k3K 24 true))
    (ho' : Item.forms m k ρ ∈ IM.openAt IM.linksW IM.placesW (k3K 24 true + 1)) :
    ∀ p ∈ h.𝔇.runs m k ρ, Fwd (h.𝔇.Rd m) p.1 p.2 s s' := by
  have hsh : shapeAt linksFull (PS)[k3K 24 true]? s = true := by
    have h0 := (IM.xk_parts hx).1
    rwa [linksW_full, placesW_full] at h0
  have h1 := outsOpen_full
  rw [outsOpenB_def] at h1
  obtain ⟨rfl, h3⟩ := open_cut h1 ho ho'
  exact k03_readers_out_items h hb ft hsh hO hL hK hy k ρ h3

/-- **The same, hK shown from "reached by the sub-protocols with the test on the words in
front".** -/
theorem k3_digits_readers_out_below (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    {blk : Block S ProofFile.Cl} (hb : cF.blocksInOrder[k3K 24 true]? = some blk) (N : Numbers)
    (E : ℕ → S → Bool) (z : ProofFile.InstPub) (ft : ℕ) {s s' : S}
    (hreach : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (k3K 24 true) (z, s))
    (hx : IM.XK N IM.linksW IM.placesW E (k3K 24 true) s = true)
    (hO : k3OnOutAt (At.X Zp) 24 false s = true) (hL : k3LeftOnItemAt (At.X Zp) 24 s)
    (hy : IM.Yes ft blk s s') (m k : ℕ) (ρ : String)
    (ho : Item.forms m k ρ ∈ IM.openAt IM.linksW IM.placesW (k3K 24 true))
    (ho' : Item.forms m k ρ ∈ IM.openAt IM.linksW IM.placesW (k3K 24 true + 1)) :
    ∀ p ∈ h.𝔇.runs m k ρ, Fwd (h.𝔇.Rd m) p.1 p.2 s s' := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hr' : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 345 (z, s) := hreach
  have kk := heardAt_345 h.scope h.reads O h.laid.planOk hr'
  rw [O.W] at kk
  exact k3_digits_readers_out h hb N E ft hx hO hL kk hy m k ρ ho ho'

end P5J

#print axioms P5J.k03_readers_out_runs
#print axioms P5J.k03_readers_out_items
#print axioms P5J.outsOpen_full
#print axioms P5J.outsOpen_control
#print axioms P5J.outsOpen_control2
#print axioms P5J.outsOpen_six
#print axioms P5J.outsOpenB_def
#print axioms P5J.open_cut
#print axioms P5J.k3_digits_readers_out
#print axioms P5J.k3_digits_readers_out_below
