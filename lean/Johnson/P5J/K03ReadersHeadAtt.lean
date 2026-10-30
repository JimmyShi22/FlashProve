-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K03ReadersHeadAtt.lean: the kind "lookup" (K3): what a segment's readers answer in front
of the lookup on the digits they answer behind it: at the twelve attention segments, under the
library's hypothesis `AtMgA`. Conditional: under two hypotheses on the lookup on the calls that the
asked form did not name. No string of a file stands in any hypothesis beyond `AtMgA`'s own letters.
After Johnson/P5J/K03ReadersHeadLay.lean (the layers' twelve). One closed test with code and eleven
theorems: five by the kernel's evaluation (two of them negative tests), the others compositions of
the library's theorems.

Terms. lean/GLOSSARY.md; the head of Johnson/P5J/K03ReadersHeadLay.lean.

What is shown.
  `linksW_full`, `placesW_full`: the written lists of the files under Johnson/IMR/ (`IM.linksW`,
    `IM.placesW`) are the table's: the first by the kernel's evaluation, the second by unfolding
    over the first. Both equations stand in the library under other namespaces already: they are
    proved anew here.
  `k03_stand_of_shape`: where the table's test on the state's shape holds at the border in front of
    a segment's digits, the state stands in a link of the segment's sort: the text of the library's
    `k03_stand_dig` (Johnson/P5J/K03RidesDigAt2.lean) behind its first two lines.
  `k03_onOut_ledger`: where the two facts on the lookup on the calls hold, at a place of a lookup on
    calls, a ledger is open and has its sizes.
  `k03_readers_att_runs`: at attention's segment 2 g + 1 eight runs go forward over the step: (1,
    "objects"), (1, "guests"), (1, "planes"), (2, "join"), (2, "first"), (2, "keys"), (2, "second"),
    (4, "K8.equations").
  `k03_readers_att_items`: so every run of the five items of `earlyOf .attention`: "objects" has two
    runs, "planes" one, "join" one, "own" three, "small" one (`runs_attention`,
    Johnson/Desc/Sound/MgAt/Runs.lean).
  `attsOpenB`, `attsOpen_full`, `attsOpen_control`, `attsOpen_control2`: at each of the twelve
    borders: a sentence forms that is open in front and behind is of that segment and stands in the
    written list: by the kernel's evaluation. With an empty list the test says no, and with the
    neighbour's number for the segment's: each of the two shows that at one border at least some
    sentence is tried.
  `attsOpen_five`: at each of the twelve borders five sentences forms are open in front and behind:
    by the kernel's evaluation.
  `k3_digits_readers_att`: the last theorem. Its conclusion is the asked form's to the letter, and
    so are its binders on `h`, the sub-protocol at the border, ft, the step, the item, "open in
    front" and "open behind", at l := 2 g + 1.

Hypotheses that remain.
  `h`: the library's hypothesis `AtMgA`.
  `hg`: g < 12, the segment being 2 g + 1. `hb`: blk is the chain's sub-protocol at the border.
  `hy`: the step: blk accepts from s to s' (`IM.Yes`).
  `hx`: (in `k3_digits_readers_att`) the Boolean tests at the border (`IM.XK`, at any numbers N and
    any further tests E): of its five parts the test on the shape alone is used. `hsh`: (in the two
    theorems on the runs) that test on the shape by itself.
  `hO`, `hL`: the two facts on the lookup on the calls of the same segment, as in
    Johnson/P5J/K03ReadersHeadLay.lean: used for the window of the sumcheck over the leaves and for
    "a ledger is open and has its sizes".
  `hin`: (in `k03_readers_att_items`) the item stands in the written list.
  `ho`, `ho'`: (in `k3_digits_readers_att`) the sentence forms is open in front of the border, and
    behind it.
  In `k03_stand_of_shape`: `hl`, `hsub`, `hs`: l < 25; the segment's sort; the table's test on the
    shape holds. In `k03_onOut_ledger`: `hdc`, `hO`, `hL`: the place is that of a lookup on calls;
    the two facts at that place.
Nothing is asked of the state behind but the step. Not used, and so not asked: "reached"; "no mark
in front"; the test on the samples.

Who shows `hO` and `hL`. They are the composed meaning's own two public items at that border. By the
kernel's evaluation, at all 25 segments (`planesFront_mgMore`,
Johnson/Desc/Sound/MgAt/K3DigitsPlanesIt.lean): Pub.lookOut l (IM.k3Place l false).piece stands
among the items whose test holds in front of the digits' place, and Pub.leftOn l among those whose
sentence holds there. At mgAll the first's test is `hO`'s left side and the second's sentence is
`hL` (the fields lookOut and pLeftOn of `k3At_mgAll`). The library's `callsItems_front_dig`
(Johnson/Desc/Sound/MgAt/K3DigitsStaysBelow.lean) takes the two out of the promise with the files'
strings in just this way, and uses "no mark in front" for it: whoever draws `hO` and `hL` from a
promise will need that hypothesis there, though no theorem of this file asks it.

How the proof goes. It follows the library's `fwd_step_att`
(Johnson/Desc/Sound/MgAt/K3RidesDigFwd2.lean) and `k03_fwd_att_front`
(Johnson/P5J/K03OwnFwdAttAt.lean) step by step, with what each takes from the promise with the
files' strings in its place.

Options. `maxRecDepth` is raised to 100000 for the file and to 1000000 in front of five theorems;
`maxHeartbeats` to 4000000 in front of one theorem; the file is one `noncomputable section`. These
raise limits on Lean's own work or switch off a check on a notation's names: none loosens a check on
a proof.

Limits. Compositions. `h` is a hypothesis. An instance of it at each of the two named sets of public
files stands in the library's side files: `headMember_zFull` (AtFullSide/Top/HeadMemberAtFull.lean)
and `headMember_zGap` (AtFullSide/Top/HeadMemberAtGap.lean). No state is
shown at which the hypotheses hold together. Attention's twelve segments alone. At OnBytes.secondHashFunction.
The full size alone. Of the files composed here the statements that are
called and the proofs of the two theorems named were read, no more.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.P5J.K03ReadersHeadLay
import Johnson.P5J.K03OwnFwdAttAt

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
open VerifiableInference.Desc.First (ModelPart Item runsOf shapeAt standOf standAt Numbers)
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.K9 (statesOfLink holesAt smallReader readersOfLink)
open VerifiableInference.Desc.First.Att.P (runsN K05_states_raw_of_open readersOfO keysOfO)
open VerifiableInference.Reads.Pass (Fwd)

local notation "FS" => VerifiableInference.Desc.First.S
local notation "PS" => VerifiableInference.Desc.First.flatPlacesOf linksFull true

set_option maxRecDepth 1000000 in
/-- The written row of sorts is the table's. -/
theorem linksW_full : IM.linksW = linksFull := by decide +kernel

/-- The written list of places is the table's. -/
theorem placesW_full : IM.placesW = PS := by
  unfold IM.placesW
  rw [linksW_full]

/-- **Where the state stands in front of a segment's digits**, from the table's test on the
shape. `ProofFile.Honest.K3.Law.Total.dig_stand` (Honest/K3/Law/Total/DigitsFormsFour.lean) has the same
statement; neither calls the other. -/
theorem k03_stand_of_shape {l : ℕ} (hl : l < 25) {sub : ModelPart} (hsub : linksFull[l]? = some sub)
    {s : FS} (hs : shapeAt linksFull (PS)[k3K l true]? s = true) : standOf s = .link sub := by
  rw [K3Lot.k03_at_full l hl true] at hs
  unfold shapeAt at hs
  simp only [Bool.and_eq_true, beq_iff_eq] at hs
  rw [hs.1.1]
  unfold standAt
  show (if (IM.k3Place l true).piece ≤ 1 then _ else _) = _
  have hp : ¬ (IM.k3Place l true).piece ≤ 1 := by
    show ¬ (if (true : Bool) = true then 6 else 1) + (if l = 24 then 1 else 0) + 1 ≤ 1
    simp
  rw [if_neg hp]
  show (if ((linksFull[l]?).getD .layers == .head && (IM.k3Place l true).piece == 2) = true then _
    else _) = _
  have hp2 : ((IM.k3Place l true).piece == 2) = false := by
    show ((if (true : Bool) = true then 6 else 1) + (if l = 24 then 1 else 0) + 1 == 2) = false
    by_cases e : l = 24 <;> simp [e]
  rw [hp2, Bool.and_false, hsub]
  rfl

/-- **Where the two facts on the lookup on the calls hold, a ledger is open and has its sizes.**
Conditional besides on hdc: the place is that of a lookup on calls. -/
theorem k03_onOut_ledger {pc : VerifiableInference.Desc.First.Look.P} (hdc : pc.digits = false)
    {s : FS} (hO : VerifiableInference.Desc.K3.k3OnOut pc s = true) (hL : k3LeftOnItem pc s) :
    ∃ F, s.fork? = some F ∧ OnBytes.PscRun.Sized F := by
  obtain ⟨⟨h, hs, F0, F', G, g0, rs, _, _, K, hg0, _, _, _⟩, _⟩ := hL
  have hH : VerifiableInference.Desc.K3.heardAt pc.digits s = some g0 := by
    rw [hdc]
    exact hg0
  cases hF : s.fork? with
  | none =>
    unfold VerifiableInference.Desc.K3.k3OnOut at hO
    rw [hs, hH, hF] at hO
    cases hO
  | some F =>
    unfold VerifiableInference.Desc.K3.k3OnOut at hO
    rw [hs, hH, hF] at hO
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hO
    obtain ⟨⟨⟨⟨⟨⟨⟨_, _⟩, c8⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hO
    simp only [VerifiableInference.Desc.K3.sizedB, Bool.and_eq_true, beq_iff_eq] at c8
    exact ⟨F, rfl, c8.1.1, c8.1.2, c8.2⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

set_option maxHeartbeats 4000000 in
/-- **The eight runs at an attention segment.** -/
theorem k03_readers_att_runs (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {g : ℕ} (hg : g < 12)
    {blk : Block FS ProofFile.Cl} (hb : cF.blocksInOrder[k3K (2 * g + 1) true]? = some blk) (ft : ℕ) {s s' : FS}
    (hsh : shapeAt linksFull (PS)[k3K (2 * g + 1) true]? s = true)
    (hO : k3OnOutAt (At.X Zp) (2 * g + 1) false s = true)
    (hL : k3LeftOnItemAt (At.X Zp) (2 * g + 1) s) (hy : IM.Yes ft blk s s') :
    ∀ p ∈ [(1, "objects"), (1, "guests"), (1, "planes"), (2, "join"), (2, "first"), (2, "keys"),
        (2, "second"), (4, "K8.equations")],
      Fwd (h.𝔇.Rd (2 * g + 1)) p.1 p.2 s s' := by
  intro p hp
  have hl : 2 * g + 1 < 25 := by omega
  obtain ⟨b', hb', hOk, hstep⟩ := k03_yes_stepRel h hl hb
  obtain ⟨rs, gs, hd⟩ := hstep ft s s' hy
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hW : Bs.G₀.W = At.X Zp := O.W
  have hsub : linksFull[2 * g + 1]? = some ModelPart.attention := by
    have h0 := List.all_eq_true.1 linksAttFull g (List.mem_range.2 hg)
    simpa using h0
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
  obtain ⟨w₀, hw⟩ := VerifiableInference.Desc.K1.here_att_of_stand (k03_stand_of_shape hl hsub hsh)
  have eF : w₀.F = F := by
    have h0 := hF
    simp only [VerifiableInference.Desc.First.S.fork?, hw] at h0
    exact Option.some.inj h0
  have hSw : OnBytes.PscRun.Sized w₀.F := by rw [eF]; exact hSz
  -- across the whole acceptance at the seat
  have hpc := k03_pieceAt_dig h.toAtMg (2 * g + 1)
  obtain ⟨G, Q⟩ := k3_digits_step_pass K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp)
    Zp.first.codes Zp.first.shape (IM.k3Place (2 * g + 1) true) b' hb' hOk (2 * g + 1) rfl hpc s s'
    rs gs hd hF hSz
  obtain ⟨-, -, -, -, hLk, -, -⟩ := k3_digits_step_leaves K3Lot.ofForm (K3Lot.readersAt (At.X Zp))
    (At.X Zp) Zp.first.codes Zp.first.shape (IM.k3Place (2 * g + 1) true) b' hb' hOk (2 * g + 1) rfl
    hpc s s' rs gs hd
  -- the plan, the link, its readers, its holes
  have h24 : headLink (At.X Zp) = 24 := headLink_in_scope h.scope h.reads h.pubOne
  obtain ⟨hp4, hN, -, -⟩ := _root_.Meaning.scope_plans h.scope h.reads h.pubOne
  obtain ⟨A, hA⟩ := H2K5.Door.planAt_all h hg
  have hix : IM.k3Ix (2 * g + 1) false = 1 := by
    unfold IM.k3Ix
    simp [show 2 * g + 1 ≠ 24 by omega]
  obtain ⟨Lk, hLk0, hOb⟩ := k03_objects_raw h.scope h.reads O (2 * g + 1) hl false
  obtain ⟨L2, e2, hGu⟩ := k03_guests_raw h.scope h.reads O (2 * g + 1) hl false
  obtain ⟨L3, pp, e3, -, hPl⟩ := k03_planes_raw h.scope h.reads O (2 * g + 1) hl (readersOfO A)
    (by
      rw [hW]
      exact H2K5.Door.readersAt_att hp4 hA)
  obtain ⟨L4, e4, hSt⟩ := K05_states_raw_of_open O (by rw [hW]; exact hp4)
    (by rw [hW]; exact hN ▸ hg) (by rw [hW]; exact hA)
  obtain rfl : Lk = L2 := Option.some.inj (hLk0.symm.trans e2)
  obtain rfl : Lk = L3 := Option.some.inj (hLk0.symm.trans e3)
  obtain rfl : Lk = L4 := Option.some.inj (hLk0.symm.trans e4)
  rw [hix] at hOb hGu hPl
  have hsil : ∀ (b : ℕ) (n : String) (t : FS),
      (holesAt (At.X Zp) (headLink (At.X Zp)) (2 * g + 1) Lk).silent b n t = none := by
    intro b n t
    have hne : ¬ ((2 * g + 1 == 24) = true) := by
      rw [beq_iff_eq]
      omega
    unfold holesAt
    rw [h24]
    dsimp only
    rw [if_neg hne]
  -- the calling kind's own runs
  obtain ⟨w, hw', hg', h5, HS, hwd⟩ := k3_digits_step_attSame K3Lot.ofForm
    (K3Lot.readersAt (At.X Zp)) (At.X Zp) Zp.first.codes Zp.first.shape
    (IM.k3Place (2 * g + 1) true) b' hb' hOk (2 * g + 1) rfl hpc s s' rs gs hd hw hSw
  have hsame := runsN_same A hw hw' hg' h5 HS hwd hF Q.behind Q.trees
  have key : ∀ name : String, name ≠ "join" → (name == "K8.equations") = false →
      Fwd (readersOfLink (holesAt (At.X Zp) (headLink (At.X Zp)) (2 * g + 1) Lk) Lk) 2 name s
        s' := by
    intro name hj hn
    refine link_fwd _ Lk 2 hn (hsil 2 name s) fun nm r hfr => ?_
    rw [hSt] at hfr
    have hym := List.mem_of_find?_eq_some hfr
    have hyn : nm = name := by simpa using List.find?_some hfr
    exact hsame (nm, r) hym (hyn ▸ hj)
  have hRd : h.𝔇.Rd (2 * g + 1) =
      readersOfLink (holesAt (At.X Zp) (headLink (At.X Zp)) (2 * g + 1) Lk) Lk :=
    k03_hlink h (2 * g + 1) Lk hLk0
  rw [hRd]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact objects_fwd _ Lk 1 (VerifiableInference.Desc.K3.seatCalls K3Lot.ofForm) k03_atS2_calls Q
      hLk (hsil 1 "objects" s)
      (fun n r e => (Prod.mk.inj (Option.some.inj (hOb.symm.trans e))).2.symm)
  · exact guests_fwd _ Lk 1 Q (hsil 1 "guests" s)
      (fun n r e => (Prod.mk.inj (Option.some.inj (hGu.symm.trans e))).2.symm)
  · exact planes_fwd' _ Lk 1 (VerifiableInference.Desc.K3.seatCalls K3Lot.ofForm) k03_atS2_calls Q
      hLk pp.lm (readersOfO A)
      (k3_digits_step_attReaders K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp) Zp.first.codes
        Zp.first.shape (IM.k3Place (2 * g + 1) true) b' hb' hOk (2 * g + 1) rfl hpc s s' rs gs hd hw
        hSw A)
      (hwin_of_onOut hdc hF hOo hLf) (hsil 1 "planes" s)
      (fun n r e => (Prod.mk.inj (Option.some.inj (hPl.symm.trans e))).2.symm)
  · exact join_fwd' _ Lk 2 (VerifiableInference.Desc.K3.seatCalls K3Lot.ofForm) k03_atS2_calls Q
      hLk (keysOfO A)
      (k3_digits_step_attKeys K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp) Zp.first.codes
        Zp.first.shape (IM.k3Place (2 * g + 1) true) b' hb' hOk (2 * g + 1) rfl hpc s s' rs gs hd hw
        hSw A)
      (hsil 2 "join" s) (k03_joinFind_att h g hg A hA Lk hLk0)
  · exact key "first" (by decide) (by decide)
  · exact key "keys" (by decide) (by decide)
  · exact key "second" (by decide) (by decide)
  · exact small_fwd _ Lk 4 (fun R hR => by
      show smallReader s' = some R
      rw [k3_digits_step_smallReader K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp)
        Zp.first.codes Zp.first.shape (IM.k3Place (2 * g + 1) true) b' hb' hOk (2 * g + 1) rfl hpc s
        s' rs gs hd]
      exact hR)

/-- **Every run of the five items of the written list.** -/
theorem k03_readers_att_items (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {g : ℕ} (hg : g < 12)
    {blk : Block FS ProofFile.Cl} (hb : cF.blocksInOrder[k3K (2 * g + 1) true]? = some blk) (ft : ℕ) {s s' : FS}
    (hsh : shapeAt linksFull (PS)[k3K (2 * g + 1) true]? s = true)
    (hO : k3OnOutAt (At.X Zp) (2 * g + 1) false s = true)
    (hL : k3LeftOnItemAt (At.X Zp) (2 * g + 1) s) (hy : IM.Yes ft blk s s') (k : ℕ) (ρ : String)
    (hin : (k, ρ) ∈ earlyOf .attention) :
    ∀ p ∈ h.𝔇.runs (2 * g + 1) k ρ, Fwd (h.𝔇.Rd (2 * g + 1)) p.1 p.2 s s' := by
  intro p hp
  have hsub : linksFull[2 * g + 1]? = some ModelPart.attention := by
    have h0 := List.all_eq_true.1 linksAttFull g (List.mem_range.2 hg)
    simpa using h0
  have e : h.𝔇.runs (2 * g + 1) k ρ = runsOf .attention k ρ :=
    runsAt_of linksFull (2 * g + 1) .attention hsub k ρ
  rw [e] at hp
  have H := k03_readers_att_runs h hg hb ft hsh hO hL hy p
  simp only [earlyOf, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hin
  rcases hin with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [runs_attention.1] at hp
    exact H (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp ⊢
      rcases hp with rfl | rfl <;> simp)
  · rw [runs_attention.2.1] at hp
    exact H (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp ⊢
      subst hp
      simp)
  · rw [runs_attention.2.2.1] at hp
    exact H (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp ⊢
      subst hp
      simp)
  · rw [runs_attention.2.2.2.1] at hp
    exact H (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp ⊢
      rcases hp with rfl | rfl | rfl <;> simp)
  · rw [runs_attention.2.2.2.2.1] at hp
    exact H (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp ⊢
      subst hp
      simp)

/-- At each of the twelve borders: a sentence forms that is open in front and behind bears the
number 2 g + off and stands in the list E. -/
def attsOpenB (E : List (ℕ × String)) (off : ℕ) : Bool :=
  (List.range 12).all fun g =>
    (IM.openAt IM.linksW IM.placesW (k3K (2 * g + 1) true)).all fun i =>
      match i with
      | .forms m k ρ =>
        !((IM.openAt IM.linksW IM.placesW (k3K (2 * g + 1) true + 1)).contains (.forms m k ρ)) ||
          (m == 2 * g + off && E.contains (k, ρ))
      | _ => true

set_option maxRecDepth 1000000 in
theorem attsOpen_full : attsOpenB (earlyOf .attention) 1 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **A negative test**: with an empty list the test says no. -/
theorem attsOpen_control : attsOpenB [] 1 = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **A second negative test**: with the neighbour's number for the segment's it says no. -/
theorem attsOpen_control2 : attsOpenB (earlyOf .attention) 0 = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- At each of the twelve borders there are five. -/
theorem attsOpen_five :
    ((List.range 12).all fun g => (ridersAt (k3K (2 * g + 1) true)).length == 5) = true := by
  decide +kernel

/-- **The last theorem, at l := 2 g + 1**: the tests at the border, at any numbers and any further
tests; the two facts on the lookup on the calls; the step. -/
theorem k3_digits_readers_att (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {g : ℕ} (hg : g < 12)
    {blk : Block FS ProofFile.Cl} (hb : cF.blocksInOrder[k3K (2 * g + 1) true]? = some blk) (N : Numbers)
    (E : ℕ → FS → Bool) (ft : ℕ) {s s' : FS}
    (hx : IM.XK N IM.linksW IM.placesW E (k3K (2 * g + 1) true) s = true)
    (hO : k3OnOutAt (At.X Zp) (2 * g + 1) false s = true)
    (hL : k3LeftOnItemAt (At.X Zp) (2 * g + 1) s) (hy : IM.Yes ft blk s s') (m k : ℕ) (ρ : String)
    (ho : Item.forms m k ρ ∈ IM.openAt IM.linksW IM.placesW (k3K (2 * g + 1) true))
    (ho' : Item.forms m k ρ ∈ IM.openAt IM.linksW IM.placesW (k3K (2 * g + 1) true + 1)) :
    ∀ p ∈ h.𝔇.runs m k ρ, Fwd (h.𝔇.Rd m) p.1 p.2 s s' := by
  have hsh : shapeAt linksFull (PS)[k3K (2 * g + 1) true]? s = true := by
    have h0 := (IM.xk_parts hx).1
    rwa [linksW_full, placesW_full] at h0
  have h1 := List.all_eq_true.1 attsOpen_full g (List.mem_range.2 hg)
  have h2 : (!((IM.openAt IM.linksW IM.placesW (k3K (2 * g + 1) true + 1)).contains
      (Item.forms m k ρ)) || (m == 2 * g + 1 && (earlyOf .attention).contains (k, ρ))) = true :=
    List.all_eq_true.1 h1 _ ho
  rw [List.contains_iff_mem.2 ho'] at h2
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at h2
  obtain ⟨rfl, h3⟩ := h2
  exact k03_readers_att_items h hg hb ft hsh hO hL hy k ρ (List.contains_iff_mem.1 h3)

end P5J

#print axioms P5J.linksW_full
#print axioms P5J.placesW_full
#print axioms P5J.k03_stand_of_shape
#print axioms P5J.k03_onOut_ledger
#print axioms P5J.k03_readers_att_runs
#print axioms P5J.k03_readers_att_items
#print axioms P5J.attsOpen_full
#print axioms P5J.attsOpen_control
#print axioms P5J.attsOpen_control2
#print axioms P5J.attsOpen_five
#print axioms P5J.k3_digits_readers_att
