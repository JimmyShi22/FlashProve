-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K03ReadersHeadLay.lean: the kind "lookup" (K3): what a segment's readers answer in front
of the lookup on the digits they answer behind it: at the twelve layers' segments, under the
library's hypothesis `AtMgA`. Conditional: under two hypotheses on the lookup on the calls that the
asked form did not name. No string of a file stands in any hypothesis beyond `AtMgA`'s own letters.
One closed test with code, one definition of a list and eight theorems: four by the kernel's
evaluation (two of them negative tests), the others compositions of the library's theorems.

Terms. lean/GLOSSARY.md. In this file: `h` is a value of the structure `AtMgA`
(Johnson/P5J/MgAtAll.lean); the step is an accepting step of the chain's own sub-protocol at the
border k3K l true, in the names of the files under Johnson/IMR/ (`IM.Yes`,
Johnson/IMR/HandsDef.lean); `Fwd Rd piece run s s'` says: what the reader answers at s it answers at
s' (Johnson/Desc/Reads/FormsPass.lean): where the reader is silent at s it says nothing. "The asked
form" is the statement as written for the files under
Johnson/Desc/ProofFile/Honest/Thread/, for whose use this theorem is meant.

What is shown.
  `k03_yes_stepRel`: the bridge, at all 25 segments: at the border k3K l true the kind's own
    constant is there and passes its test on the plan, and an accepting step of the chain's
    sub-protocol is a yes of the constant's decision. (That the chain's sub-protocol is that
    constant, alone, at its address, is used in the proof; the statement does not say it.) By
    `IM.k3_of`, `IM.hear_at_flat`, `IM.flatIx_scope`, `IM.plan_alone` (Johnson/IMR/) and
    `yes_alone_steps` (Johnson/LPFK9R/TreesRideK3.lean).
  `k03_readers_lay_runs`: at the layers' segment 2 g five runs go forward over the step: (1,
    "objects"), (1, "guests"), (2, "front"), (2, "back"), (4, "K8.equations").
  `k03_readers_lay_items`: so every run of the five items of the written list (`earlyOf .layers`,
    Johnson/Desc/Sound/MgAt/K3RidesDigFwd.lean). The runs are not one an item: "objects" has two,
    "planes" none, "join" none, "own" two, "small" one (`runs_layers`,
    Johnson/Desc/Sound/MgAt/Runs.lean): at "planes" and "join", 24 of the 60 pairs, the conclusion
    is true of nothing, by the table.
  `laysOpenB`, `laysOpen_full`, `laysOpen_control`, `laysOpen_control2`: at each of the twelve
    borders: a sentence forms that is open in front and behind is of that segment and stands in the
    written list: by the kernel's evaluation, over the form of the table in the files under
    Johnson/IMR/. With an empty list the test says no, and with the neighbour's number for the
    segment's: each of the two shows that at one border at least some sentence is tried.
  `ridersAt`, `laysOpen_five`: the sentences forms that are open in front and behind a border; at
    each of the twelve borders there are five: by the kernel's evaluation.
  `k3_digits_readers_lay`: the last theorem. Its conclusion is the asked form's to the letter, and
    so are nine of its binders at l := 2 g (`h`, the sub-protocol at the border, z, ft, "reached",
    the step, the item, "open in front", "open behind"). Three hypotheses of the asked form are not
    there, two others are: see the next paragraph.

Hypotheses that remain.
  `h`: the library's hypothesis `AtMgA`.
  `hl` (in `k03_yes_stepRel`), `hg`: the segment's number: l < 25; g < 12, the segment being 2 g.
  `hb`: blk is the chain's sub-protocol at the border.
  `hy`: the step: blk accepts from s to s' (`IM.Yes`).
  `hreach`: the state in front is reached (the bare `Reach`: no string).
  `hO`, `hL`: two facts on the lookup on the calls of the same segment, in the kind's own terms:
    hO : k3OnOutAt X (2 g) false s = true: a Bool (Johnson/Desc/First/Look/K3BoolsAt.lean);
    hL : k3LeftOnItemAt X (2 g) s: a sentence on the state
      (Johnson/Desc/First/Look/K3LeftItem.lean).
  `hin`: (in `k03_readers_lay_items`) the item stands in the written list.
  `ho`, `ho'`: (in `k3_digits_readers_lay`) the sentence forms is open in front of the border, and
    behind it.
`hO` and `hL` are used for one thing: the window of the sumcheck over the leaves ends at or below
the ledger's next slot (`hwin_of_onOut`, Johnson/Top/H/Keep/CallersStay.lean); the other two windows
come of the bare reach (`wins_reached`, Johnson/Road/K4/InT/WinsReached.lean). Nothing is asked of
the state behind but the step. Not used, and so not asked: "no mark in front"; the Boolean tests at
the border; the test on the samples.

Who shows `hO` and `hL`. They are the composed meaning's own two public items at that border. By the
kernel's evaluation, at all 25 segments (`planesFront_mgMore`,
Johnson/Desc/Sound/MgAt/K3DigitsPlanesIt.lean): Pub.lookOut l (IM.k3Place l false).piece stands
among the items whose test holds in front of the digits' place, and Pub.leftOn l among those whose
sentence holds there. At mgAll the first's test is `hO`'s left side and the second's sentence is
`hL` (the fields lookOut and pLeftOn of `k3At_mgAll`). The library's `callsItems_front_dig`
(Johnson/Desc/Sound/MgAt/K3DigitsStaysBelow.lean) takes the two out of the promise with the files'
strings in just this way, and uses "no mark in front" for it: whoever draws `hO` and `hL` from a
promise will need that hypothesis there, though no theorem of this file asks it.

How the proof goes. It follows the library's `fwd_step_layers`
(Johnson/Desc/Sound/MgAt/K3RidesDigFwd.lean) and `hOwn_of_below` (K3DigitsStaysBelow.lean) step by
step, with what each takes from the promise in its place: "the ledger is there and sized" from
`wins_reached`, where the library's proof calls `led_mgAll`; the test on the plan from
`IM.plan_alone`, where the library's composition took it from the filling's three equations.

Options. `maxRecDepth` is raised to 40000 for the file and to 1000000 in front of four theorems; the
file is one `noncomputable section`. These raise limits on Lean's own work or switch off a check on
a notation's names: none loosens a check on a proof.

Limits. Compositions. `h` is a hypothesis. An instance of it at each of the two named sets of public
files stands in the library's side files: `headMember_zFull` (AtFullSide/Top/HeadMemberAtFull.lean)
and `headMember_zGap` (AtFullSide/Top/HeadMemberAtGap.lean). No state is
shown at which the hypotheses hold together. The layers' twelve segments alone. At OnBytes.secondHashFunction.
The full size alone. Of the files composed here the statements that are
called and the two proofs named were read, no more.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.P5J.K03OwnFwdLayAt
import Johnson.LPFK9R.TreesRideK3
import Johnson.IMR.PlanAt
import Johnson.IMR.FlatScope
import Johnson.IMR.WrittenList
import Johnson.IMR.HandsDef

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open Inst.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit Link Block)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item runsOf)
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.K9 (statesOfLink holesAt smallReader readersOfLink)
open VerifiableInference.Reads.Pass (Fwd)
open OnBytes.Road.K4.InT (StatesAt k4_runSame_below)
open Johnson.Desc.First.Walk.Tied (Reach)

local notation "FS" => VerifiableInference.Desc.First.S

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **The bridge, at all 25 segments.** -/
theorem k03_yes_stepRel (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {l : ℕ} (hl : l < 25)
    {blk : Block FS ProofFile.Cl} (hb : cF.blocksInOrder[k3K l true]? = some blk) :
    ∃ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l true = some b' ∧ b'.planOk = true ∧
      ∀ ft s s', IM.Yes ft blk s s' → StepRel b' s s' := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b, b', h1, h2, h3, h4⟩ := IM.k3_of h.scope h.reads O l hl true
  have hf : cF.blocksInOrder[k3K l true]? = some b := by
    have k := IM.hear_at_flat h1 h2
    rwa [IM.flatIx_scope h.scope h.reads O (by omega) (IM.k3Ix l true)] at k
  obtain rfl : blk = b := Option.some.inj (hb.symm.trans hf)
  rw [O.W] at h3
  exact ⟨b', h3, IM.plan_alone O h.laid.planOk h1 h2 h4, fun ft s s' hy =>
    VerifiableInference.Desc.LinkJoin.yes_alone_steps (R := StepRel b') h4
      (fun s rs gs s' hd => ⟨rs, gs, hd⟩) hy⟩

/-- **The five runs at a layers' segment.** -/
theorem k03_readers_lay_runs (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {g : ℕ} (hg : g < 12)
    {blk : Block FS ProofFile.Cl} (hb : cF.blocksInOrder[k3K (2 * g) true]? = some blk) (z : ProofFile.InstPub)
    (ft : ℕ) {s s' : FS}
    (hreach : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (k3K (2 * g) true) (z, s))
    (hO : k3OnOutAt (At.X Zp) (2 * g) false s = true) (hL : k3LeftOnItemAt (At.X Zp) (2 * g) s)
    (hy : IM.Yes ft blk s s') :
    ∀ p ∈ [(1, "objects"), (1, "guests"), (2, "front"), (2, "back"), (4, "K8.equations")],
      Fwd (h.𝔇.Rd (2 * g)) p.1 p.2 s s' := by
  intro p hp
  have hl : 2 * g < 25 := by omega
  obtain ⟨b', hb', hOk, hstep⟩ := k03_yes_stepRel h hl hb
  obtain ⟨rs, gs, hd⟩ := hstep ft s s' hy
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  -- what is reached in front
  have hr' := hreach
  rw [k03_dig_number g hg] at hr'
  obtain ⟨al, o, hal, ho, hSz, w1, w3, hT⟩ :=
    OnBytes.Road.K4.InT.wins_reached h.scope h.reads O h.laid.planOk hg hr'
  have hF : s.fork? = some al.F := by simp [VerifiableInference.Desc.First.S.fork?, hal]
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
  -- across the whole acceptance at the seat
  have hpc := k03_pieceAt_dig h.toAtMg (2 * g)
  obtain ⟨G, Q⟩ := k3_digits_step_pass K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp)
    Zp.first.codes Zp.first.shape (IM.k3Place (2 * g) true) b' hb' hOk (2 * g) rfl hpc s s' rs gs hd
    hF hSz
  obtain ⟨-, -, -, -, hLk, -, -⟩ := k3_digits_step_leaves K3Lot.ofForm (K3Lot.readersAt (At.X Zp))
    (At.X Zp) Zp.first.codes Zp.first.shape (IM.k3Place (2 * g) true) b' hb' hOk (2 * g) rfl hpc s
    s' rs gs hd
  -- the link, its readers, its holes
  have h24 : headLink (At.X Zp) = 24 := headLink_in_scope h.scope h.reads h.pubOne
  have hix : IM.k3Ix (2 * g) false = 1 := by
    unfold IM.k3Ix
    simp [show 2 * g ≠ 24 by omega]
  obtain ⟨Lk, hLk0, hOb⟩ := k03_objects_raw h.scope h.reads O (2 * g) hl false
  obtain ⟨Lk', hLk', hGu⟩ := k03_guests_raw h.scope h.reads O (2 * g) hl false
  obtain rfl : Lk = Lk' := Option.some.inj (hLk0.symm.trans hLk')
  rw [hix] at hOb hGu
  have hne : ¬ ((2 * g == 24) = true) := by
    rw [beq_iff_eq]
    omega
  have hsil : ∀ (b : ℕ) (n : String) (t : FS),
      (holesAt (At.X Zp) (headLink (At.X Zp)) (2 * g) Lk).silent b n t = none := by
    intro b n t
    unfold holesAt
    rw [h24]
    dsimp only
    rw [if_neg hne]
  have hRd : h.𝔇.Rd (2 * g) =
      readersOfLink (holesAt (At.X Zp) (headLink (At.X Zp)) (2 * g) Lk) Lk :=
    k03_hlink h (2 * g) Lk hLk0
  rw [hRd]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact objects_fwd _ Lk 1 (VerifiableInference.Desc.K3.seatCalls K3Lot.ofForm) k03_atS2_calls Q
      hLk (hsil 1 "objects" s)
      (fun n r e => (Prod.mk.inj (Option.some.inj (hOb.symm.trans e))).2.symm)
  · exact guests_fwd _ Lk 1 Q (hsil 1 "guests" s)
      (fun n r e => (Prod.mk.inj (Option.some.inj (hGu.symm.trans e))).2.symm)
  all_goals first
    | (exact small_fwd _ Lk 4 (fun R hR => by
        show smallReader s' = some R
        rw [k3_digits_step_smallReader K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp)
          Zp.first.codes Zp.first.shape (IM.k3Place (2 * g) true) b' hb' hOk (2 * g) rfl hpc s s' rs
          gs hd]
        exact hR))
    | skip
  all_goals
    have hW := windows_of_leaves hdc hal hOo hLf
      (fun o' ho' => by
        obtain rfl : o = o' := Option.some.inj (ho.symm.trans ho')
        exact hT)
      (fun o' ho' => by
        obtain rfl : o = o' := Option.some.inj (ho.symm.trans ho')
        exact ⟨w1, w3⟩)
    have K := k4StaysBelow_of_digits K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp)
      Zp.first.codes Zp.first.shape (IM.k3Place (2 * g) true) b' hb' hOk (2 * g) rfl hpc s s' rs gs
      hd hal hSz hW
    obtain ⟨pK, hSt⟩ := k03_states_lay h hg Lk hLk0
  · exact link_fwd _ Lk 2 (by decide) (hsil 2 "front" s) fun nm r hfr => by
      obtain ⟨y, runC, hy1, hC, e1⟩ := hSt "front" (Or.inl rfl) s
      obtain ⟨y', runC', hy', hC', e2⟩ := hSt "front" (Or.inl rfl) s'
      obtain rfl : y = (nm, r) := Option.some.inj (hy1.symm.trans hfr)
      obtain rfl : y' = (nm, r) := Option.some.inj (hy'.symm.trans hfr)
      obtain rfl : runC' = runC := Option.some.inj (hC'.symm.trans hC)
      exact runSame_congr e1 e2 (k4_runSame_below (Or.inl rfl) hC K)
  · exact link_fwd _ Lk 2 (by decide) (hsil 2 "back" s) fun nm r hfr => by
      obtain ⟨y, runC, hy1, hC, e1⟩ := hSt "back" (Or.inr rfl) s
      obtain ⟨y', runC', hy', hC', e2⟩ := hSt "back" (Or.inr rfl) s'
      obtain rfl : y = (nm, r) := Option.some.inj (hy1.symm.trans hfr)
      obtain rfl : y' = (nm, r) := Option.some.inj (hy'.symm.trans hfr)
      obtain rfl : runC' = runC := Option.some.inj (hC'.symm.trans hC)
      exact runSame_congr e1 e2 (k4_runSame_below (Or.inr rfl) hC K)

/-- **Every run of the five items of the written list.** -/
theorem k03_readers_lay_items (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {g : ℕ} (hg : g < 12)
    {blk : Block FS ProofFile.Cl} (hb : cF.blocksInOrder[k3K (2 * g) true]? = some blk) (z : ProofFile.InstPub)
    (ft : ℕ) {s s' : FS}
    (hreach : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (k3K (2 * g) true) (z, s))
    (hO : k3OnOutAt (At.X Zp) (2 * g) false s = true) (hL : k3LeftOnItemAt (At.X Zp) (2 * g) s)
    (hy : IM.Yes ft blk s s') (k : ℕ) (ρ : String) (hin : (k, ρ) ∈ earlyOf .layers) :
    ∀ p ∈ h.𝔇.runs (2 * g) k ρ, Fwd (h.𝔇.Rd (2 * g)) p.1 p.2 s s' := by
  intro p hp
  have hsub : linksFull[2 * g]? = some ModelPart.layers := by
    have h0 := List.all_eq_true.1 linksLayFull g (List.mem_range.2 hg)
    simpa using h0
  have e : h.𝔇.runs (2 * g) k ρ = runsOf .layers k ρ :=
    runsAt_of linksFull (2 * g) .layers hsub k ρ
  rw [e] at hp
  have H := k03_readers_lay_runs h hg hb z ft hreach hO hL hy p
  simp only [earlyOf, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hin
  rcases hin with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [runs_layers.1] at hp
    exact H (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp ⊢
      rcases hp with rfl | rfl <;> simp)
  · rw [runs_layers.2.2.2.2.1] at hp
    cases hp
  · rw [runs_layers.2.2.2.2.2] at hp
    cases hp
  · rw [runs_layers.2.1] at hp
    exact H (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp ⊢
      rcases hp with rfl | rfl <;> simp)
  · rw [runs_layers.2.2.1] at hp
    exact H (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp ⊢
      subst hp
      simp)

/-- At each of the twelve borders: a sentence forms that is open in front and behind bears the
number 2 g + off and stands in the list E. -/
def laysOpenB (E : List (ℕ × String)) (off : ℕ) : Bool :=
  (List.range 12).all fun g =>
    (IM.openAt IM.linksW IM.placesW (k3K (2 * g) true)).all fun i =>
      match i with
      | .forms m k ρ =>
        !((IM.openAt IM.linksW IM.placesW (k3K (2 * g) true + 1)).contains (.forms m k ρ)) ||
          (m == 2 * g + off && E.contains (k, ρ))
      | _ => true

set_option maxRecDepth 1000000 in
theorem laysOpen_full : laysOpenB (earlyOf .layers) 0 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **A negative test**: with an empty list the test says no. -/
theorem laysOpen_control : laysOpenB [] 0 = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **A second negative test**: with the neighbour's number for the segment's it says no. -/
theorem laysOpen_control2 : laysOpenB (earlyOf .layers) 1 = false := by decide +kernel

/-- The sentences forms that are open in front of border k and behind it. The library has two
definitions of this short name in other senses (Johnson/Desc/First/RidersBare.lean;
Johnson/Desc/First/Link/Law/FifthTieRiders.lean). -/
def ridersAt (k : ℕ) : List Item :=
  (IM.openAt IM.linksW IM.placesW k).filter fun i =>
    (match i with
      | .forms _ _ _ => true
      | _ => false) && (IM.openAt IM.linksW IM.placesW (k + 1)).contains i

set_option maxRecDepth 1000000 in
/-- At each of the twelve borders there are five. -/
theorem laysOpen_five :
    ((List.range 12).all fun g => (ridersAt (k3K (2 * g) true)).length == 5) = true := by
  decide +kernel

/-- **The last theorem, at l := 2 g**: "reached"; the two facts on the lookup on the calls; the
step. -/
theorem k3_digits_readers_lay (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {g : ℕ} (hg : g < 12)
    {blk : Block FS ProofFile.Cl} (hb : cF.blocksInOrder[k3K (2 * g) true]? = some blk) (z : ProofFile.InstPub)
    (ft : ℕ) {s s' : FS}
    (hreach : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (k3K (2 * g) true) (z, s))
    (hO : k3OnOutAt (At.X Zp) (2 * g) false s = true) (hL : k3LeftOnItemAt (At.X Zp) (2 * g) s)
    (hy : IM.Yes ft blk s s') (m k : ℕ) (ρ : String)
    (ho : Item.forms m k ρ ∈ IM.openAt IM.linksW IM.placesW (k3K (2 * g) true))
    (ho' : Item.forms m k ρ ∈ IM.openAt IM.linksW IM.placesW (k3K (2 * g) true + 1)) :
    ∀ p ∈ h.𝔇.runs m k ρ, Fwd (h.𝔇.Rd m) p.1 p.2 s s' := by
  have h1 := List.all_eq_true.1 laysOpen_full g (List.mem_range.2 hg)
  have h2 : (!((IM.openAt IM.linksW IM.placesW (k3K (2 * g) true + 1)).contains
      (Item.forms m k ρ)) || (m == 2 * g + 0 && (earlyOf .layers).contains (k, ρ))) = true :=
    List.all_eq_true.1 h1 _ ho
  rw [List.contains_iff_mem.2 ho'] at h2
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq, Nat.add_zero] at h2
  obtain ⟨rfl, h3⟩ := h2
  exact k03_readers_lay_items h hg hb z ft hreach hO hL hy k ρ (List.contains_iff_mem.1 h3)

end P5J

#print axioms P5J.k03_yes_stepRel
#print axioms P5J.k03_readers_lay_runs
#print axioms P5J.k03_readers_lay_items
#print axioms P5J.laysOpen_full
#print axioms P5J.laysOpen_control
#print axioms P5J.laysOpen_control2
#print axioms P5J.laysOpen_five
#print axioms P5J.k3_digits_readers_lay
