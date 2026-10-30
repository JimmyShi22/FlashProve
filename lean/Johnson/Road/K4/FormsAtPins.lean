-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/FormsAtPins.lean: THE LINE "forms" OF K4Lines AT THE PINNED VALUE: forms_of_means
(Johnson/Road/K4/FormsOfMeans.lean) with its letters QK, part and M filled: QK := the reference
value at a structure A : PinPlan (PinPlan.seatN, Johnson/Road/K4/K4PinsPlanes.lean; RefSeat.atRec),
part := partOf (Johnson/Road/K4/K4Pins.lean), M := the matrices unpacked from the data's symbols
(matsOfB, Johnson/Road/K4/K4PinsCellQ.lean). A GROUP THAT IS NOT THE FIRST IS MEANT (atRec); the
first group's twin: Johnson/Road/K4/FormsAtPinsFirst.lean. Of forms_of_means' five premises at an
accepting run asks stays; arrB and hM are concluded from tests and two conditions on letters; hm
from two tests and hns; X is exchanged for hSt: THREE PREMISES AT AN ACCEPTING RUN ARE LEFT: asks,
hns, hSt.

  `mask_pins`: below nV the value's mask row at the pinned part of a witness is the table's data's,
    where nV is at most the mask row's length.
  `raw_pins`: the value's raw matrices there are matsOfB at the table's data.
  `recIs_run`: behind an accepting run inside the table's promise in front, the open segment's part
    holds the public parameters' own frame, layout, book and arrays (RecIs).
  `ns_behind`: the ledger's number of slots behind an accepting run is that in front.
  `forms_pins`: THE LINE.
No new argument: recIs_at, recIs_behind, readsArray_plan, maskOne_of_plan, cellOne_of_plan and the
tests' laws (Johnson/Road/K4/Rec/); mask_dataQ_tab, raw_dataQ_tab (Johnson/Road/K4/K4PinsTab.lean);
mats_raw (Johnson/Road/K4/K4PinsIdn.lean); statedAt_of_is (Johnson/Road/K4/ArmLay.lean).
Limits. PREMISES of forms_pins, none paid here:
  E: K4Means at Mg and the data D · hRd, hruns: the data's reader and runs at segment m · hk: one
    flag of the place's parameters · hcs: A's codes are the data's.
  asks: the conclusion of asks_of_means (Johnson/Road/K4/Riders/AsksAtMeans.lean), to the letter.
  FIVE TESTS WITH CODE ON LETTERS THAT ARE MEANT AS THE PUBLIC PARAMETERS (A's D, rad, link, seatT;
    D's moreL, D3, sd, d12, N: public parameters only when these are terms): hO (the six public
    items that RecIs spends are open at border k) · hArr (readsArrayP) · hMask (maskPlanB) · hCells
    (arraysPlanB) · hell (nV is at most the mask row's length). The first four have run true, with
    negative tests that rejected, at both sizes, AT LETTERS FILLED BY HAND AND AT A PinPlan MADE
    OTHERWISE THAN THE CALLER's; hell at the small size alone.
  TWO CONDITIONS ON PUBLIC LETTERS: hsits (SitsIn) · hcov (Covers).
  hns: behind an accepting run the ledger's number of slots is at most nV (ns_behind has it from the
    same bound in front; Johnson/Road/K4/FormsPinsNs.lean from the promise in front). Three letters
    speak of slots: nV (where the value's mask row is cut), ns (the value's own letter, read by no
    premise) and the ledger's G.ns.
  hSt: behind an accepting run the data's letter St is K4's arm there (StatedIs at uLay): a tie on a
    letter without a term here. hSt_pins (Johnson/Road/K4/ULayPins.lean) has it at one state where
    St is the one stated function at the arm off the public parameters: it owes that the open
    segment's number is m, that tlAt X m is par.hp.tl and that the names are A's.
The promise behind at the table (onQ at k + 1) and "no mark" behind are in the line's words and are
not spent. RecIs rests on six public items, of which three (frame.liveIs, K12.seatsCarried,
K12.msgShapes) leave the table's door in the composed filling (`mgAll`, MgAll.lean: `mgAll_more`;
`leavesName`, SmallDoor.lean): THERE hO SAYS FALSE, E AND hO CANNOT HOLD TOGETHER, AND forms_pins
IS IDLE; so is the payer of asks. IT SPEAKS AT A WIDER MEANING ALONE, and what is shown there counts
only when the bridge from that meaning to `mgAll`'s is paid. Met through Lean at no member.
K04_law, the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.


-/
import Johnson.Road.K4.FormsOfMeans
import Johnson.Road.K4.ArmLay
import Johnson.Road.K4.K4PinsTab
import Johnson.Road.K4.K4PinsIdn
import Johnson.Road.K4.Rec.AtMeans
import Johnson.Road.K4.Rec.Arrays
import Johnson.Road.K4.Rec.PinsBools

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Road.K4

open Iop OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Flat OnBytes.Maker
open OnBytes.Model.Layer (Pub Own Lay)
open OnBytes.Desc.First.K4 (Par seatS formsBack)
open OnBytes.Desc.First.K4.Total (KeptAsks)
open OnBytes.Desc.First.K4.InT (segAt_lay)
open OnBytes.Road.K4.InT (InTAsks StatesAt kept_open)
open OnBytes.Road.K4.Rec (RecIs RecPlan Part9 recPlanOf recIs_at recIs_behind readsArrayP
  readsArray_plan maskPlanB maskPlan_of_B maskOne_of_plan maskEllP maskEllP_at arraysPlanB
  arrayPlan_of_B cellPlan_of_array cellOne_of_plan openAllB)
open _root_.Run (ckP)
open VerifiableInference.Desc (Place Wit Claim Link K9.LinkHoles K9.statesOfLink K9.readersOfLink
  K9.segAt?)
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers)
open VerifiableInference.Desc.First.Look (sigListCalls szOf)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (Frame Piece Mem onQ meansQ MsgT GQ dataQ seatTab StatedIs)
open VerifiableInference.Desc.Plain.K04 (FormsT frontRun)

section
variable {Cells Tok : Type} (A : PinPlan Cells) {own : List (ℕ × ℕ)} {R : RecPlan} {n m : ℕ}
  {a : Part9} (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers) (mS : ℕ)

/-- Below nV the value's mask row at the pinned part is the table's data's, under hs hB h hl. -/
theorem mask_pins (hs : SitsIn (sigListCalls A.D A.rad A.link) A.seatT ms N mS)
    (hB : maskPlanB A own R n m = true) (h : RecIs a R n m) {nV : ℕ} (hl : nV ≤ maskEllP A)
    (w : Wit Cells Tok MsgT) {j : ℕ} (hj : j < nV) :
    A.maskN nV (partOf A.D.codes arr ms N mS w) j =
      (dataQ own a (seatTab A.D.codes arr ms w)).mask j := by
  obtain ⟨H⟩ := maskPlan_of_B A hB
  unfold PinPlan.maskN
  rw [if_pos hj]
  refine mask_dataQ_tab A own a arr ms N mS hs (maskOne_of_plan A H h) w j ?_
  have e := maskEllP_at A H
  exact Nat.lt_of_lt_of_le hj (e ▸ hl)

/-- The value's raw matrices at the pinned part are matsOfB at the table's data, under hs hB h. -/
theorem raw_pins (hs : SitsIn (sigListCalls A.D A.rad A.link) A.seatT ms N mS) (tl : HTailF2)
    (hB : arraysPlanB A tl own R n m = true) (h : RecIs a R n m) (w : Wit Cells Tok MsgT) :
    A.raw tl (partOf A.D.codes arr ms N mS w) =
      matsOfB A tl (dataQ own a (seatTab A.D.codes arr ms w)) :=
  raw_dataQ_tab A own a arr ms N mS hs tl (fun μ i c' => cellOne_of_plan A
    (Classical.choice (cellPlan_of_array A
      (Classical.choice (arrayPlan_of_B A (List.all_eq_true.1 hB μ (List.mem_finRange μ))))
      i.isLt c'.isLt)) h) w

end

variable [scl : Inst.Model.Scl] {Xi P Tok Cl : Type} {rows cols nR kC : ℕ} {X : Verify.Public}
  {Fr : Frame}
  {Mg : Meaning P (Wit (CellsK rows cols) Tok MsgT)} {D : K4Data Xi P Tok rows cols nR kC X} {Z : P}
  {links : List ModelPart} {ps : List Place} {k m : ℕ}
  {q : Piece (ckP .two) Fr S Cl (Wit (CellsK rows cols) Tok MsgT)} {par : Par}

omit scl in
/-- Behind an accepting run inside the promise in front, at a statement that bears no mark: RecIs at
the open segment's part, under E hO hS. -/
theorem recIs_run (E : K4Means Mg D) (hO : openAllB D.moreL links ps k m = true)
    {a : S × Fr.E.Str} {τ : Tr (uLT (ckP .two) q.ds)} {fo : Forest.Heard} {o : Own} {G' : Fork}
    (ha : onQ D.N Mg links ps (fun s => (Z, s)) k a) (hu : a.1.failed = none)
    (Y : Yes seatS par q a τ fo o G')
    (hS : ∀ a₀, a.1.here = .lay a₀ → PscRun.Sized a₀.F) {A' : Part9}
    (hA' : K9.segAt? (behindOf seatS q a τ o G').1 = some A') :
    RecIs A' (recPlanOf D D.sd) (D.N.msgsAt ps[k]?) m := by
  have K := kept_of_yes Y
  obtain ⟨a₀, _, _, _, _, _, _, h0, _⟩ := kept_open K
  obtain ⟨A₀, hA₀, _, _⟩ := segAt_lay h0
  exact recIs_behind K hS hA₀ hA' (recIs_at E Z links ps k m a A₀ hO ⟨ha, hu, hA₀⟩)

omit scl in
/-- The ledger's number of slots behind an accepting run is that in front: so hns of forms_pins
follows from a bound in front. -/
theorem ns_behind {a : S × Fr.E.Str} {τ : Tr (uLT (ckP .two) q.ds)} {fo : Forest.Heard} {o : Own}
    {G' : Fork} (Y : Yes seatS par q a τ fo o G') {nV : ℕ}
    (h0 : ∀ a₀, a.1.here = .lay a₀ → a₀.F.ns ≤ nV) :
    ∀ G, (behindOf seatS q a τ o G').1.fork? = some G → G.ns ≤ nV := by
  intro G hG
  obtain ⟨a₀, _, _, _, G₁, _, _, ha, _, _, _, _, _, hG₁, hh⟩ := kept_open (kept_of_yes Y)
  obtain rfl : G₁ = G := Option.some.inj (hG₁.symm.trans hG)
  rw [(OnBytes.Desc.First.K4.hearFl_later hh).ns]
  exact h0 a₀ ha

/-- **THE LINE "forms" AT THE PINNED VALUE**, under hg E hRd hruns hk hcs · asks · hO hArr hMask
hCells hell · hsits hcov · hns hSt. -/
theorem forms_pins (A : PinPlan (CellsK rows cols)) (nV : ℕ) (y : Lay)
    (nM nRr nC n0 ns nx v7 : ℕ) (hg : par.g < 12) (E : K4Means Mg D) {Hh : K9.LinkHoles}
    {l : Link S Claim} (hRd : D.Rd m = K9.readersOfLink Hh l)
    (hruns : D.runs m 3 "own" = [(2, "front"), (2, "back")]) (hk : par.k3Runs = true)
    (hcs : A.D.codes = D.cs)
    (asks : ∀ a τ fo o G', onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' → ∃ (P₀ : Pub) (o₀ : Own),
        KeptAsks par a.1 (behindOf seatS q a τ o G').1 P₀ o₀ ∧
        InTAsks (D.N.sent m 0) par a.1 (behindOf seatS q a τ o G').1 ∧
        StatesAt (K9.statesOfLink l) 2 par "front" (behindOf seatS q a τ o G').1 ∧
        StatesAt (K9.statesOfLink l) 2 par "back" (behindOf seatS q a τ o G').1)
    (hO : openAllB D.moreL links ps k m = true)
    (hArr : readsArrayP par.hp D.D3.shape D.D3.layout (D.D3.arrayOf.getD m #[]) m (D.sd.trees m) =
      true)
    (hMask : maskPlanB A (D.N.sent m 0) (recPlanOf D D.sd) (D.N.msgsAt ps[k]?) m = true)
    (hCells : arraysPlanB A par.hp.tl (D.N.sent m 0) (recPlanOf D D.sd) (D.N.msgsAt ps[k]?) m =
      true)
    (hell : nV ≤ maskEllP A)
    (hsits : SitsIn (sigListCalls A.D A.rad A.link) A.seatT D.ms D.N m)
    (hcov : Covers par.hp.tl nM nRr nC)
    (hns : ∀ a τ fo o G', onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' → ∀ G, (behindOf seatS q a τ o G').1.fork? = some G → G.ns ≤ nV)
    (hSt : ∀ a τ fo o G', onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' →
      StatedIs D.St (uLay par.hp.tl fun _ B => matsOfB A par.hp.tl B)
        (behindOf seatS q a τ o G').1) :
    ∀ b w, keptFrom (tableOn0 D.N Mg Z links ps k) par q b →
      onQ D.N Mg links ps (fun s => (Z, s)) (k + 1) b → b.1.failed = none →
      meansQ (Fr := Fr) D.N Mg (fun s => (Z, s)) (.formsT m 3 "own") b w →
      FormsT seatS
        (((A.seatN nV D.N par.hp.tl y nM nRr nC n0 ns nx v7).atRec X par hg).semOf
          (partOf A.D.codes D.arr D.ms D.N m) par.hp.tl) (frontRun par) formsBack b.1 w := by
  have hrec : ∀ a τ fo o G', onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' → ∀ A', K9.segAt? (behindOf seatS q a τ o G').1 = some A' →
      RecIs A' (recPlanOf D D.sd) (D.N.msgsAt ps[k]?) m := by
    intro a τ fo o G' ha hu Y A' hA'
    obtain ⟨_, _, As, _, _, _⟩ := asks a τ fo o G' ha hu Y
    exact recIs_run E hO ha hu Y As.sized hA'
  refine forms_of_means _ _ (fun _ B => matsOfB A par.hp.tl B) E hRd hruns hk asks ?_ ?_ ?_ ?_
  · intro a τ fo o G' ha hu Y
    obtain ⟨_, a', _, _, _, _, _, _, _, ha', _⟩ := kept_open (kept_of_yes Y)
    obtain ⟨A', hA', _, _⟩ := segAt_lay ha'
    rw [readsArray_plan (hrec a τ fo o G' ha hu Y A' hA') par.hp ha' hA']
    exact hArr
  · intro a τ fo o G' ha hu Y w A' o' c hA' ho' hc h2
    obtain ⟨_, a', _, o₁, _, _, _, _, _, ha', _, eo, ho₁, _⟩ := kept_open (kept_of_yes Y)
    obtain ⟨A'', hA'', _, eAL⟩ := segAt_lay ha'
    obtain rfl : A'' = A' := Option.some.inj (hA''.symm.trans hA')
    obtain rfl : o₁ = o' := Option.some.inj (ho₁.symm.trans ho')
    exact statedAt_of_is (hSt a τ fo o G' ha hu Y) ha' eo (by rw [← eAL]; exact hc) h2 _ _
  · intro a τ fo o G' ha hu Y w A' G hA' hG j hj
    show A.maskN nV (partOf A.D.codes D.arr D.ms D.N m w) j = _
    rw [← hcs]
    exact mask_pins A D.arr D.ms D.N m hsits hMask (hrec a τ fo o G' ha hu Y A' hA') hell w
      (Nat.lt_of_lt_of_le hj (hns a τ fo o G' ha hu Y G hG))
  · intro a τ fo o G' ha hu Y w A' hA' x r c _ _ _
    rw [mats_raw A nV D.N par.hp.tl y nM nRr nC n0 ns nx v7 hcov X par hg, ← hcs,
      raw_pins A D.arr D.ms D.N m hsits par.hp.tl hCells (hrec a τ fo o G' ha hu Y A' hA') w]

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.mask_pins
#print axioms OnBytes.Road.K4.raw_pins
#print axioms OnBytes.Road.K4.recIs_run
#print axioms OnBytes.Road.K4.ns_behind
#print axioms OnBytes.Road.K4.forms_pins
