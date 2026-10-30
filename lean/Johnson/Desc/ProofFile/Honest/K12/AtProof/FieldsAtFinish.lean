-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/AtProof/FieldsAtFinish.lean: UNDER THE HEAD, OF THE RECORD T THAT
THE WAY INTO THE FIRST CHAIN's PROXIMITY TEST RETURNS (`enterFinish`,
Johnson/Desc/K12/AtFinish.lean) AT A STATE THAT THE CHAIN's OWN SUB-PROTOCOLS' STEPS REACH: its
statement is tidy; its codes are the written table; the first fold's mask has come; the group under
test is number 25. Statements and proofs: calls of the library's laws, joined at T; no definition.

What for. The condition of the frame's sentence at the test's second member asks eight things of the
job's state on entry (`FrontAsksD`, ShapeAllDense.lean in the folder above). These are three of
them, and the number of the group that five of them read, at the verifier's own record.

  `fin_mask_place`, `mask_of_reach`   behind an accept at the place of the last code switch the
                 finish holds a mask's number; so along "reached". The twins of `fin_group_place`
                 and `group_of_reach` (Johnson/Loose/H2K12/GroupAt354.lean)
  `tidy_at_finish`   `stTidyB T.st = true`: at any earlier hash, at every border
  `codes_at_finish`   `T.st.codes = codesFull2`: at every border
  `came_at_finish`   `T.mask.isSome = true`: at border 354
  `group_at_finish`   `T.g = 25`: at border 354
  `four_at_finish`   the four, at a state reached at border 354 by the wrapped steps

By what. `enterFinish_ok` (Johnson/Desc/K12/SeatLaws.lean): T has the state's statement, the
finish's group and mask, and the state bears no mark. `tidy_at_open_raw`
(Johnson/Desc/AtSeats/Fit/TidyAtOpen.lean); `stTidyB` is `tidy4B` by its text
(Johnson/Desc/Ground/Shape/Marks.lean). `codes_field` (Johnson/IMR/AtReach.lean),
`written354_of_pins` (Johnson/Loose/H2K12/ClosedOfPins354.lean), `AtMg.pins`
(Johnson/P5T/FenceAtMg.lean). `finishPlace_cut`, `reach_last`, `seat_yes`, `group_of_reach`
(GroupAt354.lean), `finishBehindQ_iff` (Johnson/Top/H0/Tw/K2C/Asks.lean), `seat353_open`,
`grp_of_yes`, `count353_open` (Johnson/Loose/H2K12/Seat353AtMg.lean), `reach_raw`
(Johnson/Top/H0/Walk/Reach.lean).

A neighbour. The library has three of the four as fields of one structure, at a state without a mark
at border 354, under the head at the format's second hash function: `FactsK12`
(Johnson/Loose/H2K12/Promise354.lean: `tidy`, `codes`, `groupAtFinish`), made by `factsK12_at_head`
(Johnson/Loose/H2K12/Seat353AtMg.lean) under three premises more. Here less is asked, and it is said
of T. The mask is not among that structure's fields.

Limits.
- THAT THE WAY IN RETURNS (he) AND THAT THE STATE IS REACHED (hr) ARE PREMISES. That any state is
  reached at a border above 0 is not shown here.
- OF THE VERIFIER's RECORD, NOT OF A JOB's STATE ON ENTRY: no job is named here.
- FOUR FIELDS OF `FrontAsksD` ARE NOT TREATED: `door`, `claims`, `plain`, `pub`. `denseRows` is the
  library's `taken_dense_entered` (Johnson/AtFull/Shape/TakenRowsDense.lean). That the group number
  25 is there is not said here.
- TWO KINDS OF "REACHED". `tidy_at_finish`, `codes_at_finish`: by the sub-protocols' bare steps.
  `came_at_finish`, `group_at_finish`, `four_at_finish`: by the wrapped steps (`below`), which give
  the bare ones (`reach_raw`). All but `tidy_at_finish`: at the format's second hash function.
- `codesFull2` (Johnson/G/PackLit.lean) and `H2K.Member.codesFull` are one table (`codes_two`,
  AsksAtHead.lean in the folder above).
- Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean in the folder above.
-/
import Johnson.Loose.H2K12.Seat353AtMg
import Johnson.Loose.H2K12.ClosedOfPins354
import Johnson.Desc.AtSeats.Fit.TidyAtOpen
import Johnson.Desc.AtSeats.FoldFactsPaid
import Johnson.IMR.AtReach
import Johnson.P5T.FenceAtMg
import Johnson.Desc.K12.SeatLaws
import Johnson.Desc.Ground.Shape.Marks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 finishPlace)
open VerifiableInference.Desc.K12 (T12 enterFinish)
open VerifiableInference.Desc.Ground.Sh (stTidyB)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open Johnson.G (codesFull2)
open H2K12 (SeatF1)

/-! ## 1 The mask behind the last code switch -/

/-- **Behind an accept at the place of the last code switch the state stands at the finish, and the
finish holds a mask's number**: the quiet step behind lays it. -/
theorem fin_mask_place (p : P2) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))}
    (h : (finishPlace p : Block S Unit).decide s rs gs = .ok s') :
    ∃ o, s'.here = .fin o ∧ o.mask.isSome = true := by
  obtain ⟨t, t', rs', gs', -, -, h3, -⟩ := H2K12.finishPlace_cut p h
  obtain ⟨a', m, -, -, rfl⟩ := (VerifiableInference.Desc.First.K2.finishBehindQ_iff t' s').1 h3
  exact ⟨_, rfl, rfl⟩

/-- **The mask at the finish, along "reached".** -/
theorem mask_of_reach {Cl P : Type} (bs : List (Block S Cl)) (start : P → S) (k : ℕ)
    (B : Block S Cl) (hB : bs[k]? = some B) (p : P2) (hK : SeatF1 B p) {z : P} {s' : S}
    (h : Reach 0 (bs.map below) start (k + 1) (z, s')) :
    ∀ o, s'.here = .fin o → o.mask.isSome = true := by
  obtain ⟨s, b, -, hb, hy⟩ := H2K12.reach_last h
  rw [List.getElem?_map, hB] at hb
  obtain rfl : below B = b := Option.some.inj hb
  obtain ⟨rs, gs, -, hd⟩ := H2K12.seat_yes hK hy
  obtain ⟨o', ho', hm⟩ := fin_mask_place p hd
  intro o ho
  rw [ho'] at ho
  obtain rfl : o' = o := by injection ho
  exact hm

/-! ## 2 Under the head -/

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- **The record's statement is tidy.** At any earlier hash; at every border; the bare steps. -/
theorem tidy_at_finish (h : P5J.AtMg o Z D r₀ Zp Np cF) {k : ℕ} {p : ProofFile.InstPub} {s : S}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k (p, s)) {T : T12} (he : enterFinish s = .ok T) :
    stTidyB T.st = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨f, -, -, hf, rfl⟩ := VerifiableInference.Desc.K12.Seat.enterFinish_ok s T he
  exact _root_.Meaning.K2.tidy_at_open_raw h.laid.value h.laid.planOk O k (p, s) hr
    (Option.isNone_iff_eq_none.1 hf)

/-- **The record's codes are the written table.** At every border; the bare steps. -/
theorem codes_at_finish (h : P5J.AtMg OnBytes.secondHashFunction Z D r₀ Zp Np cF) {k : ℕ}
    {p : ProofFile.InstPub} {s : S} (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k (p, s)) {T : T12}
    (he : enterFinish s = .ok T) : T.st.codes = codesFull2 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨f, -, -, hf, rfl⟩ := VerifiableInference.Desc.K12.Seat.enterFinish_ok s T he
  have hp : ∀ b ∈ cF.blocksInOrder, b.planOk = true := _root_.Meaning.K2.flat_planOk O.desc h.laid.planOk
  have e := _root_.Meaning.K2.codes_field h.scope h.reads O hp _ id (fun _ _ q => q) k (p, s) hr
    (Option.isNone_iff_eq_none.1 hf)
  have W := H2K12.written354_of_pins h.scope h.laid.pub h.pins.1
    (h.laid.run ▸ LPFD.Full.laidPOf_of h.laid.value h.laid.planOk h.laid.data h.laid.asks)
  exact e.trans W.codes

/-- **The first fold's mask has come.** At border 354; the wrapped steps. -/
theorem came_at_finish (h : P5J.AtMg OnBytes.secondHashFunction Z D r₀ Zp Np cF) {p : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 354 (p, s)) {T : T12}
    (he : enterFinish s = .ok T) : T.mask.isSome = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨b, q, hb, hK⟩ := H2K12.seat353_open h.scope h.reads O h.laid.planOk
  obtain ⟨f, hf, -, -, rfl⟩ := VerifiableInference.Desc.K12.Seat.enterFinish_ok s T he
  exact mask_of_reach cF.blocksInOrder (ProofFile.startS Zp) 353 b hb q hK hr f hf

/-- **The group under test is number 25.** At border 354; the wrapped steps. -/
theorem group_at_finish (h : P5J.AtMg OnBytes.secondHashFunction Z D r₀ Zp Np cF) {p : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 354 (p, s)) {T : T12}
    (he : enterFinish s = .ok T) : T.g = 25 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨b, q, hb, hK⟩ := H2K12.seat353_open h.scope h.reads O h.laid.planOk
  obtain ⟨f, hf, -, -, rfl⟩ := VerifiableInference.Desc.K12.Seat.enterFinish_ok s T he
  have hg : f.fr.group = q.grp :=
    H2K12.group_of_reach cF.blocksInOrder (ProofFile.startS Zp) 353 b hb q hK hr f hf
  obtain ⟨s₀, b', h0, hb', hy⟩ := H2K12.reach_last hr
  rw [List.getElem?_map, hb] at hb'
  obtain rfl : below b = b' := Option.some.inj hb'
  obtain ⟨rs, gs, -, hd⟩ := H2K12.seat_yes hK hy
  exact hg.trans ((H2K12.grp_of_yes q hK.1 hd).trans
    (H2K12.count353_open h.scope h.reads O p s₀ h0))

/-- **The four.** -/
theorem four_at_finish (h : P5J.AtMg OnBytes.secondHashFunction Z D r₀ Zp Np cF) {p : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 354 (p, s)) {T : T12}
    (he : enterFinish s = .ok T) :
    stTidyB T.st = true ∧ T.st.codes = codesFull2 ∧ T.mask.isSome = true ∧ T.g = 25 :=
  ⟨tidy_at_finish h (reach_raw hr) he, codes_at_finish h (reach_raw hr) he, came_at_finish h hr he,
    group_at_finish h hr he⟩

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.fin_mask_place
#print axioms ProofFile.Honest.K12.AtProof.mask_of_reach
#print axioms ProofFile.Honest.K12.AtProof.tidy_at_finish
#print axioms ProofFile.Honest.K12.AtProof.codes_at_finish
#print axioms ProofFile.Honest.K12.AtProof.came_at_finish
#print axioms ProofFile.Honest.K12.AtProof.group_at_finish
#print axioms ProofFile.Honest.K12.AtProof.four_at_finish
