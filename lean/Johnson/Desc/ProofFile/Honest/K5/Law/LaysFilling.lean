-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/LaysFilling.lean: IT MOVES THE EQUATION THAT THIS KIND's CELLS
ASK OF A SCRIPT (`ESymsRaw`, CellsQRaw.lean in this folder) TO ONE SENTENCE ON THE SCRIPT's TEXT AT
EACH OF TWO SEGMENTS, IN THE FRAME's OWN LETTERS. THAT TEXT IS NOT WRITTEN: IT PAYS NOTHING OF THE
SCRIPT. CONDITIONAL: under the hypothesis h; on the premise's form `LaysFilling` at the attention
segment and at the group's feed-forward segment; on one equation between the two readers of the
cells; on one premise on the reader at the borrowed matrix qa. One definition, a premise's form; two
theorems.

What it is for. `ESymsRaw` says what a script's message holds at the seat of a symbol, in the
letters of the verifier's side. The frame has a filling of a segment's first sending (`firstData`,
Johnson/Desc/ProofFile/Honest/K1/FirstData.lean). `LaysFilling` says, in the frame's letters, that
the script's messages hold what that filling lays. This file shows that the second gives the first.

Main names:
  `LaysFilling h Q Vd N rd seat heard l`: THE FORM, at segment l. reach, on public data: each array
    of segment l that the values have (`cellsVals`) lies in a message that is seated at an address
    whose sending begins when at most N challenges have been heard. lays, on the script: where the
    filling's call that asks first (`RowData.ask`) answers an element at a main row and place of
    message m, the witness's message with the plan's number of (l, m) (`P5J.At.num Zp`) holds it.
  `eSyms_of_lays`: **`ESymsRaw` from the form at 2 g and at 2 g + 1.**
  `msg_of_lays`: what the form gives at one element that the layout's rule lays.

WHAT THE FORM DOES NOT ASK. Nothing where the filling lays nothing or its call rejects. Nothing on
mask rows. seat and heard may be those of one sending; the two forms' seats and heards are letters
without a tie.

How. `seat_number_head` (SeatNumber.lean): the array, the place and the number at a symbol's seat;
`laidData_ask` (WayBackFill.lean): what the filling answers there; `cellsVals_size`,
`labelNo_arrayLabel` (PackedVals.lean); `cells_pack_label`, `owner_numbers_att`, `shape_at_plan`,
`labelOf_label`, `mu_att` (PackedAtSeg.lean); the programs' two public tests under the head:
`Meaning.K2.pub_layoutOk` (Johnson/IMR/LayoutOkPub.lean), `P1K2.hok_open`
(Johnson/P1K2R/DebtsConst.lean); `nm_head` (CellsQAtHead.lean).

Limits. THAT THE FORM CAN BE MET IS NOT SHOWN: no script is exhibited. It must ask no number for two
texts: that it does not is not shown here: see `lays_one_text` (KeysCover.lean in this folder). That
a seat of the frame's reaches is not shown. reach asks of all arrays of the two segments that the
values have; the proof spends those of as0, ah, ao and qa. That the reader answers for qa the same
under both segments' numbers is a premise, shown by nobody. The planes are left out by `ESymsRaw`
itself. At `Sz.ref`, the full-size example's numbers. It rests, beside the head, on closed facts
that Lean's kernel decided by evaluation (see SeatNumber.lean and PackedVals.lean). Through its
imports the file stands above Cb/Bridge/CodeListRSProved.lean, and so above the files under
ThirdParty/ (lean/LIMITS.md, L15): a fact on import lines. At the earlier hash `OnBytes.secondHashFunction`, a
fixed function.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.SeatNumber
import Johnson.Desc.ProofFile.Honest.K5.Law.PackedAtSeg
import Johnson.Desc.ProofFile.Honest.K5.Law.WayBackFill
import Johnson.P1K2R.DebtsConst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz Seg MatName nameNo_isSome nameNo_eq_some_iff matAt_eq_some_iff no?_lt
  parts_in_scope shape_owner owner_owner below_of_mu ref_ok arrayNo_isSome_iff)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First.Look (lookAt)
open ProofFile.Honest.FirstThread (Script)
open ProofFile.Honest.K1 (labelNo cellsVals firstData)
open P5J (AtMgA TS CellsM)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)

/-- **THE SCRIPT LAYS THE FILLING, AT ONE SEGMENT**: a premise's form, in the frame's own letters.
l: the segment's number; rd: the readers of an input; seat, heard: the filling's two public letters,
which may be those of one sending. It is a definition: nothing is claimed of it, and nothing here
shows that it can be met. -/
structure LaysFilling (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (N : Nat)
    (rd : Local W₀ Rc ProofFile.Inst Tr → Readers) (seat : MsgAddr → Option (Nat × Nat))
    (heard : MsgAddr → Nat) (l : Nat) : Prop where
  /-- ON PUBLIC DATA: the message of each array of segment l that the values have is seated at an
  address whose sending begins when no more than N challenges have been heard -/
  reach : ∀ (As : List OnBytes.Params.ReqArray) (A : OnBytes.Params.ReqArray),
    h.𝔇.sent.layout.link[l]? = some As → A ∈ As → ((cellsVals Sz.ref).size l A.name).isSome = true →
    ∃ Ad : MsgAddr, seat Ad = some (l, A.message) ∧ heard Ad ≤ N
  /-- ON THE SCRIPT: where the filling's call that asks first answers an element in a main row of
  message m of segment l, the witness's message with the plan's number of (l, m) holds that element,
  read into the extension field -/
  lays : ∀ (k : Coins Bk) (v : Local W₀ Rc ProofFile.Inst Tr) (hd : List Fmt.Drawn), Vd v →
    N ≤ hd.length → ∀ (Ad : MsgAddr) (m : Nat), seat Ad = some (l, m) →
    ∀ (row place : Nat) (y : Cb.Gl.F ⊕ Cb.Gl.E),
    (firstData Sz.ref h.𝔇.sent.codes h.𝔇.sent.shape h.𝔇.sent.layout seat heard).ask (rd v) hd Ad row
      place = .ok (some y) →
    Q.msg (P5J.At.num Zp l m) k v (hd.take (Q.fixedMsg (P5J.At.num Zp l m))) false row place =
      asE (some y)

variable {h Q}

/-- **What the form gives at one element that the layout's rule lays.** CONDITIONAL: under the
hypothesis h; L: the form at segment l; A is an array of segment l; the rule lays (i', c) of A at p;
the values have A, and (i', c) lies inside the size that they say; the input meets Vd; at least N
challenges have been heard. -/
theorem msg_of_lays {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : ℕ}
    {rd : Local W₀ Rc ProofFile.Inst Tr → Readers} {seat : MsgAddr → Option (ℕ × ℕ)}
    {heard : MsgAddr → ℕ} {l : ℕ} (L : LaysFilling h Q Vd N rd seat heard l) {n : String}
    {A : OnBytes.Params.ReqArray}
    (hA : VerifiableInference.Desc.arrayOf h.𝔇.sent.layout l n = some A) {i' c : ℕ} {p : ℕ × ℕ}
    (hp : VerifiableInference.Desc.laidAt A i' c = some p) {z : ℕ × ℕ}
    (hz : (cellsVals Sz.ref).size l A.name = some z) (hi : i' < z.1) (hc : c < z.2)
    (k : Coins Bk) {v : Local W₀ Rc ProofFile.Inst Tr} (hv : Vd v) {hd : List Fmt.Drawn}
    (hN : N ≤ hd.length) :
    ∃ hd' : List Fmt.Drawn,
      Q.msg (P5J.At.num Zp l A.message) k v (hd.take (Q.fixedMsg (P5J.At.num Zp l A.message))) false
          p.1 p.2 =
        asE (some ((cellsVals Sz.ref).val (rd v) hd' l A.name i' c)) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have ok : OnBytes.reqLayoutOk h.𝔇.sent.codes h.𝔇.sent.shape h.𝔇.sent.layout = true :=
    _root_.Meaning.K2.pub_layoutOk h.laid.pub
  have okS : OnBytes.reqShapeOk h.𝔇.sent.shape = true := P1K2.hok_open O
  obtain ⟨As, hl, hf⟩ := Option.bind_eq_some_iff.1 hA
  obtain ⟨Ad, hAd, hh⟩ := L.reach As A hl (List.mem_of_find?_eq_some hf) (by rw [hz]; rfl)
  have q := laidData_ask okS ok hA hp heard hAd hz hi hc (rd v) (hd := hd) (Nat.le_trans hh hN) rfl
  exact ⟨_, L.lays k v hd hv hN Ad A.message hAd p.1 p.2 _ q⟩

/-- **THE CELLS' EQUATION FROM THE FORM AT THE TWO SEGMENTS.** CONDITIONAL: under the hypothesis h;
g is below 12; a is the group's plan; x₁ is the place of the segment's lookup on the calls; hS, hL:
the seat's shape and segment are the plan's; hrd: the frame's reader of the cells is this kind's;
hqa: THE READER ANSWERS FOR qa THE SAME UNDER BOTH SEGMENTS' NUMBERS; L0, L1: THE FORM at the
group's feed-forward segment and at the attention segment. It moves the debt: none of these is shown
here. -/
theorem eSyms_of_lays {g : ℕ} (hg : g < 12) {a : OnBytes.Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {x₁ : VerifiableInference.Desc.First.Look.Place}
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁)
    {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : ℕ} {cells : Tr → Cells} {Z5 : Seat5}
    {rd : Local W₀ Rc ProofFile.Inst Tr → Readers} {seat₀ seat₁ : MsgAddr → Option (ℕ × ℕ)}
    {heard₀ heard₁ : MsgAddr → ℕ} (hS : Z5.P.S = a.S) (hL : Z5.link = 2 * g + 1)
    (hrd : ∀ v, (rd v).cells = cells v.trace)
    (hqa : ∀ v, Vd v → ∀ r c, (cells v.trace).cell (2 * g) "qa" r c = (cells v.trace).cell
        (2 * g + 1) "qa" r c)
    (L0 : LaysFilling h Q Vd N rd seat₀ heard₀ (2 * g))
    (L1 : LaysFilling h Q Vd N rd seat₁ heard₁ (2 * g + 1)) : ESymsRaw h Q Vd N x₁ a cells Z5 := by
  intro k v hd hv hN i i' c hi3 hi' hc s hk hs
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hX := O.public
  rw [O.W] at hX
  have C := OnBytes.Road.Hd.core_of_scope h.scope h.reads hX
  have eL : x₁.link = 2 * g + 1 := VerifiableInference.OnPublicFiles.lookAt_link hx
  have h5 : a.seam.tl.mats.size = 5 := by
    have e : (_root_.Meaning.tlAt (P5J.At.X Zp) (2 * g + 1)).mats.size = 5 :=
      _root_.Meaning.size_odd hX C hg
    rw [H2K5.Door.tlAt_att hg ha] at e
    exact e
  have hsz : i < 5 := by
    by_contra hn
    have e0 : a.seam.tl.mats.getD i {} = {} := by
      simp [Array.getD, show ¬ i < a.seam.tl.mats.size by omega]
    rw [e0] at hc
    exact absurd hc (Nat.not_lt_zero _)
  have hiN : i < a.seam.tl.NM := Nat.lt_of_lt_of_le (by omega) (nm_head h ha)
  obtain ⟨μ, hμ⟩ := nameNo_isSome Sz.ref (σ := .att g) (mu := i) hsz
  have eN : a.S.cf.NAs = Sz.ref.NAs := by
    rw [← H2K5.Door.shapeA_at ha]
    exact (parts_in_scope h.scope h.reads hX).2.2.1 g hg
  have hp : μ ≠ .bA := by
    rintro rfl
    have e3 : 3 = i := Option.some.inj ((nameNo_eq_some_iff Sz.ref _ _ _).1 hμ)
    exact hi3 (by rw [hS, eN, ← e3]; rfl)
  obtain ⟨A, -, hA, hlaid, hnum⟩ := seat_number_head h hg ha hx hiN hi' hc hk hs
  rw [hnum, hS, hL, ← hrd v]
  rw [eL] at hA ⊢
  have k12 : _root_.Meaning.ownerK (_root_.Meaning.labAt (P5J.At.X Zp) (2 * g + 1) i) =
      (Sz.ref.owner (.att g) μ).1.no 12 ∧
      Sz.ref.mu (Sz.ref.owner (.att g) μ).1 (Sz.ref.owner (.att g) μ).2 =
        some (_root_.Meaning.ownerA (_root_.Meaning.labAt (P5J.At.X Zp) (2 * g + 1) i)) :=
    owner_numbers_att h.scope h.reads hX hg hμ
  obtain ⟨k1, k2⟩ := k12
  obtain ⟨As, -, hf⟩ := Option.bind_eq_some_iff.1 hA
  have hname : A.name = _root_.Meaning.nameOf
      (_root_.Meaning.ownerA (_root_.Meaning.labAt (P5J.At.X Zp) (2 * g + 1) i)) := by
    simpa using List.find?_some hf
  have h9 : ∀ σ : Seg, Sz.ref.len σ ≤ 9 := fun σ => by
    cases σ with
    | ff _ => exact (by decide : 3 + 1 + 5 ≤ 9)
    | att _ => exact (by decide : 1 + 4 ≤ 9)
    | head => exact (by decide : 4 + 4 ≤ 9)
  have hlt : _root_.Meaning.ownerA (_root_.Meaning.labAt (P5J.At.X Zp) (2 * g + 1) i) < 26 := by
    have k3 := k2
    unfold Sz.mu at k3
    split_ifs at k3
    exact Nat.lt_of_lt_of_le (no?_lt Sz.ref k3) (Nat.le_trans (h9 _) (by decide))
  have hn : labelNo A.name = some
      (_root_.Meaning.ownerA (_root_.Meaning.labAt (P5J.At.X Zp) (2 * g + 1) i)) := by
    rw [hname]
    exact labelNo_arrayLabel hlt
  have hM₀ : Sz.ref.matAt (_root_.Meaning.ownerK (_root_.Meaning.labAt (P5J.At.X Zp) (2 * g + 1) i))
      (_root_.Meaning.ownerA (_root_.Meaning.labAt (P5J.At.X Zp) (2 * g + 1) i)) =
      some ((Sz.ref.owner (.att g) μ).1, (Sz.ref.owner (.att g) μ).2) := by
    rw [k1]
    exact (matAt_eq_some_iff Sz.ref _ _ _ _).2 ⟨below_of_mu (by rw [k2]; rfl), rfl, k2⟩
  have ho : (Sz.ref.arrayNo (Sz.ref.owner (.att g) μ).1
      (Sz.ref.owner (.att g) μ).2).isSome = true :=
    (arrayNo_isSome_iff Sz.ref _ _).2 ⟨by rw [k2]; rfl, owner_owner Sz.ref (.att g) μ⟩
  have hz := cellsVals_size Sz.ref hn hM₀ ho
  obtain ⟨hm, hkk⟩ := shape_at_plan h.scope h.reads hX hg ha hμ hp
  have eO := shape_owner Sz.ref ref_ok.1 (.att g) μ (by rw [mu_att hg hμ]; rfl)
  have ePS : Sz.ref.packedShape
      (_root_.Meaning.ownerK (_root_.Meaning.labAt (P5J.At.X Zp) (2 * g + 1) i))
      (_root_.Meaning.ownerA (_root_.Meaning.labAt (P5J.At.X Zp) (2 * g + 1) i)) =
      (Alg.symRows (a.seam.tl.mats.getD i {}).m, (a.seam.tl.mats.getD i {}).k) := by
    unfold Sz.packedShape Sz.shapeNo
    rw [hM₀]
    show (Alg.symRows (Sz.ref.shape (Sz.ref.owner (.att g) μ).1 (Sz.ref.owner (.att g) μ).2).1,
        (Sz.ref.shape (Sz.ref.owner (.att g) μ).1 (Sz.ref.owner (.att g) μ).2).2) = _
    rw [eO, ← hm, ← hkk]
  rw [ePS] at hz
  have own : μ ≠ .qa → Sz.ref.owner (.att g) μ = (.att g, μ) := fun hq => by
    cases μ with
    | qa => exact absurd rfl hq
    | _ => rfl
  have hC : ∀ r, (rd v).cells.cell
      (_root_.Meaning.ownerK (_root_.Meaning.labAt (P5J.At.X Zp) (2 * g + 1) i))
      (Sz.ref.owner (.att g) μ).2.label r c =
      (rd v).cells.cell (2 * g + 1) (labelOf a.S i) r c := by
    intro r
    rw [labelOf_label eN hμ, k1, hrd v]
    by_cases hq : μ = .qa
    · subst hq
      exact hqa v hv r c
    · rw [own hq]
      rfl
  have main : ∀ {seat : MsgAddr → Option (ℕ × ℕ)} {heard : MsgAddr → ℕ},
      LaysFilling h Q Vd N rd seat heard
          (_root_.Meaning.ownerK (_root_.Meaning.labAt (P5J.At.X Zp) (2 * g + 1) i)) →
      Q.msg (P5J.At.num Zp
          (_root_.Meaning.ownerK (_root_.Meaning.labAt (P5J.At.X Zp) (2 * g + 1) i)) A.message) k v
          (hd.take (Q.fixedMsg
              (P5J.At.num Zp
              (_root_.Meaning.ownerK (_root_.Meaning.labAt (P5J.At.X Zp) (2 * g + 1) i))
              A.message))) false s.row s.place =
        Alg.pack (((VerifiableInference.Desc.First.Look.szOf a.seam.tl).rad : ℕ) : ℤ)
          (fun r : Fin (a.seam.tl.mats.getD i {}).m => OnBytes.Model.Reading.gl.val
              (cellAt a.S (2 * g + 1) (rd v).cells i r.val c)) i' := by
    intro seat heard L
    obtain ⟨hd', q⟩ := msg_of_lays L hA hlaid hz hi' hc k hv hN
    refine q.trans ?_
    rw [hname]
    exact cells_pack_label h.scope h.reads hX hg ha hμ hp (rd v) hd' hc hC i'
  by_cases hq : μ = .qa
  · refine main (seat := seat₀) (heard := heard₀) ?_
    rw [k1, hq]
    exact L0
  · refine main (seat := seat₁) (heard := heard₁) ?_
    rw [k1, own hq]
    exact L1

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.msg_of_lays
#print axioms ProofFile.Honest.K5.eSyms_of_lays
