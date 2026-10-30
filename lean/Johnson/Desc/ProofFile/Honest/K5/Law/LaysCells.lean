-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/LaysCells.lean: THE PREMISE's FORM "THE SCRIPT LAYS THE
FILLING", NARROWED OFF THE PLANES AND SPELLED AS THE FRAME's FORM "OWN ENTRIES OF A MESSAGE"
(`OwnMsgs`, Johnson/Desc/ProofFile/Honest/Thread/ScriptLots.lean); AND THE CELLS' EQUATION FROM IT.
IT PAYS NOTHING OF THE SCRIPT: it moves the debt. CONDITIONAL: under the hypothesis h, the library's
head on the public input (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean). GENERAL IN THE SIZES S of the
filling, under one public premise, hSz: `planesAtRef S = Sz.ref` (SizesOffPlanes.lean in this
folder: met at `Sz.ref`, and at `Sz.ofPublic X` in the goals' scope). Four definitions, one of them
a premise's form; four theorems.

WHICH FORM IS THE ONE TO PAY. `LaysCells`, of this file. `LaysFilling` (LaysFilling.lean in this
folder) stays as the stronger one at `Sz.ref`: it asks the same at the planes' arrays too, which the
cells' equation never reads, and `laysCells_of_laysFilling` proves that it gives this one.

Main names:
  `LaysCells h Q S Vd N rd seat heard l`: THE FORM, at one segment. reach, on public data: the
    message of each array off the planes that the values have is seated. lays, on the Script: for
    each address seated at (l, m): `OwnMsgs` at n := `P5J.At.num Zp l m`, fx := `heard Ad`, txt :=
    `fillTxt`.
  `fillTxt S codes s ly rd seat heard Ad l m`: THE TEXT THAT WOULD BE HANDED IN AS A LOT's:
     "none" in the mask table; "none" where the way back finds no array, or a plane's; else
    what the filling's call that asks first answers at the sizes S, read into the extension field.
  `offPlanes l name`: a test with code on public data: the name is not the label of a matrix of
    planes (b, bA, bH) of segment l. True also at a name that is no matrix's label.
  `eSyms_of_laysCells`: **THE CELLS' EQUATION (`ESymsRaw`) FROM THE FORM AT THE TWO SEGMENTS**: the
    statement of `eSyms_of_lays` with the form's name turned, the sizes' letter S in the form, and
    ONE PREMISE MORE, hSz. Its end is the same.
  `msg_of_laysCells`: what the form gives at one element that the layout's rule lays.
    `fillTxt_isSome`: THE TEXT ANSWERS JUST WHERE `fillAnswers`, a test on public data and the
    number of challenges, says so: no premise.

How. `eSyms_of_laysCells` HAS THE PROOF OF `eSyms_of_lays`, line for line, but for two lines turned
and one fact added: the array that the proof meets lies off the planes. `msg_of_laysCells`:
`laidData_ask`, `laidBack_of_laidAt` (WayBackFill.lean, WayBack.lean) and `ask_take` (AskTake.lean
in this folder): the call does not read beyond the challenges heard when the sending begins; and
`ask_off_planes` (SizesOffPlanes.lean): off the planes the call at S is the call at `Sz.ref`.

Limits. Nothing here proves that a Script meets the form. NOTHING AT A PLANE's ARRAY. One S for both
segments. reach and `offPlanes` are public tests at `Sz.ref`: they say which arrays are asked. The
small example's sizes do not meet hSz. As the text of a lot `fillTxt` makes sense at an address that
is seated at (l, m) alone. The premises of `eSyms_of_laysCells` on the readers (hrd, hqa) are proved
nowhere. Through its imports it stands above Cb/Bridge/CodeListRSProved.lean, and so above the files
under ThirdParty/ (lean/LIMITS.md, L15): a fact on import lines. At the earlier hash
`OnBytes.secondHashFunction`, a fixed function.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.LaysFilling
import Johnson.Desc.ProofFile.Honest.K5.Law.AskTake
import Johnson.Desc.ProofFile.Honest.K5.Law.SizesOffPlanes
import Johnson.Desc.ProofFile.Honest.Thread.ScriptLots

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz Seg MatName nameNo_isSome nameNo_eq_some_iff matAt_eq_some_iff no?_lt
  parts_in_scope shape_owner owner_owner below_of_mu ref_ok arrayNo_isSome_iff)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First.Look (lookAt)
open ProofFile.Honest.FirstThread (Script OwnMsgs)
open ProofFile.Honest.K1 (labelNo cellsVals firstData)
open P5J (AtMgA TS CellsM)

/-- **Off the planes**: a test with code on public data. True also where the name is no matrix's
label, or its number has no matrix in segment l. -/
def offPlanes (l : ℕ) (name : String) : Bool :=
  (labelNo name).all fun mu => (Sz.ref.matAt l mu).all fun x =>
    decide (x.2 ≠ .b ∧ x.2 ≠ .bA ∧ x.2 ≠ .bH)

/-- **The filling's own entries of message m of segment l, off the planes**: the text of a lot, with
n := `P5J.At.num Zp l m` and fx := `heard Ad`, at an address Ad that is seated at (l, m). -/
def fillTxt {Bk : ProverCoinCounts} {W : Type} (S : Sz) (codes : OnBytes.Codes)
    (s : OnBytes.Params.ReqShape)
    (ly : OnBytes.Params.ReqLayout) (rd : W → Readers) (seat : MsgAddr → Option (ℕ × ℕ))
    (heard : MsgAddr → ℕ) (Ad : MsgAddr) (l m : ℕ) :
    Coins Bk → W → List Fmt.Drawn → Bool → ℕ → ℕ → Option OnBytes.Slice.GE :=
  fun _ v hd mask row place =>
    if mask then none
    else
      match laidBack ly l m row place with
      | some (A, _, _) =>
        if offPlanes l A.name then
          match (firstData S codes s ly seat heard).ask (rd v) hd Ad row place with
          | .ok (some y) => some (asE (some y))
          | _ => none
        else none
      | none => none

/-- **Where the filling's text answers**: a test with code on public data. n: how many challenges
stand in the list at which the text is called. It reads the filling's three public parts, which take
no reader and no coin. -/
def fillAnswers (S : Sz) (codes : OnBytes.Codes) (s : OnBytes.Params.ReqShape)
    (ly : OnBytes.Params.ReqLayout) (seat : MsgAddr → Option (ℕ × ℕ)) (heard : MsgAddr → ℕ)
    (Ad : MsgAddr) (l m n : ℕ) (mask : Bool) (row place : ℕ) : Bool :=
  !mask && (laidBack ly l m row place).any (fun x => offPlanes l x.1.name) &&
    (firstData S codes s ly seat heard).heardOk Ad n &&
    (firstData S codes s ly seat heard).ready [] Ad &&
    (firstData S codes s ly seat heard).lays Ad row place

/-- **THE FILLING's TEXT ANSWERS JUST WHERE THAT TEST SAYS SO**: whatever the readers, the run's
coins and the input; of the challenges their number alone is read. No premise. -/
theorem fillTxt_isSome {Bk : ProverCoinCounts} {W : Type} (S : Sz) (codes : OnBytes.Codes)
    (s : OnBytes.Params.ReqShape) (ly : OnBytes.Params.ReqLayout) (rd : W → Readers)
    (seat : MsgAddr → Option (ℕ × ℕ)) (heard : MsgAddr → ℕ) (Ad : MsgAddr) (l m : ℕ)
    (k : Coins Bk) (v : W) (hd : List Fmt.Drawn) (mask : Bool) (row place : ℕ) :
    (fillTxt S codes s ly rd seat heard Ad l m k v hd mask row place).isSome =
      fillAnswers S codes s ly seat heard Ad l m hd.length mask row place := by
  have hr : (firstData S codes s ly seat heard).ready
      (hd.take ((firstData S codes s ly seat heard).heardAt Ad)) Ad =
      (firstData S codes s ly seat heard).ready [] Ad := rfl
  cases mask with
  | true => simp [fillTxt, fillAnswers]
  | false =>
    unfold fillTxt fillAnswers
    cases hB : laidBack ly l m row place with
    | none => simp
    | some x =>
      obtain ⟨A, i, c⟩ := x
      cases hO : offPlanes l A.name with
      | false => simp [hO]
      | true =>
        unfold RowData.ask RowData.at_
        rw [hr]
        cases h1 : (firstData S codes s ly seat heard).heardOk Ad hd.length <;>
        cases h2 : (firstData S codes s ly seat heard).ready [] Ad <;>
        cases h3 : (firstData S codes s ly seat heard).lays Ad row place <;>
        simp [hO]

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)

/-- **THE SCRIPT LAYS THE FILLING OFF THE PLANES, AT ONE SEGMENT**: a premise's form, in the frame's
own form. It is a definition: nothing is claimed of it, and nothing here proves that it can be met.
-/
structure LaysCells (S : Sz) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (N : Nat)
    (rd : Local W₀ Rc ProofFile.Inst Tr → Readers) (seat : MsgAddr → Option (Nat × Nat))
    (heard : MsgAddr → Nat) (l : Nat) : Prop where
  /-- ON PUBLIC DATA: the message of each array of segment l off the planes that the values have is
  seated at an address whose sending begins when no more than N challenges have been heard -/
  reach : ∀ (As : List OnBytes.Params.ReqArray) (A : OnBytes.Params.ReqArray),
    h.𝔇.sent.layout.link[l]? = some As → A ∈ As → offPlanes l A.name = true →
    ((cellsVals Sz.ref).size l A.name).isSome = true →
    ∃ Ad : MsgAddr, seat Ad = some (l, A.message) ∧ heard Ad ≤ N
  /-- ON THE SCRIPT: the frame's form at the filling's text, for each address seated in segment l -/
  lays : ∀ (Ad : MsgAddr) (m : Nat), seat Ad = some (l, m) →
    OwnMsgs Q Vd N (P5J.At.num Zp l m) (heard Ad)
      (fillTxt S h.𝔇.sent.codes h.𝔇.sent.shape h.𝔇.sent.layout rd seat heard Ad l m)

variable {h Q}

/-- **The form at all arrays gives this one, at `Sz.ref`.** -/
theorem laysCells_of_laysFilling {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : ℕ}
    {rd : Local W₀ Rc ProofFile.Inst Tr → Readers} {seat : MsgAddr → Option (ℕ × ℕ)}
    {heard : MsgAddr → ℕ} {l : ℕ} (L : LaysFilling h Q Vd N rd seat heard l) :
    LaysCells h Q Sz.ref Vd N rd seat heard l := by
  refine ⟨fun As A hl hA _ hz => L.reach As A hl hA hz, fun Ad m hAd => ?_⟩
  intro k w hd hv hN mask row place y₁ hy
  unfold fillTxt at hy
  split at hy
  · cases hy
  · rename_i hm
    have em : mask = false := by simpa using hm
    subst em
    split at hy
    · split at hy
      · split at hy
        · rename_i y hq
          have q := (ask_take _ (rd w) hd Ad row place).symm.trans hq
          rw [← Option.some.inj hy]
          exact L.lays k w hd hv hN Ad m hAd row place y q
        · cases hy
      · cases hy
    · cases hy

/-- **What the form gives at one element that the layout's rule lays.** CONDITIONAL: under the
hypothesis h; hSz; L: the form at segment l; A is an array of segment l, off the planes; hn, hM name
the matrix that A's name labels: NO NEW DEBT: they follow from hz; the rule lays (i', c) of A at p;
the values have A, and (i', c) lies inside the size that they say; the input meets Vd; at least N
challenges have been heard. -/
theorem msg_of_laysCells {S : Sz} (hSz : planesAtRef S = Sz.ref)
    {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : ℕ}
    {rd : Local W₀ Rc ProofFile.Inst Tr → Readers} {seat : MsgAddr → Option (ℕ × ℕ)}
    {heard : MsgAddr → ℕ} {l : ℕ} (L : LaysCells h Q S Vd N rd seat heard l) {n : String}
    {A : OnBytes.Params.ReqArray}
    (hA : VerifiableInference.Desc.arrayOf h.𝔇.sent.layout l n = some A)
    (hO : offPlanes l A.name = true) {mu : ℕ} {σ : Seg} {μ : MatName}
    (hn : labelNo A.name = some mu) (hM : Sz.ref.matAt l mu = some (σ, μ)) {i' c : ℕ} {p : ℕ × ℕ}
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
  obtain ⟨Ad, hAd, hh⟩ := L.reach As A hl (List.mem_of_find?_eq_some hf) hO (by rw [hz]; rfl)
  have q := laidData_ask okS ok hA hp heard hAd hz hi hc (rd v) (hd := hd) (Nat.le_trans hh hN) rfl
  have hB := laidBack_of_laidAt ok hA hp
  have q' : (firstData Sz.ref h.𝔇.sent.codes h.𝔇.sent.shape h.𝔇.sent.layout seat heard).ask (rd v)
      (hd.take (heard Ad)) Ad p.1 p.2 =
      .ok (some ((cellsVals Sz.ref).val (rd v) (hd.take (heard Ad)) l A.name i' c)) :=
    (ask_take _ (rd v) hd Ad p.1 p.2).trans q
  have hne : μ ≠ .b ∧ μ ≠ .bA ∧ μ ≠ .bH := by
    have hO' := hO
    simp only [offPlanes, hn, hM, Option.all_some] at hO'
    exact of_decide_eq_true hO'
  have qS : (firstData S h.𝔇.sent.codes h.𝔇.sent.shape h.𝔇.sent.layout seat heard).ask (rd v)
      (hd.take (heard Ad)) Ad p.1 p.2 =
      .ok (some ((cellsVals Sz.ref).val (rd v) (hd.take (heard Ad)) l A.name i' c)) :=
    (ask_off_planes hSz h.𝔇.sent.codes h.𝔇.sent.shape h.𝔇.sent.layout seat heard hAd hB hn hM hne.1
      hne.2.1 hne.2.2 (rd v) (hd.take (heard Ad))).trans q'
  refine ⟨hd.take (heard Ad), L.lays Ad A.message hAd k v hd hv hN false p.1 p.2 _ ?_⟩
  unfold fillTxt
  simp only [Bool.false_eq_true, if_false, hB, hO, if_true, qS]

/-- **THE CELLS' EQUATION FROM THE FORM AT THE TWO SEGMENTS.** CONDITIONAL: under the hypothesis h;
hSz; g is below 12; a is the group's plan; x₁ is the place of the segment's lookup on the calls; hS,
hL: the seat's shape and segment are the plan's; hrd: the frame's reader of the cells is this
kind's; hqa: THE READER ANSWERS FOR qa THE SAME UNDER BOTH SEGMENTS' NUMBERS; L0, L1: THE FORM at
the group's feed-forward segment and at the attention segment. It moves the debt: none of these is
proved here. -/
theorem eSyms_of_laysCells {S : Sz} (hSz : planesAtRef S = Sz.ref) {g : ℕ} (hg : g < 12)
    {a : OnBytes.Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {x₁ : VerifiableInference.Desc.First.Look.Place}
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁)
    {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : ℕ} {cells : Tr → Cells} {Z5 : Seat5}
    {rd : Local W₀ Rc ProofFile.Inst Tr → Readers} {seat₀ seat₁ : MsgAddr → Option (ℕ × ℕ)}
    {heard₀ heard₁ : MsgAddr → ℕ} (hS : Z5.P.S = a.S) (hL : Z5.link = 2 * g + 1)
    (hrd : ∀ v, (rd v).cells = cells v.trace)
    (hqa : ∀ v, Vd v → ∀ r c, (cells v.trace).cell (2 * g) "qa" r c = (cells v.trace).cell
        (2 * g + 1) "qa" r c)
    (L0 : LaysCells h Q S Vd N rd seat₀ heard₀ (2 * g))
    (L1 : LaysCells h Q S Vd N rd seat₁ heard₁ (2 * g + 1)) : ESymsRaw h Q Vd N x₁ a cells Z5 := by
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
  have hO : offPlanes (_root_.Meaning.ownerK (_root_.Meaning.labAt (P5J.At.X Zp) (2 * g + 1) i))
      A.name = true := by
    simp only [offPlanes, hn, hM₀, Option.all_some]
    refine decide_eq_true ?_
    by_cases hq : μ = .qa
    · subst hq
      exact ⟨show MatName.qa ≠ .b by decide, show MatName.qa ≠ .bA by decide,
        show MatName.qa ≠ .bH by decide⟩
    · rw [own hq]
      refine ⟨?_, hp, ?_⟩
      · rintro rfl
        have e : (none : Option ℕ) = some i := (nameNo_eq_some_iff Sz.ref _ _ _).1 hμ
        cases e
      · rintro rfl
        have e : (none : Option ℕ) = some i := (nameNo_eq_some_iff Sz.ref _ _ _).1 hμ
        cases e
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
      LaysCells h Q S Vd N rd seat heard
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
    obtain ⟨hd', q⟩ := msg_of_laysCells hSz L hA hO hn hM₀ hlaid hz hi' hc k hv hN
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

#print axioms ProofFile.Honest.K5.fillTxt_isSome
#print axioms ProofFile.Honest.K5.laysCells_of_laysFilling
#print axioms ProofFile.Honest.K5.msg_of_laysCells
#print axioms ProofFile.Honest.K5.eSyms_of_laysCells
