-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AT ANY SCRIPT, UNDER THE LIBRARY's HEAD ON THE PUBLIC INPUT.
Johnson/Desc/ProofFile/Honest/K3/Term/PackedTraceCellsFromLaysFilling.lean: the honest side of the
kind "lookup" (K3): THE NAMED PREMISE `ScriptHoldsThePackedTraceCells`
(Honest/K3/Term/ScriptHoldsTheHonestValues.lean) AS THE END OF A LEMMA: from the senders' own sentence
on the `Script`'s messages, `LaysFilling` (Honest/K5/Law/LaysFilling.lean), at one link of whatever
sort (layers, attention, head), the planes' matrix included.

Why. The named premise speaks through the lookup's own reader of the witness. What another file
can be asked is a sentence on `Script.msg` alone. The way between the two is public, but for two
laws of the trace.

  `everyMatrixOfThePlanHasAName`        ON PUBLIC DATA: a number of the plan's list is a number of the
                                        filling's list of names
  `sizesOfThePlanAreTheFillings`        ON PUBLIC DATA: rows and columns, off the planes by the library,
                                        at the planes by the premise `planesSizes`
  `packedTraceCellsFromLaysFilling`     THE END, at integers that are a letter
  `labelOfTheNumberIsTheNamesLabel`, `cellsUnderTheirNamesAreTheCastsOfTheirIntegers`   on public data
  `packedCellsOfTheInputFromLaysFilling`   THE END AT THE CLOSED LETTER `traceMatricesOfTheCells`

How. It is `eSyms_of_lays`' road (LaysFilling.lean), general in the link: the seat, its room and its
number (`symbolsRoomAtEveryLink`, `seatNumberAtEveryLink`, Term/SymbolSeatsAtEveryLink.lean); `val_sym`
(Honest/K5/Law/CellsQRaw.lean); the owner's numbers (`ownerNumbersAtEveryLink`,
Term/OwnersOfTheMatricesAtEveryLink.lean); `msg_of_lays`; `cellsVals_size`, `cellsVals_pack`
(Honest/K5/Law/PackedVals.lean); `pack3_eq_pack` (Johnson/HonestTrace/Packed.lean); `Alg.pack_intCast`.

Limits. CONDITIONAL: the head; `oneAccepts`, `planesSizes` (public; premises here); `lays` (the
`Script`; NO FILE SHOWS IT OF ANY SCRIPT); `readersReadTheTrace`, `cellsAreTheIntegers`, `seams` (the
readers and the trace). The tail is `Meaning.tlAt`'s. The full size and the earlier hash alone.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.ScriptHoldsTheHonestValues
import Johnson.Desc.ProofFile.Honest.K3.Term.SymbolSeatsAtEveryLink
import Johnson.Desc.ProofFile.Honest.K3.Term.OwnersOfTheMatricesAtEveryLink
import Johnson.Desc.ProofFile.Honest.K5.Law.LaysFilling
import Johnson.Goal.HonestTrace.ShapesAtRefInScope
import Johnson.Goal.HonestTrace.FromCellsInScope
import Johnson.Desc.ProofFile.Honest.K3.Term.TraceMatricesOfTheCells

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open OnBytes.Model (HTailF2)
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz Seg MatName planeOf matAt_eq_some_iff nameNo_eq_some_iff nameNo_isSome
  no?_lt shapeNo_in_scope planMats planMats_eq shape_owner owner_owner below_of_mu ref_ok
  arrayNo_isSome_iff pack3 pack3_eq_pack)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First.Look (szOf valAt sigListCalls seatCalls)
open VerifiableInference.OnPublicFiles (attMs)
open ProofFile.Honest.FirstThread (Script)
open ProofFile.Honest.K1 (labelNo cellsVals)
open ProofFile.Honest.K5 (LaysFilling msg_of_lays val_sym msgNo5 cellsVals_size cellsVals_pack
  labelNo_arrayLabel)
open P5J (AtMgA TS CellsM)

local notation "PlaceL" => VerifiableInference.Desc.First.Look.Place

/-! ## 1 On public data -/

section scope
variable {Zl : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
  {X : OnBytes.Model.Verify.Public}

/-- **A number of the plan's list of matrices is a number of the filling's list of names.**
CONDITIONAL: the three premises on the public files; the link is below 25. -/
theorem everyMatrixOfThePlanHasAName (inScope : VerifierAndGoals.InScope Zl = true)
    (filesRead : VerifierAndGoals.readFiles Zl = .ok pp)
    (publicPartMade : OnBytes.Model.Verify.publicOf Zl.pol Zl.KL lay = .ok X) {link number : ℕ}
    (linkBelow : link < 25) (numberBelow : number < (_root_.Meaning.matsAt X link).size) :
    ∃ segment name, Sz.ref.matAt link number = some (segment, name) := by
  have C := OnBytes.Road.Hd.core_of_scope inScope filesRead publicPartMade
  have key : ∀ σ : Seg, σ.Below 12 → σ.no 12 = link → number < Sz.ref.len σ →
      ∃ segment name, Sz.ref.matAt link number = some (segment, name) := by
    intro σ hb hn hl
    obtain ⟨μ, hμ⟩ := nameNo_isSome Sz.ref hl
    refine ⟨σ, μ, (matAt_eq_some_iff Sz.ref _ _ _ _).2 ⟨hb, hn, ?_⟩⟩
    unfold Sz.mu
    rw [if_pos (show Seg.Below Sz.ref.nGr σ from hb)]
    exact (nameNo_eq_some_iff Sz.ref _ _ _).1 hμ
  by_cases h24 : link = 24
  · subst h24
    rw [_root_.Meaning.size_head publicPartMade C] at numberBelow
    exact key .head trivial rfl numberBelow
  · by_cases he : link % 2 = 0
    · obtain ⟨g, rfl⟩ : ∃ g, link = 2 * g := ⟨link / 2, by omega⟩
      have hg : g < 12 := by omega
      rw [_root_.Meaning.size_even publicPartMade C hg] at numberBelow
      exact key (.ff g) hg rfl numberBelow
    · obtain ⟨g, rfl⟩ : ∃ g, link = 2 * g + 1 := ⟨link / 2, by omega⟩
      have hg : g < 12 := by omega
      rw [_root_.Meaning.size_odd publicPartMade C hg] at numberBelow
      exact key (.att g) hg rfl numberBelow

/-- **The plan's record has the filling's rows and columns, at every matrix of the list.** Off the
planes: the library's `shapeNo_in_scope`. At the planes: the premise. -/
theorem sizesOfThePlanAreTheFillings (inScope : VerifierAndGoals.InScope Zl = true)
    (filesRead : VerifierAndGoals.readFiles Zl = .ok pp)
    (publicPartMade : OnBytes.Model.Verify.publicOf Zl.pol Zl.KL lay = .ok X) {link : ℕ}
    (planesSizes : ∀ number segment, Sz.ref.matAt link number = some (segment, planeOf segment) →
      (szOf (_root_.Meaning.tlAt X link)).m number = (Sz.ref.shapeNo link number).1 ∧
        (szOf (_root_.Meaning.tlAt X link)).k number = (Sz.ref.shapeNo link number).2)
    {number : ℕ} {segment : Seg} {name : MatName}
    (isTheMatrix : Sz.ref.matAt link number = some (segment, name)) :
    (szOf (_root_.Meaning.tlAt X link)).m number = (Sz.ref.shapeNo link number).1 ∧
      (szOf (_root_.Meaning.tlAt X link)).k number = (Sz.ref.shapeNo link number).2 := by
  by_cases hp : name = planeOf segment
  · subst hp
    exact planesSizes number segment isTheMatrix
  · obtain ⟨-, -, hm, hk⟩ := shapeNo_in_scope inScope filesRead publicPartMade isTheMatrix hp
    rw [planMats_eq] at hm hk
    exact ⟨hm, hk⟩

end scope

/-! ## 2 The end -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : PlaceL}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)

/-- **FROM THE SENDERS' SENTENCE TO THE LOOKUP's NAMED PREMISE**, at one link, of whatever sort. The
place x is read at its link alone. CONDITIONAL: under the head h; the link is below 25;
`oneAccepts`, `planesSizes`: on public data; `readersReadTheTrace`: the frame's reader of the cells is
`cells` of the input's trace; `cellsAreTheIntegers`: inside the sizes the cells under the link's
number and the matrix's own name are the casts of `traceMatrices` BY THE LINK's OWN LIST; `seams`:
inside the sizes the cells answer the same under the owner's link and name (for a matrix of the
link's own: nothing; for a borrowed one: a law of the trace); `lays`: the senders' sentence at the
owner's link of every matrix of the list. -/
theorem packedTraceCellsFromLaysFilling {x : PlaceL} (linkBelow : x.link < 25)
    (oneAccepts : h.oneC x.link = true)
    (planesSizes : ∀ number segment,
      Sz.ref.matAt x.link number = some (segment, planeOf segment) →
      (szOf (_root_.Meaning.tlAt (P5J.At.X Zp) x.link)).m number =
          (Sz.ref.shapeNo x.link number).1 ∧
        (szOf (_root_.Meaning.tlAt (P5J.At.X Zp) x.link)).k number =
          (Sz.ref.shapeNo x.link number).2)
    {valid : Local W₀ Rc ProofFile.Inst Tr → Prop} {challengesHeard : ℕ} {cells : Tr → Cells}
    {readers : Local W₀ Rc ProofFile.Inst Tr → Readers} {seat : ℕ → MsgAddr → Option (ℕ × ℕ)}
    {heard : ℕ → MsgAddr → ℕ} {traceMatrices : Local W₀ Rc ProofFile.Inst Tr → OnBytes.Road.Mats ℤ}
    (readersReadTheTrace : ∀ v, (readers v).cells = cells v.trace)
    (cellsAreTheIntegers : ∀ v, valid v → ∀ number segment name,
      Sz.ref.matAt x.link number = some (segment, name) →
      ∀ row column, row < (szOf (_root_.Meaning.tlAt (P5J.At.X Zp) x.link)).m number →
        column < (szOf (_root_.Meaning.tlAt (P5J.At.X Zp) x.link)).k number →
        (cells v.trace).cell x.link name.label row column =
          ((traceMatrices v number row column : ℤ) : Cb.Gl.F))
    (seams : ∀ v, valid v → ∀ number segment name,
      Sz.ref.matAt x.link number = some (segment, name) →
      ∀ row column, row < (szOf (_root_.Meaning.tlAt (P5J.At.X Zp) x.link)).m number →
        column < (szOf (_root_.Meaning.tlAt (P5J.At.X Zp) x.link)).k number →
        (cells v.trace).cell ((Sz.ref.owner segment name).1.no 12)
            (Sz.ref.owner segment name).2.label row column =
          (cells v.trace).cell x.link name.label row column)
    (lays : ∀ number segment name, Sz.ref.matAt x.link number = some (segment, name) →
      LaysFilling h Q valid challengesHeard readers
        (seat ((Sz.ref.owner segment name).1.no 12)) (heard ((Sz.ref.owner segment name).1.no 12))
        ((Sz.ref.owner segment name).1.no 12)) :
    ScriptHoldsThePackedTraceCells Q h.𝔇.sent h.𝔇.l3 valid challengesHeard x
      (_root_.Meaning.tlAt (P5J.At.X Zp) x.link) traceMatrices := by
  intro k v hd hv hN matrix column symbolRow
  have hX := h.pubOne
  have C := OnBytes.Road.Hd.core_of_scope h.scope h.reads hX
  -- the matrix has a name
  have hsize : matrix.val < (_root_.Meaning.matsAt (P5J.At.X Zp) x.link).size := by
    have e := _root_.Meaning.nm_of_core hX C linkBelow
    have hm : matrix.val < (_root_.Meaning.tlAt (P5J.At.X Zp) x.link).NM := matrix.isLt
    rw [e] at hm
    exact hm
  obtain ⟨σ, μ, hM⟩ := everyMatrixOfThePlanHasAName h.scope h.reads hX linkBelow hsize
  obtain ⟨hσ, hno, hmu⟩ := (matAt_eq_some_iff Sz.ref _ _ _ _).1 hM
  obtain ⟨em, ek⟩ := sizesOfThePlanAreTheFillings h.scope h.reads hX planesSizes hM
  have eS : Sz.ref.shapeNo x.link matrix.val = Sz.ref.shape σ μ := by
    unfold Sz.shapeNo
    rw [hM]
  rw [eS] at em ek
  -- the seat, its room, its number
  obtain ⟨s, hk, hs, h1, h2, hp⟩ := symbolsRoomAtEveryLink h linkBelow oneAccepts matrix.isLt
    symbolRow.val column.val symbolRow.isLt column.isLt
  obtain ⟨A, -, hA, hlaid, hnum⟩ := seatNumberAtEveryLink h linkBelow oneAccepts matrix.isLt
    symbolRow.isLt column.isLt hk hs
  show (valAt h.𝔇.sent.codes (sigListCalls h.𝔇.sent h.𝔇.l3.rad x.link)
    (seatCalls h.𝔇.sent x.link) (attMs x h.𝔇.sent h.𝔇.l3.rad
      (fun j => h.𝔇.l3.seat x.link false j.1) h.𝔇.l3.arr (Q.wit k v hd))
    (.cell ((_root_.Meaning.tlAt (P5J.At.X Zp) x.link).gtTree.getD matrix.val 0) symbolRow.val
      column.val)).getD 0 = _
  rw [val_sym hs h1 h2 hp _ _ (Q.wit k v hd)]
  show Q.msg (msgNo5 h x s.msg hk) k v (hd.take (Q.fixedMsg (msgNo5 h x s.msg hk))) false s.row
    s.place = _
  rw [hnum]
  -- the owner's numbers
  obtain ⟨k1, k2⟩ := ownerNumbersAtEveryLink h.scope h.reads hX hM
  obtain ⟨As, -, hf⟩ := Option.bind_eq_some_iff.1 hA
  have hname : A.name = _root_.Meaning.nameOf
      (_root_.Meaning.ownerA (_root_.Meaning.labAt (P5J.At.X Zp) x.link matrix.val)) := by
    simpa using List.find?_some hf
  have h9 : ∀ τ : Seg, Sz.ref.len τ ≤ 9 := fun τ => by
    cases τ with
    | ff _ => exact (by decide : 3 + 1 + 5 ≤ 9)
    | att _ => exact (by decide : 1 + 4 ≤ 9)
    | head => exact (by decide : 4 + 4 ≤ 9)
  have hlt : _root_.Meaning.ownerA (_root_.Meaning.labAt (P5J.At.X Zp) x.link matrix.val) < 26 := by
    have k3 := k2
    unfold Sz.mu at k3
    split_ifs at k3
    exact Nat.lt_of_lt_of_le (no?_lt Sz.ref k3) (Nat.le_trans (h9 _) (by decide))
  have hn : labelNo A.name = some
      (_root_.Meaning.ownerA (_root_.Meaning.labAt (P5J.At.X Zp) x.link matrix.val)) := by
    rw [hname]
    exact labelNo_arrayLabel hlt
  have hM₀ : Sz.ref.matAt
      (_root_.Meaning.ownerK (_root_.Meaning.labAt (P5J.At.X Zp) x.link matrix.val))
      (_root_.Meaning.ownerA (_root_.Meaning.labAt (P5J.At.X Zp) x.link matrix.val)) =
      some ((Sz.ref.owner σ μ).1, (Sz.ref.owner σ μ).2) := by
    rw [k1]
    exact (matAt_eq_some_iff Sz.ref _ _ _ _).2 ⟨below_of_mu (by rw [k2]; rfl), rfl, k2⟩
  have ho : (Sz.ref.arrayNo (Sz.ref.owner σ μ).1 (Sz.ref.owner σ μ).2).isSome = true :=
    (arrayNo_isSome_iff Sz.ref _ _).2 ⟨by rw [k2]; rfl, owner_owner Sz.ref σ μ⟩
  have hz := cellsVals_size Sz.ref hn hM₀ ho
  have eO := shape_owner Sz.ref ref_ok.1 σ μ (by rw [hmu]; rfl)
  have ePS : Sz.ref.packedShape
      (_root_.Meaning.ownerK (_root_.Meaning.labAt (P5J.At.X Zp) x.link matrix.val))
      (_root_.Meaning.ownerA (_root_.Meaning.labAt (P5J.At.X Zp) x.link matrix.val)) =
      (Alg.symRows ((szOf (_root_.Meaning.tlAt (P5J.At.X Zp) x.link)).m matrix.val),
        (szOf (_root_.Meaning.tlAt (P5J.At.X Zp) x.link)).k matrix.val) := by
    unfold Sz.packedShape Sz.shapeNo
    rw [hM₀]
    show (Alg.symRows (Sz.ref.shape (Sz.ref.owner σ μ).1 (Sz.ref.owner σ μ).2).1,
        (Sz.ref.shape (Sz.ref.owner σ μ).1 (Sz.ref.owner σ μ).2).2) = _
    rw [eO, ← em, ← ek]
  rw [ePS] at hz
  -- the senders' sentence, at the owner's link
  have L := lays matrix.val σ μ hM
  rw [← k1] at L
  obtain ⟨hd', q⟩ := msg_of_lays L hA hlaid hz symbolRow.isLt column.isLt k hv hN
  refine q.trans ?_
  have hc₀ : column.val < (Sz.ref.shape (Sz.ref.owner σ μ).1 (Sz.ref.owner σ μ).2).2 := by
    rw [eO, ← ek]
    exact column.isLt
  rw [cellsVals_pack Sz.ref (readers v) hd' hn hM₀ hc₀ symbolRow.val]
  -- the packing
  have eR : (((szOf (_root_.Meaning.tlAt (P5J.At.X Zp) x.link)).rad : ℕ) : ℤ) = 2 ^ 20 := by
    show ((2 ^ 20 : ℕ) : ℤ) = 2 ^ 20
    norm_num
  have em₀ : (Sz.ref.shape (Sz.ref.owner σ μ).1 (Sz.ref.owner σ μ).2).1 =
      (szOf (_root_.Meaning.tlAt (P5J.At.X Zp) x.link)).m matrix.val := by rw [eO, ← em]
  rw [eR]
  refine ((pack3_eq_pack _ (fun r => algebraMap Cb.Gl.F Cb.Gl.E ((readers v).cells.cell
    (_root_.Meaning.ownerK (_root_.Meaning.labAt (P5J.At.X Zp) x.link matrix.val))
    (Sz.ref.owner σ μ).2.label r column.val)) symbolRow.val).symm.trans ?_)
  rw [em₀, pack3_eq_pack, ← Alg.pack_intCast]
  have key : (fun r : Fin ((szOf (_root_.Meaning.tlAt (P5J.At.X Zp) x.link)).m matrix.val) =>
      algebraMap Cb.Gl.F Cb.Gl.E ((readers v).cells.cell
        (_root_.Meaning.ownerK (_root_.Meaning.labAt (P5J.At.X Zp) x.link matrix.val))
        (Sz.ref.owner σ μ).2.label r.val column.val)) =
      fun r => ((traceMatrices v matrix.val r.val column.val : ℤ) : Cb.Gl.E) := by
    funext row
    have e1 := seams v hv matrix.val σ μ hM row.val column.val row.isLt column.isLt
    have e2 := cellsAreTheIntegers v hv matrix.val σ μ hM row.val column.val row.isLt column.isLt
    rw [readersReadTheTrace v, k1, e1, e2, map_intCast]
  exact congrArg (fun f : Fin ((szOf (_root_.Meaning.tlAt (P5J.At.X Zp) x.link)).m matrix.val) →
    Cb.Gl.E => Alg.pack (2 ^ 20) f symbolRow.val) key

/-! ## 3 At the closed letter: the integers read off the input's own cells -/

/-- **ON PUBLIC DATA: the library's label of a number of a link's list is the label of the filling's
name with that number.** CONDITIONAL: the public part's numbers of parts are 3, 1, 1, 4. -/
theorem labelOfTheNumberIsTheNamesLabel {X : OnBytes.Model.Verify.Public}
    (partsFit : OnBytes.HonestTrace.PartsFit X) {link number : ℕ} {segment : Seg} {name : MatName}
    (isTheMatrix : Sz.ref.matAt link number = some (segment, name)) :
    OnBytes.HonestTrace.labelAt X link number = some name.label := by
  obtain ⟨hb, hno, hmu⟩ := (matAt_eq_some_iff Sz.ref _ _ _ _).1 isTheMatrix
  have hb' : segment.Below 12 := hb
  have hno' : segment.no 12 = link := hno
  have hσ : Seg.ofNo 12 link = some segment := by
    rw [← hno']
    exact Seg.ofNo_no hb'
  have hn : MatName.no? 3 1 1 4 segment name = some number := by
    unfold Sz.mu at hmu
    rw [if_pos hb] at hmu
    exact hmu
  have hlen : number < (MatName.all 3 1 1 4 segment).length := by
    have hl : number < Sz.ref.len segment := no?_lt Sz.ref hn
    cases segment with
    | ff _ => exact hl
    | att _ => exact hl
    | head => exact hl
  have hget : (MatName.all 3 1 1 4 segment)[number]? =
      some ((MatName.all 3 1 1 4 segment)[number]'hlen) := List.getElem?_eq_getElem hlen
  have e := MatName.no?_inj (OnBytes.HonestTrace.all_no_ref segment hget) hn
  unfold OnBytes.HonestTrace.labelAt
  rw [hσ]
  show ((MatName.all (X.y.parts.getD 0 0) (X.y.parts.getD 1 0)
    (OnBytes.Road.Hd.shapeA X (link / 2)).cf.NAs X.hS.NHf segment)[number]?).map MatName.label = _
  rw [(OnBytes.HonestTrace.parts_at partsFit hσ).1, hget, e]
  rfl

/-- **Every reader of cells answers, under a matrix's own name, the cast of the integer that is read
off it**: no law of the trace. -/
theorem cellsUnderTheirNamesAreTheCastsOfTheirIntegers {X : OnBytes.Model.Verify.Public}
    (partsFit : OnBytes.HonestTrace.PartsFit X) (cell : ℕ → String → ℕ → ℕ → Cb.Gl.F)
    {link number : ℕ} {segment : Seg} {name : MatName}
    (isTheMatrix : Sz.ref.matAt link number = some (segment, name)) (row column : ℕ) :
    cell link name.label row column =
      ((traceMatricesOfTheCells X cell link number row column : ℤ) : Cb.Gl.F) := by
  unfold traceMatricesOfTheCells
  rw [labelOfTheNumberIsTheNamesLabel partsFit isTheMatrix]
  exact (ZMod.coe_valMinAbs _).symm

/-- **THE NAMED PREMISE AT THE CLOSED LETTER, FROM THE SENDERS' SENTENCE.** The integers are those read
off the input's own cells (`traceMatricesOfTheCells`); the test "one" is paid from the head. LEFT AS
PREMISES: `planesSizes` (public), `readersReadTheTrace`, `seams` (the trace), `lays` (the `Script`). -/
theorem packedCellsOfTheInputFromLaysFilling {x : PlaceL} (linkBelow : x.link < 25)
    (planesSizes : ∀ number segment,
      Sz.ref.matAt x.link number = some (segment, planeOf segment) →
      (szOf (_root_.Meaning.tlAt (P5J.At.X Zp) x.link)).m number =
          (Sz.ref.shapeNo x.link number).1 ∧
        (szOf (_root_.Meaning.tlAt (P5J.At.X Zp) x.link)).k number =
          (Sz.ref.shapeNo x.link number).2)
    {valid : Local W₀ Rc ProofFile.Inst Tr → Prop} {challengesHeard : ℕ} {cells : Tr → Cells}
    {readers : Local W₀ Rc ProofFile.Inst Tr → Readers} {seat : ℕ → MsgAddr → Option (ℕ × ℕ)}
    {heard : ℕ → MsgAddr → ℕ}
    (readersReadTheTrace : ∀ v, (readers v).cells = cells v.trace)
    (seams : ∀ v, valid v → ∀ number segment name,
      Sz.ref.matAt x.link number = some (segment, name) →
      ∀ row column, row < (szOf (_root_.Meaning.tlAt (P5J.At.X Zp) x.link)).m number →
        column < (szOf (_root_.Meaning.tlAt (P5J.At.X Zp) x.link)).k number →
        (cells v.trace).cell ((Sz.ref.owner segment name).1.no 12)
            (Sz.ref.owner segment name).2.label row column =
          (cells v.trace).cell x.link name.label row column)
    (lays : ∀ number segment name, Sz.ref.matAt x.link number = some (segment, name) →
      LaysFilling h Q valid challengesHeard readers
        (seat ((Sz.ref.owner segment name).1.no 12)) (heard ((Sz.ref.owner segment name).1.no 12))
        ((Sz.ref.owner segment name).1.no 12)) :
    ScriptHoldsThePackedTraceCells Q h.𝔇.sent h.𝔇.l3 valid challengesHeard x
      (_root_.Meaning.tlAt (P5J.At.X Zp) x.link)
      (fun v => traceMatricesOfTheCells (P5J.At.X Zp) (cells v.trace).cell x.link) :=
  packedTraceCellsFromLaysFilling h Q linkBelow (oneNumberTestAcceptsAtEveryLink h linkBelow)
    planesSizes readersReadTheTrace
    (fun v _ _ _ _ isTheMatrix row column _ _ =>
      cellsUnderTheirNamesAreTheCastsOfTheirIntegers
        (OnBytes.HonestTrace.partsFit_in_scope h.scope h.reads h.pubOne) (cells v.trace).cell
        isTheMatrix row column)
    seams lays

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.everyMatrixOfThePlanHasAName
#print axioms ProofFile.Honest.K3.Term.sizesOfThePlanAreTheFillings
#print axioms ProofFile.Honest.K3.Term.packedTraceCellsFromLaysFilling
#print axioms ProofFile.Honest.K3.Term.labelOfTheNumberIsTheNamesLabel
#print axioms ProofFile.Honest.K3.Term.cellsUnderTheirNamesAreTheCastsOfTheirIntegers
#print axioms ProofFile.Honest.K3.Term.packedCellsOfTheInputFromLaysFilling
