-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K1/Law/TieMatSeats.lean: THE PLAN's HALF OF THE SEATS OF THE MATRICES AT
THE READS OF EACH SEGMENT: where each matrix that a segment reads lies, as public data alone, under
the library's head. A trial.

  ownW, nmW               each matrix's owner (segment, matrix) and each segment's number of matrices
  dW                      the written data of the plan's term whereIsP
  rowW                    the one test on written data at a segment and a matrix
  tieRows_written         Lean's kernel: rowW at all 176 (12 x 9 + 12 x 5 + 8)
  tie_bites               negative tests
  laidIn_bound, room_of_blocks   a law: the blocks' test gives every cell of the array
  ownerOf_W, nm_W, pair_W under the head: the library's terms are these written ones
  tieSeats_head           the statement

Under the head every term of the statement is carried to its written value: P5J.At.ms by
seats_in_scope and memsSame_atR (ms_seat); P5J.At.arr and P5J.At.num by seats_in_scope and arrOf_is_num;
P5J.At.cs by likeFull_in_scope; h.𝔇.layout by layout_in_scope; h.𝔇.shape by hDsh_atAll;
h.𝔇.pubD.d3.arrayOf by names_tie_all with owner_label (pair_W); h.𝔇.pubD.dS by dS_W;
Meaning.tlAt by nm_W (its number alone; its gtTree is read through pair_W). The first pin is
pin1_atAll, the cut hc_at_laid: no premise.

Limits. Public data alone: nothing on a run, a state or a witness. The full size alone. Nothing on
soundness, completeness or hiding.
-/
import Johnson.P2LawR.NamesTieAll
import Johnson.Desc.AtSeats.FirstSeatedAtReads
import Johnson.Desc.AtSeats.SymsLayAtAll
import Johnson.Desc.AtSeats.K13KindRowB
import Johnson.Desc.K1.Law.ArmSyms
import Johnson.Desc.K1.Law.TestsAtAll
import Johnson.Desc.LaidAt
import Johnson.Desc.SeatAt
import Johnson.HonestTrace.Packed
import Johnson.P5T.NumOfPlan
import Johnson.P5T.MembersByMake
import Johnson.P5T.PlanSeatsTie
import Johnson.P5J.LettersAt
import Johnson.Desc.ProofFile.Honest.K1.FirstData
import Johnson.Desc.ProofFile.Honest.K2.Law.LabelByList
import Johnson.P5J.AtMg
import Johnson.P5J.MgAtAll
import Johnson.Desc.K1.Law.PinsAtHead
import Johnson.Desc.AtSeats.K13PlanM3At
import Johnson.Desc.First.Close.Law.HingeMore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Params VerifiableInference.Desc
open VerifiableInference.Desc.K1 (symsSeatedB firstOrKeptB numsW)
open VerifiableInference.Desc.First.FillSent
open VerifiableInference.Desc.First (flatPlacesOf shift S)
open VerifiableInference.Desc.Sound (linksFull Mem seatOf)
open VerifiableInference.PlanWritten (proofSizedFull madePinnedAt)
open Johnson.G (layoutFull codesFull2)
open OnBytes.HonestTrace (Sz Seg MatName)
open P5T (psFull seatsAllFull)
open OnBytes.Maker (WholeD)

/-- Each matrix's owner: its segment and its number there. -/
def ownW (l ν : ℕ) : ℕ × ℕ :=
  if l = 24 then (if ν = 7 then (22, 7) else (24, ν))
  else if l % 2 = 1 then (if ν = 4 then (l - 1, 6) else (l, ν))
  else if ν = 8 ∧ 0 < l then (l - 2, 7) else (l, ν)

/-- Each segment's number of matrices. -/
def nmW (l : ℕ) : ℕ := if l = 24 then 8 else if l % 2 = 1 then 5 else 9

/-- The written data of the plan's term. -/
abbrev dW : SentData :=
  sentDataOf proofSizedFull.request (fun m => numsW.msgsAt ((flatPlacesOf linksFull true).find? fun p =>
    p.link == some m && p.piece == 1 + ((linksFull[m]?).map shift).getD 0)) fun _ => []

/-- The array of a matrix, at the written layout. -/
def arrW (l ν : ℕ) : Option ReqArray :=
  reqArray layoutFull (ownW l ν).1 (_root_.Meaning.nameOf (ownW l ν).2)

/-- A block of an array lies in the message's main rows and off its pad. -/
def blockRoomB (cs : Codes) (sh : OracleShape) (b : LaidBlock) : Bool :=
  decide (b.firstRow + 2 ^ b.rowBits ≤ sh.mainRows) &&
    (sh.maskRows != 0 || decide (b.firstRow + 2 ^ b.rowBits < sh.mainRows) ||
      decide (b.firstPlace + 2 ^ b.placeBits + (if sh.mainDeg = 3 then 1 else 3) ≤
        (cs.base.getD sh.code default).ell))

/-- A seat is a sampled message's, and every sampled message there has that shape. -/
def seatIsB (q : ℕ × ℕ) (sh : OracleShape) : Bool :=
  ((psFull.filter (·.smpd)).any fun p => decide (p.seat = q)) &&
    (psFull.filter (·.smpd)).all fun p => !decide (p.seat = q) || decide (p.shape = sh)

/-- The first holder of a seat in the whole list is the message k of segment l₀. -/
def keyB (q : ℕ × ℕ) (l₀ k : ℕ) : Bool :=
  (seatsAllFull.find? fun r => r.j == q.1 && r.t == q.2).any fun p =>
    decide (P5T.keyOf p = (0, l₀, k))

/-- Each matrix's owner is the one that the trace's numbering names. -/
def ownerRowB (l ν : ℕ) (a : ReqArray) : Bool :=
  (Seg.ofNo 12 l).any fun σ => decide (σ.Below 12) && decide (σ.no 12 = l) &&
    ((MatName.all 3 1 1 4 σ)[ν]?).any fun μ =>
      decide (Sz.ref.matAt (ownW l ν).1 (ownW l ν).2 = some (Sz.ref.owner σ μ)) &&
      decide ((ownW l ν).1 = (Sz.ref.owner σ μ).1.no 12) && decide ((ownW l ν).1 < 25) &&
      decide (VerifiableInference.Desc.arrayOf layoutFull (ownW l ν).1 a.name = some a) &&
      decide (K2.Law.labelNoL a.name = some (ownW l ν).2) &&
      decide ((Sz.ref.packedShape l ν).1 ≤ a.sizeI) && decide ((Sz.ref.packedShape l ν).2 ≤ a.sizeC)

/-- **The one test** at segment l and matrix ν. -/
def rowW (l ν : ℕ) : Bool :=
  (arrW l ν).any fun a =>
    firstOrKeptB VerifiableInference.Desc.ReqLit.shapeFull l (ownW l ν).1 a.message &&
    ownerRowB l ν a &&
    (whereIsP dW l (ownW l ν).1 a.message).any fun o =>
      (K13.Law.LFull.places[o]?).any fun q => (K13.Law.MFull[o]?).any fun sh =>
        seatIsB q sh &&
        laidMatrixOk a (ceilLog2 (sh.rows Part.main))
          (if sh.rows Part.main == 0 then 0 else (codesFull2.base.getD sh.code default).logEll) &&
        keyB q (ownW l ν).1 a.message &&
        decide (Sz.ref.packedShape l ν = Sz.ref.packedShape (ownW l ν).1 (ownW l ν).2) &&
        a.blocks.all (blockRoomB codesFull2 sh)

set_option maxRecDepth 1000000 in
/-- **Lean's kernel, on the written data.** -/
theorem tieRows_written : ((List.range 25).all fun l => (List.range (nmW l)).all (rowW l)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **Each clause of the test can fail.** A matrix that the list does not have; a seat's key at another
message; a shape one row short of the blocks; another shape at a seat; another owner's array; a table
too small; two matrices of different sizes; a message that the segment neither sends nor keeps. -/
theorem tie_bites : rowW 0 9 = false ∧ keyB (0, 1) 0 0 = false ∧ keyB (0, 1) 0 1 = true ∧
    ((arrW 2 6).all fun a => ownerRowB 2 8 a) = false ∧
    ((arrW 0 6).all fun a => laidMatrixOk a 0 0) = false ∧
    decide (Sz.ref.packedShape 0 0 = Sz.ref.packedShape 0 3) = false ∧
    firstOrKeptB VerifiableInference.Desc.ReqLit.shapeFull 0 2 0 = false ∧
    ((arrW 0 6).all fun a => a.blocks.all (blockRoomB codesFull2
      { (K13.Law.MFull[1]?).getD default with mainRows := 8 })) = false ∧
    seatIsB (0, 1) ((K13.Law.MFull[0]?).getD default) = false := by
  decide +kernel

/-! ## Cells from blocks -/

theorem mul_add_lt' {a b m n : ℕ} (ha : a < m) (hb : b < n) : a * n + b < m * n := by
  calc a * n + b < a * n + n := by omega
    _ = (a + 1) * n := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ m * n := Nat.mul_le_mul_right n ha

/-- Where a block holds a cell, the cell lies within the block's rows and places. -/
theorem laidIn_bound {b : LaidBlock} {i c : ℕ} {rp : ℕ × ℕ}
    (hb : b.rowBits + b.placeBits = b.bitsI + b.bitsC) (h : laidIn b i c = some rp) :
    rp.1 < b.firstRow + 2 ^ b.rowBits ∧ rp.2 < b.firstPlace + 2 ^ b.placeBits := by
  unfold laidIn at h
  split at h
  · rename_i hc
    obtain ⟨h1, h2, h3, h4⟩ := hc
    have hI : i - b.firstI < 2 ^ b.bitsI := by omega
    have hC : c - b.firstC < 2 ^ b.bitsC := by omega
    have hx : (if b.iIsLow then (c - b.firstC) * 2 ^ b.bitsI + (i - b.firstI)
        else (i - b.firstI) * 2 ^ b.bitsC + (c - b.firstC)) < 2 ^ b.rowBits * 2 ^ b.placeBits := by
      rw [← Nat.pow_add, hb, Nat.pow_add]
      split
      · rw [Nat.mul_comm (2 ^ b.bitsI)]
        exact mul_add_lt' hC hI
      · exact mul_add_lt' hI hC
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨?_, ?_⟩
    · have hx' := hx
      rw [Nat.mul_comm (2 ^ b.rowBits) (2 ^ b.placeBits)] at hx'
      exact Nat.add_lt_add_left (Nat.div_lt_of_lt_mul hx') _
    · have := Nat.mod_lt (if b.iIsLow then (c - b.firstC) * 2 ^ b.bitsI + (i - b.firstI)
        else (i - b.firstI) * 2 ^ b.bitsC + (c - b.firstC))
        (Nat.pow_pos (n := b.placeBits) (show 0 < 2 by omega))
      exact Nat.add_lt_add_left this _
  · cases h

/-- **Every cell of an array lies in the main rows and off the pad**, from the test on its blocks. -/
theorem room_of_blocks {cs : Codes} {sh : OracleShape} {a : ReqArray}
    (hb : ∀ b ∈ a.blocks, b.rowBits + b.placeBits = b.bitsI + b.bitsC)
    (hr : a.blocks.all (blockRoomB cs sh) = true) {i c : ℕ} {rp : ℕ × ℕ}
    (h : laidAt a i c = some rp) : rp.1 < sh.mainRows ∧ padB cs sh false rp.1 rp.2 = false := by
  obtain ⟨b, hbm, hin⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨e1, e2⟩ := laidIn_bound (hb b hbm) hin
  have hB := List.all_eq_true.1 hr b hbm
  unfold blockRoomB at hB
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hB
  obtain ⟨r1, r2⟩ := hB
  refine ⟨by omega, ?_⟩
  unfold padB
  simp only [Bool.false_eq_true, if_false, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
    decide_eq_false_iff_not]
  rcases r2 with (r2 | r2) | r2
  · exact Or.inl (Or.inl r2)
  · exact Or.inl (Or.inr (by omega))
  · exact Or.inr (by omega)

/-- What the test gives. -/
theorem row_facts {l ν : ℕ} (hr : rowW l ν = true) :
    ∃ (a : ReqArray) (o : ℕ) (q : ℕ × ℕ) (sh : OracleShape), arrW l ν = some a ∧
      firstOrKeptB VerifiableInference.Desc.ReqLit.shapeFull l (ownW l ν).1 a.message = true ∧
      ownerRowB l ν a = true ∧ whereIsP dW l (ownW l ν).1 a.message = some o ∧
      K13.Law.LFull.places[o]? = some q ∧ K13.Law.MFull[o]? = some sh ∧ seatIsB q sh = true ∧
      laidMatrixOk a (ceilLog2 (sh.rows Part.main))
        (if sh.rows Part.main == 0 then 0 else (codesFull2.base.getD sh.code default).logEll) = true ∧
      keyB q (ownW l ν).1 a.message = true ∧
      Sz.ref.packedShape l ν = Sz.ref.packedShape (ownW l ν).1 (ownW l ν).2 ∧
      a.blocks.all (blockRoomB codesFull2 sh) = true := by
  unfold rowW at hr
  obtain ⟨a, ha, hr⟩ := (Option.any_eq_true _ _).1 hr
  rw [Bool.and_eq_true, Bool.and_eq_true] at hr
  obtain ⟨⟨h1, h2⟩, hr⟩ := hr
  obtain ⟨o, ho, hr⟩ := (Option.any_eq_true _ _).1 hr
  obtain ⟨q, hq, hr⟩ := (Option.any_eq_true _ _).1 hr
  obtain ⟨sh, hs, hr⟩ := (Option.any_eq_true _ _).1 hr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
  obtain ⟨⟨⟨⟨r1, r2⟩, r3⟩, r4⟩, r5⟩ := hr
  exact ⟨a, o, q, sh, ha, h1, h2, ho, hq, hs, r1, r2, r3, r4, r5⟩

/-- The test at a pair in range. -/
theorem row_at {l ν : ℕ} (hl : l < 25) (hν : ν < nmW l) : rowW l ν = true :=
  List.all_eq_true.1 (List.all_eq_true.1 tieRows_written l (List.mem_range.2 hl)) ν
    (List.mem_range.2 hν)

/-- The table's entry of the owner at a matrix. -/
def ownAt (Zp : ProofFile.Pub) (l ν : ℕ) : ℕ × ℕ × ℕ × ReqArray :=
  match arrW l ν with
  | some a => (P5J.At.num Zp (ownW l ν).1 a.message, (ownW l ν).1, (ownW l ν).2, a)
  | none => (0, 0, 0, default)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
include h

/-- The library's number of matrices. -/
theorem nm_W {l : ℕ} (hl : l < 25) : (_root_.Meaning.tlAt Zp.p.X l).NM = nmW l := by
  have hX : OnBytes.Model.Verify.publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X := h.pubOne
  have C := OnBytes.Road.Hd.core_of_scope h.scope h.reads hX
  rw [_root_.Meaning.nm_of_core hX C hl]
  show (_root_.Meaning.matsAt Zp.p.X l).size = nmW l
  unfold nmW
  by_cases h24 : l = 24
  · subst h24
    exact _root_.Meaning.size_head hX C
  rw [if_neg h24]
  by_cases ho : l % 2 = 1
  · rw [if_pos ho]
    obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g + 1 := ⟨l / 2, by omega⟩
    exact _root_.Meaning.size_odd hX C (by omega)
  · rw [if_neg ho]
    obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g := ⟨l / 2, by omega⟩
    exact _root_.Meaning.size_even hX C (by omega)

/-- The library's owner is the written one. -/
theorem ownerOf_W {l ν : ℕ} (hl : l < 25) : _root_.Meaning.ownerOf Zp.p.X l ν = ownW l ν := by
  have hX : OnBytes.Model.Verify.publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X := h.pubOne
  have C := OnBytes.Road.Hd.core_of_scope h.scope h.reads hX
  have B := (OnBytes.Road.Hd.eleven_of_core hX C (OnBytes.Road.Hd.npOf Zp.p.X.hS)).1
  have hN : Zp.p.X.hS.NHf = 4 := (OnBytes.Road.Hd.numH_of_layout B.full B.head).NHf
  obtain ⟨i6, i7, i8⟩ := _root_.Meaning.ix_of_core hX C
  unfold _root_.Meaning.ownerOf ownW
  by_cases h24 : l = 24
  · subst h24
    rw [if_pos rfl, if_pos rfl, hN, i7]
  rw [if_neg h24, if_neg h24]
  by_cases ho : l % 2 = 1
  · rw [if_pos ho, if_pos ho]
    obtain ⟨-, -, n1, -⟩ := _root_.Meaning.matsAt_att_gid hX C (g := l / 2) (by omega)
    rw [n1, i6]
  · rw [if_neg ho, if_neg ho, i7, i8]

/-- The list of arrays names the owner's array. -/
theorem pair_W {l ν : ℕ} (hl : l < 25) (hν : ν < nmW l) :
    (h.𝔇.pubD.d3.arrayOf.getD l #[])[(_root_.Meaning.tlAt Zp.p.X l).gtTree.getD ν 0]? =
      some ((ownW l ν).1, _root_.Meaning.nameOf (ownW l ν).2) := by
  have hX : OnBytes.Model.Verify.publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X := h.pubOne
  have C := OnBytes.Road.Hd.core_of_scope h.scope h.reads hX
  have hm : ν < (_root_.Meaning.matsAt Zp.p.X l).size := by
    have e := _root_.Meaning.nm_of_core hX C hl
    have e' := nm_W h hl
    have : (_root_.Meaning.tlAt Zp.p.X l).mats.size = nmW l := e.symm.trans e'
    show ν < (_root_.Meaning.tlAt Zp.p.X l).mats.size
    omega
  have hs : ν < (_root_.Meaning.sizesOf Zp.p.X l).NM := by
    rw [(_root_.Meaning.follows_of_core hX C).NM _ hl]
    exact hm
  have hn := P2Law.Names.names_tie_all h.scope h.reads h.laid.pub hl hs
  have ol := _root_.Meaning.owner_label hX C hl hm
  rw [ownerOf_W h hl] at ol
  have e1 := congrArg Prod.fst ol
  have e2 := congrArg Prod.snd ol
  have hn' : (h.𝔇.pubD.d3.arrayOf.getD l #[])[(_root_.Meaning.tlAt Zp.p.X l).gtTree.getD ν 0]? =
      some (_root_.Meaning.ownerK (_root_.Meaning.labAt Zp.p.X l ν),
        _root_.Meaning.nameOf (_root_.Meaning.ownerA (_root_.Meaning.labAt Zp.p.X l ν))) := hn
  rw [hn']
  simp only at e1 e2
  rw [e1, e2]

/-- The plan's term is the written one. -/
theorem dS_W (l b k : ℕ) :
    whereIsP h.𝔇.pubD.dS l b k = whereIsP dW l b k := by
  have hC := VerifiableInference.Desc.First.Close.hc_at_laid h.scope h.laid
  have e1 : h.𝔇.shape = proofSizedFull.request :=
    (VerifiableInference.PlanWritten.Joined.first_written_in_scope h.scope h.laid.pub
      (VerifiableInference.Desc.K1.pin1_atAll h)).2.2.1
  have e2 : h.𝔇.N.msgsAt = numsW.msgsAt := by
    show (fun p => First.msgsTold (P5J.At.told cF) (First.borderOf P5J.At.ps p)) = _
    rw [K13.Law.told_of_cut (cF := cF) hC]
    rfl
  show whereIsP (sentDataOf h.𝔇.shape (fun m => h.𝔇.N.msgsAt ((flatPlacesOf linksFull true).find? fun p =>
    p.link == some m && p.piece == 1 + ((linksFull[m]?).map shift).getD 0)) fun _ => []) l b k = _
  rw [e1, e2]

omit h in
/-- A lawful array's blocks are as large in the table as in the matrix. -/
theorem blocks_of_laid {a : ReqArray} {R P : ℕ} (hl : laidMatrixOk a R P = true) :
    ∀ b ∈ a.blocks, b.rowBits + b.placeBits = b.bitsI + b.bitsC := by
  intro b hb
  unfold laidMatrixOk at hl
  simp only [Bool.and_eq_true] at hl
  have e := List.all_eq_true.1 hl.1.1 b hb
  simp only [laidBlockOk, Bool.and_eq_true, beq_iff_eq] at e
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨e, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := e
  exact e

/-- A seat that the test names has a member, and the member has the shape. -/
theorem ms_seat {q : ℕ × ℕ} {sh : OracleShape} (hs : seatIsB q sh = true) :
    ∃ yM : Mem, ((P5J.At.ms Zp Z.lay).find? fun z => decide (seatOf z = q)) = some yM ∧
      (yM.1.l.get yM.2).1 = sh := by
  have eP := (P5T.seats_in_scope h.scope h.laid.pub (K1.pin1_atAll h) (K1.laidP_atAll h)).1
  have hM : ∀ y : OnBytes.OracleShape × (Nat × Nat),
      y ∈ (P5J.At.ms Zp Z.lay).map (fun m => ((m.1.l.get m.2).1, seatOf m)) ↔
        y ∈ (psFull.filter (·.smpd)).map fun p => (p.shape, p.seat) := by
    intro y
    have e := P5T.memsSame_atR Zp (P5J.At.rad Zp Z.lay) y
    rw [eP] at e
    exact e
  unfold seatIsB at hs
  rw [Bool.and_eq_true, List.any_eq_true, List.all_eq_true] at hs
  obtain ⟨⟨p, hp, hpq⟩, hall⟩ := hs
  obtain ⟨m, hm, e⟩ := List.mem_map.1 ((hM (p.shape, p.seat)).2 (List.mem_map.2 ⟨p, hp, rfl⟩))
  have e2 : seatOf m = p.seat := congrArg Prod.snd e
  have hq : seatOf m = q := e2.trans (of_decide_eq_true hpq)
  cases hf : (P5J.At.ms Zp Z.lay).find? (fun z => decide (seatOf z = q)) with
  | none =>
    have := List.find?_eq_none.1 hf m hm
    simp only [decide_eq_true_eq] at this
    exact absurd hq this
  | some yM =>
    refine ⟨yM, rfl, ?_⟩
    have hy0 := List.find?_some hf
    have hy : seatOf yM = q := of_decide_eq_true hy0
    have hmem := List.mem_of_find?_eq_some hf
    obtain ⟨p', hp', e'⟩ := List.mem_map.1
      ((hM ((yM.1.l.get yM.2).1, seatOf yM)).1 (List.mem_map.2 ⟨yM, hmem, rfl⟩))
    have e1 : p'.shape = (yM.1.l.get yM.2).1 := congrArg Prod.fst e'
    have e3 : p'.seat = seatOf yM := congrArg Prod.snd e'
    have hw := hall p' hp'
    rw [Bool.or_eq_true] at hw
    rcases hw with hw | hw
    · simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hw
      exact absurd (e3.trans hy) hw
    · rw [← e1]
      exact of_decide_eq_true hw

/-- **THE PLAN's HALF OF THE SEATS AT SEGMENT l.** -/
theorem tieSeats_head {l : ℕ} (hl : l < 25) :
    (_root_.Meaning.tlAt Zp.p.X l).NM = nmW l ∧
    symsSeatedB (h.𝔇.pubD.d3.arrayOf.getD l #[]) h.𝔇.layout h.𝔇.shape l
      (_root_.Meaning.tlAt Zp.p.X l) = true ∧
    ∀ ν, ν < nmW l → ∀ (c₁ : ℕ × String) (a₁ : ReqArray) (o : ℕ) (q : ℕ × ℕ) (sh : OracleShape),
      (h.𝔇.pubD.d3.arrayOf.getD l #[])[(_root_.Meaning.tlAt Zp.p.X l).gtTree.getD ν 0]? = some c₁ →
      reqArray h.𝔇.layout c₁.1 c₁.2 = some a₁ →
      whereIsP h.𝔇.pubD.dS l c₁.1 a₁.message = some o →
      K13.Law.d12Full.L.places[o]? = some q →
      K13.Law.d12Full.M[o]? = some sh →
      ∃ (yM : Mem) (l₀ ν₀ : ℕ), ((P5J.At.ms Zp Z.lay).find? fun z => decide (seatOf z = q)) = some yM ∧
        (yM.1.l.get yM.2).1 = sh ∧
        laidMatrixOk a₁ (ceilLog2 (sh.rows Part.main))
          (if sh.rows Part.main == 0 then 0 else ((P5J.At.cs Zp).base.getD sh.code default).logEll) = true ∧
        ownAt Zp l ν = (P5J.At.arr Zp q.1 q.2, l₀, ν₀, a₁) ∧
        Sz.ref.packedShape l ν = Sz.ref.packedShape l₀ ν₀ ∧
        ∀ i c rp, i < (Sz.ref.packedShape l ν).1 → c < (Sz.ref.packedShape l ν).2 →
          laidAt a₁ i c = some rp → rp.1 < sh.mainRows ∧ padB (P5J.At.cs Zp) sh false rp.1 rp.2 = false := by
  have hP1 := K1.pin1_atAll h
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hlay : h.𝔇.layout = layoutFull :=
    VerifiableInference.PlanWritten.Joined.layout_in_scope h.scope h.laid.pub hP1
  have hshp : h.𝔇.shape = VerifiableInference.Desc.ReqLit.shapeFull := K1.hDsh_atAll h O hP1
  have hcs : P5J.At.cs Zp = codesFull2 := (K13.Law.likeFull_in_scope h.scope h.laid.pub hP1).codes
  have eA : P5J.At.pseatsAll Zp = seatsAllFull :=
    (P5T.seats_in_scope h.scope h.laid.pub hP1 (K1.laidP_atAll h)).2.1
  refine ⟨nm_W h hl, ?_, ?_⟩
  · unfold symsSeatedB
    rw [nm_W h hl, hlay, hshp]
    refine List.all_eq_true.2 fun μ hμ => ?_
    have hμ' := List.mem_range.1 hμ
    obtain ⟨a, o, q, sh, ha, hfk, -⟩ := row_facts (row_at hl hμ')
    have ha' : reqArray layoutFull (ownW l μ).1 (_root_.Meaning.nameOf (ownW l μ).2) = some a := ha
    rw [pair_W h hl hμ']
    show (match reqArray layoutFull (ownW l μ).1 (_root_.Meaning.nameOf (ownW l μ).2) with
      | none => false
      | some Ar => firstOrKeptB _ l (ownW l μ).1 Ar.message) = true
    rw [ha']
    exact hfk
  · intro ν hν c₁ a₁ o q sh h1 h2 h3 h4 h5
    rw [pair_W h hl hν] at h1
    obtain rfl := Option.some.inj h1
    rw [hlay] at h2
    rw [dS_W h] at h3
    obtain ⟨a, o', q', sh', ha, -, -, ho, hq, hs, hseat, hlaid, hkey, hpk, hroom⟩ :=
      row_facts (row_at hl hν)
    have ha' : reqArray layoutFull (ownW l ν).1 (_root_.Meaning.nameOf (ownW l ν).2) = some a := ha
    obtain rfl : a = a₁ := Option.some.inj (ha'.symm.trans h2)
    obtain rfl : o' = o := Option.some.inj (ho.symm.trans h3)
    obtain rfl : q' = q := Option.some.inj (hq.symm.trans h4)
    obtain rfl : sh' = sh := Option.some.inj (hs.symm.trans h5)
    obtain ⟨yM, hy, hys⟩ := ms_seat h hseat
    refine ⟨yM, (ownW l ν).1, (ownW l ν).2, hy, hys, by rw [hcs]; exact hlaid, ?_, hpk, ?_⟩
    · unfold ownAt
      rw [ha]
      obtain ⟨p, hf, hk⟩ := (Option.any_eq_true _ _).1 hkey
      have e : P5J.At.num Zp (ownW l ν).1 a.message = P5J.At.arr Zp q'.1 q'.2 := by
        show P5T.numOfPlan (P5J.At.pseatsAll Zp) _ _ = P5T.arrOf (P5J.At.pseatsAll Zp) _ _
        rw [eA]
        exact (P5T.arrOf_is_num _ _ _ _ _ _ hf (of_decide_eq_true hk)).symm
      show (P5J.At.num Zp (ownW l ν).1 a.message, _, _, _) = _
      rw [e]
    · intro i c rp _ _ hrp
      rw [hcs]
      exact room_of_blocks (blocks_of_laid hlaid) hroom hrp

/-- **EACH MATRIX's OWNER IS THE TRACE's.** -/
theorem ownerRows_head {l : ℕ} (hl : l < 25) :
    ∀ ν, ν < nmW l → ∀ n l₀ ν₀ a, ownAt Zp l ν = (n, l₀, ν₀, a) →
      ∃ (σ : Seg) (μ : MatName) (R P : ℕ), σ.Below 12 ∧ σ.no 12 = l ∧
        (MatName.all 3 1 1 4 σ)[ν]? = some μ ∧ Sz.ref.matAt l₀ ν₀ = some (Sz.ref.owner σ μ) ∧
        l₀ < 25 ∧ n = P5J.At.num Zp l₀ a.message ∧
        VerifiableInference.Desc.arrayOf h.𝔇.sent.layout l₀ a.name = some a ∧
        labelNo a.name = some ν₀ ∧ laidMatrixOk a R P = true ∧
        (Sz.ref.packedShape l ν).1 ≤ a.sizeI ∧ (Sz.ref.packedShape l ν).2 ≤ a.sizeC := by
  intro ν hν n l₀ ν₀ a hown
  have hP1 := K1.pin1_atAll h
  have hlay : h.𝔇.layout = layoutFull :=
    VerifiableInference.PlanWritten.Joined.layout_in_scope h.scope h.laid.pub hP1
  obtain ⟨a', o, q, sh, ha, -, hor, -, -, -, -, hlaid, -, -, -⟩ := row_facts (row_at hl hν)
  unfold ownAt at hown
  rw [ha] at hown
  obtain ⟨rfl, rfl, rfl, rfl⟩ : P5J.At.num Zp (ownW l ν).1 a'.message = n ∧ (ownW l ν).1 = l₀ ∧
      (ownW l ν).2 = ν₀ ∧ a' = a := by
    have e := hown
    simp only [Prod.mk.injEq] at e
    exact e
  unfold ownerRowB at hor
  obtain ⟨σ, hσ, hor⟩ := (Option.any_eq_true _ _).1 hor
  rw [Bool.and_eq_true, Bool.and_eq_true] at hor
  obtain ⟨⟨b1, b2⟩, hor⟩ := hor
  obtain ⟨μ, hμ, hor⟩ := (Option.any_eq_true _ _).1 hor
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hor
  obtain ⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩ := hor
  refine ⟨σ, μ, _, _, of_decide_eq_true b1, of_decide_eq_true b2, hμ, c1, c3, rfl, ?_,
    (K2.Law.labelNo_eq _).trans c5, hlaid, c6, c7⟩
  show VerifiableInference.Desc.arrayOf h.𝔇.layout _ _ = _
  rw [hlay]
  exact c4

end

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.tieRows_written
#print axioms ProofFile.Honest.K1.tie_bites
#print axioms ProofFile.Honest.K1.laidIn_bound
#print axioms ProofFile.Honest.K1.room_of_blocks
#print axioms ProofFile.Honest.K1.nm_W
#print axioms ProofFile.Honest.K1.ownerOf_W
#print axioms ProofFile.Honest.K1.pair_W
#print axioms ProofFile.Honest.K1.dS_W
#print axioms ProofFile.Honest.K1.ms_seat
#print axioms ProofFile.Honest.K1.tieSeats_head
#print axioms ProofFile.Honest.K1.ownerRows_head
