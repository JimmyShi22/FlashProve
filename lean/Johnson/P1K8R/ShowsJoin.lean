-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/ShowsJoin.lean: THE SMALLNESS TEST AT THE TABLE OF JOINTS: A
PAYMENT BENEATH THE KIND'S FROZEN CONDITION: THE SENTENCE ON THE LAYOUT (`ShowsAt`)
FROM PLAIN FACTS ON THE OPEN LINK, THE BOOK AND THE LAYOUT. NO SOUNDNESS.

Two readers read one committed symbol off a witness. The table of joints' reader `readAt` goes by
the message's number in the witness, at the seat that the layout gives the element (`seatIn`). The
smallness test's table of cells `cellsAt` goes by the open link's list of arrays, the live request's
frame, the book of trees, and a sum over the layout's blocks. Here they are shown to read one entry
of one table:
  `cell_is_entry`: **the table of cells' entry is `seatTab` at the book's seat of the array's
    message, at the row and place at which the layout lays the element**: by
    `blocks_sum`, `laidPlace_one`, `laidIn_row_lt`, `tableIndex_parts`
    (Johnson/Desc/First/Att/K05CellAt.lean) under the programs' own test `laidMatrixOk`, and our
    `cellsAt_named`.
  `read_is_entry`: **the other reader's entry is `seatTab` at that same seat**, where the seat is a
    tenant of the segment's group with the message's number and the number is named once
    (`readAt_of_named`).
  `ArrFacts`: THE PLAIN FACTS at one matrix of the part: the open link's list names the array of the
    matrix's label at the part's number of that matrix's array; the link's layout and the plan's
    both have it; the frame knows where its message is; `laidMatrixOk`; the book seats that message
    at a tenant with the plan's number of the message; inside the sizes every element is laid.
  `shows_of_facts`: **`ArrFacts` at every matrix, with the two equations on the part, give
    `ShowsAt`.**
Limits. `ArrFacts` is shown nowhere here. Nothing on soundness.

-/
import Johnson.P1K8R.SmallJoin
import Johnson.Desc.First.K8.LawBlockIn
import Johnson.Desc.First.Att.K05CellAt

set_option autoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T

open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat
open OnBytes.Params (LaidBlock ReqArray ReqLayout)
open VerifiableInference.Desc (Chain Strs Wit laidAt seatIn)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.First.Look (laidHolds laidPlace)
open VerifiableInference.Desc.First.Att.P (blocks_sum laidPlace_one laidIn_row_lt tableIndex
  tableIndex_parts)
open VerifiableInference.Desc.K9L (BlockFacts blockFacts)
open VerifiableInference.Desc.K9 (seatAt seatAt_mem)
open ProofFile (Cl)
open P5J (AtMgA)

section
variable {P Cells Tok : Type} (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers)
  (m : ℕ)

/-- **The table of cells' entry is the witness's table's, at the book's seat and the layout's
place.** -/
theorem cell_is_entry (z : P) (s : S) {L : LinkCtx} {F : Fork} {tl : HTailF2}
    (hL : s.link? = some L) (hF : s.fork? = some F) (ht : s.tl? = some tl) {t o : ℕ}
    {x : ℕ × String} {a : ReqArray} {q rp : ℕ × ℕ} (hx : L.arrayOf[t]? = some x)
    (ha : OnBytes.reqArray L.check.rows.layout x.1 x.2 = some a)
    (hwi : L.check.frame.whereIs x.1 a.message = some o)
    (hok : laidMatrixOk a (s.st.rowBits o .main) (s.st.placeBits o .main) = true)
    (hq : seatAt (N.group m) s.book o = some q) (w : Wit Cells Tok MsgT) {r c : ℕ}
    (hrp : laidAt a r c = some rp) :
    cellsAt cs arr ms N m (z, s) w t r c = seatTab cs arr ms w q false rp.1 rp.2 := by
  have hok' := hok
  unfold laidMatrixOk at hok'
  obtain ⟨hok1, -⟩ := Eq.mp (Bool.and_eq_true _ _) hok'
  obtain ⟨hall, hno⟩ := Eq.mp (Bool.and_eq_true _ _) hok1
  have hBF : ∀ b ∈ a.blocks,
      BlockFacts b (s.st.rowBits o .main) (s.st.placeBits o .main) := by
    intro b hb
    have h1 := List.all_eq_true.1 hall b hb
    obtain ⟨h2, -⟩ := Eq.mp (Bool.and_eq_true _ _) h1
    obtain ⟨h3, -⟩ := Eq.mp (Bool.and_eq_true _ _) h2
    exact blockFacts b _ _ h3
  have hlp : laidPlace a.blocks r c = some rp := (laidPlace_one a r c).trans hrp
  have hlt : rp.1 < 2 ^ s.st.rowBits o .main := by
    have h0 := hlp
    unfold laidPlace at h0
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 h0
    exact laidIn_row_lt b _ _ (hBF b (List.mem_of_find?_eq_some hb)) r c
      (List.find?_some (p := fun b => laidHolds b r c) hb)
  rw [cellsAt_named cs arr ms N m z s hL hF ht hx ha hwi w r c,
    blocks_sum _ _ (tabQ (N.group m) s.st s.book (seatTab cs arr ms w) o .main) r c a.blocks hBF
      hno,
    hlp]
  show tabQ (N.group m) s.st s.book (seatTab cs arr ms w) o .main
    (tableIndex (s.st.rowBits o .main) rp) = _
  unfold tabQ
  rw [hq]
  show seatTab cs arr ms w q false (tableIndex (s.st.rowBits o .main) rp % 2 ^ s.st.rowBits o .main)
    (tableIndex (s.st.rowBits o .main) rp / 2 ^ s.st.rowBits o .main) = _
  rw [(tableIndex_parts _ rp hlt).1, (tableIndex_parts _ rp hlt).2]

/-- **The reader by numbers reads the same table**, at a tenant with that number. -/
theorem read_is_entry (w : Wit Cells Tok MsgT) {n : ℕ} {q : ℕ × ℕ} (hn : namedOnce arr N m n = true)
    (hq : q ∈ N.group m) (ha : arr q.1 q.2 = n) :
    readAt cs arr ms N m w n = seatTab cs arr ms w q := by
  obtain ⟨x, hx, e⟩ := readAt_of_named cs arr ms N m n w hn
  have hm : q ∈ (N.group m).filter fun x => arr x.1 x.2 == n :=
    List.mem_filter.2 ⟨hq, by rw [ha]; exact beq_self_eq_true n⟩
  rw [hx] at hm
  rw [e, List.mem_singleton.1 hm]

end

/-- **THE PLAIN FACTS AT ONE MATRIX OF THE PART.** born, name: the owner's link and the array's name
off the matrix's label; t: the part's number of that matrix's array; rows, cols: its sizes. -/
def ArrFacts (layout : ReqLayout) (num arr : ℕ → ℕ → ℕ) (own : List (ℕ × ℕ)) (s : S) (L : LinkCtx)
    (born : ℕ) (name : String) (t rows cols : ℕ) : Prop :=
  ∃ (a : ReqArray) (o : ℕ) (q : ℕ × ℕ), L.arrayOf[t]? = some (born, name) ∧
    OnBytes.reqArray L.check.rows.layout born name = some a ∧
    VerifiableInference.Desc.arrayOf layout born name = some a ∧
    L.check.frame.whereIs born a.message = some o ∧
    laidMatrixOk a (s.st.rowBits o .main) (s.st.placeBits o .main) = true ∧
    seatAt own s.book o = some q ∧ arr q.1 q.2 = num born a.message ∧
    ∀ r c, r < rows → c < cols → (laidAt a r c).isSome = true

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **THE SENTENCE ON THE LAYOUT, FROM THE PLAIN FACTS.** -/
theorem shows_of_facts (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) (l : ℕ) (z : ProofFile.InstPub)
    (s : S) (w : Wit (P5J.CellsM numsFull) P5J.At.Tok MsgT)
    (H : ∀ tl, s.tl? = some tl → tl.NM = (Meaning.tlAt (P5J.At.X Zp) l).NM ∧
      tl.mats = (Meaning.tlAt (P5J.At.X Zp) l).mats ∧
      ∃ (L : LinkCtx) (F : Fork), s.link? = some L ∧ s.fork? = some F ∧
        ∀ μ : Fin (Meaning.sizesOf (P5J.At.X Zp) l).NM,
          ArrFacts (P5J.At.layout Zp) (P5J.At.num Zp) (P5J.At.arr Zp) ((P5J.At.N Zp cF).group l) s L
            (Meaning.ownerK (Meaning.labAt (P5J.At.X Zp) l μ.val))
            (Meaning.nameOf (Meaning.ownerA (Meaning.labAt (P5J.At.X Zp) l μ.val)))
            (tl.gtTree.getD μ 0) (Alg.symRows ((Meaning.sizesOf (P5J.At.X Zp) l).m μ))
            ((Meaning.sizesOf (P5J.At.X Zp) l).k μ)) :
    ShowsAt Zp cF Z.lay l (z, s) w := by
  intro tl ht
  obtain ⟨eN, eM, L, F, hL, hF, hA⟩ := H tl ht
  refine ⟨eN, eM, fun μ r c hr hc => ?_⟩
  obtain ⟨a, o, q, hx, ha, ha', hwi, hok, hq, hn, hlaid⟩ := hA μ
  obtain ⟨rp, hrp⟩ := Option.isSome_iff_exists.1 (hlaid r c hr hc)
  have eS : seatC Zp l μ r c = (P5J.At.num Zp
      (Meaning.ownerK (Meaning.labAt (P5J.At.X Zp) l μ.val)) a.message, rp.1, rp.2) := by
    show (seatIn (P5J.At.layout Zp) (P5J.At.num Zp)
      (Meaning.ownerK (Meaning.labAt (P5J.At.X Zp) l μ.val))
      (Meaning.nameOf (Meaning.ownerA (Meaning.labAt (P5J.At.X Zp) l μ.val))) r c).getD
      (0, 0, 0) = _
    unfold seatIn
    rw [ha', Option.bind_some, hrp]
    rfl
  have hN1 := h.plan.hN l μ r c hr hc
  rw [show (Meaning.seatBy (Meaning.fLay (P5J.At.layout Zp) (P5J.At.num Zp)) (P5J.At.X Zp)
    (Meaning.sizesOf (P5J.At.X Zp)) l μ r c) = seatC Zp l μ r c from rfl, eS] at hN1
  rw [eS, read_is_entry (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) l w hN1
    (seatAt_mem _ _ _ _ hq) hn]
  exact (cell_is_entry (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) l z s hL
    hF ht hx ha hwi hok hq w hrp).symm

end P1K8T

#print axioms P1K8T.cell_is_entry
#print axioms P1K8T.read_is_entry
#print axioms P1K8T.shows_of_facts
