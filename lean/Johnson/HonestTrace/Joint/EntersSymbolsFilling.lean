-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/Joint/EntersSymbolsFilling.lean

Nothing on hiding. No property of the protocol is claimed. One structure of public premises, two theorems.

FROM THE SENDERS' SENTENCE TO THE PLAIN EQUATION AT THE LAYOUT's SEATS, PLANES AND CELLS ALIKE. The senders' sentence is
"LaysFilling" (Johnson/Desc/ProofFile/Honest/K5/Law/LaysFilling.lean): the Script's messages hold what the filling of a segment's
first sending lays. The plain equation is "SeatEntriesArePackedAt" (EntersSymbols.lean): at each seat of the layout the message's
entry is the library's packing "msgOf" of a trace τ.

The road. A seat of "Meaning.fLay" is the layout's own reader at the link and the array that the entry's label names
("Meaning.seat_of_laidThere", under the head's test "laidThere"). "msg_of_lays" says what the Script holds there: the value of
"cellsVals", which is "packedCells" of the reader's cells. Where the reader's cells are τ's integers that is "packedOf"
("packedOf_eq_cells"), and "msgOf" is its image ("msgOf_eq_packedOf"). No word parts planes from cells on this road.

Main definitions and theorems:
* "EntryHasTheFillingsShape X m a": ON PUBLIC DATA, at entry a of the list of sub-proof m: the array that the label names is owned by
  a segment of the filling's sizes "Sz.ref", below link 25, and the plan's rows and columns, at the entry and at its owner, are the
  filling's.
* "seatEntriesArePacked_of_laysFilling": under the head h, the senders' sentence at every link below 25, at a valid input whose
  reader's cells are τ's integers, on the entries that P picks and that have the filling's shape: the plain equation at every list
  of at least N challenges.
* "rawOn_of_laysFilling": with "SeatEntriesReadNoChallenge": ScriptSymsRawOn on P.

Limits. CONDITIONAL on the head; on the senders' sentence, which is shown of no Script; on the public premise, which is not paid here;
on the tie between the reader's cells and τ. At "Sz.ref", the full size's numbers.
-/
import Johnson.HonestTrace.Joint.EntersSymbols
import Johnson.Desc.ProofFile.Honest.K5.Law.LaysFilling
import Johnson.Goal.HonestTrace.PackedIsMsg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open VerifiableInference.Desc.Sound (MsgT)
open Meaning (msgOf labAt ownerK ownerA sizesOf)
open P5J (CellsM AtMgA TS)
open OnBytes.Maker (WholeD)
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.K1 (labelNo cellsVals)
open ProofFile.Honest.K5 (LaysFilling msg_of_lays cellsVals_size labelNo_arrayLabel asE_inl)

/-- **ON PUBLIC DATA: entry a of the list of sub-proof m has the filling's shape.** -/
structure EntryHasTheFillingsShape (X : OnBytes.Model.Verify.Public) (m a : ℕ) : Prop where
  /-- the owner's link is one of the 25 -/
  ownerLink : ownerK (labAt X m a) < 25
  /-- the owner's number is one that the frame's reader of names reads -/
  ownerNumber : ownerA (labAt X m a) < 26
  /-- the label names a matrix of the filling's sizes that has an array of its own segment -/
  owned : ∃ (σ : Seg) (μ : MatName),
    Sz.ref.matAt (ownerK (labAt X m a)) (ownerA (labAt X m a)) = some (σ, μ) ∧
      (Sz.ref.arrayNo σ μ).isSome = true
  /-- the plan's rows of cells at the entry are the filling's -/
  rows : (sizesOf X m).m a = (Sz.ref.shapeNo (ownerK (labAt X m a)) (ownerA (labAt X m a))).1
  /-- the plan's columns at the entry are the filling's -/
  columns : (sizesOf X m).k a = (Sz.ref.shapeNo (ownerK (labAt X m a)) (ownerA (labAt X m a))).2
  /-- the plan's rows of cells at the owner's own entry are the filling's -/
  ownerRows : (sizesOf X (ownerK (labAt X m a))).m (ownerA (labAt X m a)) =
    (Sz.ref.shapeNo (ownerK (labAt X m a)) (ownerA (labAt X m a))).1

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl} {xp : VerifiableInference.Desc.First.Look.Place}
  {Bk : ProverCoinCounts} {W₀ Rc T : Type}
  {Q : Script Bk (Local W₀ Rc ProofFile.Inst T) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}

/-- **The plain equation at every long list, from the senders' sentence.** -/
theorem seatEntriesArePacked_of_laysFilling (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xp)
    {valid : Local W₀ Rc ProofFile.Inst T → Prop} {N : ℕ} {readers : Local W₀ Rc ProofFile.Inst T → Readers}
    (lays : ∀ link < 25, ∃ seat heard, LaysFilling h Q valid N readers seat heard link)
    (k : Coins Bk) {v : Local W₀ Rc ProofFile.Inst T} (isValid : valid v) {τ : Tr}
    (cellsAreTheTraces : ∀ σ μ mu, σ.Below Sz.ref.nGr → Sz.ref.mu σ μ = some mu → ∀ row column,
      (readers v).cells.cell (σ.no Sz.ref.nGr) μ.label row column =
        ((τ (σ.no Sz.ref.nGr) mu row column : ℤ) : Cb.Gl.F))
    {P : ℕ → ℕ → Prop}
    (shapes : ∀ m < 25, ∀ a < (sizesOf (P5J.At.X Zp) m).NM, P m a →
      EntryHasTheFillingsShape (P5J.At.X Zp) m a)
    {heard : List Fmt.Drawn} (long : N ≤ heard.length) :
    SeatEntriesArePackedAt Zp Q k v τ P heard := by
  intro m hm a ha hP i' hi' c hc
  have E := shapes m hm a ha hP
  obtain ⟨σ, μ, hM, ho⟩ := E.owned
  obtain ⟨seat, heardAt, L⟩ := lays _ E.ownerLink
  obtain ⟨A, x, hA, -, -, hx, hseat⟩ :=
    Meaning.seat_of_laidThere h.plan.laid (P5J.At.num Zp) hm ⟨a, ha⟩ hi' hc
  have hf : Meaning.fLay (P5J.At.layout Zp) (P5J.At.num Zp) (labAt (P5J.At.X Zp) m a) i' c =
      (P5J.At.num Zp (ownerK (labAt (P5J.At.X Zp) m a)) A.message, x.1, x.2) := hseat
  obtain ⟨As, -, hfind⟩ := Option.bind_eq_some_iff.1 hA
  have hname : A.name = Meaning.nameOf (ownerA (labAt (P5J.At.X Zp) m a)) := by
    simpa using List.find?_some hfind
  have hn : labelNo A.name = some (ownerA (labAt (P5J.At.X Zp) m a)) := by
    rw [hname]
    exact labelNo_arrayLabel E.ownerNumber
  have hz := cellsVals_size Sz.ref hn hM ho
  have hi₀ : i' < (Sz.ref.packedShape (ownerK (labAt (P5J.At.X Zp) m a))
      (ownerA (labAt (P5J.At.X Zp) m a))).1 := by
    show i' < Alg.symRows _
    rw [← E.rows]
    exact hi'
  have hc₀ : c < (Sz.ref.shapeNo (ownerK (labAt (P5J.At.X Zp) m a))
      (ownerA (labAt (P5J.At.X Zp) m a))).2 := by
    rw [← E.columns]
    exact hc
  obtain ⟨heard', q⟩ := msg_of_lays L hA hx hz hi₀ hc₀ k isValid long
  have value : (cellsVals Sz.ref).val (readers v) heard' (ownerK (labAt (P5J.At.X Zp) m a)) A.name i' c =
      .inl (packedCells Sz.ref (readers v).cells.cell (ownerK (labAt (P5J.At.X Zp) m a))
        (ownerA (labAt (P5J.At.X Zp) m a)) i' c) := by
    simp only [cellsVals, hn]
  rw [value, asE_inl, ← packedOf_eq_cells Sz.ref τ _ cellsAreTheTraces,
    ← msgOf_eq_packedOf Sz.ref (sizesOf (P5J.At.X Zp)) τ (labAt (P5J.At.X Zp) m a) false i' c rfl
      E.ownerRows hc₀] at q
  show Q.msg (Meaning.fLay (P5J.At.layout Zp) (P5J.At.num Zp) (labAt (P5J.At.X Zp) m a) i' c).1 k v
      (heard.take (Q.fixedMsg
        (Meaning.fLay (P5J.At.layout Zp) (P5J.At.num Zp) (labAt (P5J.At.X Zp) m a) i' c).1)) false
      (Meaning.fLay (P5J.At.layout Zp) (P5J.At.num Zp) (labAt (P5J.At.X Zp) m a) i' c).2.1
      (Meaning.fLay (P5J.At.layout Zp) (P5J.At.num Zp) (labAt (P5J.At.X Zp) m a) i' c).2.2 = _
  rw [hf]
  exact q

/-- **ScriptSymsRawOn from the senders' sentence and "the seats' entries read no challenge".** -/
theorem rawOn_of_laysFilling (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xp)
    {valid : Local W₀ Rc ProofFile.Inst T → Prop} {N : ℕ} {readers : Local W₀ Rc ProofFile.Inst T → Readers}
    (lays : ∀ link < 25, ∃ seat heard, LaysFilling h Q valid N readers seat heard link)
    {k : Coins Bk} {v : Local W₀ Rc ProofFile.Inst T} (isValid : valid v) {τ : Tr}
    (cellsAreTheTraces : ∀ σ μ mu, σ.Below Sz.ref.nGr → Sz.ref.mu σ μ = some mu → ∀ row column,
      (readers v).cells.cell (σ.no Sz.ref.nGr) μ.label row column =
        ((τ (σ.no Sz.ref.nGr) mu row column : ℤ) : Cb.Gl.F))
    {P : ℕ → ℕ → Prop}
    (shapes : ∀ m < 25, ∀ a < (sizesOf (P5J.At.X Zp) m).NM, P m a →
      EntryHasTheFillingsShape (P5J.At.X Zp) m a)
    (noChallenge : SeatEntriesReadNoChallenge Zp Q k v P) : ScriptSymsRawOn Zp Q k v τ P :=
  rawOn_of_one_list noChallenge
    (seatEntriesArePacked_of_laysFilling h lays k isValid cellsAreTheTraces shapes
      (heard := List.replicate N ⟨[], [], [], none⟩) (by rw [List.length_replicate]))

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.seatEntriesArePacked_of_laysFilling
#print axioms OnBytes.HonestTrace.rawOn_of_laysFilling
