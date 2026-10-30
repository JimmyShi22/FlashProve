-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K1/Law/TieMatOwners.lean: THE FIRST FAMILY OF "tie m" (TieMatS,
TiePlanSplit.lean) AT EVERY SEGMENT. The witness holds one message a number, and a kept copy and its
original bear one number (arr_same_key). So an array that the state's record names is read, off the pad,
as the message at the owner's number, whoever sent it. One law says that; each sender pays one premise at
its own messages.

  arr_same_key       two seats with one key have one number (P5T.arrOf)
  cell_at_seat       a cell at a seat, off the pad, is the witness's message at that seat's number
  OwnerHolds         the premise on the owners' messages: the packed cells of the owner's segment
  MatSeatS           the public half: where each matrix of the segment is read, at a stand
  tieMatS_of_owners  TieMatS at segment l, from these

THE BORROWED MATRIX. TieMatS ends at packedCells of segment l; the message holds packedCells of the owner's
segment. hSame carries one to the other. It names the input: of completeness's kind, to be paid from the
trace; NOT IN FRONT OF A LAW OVER COINS (the rule: Johnson/Bind/ForProver/FiveFieldsAt.lean).


NO PROPERTY IS CLAIMED.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.TiePlanSplit
import Johnson.Desc.ProofFile.Honest.K1.Law.CellIsWord
import Johnson.Desc.Sound.CellsAtName
import Johnson.P5T.PlanSeats
import Johnson.Prover.Send.Held

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Params OnBytes.Means VerifiableInference.Desc
open OnBytes.Model (HTailF2)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT Mem cellsAt cellsAt_name dataQ seatTab seatOf tabAt seatBy
  noFirst wordsFirst)
open VerifiableInference.Desc.First.Att.P (tableIndex)
open OnBytes.HonestTrace (Sz packedCells)
open ProofFile.Honest.FirstThread (Letters)
open Johnson.Prover.Send (split_index)

/-- (q1): two seats with one key have one number. -/
theorem arr_same_key {ps : List P5T.PSeat} {j t j' t' : ℕ} {p q : P5T.PSeat}
    (hp : ps.find? (fun r => r.j == j && r.t == t) = some p)
    (hq : ps.find? (fun r => r.j == j' && r.t == t') = some q)
    (hk : P5T.keyOf p = P5T.keyOf q) : P5T.arrOf ps j t = P5T.arrOf ps j' t' := by
  unfold P5T.arrOf
  simp only [hp, hq, hk]

/-- **One cell at a seat, off the pad: the witness's message at the seat's number.** -/
theorem cell_at_seat {Cells Tok : Type} (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem)
    (own : List (ℕ × ℕ)) (p : K9.Part) (v : Wit Cells Tok MsgT) (c₀ : ℕ × String) (a : ReqArray)
    (o i c : ℕ) (rp : ℕ × ℕ) (sh : OracleShape) (q : ℕ × ℕ) (y : Mem) (x : _)
    (ha : reqArray p.L.check.rows.layout c₀.1 c₀.2 = some a)
    (ho : p.L.check.frame.whereIs c₀.1 a.message = some o)
    (hok : laidMatrixOk a (p.d.st.rowBits o .main) (p.d.st.placeBits o .main) = true)
    (hrp : laidAt a i c = some rp) (hx : p.d.st.oracles[o]? = some x) (hxs : x.shape = sh)
    (hq : p.d.book.place[o]? = some q) (hseat : seatBy noFirst p.d.book o = some q)
    (hown : own.contains q = true)
    (hy : (ms.find? fun y => decide (seatOf y = q)) = some y) (hsh : (y.1.l.get y.2).1 = sh)
    (hcs : p.d.st.codes = cs) (hr : rp.1 < sh.mainRows)
    (hpad : padB cs sh false rp.1 rp.2 = false) :
    (dataQ own p (seatTab cs arr ms v)).cell c₀.1 c₀.2 i c = v.msg (arr q.1 q.2) false rp.1 rp.2 := by
  have hT : tabAt p.d.st.codes arr (seatBy noFirst p.d.book) p.d.st v o =
      v.tab p.d.st.codes sh (arr q.1 q.2) q.1 q.2 := by
    unfold tabAt
    rw [hseat, hx]
    simp only [hxs]
  have hbits : p.d.st.rowBits o .main = K1.clog sh.mainRows := by
    unfold Statement.rowBits
    rw [hx]
    show ceilLog2 (x.shape.rows Part.main) = _
    rw [hxs]
    rfl
  obtain ⟨e1, e2⟩ := split_index rp.1 rp.2 sh.mainRows hr
  have hreal : tableIndex (p.d.st.rowBits o .main) rp % 2 ^ p.d.st.rowBits o .main <
      realRows p.d.st o .main := by
    rw [hbits]
    unfold realRows tableIndex
    rw [hx]
    show _ < x.shape.rows Part.main
    rw [hxs, Nat.mul_comm (2 ^ K1.clog sh.mainRows) rp.2, e1]
    exact hr
  rw [cell_is_word cs arr ms own p v c₀ a o i c rp sh q y ha ho hok hrp hT hq hown hy hsh hcs hreal]
  show wordsOn p.d.st (tabAt p.d.st.codes arr (seatBy noFirst p.d.book) p.d.st v) o .main _ = _
  unfold wordsOn
  rw [if_pos hreal, hT, hbits, hcs]
  unfold tableIndex
  rw [Nat.mul_comm (2 ^ K1.clog sh.mainRows) rp.2]
  show v.tab cs sh (arr q.1 q.2) q.1 q.2 false _ _ = _
  rw [e1, e2]
  unfold Wit.tab
  rw [if_neg (by rw [hpad]; exact Bool.false_ne_true)]

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr' X' P Cells Tok : Type}

/-- **A hidden premise on the owners' messages**: at number n, at the laid place of array a, at an
element inside the owner's packed shape: the packed cells of the owner's segment, at every list of
challenges no shorter than N. OF COMPLETENESS's KIND. A definition: a premise's form. -/
def OwnerHolds (L : Letters Bk Cl W₀ Rc Xi Tr' X' P Cells Tok MsgT)
    (wit : Local W₀ Rc Xi Tr' → PlaceIn Xi) (Sz₀ : Sz) (n N l₀ ν₀ : ℕ) (a : ReqArray) : Prop :=
  ∀ k w (hd : List Fmt.Drawn), L.valid w → N ≤ hd.length → ∀ i c rp, laidAt a i c = some rp →
    c < (Sz₀.packedShape l₀ ν₀).2 → i < (Sz₀.packedShape l₀ ν₀).1 →
    (L.Q.wit k w hd).msg n false rp.1 rp.2 =
      algebraMap Cb.Gl.F Cb.Gl.E (packedCells Sz₀ (wit w).R.cells.cell l₀ ν₀ i c)

/-- **Public, at a stand: where matrix ν of segment l is read.** own: the owner's number, segment,
matrix and array, off the plan. NM: the record's number of matrices. A definition: a premise's form. -/
def MatSeatS (L : Letters Bk Cl W₀ Rc Xi Tr' X' P Cells Tok MsgT)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr') X' → Prop) (cs : OnBytes.Codes)
    (arr : ℕ → ℕ → ℕ) (ms : List Mem) (Sz₀ : Sz) (b l NM : ℕ)
    (own : ℕ → ℕ × ℕ × ℕ × ReqArray) : Prop :=
  ∀ blk, L.bs[b]? = some blk → ∀ k s μ E ds y cols s', ThrS L.thread Said b k s μ E →
    drawsFit blk.rounds ds = true → L.thread.Stepped blk k s μ E ds y cols s' →
    ∀ tl : HTailF2, s'.tl? = some tl → tl.NM = NM ∧ ∃ p : K9.Part, K9.segAt? s' = some p ∧
    p.d.st.codes = cs ∧
    ∀ ν, ν < NM → ∃ (q : ℕ × ℕ) (yM : Mem) (o : ℕ) (x : _) (sh : OracleShape) (c₁ : ℕ × String)
        (a₁ : ReqArray) (l₀ ν₀ : ℕ),
      (L.N.group l).contains q = true ∧ p.d.st.oracles[o]? = some x ∧ x.shape = sh ∧
      p.d.book.place[o]? = some q ∧ seatBy noFirst p.d.book o = some q ∧
      (ms.find? fun z => decide (seatOf z = q)) = some yM ∧ (yM.1.l.get yM.2).1 = sh ∧
      p.L.arrayOf[tl.gtTree.getD ν 0]? = some c₁ ∧
      reqArray p.L.check.rows.layout c₁.1 c₁.2 = some a₁ ∧
      p.L.check.frame.whereIs c₁.1 a₁.message = some o ∧
      laidMatrixOk a₁ (p.d.st.rowBits o .main) (p.d.st.placeBits o .main) = true ∧
      own ν = (arr q.1 q.2, l₀, ν₀, a₁) ∧
      Sz₀.packedShape l ν = Sz₀.packedShape l₀ ν₀ ∧
      ∀ i c rp, i < (Sz₀.packedShape l ν).1 → c < (Sz₀.packedShape l ν).2 →
        laidAt a₁ i c = some rp → rp.1 < sh.mainRows ∧ padB cs sh false rp.1 rp.2 = false

/-- **The first family at every segment.** hLay: inside the shape the layout lays. hSame: the
borrowed matrix. -/
theorem tieMatS_of_owners {L : Letters Bk Cl W₀ Rc Xi Tr' X' P Cells Tok MsgT}
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr') X' → Prop} {cs : OnBytes.Codes}
    {arr : ℕ → ℕ → ℕ} {ms : List Mem} {Sz₀ : Sz} {wit : Local W₀ Rc Xi Tr' → PlaceIn Xi}
    {b l NM N : ℕ} {own : ℕ → ℕ × ℕ × ℕ × ReqArray}
    (hSeat : MatSeatS L Said cs arr ms Sz₀ b l NM own)
    (hN : N ≤ L.thread.front + roundsTo L.bs b)
    (hHold : ∀ ν, ν < NM → ∀ n l₀ ν₀ a, own ν = (n, l₀, ν₀, a) → OwnerHolds L wit Sz₀ n N l₀ ν₀ a)
    (hLay : ∀ ν, ν < NM → ∀ n l₀ ν₀ a, own ν = (n, l₀, ν₀, a) → ∀ i c,
      i < (Sz₀.packedShape l ν).1 → c < (Sz₀.packedShape l ν).2 → ∃ rp, laidAt a i c = some rp)
    (hSame : ∀ w, L.valid w → ∀ ν, ν < NM → ∀ n l₀ ν₀ a, own ν = (n, l₀, ν₀, a) → ∀ i c,
      i < (Sz₀.packedShape l ν).1 → c < (Sz₀.packedShape l ν).2 →
      packedCells Sz₀ (wit w).R.cells.cell l₀ ν₀ i c = packedCells Sz₀ (wit w).R.cells.cell l ν i c) :
    TieMatS L Said cs arr ms Sz₀ wit b l := by
  intro blk hb k s μ E ds y cols s' hA hd hS tl htl ds' A hAe ν hν c hc i' hi'
  obtain ⟨hNM, p, hp, hcs, hall⟩ := hSeat blk hb k s μ E ds y cols s' hA hd hS tl htl
  have hν' : ν < NM := hNM ▸ hν
  obtain ⟨q, yM, o, x, sh, c₁, a₁, l₀, ν₀, hown, hx, hxs, hq, hseat, hy, hsh, hc₁, ha, ho, hok, hO,
    hShape, hoff⟩ := hall ν hν'
  obtain ⟨rp, hrp⟩ := hLay ν hν' _ _ _ _ hO i' c hi' hc
  obtain ⟨hr, hpad⟩ := hoff i' c rp hi' hc hrp
  have hval : L.valid μ.st.input := hA.1.2.2.2.2.2.2
  have hlenH : μ.st.heard.length = L.thread.front + roundsTo L.bs b := by
    have q' := drawsFit_length _ _ hA.1.2.1
    rw [q', List.length_append]
    rfl
  have hlen : N ≤ (μ.st.heard ++ (ds ++ ds')).length := by
    rw [List.length_append, hlenH]
    omega
  subst hAe
  rw [cellsAt_name _ arr ms L.N l _ s' _ p hp (tl.gtTree.getD ν 0) c₁ hc₁ i' c,
    cell_at_seat cs arr ms _ p _ c₁ a₁ o i' c rp sh q yM x ha ho hok hrp hx hxs hq hseat hown hy hsh
      hcs hr hpad]
  rw [hHold ν hν' _ _ _ _ hO k μ.st.input _ hval hlen i' c rp hrp (hShape ▸ hc) (hShape ▸ hi'),
    hSame μ.st.input hval ν hν' _ _ _ _ hO i' c hi' hc]

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.arr_same_key
#print axioms ProofFile.Honest.K1.cell_at_seat
#print axioms ProofFile.Honest.K1.tieMatS_of_owners
