-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/ClosingSaysAt.lean: at a stand of the library's own thread in
front of the first chain's closing proximity test, the rows that the test takes in say their claims
of the words that the plain rows make, where these are the thread's witness's words on the members'
tables. The pieces of ClosingSays.lean joined at member 354.

  `rowsDue_filter`  the count of open rows reads the open classes of the segment alone
  `open_carried`, `open_position`, `open_sample`   the three items are open at 354
  `open_classes_354`  the classes of segment 25 in its group's list that are open there
  `rowsDue_354`     so the count due is those two classes'
  `says_head_L`     the clause on values of `DataFront`, at the stand

By what. `rows_of_thr`, `open_of_classes`, `samples_of_class`, `allSay_at_items` (ClosingSays.lean);
`rowsAtFit_at` (Johnson/LPFK9R/RowsAtFitAt.lean); `members_placed`, `pins_354`, `rowOpen_354`
(Johnson/Loose/H2K12/); `tidy_at_finish` and `four_at_finish` (K12/AtProof/FieldsAtFinish.lean).

Hypotheses of `says_head_L`. hT: the stand. hr, he: the state is reached and the way in returns R. hw:
the witness's words are the plain rows' on the members' tables.

Limits.
- hw is the tie of the witness to the rows: it stays a premise, and it can say no.
- Full size, the format's own hash alone.
- Nothing on completeness of the chain, soundness or hiding.

NOT IN FRONT OF A LAW OVER COINS: `says_head_L` bears this label; the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean. Its ground: the thread from `Thr` as a premise.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingSays
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingHead
import Johnson.Desc.ProofFile.Honest.K12.AtProof.FieldsAtFinish
import Johnson.Desc.Sound.MgAll
import Johnson.LPFK9R.RowsAtFitAt
import Johnson.Loose.H2K12.PublicAt354

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice OnBytes.Means
open VerifiableInference.Desc (Block Chain Place Strs)
open VerifiableInference.Desc.K12 (T12 enterFinish)
open VerifiableInference.Desc.First (S Item RowClass Numbers start rowsDue rowsHeld membersHeld
  rowSegs wordsAtFirst)
open VerifiableInference.Desc.Sound (MsgT below wordsFirst)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile.Honest.FirstThread (lettersHead Script WtF)
open ProofFile.Honest.K12.Light (WordsTied)
open ProofFile.Honest.K12.AtProof (four_at_finish)
open P5J (AtMgA CellsM TS)

/-- An item that counts among the open rows of a segment's list. -/
def inListOf (n : Nat) (i : VerifiableInference.Desc.First.Item) : Bool :=
  match i with
  | .row m c => m == n && c.inList
  | _ => false

/-- One step of `rowsDue`'s count. -/
def dueStep (N : Numbers) (n k : Nat) (i : VerifiableInference.Desc.First.Item) : Nat :=
  match i with
  | .row m' c => if m' == n && c.inList then k + (N.rowsAt n c).2 else k
  | _ => k

theorem dueStep_off (N : Numbers) (n k : Nat) (i : VerifiableInference.Desc.First.Item)
    (h : inListOf n i = false) : dueStep N n k i = k := by
  cases i with
  | row m c =>
    have h' : (m == n && c.inList) = false := h
    simp [dueStep, h']
  | _ => rfl

theorem foldl_filter (N : Numbers) (n : Nat) :
    ∀ (l : List VerifiableInference.Desc.First.Item) (k : Nat),
      l.foldl (dueStep N n) k = (l.filter (inListOf n)).foldl (dueStep N n) k
  | [], _ => rfl
  | i :: l, k => by
    cases hf : inListOf n i with
    | true =>
      rw [List.filter_cons_of_pos (by simpa using hf), List.foldl_cons, List.foldl_cons]
      exact foldl_filter N n l _
    | false =>
      rw [List.filter_cons_of_neg (by simpa using hf), List.foldl_cons, dueStep_off N n k i hf]
      exact foldl_filter N n l k

/-- **The count of open rows reads those items alone.** -/
theorem rowsDue_filter (N : Numbers) (n : Nat) (O : List VerifiableInference.Desc.First.Item) :
    rowsDue N O n = rowsDue N (O.filter (inListOf n)) n :=
  foldl_filter N n O 0

theorem open_carried : (fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps)
    354).contains (Item.row 25 .carried) = true := by
  decide +kernel

theorem open_position : (fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps)
    354).contains (Item.row 25 .position) = true := by
  decide +kernel

theorem open_sample : (fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps)
    354).contains (Item.row 25 (.sample 0)) = true := by
  decide +kernel

/-- At the library's open sets the classes of segment 25 in its group's list. -/
theorem open_classes_354 : H2K12.O354.filter (inListOf 25) =
    [Item.row 25 .carried, Item.row 25 .position] := by
  decide +kernel

theorem rowsDue_354 (N : Numbers) :
    rowsDue N H2K12.O354 25 = (N.rowsAt 25 .carried).2 + (N.rowsAt 25 .position).2 := by
  rw [rowsDue_filter, open_classes_354]
  have e : rowsDue N [Item.row 25 .carried, Item.row 25 .position] 25 =
      0 + (N.rowsAt 25 .carried).2 + (N.rowsAt 25 .position).2 := rfl
  rw [e, Nat.zero_add]

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The rows taken in say their claims**, at a stand. -/
theorem says_head_L (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr) {k : Coins Bk} {s : S} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {E : Env} (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 354 k s m E)
    {p : ProofFile.InstPub} (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 354 (p, s)) {R : T12}
    (he : enterFinish s = .ok R) (Rr : PlainRows) {G : Group} (hG : R.st.groups[R.g]? = some G)
    (hw : WordsTied R.st R.g G
      (wordsFirst (P5J.At.arr Zp) s.st s.book
        ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.wit k m.st.input
          (m.st.heard ++ [])))
      (layoutOf R.st G) Rr) :
    AllSay rdE (begun R.st R.g G) (runRows R.st G).toList
      (wordsAt (begun R.st R.g G) (layoutOf R.st G) Rr) := by
  obtain ⟨o, -, -, -, e⟩ := VerifiableInference.Desc.K12.Seat.enterFinish_ok s R he
  have est : R.st = s.st := by rw [e]
  have four := four_at_finish h.toAtMg hr he
  have hg : R.g = 25 := four.2.2.2
  have hti := VerifiableInference.Desc.Ground.Sh.tidy_of four.1
  rw [est] at hti
  rw [est, hg] at hG hw ⊢
  have hG' : s.st.groups[(P5J.At.N Zp cF).groupAt 25]? = some G := hG
  have h' := hT
  unfold Thr at h'
  obtain ⟨-, -, hF, -, -, -, -⟩ := h'
  obtain ⟨hf, -, hc⟩ := hF
  have hfail : s.failed = none :=
    Option.isNone_iff_eq_none.1 (show s.failed.isNone = true from hf)
  rcases hc with hc | ⟨hb, -, -, -⟩
  · exact absurd hfail hc
  simp only [Bool.and_eq_true] at hb
  have hrows : rowsHeld (P5J.At.N Zp cF) H2K12.O354 s = true := hb.1.1.1.1.2
  have hmem : membersHeld (P5J.At.N Zp cF) H2K12.O354 s = true := hb.1.1.1.2
  have hsize : G.rows.size ≤ ((P5J.At.N Zp cF).rowsAt 25 .carried).2 +
      ((P5J.At.N Zp cF).rowsAt 25 .position).2 := by
    unfold rowsHeld at hrows
    have q := List.all_eq_true.1 hrows 25 H2K12.rowOpen_354
    simp only [hG', Bool.and_eq_true, beq_iff_eq] at q
    rw [q.1.2, rowsDue_354]
  have hfit := LPFK9.rowsAtFit_at h
  unfold VerifiableInference.Desc.First.rowsAtFit at hfit
  simp only [Bool.and_eq_true] at hfit
  have hq := List.all_eq_true.1 hfit.2 25 (List.mem_range.2 (by decide +kernel))
  simp only [Bool.and_eq_true, beq_iff_eq] at hq
  obtain ⟨⟨⟨⟨h0', h1'⟩, -⟩, -⟩, -⟩ := hq
  have h0 : ((P5J.At.N Zp cF).rowsAt 25 .carried).1 = 0 := h0'
  have h1 : ((P5J.At.N Zp cF).rowsAt 25 .position).1 = ((P5J.At.N Zp cF).rowsAt 25 .carried).2 := h1'
  have hM : ∀ v, ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).Mg v).row =
      VerifiableInference.Desc.First.rowSays (P5J.At.N Zp cF) (wordsAtFirst (P5J.At.arr Zp)) :=
    fun _ => rfl
  have c1 := rows_of_thr _ _ hM (List.contains_iff_mem.1 open_carried) hT
  have c2 := rows_of_thr _ _ hM (List.contains_iff_mem.1 open_position) hT
  have c3 := rows_of_thr _ _ hM (List.contains_iff_mem.1 open_sample) hT
  refine allSay_at_items s.st 25 G hG hti.inOrder hti.kinds _
    (open_of_classes hG' c1 c2 h0 h1 hsize)
    (samples_of_class c3 fun o ho => ?_) _ _ hw
  obtain ⟨q, hq1, hq2⟩ := H2K12.members_placed _ _ s 25 H2K12.rowOpen_354 hmem G hG' o ho
  rw [H2K12.pins_354] at hq2
  rw [hq1]
  simpa using hq2

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.rowsDue_filter
#print axioms ProofFile.Honest.K12.rowsDue_354
#print axioms ProofFile.Honest.K12.says_head_L
