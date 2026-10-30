-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/XchOwedMembers.lean: the closing of a segment (K10): the nine premises of the exchange
at the items that a closing owes (`CarryOwed`, Honest/K10/Xch/CarryTop.lean), from five: half and fill (on parameters), made,
and two sentences on the witness's own tables. The sentence in the place of the field tie is here as small as this folder's
files make it: ONE equation for each member of the group.

  `seg_members_len`, `LotMember`, `lot_members_all`   where the lot's job returns rows R: each member number i of R is `memberOf`
           of a shape a.1, a mark, and rows Rr; Rr is what the shared text of a message's rows returned at a.1, the data a.2 and
           the carried stretch number n; `LotMember … i a n` names a and n: the i-th of the last segment's members by the
           segment's public data and the job's own data, and the number of stretches of the segments in front, plus i
  tieM     for such i, a, n, Rr and the member o of the statement's group at place i: the witness's table of o is
           `K1.rowsMsg a.1 Rr`
  freshT   as in Pay/XchOwedTabs.lean

  **`carryOwed_of_members`**   at a block that `Tied` names, and at a second condition Said that gives `SaidOk`: `CarryOwed`

By: `carryOwed_of_three` (Pay/XchOwedThree.lean); `tie_of_made` (Pay/XchTieFit.lean); `seg_member_at` (Pay/XchRowsAt.lean);
`fresh_of_base` (Pay/XchFreshAt.lean).

Limits. The five are premises, shown here of no prover, script or state. The head is a premise. The thread stands at the
exact carry. The full size and the older hash alone.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchOwedThree
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchTieFit
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchRowsAt
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchFreshAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.First.Close (Par)
open VerifiableInference.Desc.First.K2Caller (doorZ)
open VerifiableInference.Desc.K2.Honest (carryExact)
open VerifiableInference.Desc.Sound (MsgT wordsFirst tabAt seatBy noFirst)
open VerifiableInference.Desc.K2.Honest (GroupMember)
open OnBytes.Slice (readE)
open OnBytes.Maker (WholeD)
open Johnson.Prover.Link (Pairs)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K10.YesFree (BaseData CloseBase)
open ProofFile.Honest.K10.LeftIs (stageB freshB)

open Johnson.Prover.Send (Rows)
open ProofFile.Honest.K2 (SegmentPub GroupRows Stretch FreshTable closingFrom messageRows freshTable)
open ProofFile.Honest.K2.Law (Laid rowsCore inFirstOf laterOf segmentRows_eq)

/-- Where the text of a segment's group's rows returns without the fresh mask: as many members, and as many rows, as the
two lists hold. -/
theorem seg_members_len {table : FreshTable} {S : SegmentPub} {ps : Bool} {prevKept : List OnBytes.OracleShape}
    {A : List Laid} {B : List Laid × Nat} {k : Nat → Except String Stretch} {base : Nat} {GR : GroupRows}
    (h : rowsCore table S ps prevKept A B k base false = .ok GR) :
    GR.members.length = (A ++ B.1).length ∧ GR.rows.length = (A ++ B.1).length := by
  obtain ⟨rows₀, rows₁, h0, h1, hm, hr⟩ := rowsCore_inv h
  have hfl := rowsCore_flags h
  have l0 : rows₀.length = A.length := by rw [mapM_len _ _ _ h0, List.length_zipIdx]
  have l1 : rows₁.length = B.1.length := by rw [mapM_len _ _ _ h1, List.length_zipIdx]
  refine ⟨?_, ?_⟩
  · rw [hm, List.length_map, List.length_zip, List.length_map, hfl, List.length_append, Nat.min_self]
  · rw [hr, List.length_append, List.length_append, l0, l1]

section
variable {W₁ Rc₁ Xi₁ Tr₁ : Type}

/-- **The i-th member of the last segment, as the lot's job takes it.** a: its shape by the segment's public data, and its
data by the job's own texts. n: the number of its carried stretch. -/
def LotMember (readers : Local W₁ Rc₁ Xi₁ Tr₁ → Readers) (rows : RowDataOf Xi₁) (Z : ProofFile.Pub) (G : ProofFile.Ground) (Q : Par)
    (w : Local W₁ Rc₁ Xi₁ Tr₁) (front : List Fmt.Drawn) (ca : CsAll (closeCarries ⟨Q, borneAt Z Q⟩)) (i : Nat) (a : Laid)
    (n : Nat) : Prop :=
  ∃ (S : SegmentPub) (x : Option (VerifiableInference.Desc.K2.Honest.Left × List OnBytes.OracleShape) × Nat),
    (lotSegs Z G Q).getLast? = some S ∧
    closingFrom freshTable (lotOwn readers rows Z G Q w front) front (Stretch.carried _ ca)
      (lotSegs Z G Q).dropLast 0 0 none = .ok x ∧
    (inFirstOf S (x.1.map (·.1)) (lotOwn readers rows Z G Q w front ((lotSegs Z G Q).length - 1)) ++
      (laterOf S (x.1.map (·.1)).isSome
        (lotOwn readers rows Z G Q w front ((lotSegs Z G Q).length - 1))).1)[i]? = some a ∧
    n = x.2 + i

/-- Every member of what the lot's job returns. -/
theorem lot_members_all (readers : Local W₁ Rc₁ Xi₁ Tr₁ → Readers) (rows : RowDataOf Xi₁) (stAt : StAtOf Xi₁) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) (Q : Par) (w : Local W₁ Rc₁ Xi₁ Tr₁) (front : List Fmt.Drawn)
    (ca : CsAll (closeCarries (lotJob readers rows stAt Z G Q).pub)) {R : GroupData}
    (h : (lotJob readers rows stAt Z G Q).rows w front ca = .ok R) {i : Nat} (hi : i < R.members.length) :
    ∃ (a : Laid) (n : Nat) (flag : Bool) (Rr : Rows) (kk : Stretch),
      LotMember readers rows Z G Q w front ca i a n ∧ R.members[i]? = some (memberOf ⟨a.1, flag⟩ Rr) ∧
      Stretch.carried _ ca n = .ok kk ∧ messageRows freshTable R.codes a.1 none a.2 kk = .ok Rr := by
  obtain ⟨S, GR, hL, hG, rfl⟩ := lot_rows_inv readers rows stAt Z G Q w front ca h
  obtain ⟨x, hx, hS⟩ := groupRows_inv hL hG
  rw [segmentRows_eq] at hS
  obtain ⟨e1, e2⟩ := seg_members_len hS
  have hlen : (rowsOut S GR).members.length = GR.members.length := by
    show ((GR.members.zip GR.rows).map fun x => memberOf x.1 x.2).length = _
    rw [List.length_map, List.length_zip, e1, e2, Nat.min_self]
  rw [hlen, e1] at hi
  obtain ⟨flag, Rr, kk, h1, h2, h3, h4⟩ := seg_member_at hS (inFirst_length S _ _) (List.getElem?_eq_getElem hi)
  exact ⟨_, x.2 + i, flag, Rr, kk, ⟨S, x, hL, hx, List.getElem?_eq_getElem hi, rfl⟩, out_at S GR h1 h2, h3, h4⟩

end

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Sc : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (rows : RowDataOf ProofFile.Inst) (stAt : StAtOf ProofFile.Inst)
  (Gr : ProofFile.Ground) (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

-- The exact carry at the head's letters; the first chain's thread under the head at that value of the carry. The option
-- turns off one early look at a notation's text, which has no case for a field access or a named argument; it loosens
-- nothing in what Lean checks of a theorem.
set_option quotPrecheck false in
local notation "𝕏" => (carryExact (P := ProofFile.InstPub) (Cells := CellsM OnBytes.Flat.numsFull) (Tok := P5J.At.Tok) Zp
  (P5J.At.arr Zp))
set_option quotPrecheck false in
local notation "𝕋X" => (lettersHead h H Sc test 𝕏 item n₁ n₂ b₀ Vd Rd Kp w).thread

/-- **`CarryOwed` from half, fill, made, one equation for each member, and the sentence on the fresh mask's table**, at a block that `Tied` names and at a Said that gives `SaidOk`. -/
theorem carryOwed_of_members (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    {l : Nat} {p : VerifiableInference.Desc.K9.Where} {Qc : Par} {blk : Block TS ProofFile.Cl}
    (Td : Tied cF Zp l p Qc blk)
    (half : ClosingsFirst H.first readers rows stAt Zp Gr)
    (fill : stAt = fun ξ : ProofFile.Inst => stAtZero cF.blocksInOrder (ProofFile.startS Zp) ξ.pub)
    (made : ∀ {k s m En ds y cols s'}, StepAt 𝕋X Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s' →
      ∀ {D}, CloseBase Qc (K9.recOf s) D → ∀ {cc},
        closeCoins (V := Local W₀ Rc ProofFile.Inst Tr) (X := X) Bk (Bk.rowsOf (𝕋X).chain) (k.look (𝕋X).chain) blk.place
          (lotJob readers rows stAt Zp Gr Qc) = .ok cc →
        ∃ R, (lotJob readers rows stAt Zp Gr Qc).rows m.st.input m.st.heard (handSnd cc).2.2 = .ok R ∧
          rowsFit s.st D.G R = true)
    (tieM : ∀ {k s m En ds y cols s'}, StepAt 𝕋X Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s' →
      ∀ {D}, CloseBase Qc (K9.recOf s) D → ∀ {cc},
        closeCoins (V := Local W₀ Rc ProofFile.Inst Tr) (X := X) Bk (Bk.rowsOf (𝕋X).chain) (k.look (𝕋X).chain) blk.place
          (lotJob readers rows stAt Zp Gr Qc) = .ok cc →
        ∀ {R}, (lotJob readers rows stAt Zp Gr Qc).rows m.st.input m.st.heard (handSnd cc).2.2 = .ok R →
        rowsFit s.st D.G R = true →
        ∀ (ds' : List Fmt.Drawn) (o i : Nat) (a : Laid) (n : Nat) (kk : Stretch) (Rr : Rows),
        D.G.members.idxOf? o = some i →
        LotMember readers rows Zp Gr Qc m.st.input m.st.heard (handSnd cc).2.2 i a n →
        Stretch.carried _ (handSnd cc).2.2 n = .ok kk → messageRows freshTable R.codes a.1 none a.2 kk = .ok Rr →
        tabAt s.st.codes (P5J.At.arr Zp) (seatBy noFirst s.book) s.st
          (Sc.wit k m.st.input (m.st.heard ++ (ds ++ ds'))) o = K1.rowsMsg a.1 Rr)
    (freshT : ∀ {k s m En ds y cols s'}, StepAt 𝕋X Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s' →
      ∀ {D}, CloseBase Qc (K9.recOf s) D → ∀ {cc},
        closeCoins (V := Local W₀ Rc ProofFile.Inst Tr) (X := X) Bk (Bk.rowsOf (𝕋X).chain) (k.look (𝕋X).chain) blk.place
          (lotJob readers rows stAt Zp Gr Qc) = .ok cc →
        ∀ (ds' : List Fmt.Drawn) (b j : Nat), b < 2 ^ (stageB D (K9.recOf s)).h → j < (stageB D (K9.recOf s)).Z.l →
        tabAt s.st.codes (P5J.At.arr Zp) (seatBy noFirst s.book) s.st
            (Sc.wit k m.st.input (m.st.heard ++ (ds ++ ds'))) D.m true b j =
          (⟨(stageB D (K9.recOf s)).h + (stageB D (K9.recOf s)).g, (stageB D (K9.recOf s)).h⟩ : K1.Ride).lay
            (fun n => readE (wordsAll (spentRun (lotJob readers rows stAt Zp Gr Qc) (handSnd cc)) n)) b j) :
    CarryOwed h H Sc test item n₁ n₂ b₀ Vd Rd Kp w readers rows stAt Gr Said l Qc blk :=
  carryOwed_of_three h H Sc test item n₁ n₂ b₀ Vd Rd Kp w readers rows stAt Gr Said hSaid Td half fill made
    (fun St _ Hb _ hcc _ hR hfit ds' =>
      tie_of_made (P5J.At.arr Zp) Hb.inOrder.there hfit fun o ho => by
        obtain ⟨i, hi⟩ := OnBytes.Means.find_of_mem
          (L := { (default : OnBytes.GroupLayout) with members := _ }) ho
        have hlt := (OnBytes.Means.find_some hi).1
        obtain ⟨a, n, flag, Rr, kk, hL, hm, hk, hmsg⟩ := lot_members_all readers rows stAt Zp Gr Qc _ _ _ hR
          (i := i) (by rw [rowsFit_length hfit]; exact hlt)
        exact ⟨i, ⟨a.1, flag⟩, Rr, freshTable, none, a.2, kk, hi, hm, hmsg,
          tieM St Hb hcc hR hfit ds' o i a n kk Rr hi hL hk hmsg⟩)
    (fun St _ Hb _ hcc ds' W hW =>
      fresh_of_base Hb (P5J.At.arr Zp) _ rfl _ (freshT St Hb hcc ds') W hW)

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.seg_members_len
#print axioms ProofFile.Honest.K10.LotMember
#print axioms ProofFile.Honest.K10.lot_members_all
#print axioms ProofFile.Honest.K10.carryOwed_of_members
