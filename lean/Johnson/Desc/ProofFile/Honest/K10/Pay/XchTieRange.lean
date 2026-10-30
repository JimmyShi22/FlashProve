-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/XchTieRange.lean: the closing of a segment (K10): the field tie of `CarryOwed`
(Honest/K10/Xch/CarryTop.lean), with the thread a letter, from the one equation a member of Pay/XchOwedMembers.lean, said of a
range of the group's members.

  `TiedRange … lo cnt`   at every stand in front of an accepted closing: at the members of the places lo, …, lo + cnt − 1 in the
                       group's list the witness's table is `K1.rowsMsg` of the rows that the closing's job has made anew
  `TiedRange.append`     two ranges in a row are one
  **`tie_of_range`**       from the range 0, …, cnt − 1, where the group has no more than cnt members: the field tie, to the sign

Limits. `TiedRange` is a definition, meant as a premise or as the end of a law on a sender; it is shown here of no script.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchOwedMembers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc
open VerifiableInference.Desc.First.Close (Par)
open VerifiableInference.Desc.Sound (MsgT wordsFirst tabAt seatBy noFirst)
open P5J (CellsM TS)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K2 (Stretch messageRows freshTable)
open ProofFile.Honest.K2.Law (Laid)
open ProofFile.Honest.K10.YesFree (BaseData CloseBase)

variable {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}

/-- **At the members of a range of places in the group's list, the witness's table is the rows that the closing's job has made
anew.** A definition. -/
def TiedRange (T : Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst)
    (Sc : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT) (Zp : ProofFile.Pub)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (rows : RowDataOf ProofFile.Inst) (stAt : StAtOf ProofFile.Inst) (Gr : ProofFile.Ground)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) (l : Nat) (Qc : Par) (blk : Block TS ProofFile.Cl)
    (lo cnt : Nat) : Prop :=
  ∀ {k s m En ds y cols s'}, StepAt T Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s' →
    ∀ {D}, CloseBase Qc (K9.recOf s) D → ∀ {cc},
      closeCoins (V := Local W₀ Rc ProofFile.Inst Tr) (X := X) Bk (Bk.rowsOf T.chain) (k.look T.chain) blk.place
        (lotJob readers rows stAt Zp Gr Qc) = .ok cc →
      ∀ {R}, (lotJob readers rows stAt Zp Gr Qc).rows m.st.input m.st.heard (handSnd cc).2.2 = .ok R →
      rowsFit s.st D.G R = true →
      ∀ (ds' : List Fmt.Drawn) (o n : Nat) (a : Laid) (nn : Nat) (kk : Stretch) (Rr : Johnson.Prover.Send.Rows),
      n < cnt → D.G.members.idxOf? o = some (lo + n) →
      LotMember readers rows Zp Gr Qc m.st.input m.st.heard (handSnd cc).2.2 (lo + n) a nn →
      Stretch.carried _ (handSnd cc).2.2 nn = .ok kk → messageRows freshTable R.codes a.1 none a.2 kk = .ok Rr →
      tabAt s.st.codes (P5J.At.arr Zp) (seatBy noFirst s.book) s.st
        (Sc.wit k m.st.input (m.st.heard ++ (ds ++ ds'))) o = K1.rowsMsg a.1 Rr

section
variable {T : Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst}
  {Sc : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT} {Zp : ProofFile.Pub}
  {readers : Local W₀ Rc ProofFile.Inst Tr → Readers} {rows : RowDataOf ProofFile.Inst} {stAt : StAtOf ProofFile.Inst} {Gr : ProofFile.Ground}
  {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop} {l : Nat} {Qc : Par} {blk : Block TS ProofFile.Cl}

/-- Two ranges in a row are one. -/
theorem TiedRange.append {lo c₁ c₂ : Nat} (A : TiedRange T Sc Zp readers rows stAt Gr Said l Qc blk lo c₁)
    (B : TiedRange T Sc Zp readers rows stAt Gr Said l Qc blk (lo + c₁) c₂) :
    TiedRange T Sc Zp readers rows stAt Gr Said l Qc blk lo (c₁ + c₂) := by
  intro k s m En ds y cols s' St D Hb cc hcc R hR hfit ds' o n a nn kk Rr hn hi hL hk hmsg
  by_cases c : n < c₁
  · exact A St Hb hcc hR hfit ds' o n a nn kk Rr c hi hL hk hmsg
  · have e : lo + n = lo + c₁ + (n - c₁) := by omega
    rw [e] at hi hL
    exact B St Hb hcc hR hfit ds' o (n - c₁) a nn kk Rr (by omega) hi hL hk hmsg

/-- **The field tie, from a range that holds all the group's members.** -/
theorem tie_of_range {cnt : Nat} (A : TiedRange T Sc Zp readers rows stAt Gr Said l Qc blk 0 cnt)
    (hcount : ∀ {k s m En ds y cols s'}, StepAt T Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s' →
      ∀ {D}, CloseBase Qc (K9.recOf s) D → D.G.members.size ≤ cnt) :
    ∀ {k s m En ds y cols s'}, StepAt T Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s' →
    ∀ {D}, CloseBase Qc (K9.recOf s) D → ∀ {cc},
      closeCoins (V := Local W₀ Rc ProofFile.Inst Tr) (X := X) Bk (Bk.rowsOf T.chain) (k.look T.chain) blk.place
        (lotJob readers rows stAt Zp Gr Qc) = .ok cc →
      ∀ {R}, (lotJob readers rows stAt Zp Gr Qc).rows m.st.input m.st.heard (handSnd cc).2.2 = .ok R →
      rowsFit s.st D.G R = true → ∀ ds',
      OnBytes.Means.tablesOf (D.S1 (K9.recOf s)) (Own.layoutOf (K9.recOf s).st D.G)
          (wordsFirst (P5J.At.arr Zp) s.st s.book (Sc.wit k m.st.input (m.st.heard ++ (ds ++ ds')))) =
        OnBytes.Means.tablesOf (D.S1 (K9.recOf s)) (Own.layoutOf (K9.recOf s).st D.G) (rowWords D (K9.recOf s) R) := by
  intro k s m En ds y cols s' St D Hb cc hcc R hR hfit ds'
  refine tie_of_made (P5J.At.arr Zp) Hb.inOrder.there hfit fun o ho => ?_
  obtain ⟨i, hi⟩ := OnBytes.Means.find_of_mem
    (L := { (default : OnBytes.GroupLayout) with members := D.G.members }) ho
  have hlt : i < D.G.members.size := (OnBytes.Means.find_some hi).1
  have hi' : D.G.members.idxOf? o = some i := hi
  obtain ⟨a, n, flag, Rr, kk, hL, hm, hk, hmsg⟩ := lot_members_all readers rows stAt Zp Gr Qc _ _ _ hR
    (i := i) (by rw [rowsFit_length hfit]; exact hlt)
  refine ⟨i, ⟨a.1, flag⟩, Rr, freshTable, none, a.2, kk, hi', hm, hmsg, ?_⟩
  have e : i = 0 + i := (Nat.zero_add i).symm
  exact A St Hb hcc hR hfit ds' o i a n kk Rr (Nat.lt_of_lt_of_le hlt (hcount St Hb)) (e ▸ hi') (e ▸ hL) hk hmsg

end

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.TiedRange
#print axioms ProofFile.Honest.K10.TiedRange.append
#print axioms ProofFile.Honest.K10.tie_of_range
