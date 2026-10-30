-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/XchThreeLeft.lean: the closing of a segment (K10): the record `ThreeLeft` (Pay/Five.lean: the
three premises of the exchange at a closing that are still unpaid: made, tie, fresh), with the thread a letter, from the field
made and this folder's records on the senders of the group's members and of the fresh mask.

  `threeLeft_of_range`     from made, a range of tied members that holds the whole group, and the field fresh
  **`threeLeft_at_switch`**  at a segment into which a code switch leads (segments 1 to 24): from made; the record on the switch's
                         sending (`TieBySwitch`); two records on the shared kind's later sendings (`TieByShared`); the count of the
                         group's members; the record on the fresh mask (`FreshBySwitch`)
  **`threeLeft_at_first`**   at the first segment: three records on the shared kind's sendings; the count; `FreshByShared`

That Lean takes these terms as members of `ThreeLeft` is the check that the ends of `tie_of_range`, `fresh_by_switch` and
`fresh_by_shared` are that record's fields to the sign.

Limits. The records are premises, shown here of no script, book, thread or run; made is a premise.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.Five
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchTieBySwitch
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchTieByShared
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchFreshField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open Johnson.Prover.Link (Pairs)
open VerifiableInference.Desc
open VerifiableInference.Desc.First.Close (Par)
open VerifiableInference.Desc.Sound (MsgT wordsFirst)
open P5J (CellsM TS)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K2 (SegmentPub SwitchPlace switchSent lotClosingAt)
open ProofFile.Honest.K10.LeftIs (stageB freshB)
open ProofFile.Honest.K10.YesFree (BaseData CloseBase)

variable {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  {T : Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst}
  {Sc : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT} {Zp : ProofFile.Pub}
  {readers : Local W₀ Rc ProofFile.Inst Tr → Readers} {rows : RowDataOf ProofFile.Inst} {stAt : StAtOf ProofFile.Inst} {Gr : ProofFile.Ground}
  {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop} {l : Nat} {Qc : Par} {blk : Block TS ProofFile.Cl}

/-- From made, a range of tied members that holds the whole group, and the field fresh. -/
theorem threeLeft_of_range
    (made : ∀ {k s m En ds y cols s'}, StepAt T Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s' →
      ∀ {D}, CloseBase Qc (K9.recOf s) D → ∀ {cc},
        closeCoins (V := Local W₀ Rc ProofFile.Inst Tr) (X := X) Bk (Bk.rowsOf T.chain) (k.look T.chain) blk.place
          (lotJob readers rows stAt Zp Gr Qc) = .ok cc →
        ∃ R, (lotJob readers rows stAt Zp Gr Qc).rows m.st.input m.st.heard (handSnd cc).2.2 = .ok R ∧
          rowsFit s.st D.G R = true)
    {cnt : Nat} (A : TiedRange T Sc Zp readers rows stAt Gr Said l Qc blk 0 cnt)
    (hcount : ∀ {k s m En ds y cols s'}, StepAt T Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s' →
      ∀ {D}, CloseBase Qc (K9.recOf s) D → D.G.members.size ≤ cnt)
    (fresh : ∀ {k s m En ds y cols s'}, StepAt T Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s' →
      ∀ {D}, CloseBase Qc (K9.recOf s) D → ∀ {cc},
        closeCoins (V := Local W₀ Rc ProofFile.Inst Tr) (X := X) Bk (Bk.rowsOf T.chain) (k.look T.chain) blk.place
          (lotJob readers rows stAt Zp Gr Qc) = .ok cc →
        ∀ ds' W, CoefOf (spentRun (lotJob readers rows stAt Zp Gr Qc) (handSnd cc)) W →
        Pairs (stageB D (K9.recOf s)) (stageB D (K9.recOf s)).Z.l W
          (freshB D (K9.recOf s)
            (wordsFirst (P5J.At.arr Zp) s.st s.book (Sc.wit k m.st.input (m.st.heard ++ (ds ++ ds')))))) :
    ThreeLeft T Sc Zp readers rows stAt Gr Said l Qc blk where
  made := made
  tie := tie_of_range A hcount
  fresh := fresh

/-- **At a segment into which a code switch leads.** -/
theorem threeLeft_at_switch {Wj Xj : Type}
    (made : ∀ {k s m En ds y cols s'}, StepAt T Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s' →
      ∀ {D}, CloseBase Qc (K9.recOf s) D → ∀ {cc},
        closeCoins (V := Local W₀ Rc ProofFile.Inst Tr) (X := X) Bk (Bk.rowsOf T.chain) (k.look T.chain) blk.place
          (lotJob readers rows stAt Zp Gr Qc) = .ok cc →
        ∃ R, (lotJob readers rows stAt Zp Gr Qc).rows m.st.input m.st.heard (handSnd cc).2.2 = .ok R ∧
          rowsFit s.st D.G R = true)
    {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop} {lay : OnBytes.Params.ReqLayout} {segs : List SegmentPub} {p : SwitchPlace}
    {N fx : Nat} {seat : Nat → Nat × Nat}
    (Fs : TieBySwitch T Sc Zp readers rows Gr Said l Qc blk Vd lay segs p N fx seat)
    {wit : Local W₀ Rc ProofFile.Inst Tr → Wj} {J₁ J₂ : K1.SendJob Wj Xj} {own₀ : Xj} {N₁ f₁ c₁ N₂ f₂ c₂ : Nat}
    {seat₁ seat₂ : Nat → Nat × Nat}
    (F₁ : TieByShared T Sc Zp readers rows Gr Said l Qc blk Vd wit J₁ own₀ N₁ f₁
      (0 + ((switchSent p.sizes p.others).size - 1)) c₁ seat₁)
    (F₂ : TieByShared T Sc Zp readers rows Gr Said l Qc blk Vd wit J₂ own₀ N₂ f₂
      (0 + ((switchSent p.sizes p.others).size - 1 + c₁)) c₂ seat₂)
    (hcount : ∀ {k s m En ds y cols s'}, StepAt T Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s' →
      ∀ {D}, CloseBase Qc (K9.recOf s) D → D.G.members.size ≤ (switchSent p.sizes p.others).size - 1 + c₁ + c₂)
    {Nf jf tf : Nat} (Ff : FreshBySwitch T Sc Zp readers rows Said l Qc blk Vd (lotClosingAt lay segs) p Nf fx jf tf) :
    ThreeLeft T Sc Zp readers rows stAt Gr Said l Qc blk := by
  refine threeLeft_of_range made (TiedRange.append (TiedRange.append ?_ ?_) ?_) hcount (fresh_by_switch Ff stAt Gr)
  · intro k s m En ds y cols s' St
    exact tied_by_switch Fs stAt St
  · intro k s m En ds y cols s' St
    exact tied_by_shared F₁ stAt St
  · intro k s m En ds y cols s' St
    exact tied_by_shared F₂ stAt St

/-- **At the first segment.** -/
theorem threeLeft_at_first {Wj Xj : Type}
    (made : ∀ {k s m En ds y cols s'}, StepAt T Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s' →
      ∀ {D}, CloseBase Qc (K9.recOf s) D → ∀ {cc},
        closeCoins (V := Local W₀ Rc ProofFile.Inst Tr) (X := X) Bk (Bk.rowsOf T.chain) (k.look T.chain) blk.place
          (lotJob readers rows stAt Zp Gr Qc) = .ok cc →
        ∃ R, (lotJob readers rows stAt Zp Gr Qc).rows m.st.input m.st.heard (handSnd cc).2.2 = .ok R ∧
          rowsFit s.st D.G R = true)
    {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop} {wit : Local W₀ Rc ProofFile.Inst Tr → Wj} {J₀ J₁ J₂ : K1.SendJob Wj Xj} {own₀ : Xj}
    {N₀ f₀ c₀ N₁ f₁ c₁ N₂ f₂ c₂ : Nat} {seat₀ seat₁ seat₂ : Nat → Nat × Nat}
    (F₀ : TieByShared T Sc Zp readers rows Gr Said l Qc blk Vd wit J₀ own₀ N₀ f₀ 0 c₀ seat₀)
    (F₁ : TieByShared T Sc Zp readers rows Gr Said l Qc blk Vd wit J₁ own₀ N₁ f₁ (0 + c₀) c₁ seat₁)
    (F₂ : TieByShared T Sc Zp readers rows Gr Said l Qc blk Vd wit J₂ own₀ N₂ f₂ (0 + (c₀ + c₁)) c₂ seat₂)
    (hcount : ∀ {k s m En ds y cols s'}, StepAt T Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s' →
      ∀ {D}, CloseBase Qc (K9.recOf s) D → D.G.members.size ≤ c₀ + c₁ + c₂)
    {Nf ff nf jf tf : Nat} (Ff : FreshByShared T Sc Zp Said l Qc blk Vd wit J₀ own₀ Nf ff nf jf tf) :
    ThreeLeft T Sc Zp readers rows stAt Gr Said l Qc blk := by
  refine threeLeft_of_range made (TiedRange.append (TiedRange.append ?_ ?_) ?_) hcount
    (fresh_by_shared Ff readers rows stAt Gr)
  · intro k s m En ds y cols s' St
    exact tied_by_shared F₀ stAt St
  · intro k s m En ds y cols s' St
    exact tied_by_shared F₁ stAt St
  · intro k s m En ds y cols s' St
    exact tied_by_shared F₂ stAt St

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.threeLeft_of_range
#print axioms ProofFile.Honest.K10.threeLeft_at_switch
#print axioms ProofFile.Honest.K10.threeLeft_at_first
