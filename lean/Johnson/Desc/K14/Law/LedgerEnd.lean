-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerEnd.lean: THE CHAIN's END AT THE LEDGER OF A PROOF FILE's SHARED CHAIN:
what a kind's files owe at block 11 (ClauseAt, Johnson/Desc/Sound/LedgerClause.lean), with a split,
at the table's files' own filling (meaningSigS, promSigS, extS:
Johnson/Desc/Sound/BordersSharedFill.lean). The table's row 11 is empty; the one shared item that is
open there is o_omega's pin; the promise behind has "nothing is left untested" more. The block has
one written round, the seal, in which nothing is drawn: ALL IS FOR CERTAIN, at any errors.

  ins11, lays11, proms11, proms12, open11   the table at 11 and 12, by evaluation.
  end_clause      **the clause at block 11**, at any piece whose block, at a yes, leaves the chain's
                  own record and has found every clause of ask true.
  end_wrapped     its first premise at the wrap in which a description's pieces hold blocks, for a
                  block that is exact for ask (ChainEnd.Exact, Johnson/Desc/ChainEndExact.lean).
  end_at_last     so at the shared chain's own last block (K12.Seat.last,
                  Johnson/Desc/K12/Seat/Fill.lean: chainEnd 2 11 true … untestedL).
THE PREMISES, AND WHOSE EACH IS. hend: the block's text (paid by end_wrapped) · hB: four comparisons
of numbers for o_omega's tree (the plan's and the tiling's) · htab: the stored table's promise reads
the oracles through the stored table alone (the table's files' filling) · hS: the book-keeping 11
gives 12 at one record (whoever fills shape 11 | 12) · hnl: the letter nothingLeft is the end's own
test (a filling).
What is not claimed. NO MEMBER IS SHOWN. A block that refuses all meets the clause. No soundness of
a verifier.

-/
import Johnson.Desc.K14.Law.LedgerSplitFilled
import Johnson.Desc.K14.Law.LedgerWrap
import Johnson.Desc.ChainEndExact
import Johnson.Desc.K12.Seat.Fill

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Cb Johnson.Pack Desc.Plain
open Iop Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words)
open VerifiableInference.Desc (Block Strs Wit FileDescription smpHeld smpSeed smpRows oracleNo)
open VerifiableInference.Desc.ChainEnd (Clauses Exact untestedL chainEnd_exact)
open VerifiableInference.Desc.K1 (SameMsgs)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared

/-- The table's row 11 names nothing in front. -/
theorem ins11 (i : ItemS) : ¬ insSh true 11 i := by
  have hr : (rowAtS true 11).ins ++ (rowAtS true 11).ctx = [] := rfl
  unfold insSh
  rw [hr]
  rintro ⟨_, h⟩
  cases h

theorem lays11 : laysAtS true 11 = [] := rfl

theorem proms11 : promsAt true 11 = [.tablePromise, .shape 11, .noColl .oOmega] := by decide

theorem proms12 :
    promsAt true 12 = [.tablePromise, .shape 12, .noColl .oOmega, .nothingLeft] := by decide

/-- The one shared item that is open in front of the end is o_omega's pin. -/
theorem open11 (i : ItemS) (h : openSh true 11 i) : i = .pin .oOmega := by
  have h1 := (openSh_iff true 11 i).1 h
  have h2 : ∀ j ∈ openL (insLSh true) (outsLSh true) startLSh 11, j = ItemS.pin .oOmega := by decide
  exact h2 i h1

variable {P₁ Cl Xi Cells Tok : Type} {Fr : Frame} (cs : OnBytes.Codes) (G : FileDescription Xi)
  (arr : ℕ → ℕ → ℕ)
  (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem) (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells) (c₀ : Cells)
  (stOf : St → OnBytes.Statement) (bookOf : St → OnBytes.TreeBook)
  (N : NumbersS) (Mg : MeaningS St P₁ (Wit Cells Tok MsgT)) (Pm : PromMeaning St)
  (Oc : P₁ → Strs → Prop)
  (p : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
  (l : List (Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)))

/-- **The chain's end at the ledger.** -/
theorem end_clause (ask : St → Clauses)
    (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (ε : Err (uLT (ckP .two) x.ds))
    (hend : ∀ t rs gs t', x.b.decide t rs gs = .ok t' →
      t'.2 = t.2 ∧ ∀ c ∈ ask t.2, c.2 = true)
    (hB : SentBefore N p l 11 x .oOmega)
    (htab : ∀ (s : St) y y', y'.cell = y.cell → Pm.tablePromise s y → Pm.tablePromise s y')
    (hS : ∀ s, Pm.shape 11 s = true → Pm.shape 12 s = true)
    (hnl : ∀ s, (∀ c ∈ ask s, c.2 = true) → Pm.nothingLeft s = true) :
    ClauseAt N (meaningSigS cs G arr smp₂ ms decT₂ Mg) (promSigS cs G smp₂ ms stOf bookOf Pm) Oc
      true p l
      (fun k v w => extS cs G arr smp₂ ms decT₂ c₀ N true k v.1 (strsOfAct Fr v) w) 11 x ε := by
  have hyes : ∀ a τ b, x.ior.red.out a τ = some b →
      b.1.2 = a.1.2 ∧ ∀ c ∈ ask a.1.2, c.2 = true := by
    intro a τ b hout
    obtain ⟨_, gs, hd⟩ := piece_yes x a τ b hout
    exact hend _ _ gs _ hd
  refine empty_clause N _ _ Oc true p l _ 11 ins11 x ε
    (fun v w => extS_id cs G arr smp₂ ms decT₂ c₀ N true 11 lays11 _ _ w) ?_ ?_
  · intro a τ b ha hout c hc
    obtain ⟨e, hask⟩ := hyes a τ b hout
    rw [proms12] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · show Pm.tablePromise b.1.2 (strsOfAct Fr ((actQ N p l 12).2 b))
      rw [e]
      exact htab _ _ _ (cells_stay N p l 11 x a b τ hout).symm
        (ha.1 .tablePromise (by rw [proms11]; simp))
    · show Pm.shape 12 b.1.2 = true
      rw [e]
      exact hS _ (ha.1 (.shape 11) (by rw [proms11]; simp))
    · exact noColl_rides cs G smp₂ ms stOf bookOf N Pm p l 11 x .oOmega hB a b τ hout
        (fun _ _ => by rw [e]) (ha.1 (.noColl .oOmega) (by rw [proms11]; simp))
    · show Pm.nothingLeft b.1.2 = true
      rw [e]
      exact hnl _ hask
  · intro a τ b w i _ hout hi h
    obtain rfl := open11 i hi
    exact pin_rides cs G arr smp₂ ms decT₂ N Mg p l 11 x .oOmega hB a b τ hout
      (fun _ _ => by rw [(hyes a τ b hout).1]) w h

/-- hend at the wrap, for a block that is exact for ask. -/
theorem end_wrapped {U : Type} (ask : St → Clauses) (b₀ : Block St Cl)
    (he : Exact ask b₀) :
    ∀ (t : U × St) rs gs t',
      (Block.lift Prod.snd (fun x s => (x.1, s)) (below b₀)).decide t rs gs = .ok t' →
      t'.2 = t.2 ∧ ∀ c ∈ ask t.2, c.2 = true := fun t rs gs t' h =>
  (he t.2 rs gs t'.2).1 (wrap_decide b₀ t t' rs gs h).1

/-- hend at the shared chain's own last block. -/
theorem end_at_last {U : Type} (front : List (Block St Unit)) :
    ∀ (t : U × St) rs gs t',
      (Block.lift Prod.snd (fun x s => (x.1, s))
        (below (VerifiableInference.Desc.K12.Seat.last front))).decide t rs gs = .ok t' →
      t'.2 = t.2 ∧ ∀ c ∈ untestedL t.2.st, c.2 = true :=
  end_wrapped (fun d : St => untestedL d.st) _
    (chainEnd_exact 2 11 true _ _)

end Desc.K14.Law
