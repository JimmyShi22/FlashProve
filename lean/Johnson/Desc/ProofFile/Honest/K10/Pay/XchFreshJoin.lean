-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/XchFreshJoin.lean: the closing of a segment (K10): the pairing of the field fresh of
`CarryOwed` (Honest/K10/Xch/CarryTop.lean), from what is said of the fresh mask's sender, clause by clause. A join of this
folder's files on that field.

  **`fresh_of_sender`**   the pairing, under `CloseBase` and where the book gives the closing's part its coins, from:
      hq      the fresh mask's message has a seat in the state's book
      hv      the witness's table there is `K1.rowsMsg` of rows Vn (the senders' laws on a script end so: `tab_rows`,
              Honest/K1/ScriptTie.lean; `tab_rows_switch`, Honest/K2/Law/TabRows.lean)
      hm      inside the mask table Vn's mask rows are the laying of a fold's fresh table at coins c₀ (`sent_fresh_mask`,
              Pay/XchFreshSent.lean; `ride_coin`, Honest/K1/RideLaw.lean)
      hc₀     c₀ t, below 2 k + 1, is the coin number off + t of the part at the address sender
      hbook   on the book: an entry by which the closing's part spends has that sender as its owner and starts at off

Limits. The five clauses are premises, shown here of no script, sender or book. No head and no thread is named.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchFreshCoins
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchSpent
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchTieRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes.Slice (GE readE)
open Cb (HIdx sVars)
open Johnson.Prover.Link (Pairs)
open Johnson.Prover.Send (Rows)
open VerifiableInference.Desc
open VerifiableInference.Desc.First.Close (Par)
open VerifiableInference.Desc.Sound (MsgT wordsFirst seatBy noFirst)
open ProofFile.Honest.K10.LeftIs (stageB freshB)
open ProofFile.Honest.K10.YesFree (BaseData CloseBase)

variable {V W X : Type}

/-- **The field fresh's pairing, from what is said of the fresh mask's sender.** -/
theorem fresh_of_sender {P : Par} {D : BaseData} {s : First.S} (Hb : CloseBase P (K9.recOf s) D) {Cells Tok : Type}
    (arr : Nat → Nat → Nat) (v : Wit Cells Tok MsgT)
    {Bk : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d} {pl : Place} {J : CloseJob W}
    (hJ : J.pub.par.k = P.k) {cc : (closePart (V := V) (X := X) (foldShellT true J foldWords)).Coins}
    (hcc : closeCoins (V := V) (X := X) Bk rows look pl J = .ok cc)
    {q : Nat × Nat} (hq : seatBy noFirst s.book D.m = some q) {Vn : Rows}
    (hv : ∀ y, s.st.oracles[D.m]? = some y →
      v.tab s.st.codes y.shape (arr q.1 q.2) q.1 q.2 = K1.rowsMsg y.shape Vn)
    {c₀ : Nat → GE}
    (hm : ∀ b j, b < 2 ^ (stageB D (K9.recOf s)).h → j < (stageB D (K9.recOf s)).Z.l → Vn.mask b j =
      (⟨(stageB D (K9.recOf s)).h + (stageB D (K9.recOf s)).g, (stageB D (K9.recOf s)).h⟩ : K1.Ride).lay c₀ b j)
    {sender : Addr} {off : Nat}
    (hc₀ : ∀ t, t < 2 * J.pub.par.k + 1 → c₀ t = (K12.stretchOf (look sender).2).e (off + t))
    (hbook : ∀ e ∈ Bk.ahead, (e.spender == ⟨pl, 0⟩) = true → e.once = true → e.owner = sender ∧ e.start.e = off)
    (W' : HIdx (sVars GE 2 ((stageB D (K9.recOf s)).h + (stageB D (K9.recOf s)).g)) → GE)
    (hW : CoefOf (spentRun J (handSnd cc)) W') :
    Pairs (stageB D (K9.recOf s)) (stageB D (K9.recOf s)).Z.l W'
      (freshB D (K9.recOf s) (wordsFirst arr s.st s.book v)) := by
  obtain ⟨y, hy₀, -⟩ := mask_shape_of_base Hb
  have hy : s.st.oracles[D.m]? = some y := hy₀
  obtain ⟨e, he, -, -, hval⟩ := spent_value hcc
  have hmem : e ∈ (Bk.ahead.filter fun e => e.spender == ⟨pl, 0⟩).filter (·.once) := by
    rw [he]
    exact List.mem_singleton.2 rfl
  obtain ⟨h1, h2⟩ := List.mem_filter.1 hmem
  obtain ⟨h3, h4⟩ := List.mem_filter.1 h1
  obtain ⟨ho, hs⟩ := hbook e h3 h4 h2
  refine fresh_of_coins Hb arr v hJ (spentRun J (handSnd cc)) c₀ (fun i hi => ?_) (fun b j hb hj => ?_) W' hW
  · rw [hval i hi, ho, hs]
    exact hc₀ i hi
  · rw [tabAt_seat _ _ _ _ _ hq hy, hv y hy]
    exact hm b j hb hj

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.fresh_of_sender
