-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/HeadM.lean: CONDITIONAL: all the debts of the member at an
attention segment's own rounds (kind K5) AT THE FIRST CHAIN's LETTERS AS THEY ARE LAID
(`lettersHead`, Honest/Thread/FirstHead.lean), WHERE THE LETTER Kp AT THE KIND's PLACE IS THE CLAUSE
WITH "NO MARK BEHIND" INSIDE (`K5KeepsM`, Johnson/Desc/K5/Honest/Law/KeepsM.lean).

It is `k5_owes_all_head` (Honest/K5/Law/AtHeadLetters.lean) over the newer clause: there the premise
on Kp ties it to `K5Keeps`; here to `K5KeepsM` at the group's plan's numbers. Whoever lays Kp at the
kind's places as `K5KeepsAt` at the public input pays the premise by `k5KeepsAt_iff`.

  `rides_head_M`         T.rides goes on past the member, along the clause
  `k5_owes_all_head_M`   CONDITIONAL: **`Plays`, `Behind`, `Exchange`, `RidesPast` and, for every
                         fall, `Accepted`**, at that `Thread` and the kind's border
  `k5_owes_all_reply_M`  the same with the number b₀ at the border behind the member that hears the
                         reply (`replyBorder`, Honest/K5/Law/ReplyAt.lean), without the premise on
                         b₀

Limits. Every theorem is conditional. The hypothesis `P5J.AtMgA` is not shown here. `K5Script` is
shown by nobody; hV of no Vd. Kp and b₀ are still letters of `lettersHead`: nothing here says how
they are or will be laid. No premise on the letter ans is left, because the laid pin reads no oracle
and of the state the statement alone: what a pin is worth there is said in Honest/Thread/Ans.lean's
own Limits. At a Vd that w does not meet every premise can hold and the statements say nothing; so
too if, at the list of members that `lettersHead` lays, no member sat at the tenant of a pin that is
open at the border: that one does is not shown here. One member of the chain. At the library's full
size and the format's second hash function alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.KeepsMT
import Johnson.Desc.ProofFile.Honest.K5.Law.ReplyAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Block Place Strs Chain)
open VerifiableInference.Desc.Sound (seatTab)
open H2K5.Honest (K5KeepsM AtIdn tOf k5KeepsM_out)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open P5J (AtMgA TS CellsM)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
    VerifiableInference.Desc.Sound.MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : (Local W₀ Rc ProofFile.Inst Tr) → Prop)
  (RdL : Nat → (Local W₀ Rc ProofFile.Inst Tr) → TS → Prop) (KpL : Place → TS → TS → Prop)
  (w : (Local W₀ Rc ProofFile.Inst Tr))

/-- **T.rides goes on past the member, along the clause.** CONDITIONAL: hb₀: the member that hears
the reply is not this one; hRd: the letter RdL's part goes on. -/
theorem rides_head_M {g : Nat} {o : Params.AttentionRounds} (hb₀ : b₀ ≠ borderOf g + 1)
    (hRd : ∀ v s s', RdL (borderOf g) v s → K5KeepsM o s s' → RdL (borderOf g + 1) v s')
    (v : (Local W₀ Rc ProofFile.Inst Tr)) (s s' : TS)
    (h0 : ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread).rides (borderOf g) v
      s)
    (hK : K5KeepsM o s s') :
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread).rides (borderOf g + 1) v
      s' := by
  obtain ⟨h1, h2⟩ := h0
  refine ⟨fun hb => ?_, hRd v s s' h2 hK⟩
  rw [k5KeepsM_out hK]
  exact h1 (Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hb hb₀))

/-- **ALL OF THE MEMBER's DEBTS AT THE LETTERS AS THEY ARE LAID, OVER THE CLAUSE WITH THE MARK
INSIDE.** CONDITIONAL: the premises of `k5_owes_all_head`, with hKpM and hRdM over `K5KeepsM`. It
bears on values through Sc and hV; neither is shown. -/
theorem k5_owes_all_head_M {n g : Nat} (hg : g < 12)
    {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array OnBytes.E)} {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    (hKey : ∀ a, (P5J.At.X Zp).A[g]? = some a → (seatOf keyOf Zp G cF g a).keysFit
      (blankDraws (Zp.D.1.take (roundsTo cF.blocksInOrder (borderOf g)))) = true)
    (hK : ∀ a, (P5J.At.X Zp).A[g]? = some a → KeySizes (seatOf keyOf Zp G cF g a))
    {cells : Tr → Cells} (hL : LotLaid H.first (seatAtK keyOf Zp G) cells G)
    (hfit : ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread).fits n =
      true)
    (hb : borderOf g < n)
    (hKpM : ∀ a, (P5J.At.X Zp).A[g]? = some a → ∀ s s',
      KpL ⟨1, some (2 * g + 1), 3, .K5⟩ s s' ↔ K5KeepsM a.own s s')
    (hb₀ : b₀ ≠ borderOf g + 1)
    (hRdM : ∀ a, (P5J.At.X Zp).A[g]? = some a → ∀ v s s', RdL (borderOf g) v s →
      K5KeepsM a.own s s' → RdL (borderOf g + 1) v s')
    (Sc : ∀ a blk, (P5J.At.X Zp).A[g]? = some a → cF.blocksInOrder[borderOf g]? = some blk →
      K5Script ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread)
        (borderOf g) cells (seatOf keyOf Zp G cF g a) a blk (h.𝔇.pubD.N.sent (2 * g + 1) 0)
        (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms))
    (hV : ∀ a, (P5J.At.X Zp).A[g]? = some a → Vd w →
      AtIdn (seatOf keyOf Zp G cF g a).P.D
        (tOf Reading.gl (inOf (seatOf keyOf Zp G cF g a).P.S (seatOf keyOf Zp G cF g a).link
          (cells w.trace)))) :
    (Plays ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread)
        (borderOf g) ∧
      Behind ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread)
        (borderOf g) ∧
      Exchange ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread)
        (borderOf g) ∧
      RidesPast ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread)
        (borderOf g)) ∧
      ∀ fall, Accepted ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread)
        fall (borderOf g) := by
  obtain ⟨blk, a, ha, Hs⟩ := k5_seated_keys h H.first Q (fun v => H.storedWords v.w₀ v.rc)
      (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp) (P5J.At.ms Zp Z.lay))
      test carryX item n₁ n₂ (fun v => v = w ∧ Vd v)
      (fun b v s => (b₀ ≤ b → s.out.reply = some v.x.asked) ∧ RdL b v s)
      (fun b s s' => ∀ p, P5J.At.ps[b]? = some p → KpL p s s')
    hg hG hKey hK hL
  exact k5_owes_all_M_T h
    (k5AtT_thrAt h H.first Q (fun v => H.storedWords v.w₀ v.rc)
      (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp) (P5J.At.ms Zp Z.lay))
      test carryX item n₁ n₂ (fun v => v = w ∧ Vd v)
      (fun b v s => (b₀ ≤ b → s.out.reply = some v.x.asked) ∧ RdL b v s)
      (fun b s s' => ∀ p, P5J.At.ps[b]? = some p → KpL p s s') hg)
    (k5RidersM_thrAt h H.first Q (fun v => H.storedWords v.w₀ v.rc)
      (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp) (P5J.At.ms Zp Z.lay))
      test carryX item n₁ n₂ (fun v => v = w ∧ Vd v)
      (fun b v s => (b₀ ≤ b → s.out.reply = some v.x.asked) ∧ RdL b v s)
      (fun b s s' => ∀ p, P5J.At.ps[b]? = some p → KpL p s s') hg
      fun s s' k => (hKpM a ha s s').1
        ((keeps_head h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w hg s s').1 k))
    hg ha Hs hfit hb
    (fun s s' k => (keeps_head h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w hg s s').2
      ((hKpM a ha s s').2 k))
    (rides_head_M h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w hb₀ (hRdM a ha))
    (ansReadsRest_JT Zp _ _) (ansOn_JT Zp _ _ _) (Sc a blk ha Hs.member) rfl
    (idnOwed_head Vd w (hV a ha))

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
    VerifiableInference.Desc.Sound.MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ : Nat) (Vd : (Local W₀ Rc ProofFile.Inst Tr) → Prop)
  (RdL : Nat → (Local W₀ Rc ProofFile.Inst Tr) → TS → Prop) (KpL : Place → TS → TS → Prop)
  (w : (Local W₀ Rc ProofFile.Inst Tr))

/-- **THE SAME WITH b₀ AT THE BORDER BEHIND THE MEMBER THAT HEARS THE REPLY.** CONDITIONAL: the
premises of `k5_owes_all_head_M` but the one on b₀. That b₀ is laid so is said by nobody. -/
theorem k5_owes_all_reply_M {n g : Nat} (hg : g < 12)
    {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array OnBytes.E)} {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    (hKey : ∀ a, (P5J.At.X Zp).A[g]? = some a → (seatOf keyOf Zp G cF g a).keysFit
      (blankDraws (Zp.D.1.take (roundsTo cF.blocksInOrder (borderOf g)))) = true)
    (hK : ∀ a, (P5J.At.X Zp).A[g]? = some a → KeySizes (seatOf keyOf Zp G cF g a))
    {cells : Tr → Cells} (hL : LotLaid H.first (seatAtK keyOf Zp G) cells G)
    (hfit : ((lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL KpL w).thread).fits n =
      true)
    (hb : borderOf g < n)
    (hKpM : ∀ a, (P5J.At.X Zp).A[g]? = some a → ∀ s s',
      KpL ⟨1, some (2 * g + 1), 3, .K5⟩ s s' ↔ K5KeepsM a.own s s')
    (hRdM : ∀ a, (P5J.At.X Zp).A[g]? = some a → ∀ v s s', RdL (borderOf g) v s →
      K5KeepsM a.own s s' → RdL (borderOf g + 1) v s')
    (Sc : ∀ a blk, (P5J.At.X Zp).A[g]? = some a → cF.blocksInOrder[borderOf g]? = some blk →
      K5Script ((lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL KpL w).thread)
        (borderOf g) cells (seatOf keyOf Zp G cF g a) a blk (h.𝔇.pubD.N.sent (2 * g + 1) 0)
        (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms))
    (hV : ∀ a, (P5J.At.X Zp).A[g]? = some a → Vd w →
      AtIdn (seatOf keyOf Zp G cF g a).P.D
        (tOf Reading.gl (inOf (seatOf keyOf Zp G cF g a).P.S (seatOf keyOf Zp G cF g a).link
          (cells w.trace)))) :
    (Plays ((lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL KpL w).thread)
        (borderOf g) ∧
      Behind ((lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL KpL w).thread)
        (borderOf g) ∧
      Exchange ((lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL KpL w).thread)
        (borderOf g) ∧
      RidesPast ((lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL KpL w).thread)
        (borderOf g)) ∧
      ∀ fall, Accepted ((lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL KpL w).thread)
        fall (borderOf g) :=
  k5_owes_all_head_M h H Q test carryX item n₁ n₂ replyBorder Vd RdL KpL w hg hG hKey hK hL hfit
    hb hKpM (Nat.ne_of_gt (reply_behind hg)) hRdM Sc hV

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.rides_head_M
#print axioms ProofFile.Honest.K5.k5_owes_all_head_M
#print axioms ProofFile.Honest.K5.k5_owes_all_reply_M
