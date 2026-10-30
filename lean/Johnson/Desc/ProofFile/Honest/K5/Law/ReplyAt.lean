-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/ReplyAt.lean: the member of the first chain that hears the
reply stands behind all twelve members of the kind "an attention segment's own rounds" (K5), at the
library's written list of places; and so, at the first chain's letters as they are laid
(`lettersHead`, Honest/Thread/FirstHead.lean) with the number b₀ laid as that file's head says ("the
border behind the member that hears the reply"), the premise b₀ ≠ `borderOf g` + 1 of
`k5_owes_all_head` (Honest/K5/Law/AtHeadLetters.lean) falls.

Which member hears the reply is the library's own text: `hearsReply`
(Johnson/Desc/First/Driver/Chain.lean): the place of the kind K7.

  `replyBorder`   the border behind the first place of the written list that hears the reply
  `replyB`, `reply_closed`, `reply_bite`   a test with code on the written list: one place hears the
                  reply, and each of the kind's twelve borders, and the border behind it, lies in
                  front of `replyBorder`; a closed fact, by the kernel; a control: at the number
                  that a thirteenth group would have the comparison says no
  `reply_behind`  CONDITIONAL (g is below 12): `borderOf g` + 1 is below `replyBorder`
  `k5_owes_all_reply`   CONDITIONAL: `k5_owes_all_head` at b₀ := `replyBorder`, without that premise

Limits. b₀ IS STILL A LETTER OF `lettersHead`: nothing here says that it is or will be laid at
`replyBorder`. At the full size and the written list alone. At the kind K5's borders the reply's
clause of T.rides is then idle: it speaks from `replyBorder` on. The other premises of
`k5_owes_all_head` stay.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.AtHeadLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Block Place Strs Chain)
open VerifiableInference.Desc.First (hearsReply)
open VerifiableInference.Desc.Sound (seatTab)
open H2K5.Honest (K5Keeps AtIdn tOf)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open P5J (AtMgA TS CellsM)

/-- The border behind the first place of the library's written list that hears the reply. -/
def replyBorder : Nat := P5J.At.ps.findIdx hearsReply + 1

/-- A test with code on the written list. n: how many groups are looked at. -/
def replyB (n : Nat) : Bool :=
  (P5J.At.ps.filter hearsReply).length == 1 &&
    (List.range n).all fun g => decide (borderOf g + 1 < replyBorder)

set_option maxRecDepth 1000000 in
/-- **The test says yes at the twelve groups.** No premise: a closed fact, by the kernel. -/
theorem reply_closed : replyB 12 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with a thirteenth group's number the test says no. No premise: a closed fact, by the
kernel. -/
theorem reply_bite : replyB 13 = false := by decide +kernel

/-- **The member that hears the reply stands behind the kind's member.** CONDITIONAL: g is below
12. -/
theorem reply_behind {g : Nat} (hg : g < 12) : borderOf g + 1 < replyBorder := by
  have h1 := reply_closed
  unfold replyB at h1
  rw [Bool.and_eq_true] at h1
  exact of_decide_eq_true (List.all_eq_true.1 h1.2 g (List.mem_range.2 hg))

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

/-- **ALL OF THE MEMBER's DEBTS AT THE LETTERS AS THEY ARE LAID, WITH b₀ AT THE BORDER BEHIND THE
MEMBER THAT HEARS THE REPLY.** CONDITIONAL: the premises of `k5_owes_all_head` but the one on b₀.
That b₀ is laid so is said by nobody: it is a letter. -/
theorem k5_owes_all_reply {n g : Nat} (hg : g < 12)
    {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array OnBytes.E)} {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    (hKey : ∀ a, (P5J.At.X Zp).A[g]? = some a → (seatOf keyOf Zp G cF g a).keysFit
      (blankDraws (Zp.D.1.take (roundsTo cF.blocksInOrder (borderOf g)))) = true)
    (hK : ∀ a, (P5J.At.X Zp).A[g]? = some a → KeySizes (seatOf keyOf Zp G cF g a))
    {cells : Tr → Cells} (hL : LotLaid H.first (seatAtK keyOf Zp G) cells G)
    (hfit : ((lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL KpL w).thread).fits n =
      true)
    (hb : borderOf g < n)
    (hKp : ∀ s s', KpL ⟨1, some (2 * g + 1), 3, .K5⟩ s s' ↔ K5Keeps s s')
    (hRd : ∀ v s s', RdL (borderOf g) v s → K5Keeps s s' → RdL (borderOf g + 1) v s')
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
  k5_owes_all_head h H Q test carryX item n₁ n₂ replyBorder Vd RdL KpL w hg hG hKey hK hL hfit hb
    hKp (Nat.ne_of_gt (reply_behind hg)) hRd Sc hV

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.reply_closed
#print axioms ProofFile.Honest.K5.reply_bite
#print axioms ProofFile.Honest.K5.reply_behind
#print axioms ProofFile.Honest.K5.k5_owes_all_reply
