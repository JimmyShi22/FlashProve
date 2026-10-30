-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/AtHeadLetters.lean: CONDITIONAL: the debts of the member at an
attention segment's own rounds (kind K5) AT THE FIRST CHAIN's LETTERS AS THEY ARE LAID
(`lettersHead`, Honest/Thread/FirstHead.lean): which of the premises on letters fall there, and to
what the others come down.

`lettersHead` is `lettersAt` with five letters laid: so its `Thread` is `thrAt`
(Honest/K5/Law/Ready.lean) at these letters, by unfolding (`thrHead_eq`).

WHAT FALLS.
  `ansJT_keeps`, `ansReadsRest_JT`, `ansOn_JT`   a pin's sentence on the honest side (`ansJT`,
      Honest/Thread/Ans.lean) reads no oracle, and of the verifier's state the statement alone,
      which the kind's step leaves: so `AnsReadsRest` and `AnsOn` hold of it, at every list, tenant
      and number. The last two: no premise. THEY FALL BECAUSE THE LAID PIN READS NO ORACLE AND, OF
      THE STATE, THE STATEMENT ALONE: what a pin is worth there is said in that file's own
      Limits (nothing ties its text to the library's pin; that the witness's message has the answers
      is shown there of no run). The weight has moved, not gone.
WHAT COMES DOWN TO LESS.
  `keeps_head`     T.keeps at the border is the letter KpL at the kind's place: so the two premises
                   on T.keeps are one sentence on KpL there: it is `K5Keeps` (hKp)
  `rides_head`     T.rides: the reply's clause goes on, where the member that hears the reply is not
                   this one (hb₀); the letter RdL's part stays a premise (hRd)
  `idnOwed_head`   `IdnOwed`: T.valid pins the input to the run's own w: so it is one sentence at w,
                   on the letter Vd (hV)
WHAT STAYS AS IT WAS: the hypothesis h · hG, hKey, hK (the reader of the key points) · `LotLaid`,
now on the prover's own list of halves H.first, which is a letter · the test T.fits · `K5Script`.

  `k5_owes_all_head`   CONDITIONAL: **`Plays`, `Behind`, `Exchange`, `RidesPast` at that `Thread`
                       and the kind's border, and `Accepted` for every fall**

Limits. Every theorem but `ansReadsRest_JT`, `ansOn_JT` and `thrHead_eq` is conditional. The
hypothesis is not shown here. `K5Script` is shown by nobody; hV of no Vd. At a Vd that w does not
meet every premise can hold and `k5_owes_all_head` says nothing. One member of the chain.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.K5.Law.RidesT
import Johnson.Desc.ProofFile.Honest.K5.Law.Whole

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Block Place Strs Chain Wit)
open VerifiableInference.Desc.Sound (seatTab MsgT Mem smpNamed)
open VerifiableInference.Desc.First.Att.P (rest_st rest_out)
open H2K5.Honest (K5Keeps AtIdn tOf keeps_reads)
open ProofFile.Honest.FirstThread (Script WtF lettersHead head_keeps)
open P5J (AtMgA TS CellsM)

/-! ## 1 What a pin says on the honest side -/

/-- **What a pin says on the honest side of a state it says of every state that `K5Keeps` ties to
it**, at any strings and whatever was handed. No premise on the letters: by `ansJT_rows`: the
sentence reads of the state the statement's sample rows alone. CONDITIONAL: `K5Keeps`; the sentence
in front. -/
theorem ansJT_keeps {P Cells Tok : Type} (cs : OnBytes.Codes) (arr : Nat → Nat → Nat)
    (seats : List (Nat × Nat)) (ms : List Mem) (j t : Nat) {π π' : P} {s s' : TS} {y y' : Strs}
    {v : Wit Cells Tok MsgT} (hK : K5Keeps s s')
    (h0 : ansJT cs arr (smpNamed cs seats) ms j t (π, s) y v) :
    ansJT cs arr (smpNamed cs seats) ms j t (π', s') y' v := by
  have e : s.st = s'.st := keeps_reads rest_st hK
  exact ansJT_rows cs arr (fun _ _ _ => by rw [e]) h0

/-- **`AnsReadsRest` holds of the laid letter**, at every list of tenants. No premise. -/
theorem ansReadsRest_JT (Zp : ProofFile.Pub) (ms : List Mem) (L : List (Nat × Nat)) :
    AnsReadsRest (P := ProofFile.InstPub) (Wt := WtF)
      (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp) ms) L :=
  fun z _ _ _ _ _ _ hK h0 =>
    ansJT_keeps (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.seats Zp) ms z.1 z.2 hK h0

/-- **`AnsOn` holds of the laid letter**, at every tenant and number. No premise: the strings are
not read. -/
theorem ansOn_JT (Zp : ProofFile.Pub) (ms : List Mem) (z : Nat × Nat) (n : Nat) :
    AnsOn (P := ProofFile.InstPub) (Wt := WtF)
      (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp) ms) z n :=
  fun _ _ _ _ _ _ _ hK h0 =>
    ansJT_keeps (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.seats Zp) ms z.1 z.2 hK h0

/-! ## 2 The other letters -/

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

/-- The `Thread` of the laid letters is `thrAt` at them. No premise: by unfolding. -/
theorem thrHead_eq :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread =
      thrAt h H.first Q (fun v => H.storedWords v.w₀ v.rc)
      (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp) (P5J.At.ms Zp Z.lay))
      test carryX item n₁ n₂ (fun v => v = w ∧ Vd v)
      (fun b v s => (b₀ ≤ b → s.out.reply = some v.x.asked) ∧ RdL b v s)
      (fun b s s' => ∀ p, P5J.At.ps[b]? = some p → KpL p s s') := rfl

/-- **T.keeps at the kind's border is the letter KpL at the kind's place.** CONDITIONAL: g is below
12. -/
theorem keeps_head {g : Nat} (hg : g < 12) (s s' : TS) :
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread).keeps (borderOf g) s s' ↔
      KpL ⟨1, some (2 * g + 1), 3, .K5⟩ s s' :=
  head_keeps h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w (H2K5.Door.place_full hg) s s'

/-- **T.rides goes on past the member.** CONDITIONAL: hb₀: the member that hears the reply is not
this one; hRd: the letter RdL's part goes on. -/
theorem rides_head {g : Nat} (hb₀ : b₀ ≠ borderOf g + 1)
    (hRd : ∀ v s s', RdL (borderOf g) v s → K5Keeps s s' → RdL (borderOf g + 1) v s')
    (v : (Local W₀ Rc ProofFile.Inst Tr)) (s s' : TS)
    (h0 : ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread).rides (borderOf g) v
      s)
    (hK : K5Keeps s s') :
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread).rides (borderOf g + 1) v
      s' := by
  obtain ⟨h1, h2⟩ := h0
  refine ⟨fun hb => ?_, hRd v s s' h2 hK⟩
  have e : s.out = s'.out := keeps_reads rest_out hK
  rw [← e]
  exact h1 (Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hb hb₀))

omit h in
/-- **`IdnOwed` at the laid `valid` is one sentence at the run's own input.** CONDITIONAL: hV. -/
theorem idnOwed_head {cells : Tr → Cells} {Z5 : Seat5}
    (hV : Vd w → AtIdn Z5.P.D (tOf Reading.gl (inOf Z5.P.S Z5.link (cells w.trace)))) :
    IdnOwed (fun v => v = w ∧ Vd v) cells Z5 := by
  rintro v ⟨rfl, hv⟩
  exact hV hv

/-- **ALL OF THE MEMBER's DEBTS AT THE LETTERS AS THEY ARE LAID**: it plays; behind its yes; the
exchange; the riders; it is accepted, for every fall. CONDITIONAL: the premises stand in the file's
head. NO PREMISE ON THE LETTER ans IS LEFT, because the laid pin reads no oracle and of the state
the statement alone: see the head. It bears on values through Sc and hV alone; neither is
shown. -/
theorem k5_owes_all_head {n g : Nat} (hg : g < 12)
    {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array OnBytes.E)} {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    (hKey : ∀ a, (P5J.At.X Zp).A[g]? = some a → (seatOf keyOf Zp G cF g a).keysFit
      (blankDraws (Zp.D.1.take (roundsTo cF.blocksInOrder (borderOf g)))) = true)
    (hK : ∀ a, (P5J.At.X Zp).A[g]? = some a → KeySizes (seatOf keyOf Zp G cF g a))
    {cells : Tr → Cells} (hL : LotLaid H.first (seatAtK keyOf Zp G) cells G)
    (hfit : ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread).fits n = true)
    (hb : borderOf g < n)
    (hKp : ∀ s s', KpL ⟨1, some (2 * g + 1), 3, .K5⟩ s s' ↔ K5Keeps s s')
    (hb₀ : b₀ ≠ borderOf g + 1)
    (hRd : ∀ v s s', RdL (borderOf g) v s → K5Keeps s s' → RdL (borderOf g + 1) v s')
    (Sc : ∀ a blk, (P5J.At.X Zp).A[g]? = some a → cF.blocksInOrder[borderOf g]? = some blk →
      K5Script ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread)
        (borderOf g) cells (seatOf keyOf Zp G cF g a) a blk (h.𝔇.pubD.N.sent (2 * g + 1) 0)
        (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms))
    (hV : ∀ a, (P5J.At.X Zp).A[g]? = some a → Vd w →
      AtIdn (seatOf keyOf Zp G cF g a).P.D
        (tOf Reading.gl (inOf (seatOf keyOf Zp G cF g a).P.S (seatOf keyOf Zp G cF g a).link
          (cells w.trace)))) :
    (Plays ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread) (borderOf g) ∧
      Behind ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread) (borderOf g) ∧
      Exchange ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread) (borderOf g) ∧
      RidesPast ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread) (borderOf g)) ∧
      ∀ fall, Accepted ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread) fall
        (borderOf g) := by
  obtain ⟨blk, a, ha, Hs⟩ := k5_seated_keys h H.first Q (fun v => H.storedWords v.w₀ v.rc)
      (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp) (P5J.At.ms Zp Z.lay))
      test carryX item n₁ n₂ (fun v => v = w ∧ Vd v)
      (fun b v s => (b₀ ≤ b → s.out.reply = some v.x.asked) ∧ RdL b v s)
      (fun b s s' => ∀ p, P5J.At.ps[b]? = some p → KpL p s s')
    hg hG hKey hK hL
  exact k5_owes_all_T h
    (k5AtT_thrAt h H.first Q (fun v => H.storedWords v.w₀ v.rc)
      (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp) (P5J.At.ms Zp Z.lay))
      test carryX item n₁ n₂ (fun v => v = w ∧ Vd v)
      (fun b v s => (b₀ ≤ b → s.out.reply = some v.x.asked) ∧ RdL b v s)
      (fun b s s' => ∀ p, P5J.At.ps[b]? = some p → KpL p s s') hg)
    (k5RidersT_thrAt h H.first Q (fun v => H.storedWords v.w₀ v.rc)
      (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp) (P5J.At.ms Zp Z.lay))
      test carryX item n₁ n₂ (fun v => v = w ∧ Vd v)
      (fun b v s => (b₀ ≤ b → s.out.reply = some v.x.asked) ∧ RdL b v s)
      (fun b s s' => ∀ p, P5J.At.ps[b]? = some p → KpL p s s') hg
      fun s s' k => (hKp s s').1
        ((keeps_head h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w hg s s').1 k))
    hg ha Hs hfit hb
    (fun s s' k => (keeps_head h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w hg s s').2
      ((hKp s s').2 k))
    (rides_head h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w hb₀ hRd)
    (ansReadsRest_JT Zp _ _) (ansOn_JT Zp _ _ _) (Sc a blk ha Hs.member) rfl
    (idnOwed_head Vd w (hV a ha))

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.ansJT_keeps
#print axioms ProofFile.Honest.K5.ansReadsRest_JT
#print axioms ProofFile.Honest.K5.ansOn_JT
#print axioms ProofFile.Honest.K5.thrHead_eq
#print axioms ProofFile.Honest.K5.keeps_head
#print axioms ProofFile.Honest.K5.rides_head
#print axioms ProofFile.Honest.K5.idnOwed_head
#print axioms ProofFile.Honest.K5.k5_owes_all_head
