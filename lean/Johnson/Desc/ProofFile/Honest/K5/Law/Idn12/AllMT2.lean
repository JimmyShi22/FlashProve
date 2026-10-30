-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/Idn12/AllMT2.lean: CONDITIONAL: all the debts of the member at
an attention segment's own rounds (kind K5) in one statement, WITHOUT THE PREMISE `IdnOwed` (the
input's cells meet the library's three families of identities) AND OVER THE CLAUSE OF T.keeps WITH
"NO MARK BEHIND" INSIDE (`K5KeepsM`, Johnson/Desc/K5/Honest/Law/KeepsM.lean): with the `Thread` T a
variable, and at the first chain's letters as they are laid (`lettersHead`,
Honest/Thread/FirstHead.lean).

  `k5_owes_all_M_T₂`       CONDITIONAL, T A VARIABLE: `k5_owes_all_M_T` (Honest/K5/Law/KeepsMT.lean)
                           with hH: `HoldsOwed` T.valid cq (Honest/K5/Law/Idn12/AskedT.lean) in hV's
                           stead
  `holdsOwed_head`         `HoldsOwed` at the laid `valid` is one sentence at the run's own input
  `k5_owes_all_head_M₂`    CONDITIONAL: `k5_owes_all_head_M` (Honest/K5/Law/HeadM.lean) likewise
  `k5_owes_all_reply_M₂`   the same with b₀ at the border behind the member that hears the reply,
                           without the premise on b₀

Limits. Every theorem is conditional. TWO PREMISES BEAR ON VALUES: Sc (`K5Script`): NOT SHOWN;
hH: SHOWN OF NO `valid` AND NO Vd. THE WEIGHT OF `IdnOwed` HAS MOVED, NOT GONE: that the
identities hold now comes from three items that `Thr` T holds in front of the member, of T's own
witness: whoever shows that a run meets `Thr` T there owes them. At `lettersHead` no premise on the
letter ans is left, because the laid pin reads no oracle and of the state the statement alone: what
a pin is worth there is said in Honest/Thread/Ans.lean's own Limits. Kp and b₀ are still letters of
`lettersHead`. The hypothesis `P5J.AtMgA` is not shown here. Where no input is valid every premise
can hold and the statements say nothing; so too if, at the list of members that `lettersHead` lays,
no member sat at the tenant of a pin that is open at the border: that one does is not shown here.
One member of the chain. At the library's full size and the format's second hash function alone. The older
laws stand beside these.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Idn12.AllT2
import Johnson.Desc.ProofFile.Honest.K5.Law.HeadM

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Block Place Strs Chain)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (seatTab)
open H2K5.Honest (K5KeepsM)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open P5J (AtMgA TS CellsM)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  {T : Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst}
  {g : Nat} {it : Item → T.ι} {pb : T.P → ProofFile.InstPub} {wt : T.Wt → WtF}
  {ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop} {test : Nat → TS → Option String}
  {carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop}
  {cq : (Local W₀ Rc ProofFile.Inst Tr) → CellsM OnBytes.Flat.numsFull}
  (A : K5AtT h T g it pb wt ans test carryX cq)
include A

/-- **ALL OF THE MEMBER's DEBTS IN ONE STATEMENT, WITHOUT `IdnOwed`**, T.keeps tied to `K5KeepsM`. T
IS A VARIABLE. CONDITIONAL: as `k5_owes_all_M_T` (Honest/K5/Law/KeepsMT.lean), with hH in hV's
stead. It bears on values through Sc and hH, and through what `Thr` T holds of the asked items in
front; none of these is shown. -/
theorem k5_owes_all_M_T₂ {a : Attention.Plan}
    (R : K5RidersM h T g it pb wt ans test carryX cq a.own) {n : Nat} (hg : g < 12)
    (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl} (Hs : K5Seated T (borderOf g) cells Z5 (parAt Zp g a) blk)
    (hfit : T.fits n = true) (hb : borderOf g < n)
    (KpM : ∀ s s', K5KeepsM a.own s s' → T.keeps (borderOf g) s s')
    (RdM : ∀ w s s', T.rides (borderOf g) w s → K5KeepsM a.own s s' →
      T.rides (borderOf g + 1) w s')
    (hans : AnsReadsRest ans ((P5J.At.N Zp cF).sent (2 * g + 1) 0))
    (hidx : AnsOn ans (P5J.At.N Zp cF).index (treesTo cF.blocksInOrder (borderOf g)))
    (Sc : K5Script T (borderOf g) cells Z5 a blk (h.𝔇.pubD.N.sent (2 * g + 1) 0)
      fun v => seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms (wt v))
    (hP : Z5.P = ⟨a.S, a.own⟩) (hH : HoldsOwed T.valid cq) :
    (Plays T (borderOf g) ∧ Behind T (borderOf g) ∧ Exchange T (borderOf g) ∧
      RidesPast T (borderOf g)) ∧ ∀ fall, Accepted T fall (borderOf g) :=
  ⟨⟨k5_plays T Hs, k5_behind_M_T h A hg ha Hs KpM RdM,
      k5_exchange_shares_T₂ h A hg ha Hs hfit hb hans Sc hP hH, k5_ridesPast_M_T h A R hg hidx⟩,
    fun fall => k5_accepted_T h A hg ha Hs fall⟩

end

/-- **`HoldsOwed` at the laid `valid` is one sentence at the run's own input.** CONDITIONAL: hH. -/
theorem holdsOwed_head {W : Type} (Vd : W → Prop) (w : W) {cq : W → CellsM OnBytes.Flat.numsFull}
    (hH : Vd w → ∃ i, VerifiableInference.OnPublicFiles.Flat.Holds (cq w) i) :
    HoldsOwed (fun v => v = w ∧ Vd v) cq := by
  rintro v ⟨rfl, hv⟩
  exact hH hv

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

/-- **ALL OF THE MEMBER's DEBTS AT THE LETTERS AS THEY ARE LAID, OVER THE CLAUSE WITH THE MARK
INSIDE, WITHOUT `IdnOwed`.** CONDITIONAL: the premises of `k5_owes_all_head_M`, with hH in hV's
stead: where the run's own input meets Vd, the cells that the Script lays for it hold an index. -/
theorem k5_owes_all_head_M₂ {n g : Nat} (hg : g < 12)
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
    (hH : Vd w → ∃ i, VerifiableInference.OnPublicFiles.Flat.Holds (Q.cells w) i) :
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
  exact k5_owes_all_M_T₂ h
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
    (holdsOwed_head Vd w hH)

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
premises of `k5_owes_all_head_M₂` but the one on b₀. That b₀ is laid so is said by nobody. -/
theorem k5_owes_all_reply_M₂ {n g : Nat} (hg : g < 12)
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
    (hH : Vd w → ∃ i, VerifiableInference.OnPublicFiles.Flat.Holds (Q.cells w) i) :
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
  k5_owes_all_head_M₂ h H Q test carryX item n₁ n₂ replyBorder Vd RdL KpL w hg hG hKey hK hL hfit
    hb hKpM (Nat.ne_of_gt (reply_behind hg)) hRdM Sc hH

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k5_owes_all_M_T₂
#print axioms ProofFile.Honest.K5.holdsOwed_head
#print axioms ProofFile.Honest.K5.k5_owes_all_head_M₂
#print axioms ProofFile.Honest.K5.k5_owes_all_reply_M₂
