-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/ZzStateAtHead.lean: the honest side of the smallness test (K8): THE
PREMISE hSt OF `zz_at_join_head` (Johnson/Desc/ProofFile/Honest/K8/ZzAtJoin.lean), AT THE FIRST
CHAIN's LETTERS AT THE LIBRARY's HEAD, AT EVERY SCRIPT, EXCHANGED FOR PUBLIC PREMISES. One theorem;
no definition.

  **`hSt_at_head`**   under the head and an opening of the description · what is said gives `SaidOk`
                  · l below 25 · the built segment · the kind's member seated at the description's
                  own parameters · the job's plan is the shared sending's second later plan of the
                  segment · FIVE PUBLIC PREMISES: haA (the array that the built segment's list names
                  at the digits' index is a) · hn, hans (the plan's message number n is there and is
                  sampled) · hseat (the seat that the plan of seats gives a's message is the seat of
                  the sender's message number n) · hmz (the built record's count of columns is at
                  most the sum of its matrices' rows) ⊢ behind every step of the member from the
                  pair of the stand and what is said: the ten clauses of hSt
How. The pair with `SaidOk` gives the library's "reached" (`thrS_rchAt`,
Johnson/Desc/ProofFile/Honest/Thread/ReachAtHead.lean); the step gives the draw's yes, as in
Johnson/Desc/ProofFile/Honest/K8/DigitsFieldAtHead.lean. Then: the open part, the array ahead, its
seat, shape and the layout's test: `zzAhead_at_reach` (Johnson/Desc/K8/Honest/ZzAheadAtReach.lean) ·
the record's fields behind the yes: `six_behind_draw` (Johnson/P1K8R/DigitsAtDraw.lean) · the
table's member at the seat and its shape: `sits_fifty`
(Johnson/Desc/ProofFile/Honest/K1/Law/SeatsAtFifty.lean) · the sender's number: `behind_closed`
(Johnson/Desc/ProofFile/Honest/K8/ZzJobInList.lean).
One option is raised (maxHeartbeats) and one instance is taken away, as in the files beneath.
Tactics that search: `omega` on one line, on l.
Limits. An implication. The five public premises are shown nowhere here. `K8Seated` is a premise.
That the thread stands at any of these numbers, at any prover, is not said: where it stands at none,
all is idle. The verifier's state, the plan and the layout alone: no coin, no input and no witness
is read; the run's coins and the input stand under "for all", in the pair and the step. The full
size alone.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.DigitsFieldAtHead
import Johnson.Desc.ProofFile.Honest.K8.ZzJobInList
import Johnson.Desc.ProofFile.Honest.K8.Digits
import Johnson.Desc.K8.Honest.ZzAheadAtReach
import Johnson.Desc.ProofFile.Honest.K1.Law.SeatsAtFifty

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open OnBytes.Params (ReqArray)
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc
open VerifiableInference.Desc.Sound (MsgT Mem numOf)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8 (step_seats_iff decide_atS_iff approximateRangeProofDrawKind atS drawAt)
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.K9 (rowBitsOf placeBitsOf)
open Johnson.Prover.Send (shapeAt)
open _root_.Desc.K14.Law (seatZ secondAt)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead WtF Script thrS_rchAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **The premise hSt at the head's letters, exchanged, not paid.** What stays unpaid: the head, the
opening O₁, the built segment e3, hOk (what is said gives `SaidOk`), `K8Seated`, hP (the job's
plan), l below 25, and the five public premises haA, hn, hans, hseat, hmz. On the verifier's state,
the plan and the layout alone. -/
theorem hSt_at_head {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (hOk : ∀ b k m, Said b k m → SaidOk b k m) {l : ℕ} (hl : l < 25) {Bs : ProofFile.PureBase}
    {base₀ : List (Block S ProofFile.Cl)}
    (O₁ : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {blk : Block S ProofFile.Cl} {cells : Tr → Cells}
    {mats : List (Nat × String × Nat)}
    (hK : K8Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (14 * l + (if l = 24 then 5 else 4) + 2) blk cells (ProofFile.k8Par Zp Bs.G₀ Xl l, mats))
    {J : K1.SendJob (K1.PlaceIn ProofFile.Inst) X} (hP : J.P = K1.parL Zp Bs.G₀ l true)
    {a : ReqArray} {n : ℕ}
    (haA : ∀ bn, Xl.arrayOf[Xl.tl.ix.ZZ]? = some bn →
      reqArray Bs.G₀.first.layout l bn.2 = some a)
    (hn : n < J.P.sent.size) (hans : (shapeAt J.P n).answers ≠ 0)
    (hseat : P5J.At.seat3At Zp l true a.message =
      K1.seatAtMember cF.blocksInOrder (14 * l + (if l = 24 then 5 else 4) + 2 + 1) J.P n)
    (hmz : Xl.tl.mz ≤ allRows (parOfTail Xl.tl)) :
    ∀ k s m E ds pl cols s' tl',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
        (14 * l + (if l = 24 then 5 else 4) + 2) k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds pl
        cols s' →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form
        (14 * l + (if l = 24 then 5 else 4) + 2 + 1) k s' pl.2 →
      s'.tl? = some tl' →
      ∃ (q : K9.Part) (x : ℕ × String) (g : K9.Ahead) (y : Mem), K9.segAt? s' = some q ∧
        q.L.arrayOf[tl'.ix.ZZ]? = some x ∧
        K9.aheadIn (h.𝔇.N.sent l) (h.𝔇.N.group l) q (x.1, x.2) = some g ∧ g.A = a ∧
        laidMatrixOk g.A (rowBitsOf g.shape .main) (placeBitsOf q.d.st.codes g.shape .main) =
          true ∧
        h.𝔇.ms.find? (fun y => decide (Sound.seatOf y = g.seat)) = some y ∧ numOf h.𝔇.arr y =
          h.𝔇.arr
            (K1.seatAtMember cF.blocksInOrder (14 * l + (if l = 24 then 5 else 4) + 2 + 1) J.P n).1
            (K1.seatAtMember cF.blocksInOrder (14 * l + (if l = 24 then 5 else 4) + 2 + 1) J.P n).2 ∧
        (y.1.l.get y.2).1 = shapeAt J.P n ∧ parOfTail Xl.tl = parOfTail tl' ∧
        2 * tl'.mz ≤ 2 * allRows (parOfTail Xl.tl) := by
  intro k s m E ds pl cols s' tl' hA _ hS _ ht
  have hl' : l ≤ 24 := by omega
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some Bs.G₀ := O₁.blank
  have hr0 := thrS_rchAt h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w ()
    (Nat.le_of_lt (List.getElem?_eq_some_iff.1 hK.here).1) ⟨hA.1, hOk _ _ _ hA.2⟩
  have hr : Johnson.Desc.First.Walk.Tied.RchAt
      (P1K8T.FD Zp (Desc.K14.Law.seatZ Zp Np) (Desc.K14.Law.secondAt Zp Np) cF) (drawAt l)
      ((m.st.input.x.pub, s), ()) := by
    rw [P1K8T.drawAt_place l]
    exact hr0
  have hu : s.failed = none := Option.isNone_iff_eq_none.1 hA.1.2.2.1.1
  obtain ⟨-, hstep⟩ := hS
  obtain ⟨rv, -, -, hm, -, -⟩ :=
    (step_seats_iff (ProofFile.k8Par Zp Bs.G₀ Xl l) blk hK.seats _ s s' _ _ _).1 hstep
  have hy : ∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS (ProofFile.k8ParW Zp Bs.G₀ Xl l).toPar).decide s rs gs =
      .ok s' := ⟨[rv], [], (decide_atS_iff _ s s' rv []).2 hm⟩
  obtain ⟨p, bn, A, sh, M, hp, pArr, pCs, f1, -, f3, -, -, f6, hmat⟩ :=
    zzAhead_at_reach h hG hl' e3 m.st.input.x.pub s s' hr hu hy
  obtain ⟨ts, hts, -, c2, c3, c4, c5, -⟩ :=
    P1K8T.six_behind_draw h hG hl' e3 ((m.st.input.x.pub, s), ()) hr hy
  obtain rfl : ts = tl' := Option.some.inj (hts.symm.trans ht)
  obtain rfl : A = a := Option.some.inj (f3.symm.trans (haA bn f1))
  have eNo := beq_iff_eq.1 (List.all_eq_true.1 behind_closed l (List.mem_range.2 hl))
  rw [hP] at hn hans hseat
  rw [← eNo] at hseat
  obtain ⟨⟨y₀, hy₀, hs₀⟩, hall⟩ := K1.sits_fifty h O₁ hl true n hn hans
  have hs₀' : Sound.seatOf y₀ = P5J.At.seat3At Zp l true A.message := by
    rw [hseat]
    exact hs₀
  cases hf : h.𝔇.ms.find? (fun y => decide (Sound.seatOf y = P5J.At.seat3At Zp l true A.message))
    with
  | none =>
    exact absurd (decide_eq_true hs₀') (List.find?_eq_none.1 hf y₀ hy₀)
  | some y =>
    have hy0 := List.find?_some hf
    have hy1 : Sound.seatOf y = P5J.At.seat3At Zp l true A.message := of_decide_eq_true hy0
    have hy2 : y ∈ h.𝔇.ms := List.mem_of_find?_eq_some hf
    have hy3 : Sound.seatOf y =
        K1.seatAtMember cF.blocksInOrder (K1.noL l true) (K1.parL Zp Bs.G₀ l true) n := hy1.trans hseat
    refine ⟨p, bn, ⟨A, P5J.At.seat3At Zp l true A.message, M.shape⟩, y, hp, ?_, f6, rfl, ?_, hf,
      ?_, ?_, ?_, ?_⟩
    · rw [pArr, c4]
      exact f1
    · rw [pCs]
      exact hmat
    · rw [hP, ← eNo, ← hy3]
      rfl
    · rw [hP]
      exact hall y hy2 hy3
    · unfold parOfTail
      rw [c2, c3]
    · rw [c5]
      exact Nat.mul_le_mul_left 2 hmz

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.hSt_at_head
