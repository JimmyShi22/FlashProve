-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/CellsPin.lean: at every place of the first chain at the full
size that is not of the kind `frame`, the clause of `fHead` (FHead.lean) keeps each oracle message's
first sample row: a row that is there before the step is there after it. So the items `pinI` and
`pin` pass over these 281 sub-protocols, where the condition `keeps` is `fHead`. That is a part of
the column `hR` of the gathering (`owesS_head_form`, GatherHeadForm.lean). No definition.

  1  `sameAll_row`, `k12_row`, `k2_row`   on two states: what the clauses of K13, of K12 and of K2
     say of the first sample rows
  2  `fHead_row`   the clause at a place of one of eleven kinds keeps the first sample rows, if no
     message without the mark "sampled" has a sample row before the step
  3  `head_older_all`   the hypothesis of `ridesPastAt_pinI_older` and `ridesPastAt_pin_older`
     (PinForward.lean) at every place that is not of the kind `frame`
  4  `head_rides_pins`   the two sorts of item pass

Called: at K1 `k1Rest_row`, `k1KeepsAt_row` (PinForwardKinds.lean) and `send_rows_row`
(PinForwardSend.lean); at K10 `k10Keeps_row` (PinForwardKinds.lean); at K7 and K9 `head_older_k7`,
`head_older_k9` (PinKeptCells.lean); at K11 `k11Keeps_st` (K11PinRides.lean); at K3, K4, K6, K8
`fHead_quiet` (CellsQuiet.lean); at K5 `k5_quiet` (ArmsQuiet.lean); at the opening of a segment
`keepsOpened_st` (Honest/Law/NoHouse/OpenedKeeps.lean).

Limits.
  * The lemmas stand at `keeps` := `fHead`. A stronger `keeps` follows by
    `head_ridesPastAtS_mono` (KeepsMono.lean).
  * Full size only, under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.CellsQuiet
import Johnson.Desc.ProofFile.Honest.Thread.PinKeptCells
import Johnson.Desc.ProofFile.Honest.Thread.PinForwardSend
import Johnson.Desc.ProofFile.Honest.Thread.K11PinRides
import Johnson.Desc.ProofFile.Honest.Thread.SteppedYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (Item S)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-- Two statements that are alike in the library's sense `SameAll` have the same first sample
rows. -/
theorem sameAll_row {A B : OnBytes.Statement} (h : VerifiableInference.Desc.K13.Law.SameAll A B)
    (o : Nat) : rowAt₀ B o = rowAt₀ A o := by
  refine rowAt₀_same ?_
  have e := h.2 o
  unfold VerifiableInference.Desc.K13.Law.sampleOf at e
  cases hA : A.oracles[o]? with
  | none =>
    cases hB : B.oracles[o]? with
    | none => rfl
    | some y =>
      rw [hA, hB] at e
      cases e
  | some x =>
    cases hB : B.oracles[o]? with
    | none =>
      rw [hA, hB] at e
      cases e
    | some y =>
      rw [hA, hB] at e
      have e' : (y.shape, y.sampled, y.sampleRows, y.pad) =
          (x.shape, x.sampled, x.sampleRows, x.pad) := Option.some.inj e
      show some y.sampleRows = some x.sampleRows
      rw [(Prod.mk.inj (Prod.mk.inj (Prod.mk.inj e').2).2).1]

/-- K12's clause keeps a first sample row that is there. -/
theorem k12_row {p : VerifiableInference.Desc.K12.P12} {s s' : S}
    (K : ProofFile.Honest.Sh.K12KeepsFirst p s s') {o : Nat} {q : OnBytes.Row}
    (hq : rowAt₀ s.st o = some q) : rowAt₀ s'.st o = some q := by
  rw [rowAt₀_rows] at hq ⊢
  cases hx : s.st.oracles[o]? with
  | none =>
    rw [hx] at hq
    cases hq
  | some x =>
    obtain ⟨x', hx', e⟩ := K.samples hx
    rw [hx] at hq
    rw [hx']
    show x'.sampleRows[0]? = some q
    rw [e]
    exact hq

/-- K2's clause keeps a first sample row that is there. -/
theorem k2_row {p : VerifiableInference.Desc.First.K2.P2} {s s' : S}
    (K : VerifiableInference.Desc.K2.Honest.K2Keeps p s s') (hN : OnBytes.Means.NoneYet s.st)
    {o : Nat} {q : OnBytes.Row} (hq : rowAt₀ s.st o = some q) : rowAt₀ s'.st o = some q :=
  rowAt₀_smpStay K.common.2.2.2.2.2 hN hq

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

include h in
/-- **The clause of `fHead` keeps the first sample rows**, at a place of a kind other than `frame`,
K7 and K9. -/
theorem fHead_row (G : ProofFile.Ground) (take : Nat → Bool)
    (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
    (P13 : VerifiableInference.Desc.K13.Where) {b : Nat} {p : Place}
    (hp : P5J.At.ps[b]? = some p) (hk : p.kind ≠ KindName.frame) (hk7 : p.kind ≠ KindName.K7)
    (hk9 : p.kind ≠ KindName.K9) (s s' : TS) (hN : OnBytes.Means.NoneYet s.st)
    (ha : fHead Zp cF G take P11 p12 P13 p.kind p s s') {o : Nat} {q : OnBytes.Row}
    (hq : rowAt₀ s.st o = some q) : rowAt₀ s'.st o = some q := by
  have hm : p ∈ P5J.At.ps := List.mem_of_getElem? hp
  have hst : s'.st = s.st → rowAt₀ s'.st o = some q := fun e => by rw [e]; exact hq
  cases hκ : p.kind
  case frame => exact absurd hκ hk
  case K7 => exact absurd hκ hk7
  case K9 => exact absurd hκ hk9
  case K1 =>
    rw [hκ] at ha
    change (if p.link = some 0 ∧ p.piece = 1 then _ else if p.link = none ∧ p.piece = 4 then _
      else _) at ha
    split at ha
    · obtain ⟨m, hf, ho⟩ := ha
      rw [keepsOpened_st ho.1]
      exact k1Rest_row hf.1.1 hN hq
    · split at ha
      · exact send_rows_row ha.1 hq
      · exact k1KeepsAt_row ha.1 hN hq
  case K2 =>
    rw [hκ] at ha
    cases hl : p.link with
    | none =>
      obtain ⟨c, -, hK⟩ := (fHead_K2_finish Zp cF G take P11 p12 P13 hl s s').1 ha
      exact k2_row hK hN hq
    | some l =>
      by_cases h24 : l = 24
      · subst h24
        obtain ⟨c, -, hK⟩ := (fHead_K2_head Zp cF G take P11 p12 P13 hl s s').1 ha
        exact k2_row hK hN hq
      · obtain ⟨m, ⟨c, -, hK⟩, ho⟩ := (fHead_K2_link Zp cF G take P11 p12 P13 hl h24 s s').1 ha
        rw [keepsOpened_st ho.1]
        exact k2_row hK hN hq
  case K3 => exact hst (fHead_quiet h G take P11 p12 P13 hp (Or.inl hκ) s s' ha).1
  case K4 => exact hst (fHead_quiet h G take P11 p12 P13 hp (Or.inr (Or.inl hκ)) s s' ha).1
  case K5 =>
    rw [hκ] at ha
    have t2 := (Bool.and_eq_true_iff.1 (List.all_eq_true.1 k3_k5_places p hm)).2
    rw [hκ, show (KindName.K5 != KindName.K5) = false from rfl, Bool.false_or] at t2
    obtain ⟨t3, t4⟩ := Bool.and_eq_true_iff.1 t2
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 t3
    rw [hl] at t4
    obtain ⟨a, hA⟩ := fHead_hA h (l / 2) (of_decide_eq_true t4)
    have ha' : H2K5.Honest.K5KeepsAt (P5J.At.X Zp) p s s' := ha
    exact hst (k5_quiet (ha' l a hl hA)).1
  case K6 =>
    exact hst (fHead_quiet h G take P11 p12 P13 hp (Or.inr (Or.inr (Or.inl hκ))) s s' ha).1
  case K8 =>
    exact hst (fHead_quiet h G take P11 p12 P13 hp (Or.inr (Or.inr (Or.inr hκ))) s s' ha).1
  case K10 =>
    rw [hκ] at ha
    rw [k10Keeps_row (show ProofFile.Honest.K10.YesFree.K10Keeps s s' from ha) o]
    exact hq
  case K11 =>
    rw [hκ] at ha
    exact hst (k11Keeps_st
      (show Johnson.Desc.First.ForkMerge.Returns.K11KeepsYesAt P11 p s s' from ha).2.1)
  case K12 =>
    rw [hκ] at ha
    exact k12_row (show ProofFile.Honest.Sh.K12KeepsFirst p12 s s' from ha) hq
  case K13 =>
    rw [hκ] at ha
    rw [sameAll_row
      (show VerifiableInference.Desc.K13.Honest.K13KeepsAll P13 s s' from ha).1.2.2.2.2.2.2.1 o]
    exact hq
  case K14 =>
    have u := List.all_eq_true.1 places_no_k14_k15 p hm
    rw [hκ] at u
    exact absurd u (by decide)
  case K15 =>
    have u := List.all_eq_true.1 places_no_k14_k15 p hm
    rw [hκ] at u
    exact absurd u (by decide)

variable {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (G : ProofFile.Ground) (take : Nat → Bool)
  (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
  (P13 : VerifiableInference.Desc.K13.Where) (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **A first sample row that is there stays**, over every sub-protocol that is not of the kind
`frame`. -/
theorem head_older_all {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind ≠ KindName.frame) :
    ∀ k s mm E s',
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHead Zp cF G take P11 p12 P13)) w).thread b k s mm E →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHead Zp cF G take P11 p12 P13)) w).thread.keeps b s s' →
      ∀ o q, rowAt₀ s.st o = some q → rowAt₀ s'.st o = some q := by
  by_cases hk7 : p.kind = KindName.K7
  · exact head_older_k7 h H Q test carryX item n₁ n₂ b₀ Vd Rd (fHead Zp cF G take P11 p12 P13) w rfl
      hp hk7
  by_cases hk9 : p.kind = KindName.K9
  · exact head_older_k9 h H Q test carryX item n₁ n₂ b₀ Vd Rd (fHead Zp cF G take P11 p12 P13) w rfl
      hb hp hk9
  intro k s mm E s' hA hK o q hq
  have hlen : b ≤ cF.blocksInOrder.length := by
    rw [head_len h]
    omega
  exact fHead_row h G take P11 p12 P13 hp hk hk7 hk9 s s'
    (head_tidy h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy (fHead Zp cF G take P11 p12 P13)) w hlen
      hA).noneYet
    ((head_keeps h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy (fHead Zp cF G take P11 p12 P13)) w hp
      s s').1 hK) hq

/-- **The items `pinI` and `pin` pass over every sub-protocol that is not of the kind `frame`.** -/
theorem head_rides_pins {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind ≠ KindName.frame) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHead Zp cF G take P11 p12 P13)) w).thread b Item.pinI ∧
      ∀ m t, RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHead Zp cF G take P11 p12 P13)) w).thread b (Item.pin m t) :=
  ⟨ridesPastAt_pinI_older h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHead Zp cF G take P11 p12 P13)) w
      (head_older_all h H Q test carryX item n₁ n₂ b₀ Vd Rd G take P11 p12 P13 w hb hp hk),
    fun m t => ridesPastAt_pin_older h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHead Zp cF G take P11 p12 P13)) w m t
      (head_older_all h H Q test carryX item n₁ n₂ b₀ Vd Rd G take P11 p12 P13 w hb hp hk)⟩

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.sameAll_row
#print axioms ProofFile.Honest.FirstThread.k12_row
#print axioms ProofFile.Honest.FirstThread.k2_row
#print axioms ProofFile.Honest.FirstThread.fHead_row
#print axioms ProofFile.Honest.FirstThread.head_older_all
#print axioms ProofFile.Honest.FirstThread.head_rides_pins
