-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/FormsKinds.lean: small lemmas that bring the clauses of `keeps`
of the lookup on the digits (K3) and of a later sending (K1) to the hypotheses of the lemmas on the
open item `forms m k r` (FormsLater.lean, FormsForwardK1.lean). No definition.

  1  `k3Digits_part`, `k3Head_part`   from the clause at a lookup on the digits, of a feed-forward
     or an attention segment and of the output head's segment: the open segment's part after the
     step differs from the part before it in a later ledger alone. This is the first hypothesis of
     `ridesPastAt_forms_later` (FormsLater.lean). That writing the ledger's field `planClaimsF`
     gives a later ledger is the library's `LinkJoin.later_plan`
     (Johnson/Desc/First/Link/Law/LaterStretch.lean)
  2  `formsQA_fwd_rec_test`   `formsQA_fwd_rec` (FormsForwardK1.lean) with the public test after the
     step as a hypothesis, in the place of "each new message has a seat"
  3  `ridesPastAt_forms_rec_test`   `ridesPastAt_forms_rec` (FormsForwardK1.lean) in that form

Limits.
  * Part 3: full size only, and only under the library's hypothesis `AtMgA` at the hash function
    `secondHashFunction` (FirstAt.lean says which that is).
  * That `keeps b` gives what part 3 asks is a hypothesis. This file shows it for no number `b`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FormsLater
import Johnson.Desc.ProofFile.Honest.Thread.FormsForwardK1
import Johnson.Desc.First.Link.Law.LaterStretch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open OnBytes.PscRun (Later)
open VerifiableInference.Desc (Chain Strs Wit Place Grows)
open VerifiableInference.Desc.First (S Item)
open VerifiableInference.Desc.K9 (segAt? Readers mergeOf formsIn formsInA affInA)
open VerifiableInference.Desc.Sound (MsgT MsgQ seatTab formsQ formsQA slotIn_mask mask_rides)
open VerifiableInference.Reads.Pass (Fwd)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-! ## 1 The lookup on the digits -/

theorem k3Digits_part {hs : OnBytes.Model.Forest.Shape} {claims : Nat} {s s' : S}
    (k : ProofFile.Honest.K3.Law.AtThr.K3KeepsDigits hs claims s s') :
    ∀ a, segAt? s = some a → ∃ b, segAt? s' = some b ∧ b.L = a.L ∧ b.d.st = a.d.st ∧
      b.d.book = a.d.book ∧ Later a.F b.F := by
  obtain ⟨-, tl, F, H, G, -, hF, hA, hL⟩ := k
  exact digitsArms_part hF hA
    (hL.1.trans (VerifiableInference.Desc.LinkJoin.later_plan G claims))

theorem k3Head_part {hs : OnBytes.Model.Forest.Shape} {s s' : S}
    (k : ProofFile.Honest.K3.Law.AtThr.K3KeepsHead hs s s') :
    ∀ a, segAt? s = some a → ∃ b, segAt? s' = some b ∧ b.L = a.L ∧ b.d.st = a.d.st ∧
      b.d.book = a.d.book ∧ Later a.F b.F := by
  obtain ⟨-, tl, F, H, G, a₀, claim, -, hF, e1, ho, rfl, hL⟩ := k
  exact part_of_fields hF (by simp [S.link?, e1, ho]) (G := G) (by simp [S.fork?, ho])
    (by simp [S.tl?, ho]) rfl rfl hL.1

/-! ## 2 A later sending, with the public test after the step -/

/-- What `formsQA` states before the sending it states after it. `hin`: the public test after the
step. -/
theorem formsQA_fwd_rec_test {new : List Nat} {s s' : S}
    (R : VerifiableInference.Desc.K1.RecRides new s s') (g : Grows s.st s'.st)
    (hfull : s.book.place.size = s.st.oracles.size) (Rd : Readers) (own : List (Nat × Nat))
    (piece : Nat) (run : String) (rd : Nat × Nat → MsgQ) (hRd : Fwd Rd piece run s s')
    (sent : Nat → List (Nat × Nat)) (hin : formsInA Rd sent own piece run s' = true)
    (hmeet : VerifiableInference.Desc.K1.AheadMeets sent own new s s')
    (h : formsQA sent own Rd piece run s rd) : formsQA sent own Rd piece run s' rd := by
  obtain ⟨a, X, ha, hs, hl, hf⟩ := h
  obtain ⟨b, hb, hR, hr, hcodes⟩ := VerifiableInference.Desc.K1.rides_of_rec R g hfull own ha
  have hall : ∀ f ∈ X.forms, (∀ x ∈ f.ents.toList,
      VerifiableInference.Desc.K9.entInA sent own a x = true) ∧
      ∀ x ∈ f.slots.toList,
        VerifiableInference.Desc.K9.slotIn own (mergeOf s) X.late a x.1 = true := by
    intro f hm
    have h1 := (hf f hm).1
    unfold affInA at h1
    rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h1
    exact h1
  refine formsQA_fwd sent own Rd piece run s s' a b rd ha hb hRd hin hR.arrayOf hr.filled ?_ ?_
    ⟨a, X, ha, hs, hl, hf⟩
  · intro X' hX' f hm x hx c hc
    obtain rfl : X' = X := Option.some.inj (hX'.symm.trans hs)
    exact VerifiableInference.Desc.K1.cellQA_back sent own hR hr hcodes rd
      (fun c hh o => hmeet a b c hh o ha hb) x ((hall f hm).1 x hx) c hc
  · intro X' hX' f hm x hx
    obtain rfl : X' = X := Option.some.inj (hX'.symm.trans hs)
    obtain ⟨y, hy⟩ := slotIn_mask own (mergeOf s) X'.late a x.1 ((hall f hm).2 x hx)
    exact mask_rides own a b rd hr y hy x.1

/-! ## 3 At the invariant -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- The item `forms m k ρ` passes over a sub-protocol whose `keeps` gives the library's relations
for a sending at a later moment of a segment, and the public test after the step at each run that is
read ahead. -/
theorem ridesPastAt_forms_rec_test {b : Nat} (m k : Nat) (ρ : String)
    (hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      ProofFile.Honest.K1.K1Rest s s' ∧ ∃ new,
        VerifiableInference.Desc.K1.RecRides new s s' ∧
        (∀ p ∈ h.𝔇.runs m k ρ, Fwd (h.𝔇.Rd m) p.1 p.2 s s') ∧
        (∀ p ∈ h.𝔇.runs m k ρ, h.𝔇.ah p.1 p.2 = true →
          formsInA (h.𝔇.Rd m) (h.𝔇.N.sent m) (h.𝔇.N.group m) p.1 p.2 s' = true ∧
            VerifiableInference.Desc.K1.AheadMeets (h.𝔇.N.sent m) (h.𝔇.N.group m) new s s') ∧
        (ρ = "weights" → ∀ z y y' v, h.𝔇.wt m (z, s) y v → h.𝔇.wt m (z, s') y' v)) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b
      (Item.forms m k ρ) :=
  ridesPastAt_forms_older h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w m k ρ
    fun c s mm E s' hA hK => by
      obtain ⟨k1, new, R, hF, hM, hW⟩ := hk s s' hK
      have g : Grows s.st s'.st := k1.2.2.2.2.1.1.1.1
      have hfull := (head_book h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hA).2
      exact ⟨fun v p hp ha => formsQA_fwd_rec_test R g hfull _ _ _ _ _ (hF p hp) _
          (hM p hp ha).1 (hM p hp ha).2,
        fun v p hp _ => formsQ_fwd_rec R g hfull _ _ _ _ _ (hF p hp), hW⟩

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.k3Digits_part
#print axioms ProofFile.Honest.FirstThread.k3Head_part
#print axioms ProofFile.Honest.FirstThread.formsQA_fwd_rec_test
#print axioms ProofFile.Honest.FirstThread.ridesPastAt_forms_rec_test
