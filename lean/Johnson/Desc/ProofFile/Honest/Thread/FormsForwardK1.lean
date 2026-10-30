-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/FormsForwardK1.lean: the open item `forms m k r` of the first
chain's invariant passes over a sending of oracle messages at a later moment of a segment (kind K1).
FormsForward.lean has the general lemmas. Here their hypotheses are taken from the relations in which
the library states what such a sending does to the open segment's part. No definition.

The relations, all of the library (Johnson/Desc/K1/Law/):
  * `RecRides new s s'` (PubAtLaterIndex.lean): what the tests on forms read of the open segment's
    part stays or grows; `new` lists the numbers of the messages that are found only after the step
  * `Grows`: the statement after the step has only grown
  * `AheadMeets sent own new s s'` (GoAtLaterForms.lean): an array that is not sent yet before the
    step and is found after it sits at the seat, and has the shape, that the plan gives it
The library shows the opposite direction from the same relations (`formsQ_back`, `formsQA_back'`,
GoAtLaterForms.lean), and the forward direction of the public tests (`formsInA_rides`,
`affIn_rides`, `lateOk_rides`, PubAtLaterIndex.lean).

  1  `formsQ_fwd_rec`, `formsQA_fwd_rec`   the statement for one run passes forward
  2  `ridesPastAt_forms_rec`   the hypothesis `RidesPastAt` (Honest/Thread/Shares.lean) for the item
     at `lettersHead`, at a sub-protocol whose `keeps` gives these relations

What 2 takes as a hypothesis: `keeps b` gives the common part of K1's clauses (`K1Rest`,
Honest/K1/Law/Keeps.lean), a list `new` with `RecRides`, that the reader's answer at each run of the
item stays (`Fwd`), for a run that is read ahead `AheadMeets` and a seat for each new message, and
the letter `wt` forward where `r` is "weights". That the list of commitment trees has a place for
every message before the step is shown from the invariant (`head_book`, RowPileForwardKinds.lean).

Limits.
  * Part 2: full size only, and only under the library's hypothesis `AtMgA` at the hash function
    `secondHashFunction` (FirstAt.lean says which that is).
  * This file shows the hypothesis of part 2 for no number `b`.
  * The witness is the same before and after the step.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FormsForward
import Johnson.Desc.ProofFile.Honest.Thread.RowPileForwardKinds
import Johnson.Desc.K1.Law.GoAtLaterForms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place Grows)
open VerifiableInference.Desc.First (S Item)
open VerifiableInference.Desc.K9 (segAt? Readers mergeOf seatAt affInA)
open VerifiableInference.Desc.Sound (MsgT MsgQ seatTab formsQ formsQA formsQA_in value_rides
  slotIn_mask mask_rides)
open VerifiableInference.Reads.Pass (Fwd)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-! ## 1 The statement for one run passes forward -/

section
variable {new : List Nat} {s s' : S} (R : VerifiableInference.Desc.K1.RecRides new s s')
  (g : Grows s.st s'.st) (hfull : s.book.place.size = s.st.oracles.size) (Rd : Readers)
  (own : List (Nat × Nat)) (piece : Nat) (run : String) (rd : Nat × Nat → MsgQ)
  (hRd : Fwd Rd piece run s s')
include R g hfull hRd

/-- What `formsQ` states before the sending it states after it. -/
theorem formsQ_fwd_rec (h : formsQ Rd own piece run s rd) : formsQ Rd own piece run s' rd := by
  obtain ⟨a, X, ha, hs, hl, hf⟩ := h
  obtain ⟨b, hb, hR, hr, -⟩ := VerifiableInference.Desc.K1.rides_of_rec R g hfull own ha
  refine ⟨b, X, hb, hRd X hs, ?_, fun f hm => ⟨?_, ?_⟩⟩
  · rw [VerifiableInference.Desc.K1.lateOk_rides hR]
    exact hl
  · rw [R.merge]
    exact VerifiableInference.Desc.K1.affIn_rides hR own _ _ (hf f hm).1
  · rw [value_rides own (mergeOf s) X.late a b rd hr f (hf f hm).1]
    exact (hf f hm).2

/-- What `formsQA` states before the sending it states after it. -/
theorem formsQA_fwd_rec (sent : Nat → List (Nat × Nat))
    (hseat : ∀ o ∈ new, (seatAt own s'.book o).isSome = true)
    (hmeet : VerifiableInference.Desc.K1.AheadMeets sent own new s s')
    (h : formsQA sent own Rd piece run s rd) : formsQA sent own Rd piece run s' rd := by
  have hin := formsQA_in sent own Rd piece run s rd h
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
  refine formsQA_fwd sent own Rd piece run s s' a b rd ha hb hRd
    (VerifiableInference.Desc.K1.formsInA_rides R Rd own piece run hRd sent hseat hin) hR.arrayOf
    hr.filled ?_ ?_ ⟨a, X, ha, hs, hl, hf⟩
  · intro X' hX' f hm x hx c hc
    obtain rfl : X' = X := Option.some.inj (hX'.symm.trans hs)
    exact VerifiableInference.Desc.K1.cellQA_back sent own hR hr hcodes rd
      (fun c hh o => hmeet a b c hh o ha hb) x ((hall f hm).1 x hx) c hc
  · intro X' hX' f hm x hx
    obtain rfl : X' = X := Option.some.inj (hX'.symm.trans hs)
    obtain ⟨y, hy⟩ := slotIn_mask own (mergeOf s) X'.late a x.1 ((hall f hm).2 x hx)
    exact mask_rides own a b rd hr y hy x.1

end

/-! ## 2 At the invariant -/

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
for a sending at a later moment of a segment. -/
theorem ridesPastAt_forms_rec {b : Nat} (m k : Nat) (ρ : String)
    (hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      ProofFile.Honest.K1.K1Rest s s' ∧ ∃ new,
        VerifiableInference.Desc.K1.RecRides new s s' ∧
        (∀ p ∈ h.𝔇.runs m k ρ, Fwd (h.𝔇.Rd m) p.1 p.2 s s') ∧
        (∀ p ∈ h.𝔇.runs m k ρ, h.𝔇.ah p.1 p.2 = true →
          (∀ o ∈ new, (seatAt (h.𝔇.N.group m) s'.book o).isSome = true) ∧
            VerifiableInference.Desc.K1.AheadMeets (h.𝔇.N.sent m) (h.𝔇.N.group m) new s s') ∧
        (ρ = "weights" → ∀ z y y' v, h.𝔇.wt m (z, s) y v → h.𝔇.wt m (z, s') y' v)) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b
      (Item.forms m k ρ) :=
  ridesPastAt_forms_older h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w m k ρ
    fun c s mm E s' hA hK => by
      obtain ⟨k1, new, R, hF, hM, hW⟩ := hk s s' hK
      have g : Grows s.st s'.st := k1.2.2.2.2.1.1.1.1
      have hfull := (head_book h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hA).2
      exact ⟨fun v p hp ha => formsQA_fwd_rec R g hfull _ _ _ _ _ (hF p hp) _ (hM p hp ha).1
          (hM p hp ha).2,
        fun v p hp _ => formsQ_fwd_rec R g hfull _ _ _ _ _ (hF p hp), hW⟩

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.formsQ_fwd_rec
#print axioms ProofFile.Honest.FirstThread.formsQA_fwd_rec
#print axioms ProofFile.Honest.FirstThread.ridesPastAt_forms_rec
