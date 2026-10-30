-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/FormsLater.lean: the open item `forms m k r` of the first
chain's invariant passes over a sub-protocol that leaves the open segment's context, the statement
and the list of commitment trees, and turns the segment's ledger into a later one
(`OnBytes.PscRun.Later`, OnBytes/Tie/Pv/Psc/PscLater.lean). The draw of the smallness test (K8) and
the lookup on the digits (K3) are of this sort. FormsForward.lean has the general lemmas. No
definition.

Two hypotheses are not about fields of the state.
  * `Fwd`: what the segment's reader answers at a run before the step it answers after it.
  * The public test that the table ties to the item holds after the step (`K9.formsIn`, and
    `K9.formsInA` at a run that is read ahead). The part `Form` of the invariant after the step
    contains it.

  1  `formsQ_fwd_test`   `formsQ_fwd` (FormsForward.lean) with the public test after the step in the
     place of the relation `More`
  2  `rides_later`   for two parts of an open segment with the same context, statement and list of
     trees, the second ledger later than the first: the library's relation `Rides`. That the data
     are the same, also where a form may name an array that is not sent yet, is the library's
     `Sound.dataQA_same` (Johnson/Desc/Sound/MgAt/K3RidesDigFull.lean)
  3  `formsQ_fwd_later`, `formsQA_fwd_later`   the statement for one run passes forward
  4  `ridesPastAt_forms_later`   the hypothesis `RidesPastAt` (Honest/Thread/Shares.lean) for the
     item at `lettersHead`
  5  `drawn_part`, `part_of_fields`, `digitsArms_part`   the hypothesis of 3 and 4 on the two parts,
     from the library's relation for K8's draw and from the three forms of the state after a lookup
     on the digits

Limits.
  * Part 4: full size only, and only under the library's hypothesis `AtMgA` at the hash function
    `secondHashFunction` (FirstAt.lean says which that is).
  * `Fwd`, the public test after the step, and the letter `wt` forward where `r` is "weights" are
    hypotheses. This file shows them for no kind and at no state.
  * The witness is the same before and after the step.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FormsForward
import Johnson.Desc.ProofFile.Honest.Thread.WoKinds
import Johnson.Top.H.Keep.FormsPassK3
import Johnson.Desc.Sound.MgAt.K3RidesDigFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open OnBytes.PscRun (Later)
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.First (S Item)
open VerifiableInference.Desc.K9 (segAt? Readers mergeOf formsIn formsInA)
open VerifiableInference.Desc.Sound (MsgT MsgQ seatTab formsQ formsQA Rides value_rides
  dataQA_same)
open VerifiableInference.Reads.Pass (Fwd)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-! ## 1 With the public test after the step -/

/-- What `formsQ` states before the step it states after it. `hin`: the public test after the
step. -/
theorem formsQ_fwd_test (Rd : Readers) (own : List (ℕ × ℕ)) (piece : ℕ) (run : String) (s s' : S)
    (a b : VerifiableInference.Desc.K9.Part) (rd : ℕ × ℕ → MsgQ) (ha : segAt? s = some a)
    (hb : segAt? s' = some b) (hf : Fwd Rd piece run s s')
    (hin : formsIn Rd own piece run s' = true) (hr : Rides own a b)
    (h : formsQ Rd own piece run s rd) : formsQ Rd own piece run s' rd := by
  obtain ⟨a', R, ha', hs, -, hfm⟩ := h
  obtain rfl : a' = a := Option.some.inj (ha'.symm.trans ha)
  have hs' := hf R hs
  unfold formsIn at hin
  rw [hb, hs'] at hin
  obtain ⟨hlate, hall⟩ := Eq.mp (Bool.and_eq_true _ _) hin
  refine ⟨b, R, hb, hs', hlate, fun f hm => ⟨List.all_eq_true.1 hall f hm, ?_⟩⟩
  rw [value_rides own (mergeOf s) R.late a' b rd hr f (hfm f hm).1]
  exact (hfm f hm).2

/-! ## 2 Two parts that differ in the ledger alone -/

section
variable {a b : VerifiableInference.Desc.K9.Part} (hL : b.L = a.L) (hst : b.d.st = a.d.st)
  (hbk : b.d.book = a.d.book)
include hL hst hbk

/-- The library's relation `Rides`. -/
theorem rides_later (own : List (ℕ × ℕ)) (hl : Later a.F b.F) : Rides own a b where
  arrays := by rw [hL]
  rows := by rw [hL]
  sent := fun _ _ _ h => by rw [hL]; exact h
  mask := fun _ h => by rw [hL]; exact h
  book := fun _ _ h => by rw [hbk]; exact h
  bits := fun _ _ _ _ => by rw [hst]; exact ⟨rfl, rfl⟩
  filled := fun j _ hj => (hl.keep j hj).2

end

/-! ## 3 The statement for one run passes forward -/

section
variable {s s' : S}
  (hp : ∀ a, segAt? s = some a → ∃ b, segAt? s' = some b ∧ b.L = a.L ∧ b.d.st = a.d.st ∧
    b.d.book = a.d.book ∧ Later a.F b.F)
  (Rd : Readers) (own : List (ℕ × ℕ)) (piece : ℕ) (run : String) (rd : ℕ × ℕ → MsgQ)
  (hf : Fwd Rd piece run s s')
include hp hf

theorem formsQ_fwd_later (hin : formsIn Rd own piece run s' = true)
    (h : formsQ Rd own piece run s rd) : formsQ Rd own piece run s' rd := by
  obtain ⟨a, R, ha, hs, hl, hfm⟩ := h
  obtain ⟨b, hb, e1, e2, e3, e4⟩ := hp a ha
  exact formsQ_fwd_test Rd own piece run s s' a b rd ha hb hf hin (rides_later e1 e2 e3 own e4)
    ⟨a, R, ha, hs, hl, hfm⟩

theorem formsQA_fwd_later (sent : ℕ → List (ℕ × ℕ))
    (hin : formsInA Rd sent own piece run s' = true)
    (h : formsQA sent own Rd piece run s rd) : formsQA sent own Rd piece run s' rd := by
  obtain ⟨a, R, ha, hs, hl, hfm⟩ := h
  obtain ⟨b, hb, e1, e2, e3, e4⟩ := hp a ha
  exact formsQA_fwd sent own Rd piece run s s' a b rd ha hb hf hin (by rw [e1])
    (fun j _ hj => (e4.keep j hj).2)
    (fun _ _ _ _ _ _ _ _ => by rw [dataQA_same sent own e1 e2 e3 rd])
    (fun _ _ _ _ _ _ => by rw [dataQA_same sent own e1 e2 e3 rd]) ⟨a, R, ha, hs, hl, hfm⟩

end

/-! ## 5 The two parts, from the kinds' clauses -/

/-- After the draw of the smallness test the open segment's part is as it was. -/
theorem drawn_part {s s' : S} (k : VerifiableInference.Desc.First.K8.Drawn s s') :
    ∀ a, segAt? s = some a → ∃ b, segAt? s' = some b ∧ b.L = a.L ∧ b.d.st = a.d.st ∧
      b.d.book = a.d.book ∧ Later a.F b.F :=
  fun a ha => ⟨a, (VerifiableInference.Desc.First.K8.blind_segAt s s' k).trans ha, rfl, rfl, rfl,
    Later.refl _⟩

/-- From what a state after the step has as its context, its ledger and its range proof's part. -/
theorem part_of_fields {s s' : S} {F G : OnBytes.Model.Fork} (hF : s.fork? = some F)
    (hlink : s'.link? = s.link?) (hG : s'.fork? = some G) (htl : s'.tl?.isSome = true)
    (hst : s'.st = s.st) (hbk : s'.book = s.book) (hl : Later F G) :
    ∀ a, segAt? s = some a → ∃ b, segAt? s' = some b ∧ b.L = a.L ∧ b.d.st = a.d.st ∧
      b.d.book = a.d.book ∧ Later a.F b.F := by
  intro a ha
  obtain ⟨h1, h2, -, h4, h5⟩ := VerifiableInference.OnPublicFiles.segAt_cut ha
  obtain ⟨b, hb, e1, e2, e3, e4⟩ := VerifiableInference.OnPublicFiles.segAt_make (hlink.trans h1) hG htl
  obtain rfl : a.F = F := Option.some.inj (h2.symm.trans hF)
  exact ⟨b, hb, e1, by rw [e3, hst, h4], by rw [e4, hbk, h5], by rw [e2]; exact hl⟩

/-- After a lookup on the digits, in the three forms of the state after it. -/
theorem digitsArms_part {s s' : S} {tl' : OnBytes.Model.HTailF2} {F G' : OnBytes.Model.Fork}
    (hF : s.fork? = some F) (k : ProofFile.Honest.K3.Law.AtThr.DigitsArms s s' tl' G')
    (hl : Later F G') :
    ∀ a, segAt? s = some a → ∃ b, segAt? s' = some b ∧ b.L = a.L ∧ b.d.st = a.d.st ∧
      b.d.book = a.d.book ∧ Later a.F b.F := by
  rcases k with ⟨a₀, e1, rfl⟩ | ⟨a₀, e1, rfl⟩ | ⟨a₀, e1, ho, rfl⟩
  · exact part_of_fields hF (by simp [S.link?, e1]) (G := G') (by simp [S.fork?])
      (by simp [S.tl?]) rfl rfl hl
  · exact part_of_fields hF (by simp [S.link?, e1]) (G := G') (by simp [S.fork?])
      (by simp [S.tl?]) rfl rfl hl
  · exact part_of_fields hF (by simp [S.link?, e1, ho]) (G := G') (by simp [S.fork?, ho])
      (by simp [S.tl?, ho]) rfl rfl hl

/-! ## 4 At the invariant -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- The item `forms m k ρ` passes over a sub-protocol whose `keeps` gives: the open segment's part
after the step differs from the part before it in a later ledger alone; the reader's answers at the
item's runs stay; the public tests at these runs hold after the step; the letter `wt` passes forward
where `ρ` is "weights". -/
theorem ridesPastAt_forms_later {b : Nat} (m k : Nat) (ρ : String)
    (hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      (∀ a, segAt? s = some a → ∃ b', segAt? s' = some b' ∧ b'.L = a.L ∧ b'.d.st = a.d.st ∧
        b'.d.book = a.d.book ∧ Later a.F b'.F) ∧
      (∀ p ∈ h.𝔇.runs m k ρ, Fwd (h.𝔇.Rd m) p.1 p.2 s s') ∧
      (∀ p ∈ h.𝔇.runs m k ρ, h.𝔇.ah p.1 p.2 = true →
        formsInA (h.𝔇.Rd m) (h.𝔇.N.sent m) (h.𝔇.N.group m) p.1 p.2 s' = true) ∧
      (∀ p ∈ h.𝔇.runs m k ρ, ¬ h.𝔇.ah p.1 p.2 = true →
        formsIn (h.𝔇.Rd m) (h.𝔇.N.group m) p.1 p.2 s' = true) ∧
      (ρ = "weights" → ∀ z y y' v, h.𝔇.wt m (z, s) y v → h.𝔇.wt m (z, s') y' v)) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b
      (Item.forms m k ρ) :=
  ridesPastAt_forms_older h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w m k ρ
    fun _ s _ _ s' _ hK =>
      ⟨fun v p hp ha => formsQA_fwd_later (hk s s' hK).1 (h.𝔇.Rd m) (h.𝔇.N.group m) p.1 p.2
          (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms v) ((hk s s' hK).2.1 p hp) (h.𝔇.N.sent m)
          ((hk s s' hK).2.2.1 p hp ha),
        fun v p hp ha => formsQ_fwd_later (hk s s' hK).1 (h.𝔇.Rd m) (h.𝔇.N.group m) p.1 p.2
          (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms v) ((hk s s' hK).2.1 p hp)
          ((hk s s' hK).2.2.2.1 p hp ha),
        (hk s s' hK).2.2.2.2⟩

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.formsQ_fwd_test
#print axioms ProofFile.Honest.FirstThread.rides_later
#print axioms ProofFile.Honest.FirstThread.formsQ_fwd_later
#print axioms ProofFile.Honest.FirstThread.formsQA_fwd_later
#print axioms ProofFile.Honest.FirstThread.drawn_part
#print axioms ProofFile.Honest.FirstThread.part_of_fields
#print axioms ProofFile.Honest.FirstThread.digitsArms_part
#print axioms ProofFile.Honest.FirstThread.ridesPastAt_forms_later
