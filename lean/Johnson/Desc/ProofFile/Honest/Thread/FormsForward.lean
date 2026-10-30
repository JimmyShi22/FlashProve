-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/FormsForward.lean: the open item `forms m k r` of the first
chain's invariant passes over a sub-protocol, from the state before the step to the state after it.
The item states, for each run of a list, that the forms which the segment's reader gives for that
run are worth 0 at the witness (`formsQ`, Johnson/Desc/Sound/FormsQ.lean; `formsQA`,
Johnson/Desc/Sound/FormsAhead.lean, where a form may name an array that is not sent yet). No
definition.

The library shows the opposite direction (`forms_back`, Johnson/Desc/Reads/FormsPass.lean;
`formsQA_back`, FormsAhead.lean). It already has what the forward direction needs:
  * three relations between the two states, general in the reader, the seats and the run: `Fwd`
    (what the reader answers before the step it answers after it), `Rides` and `More` (what a form
    can see of the open segment's part stays)
  * under these a form that names only what is there before the step names only what is there after
    it (`affIn_more`, FormsPass.lean)
  * a form's worth is the same at both states (`value_rides`, `value_ridesW`, FormsQ.lean): an
    equation
The proofs of part 1 below are the library's proofs with these lemmas used in the other direction.

  1  `formsQ_fwd`, `formsQA_fwd`   the statement for one run passes forward. The second takes the
     public test after the step (`formsInA`) as a hypothesis, and the premises of `formsQA_back`
  2  `forms_older`   the item's statement at the library's meaning `mgAll`, from the statements for
     its runs and from the same for the letter `wt`, which the item reads where `r` is "weights"
  3  `ridesPastAt_forms_older`   the hypothesis `RidesPastAt` (Honest/Thread/Shares.lean) for the
     item at `lettersHead`, at every sub-protocol number `b`

The hypothesis of 3 may use the invariant before the step (`Thr`).

Limits.
  * `ridesPastAt_forms_older`: full size only, and only under the library's hypothesis `AtMgA` at
    the hash function `secondHashFunction` (FirstAt.lean says which that is).
  * The relations between the two states are hypotheses. This file shows them for no kind and at no
    state. `Fwd` is a fact on the segment's reader, not on fields of the state.
  * The witness is the same before and after the step.
  * Nothing here shows that the item's statement holds at any state of a run.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.Shares
import Johnson.Desc.Reads.FormsPass
import Johnson.Desc.Sound.FormsAhead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open OnBytes (zeroE)
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.First (S Item Meaning)
open VerifiableInference.Desc.K9 (segAt? Readers mergeOf formsInA affInA)
open VerifiableInference.Desc.Sound (MsgT MsgQ MgData mgAll mgBase mgAll_forms CellsQ seatTab
  formsQ formsQA dataQA Rides value_rides value_ridesW)
open VerifiableInference.Reads.Pass (Fwd More affIn_more)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-! ## 1 The statement for one run passes forward -/

/-- What `formsQ` states before the step it states after it, under the library's three relations. -/
theorem formsQ_fwd (Rd : Readers) (own : List (ℕ × ℕ)) (piece : ℕ) (run : String) (s s' : S)
    (a b : VerifiableInference.Desc.K9.Part) (rd : ℕ × ℕ → MsgQ) (ha : segAt? s = some a)
    (hb : segAt? s' = some b)
    (hf : Fwd Rd piece run s s') (hr : Rides own a b)
    (hM : ∀ R, Rd.forms piece run s = some R → More R.late a b s s')
    (h : formsQ Rd own piece run s rd) : formsQ Rd own piece run s' rd := by
  obtain ⟨a', R, ha', hs, -, hfm⟩ := h
  obtain rfl : a' = a := Option.some.inj (ha'.symm.trans ha)
  refine ⟨b, R, hb, hf R hs, (hM R hs).late, fun f hm =>
    ⟨affIn_more own hr (hM R hs) (hfm f hm).1, ?_⟩⟩
  rw [value_rides own (mergeOf s) R.late a' b rd hr f (hfm f hm).1]
  exact (hfm f hm).2

/-- What `formsQA` states before the step it states after it. `hin`: the public test after the step.
The other hypotheses are those of the library's `formsQA_back`. -/
theorem formsQA_fwd (sent : ℕ → List (ℕ × ℕ)) (own : List (ℕ × ℕ)) (Rd : Readers) (piece : ℕ)
    (run : String) (s s' : S) (a b : VerifiableInference.Desc.K9.Part) (rd : ℕ × ℕ → MsgQ)
    (ha : segAt? s = some a)
    (hb : segAt? s' = some b) (hf : Fwd Rd piece run s s')
    (hin : formsInA Rd sent own piece run s' = true) (harr : b.L.arrayOf = a.L.arrayOf)
    (hfill : ∀ j : ℕ, j < a.F.ns → a.F.gotF.getD j false = true →
      b.F.vp.getD j zeroE = a.F.vp.getD j zeroE ∧ b.F.mf.getD j zeroE = a.F.mf.getD j zeroE)
    (hcell : ∀ R : VerifiableInference.Desc.K9.Read, Rd.forms piece run s = some R → ∀ f ∈ R.forms,
      ∀ x ∈ f.ents.toList, ∀ c : ℕ × String, a.L.arrayOf[x.tree]? = some c →
        (dataQA sent own b rd).cell c.1 c.2 x.row x.idx =
          (dataQA sent own a rd).cell c.1 c.2 x.row x.idx)
    (hmask : ∀ R : VerifiableInference.Desc.K9.Read, Rd.forms piece run s = some R → ∀ f ∈ R.forms,
      ∀ x ∈ f.slots.toList, (dataQA sent own b rd).mask x.1 = (dataQA sent own a rd).mask x.1)
    (h : formsQA sent own Rd piece run s rd) : formsQA sent own Rd piece run s' rd := by
  obtain ⟨a', R, ha', hs, -, hfm⟩ := h
  obtain rfl : a' = a := Option.some.inj (ha'.symm.trans ha)
  have hs' := hf R hs
  unfold formsInA at hin
  rw [hb, hs'] at hin
  obtain ⟨hlate, hall⟩ := Eq.mp (Bool.and_eq_true _ _) hin
  refine ⟨b, R, hb, hs', hlate, fun f hm => ⟨List.all_eq_true.1 hall f hm, ?_⟩⟩
  have h2 := (hfm f hm).1
  unfold affInA at h2
  obtain ⟨-, h3⟩ := Eq.mp (Bool.and_eq_true _ _) h2
  rw [value_ridesW own (mergeOf s) R.late a' b (dataQA sent own a' rd) (dataQA sent own b rd)
    harr hfill f (List.all_eq_true.1 h3) (hcell R hs f hm) (hmask R hs f hm)]
  exact (hfm f hm).2

/-! ## 2 At the library's meaning -/

section
variable {Xi P Tok : Type} {rows cols nR : Nat} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))
  {s s' : S}

/-- The statement of `forms m k r` passes from `s` to `s'`, if the statement for each of its runs
does, and the letter `wt` where `r` is "weights". -/
theorem forms_older (m k : Nat) (r : String) (z : P) (y y' : Strs)
    (w : Wit (CellsQ rows cols) Tok MsgT)
    (hA : ∀ p ∈ 𝔇.runs m k r, 𝔇.ah p.1 p.2 = true →
      formsQA (𝔇.N.sent m) (𝔇.N.group m) (𝔇.Rd m) p.1 p.2 s (seatTab 𝔇.cs 𝔇.arr 𝔇.ms w) →
      formsQA (𝔇.N.sent m) (𝔇.N.group m) (𝔇.Rd m) p.1 p.2 s' (seatTab 𝔇.cs 𝔇.arr 𝔇.ms w))
    (hQ : ∀ p ∈ 𝔇.runs m k r, ¬ 𝔇.ah p.1 p.2 = true →
      formsQ (𝔇.Rd m) (𝔇.N.group m) p.1 p.2 s (seatTab 𝔇.cs 𝔇.arr 𝔇.ms w) →
      formsQ (𝔇.Rd m) (𝔇.N.group m) p.1 p.2 s' (seatTab 𝔇.cs 𝔇.arr 𝔇.ms w))
    (hW : r = "weights" → 𝔇.wt m (z, s) y w → 𝔇.wt m (z, s') y' w)
    (h0 : (mgAll 𝔇 Mg).forms m k r (z, s) y w) : (mgAll 𝔇 Mg).forms m k r (z, s') y' w := by
  rw [mgAll_forms] at h0 ⊢
  refine ⟨fun p hp => ?_, fun e => hW e (h0.2 e)⟩
  have h1 := h0.1 p hp
  by_cases ha : 𝔇.ah p.1 p.2 = true
  · rw [if_pos ha] at h1 ⊢
    exact hA p hp ha h1
  · rw [if_neg ha] at h1 ⊢
    exact hQ p hp ha h1

end

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

/-- The item `forms m k ρ` passes over sub-protocol `b` if, wherever the invariant holds before the
step, the statement for each of its runs passes from the state before the step to the state after
it, at every witness, and so does the letter `wt` where `ρ` is "weights". -/
theorem ridesPastAt_forms_older {b : Nat} (m k : Nat) (ρ : String)
    (hk : ∀ c s mm E s',
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b c s mm E →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      (∀ v : WtF, ∀ p ∈ h.𝔇.runs m k ρ, h.𝔇.ah p.1 p.2 = true →
        formsQA (h.𝔇.N.sent m) (h.𝔇.N.group m) (h.𝔇.Rd m) p.1 p.2 s
          (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms v) →
        formsQA (h.𝔇.N.sent m) (h.𝔇.N.group m) (h.𝔇.Rd m) p.1 p.2 s'
          (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms v)) ∧
      (∀ v : WtF, ∀ p ∈ h.𝔇.runs m k ρ, ¬ h.𝔇.ah p.1 p.2 = true →
        formsQ (h.𝔇.Rd m) (h.𝔇.N.group m) p.1 p.2 s (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms v) →
        formsQ (h.𝔇.Rd m) (h.𝔇.N.group m) p.1 p.2 s' (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms v)) ∧
      (ρ = "weights" → ∀ z y y' v, h.𝔇.wt m (z, s) y v → h.𝔇.wt m (z, s') y' v)) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b
      (Item.forms m k ρ) := by
  intro c s mm E s' ps v hA hK h0
  obtain ⟨k1, k2, k3⟩ := hk c s mm E s' hA hK
  exact forms_older { h.𝔇 with decT := fun _ _ => some (Q.cells mm.st.input), cr1 := carryX } mgBase
    m k ρ mm.st.input.x.pub
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E)
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs (E.add ps)) v
    (k1 v) (k2 v)
    (fun e => k3 e mm.st.input.x.pub
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E)
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs (E.add ps)) v) h0

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.formsQ_fwd
#print axioms ProofFile.Honest.FirstThread.formsQA_fwd
#print axioms ProofFile.Honest.FirstThread.forms_older
#print axioms ProofFile.Honest.FirstThread.ridesPastAt_forms_older
