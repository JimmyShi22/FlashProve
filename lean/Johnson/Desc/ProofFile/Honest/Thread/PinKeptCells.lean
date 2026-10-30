-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/PinKeptCells.lean: the item `pinKept m` of the first chain's
invariant passes over the sub-protocols of the kinds K7 and K9. These are two of the cells of the
table `rideOk` (RideOk.lean). `ridesPastAt_pinKept_older` (PinForward.lean) asks that a message's
first sample row (`rowAt₀`, Ans.lean), where there is one before the step, is the same after it.
Here that is read off the clauses of `keeps` of the two kinds. The items `pinI` and `pin m t` ask
the same of `keeps`, so items 1 and 3 below serve them too. No definition.

  1  `k7KeepsAt_row`, `shutKeeps_row`, `rest9_row`, `eqKeeps_row`   on two states: under K7's
     clause, under K9's clause at "the segment is shut", where `rest9` is the same at every choice
     of its three arguments (K9's batching: `bat_rest9_at`, Law/NoHouse/BackLeaves.lean), and under
     K9's clause at "the one equation", `rowAt₀` is the same at every message
  2  `k9_numbers`, `k7_number`   two tests without a free variable on the written list of places
     `P5J.At.ps`, each evaluated by the kernel (`decide +kernel`), each with a control that fails: a
     place of the kind K9 stands at `14 * l + IM.nAt l + 2`, `+ 4` or `+ 6` for some `l < 25`; a
     place of the kind K7 stands at 338. `k9_number_of`, `k7_number_of`: the two as sentences
  3  `head_older_k7`, `head_older_k9`   at the invariant: the hypothesis of
     `ridesPastAt_pinKept_older`, `ridesPastAt_pinI_older` and `ridesPastAt_pin_older` at a place of
     the kind
  4  `pinKept_cell_k7`, `pinKept_cell_k9`   **the two cells**

The lemmas of 3 and 4 are stated at `keeps := kpBy f` for every `f` whose arms at K7 and K9 are
`K7KeepsAt G` and `k9KeepsAt cF Zp`. `fHead` (FHead.lean) is such an `f`. `head_ridesPastAtS_mono`
(KeepsMono.lean) carries them to a stronger `keeps`.

`eqKeeps_row` is the library's `door_both` (Johnson/Desc/First/Link/Law/DoorBlind.lean) at the
reader "the message's sample rows", which does not read a message's mask ledger.

Limits.
  * Nothing shows that a clause of `keeps` holds at any step.
  * Items 2 to 4: full size only. Items 3 and 4: under the library's `AtMgA` at the hash function
    `secondHashFunction`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.PinForwardKinds
import Johnson.Desc.ProofFile.Honest.Thread.WoClose
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.BackStays
import Johnson.Desc.ProofFile.Honest.K7.KeepsAt
import Johnson.Desc.First.Link.Law.DoorBlind
import Johnson.Desc.First.Link.Law.RbRuns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (S Item)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.LinkJoin (rest9 door_both part_reads)
open ProofFile.Honest.K9 (EqKeeps ShutKeeps k9KeepsAt)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-! ## 1 On two states -/

/-- K7's sub-protocol adds one group to the statement and changes no message. -/
theorem k7KeepsAt_row {G : ProofFile.Ground} {p : Place} {s s' : S} (k : K7KeepsAt G p s s') (o : Nat) :
    rowAt₀ s'.st o = rowAt₀ s.st o := by
  rw [k.2.st]
  rfl

/-- "The segment is shut" leaves the statement. -/
theorem shutKeeps_row {s s' : S} (k : ShutKeeps s s') (o : Nat) :
    rowAt₀ s'.st o = rowAt₀ s.st o := by
  rw [(shutKeeps_four k).1]

/-- `rest9` contains the statement. -/
theorem rest9_row {s s' : S} (k : ∀ L₀ F₀ t₀, rest9 L₀ F₀ t₀ s' = rest9 L₀ F₀ t₀ s) (o : Nat) :
    rowAt₀ s'.st o = rowAt₀ s.st o := by
  have e := congrArg (fun z : S => z.st) (k { check := s.check } {} {})
  have e' : s'.st = s.st := e
  rw [e']

/-- "The one equation" takes mask entries and adds a row to a group. Neither changes a message's
sample rows. -/
theorem eqKeeps_row {s s' : S} (k : EqKeeps s s') (o : Nat) :
    rowAt₀ s'.st o = rowAt₀ s.st o := by
  obtain ⟨a, out, ha, hdoor, rfl⟩ := k.laid
  obtain ⟨-, hst⟩ := part_reads s a ha
  have e := (door_both (f := fun x : OnBytes.Oracle => x.sampleRows) (fun _ _ => rfl) _ _ _ _ _ _
    hdoor).1.2 o
  rw [hst] at e
  show rowAt₀ out.d.st o = rowAt₀ s.st o
  exact rowAt₀_same e

/-! ## 2 Where the places of the two kinds stand -/

set_option maxRecDepth 1000000 in
/-- In the written list a place of the kind K9 stands at one of three numbers of a segment. -/
theorem k9_numbers :
    ((List.range 358).all fun b => (P5J.At.ps[b]?).all fun p =>
      !(p.kind == KindName.K9) || (List.range 25).any fun l =>
        b == 14 * l + IM.nAt l + 2 || b == 14 * l + IM.nAt l + 4 ||
          b == 14 * l + IM.nAt l + 6) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with the third number left out the same test fails. -/
theorem k9_numbers_control :
    ((List.range 358).all fun b => (P5J.At.ps[b]?).all fun p =>
      !(p.kind == KindName.K9) || (List.range 25).any fun l =>
        b == 14 * l + IM.nAt l + 2 || b == 14 * l + IM.nAt l + 4) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- In the written list a place of the kind K7 stands at 338. -/
theorem k7_number :
    ((List.range 358).all fun b => (P5J.At.ps[b]?).all fun p =>
      !(p.kind == KindName.K7) || b == 338) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: at 337 in the place of 338 the same test fails. -/
theorem k7_number_control :
    ((List.range 358).all fun b => (P5J.At.ps[b]?).all fun p =>
      !(p.kind == KindName.K7) || b == 337) = false := by
  decide +kernel

/-- The first test as a sentence. -/
theorem k9_number_of {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K9) :
    ∃ l, l < 25 ∧ (b = 14 * l + IM.nAt l + 2 ∨ b = 14 * l + IM.nAt l + 4 ∨
      b = 14 * l + IM.nAt l + 6) := by
  have t := List.all_eq_true.1 k9_numbers b (List.mem_range.2 hb)
  rw [hp] at t
  have t' : (!(p.kind == KindName.K9) || (List.range 25).any fun l =>
      b == 14 * l + IM.nAt l + 2 || b == 14 * l + IM.nAt l + 4 ||
        b == 14 * l + IM.nAt l + 6) = true := t
  rw [hk] at t'
  have t2 : ((List.range 25).any fun l =>
      b == 14 * l + IM.nAt l + 2 || b == 14 * l + IM.nAt l + 4 ||
        b == 14 * l + IM.nAt l + 6) = true := t'
  obtain ⟨l, hl, e⟩ := List.any_eq_true.1 t2
  refine ⟨l, List.mem_range.1 hl, ?_⟩
  rcases Bool.or_eq_true_iff.1 e with e | e
  · rcases Bool.or_eq_true_iff.1 e with e | e
    · exact Or.inl (eq_of_beq e)
    · exact Or.inr (Or.inl (eq_of_beq e))
  · exact Or.inr (Or.inr (eq_of_beq e))

/-- The second test as a sentence. -/
theorem k7_number_of {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K7) : b = 338 := by
  have t := List.all_eq_true.1 k7_number b (List.mem_range.2 hb)
  rw [hp] at t
  have t' : (!(p.kind == KindName.K7) || b == 338) = true := t
  rw [hk] at t'
  have t2 : (b == 338) = true := t'
  exact eq_of_beq t2

/-! ## 3 and 4 At the invariant -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)

/-- At a place of the kind K7 a first sample row that is there stays. -/
theorem head_older_k7 {G : ProofFile.Ground} (hf7 : f KindName.K7 = K7KeepsAt G) {b : Nat} {p : Place}
    (hp : P5J.At.ps[b]? = some p) (hk : p.kind = KindName.K7) :
    ∀ k s mm E s',
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread b k s mm E →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.keeps b s s' →
      ∀ o q, rowAt₀ s.st o = some q → rowAt₀ s'.st o = some q :=
  head_older_same h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w
    (head_hk h H Q test carryX item n₁ n₂ b₀ Vd Rd f w hp hk fun s s' hc o => by
      rw [hf7] at hc
      exact k7KeepsAt_row hc o)

/-- At a place of the kind K9 a first sample row that is there stays. -/
theorem head_older_k9 (hf9 : f KindName.K9 = k9KeepsAt cF Zp) {b : Nat} {p : Place} (hb : b < 358)
    (hp : P5J.At.ps[b]? = some p) (hk : p.kind = KindName.K9) :
    ∀ k s mm E s',
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread b k s mm E →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.keeps b s s' →
      ∀ o q, rowAt₀ s.st o = some q → rowAt₀ s'.st o = some q := by
  obtain ⟨l, hl, rfl | rfl | rfl⟩ := k9_number_of hb hp hk
  · exact head_older_same h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w
      fun s s' hK => rest9_row
        (head_keeps_bat h H Q test carryX item n₁ n₂ b₀ Vd Rd f w hf9 hl s s' hK)
  · exact head_older_same h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w
      fun s s' hK => eqKeeps_row
        (head_keeps_eq h H Q test carryX item n₁ n₂ b₀ Vd Rd f w hf9 hl s s' hK)
  · exact head_older_same h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w
      fun s s' hK => shutKeeps_row
        (head_keeps_shut h H Q test carryX item n₁ n₂ b₀ Vd Rd f w hf9 hl s s' hK)

/-- **The cell of `pinKept m` at the kind K7.** -/
theorem pinKept_cell_k7 {G : ProofFile.Ground} (hf7 : f KindName.K7 = K7KeepsAt G) {b : Nat} {p : Place}
    (hp : P5J.At.ps[b]? = some p) (hk : p.kind = KindName.K7) (m : Nat) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread b
      (Item.pinKept m) :=
  ridesPastAt_pinKept_older h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w m
    (head_older_k7 h H Q test carryX item n₁ n₂ b₀ Vd Rd f w hf7 hp hk)

/-- **The cell of `pinKept m` at the kind K9.** -/
theorem pinKept_cell_k9 (hf9 : f KindName.K9 = k9KeepsAt cF Zp) {b : Nat} {p : Place}
    (hb : b < 358) (hp : P5J.At.ps[b]? = some p) (hk : p.kind = KindName.K9) (m : Nat) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread b
      (Item.pinKept m) :=
  ridesPastAt_pinKept_older h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w m
    (head_older_k9 h H Q test carryX item n₁ n₂ b₀ Vd Rd f w hf9 hb hp hk)

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.k7KeepsAt_row
#print axioms ProofFile.Honest.FirstThread.shutKeeps_row
#print axioms ProofFile.Honest.FirstThread.rest9_row
#print axioms ProofFile.Honest.FirstThread.eqKeeps_row
#print axioms ProofFile.Honest.FirstThread.k9_numbers
#print axioms ProofFile.Honest.FirstThread.k9_numbers_control
#print axioms ProofFile.Honest.FirstThread.k7_number
#print axioms ProofFile.Honest.FirstThread.k7_number_control
#print axioms ProofFile.Honest.FirstThread.k9_number_of
#print axioms ProofFile.Honest.FirstThread.k7_number_of
#print axioms ProofFile.Honest.FirstThread.head_older_k7
#print axioms ProofFile.Honest.FirstThread.head_older_k9
#print axioms ProofFile.Honest.FirstThread.pinKept_cell_k7
#print axioms ProofFile.Honest.FirstThread.pinKept_cell_k9
