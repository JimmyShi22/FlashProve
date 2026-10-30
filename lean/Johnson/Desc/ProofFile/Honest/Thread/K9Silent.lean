-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/K9Silent.lean: at the 75 sub-protocols of the kind K9 of the
first chain at the full size, the condition `PlaysS` (Honest/Thread/PaysS.lean) holds at the
invariant of `lettersHead` for a prover that has no side at a place of that kind. No definition.

Why it holds. In the library's K9 the prover sends nothing. The batching has one round, in which one
element is drawn and no message, root or answer is declared. The two other sub-protocols of the kind
have no round. Where the prover's list has no side at a place, the frame's `chainSteps` lays a step
without a move for each round, and `play` returns with empty messages. That is the lemma
`playsS_bare` (Honest/Law/NoHouse/Bare.lean), by which the gathering proves `PlaysS` at the
sub-protocols of the kind `frame`. This file shows its hypothesis `Bare` at the 75 numbers.

  1  `k9Numbers_full`, `k9Numbers_control`, `k9_kind_at`   a closed test by Lean's kernel on the
     library's written list of places: the numbers 14 l + nAt l + j, for l below 25 and j = 2, 4, 6,
     have a place of the kind K9. The negative test: with 5 for 4 the test fails
  2  `bare_one_plain`   a sub-protocol with one round that declares no root, no stored table and no
     opening, and with no side at its place, is `Bare`, if it is `shaped`. General
  3  `playsS_k9_silent`   **`PlaysS` at the 75 numbers**, at all arguments `Rd`, `Kp` and the
     others of `lettersHead`, and every `Said`

Called: the library's `LPFK9.k09_sits` (Johnson/LPFK9R/Sits.lean): which sub-protocols stand at the
three numbers of a segment, and their rounds. `IM.hear_len_at` (Johnson/IMR/FrameSeat.lean).
`planOk_all` (Honest/Thread/File.lean) and `shaped_parts` (Honest/Law/Data.lean): as many lists of
oracle messages as rounds, each as long as its round's number of roots. `noHalf_of_kind`,
`bare_of_quiet` (Honest/Law/NoHouse/Fill.lean).

Limits.
  * `hno` (no side at a place of the kind K9) and a hypothesis that the prover's list has a side at
    such a place exclude each other at one prover. Lemmas of other authors on K9 that take such a
    hypothesis cannot be called at a prover at which this lemma is called.
  * "It plays" is not "it is accepted". `PlaysS` does not say that a side stands at a place, nor
    that the sub-protocol's step accepts what was played. A prover that sends nothing plays here.
  * Nothing is said on `ExchangeS` at these numbers.
  * At j = 4 and j = 6 the sub-protocol has no round. There `hno` may be more than is needed: this
    file does not try it without.
  * Nothing here shows that the invariant holds at any state of a run.
  * Full size only, under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.HeadForm
import Johnson.Desc.ProofFile.Honest.Thread.FirstSits
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.Fill
import Johnson.Desc.ProofFile.Honest.Law.Data
import Johnson.LPFK9R.Sits
import Johnson.IMR.FrameSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName Block)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-! ## 1 The closed test -/

set_option maxRecDepth 1000000 in
/-- The numbers 14 l + nAt l + 2, + 4 and + 6 have a place of the kind K9. -/
theorem k9Numbers_full : ((List.range 25).all fun l => [2, 4, 6].all fun j =>
    (P5J.At.ps[14 * l + IM.nAt l + j]?).all fun p => p.kind == KindName.K9) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: with 5 in the place of 4 the same test fails. -/
theorem k9Numbers_control : ((List.range 25).all fun l => [2, 5, 6].all fun j =>
    (P5J.At.ps[14 * l + IM.nAt l + j]?).all fun p => p.kind == KindName.K9) = false := by
  decide +kernel

/-- The test at a number. -/
theorem k9_kind_at {l : Nat} (hl : l < 25) {j : Nat} (hj : j = 2 ∨ j = 4 ∨ j = 6) {p : Place}
    (hp : P5J.At.ps[14 * l + IM.nAt l + j]? = some p) : p.kind = KindName.K9 := by
  have a : ([2, 4, 6].all fun j =>
      (P5J.At.ps[14 * l + IM.nAt l + j]?).all fun p => p.kind == KindName.K9) = true :=
    List.all_eq_true.1 k9Numbers_full l (List.mem_range.2 hl)
  have c : ((P5J.At.ps[14 * l + IM.nAt l + j]?).all fun p => p.kind == KindName.K9) = true :=
    List.all_eq_true.1 a j (by rcases hj with rfl | rfl | rfl <;> simp)
  rw [hp] at c
  exact eq_of_beq (show (p.kind == KindName.K9) = true from c)

/-! ## 2 One plain round -/

/-- One round without a root, a stored table or an opening; no side at the place. -/
theorem bare_one_plain {S Cl V W X : Type} {hs : List (Placed V W X)} {b : Block S Cl}
    {r : Fmt.DeclaredRound} (hr : b.rounds = [r])
    (h0 : r.entry.roots = 0 ∧ r.stored = [] ∧ r.opens = []) (hsh : b.shaped = true)
    (hn : (hs.find? fun g => g.place == b.place) = none) : Bare hs b := by
  obtain ⟨e1, e2⟩ := shaped_parts hsh
  rw [hr] at e1 e2
  have e1' : b.oracles.length = 1 := e1
  obtain ⟨o, ho⟩ := List.length_eq_one_iff.1 e1'
  rw [ho] at e2
  have e3 : o.length = r.entry.roots := e2 (r, o) (by simp)
  rw [h0.1] at e3
  obtain rfl := List.eq_nil_of_length_eq_zero e3
  refine ⟨hn, ?_, ?_⟩
  · simp only [ho, hr, List.map_cons, List.map_nil]
  · intro r' hr'
    rw [hr] at hr'
    obtain rfl := List.mem_singleton.1 hr'
    exact h0

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
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- **At the 75 sub-protocols of the kind K9 a prover without a side there plays.** -/
theorem playsS_k9_silent (hno : ∀ g ∈ H.first, g.place.kind ≠ KindName.K9)
    {l : Nat} (hl : l < 25) {j : Nat} (hj : j = 2 ∨ j = 4 ∨ j = 6) :
    PlaysS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (14 * l + IM.nAt l + j) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, p, Qc, -, -, St⟩ := LPFK9.k09_sits h.scope h.reads O l hl
  have hlen : Lk.hear.length = IM.nAt l := St.hear.trans (IM.hear_len_at l)
  have hnone : ∀ blk : Block TS ProofFile.Cl, cF.blocksInOrder[14 * l + IM.nAt l + j]? = some blk →
      (H.first.find? fun g => g.place == blk.place) = none := fun blk hb =>
    noHalf_of_kind fun g hg => by
      rw [k9_kind_at hl hj (head_place h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb)]
      exact hno g hg
  have hshape : ∀ blk : Block TS ProofFile.Cl, cF.blocksInOrder[14 * l + IM.nAt l + j]? = some blk →
      blk.shaped = true := fun blk hb =>
    ((planOk_all (head_planOk h)).1 blk (List.mem_of_getElem? hb)).2
  rcases hj with rfl | rfl | rfl
  · have hb : cF.blocksInOrder[14 * l + IM.nAt l + 2]? = some Lk.batchB := by
      rw [← hlen]
      exact St.flat
    exact playsS_bare (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said hb
      (bare_one_plain St.rounds ⟨rfl, rfl, rfl⟩ (hshape _ hb) (hnone _ hb))
  · obtain ⟨b₃, -, hf, hr, -⟩ := St.equation
    have hb : cF.blocksInOrder[14 * l + IM.nAt l + 4]? = some b₃ := by
      rw [← hlen]
      exact hf
    exact playsS_bare (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said hb
      (bare_of_quiet hr (shaped_parts (hshape _ hb)).1 (hnone _ hb))
  · obtain ⟨b₅, -, hf, hr, -⟩ := St.shut
    have hb : cF.blocksInOrder[14 * l + IM.nAt l + 6]? = some b₅ := by
      rw [← hlen]
      exact hf
    exact playsS_bare (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said hb
      (bare_of_quiet hr (shaped_parts (hshape _ hb)).1 (hnone _ hb))

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.k9Numbers_full
#print axioms ProofFile.Honest.FirstThread.k9Numbers_control
#print axioms ProofFile.Honest.FirstThread.k9_kind_at
#print axioms ProofFile.Honest.FirstThread.bare_one_plain
#print axioms ProofFile.Honest.FirstThread.playsS_k9_silent
