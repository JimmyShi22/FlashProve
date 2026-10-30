-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Law/ReaderAtLink24.lean: K6's READER AT A TAKE
(Honest/K6/Law/ReaderAtTake.lean) AT THE ONE WRITTEN PLACE WITH LINK 24 AND ITS MESSAGE NUMBER 2:
the six premises on the written lists come down to two (p is a written place; its link is 24): the
other four are closed facts of the code switch's authors (Honest/K2/Law/Link24Written.lean). THE
LETTERS IN NUMERALS: the switch's place is ⟨1, some 24, 2, K2⟩; the mask row begins at number 439
among the extension field's coins of its sending's count; the mask code's message length is 8192.
There is such a place. A corollary; no definition.

What it is not. ALL LIMITS OF ReaderAtTake.lean HOLD: hO IS A PREMISE, PAID BY NOBODY; NO SCRIPT IS
LAID; THE ROW IS THE SENDER's. hLend IS SHOWN AT NO BOOK THAT WE KNOW (that file's head).
The library's written plan has H.ns = 3570 (not called here): with the field below the room for free
is 2168 to 3569. Nothing on the field stretch: that the book's stretch for K6's row has this owner
and begins at 439 + the lookup's scalars is not said here (AtFullSide/K6/StretchAtSwitch.lean says
it, under a premise of its own; not imported). Closed facts by Lean's kernel lie beneath, replayed
by no independent checker. THE FULL SIZE ALONE. Nothing on soundness, on completeness or on what a
proof hides.
It defines nothing.
  exists_link24         a written place has link 24
  letters_at_link24     the place, the length 8192 and the number 439
  inside_at_link24      the field inside, at free + 1 ≤ 8192
  k6_reader_at_link24   THE MAIN STATEMENT: the field reader at message 2
CALLED: atLink24W, link24W_one, role24W, atLink24_gives (Honest/K2/Law/Link24Written.lean);
inside_at_take, k6_reader_at_take (Honest/K6/Law/ReaderAtTake.lean).
-/
import Johnson.Desc.ProofFile.Honest.K6.Law.ReaderAtTake
import Johnson.Desc.ProofFile.Honest.K2.Law.Link24Written

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open VerifiableInference.Desc (Chain Place Strs)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS At.X)
open P5T (seatsAllFull)
open ProofFile.Honest (ProverCoinCounts Coins Local Mid Prover ThrS ReaderReads Readers RowDataOf declsTo lendsPart
  lookDue)
open ProofFile.Honest.FirstThread (Script WtF lettersHead OwnMsgs)
open ProofFile.Honest.K2 (SwitchPlace switchSent switchMsgTxt lotClosingAt publicOk switchNumIn)
open ProofFile.Honest.K2.Law (placesW segsW atLink24W link24W_one role24W atLink24_gives)

/-- A written place has link 24. -/
theorem exists_link24 : ∃ p ∈ placesW, p.link = 24 := by
  cases hf : placesW.filter fun p => p.link == 24 with
  | nil =>
    have e := link24W_one
    rw [hf] at e
    exact absurd e (by decide)
  | cons p l =>
    have hm : p ∈ placesW.filter fun p => p.link == 24 := by
      rw [hf]
      exact List.mem_cons_self
    exact ⟨p, (List.mem_filter.1 hm).1, beq_iff_eq.1 (List.mem_filter.1 hm).2⟩

/-- The letters in numerals, at a written place with link 24 and its message 2. -/
theorem letters_at_link24 {p : SwitchPlace} (hp : p ∈ placesW) (hlk : p.link = 24) :
    p.place = ⟨1, some 24, 2, .K2⟩ ∧ takeEll p 2 = 8192 ∧ takeBase p 2 = 439 :=
  have g := atLink24_gives (List.all_eq_true.1 atLink24W p hp) hlk
  ⟨g.1, g.2.2.2.1, g.2.2.2.2⟩

section At24

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
  (Dd : RowDataOf ProofFile.Inst) (readers : Local W₀ Rc ProofFile.Inst Tr → Readers)
  (lay : OnBytes.Params.ReqLayout) {p : SwitchPlace} (N fx free : Nat)

include h in
/-- **inside**, at message 2 of the written place with link 24. -/
theorem inside_at_link24 (hp : p ∈ placesW) (hlk : p.link = 24) (hf₁ : free + 1 ≤ 8192) :
    ∀ ν, ν < free → takeBase p 2 + ν < (takeDue p).e := by
  have g := atLink24_gives (List.all_eq_true.1 atLink24W p hp) hlk
  exact inside_at_take h hp (by rw [g.2.1]; decide) (by rw [g.2.1]; decide)
    (by rw [g.2.2.1]; decide) (by rw [(letters_at_link24 hp hlk).2.1]; exact hf₁)

/-- **K6's READER AT MESSAGE 2 OF THE SWITCH INTO LINK 24.** CONDITIONAL: on hO, which is not
paid, on the public test hLend, which is shown at no book that we know, and on public premises. -/
theorem k6_reader_at_link24 (hp : p ∈ placesW) (hlk : p.link = 24)
    (hLend : lendsPart Bk (Bk.rowsOf 0) (lookDue Bk 0) ⟨p.place, 0⟩ (takePart p) = true)
    (hN : N ≤ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.ahead ++
      declsTo (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs 341).length)
    (hf₁ : free + 1 ≤ 8192) (hf₂ : free + 1 ≤ (At.X Zp).H.ns)
    (hv : publicOk Dd lay p (segsW.take p.link) w.x = true)
    (hO : OwnMsgs Q (fun v => v = w ∧ Vd v) N (switchNumIn seatsAllFull 24 2) fx
      (switchMsgTxt 0 Dd readers (lotClosingAt lay segsW) p 2)) :
    ReaderReads (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341)
      (fun s : S => s.fork?) (fun _ _ v u ν => rd ((cutAtHead h Q carryX v u).2 ν)) rd
      (fun k _ _ ν => rowFromCoin (takeBase p 2)
        (ownByCut 0 (Nat.zero_le 1) ⟨p.place, 0⟩ (takeDue p) (covers_of_lends hLend) k) ν)
      (fun ν => ν < free ∧ ν < (At.X Zp).H.ns) := by
  have g := atLink24_gives (List.all_eq_true.1 atLink24W p hp) hlk
  exact k6_reader_at_take h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said Dd readers lay N fx free
    hp hlk (by rw [g.2.1]; decide) (by rw [g.2.1]; decide) (by rw [g.2.2.1]; decide) role24W hLend
    hN (by rw [(letters_at_link24 hp hlk).2.1]; exact hf₁) hf₂ hv hO

end At24

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.exists_link24
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.letters_at_link24
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.inside_at_link24
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_reader_at_link24
