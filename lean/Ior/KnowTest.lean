-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/KnowTest.lean: the knowledge clause bites: a toy reduction on which round-by-round knowledge
soundness (Ior/Know.lean) holds with the right extractor and fails with a wrong one, although every
statement is in the language.

Definitions, statements (`Iop.KnowTest.Spec`) and proofs.
The toy: one round. The prover sends one bit, the verifier sends a message from a finite set (which
nobody reads) and accepts if and only if the bit is 1. Statements carry nothing. A witness of the
input statement is a bit, and it is valid if and only if it is 1; so every input statement has a
valid witness. Every witness of the output statement is valid. The bit as a plain message
(`plainBit`) and the bit as an oracle of one symbol (`oracleBit`) are its two instances.

Main names, each for both instances and for every finite non-empty set C of verifier messages:
  `reads`: with the extractor that reads the bit from the transcript, `Know` holds with error 0.
  `const_fails`: with the extractor that is constantly 0, `Know` holds with error e if and only if e
    is at least the number of values of the verifier message, that is: only where the bound says
    nothing (a count of values of one message is never above their number). For every error that,
    read as a probability, is below 1, it fails.
  `lit_fails`: the same for the form with a knowledge state function (`HasRbrKnowledge`), through
    `Spec.know_iff_literal` (Ior/KnowLit.lean).
  `sound_free`: plain round-by-round soundness for the languages of the two relations holds with
    error 0, and for free: no statement is outside the input language.
So `Know` with a given extractor is not a consequence of soundness: the extractor that a theorem
names matters.

Limits: the toy tells one extractor from another; it does not separate `Know` from soundness over
all extractors: for every sound reduction `Know` holds, with the same errors, with the extractor
"some witness of the input statement, by choice" (Ior/KnowBlind.lean: `know_by_choice`, for a
non-empty type of input witnesses).
"Fails for every error list" would be false, here and for every reduction with at least one round:
an error list whose entries reach the numbers of values of the verifier messages makes `Doomed` true
of any target.
The extractor that is constantly 1 also passes the toy (it needs no transcript): the toy separates
right from wrong extractors, not transcript-reading from blind ones.
Terms: lean/GLOSSARY.md.
-/
import Ior.KnowLit

set_option autoImplicit false

namespace Iop
namespace KnowTest
open Prob Reduction

/-- The toy for a round r and a reading of one bit from the prover message. -/
def toy (r : Round) (bit : r.Msg → Bool) : Reduction Unit Unit where
  shape := [r]
  out := fun _ (τ : r.Msg × r.Chal × Unit) => if bit τ.1 = true then some () else none

/-- A witness of the input statement is valid if it is 1. -/
def RA : Unit → Bool → Prop := fun _ w => w = true
/-- Every witness of the output statement is valid. -/
def RB : Unit → Unit → Prop := fun _ _ => True

/-- The right extractor: it reads the bit. -/
def extRead (r : Round) (bit : r.Msg → Bool) : Unit → Tr (toy r bit).shape → Unit → Bool :=
  fun _ (τ : r.Msg × r.Chal × Unit) _ => bit τ.1
/-- A wrong extractor: constantly 0. -/
def extZero (r : Round) (bit : r.Msg → Bool) : Unit → Tr (toy r bit).shape → Unit → Bool :=
  fun _ _ _ => false

theorem toy_reads (r : Round) (bit : r.Msg → Bool) :
    (toy r bit).Know (fun _ => True) RA RB (extRead r bit) (Err.zero _) := by
  intro a _
  refine Doomed.of_forall _ _ fun (τ : r.Msg × r.Chal × Unit) b w hb _ => ?_
  show bit τ.1 = true
  by_contra hn
  have hb' : (if bit τ.1 = true then some () else none) = some b := hb
  rw [if_neg hn] at hb'
  exact absurd hb' (by simp)

theorem toy_const (r : Round) (bit : r.Msg → Bool) (h1 : ∃ m, bit m = true) (e : ℕ) :
    (toy r bit).Know (fun _ => True) RA RB (extZero r bit) (e, ()) ↔ Fintype.card r.Chal ≤ e := by
  constructor
  · intro h
    obtain ⟨m, hm⟩ := h1
    have h2 : cnt (fun c : r.Chal =>
          ¬ ∀ (b : Unit) (w : Unit),
            (toy r bit).out () (m, c, ()) = some b → RB b w → RA () false) ≤ e := h () trivial m
    refine le_trans (le_of_eq cnt_true.symm) (le_trans (cnt_mono fun c _ hall => ?_) h2)
    have h3 : false = true := hall () () (if_pos hm) trivial
    exact absurd h3 (by simp)
  · intro h a _ m
    exact le_trans (cnt_le_card _) h

theorem toy_lit (r : Round) (bit : r.Msg → Bool) (h1 : ∃ m, bit m = true) (e : ℕ) :
    (toy r bit).HasRbrKnowledge (fun _ => True) (onLeft (WB := Unit) RA) (onRight (WA := Bool) RB)
      (fun a => RExt.ofFull (toy r bit).shape (extZero r bit a)) (e, ()) ↔
    Fintype.card r.Chal ≤ e :=
  (know_iff_literal Unit Unit Bool Unit (toy r bit) (fun _ => True) RA RB (extZero r bit)
      (e, ()) (List.cons_ne_nil _ _)).symm.trans
    (toy_const r bit h1 e)

theorem toy_sound (r : Round) (bit : r.Msg → Bool) :
    (∀ a, ∃ w, RA a w) ∧
    (toy r bit).Sound (fun a => ∃ w, RA a w) (fun b => ∃ w, RB b w) (Err.zero _) :=
  ⟨fun _ => ⟨true, rfl⟩, fun _ ha => absurd ⟨true, rfl⟩ ha⟩

/-- The bit as a plain message; verifier messages from C. -/
def plainBit (C : Type) [Fintype C] [Nonempty C] : Round where
  Orc := Unit
  Pos := Empty
  Sym := fun _ => Unit
  rd := fun _ _ => ()
  Plain := Bool
  Chal := C
  dOrc := ()
  dPlain := false

/-- The bit as an oracle with one position; verifier messages from C. -/
def oracleBit (C : Type) [Fintype C] [Nonempty C] : Round where
  Orc := Bool
  Pos := Unit
  Sym := fun _ => Bool
  rd := fun o _ => o
  Plain := Unit
  Chal := C
  dOrc := false
  dPlain := ()

def plainToy (C : Type) [Fintype C] [Nonempty C] : Reduction Unit Unit :=
  toy (plainBit C) fun m => m.2
def oracleToy (C : Type) [Fintype C] [Nonempty C] : Reduction Unit Unit :=
  toy (oracleBit C) fun m => (oracleBit C).rd m.1 ()

namespace Spec

/-- With the extractor that reads the bit: error 0. -/
def reads : Prop :=
  ∀ (C : Type) [Fintype C] [Nonempty C],
    (plainToy C).Know (fun _ => True) RA RB (extRead _ _) (Err.zero _) ∧
    (oracleToy C).Know (fun _ => True) RA RB (extRead _ _) (Err.zero _)

/-- With the extractor that is constantly 0: only with an error that is at least the number of
values of the verifier message. -/
def const_fails : Prop :=
  ∀ (C : Type) [Fintype C] [Nonempty C] (e : ℕ),
    ((plainToy C).Know (fun _ => True) RA RB (extZero _ _) (e, ()) ↔ Fintype.card C ≤ e) ∧
    ((oracleToy C).Know (fun _ => True) RA RB (extZero _ _) (e, ()) ↔ Fintype.card C ≤ e)

/-- The same for the form with a knowledge state function (`HasRbrKnowledge`). -/
def lit_fails : Prop :=
  ∀ (C : Type) [Fintype C] [Nonempty C] (e : ℕ),
    ((plainToy C).HasRbrKnowledge (fun _ => True) (onLeft (WB := Unit) RA) (onRight (WA := Bool) RB)
        (fun a => RExt.ofFull (plainToy C).shape (extZero _ _ a)) (e, ()) ↔
      Fintype.card C ≤ e) ∧
    ((oracleToy C).HasRbrKnowledge (fun _ => True) (onLeft (WB := Unit) RA)
        (onRight (WA := Bool) RB)
        (fun a => RExt.ofFull (oracleToy C).shape (extZero _ _ a)) (e, ()) ↔
      Fintype.card C ≤ e)

/-- States: every input statement has a valid witness, and soundness for the languages holds with
error 0. -/
def sound_free : Prop :=
  ∀ (C : Type) [Fintype C] [Nonempty C],
    (∀ a, ∃ w, RA a w) ∧
    (plainToy C).Sound (fun a => ∃ w, RA a w) (fun b => ∃ w, RB b w) (Err.zero _) ∧
    (oracleToy C).Sound (fun a => ∃ w, RA a w) (fun b => ∃ w, RB b w) (Err.zero _)

end Spec

theorem reads : Spec.reads := fun _ _ _ => ⟨toy_reads _ _, toy_reads _ _⟩
theorem const_fails : Spec.const_fails := fun _ _ _ e =>
  ⟨toy_const _ _ ⟨((), true), rfl⟩ e, toy_const _ _ ⟨(true, ()), rfl⟩ e⟩
theorem lit_fails : Spec.lit_fails := fun _ _ _ e =>
  ⟨toy_lit _ _ ⟨((), true), rfl⟩ e, toy_lit _ _ ⟨(true, ()), rfl⟩ e⟩
theorem sound_free : Spec.sound_free := fun _ _ _ =>
  ⟨fun _ => ⟨true, rfl⟩, (toy_sound _ _).2, (toy_sound _ _).2⟩

end KnowTest
end Iop
