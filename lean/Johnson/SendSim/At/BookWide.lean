-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/BookWide.lean: the wider condition on the book at all addresses (BookClearAny),
and the statements that under it every Seated side has the field fresh (with the bound budAt) and
Good at predicates A and B that never hold, so that plays and acc hold vacuously. It claims no
property of the protocol: not hiding, not zero knowledge.
Terms: Johnson/SendSim/At/Sim.lean; for the book, Johnson/SendSim/At/Fresh.lean. Limits of the
folder: Johnson/SendSim/Defs.lean.

What this file has.
  BookClearAny          Every entry of the owner is within the sender's number of coins
                        (WithinTakes), and every address satisfies SpenderClearAny.
  Spec.sendFreshAtWide  Every Seated side has the field fresh, with the bound budAt, at every book
                        that satisfies BookClearAny at the sender.
  Spec.goodSeatedWide   Under the same premises the side has Good, at On := True and the bound
                        budAt. Its predicates A and B never hold, so the fields plays (the row can
                        be played) and acc (the verifier accepts) hold vacuously.
  sendFreshAtWide_of_each   Proved here: Spec.sendFreshAtPWide implies Spec.sendFreshAtWide. The
                        proof exchanges two quantifiers.
  goodSeatedWide_of     Proved here: Spec.sendExactAt and Spec.sendFreshAtWide imply
                        Spec.goodSeatedWide.
  bookClearAny_of_clear   Proved here: BookClear implies BookClearAny. No file uses it: it says that
                        the condition is indeed wider.
  bookClearAnyB_iff     Proved here: the executable test bookClearAnyB accepts exactly if
                        BookClearAny holds.
The two under Spec are statements only; proved as sendFreshAtWide and goodSeatedWide in
Johnson/SendSim/Seat/HandedWideProofs.lean.

Limits.
The two statements are all or nothing: one address that does not satisfy SpenderClearAny makes them
vacuous for every spender of that owner. Each statement speaks of one owner of coins. Where their
premises are met is said in the Limits of Johnson/SendSim/Seat/HandedWideProofs.lean: where
BookClearAny is proved: the table of premises in Johnson/SendSim/Defs.lean, "the book is clear";
Seated is proved only at the places of result (3) of Johnson/SendSim/Defs.lean.
The implications have named propositions as premises, which this file does not prove, so it proves
no equation between distributions by itself.

How it fits. SpenderClearAny and Spec.sendFreshAtPWide are in Johnson/SendSim/At/FreshWide.lean,
Spec.sendExactAt in Johnson/SendSim/At/Sim.lean, bookClearAnyB in Johnson/SendSim/At/WideTest.lean.
sendFreshAtWide is the form of fresh that Spec.fieldsAtLots (Johnson/SendSim/Seat/AtDescLots.lean)
rests on.

Notes: why the wider condition. Spec.sendFreshAt (Johnson/SendSim/At/Fresh.lean) takes BookClear. At
an owner one of whose spenders takes the coefficients of a table of two rows that is sent along,
BookClear fails (by inspection, not proved). The statement is then vacuous for every spender, and
Good cannot be derived from it at that owner's place. Spec.sendFreshAtPWide has content there, one
address at a time.
-/
import Johnson.SendSim.At.FreshWide
import Johnson.SendSim.At.GoodOf

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc

variable {S Cl V W X Pb : Type}

/-- The wider condition on the book at an owner o: every entry of o is within the sender's number of
coins (WithinTakes), and every address satisfies SpenderClearAny. -/
def BookClearAny (P : K1.Par) (ride : Nat → Option Ride) (Bk : ProverCoinCounts) (ord : List Place)
    (o : Addr) : Prop :=
  WithinTakes P ride Bk o ∧ ∀ p, SpenderClearAny P ride Bk ord o p

/-- BookClear implies BookClearAny. -/
theorem bookClearAny_of_clear {P : K1.Par} {ride : Nat → Option Ride} {Bk : ProverCoinCounts}
    {ord : List Place} {o : Addr} (h : BookClear P ride Bk ord o) : BookClearAny P ride Bk ord o :=
  ⟨h.1, fun p => clearAny_of_clear (h.2 p)⟩

/-- States that a Seated side has the field fresh of Good, with the bound budAt, at every book that
satisfies BookClearAny at the sender. Statement only; proved as sendFreshAtWide in
Johnson/SendSim/Seat/HandedWideProofs.lean. -/
def Spec.sendFreshAtWide : Prop :=
  ∀ (S Cl V W X Pb : Type) (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : SendJob W X) (Bk : ProverCoinCounts)
    (ord : List Place), Seated σ J → BookClearAny J.P J.ride Bk ord ⟨σ.block.place, 0⟩ →
    FreshAt φ σ Bk ord fun _ _ asks => budAt J.P asks

/-- States that a Seated side has the structure Good at every book that satisfies BookClearAny at
the sender, at On := True, the bound budAt and predicates A and B that never hold, so that plays and
acc hold vacuously. Statement only; proved as goodSeatedWide in
Johnson/SendSim/Seat/HandedWideProofs.lean.
pre is tied to no description; of Good's fields exact alone reads it, and at each pre that field
says no more than ExactAt. -/
def Spec.goodSeatedWide : Prop :=
  ∀ (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (S Cl V W X Pb : Type) (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : SendJob W X) (Bk : ProverCoinCounts)
    (ord : List Place) (chain firstTree : Nat), Seated σ J →
    BookClearAny J.P J.ride Bk ord ⟨σ.block.place, 0⟩ →
    Good pre φ σ Bk ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False)
      (fun _ _ _ _ => True) fun _ _ asks => budAt J.P asks

/-- Spec.sendFreshAtPWide implies Spec.sendFreshAtWide, by exchanging two quantifiers. The premise
is proved as sendFreshAtPWide in Johnson/SendSim/At/FreshWideProofs.lean. -/
theorem sendFreshAtWide_of_each (H : Spec.sendFreshAtPWide) : Spec.sendFreshAtWide :=
  fun S Cl V W X Pb φ σ J Bk ord h hB => (freshAt_iff_each φ σ Bk ord _).2 fun p =>
    H S Cl V W X Pb φ σ J Bk ord p h (withinAt_of_takes hB.1 ord p) (hB.2 p)

/-- Spec.sendExactAt and Spec.sendFreshAtWide imply Spec.goodSeatedWide. The premises are proved as
sendExactAt in Johnson/SendSim/At/ExactAt.lean and as sendFreshAtWide in
Johnson/SendSim/Seat/HandedWideProofs.lean. -/
theorem goodSeatedWide_of (He : Spec.sendExactAt) (Hr : Spec.sendFreshAtWide) :
    Spec.goodSeatedWide :=
  fun _ S Cl V W X Pb φ σ J Bk ord chain firstTree h hB =>
    good_of_fields h.fits (He S Cl V W X Pb φ σ J chain firstTree h)
      (Hr S Cl V W X Pb φ σ J Bk ord h hB)

variable (P : K1.Par) (ride : Nat → Option Ride)

/-- bookClearAnyB accepts exactly if BookClearAny holds. -/
theorem bookClearAnyB_iff {Bk : ProverCoinCounts} {ord : List Place} {o : Addr} :
    bookClearAnyB P ride Bk ord o = true ↔ BookClearAny P ride Bk ord o := by
  constructor
  · intro h
    simp only [bookClearAnyB, Bool.and_eq_true] at h
    refine ⟨within_of_test P ride h.1, fun p => ?_⟩
    by_cases hp : p ∈ Bk.ahead.map (·.spender)
    · exact (spenderClearAnyB_iff P ride).1 (List.all_eq_true.1 h.2 p hp)
    · exact Or.inl (spentBy_nil_of_not hp)
  · intro h
    simp only [bookClearAnyB, Bool.and_eq_true]
    exact ⟨test_of_within P ride h.1, List.all_eq_true.2 fun p _ =>
      (spenderClearAnyB_iff P ride).2 (h.2 p)⟩

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.sendFreshAtWide_of_each
#print axioms OnBytes.SendSim.At.goodSeatedWide_of
#print axioms OnBytes.SendSim.At.bookClearAnyB_iff
#print axioms OnBytes.SendSim.At.BookClearAny
#print axioms OnBytes.SendSim.At.bookClearAny_of_clear
#print axioms OnBytes.SendSim.At.Spec.sendFreshAtWide
#print axioms OnBytes.SendSim.At.Spec.goodSeatedWide
