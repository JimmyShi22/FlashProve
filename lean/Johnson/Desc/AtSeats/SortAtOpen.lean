-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/SortAtOpen.lean: the premise hSortB of the kind K1's law's top (sortB XV =
true: a test on the public parameters, Johnson/Desc/K1/Law/SortAtFifty.lean) FALLS TO
THE TOP's OWN HEAD: it says no more and no less than "the output head's segment is number 24", and
that is a theorem in scope. No pin is spent. A joining of what lies. A law file; no running text
imports it.
  sort_at: at one segment l the test's clause accepts just where "l is the head's segment" and "l =
      24" agree
  sortB_iff: sortB X = true ↔ headLink X = 24
  sortB_no: so the test REJECTS at every X whose head stands elsewhere (the negative side, as a
      theorem: at the stored small set, whose head is segment 4, a run saw it reject)
  sortB_open: sortB Z.p.X = true from hS : VerifierAndGoals.InScope P = true, hR : VerifierAndGoals.readFiles P = .ok
      pp and O : IM.Open …: by headLink_open (Johnson/Desc/K1/Law/ReadersPaid.lean) and
      Open.W (Bs.G₀.W = Z.p.X)
  sortB_ground: the like at Bs.G₀.W

What is not claimed. That hS, hR and O have a member. That the letter XV of a top is Z.p.X (at
the closed constant P5J.mgAtAll it is, by its definition). Nothing on soundness.

-/
import Johnson.Desc.K1.Law.SortAtFifty
import Johnson.Desc.K1.Law.ReadersPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look (k3SortAt)
open VerifiableInference.OnPublicFiles (headLink)
open ProofFile (Cl)

/-- At one segment: the clause accepts just where the two agree. -/
theorem sort_at (X : OnBytes.Model.Verify.Public) (l : ℕ) :
    (k3SortAt X l (pC l) == some false && (k3SortAt X l (pD l)).isSome) =
      (K3.isHead X l == (l == 24)) := by
  unfold k3SortAt K3.pieceAt pC pD
  cases K3.isHead X l <;> cases (l == 24) <;> rfl

/-- **The test says: the output head's segment is number 24.** -/
theorem sortB_iff (X : OnBytes.Model.Verify.Public) : sortB X = true ↔ headLink X = 24 := by
  unfold sortB
  constructor
  · intro h
    have h1 := List.all_eq_true.1 h 24 (List.mem_range.2 (by decide))
    rw [sort_at] at h1
    have h2 : K3.isHead X 24 = true := eq_of_beq h1
    have h3 : (24 == headLink X) = true := h2
    exact (eq_of_beq h3).symm
  · intro h
    refine List.all_eq_true.2 fun l _ => ?_
    rw [sort_at]
    have e : K3.isHead X l = (l == headLink X) := rfl
    rw [e, h]
    exact beq_self_eq_true _

/-- The negative side. -/
theorem sortB_no (X : OnBytes.Model.Verify.Public) (h : headLink X ≠ 24) : sortB X = false := by
  cases hs : sortB X with
  | false => rfl
  | true => exact absurd ((sortB_iff X).1 hs) h

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

theorem sortB_ground (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) : sortB Bs.G₀.W = true :=
  (sortB_iff _).2 (headLink_open hS hR O)

/-- **hSortB, from the top's own head.** -/
theorem sortB_open (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) : sortB Z.p.X = true := by
  rw [← O.W]
  exact sortB_ground hS hR O

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.sort_at
#print axioms VerifiableInference.Desc.K1.sortB_iff
#print axioms VerifiableInference.Desc.K1.sortB_no
#print axioms VerifiableInference.Desc.K1.sortB_ground
#print axioms VerifiableInference.Desc.K1.sortB_open
