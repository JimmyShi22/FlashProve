-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05U3B.lean: kind K5: U3There (Att/K05FormsMade.lean: three public facts on the
record in front of K5's block) AS A Bool ON THE RECORD: so that a program can run it at a stored
proof's record, and a table can hold it as a public item.

Main names:
  `u3ThereB own c s`: at an open attention segment: the open ledger's array number c.iU3 has one own row
    and at least c.nW columns · the link's list names at c.iU3 an array of the layout, of the open
    segment's second sending, with a row and at least c.nW columns · the mask row's message is seated.
  `u3There_of_B`, `u3ThereB_of`: it is U3There.
  `u3ThereB_behind`: it rides over the hearing's lay.
  `u3ThereB_closed`: a control: false where no attention segment is open.
Limits. IT HAS RUN AT NO RECORD. EMPTY AT: see the control.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05FormsMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Model.Road
open VerifiableInference.Desc.K9 (maskSeat atMoment1)

/-- The three facts at an open attention segment's own record. -/
def u3AtB (own : List (ℕ × ℕ)) (c : ParC) (s : First.S) (a : First.AttOwn) : Bool :=
  ((a.F.trees[c.iU3]?).any fun T => T.R == 1 && Decidable.decide (c.nW ≤ T.K)) &&
    ((a.L.arrayOf[c.iU3]?).any fun b =>
      (reqArray a.L.check.rows.layout b.1 b.2).any fun Ar =>
        atMoment1 (partAt s a a.F none) b Ar && Decidable.decide (0 < Ar.sizeI) &&
          Decidable.decide (c.nW ≤ Ar.sizeC)) &&
    (maskSeat own (partAt s a a.F none)).isSome

/-- **U3There as a Bool on the record.** -/
def u3ThereB (own : List (ℕ × ℕ)) (c : ParC) (s : First.S) : Bool :=
  match s.here with
  | .att a => u3AtB own c s a
  | _ => false

section
variable {own : List (ℕ × ℕ)} {c : ParC} {s : First.S} {a : First.AttOwn}

theorem u3There_of_B (e : s.here = .att a) (h : u3ThereB own c s = true) : U3There own s a c := by
  unfold u3ThereB at h
  rw [e] at h
  unfold u3AtB at h
  simp only [Bool.and_eq_true, Option.any_eq_true_iff_get, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨t0, t1, t2⟩, ⟨b0, r0, ⟨r1, r2⟩, r3⟩⟩, hm⟩ := h
  exact ⟨⟨_, (Option.some_get t0).symm, t1, t2⟩,
    ⟨_, _, (Option.some_get b0).symm, (Option.some_get r0).symm, r1, r2, r3⟩, hm⟩

theorem u3ThereB_of (e : s.here = .att a) (U : U3There own s a c) : u3ThereB own c s = true := by
  obtain ⟨T, hT, hR, hW⟩ := U.tree
  obtain ⟨b, Ar, hb, hA, hm1, hI, hC⟩ := U.array
  unfold u3ThereB
  rw [e]
  unfold u3AtB
  simp only [hT, hb, hA, Option.any_some, hR, hm1, U.mask, Bool.and_eq_true, decide_eq_true_eq,
    beq_self_eq_true, true_and, and_true]
  exact ⟨hW, hI, hC⟩

/-- It rides over the hearing's lay. -/
theorem u3ThereB_behind {x : Params.AttentionRounds} {rs : List Fmt.RoundView} {h : Heard} {G : Fork}
    (e : s.here = .att a) (hh : hear x (a.F, rs, 0) = some (h, G, [], 0)) (hz : Sized a.F) :
    u3ThereB own c (behind s a h G) = u3ThereB own c s := by
  obtain ⟨_, bl⟩ := hear_below hh hz
  unfold u3ThereB
  rw [e]
  show u3AtB own c (behind s a h G) { a with F := G, heard5 := some h } = u3AtB own c s a
  unfold u3AtB
  show (((G.trees[c.iU3]?).any _) && _ && _) = _
  rw [bl.trees]
  rfl

/-- A control. -/
theorem u3ThereB_closed (h : ∀ a, s.here ≠ .att a) : u3ThereB own c s = false := by
  unfold u3ThereB
  split
  · rename_i a e
    exact absurd e (h a)
  · rfl

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.u3There_of_B
#print axioms VerifiableInference.Desc.First.Att.P.u3ThereB_of
#print axioms VerifiableInference.Desc.First.Att.P.u3ThereB_behind
#print axioms VerifiableInference.Desc.First.Att.P.u3ThereB_closed
