-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
SCRATCH HEAD: Johnson/Desc/ProofFile/Honest/K2/Law/ClosingLast.lean: a trial; the head comes when
the code stands.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.ClosingGrows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc.K2.Honest (Left)

/-- Where the walk returns, it hands a fold on just where one was handed in or a segment was
walked. -/
theorem closingFrom_isSome (table : FreshTable) (own : Nat → Nat → Nat → Nat → Cb.Gl.E)
    (heard : List Fmt.Drawn) (k : Nat → Except String Stretch) :
    ∀ (A : List SegmentPub) (j base : Nat) (prev : Option (Left × List OnBytes.OracleShape))
      (y : Option (Left × List OnBytes.OracleShape) × Nat),
      closingFrom table own heard k A j base prev = .ok y →
        y.1.isSome = (prev.isSome || !A.isEmpty)
  | [], _, base, prev, y, h => by
    simp only [closingFrom] at h
    obtain rfl : (prev, base) = y := Except.ok.inj h
    simp
  | S :: rest, j, base, prev, y, h => by
    simp only [closingFrom] at h
    cases hW : segmentLeft table S (prev.map (·.1)) ((prev.map (·.2)).getD []) (own j) heard k
        base with
    | error e =>
      rw [hW] at h
      cases h
    | ok W =>
      rw [hW] at h
      rw [closingFrom_isSome table own heard k rest (j + 1) (base + S.messages) (some W) y h]
      simp

/-- **THE WALK's LAST STEP.** Where the walk over A and then Sg returns x: the walk over A returns
some y; `segmentLeft` at Sg, at what y hands on, at the number A.length, returns W; x hands W on;
and y hands a fold on just where A is not empty. -/
theorem closingFrom_last {table : FreshTable} {own : Nat → Nat → Nat → Nat → Cb.Gl.E}
    {heard : List Fmt.Drawn} {k : Nat → Except String Stretch} {A : List SegmentPub}
    {Sg : SegmentPub} {x : Option (Left × List OnBytes.OracleShape) × Nat}
    (h : closingFrom table own heard k (A ++ [Sg]) 0 0 none = .ok x) :
    ∃ (y : Option (Left × List OnBytes.OracleShape) × Nat) (W : Left × List OnBytes.OracleShape),
      closingFrom table own heard k A 0 0 none = .ok y ∧
      segmentLeft table Sg (y.1.map (·.1)) ((y.1.map (·.2)).getD []) (own (0 + A.length)) heard k
        y.2 = .ok W ∧
      x.1 = some W ∧ y.1.isSome = !A.isEmpty := by
  rw [closingFrom_append] at h
  cases hy : closingFrom table own heard k A 0 0 none with
  | error e =>
    rw [hy] at h
    cases h
  | ok y =>
    rw [hy] at h
    have h' : closingFrom table own heard k [Sg] (0 + A.length) y.2 y.1 = .ok x := h
    simp only [closingFrom] at h'
    cases hW : segmentLeft table Sg (y.1.map (·.1)) ((y.1.map (·.2)).getD []) (own (0 + A.length))
        heard k y.2 with
    | error e =>
      rw [hW] at h'
      cases h'
    | ok W =>
      rw [hW] at h'
      obtain rfl : (some W, y.2 + Sg.messages) = x := Except.ok.inj h'
      refine ⟨y, W, rfl, hW, rfl, ?_⟩
      rw [closingFrom_isSome table own heard k A 0 0 none y hy]
      simp

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.closingFrom_isSome
#print axioms ProofFile.Honest.K2.Law.closingFrom_last
