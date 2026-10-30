-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Parts/Data.lean: the honest side of the kind "lookup" (K3): THE
SPECIFICATION AT SEVERAL PARTS OF KEYS: its data, the relation after the challenge, and the one job
that the specification at one key vector does not hold. Definitions with code, definitions of
propositions, small theorems with proofs.

Johnson/HonestTrace/LookDefs.lean states a lookup's honest summands for ONE vector of 2 ^ v keys.
The verifier's text (Johnson/Desc/First/Look/Via/Rounds.lean) is general in a list of parts: each
part has a key vector and a product tree of its own; the tie speaks of the product Z of all parts'
roots, and a step for each part but the last cuts that product into the part's root and the rest's.
A key file's lookups have twelve parts.

  1  `DataP`, `DataP.part`   the shared half (table, padding, bits, alpha: a `Data` whose own keys
     are not read) and, by part, the number of levels, the orders, the keys. PART i IS A `Data` OF
     THE SPECIFICATION: all its definitions and theorems on a key tree are used at that term
  2  `DataP.Zi`, `restFrom`, `DataP.rest`   a part's root; the product of the roots from a part on
  3  `DataP.Mid`   THE RELATION AFTER THE CHALLENGE AT PARTS: bits are bits; the counts add up to
     the number of all parts' keys that are no padding; the product of all roots is the public
     factor times the planes' roots to their powers. `mid_one`: at one part it is
     the specification's own
  4  `tieTop`, `tieTop_eq`, `tieTop_lawful`   the tie's first step with Z, a, P_1, G_0 as letters;
     at a `Data`'s own it IS the specification's job; CONDITIONAL ON Z = a P_1 ^ 2 G_0 it is lawful
  5  `tie_lawful_succ`   the tie's later steps are lawful: the specification's own job, no
                         premise on keys
  6  `splitJob`, `split_lawful`   THE PARTS' STEP IS THE SPECIFICATION'S JOB OF A PRODUCT OF TWO
     TABLES, WITHOUT A VARIABLE: this part's root times the rest's

Limits. `DataP.Mid` of a key file's honest keys and counts is not shown here:
it is for the files that state the key
file's honest prover. Nothing here is held against the verifier's
text.
Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K3.JobsSpec
import Johnson.HonestTrace.LookJobs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Parts
open OnBytes.HonestTrace.Look (Job Data pj tieJob sqMul addP shownL evalP wsum Chained)

variable {P : Type}

/-! ## 1 The data -/

/-- **A lookup's data at several parts of keys.** -/
structure DataP (P : Type) where
  /-- the shared half: public numbers, bits, alpha. Its own v', oK and key are not read -/
  D : Data P KE
  /-- for each part the number of its tree's levels: the part has 2 ^ v keys -/
  vs : List Nat
  /-- part i's order of binding at the level with m variables -/
  oK : Nat → Nat → List Nat
  /-- part i's key number x -/
  key : Nat → Nat → KE

/-- **Part i, as data of the specification at one key vector.** -/
def DataP.part (A : DataP P) (i : Nat) : Data P KE :=
  { A.D with N := { A.D.N with v' := A.vs.getD i 0 - 1, oK := A.oK i }, key := A.key i }

/-! ## 2 The roots -/

/-- Part i's root: the product of alpha - key over its keys. -/
def DataP.Zi (A : DataP P) (i : Nat) : KE := (A.part i).Z

/-- The product of k numbers from number i on. -/
def restFrom (z : Nat → KE) : Nat → Nat → KE
  | 0, _ => 1
  | k + 1, i => z i * restFrom z k (i + 1)

/-- The product of the roots from part i on. -/
def DataP.rest (A : DataP P) (i : Nat) : KE := restFrom A.Zi (A.vs.length - i) i

/-- From a part that there is: its root times the rest's. -/
theorem DataP.rest_step (A : DataP P) {i : Nat} (hi : i < A.vs.length) :
    A.rest i = A.Zi i * A.rest (i + 1) := by
  unfold DataP.rest
  rw [show A.vs.length - i = (A.vs.length - (i + 1)) + 1 by omega]
  rfl

/-- From the last part on: its root. -/
theorem DataP.rest_last (A : DataP P) {i : Nat} (hi : i + 1 = A.vs.length) :
    A.rest i = A.Zi i := by
  rw [A.rest_step (by omega)]
  unfold DataP.rest
  rw [show A.vs.length - (i + 1) = 0 by omega]
  exact mul_one _

/-! ## 3 The relation after the challenge -/

/-- **The relation after the challenge, at parts.** -/
def DataP.Mid (A : DataP P) : Prop :=
  Cb.Lkp.Bits A.D.N.d A.D.N.w A.D.bits ∧
  (∑ u ∈ Finset.range (2 ^ A.D.N.d), ∑ j ∈ Finset.range (A.D.N.n + 2), (2 : KE) ^ j * A.D.bits u j =
    (((A.vs.map (2 ^ ·)).sum - Cb.Lkp.padNum A.D.N.pads : Nat) : KE)) ∧
  A.rest 0 = A.D.a * ∏ j ∈ Finset.range (A.D.N.n + 2), A.D.G j ^ 2 ^ j

/-- **At one part the relation is the specification's own**, at that part's data. -/
theorem mid_one (A : DataP P) (v : Nat) (hv : 1 ≤ v) (h : A.vs = [v]) : A.Mid ↔ (A.part 0).Mid := by
  have e1 : A.rest 0 = (A.part 0).Z := A.rest_last (by rw [h]; rfl)
  have e2 : (A.part 0).v = v := by
    show A.vs.getD 0 0 - 1 + 1 = v
    rw [h]
    show v - 1 + 1 = v
    omega
  have e3 : (A.vs.map (2 ^ ·)).sum = 2 ^ (A.part 0).v := by
    rw [e2, h]
    simp
  unfold DataP.Mid
  rw [e1, e3]
  exact Iff.rfl

/-! ## 4 The tie's first step, over letters -/

/-- **The tie's first step**: no variable but Y; end values Z, P_1, G_0; summand Z - a P_1 ^ 2 G_0;
the sum written as 0. -/
def tieTop (Z a P1 G0 : KE) : Job KE where
  zs := []
  dg := []
  dY := some 3
  sum := 0
  round := fun _ => []
  fin := fun _ => 0
  ends := fun _ => [Z, P1, G0]
  inY := fun _ m => addP [Z, m.getD 0 0] ((sqMul P1 G0 (m.getD 1 0) (m.getD 2 0)).map (-a * ·))
  S0 := fun x => x.getD 0 0 - a * (x.getD 1 0 ^ 2 * x.getD 2 0)

/-- At a datum's own letters it is the specification's job. -/
theorem tieTop_eq (D : Data P KE) : tieTop D.Z D.a (D.Pc 1) (D.G 0) = tieJob D 0 := by
  unfold tieTop tieJob
  simp

/-- **CONDITIONAL ON Z = a P_1 ^ 2 G_0: the tie's first step is lawful.** A member: every Z of that
form. -/
theorem tieTop_lawful (Z a P1 G0 : KE) (hZ : Z = a * (P1 ^ 2 * G0)) : (tieTop Z a P1 G0).Lawful :=
    by
  refine ⟨fun xs hx => ?_, fun _ xs m β _ hm => ?_⟩
  · have e : xs = [] := List.length_eq_zero_iff.1 hx
    subst e
    exact rfl
  · obtain ⟨m0, m1, m2, rfl⟩ : ∃ m0 m1 m2, m = [m0, m1, m2] := by
      match m, hm with
      | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
    refine ⟨?_, ?_⟩
    · show (Z + -a * (P1 ^ 2 * G0)) + 0 * _ = 0
      rw [hZ]
      ring
    · show evalP [Z + -a * _, m0 + -a * _, -a * _, -a * _] β =
        (shownL β [Z, P1, G0] [m0, m1, m2]).getD 0 0 - a *
          ((shownL β [Z, P1, G0] [m0, m1, m2]).getD 1 0 ^ 2 *
            (shownL β [Z, P1, G0] [m0, m1, m2]).getD 2 0)
      simp only [evalP, TwV.evalGo, List.headD_cons, List.tail_cons, shownL,
        List.zipWith_cons_cons, List.getD_cons_zero, List.getD_cons_succ]
      ring

/-! ## 5 The tie's later steps -/

/-- **The tie's later steps are lawful**, whatever the keys: the specification's own job. -/
theorem tie_lawful_succ (D : Data P KE) (s : Nat) (hs : s + 1 ≤ D.N.n) :
    (tieJob D (s + 1)).Lawful := by
  have h0 : s + 1 ≠ 0 := Nat.succ_ne_zero s
  refine ⟨fun xs hx => ?_, fun _ xs m β _ hm => ?_⟩
  · have e : xs = [] := List.length_eq_zero_iff.1 hx
    subst e
    exact rfl
  · have hends : (tieJob D (s + 1)).ends xs = [D.Pc (s + 1 + 1), D.G (s + 1)] := by
      simp only [tieJob, if_neg h0]
    rw [hends] at hm
    obtain ⟨m0, m1, rfl⟩ : ∃ m0 m1, m = [m0, m1] := by
      match m, hm with
      | [a, b], _ => exact ⟨a, b, rfl⟩
    have hY : (tieJob D (s + 1)).inY xs [m0, m1] =
        sqMul (D.Pc (s + 1 + 1)) (D.G (s + 1)) m0 m1 := by
      simp only [tieJob, if_neg h0]
      rfl
    have hfin : (tieJob D (s + 1)).fin xs = D.Pc (s + 1) := by simp only [tieJob, if_neg h0]
    have hS : ∀ x, (tieJob D (s + 1)).S0 x = x.getD 0 0 ^ 2 * x.getD 1 0 := fun x => by
      simp only [tieJob, if_neg h0]
    rw [hY, hfin, hS, hends, OnBytes.HonestTrace.Look.Pc_step D hs]
    refine ⟨?_, ?_⟩
    · show D.Pc (s + 1 + 1) ^ 2 * D.G (s + 1) + 0 * _ = _
      ring
    · simp only [sqMul, evalP, TwV.evalGo, List.headD_cons, List.tail_cons, shownL,
        List.zipWith_cons_cons, List.getD_cons_zero, List.getD_cons_succ]
      ring

/-! ## 6 The parts' step -/

/-- **The parts' step i**: the product of the roots from part i on is part i's root times the
rest's: the specification's job of a product of two tables, without a variable. -/
def splitJob (A : DataP P) (i : Nat) : Job KE :=
  pj 0 0 (fun _ => A.Zi i) (fun _ => A.rest (i + 1)) [] []

/-- The parts' step is lawful. -/
theorem split_lawful (A : DataP P) (i : Nat) : (splitJob A i).Lawful :=
  OnBytes.HonestTrace.Look.pj_lawful 0 0 _ _ [] [] (List.Perm.refl _) rfl

/-- Its true sum is the product of the roots from part i on, at a part that there is. -/
theorem split_sum (A : DataP P) {i : Nat} (hi : i < A.vs.length) :
    (splitJob A i).sum = A.rest i := by
  rw [A.rest_step hi]
  show ∑ X ∈ Finset.range (2 ^ 0), TwV.eqN [] X * (0 + A.Zi i * A.rest (i + 1)) = _
  simp [TwV.eqN]

/-- Its end values: part i's root; the rest's product. -/
theorem split_ends (A : DataP P) (i : Nat) (xs : List KE) :
    (splitJob A i).ends xs = [A.Zi i, A.rest (i + 1)] := by
  show [OnBytes.HonestTrace.Look.ext 0 _ _, OnBytes.HonestTrace.Look.ext 0 _ _] = _
  simp [OnBytes.HonestTrace.Look.ext, TwV.eqN, TwV.byVar]

#print axioms ProofFile.Honest.K3.Parts.DataP.rest_step
#print axioms ProofFile.Honest.K3.Parts.DataP.rest_last
#print axioms ProofFile.Honest.K3.Parts.mid_one
#print axioms ProofFile.Honest.K3.Parts.tieTop_eq
#print axioms ProofFile.Honest.K3.Parts.tieTop_lawful
#print axioms ProofFile.Honest.K3.Parts.tie_lawful_succ
#print axioms ProofFile.Honest.K3.Parts.split_lawful
#print axioms ProofFile.Honest.K3.Parts.split_sum
#print axioms ProofFile.Honest.K3.Parts.split_ends

end ProofFile.Honest.K3.Parts
