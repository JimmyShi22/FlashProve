-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/SpecMember.lean: the honest side of the kind "lookup" (K3).
An instance of the hypotheses of `lawfulSpec` (Honest/K3/Law/SpecProof.lean): a course of the small
synthetic lookup (Honest/K3/Toy.lean) whose summands are the specification's, with tests with code
that accept it, and theorems that lead from an acceptance by each test to the hypothesis.
Definitions with code, theorems, eight tests by evaluation.

Terms. Honest/K3/GLOSSARY.md ("course", "lawful", "settled", "specification", "synthetic", "test by
evaluation").

What is shown, by the file's sections.
  1. `perm_of_ok`, `numsAre_of_ok`: at public numbers made of a face (`numsOf`): `NumsAre` out of
     the verifier's own tests on the face, at one part of keys.
  2. `one_of_settled`, `toy_settled`: the input yields one structure at all the stages' fronts,
     where it no longer moves from the challenges in front of the lookup on.
  3. `numberedC`, `numbered_of`: `Numbered`: two clauses out of `Fit`
     (Honest/K3/Law/SpecNumbered.lean), the others by a test with code.
  4. `midC`, `mid_of`; `specC`, `specAt_of`: `SpecAt` at `specJobsAt`: the clauses that are
     equations between values, by a test with code.
  5. `member_lawful`: from an acceptance by the three tests to `Lawful`.
  6. The small lookup's course; the tests accept it, and reject altered ones.

Hypotheses that remain.
  `h`, `h1`, `h2`, `h3`: a test with code accepts (`numberedC`, `midC`, `specC`; `fitC`,
    `numberedC`, `specC` or `specT`).
  `hJ`, `hp`, `hs`: (in `specAt_of`, `member_lawful`; `hp` also in `perm_of_ok`, `numsAre_of_ok` and
    `numbered_of`, `hs` also in `one_of_settled`) the course's summands are the specification's at
    public numbers made of its own face; one part of keys; `Ask.Settled` at the place's number of
    rounds in front.
  `hF`: `Fit R`. `hok`, `hl`: (in section 1) the face passes the verifier's tests; l < v. `hb`: (in
    `toy_settled`, `M₁_lawful`) a round at least stands in front.

Users. This file is imported by Honest/K3/Law/SpecReal.lean.

Limits. How far the instance goes: that the tests accept is by evaluation: by Lean's evaluator, not
by its kernel. So "this course meets the hypotheses" is a theorem from three equations
`test = true`, and these three equations are evaluated.
One size (8 keys, 4 rows, 3 planes of 4), two orders of the key tree's rounds.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.SpecProof
import Johnson.Desc.ProofFile.Honest.K3.Law.SpecNumbered
import Johnson.Desc.ProofFile.Honest.K3.Law.Members
import Johnson.Desc.ProofFile.Honest.K3.WitLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.Spec
open OnBytes (E zeroE oneE)
open OnBytes.Model (orderDefault)
open OnBytes.HonestTrace.Look (Data)
open ProofFile.Honest.K3.Law.Members (fitC fit_of courseOf)

variable {P : Type}

/-! ## 1 NumsAre out of the verifier's tests on the face -/

/-- The verifier's tests on a face give: each level's order of the key tree lists that
level's variables, each once. -/
theorem perm_of_ok {f : LFace} {v : Nat} (hok : f.ok = true) (hp : f.parts = [v]) {l : Nat}
    (hl : l < v) : (f.orders 0 l).Perm (List.range l) := by
  simp only [VerifiableInference.Desc.K3.Face.ok, Bool.and_eq_true, List.all_eq_true] at hok
  have h1 := hok.2 (v, 0) (by rw [hp]; simp)
  simp only [VerifiableInference.Desc.First.Prod.runOk, Bool.and_eq_true, List.all_eq_true] at h1
  have h2 := h1.2 l (List.mem_range.2 hl)
  rw [Nat.zero_add] at h2
  exact perm_of_orderOk (show VerifiableInference.Desc.First.ProdV.orderOk l (f.orders 0 l) = true
    from h2)

/-- **At public numbers made of a face that passes the verifier's tests and has one part of keys,
the numbers are the face's.** -/
theorem numsAre_of_ok (f : LFace) (row : E → Nat → E) (pads : List (Nat × Nat)) (theta : KE)
    (v : Nat) (hok : f.ok = true) (hp : f.parts = [v]) : NumsAre f (numsOf f row pads theta) := by
  have hperm := fun l (hl : l < v) => perm_of_ok hok hp hl
  have h2 := two_le_planes_of_ok f hok
  simp only [VerifiableInference.Desc.K3.Face.ok, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at hok
  have hv : 1 ≤ v := hok.1.1.1.2 v (by rw [hp]; simp)
  have hroom : f.planes ≤ 2 ^ f.mu := hok.1.1.1.1.1.2
  have hv' : (numsOf f row pads theta).v' + 1 = v := by
    show f.parts.headD 0 - 1 + 1 = v
    rw [hp]
    show v - 1 + 1 = v
    omega
  refine ⟨by rw [hv']; exact hp, rfl, rfl, ?_, ?_, fun _ => rfl, ?_, fun _ => rfl, rfl, rfl⟩
  · show f.planes = f.planes - 2 + 2
    omega
  · show f.planes - 2 + 2 ≤ 2 ^ f.mu
    omega
  · intro l hl
    exact hperm l (by rw [← hv']; exact hl)

/-! ## 2 One structure at all the stages' fronts -/

/-- **Where the input no longer moves from the challenges in front of the lookup on, it yields one
structure at all the stages' fronts.** Conditional on `Fit` besides. -/
theorem one_of_settled (R : Course Ask) (hF : Fit R) (hs : Ask.Settled R.a.base R.t.input)
    (s : Stage) : R.t.input (R.front s).heard = R.t.input R.t.heard :=
  hs R.t.heard _ (by rw [hF.base])

/-- The small lookup's input reads the first challenge heard, and no other. -/
theorem toy_settled (d : Nat → Toy.Made) (base : Nat) (hb : 1 ≤ base) :
    Ask.Settled base (Toy.askOf d) := by
  intro front more hf
  unfold Toy.askOf
  cases front with
  | nil => simp at hf; omega
  | cons a l => rfl

/-! ## 3 Numbered -/

/-- The clauses of `Numbered` that Honest/K3/Law/SpecNumbered.lean does not show, with code. -/
def numberedC {W : Type} (R : Course W) : Bool :=
  ((List.range (R.f.parts.headD 0)).all fun m =>
    decide (R.pts.keyPt 0 (m + 1) =
      behind m (R.f.orders 0 m) ((R.r (.key 0 m)).take m) (R.xiK 0 m))) &&
  ((List.range R.f.d).all fun l =>
    decide (R.pts.tabPt (l + 1) = behind (R.f.mu + l) (orderDefault (R.f.mu + l))
      ((R.r (.tab l)).take (R.f.mu + l)) (R.xiT l))) &&
  decide (R.zb0 = (R.r .leaves).toArray) &&
  decide (R.zb1 = ((R.r .bits).take (R.f.mu + R.f.d)).toArray) &&
  ((stages R.f).all fun s => (R.masks s).length == s.tail R.f)

/-- An acceptance by the test, with `Fit` at one part of keys, gives the hypothesis. -/
theorem numbered_of {W : Type} (R : Course W) (v : Nat) (hp : R.f.parts = [v]) (hF : Fit R)
    (h : numberedC R = true) : Numbered R := by
  simp only [numberedC, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range,
    beq_iff_eq] at h
  exact ⟨same_of_fit R v hp hF, len_of_fit R hF, h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-! ## 4 SpecAt -/

/-- The relation after the challenge, with code. -/
def midC (D : Data P KE) : Bool :=
  decide (∀ u, u < 2 ^ D.N.d → ∀ j, j < 2 ^ D.N.w → D.bits u j * (D.bits u j - 1) = 0) &&
  decide (∑ u ∈ Finset.range (2 ^ D.N.d), ∑ j ∈ Finset.range (D.N.n + 2), (2 : KE) ^ j *
    D.bits u j =
    ((2 ^ D.v - Cb.Lkp.padNum D.N.pads : Nat) : KE)) &&
  decide (Cb.Lkp.keyProd D.v D.key D.al = Cb.Lkp.padFac D.N.tab D.N.pads D.al *
    ∏ j ∈ Finset.range (D.N.n + 2), Cb.Lkp.tabProd D.N.d D.N.tab D.bits D.al j ^ 2 ^ j)

theorem mid_of (D : Data P KE) (h : midC D = true) : D.Mid := by
  simp only [midC, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- The clauses of `SpecAt` that are equations between values, with code: the public factor; the
table at the leaves' sumcheck's own point; the count of padding; the relation
after the challenge. -/
def specC (R : Course Ask) (N : KE → TwV.Nums P KE) (w : Hidden) : Bool :=
  decide (up R.factor = (dataAt N w R.pts).a) &&
  decide (up (R.f.leaf R.pts.theta R.pts.alpha R.zb0) =
    ((List.range (2 ^ R.f.d)).map fun r => TwV.eqN ((byBit R.zb0).drop R.f.mu) r *
      (up R.pts.alpha - 1 - (N (up R.pts.theta)).tab r)).sum) &&
  decide (((N (up R.pts.theta)).pads.map (·.2)).sum = (R.f.padding.map (·.1)).sum) &&
  midC (dataAt N w R.pts)

/-- **An acceptance by the test gives `SpecAt`**, at a course whose summands are the specification's
at public numbers made of its own face, whose face has one part, which passes `Fit`, and whose input
no longer moves from the challenges in front of the lookup on. -/
theorem specAt_of (R : Course Ask) (row : E → Nat → E) (pads : List (Nat × Nat)) (v : Nat)
    (hJ : R.J = (specJobsAt R.f row pads).asked) (hp : R.f.parts = [v]) (hF : Fit R)
    (hs : Ask.Settled R.a.base R.t.input)
    (h : specC R (numsOf R.f row pads) (R.t.input R.t.heard) = true) :
    SpecAt R (numsOf R.f row pads) (R.t.input R.t.heard) := by
  simp only [specC, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨hJ, fun s _ => one_of_settled R hF hs s, numsAre_of_ok R.f row pads _ v hF.ok hp,
    h.1.1.1, h.1.1.2, h.1.2, mid_of _ h.2⟩

/-! ## 5 From the tests to Lawful -/

/-- **From an acceptance by the three tests to `Lawful`**, at a course whose summands are the
specification's at public numbers made of its own face, whose face has one part, and whose input has
settled. -/
theorem member_lawful (R : Course Ask) (row : E → Nat → E) (pads : List (Nat × Nat)) (v : Nat)
    (hJ : R.J = (specJobsAt R.f row pads).asked) (hp : R.f.parts = [v])
    (hs : Ask.Settled R.a.base R.t.input) (h1 : fitC R = true) (h2 : numberedC R = true)
    (h3 : specC R (numsOf R.f row pads) (R.t.input R.t.heard) = true) :
    Lawful R (planesOf (dataAt (numsOf R.f row pads) (R.t.input R.t.heard) R.pts))
      (keysOf (dataAt (numsOf R.f row pads) (R.t.input R.t.heard) R.pts)) :=
  lawfulSpec Unit _ _ R (fit_of R h1) (numbered_of R v hp (fit_of R h1) h2)
    (specAt_of R row pads v hJ hp (fit_of R h1) hs h3)

/-! ## 6 The small lookup's course -/

/-- The padding as the specification has it: one key, the table's row 1. -/
def toyPads : List (Nat × Nat) := [(1, 1)]

/-- The small lookup's course with the specification's summands: at the order that counts down, and
at the order that counts up. -/
def M₁ : Course Ask :=
  courseOf Toy.f₁ (specJobsAt Toy.f₁ Toy.rowAt toyPads) Toy.honest Toy.g₁ Toy.h₁
def M₂ : Course Ask :=
  courseOf Toy.f₂ (specJobsAt Toy.f₂ Toy.rowAt toyPads) Toy.honest Toy.g₃ Toy.h₃

/-- The third test at a course of the small lookup. -/
def specT (R : Course Ask) (pads : List (Nat × Nat)) : Bool :=
  specC R (numsOf R.f Toy.rowAt pads) (R.t.input R.t.heard)

-- The tests accept both courses.
#guard fitC M₁ && numberedC M₁ && specT M₁ toyPads
#guard fitC M₂ && numberedC M₂ && specT M₂ toyPads
-- A round stands in front of the lookup, so that the small lookup's input has settled.
#guard decide (1 ≤ M₁.a.base) && decide (1 ≤ M₂.a.base)
-- And they reject altered ones. Another row as padding; two keys of padding.
#guard !specT M₁ [(2, 1)] && !specT M₁ [(1, 2)]
-- False data: a key outside the table's rows as counted; a false count; a bit that is no bit.
#guard !specT (courseOf Toy.f₁ (specJobsAt Toy.f₁ Toy.rowAt toyPads) Toy.badKey Toy.g₁ Toy.h₁)
  toyPads
#guard !specT (courseOf Toy.f₁ (specJobsAt Toy.f₁ Toy.rowAt toyPads) Toy.badCount Toy.g₁ Toy.h₁)
  toyPads
#guard !specT (courseOf Toy.f₁ (specJobsAt Toy.f₁ Toy.rowAt toyPads) Toy.badBit Toy.g₁ Toy.h₁)
  toyPads
-- A course that counts one round more in front of the lookup.
#guard !numberedC { M₁ with a := { M₁.a with base := M₁.a.base + 1 } }

/-- **The instance**: from the evaluated equations to `Lawful` of the small lookup's course. -/
theorem M₁_lawful (hb : 1 ≤ M₁.a.base) (h1 : fitC M₁ = true) (h2 : numberedC M₁ = true)
    (h3 : specT M₁ toyPads = true) :
    Lawful M₁ (planesOf (dataAt (numsOf M₁.f Toy.rowAt toyPads) (M₁.t.input M₁.t.heard) M₁.pts))
      (keysOf (dataAt (numsOf M₁.f Toy.rowAt toyPads) (M₁.t.input M₁.t.heard) M₁.pts)) :=
  member_lawful M₁ Toy.rowAt toyPads 3 rfl rfl (toy_settled Toy.honest _ hb) h1 h2 h3

#print axioms ProofFile.Honest.K3.Law.Spec.numbered_of
#print axioms ProofFile.Honest.K3.Law.Spec.mid_of
#print axioms ProofFile.Honest.K3.Law.Spec.specAt_of
#print axioms ProofFile.Honest.K3.Law.Spec.member_lawful
#print axioms ProofFile.Honest.K3.Law.Spec.M₁_lawful
#print axioms ProofFile.Honest.K3.Law.Spec.perm_of_ok
#print axioms ProofFile.Honest.K3.Law.Spec.numsAre_of_ok
#print axioms ProofFile.Honest.K3.Law.Spec.one_of_settled
#print axioms ProofFile.Honest.K3.Law.Spec.toy_settled

end ProofFile.Honest.K3.Law.Spec
