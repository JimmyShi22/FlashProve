-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/JobsSpecOwed.lean: the honest side of the kind "lookup" (K3): the
statement of a lemma between the specification's statements and the filling of
Honest/K3/JobsSpec.lean. Definitions of propositions, and one line of proof: an instance of the
hypothesis. Neither statement is proved in this file: `JobsCongr` is proved in
Honest/K3/JobsSpecCongr.lean (`jobsCongr`), `MidCongr` in Honest/K3/Law/SpecReal.lean (`midCongr`).
They are none of the library's goals.

Terms. Honest/K3/GLOSSARY.md ("specification", "filling", "relation after the challenge").

Why the lemma is needed. The specification's statements on a sub-proof's lookup speak at its own
data (`dataF`: the bits are what a reading of places yields, at every pair of numbers). The
filling's data (`dataAt`, JobsSpec.lean) are made of the prover's input, and have 0 at a plane that
does not count. As functions the two differ outside the sizes. So a statement at the one reaches the
other only if the jobs read keys and bits inside the sizes alone.

What is defined.
  `SameInside D D'`: one structure of public numbers, one alpha; the keys agree below 2 ^ v; the
    bits agree at rows below 2 ^ d and planes below 2 ^ w.
  `SameJob J J'`: two jobs give the same lists and the same true sum.
  `Inside N`: the planes that count lie inside the cube; every order lists its level's variables.
  `JobsCongr`: at such numbers, data that are the same inside give, at every job that a row asks,
    the same round polynomials, polynomials in Y, end values and true sums. Without `Inside`, at
    other steps, or behind as many challenges as variables it is false: no counterexample is
    exhibited in this file.
  `MidCongr`: where all planes count (n + 2 = 2 ^ w; `Inside` is not asked there), the relation
    after the challenge holds of both data or of neither.

Can the hypotheses be met? `SameInside D D` holds of every D (`SameInside.refl`); at D' := D the
conclusion of `JobsCongr` says nothing. Of `Inside` no member is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.JobsSpec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes.HonestTrace.Look (Job Data tieJob keyJob tabJob leavesJob bitsJob)

/-- **Two data are the same inside the sizes.** -/
structure SameInside {P : Type} (D D' : Data P KE) : Prop where
  N : D.N = D'.N
  al : D.al = D'.al
  key : ∀ x, x < 2 ^ D.v → D.key x = D'.key x
  bits : ∀ u j, u < 2 ^ D.N.d → j < 2 ^ D.N.w → D.bits u j = D'.bits u j

/-- Every datum is the same inside as itself. -/
theorem SameInside.refl {P : Type} (D : Data P KE) : SameInside D D :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ _ _ _ => rfl⟩

/-- Two jobs give the same lists and the same true sum. A round polynomial is asked only behind
fewer challenges than the job has variables: behind all of them there is no round. -/
def SameJob (J J' : Job KE) : Prop :=
  J.zs = J'.zs ∧ J.dg = J'.dg ∧ J.dY = J'.dY ∧ J.sum = J'.sum ∧
    (∀ rs, rs.length < J.zs.length → J.round rs = J'.round rs) ∧
    (∀ xs, J.ends xs = J'.ends xs) ∧ (∀ xs m, J.inY xs m = J'.inY xs m) ∧
      (∀ xs, J.fin xs = J'.fin xs)

/-- The planes that count lie inside the cube, and every order lists the numbers below its level's
number of variables, each once. -/
structure Inside {P : Type} (N : TwV.Nums P KE) : Prop where
  planes : N.n + 2 ≤ 2 ^ N.w
  oK : ∀ l, l < N.v' + 1 → (N.oK l).Perm (List.range l)
  oT : ∀ l, l < N.d → (N.oT l).Perm (List.range (N.w + l))
  oE : N.oE.Perm (List.range (N.w + N.d))
  oB : N.oB.Perm (List.range (N.w + N.d))

/-- The statement that the five jobs read keys and bits inside the sizes alone: at the tie's own
steps (s ≤ n), at the trees' own levels (below v on the key side, below d on the table's), at public
numbers that are `Inside`. Proved in Honest/K3/JobsSpecCongr.lean; a lemma's statement, none of the
library's goals. -/
def JobsCongr : Prop :=
  ∀ (P : Type) (D D' : Data P KE), SameInside D D' → Inside D.N →
    (∀ s, s ≤ D.N.n → SameJob (tieJob D s) (tieJob D' s)) ∧
    (∀ l z, l < D.v → SameJob (keyJob D l z) (keyJob D' l z)) ∧
    (∀ l z, l < D.N.d → SameJob (tabJob D l z) (tabJob D' l z)) ∧
    (∀ z, SameJob (leavesJob D z) (leavesJob D' z)) ∧
    (∀ z, SameJob (bitsJob D z) (bitsJob D' z))

/-- The statement that the relation after the challenge reads keys and bits inside the sizes alone,
where all planes count. Proved in Honest/K3/Law/SpecReal.lean; a lemma's statement, none of the
library's goals. -/
def MidCongr : Prop :=
  ∀ (P : Type) (D D' : Data P KE), SameInside D D' → D.N.n + 2 = 2 ^ D.N.w → (D.Mid ↔ D'.Mid)

#print axioms ProofFile.Honest.K3.SameInside.refl

end ProofFile.Honest.K3
