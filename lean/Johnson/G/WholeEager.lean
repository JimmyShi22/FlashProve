-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/G/WholeEager.lean: a second twin of `OnBytes.Three.Whole.of`, in which every number that is
carried along a list of rounds is evaluated at each step, with the proof that it equals `Whole.of`.

Johnson/G/WholeTwin.lean's twin lets Lean's kernel evaluate `Whole.of` at some 19,000 rounds. At
48,000 the kernel runs out of stack again: the counts of trees sent, the rounds' numbers and the
sums are carried along the lists as unevaluated terms. Here each is handed on through `force`
(Johnson/G/Eager.lean). Definitions and proofs.
Main names:
  `rootsE`, `rootsE_eq`: the number of roots that a list of rounds sends.
  `opensE`, `opensOf_eq`: all openings of a chain. `rdsE`, `rdsTwin_eq`: a chain's rounds' data.
    `rowsE`, `treesE`, `treesOfChain_eq`: a chain's rows of the table of trees.
  `wholeE R₁ R₂ R₃`, `whole_eqE : Three.Whole.of R₁ R₂ R₃ = wholeE R₁ R₂ R₃`.
Limits: general in the lists; no value is treated. Nothing on soundness.

-/
import Johnson.G.WholeTwin
import Johnson.G.Eager

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G

open OnBytes.Three
open OnBytes.Params (Rounds)

/-- a plus the number of roots that the rounds send. -/
def rootsE : Nat → Rounds → Nat
  | a, [] => a
  | a, r :: R => force (a + r.1.items.countP (· == .root)) fun v => rootsE v R

theorem rootsE_eq (R : Rounds) : ∀ a, rootsE a R = a + rootsIn R := by
  induction R with
  | nil => intro a; rfl
  | cons r R ih =>
    intro a
    simp only [rootsE, force_eq, ih, rootsIn, List.map_cons, List.sum_cons]
    omega

theorem rootsIn_eq (R : Rounds) : rootsIn R = rootsE 0 R := by
  rw [rootsE_eq]
  omega

/-- The openings of the rounds, the first of which has the number i. -/
def opensE (t₁ t₂ here : Nat) : Nat → Rounds → List (Nat × Fmt.Shape × Nat × Nat)
  | _, [] => []
  | i, r :: R =>
    (r.1.opens.filterMap fun o => (named here o.2).map fun x => (wholeNo t₁ t₂ x, o.1, here, i)) ++
      force (i + 1) fun v => opensE t₁ t₂ here v R

theorem opensE_eq (t₁ t₂ here : Nat) (R : Rounds) : ∀ i,
    ((R.zipIdx i).flatMap fun r => r.1.1.opens.filterMap fun o =>
      (named here o.2).map fun x => (wholeNo t₁ t₂ x, o.1, here, r.2)) =
      opensE t₁ t₂ here i R := by
  induction R with
  | nil => intro i; rfl
  | cons r R ih =>
    intro i
    simp only [List.zipIdx_cons, List.flatMap_cons, opensE, force_eq, ih]

theorem opensOf_eq (t₁ t₂ here : Nat) (R : Rounds) :
    opensOf t₁ t₂ here R = opensE t₁ t₂ here 0 R :=
  opensE_eq t₁ t₂ here R 0

/-- The rounds' data, a trees having been sent before the first. -/
def rdsE (all : List (Nat × Fmt.Shape × Nat × Nat)) (t₁ t₂ here base first : Nat) :
    Nat → Rounds → List RDL
  | _, [] => []
  | a, r :: R => rdOf all t₁ t₂ here base first r a ::
      force (a + r.1.items.countP (· == .root)) fun v => rdsE all t₁ t₂ here base first v R

theorem rdsE_eq (all : List (Nat × Fmt.Shape × Nat × Nat)) (t₁ t₂ here base first : Nat)
    (R : Rounds) : ∀ a, List.zipWith (rdOf all t₁ t₂ here base first) R (sentFrom a R) =
      rdsE all t₁ t₂ here base first a R := by
  induction R with
  | nil => intro a; rfl
  | cons r R ih =>
    intro a
    simp only [sentFrom, List.zipWith_cons_cons, rdsE, force_eq, ih]

theorem rdsTwin_eq (all : List (Nat × Fmt.Shape × Nat × Nat)) (t₁ t₂ here base first : Nat)
    (R : Rounds) :
    rdsTwin all t₁ t₂ here base first R = rdsE all t₁ t₂ here base first 0 R :=
  rdsE_eq all t₁ t₂ here base first R 0

/-- For each tree that the rounds send: the round's number, the place among its roots, the shape. -/
def rowsE : Nat → List RDL → List (Nat × Nat × Fmt.Shape)
  | _, [] => []
  | i, d :: ds => (d.trees.zipIdx.map fun s => (i, s.2, s.1)) ++ force (i + 1) fun v => rowsE v ds

theorem rowsE_eq (ds : List RDL) : ∀ i,
    ((ds.zipIdx i).flatMap fun d => d.1.trees.zipIdx.map fun s => (d.2, s.2, s.1)) =
      rowsE i ds := by
  induction ds with
  | nil => intro i; rfl
  | cons d ds ih =>
    intro i
    simp only [List.zipIdx_cons, List.flatMap_cons, rowsE, force_eq, ih]

/-- A chain's rows of the table of trees. -/
def treesE (all : List (Nat × Fmt.Shape × Nat × Nat)) (here base : Nat) (ds : List RDL) :
    List Tree :=
  (rowsE 0 ds).zipIdx.map fun x =>
    ⟨here, x.1.1, x.1.2.1, x.1.2.2, (all.filter (·.1 == base + x.2)).map (·.2.2)⟩

theorem treesOfChain_eq (all : List (Nat × Fmt.Shape × Nat × Nat)) (here base : Nat)
    (ds : List RDL) : treesOfChain all here base ds = treesE all here base ds := by
  unfold treesOfChain treesE
  rw [← rowsE_eq]

/-- The second twin of `Three.Whole.of`. -/
def wholeE (R₁ R₂ R₃ : Rounds) : Whole :=
  force (rootsE 0 R₁) fun t₁ => force (rootsE 0 R₂) fun t₂ =>
    let all := opensE t₁ t₂ 0 0 R₁ ++ (opensE t₁ t₂ 1 0 R₂ ++ opensE t₁ t₂ 2 0 R₃)
    let ds₁ := rdsE all t₁ t₂ 0 0 0 0 R₁
    let ds₂ := rdsE all t₁ t₂ 1 t₁ 0 0 R₂
    let ds₃ := rdsE all t₁ t₂ 2 (t₁ + t₂) (first₃ t₁) 0 R₃
    ⟨ds₁, ds₂, ds₃,
      treesE all 0 0 ds₁ ++ (treesE all 1 t₁ ds₂ ++ treesE all 2 (t₁ + t₂) ds₃),
      t₁, t₂, rootsE 0 R₃, all⟩

theorem whole_eqE (R₁ R₂ R₃ : Rounds) : Whole.of R₁ R₂ R₃ = wholeE R₁ R₂ R₃ := by
  rw [whole_eq]
  unfold wholeTwin wholeE
  simp only [force_eq, rootsIn_eq, opensOf_eq, rdsTwin_eq, treesOfChain_eq]

end Johnson.G

#print axioms Johnson.G.whole_eqE
