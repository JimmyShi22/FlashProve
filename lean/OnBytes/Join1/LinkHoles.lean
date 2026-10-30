-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Join1/LinkHoles.lean: the written link with the records in its decision, as one reduction
(`linkOf`, OnBytes/Join1/LinkHole.lean): its verifier is local; and a bound on its list of errors in
the form that counts proof-of-work bits, at no bits.

General in the description (C, ds, a, xs) and in the family of decisions: no size occurs.
The written protocol `(skeletonOverBothExternalStrings C ds a xs dec).up.loc` (Run/PlanQX.lean) is local for every decision
dec (`Run.PQ.psofX_local`, Run/PlanQXLawsProofs.lean), and the positions that it declares as read
depend neither on its statement, nor on the plain parts, nor on dec: they are functions of the
verifier's messages. So a family of decisions, one for each explicit statement x, is one local
reduction.

Main names:
  `shW C ds`: the written rounds. `erW C ds a xs`, `rdW C ds a xs`: the positions read, of the two
    strings and of the prover's oracles. `accW C ds a xs dec`: the decisions.
  `linkW C ds a xs dec`: the reduction. `linkW_local`: it is local (`IOR.IsLocal`, Ior/Ior.lean).
  `linkW_accept`: at each x its protocol accepts what the written protocol at `dec x` accepts.
  `belowG_zero_of_below`: `Err.Below ε c` → `Err.BelowG (GBits.zero s) ε c`.

Limits: nothing on soundness or on an honest prover. In `IOR.IsLocal` the clause on the new implicit
instance is empty here (there is none); sources, ties and blinding are not read by it. The bits are
0 on purpose: where a written round's verifier messages hold a work test already, a bound on its
share of bad messages counts that work; other bits would lay a second test over it.

Terms: lean/GLOSSARY.md.

-/
import Hiop.GrindK
import OnBytes.Join1.LinkHole
import Run.PlanQXLawsProofs

set_option autoImplicit false

namespace OnBytes.Join1
open Iop Prob Hiop Run.PQ
open scoped ENNReal

/-- fixed plain parts -/
def plains0 : (s : Shape) → Plains s
  | [] => ()
  | r :: s => (r.dPlain, plains0 s)

section
variable (C : CK) (ds : List RD) (a : Nat) (xs : List XO)

/-- The written rounds. -/
abbrev shW : Shape := Run.Twin.up (SOf C ds)

/-- The positions of the two strings that the written verifier reads. -/
def erW : Rho (shW C ds) → Finset (twoExternalStrings (2 ^ a) SgX).Pos := fun ρ =>
  (skeletonOverBothExternalStrings C ds a xs fun _ => true).extReads () ρ

/-- The positions of the prover's oracles that the written verifier reads. -/
def rdW : Rho (shW C ds) → Finset (OPos (shW C ds)) := fun ρ =>
  (skeletonOverBothExternalStrings C ds a xs fun _ => true).reads () ρ (plains0 _)

variable {X : Type} (dec : X → View → Bool)

/-- The decisions: at the statement x the written protocol's, with `dec x`. -/
def accW : X → (twoExternalStrings (2 ^ a) SgX).Str → Tr (shW C ds) → Bool := fun x y τ =>
  (skeletonOverBothExternalStrings C ds a xs (dec x)).accept () y τ

/-- The written link with the statement in its decision, as one reduction. -/
def linkW : IOR X (twoExternalStrings (2 ^ a) SgX) Unit extNone :=
  linkOf (shW C ds) (fun _ => true) (erW C ds a xs) (rdW C ds a xs) (accW C ds a xs dec)

/-- Its verifier is local. -/
theorem linkW_local : (linkW C ds a xs dec).IsLocal :=
  linkOf_local _ _ _ _ _ fun x y y' τ τ' h1 h2 h3 h4 =>
    psofX_local C ds a xs (dec x) () y y' τ τ' h1 h2 h3 h4

/-- At each statement its protocol accepts what the written protocol accepts. -/
theorem linkW_accept (x : X) (y : (twoExternalStrings (2 ^ a) SgX).Str) (τ : Tr (shW C ds)) :
    (linkW C ds a xs dec).toInteractiveOracleProof.accept x y τ =
      (skeletonOverBothExternalStrings C ds a xs (dec x)).up.loc.accept () y τ := by
  show (if (skeletonOverBothExternalStrings C ds a xs (dec x)).accept () y τ then some () else none : Option Unit).isSome =
    (skeletonOverBothExternalStrings C ds a xs (dec x)).accept () y τ
  cases (skeletonOverBothExternalStrings C ds a xs (dec x)).accept () y τ <;> rfl

end

/-- A bound on a list of errors, in the form that counts proof-of-work bits, at no bits. -/
theorem belowG_zero_of_below {s : Shape} (ε : Err s) (c : ℝ≥0∞) (h : Err.Below ε c) :
    Err.BelowG (GBits.zero s) ε c :=
  (Err.belowG_zero ε c).2 h

end OnBytes.Join1
