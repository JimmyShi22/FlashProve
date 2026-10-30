-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req/ReqNumsGlue.lean: degrees and numbers of variables of glued families.

This file states bounds on two numbers of a constraint system over a Boolean cube (a family, `Fam`,
Cb/Req/ReqSpec.lean), on which the round errors of a sumcheck on it depend, when several systems
are joined into one. The degree of a family is here the largest number of atoms in a term
(`Fam.deg`, Cb/Req/ReqSumFmt.lean).
Definitions and statements on data only; the proofs are in Cb/Req/ReqNumsGlueProofs.lean.

Why: the preamble of a request is run on the glued form of a partition (Cb/Req/ReqGlue.lean: one
family of identities in a segment, one family of keys for each table). Gluing adds selector
variables and multiplies coefficient tables; it adds no atom to any term.

Main names:
  `Fam.DegLe f d`, `Spec.degLe_glue`: see their docstrings.
  `SegSpec.NumsLe S d V`, `Spec.numsLe_glued`: `NumsLe` passes to the glued segment, with ⌈log₂ n⌉
    more variables if the segment has at most n families of each kind.

Limits: this file says nothing on games.

Terms: lean/GLOSSARY.md.
-/
import Cb.Req.ReqGlue
import Blocks.MergeStage
import Blocks.SemClaims
import Cb.Req.ReqSumFmtProofs
import Hiop.Chain

set_option autoImplicit false

namespace Cb

/-- No term has more than d atoms, in the family and in the sums among its atoms. -/
def Fam.DegLe {X E : Type} (f : Fam X E) (d : ℕ) : Prop :=
  f.deg ≤ d ∧ ∀ j w P, f.atom j = .sum w P → P.toFam.deg ≤ d

/-- The two numbers of a segment's families: no term, of a family or of a sum among its atoms, has
more than d atoms (`Fam.DegLe`); no family has more than V variables. -/
def SegSpec.NumsLe {X F E : Type} (S : SegSpec X F E) (d V : ℕ) : Prop :=
  (∀ f ∈ S.idn, f.DegLe d ∧ f.v ≤ V) ∧ ∀ k ∈ S.keys, k.1.DegLe d ∧ k.1.v ≤ V

namespace Spec
open Blocks Iop Prob Hiop Alg Cb.Req
open scoped ENNReal

def deg_le_iff : Prop :=
  ∀ (X E : Type) (f : Fam X E) (d : ℕ), f.deg ≤ d ↔ ∀ t ∈ f.terms, t.atoms.length ≤ d

def degLe_to : Prop := ∀ (X E : Type) (f : Fam X E) (N d : ℕ), f.DegLe d → (f.to N).DegLe d

def degLe_mask : Prop :=
  ∀ (X E : Type) [Mul E] (f : Fam X E) (c : X → ℕ → E) (d : ℕ), f.DegLe d → (f.mask c).DegLe d

def degLe_pub : Prop :=
  ∀ (X E : Type) [Zero E] (v : ℕ) (c : X → ℕ → E) (d : ℕ), (Fam.pub v c).DegLe d

def degLe_add : Prop :=
  ∀ (X E : Type) (f g : Fam X E) (d : ℕ), f.DegLe d → g.DegLe d → (f.add g).DegLe d

/-- States: if every family of L has `DegLe d`, so has the glued family: gluing adds no atom to a
term. -/
def degLe_glue : Prop :=
  ∀ (X E : Type) [Zero E] [One E] [Mul E] (pad : E) (L : List (Fam X E)) (d : ℕ),
    (∀ f ∈ L, f.DegLe d) → (Fam.glue pad L).DegLe d

def glueN_le : Prop :=
  ∀ (X E : Type) (L : List (Fam X E)) (V : ℕ),
    (∀ f ∈ L, f.v ≤ V) → glueN L ≤ Nat.clog 2 L.length + V

/-- The glued segment: degrees. -/
def degLe_glued : Prop :=
  ∀ (X F E : Type) [Field F] [Field E] [Algebra F E] (S : SegSpec X F E) (d : ℕ),
    (∀ f ∈ S.idn, f.DegLe d) → (∀ k ∈ S.keys, k.1.DegLe d) →
    (∀ f ∈ S.glued.idn, f.DegLe d) ∧ ∀ k ∈ S.glued.keys, k.1.DegLe d

/-- The glued segment: numbers of variables. -/
def v_glued : Prop :=
  ∀ (X F E : Type) [Field F] [Field E] [Algebra F E] (S : SegSpec X F E) (V : ℕ),
    (∀ f ∈ S.idn, f.v ≤ V) → (∀ k ∈ S.keys, k.1.v ≤ V) →
    (∀ f ∈ S.glued.idn, f.v ≤ Nat.clog 2 S.idn.length + V) ∧
    ∀ k ∈ S.glued.keys, k.1.v ≤ Nat.clog 2 S.keys.length + V

/-- The glued segment: both numbers. -/
def numsLe_glued : Prop :=
  ∀ (X F E : Type) [Field F] [Field E] [Algebra F E] (S : SegSpec X F E) (d V n : ℕ),
    S.NumsLe d V → S.idn.length ≤ n → S.keys.length ≤ n → S.glued.NumsLe d (Nat.clog 2 n + V)

end Spec
end Cb
