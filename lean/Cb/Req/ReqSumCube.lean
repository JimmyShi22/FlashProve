-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req/ReqSumCube.lean: how two ways of writing a cube correspond.

This file treats two indexings of the Boolean cube, by numbers b < 2^v and by functions Fin v →
Bool, and the multilinear extension and the weighted sums of a sumcheck in both.
Definitions and statements; the proofs are in Cb/Req/ReqSumCubeProofs.lean. No protocol. Many
statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Why: the conditions of a request (Cb/Req/ReqSpec.lean) number the vertices of a cube (b < 2^v; the
first coordinate belongs to the most significant bit) and write points as functions on numbers
(`Blocks.ext`, `Cb.vtx`). The summand of a sumcheck on a family of conditions (`Req.summand`,
Cb/Req/ReqSumFmt.lean) has variables Fin v, vertices Fin v → Bool and points Fin
v → E (`Alg.mle`, `Alg.corner`). Here the two are joined once: a vertex b : Fin v → Bool has the
number `Alg.num b`; a point z : Fin v → E is read on numbers as `Blocks.nat z` (0 beyond the v
coordinates).

Main names:
  `wts ve γ`: the weights: see its docstring.
  `Spec.ext_mle`, `Spec.ext_nat`: the extension of a numbered vector is the extension of the same
    vector on vertices.
  `Spec.wsum_split`: the weighted sum over a cube of v + w variables, equality weights on the first
    v: it is the extension, at γ, of the vector of inner sums.
  `Spec.wsum_all`: the same without inner variables: the extension at γ.
  `Spec.wts_ne`: for ve ≤ n (n the number of variables), no weight by which a round divides
    (`wts ve γ i true`, i : Fin n) is 0 exactly if none of the first ve coordinates of γ is 0.

Limits: this file says nothing on any protocol.

Terms: lean/GLOSSARY.md: conditions (of a segment), family.
-/
import Cb.Req.ReqSpec
import Alg.Mle

set_option autoImplicit false

namespace Cb.Req
open Blocks Alg Finset

/-- The weights: the equality factor at γ on the variables t < ve, plain on the others. -/
def wts {E : Type} [Field E] {n : ℕ} (ve : ℕ) (γ : ℕ → E) : Fin n → Bool → E := fun i β =>
  if i.val < ve then (if β then γ i.val else 1 - γ i.val) else 1

end Cb.Req

namespace Cb.Spec
open Blocks Alg Finset Cb.Req

def ext_mle : Prop :=
  ∀ (E : Type) [Field E] (v : ℕ) (f : ℕ → E) (pt : ℕ → E),
    ext v f pt = mle (fun b : Fin v → Bool => f (num b)) fun t : Fin v => pt t.val

def ext_nat : Prop :=
  ∀ (E : Type) [Field E] (v : ℕ) (f : ℕ → E) (z : Fin v → E),
    ext v f (nat z) = mle (fun b : Fin v → Bool => f (num b)) z

def vtx_num : Prop :=
  ∀ (E : Type) [Field E] (v : ℕ) (b : Fin v → Bool), vtx (E := E) v (num b) = nat (corner b)

/-- The weighted sum over v + w variables. -/
def wsum_split : Prop :=
  ∀ (E : Type) [Field E] (n v w : ℕ) (γ : ℕ → E) (g : ℕ → E), n = v + w →
    ∑ b : Fin n → Bool, (∏ i, wts v γ i (b i)) * g (num b) =
      ext v (fun a => ∑ j ∈ range (2 ^ w), g (a * 2 ^ w + j)) γ

def wsum_all : Prop :=
  ∀ (E : Type) [Field E] (v : ℕ) (γ : ℕ → E) (g : ℕ → E),
    ∑ b : Fin v → Bool, (∏ i, wts v γ i (b i)) * g (num b) = ext v g γ

def wts_ne : Prop :=
  ∀ (E : Type) [Field E] (n ve : ℕ) (γ : ℕ → E),
    ve ≤ n → ((∀ i : Fin n, wts ve γ i true ≠ 0) ↔ ∀ t < ve, γ t ≠ 0)

end Cb.Spec
