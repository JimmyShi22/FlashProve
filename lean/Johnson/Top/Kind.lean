-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Kind.lean: a kind of block of a protocol description: a written list of sizes and, for
each size, a bare block; and the kind's hypothesis, knowledge soundness alone.

A bare block (`KObj.BK`, Johnson/E/KObj/Blocks.lean) is a typed reduction between two joints with an
extractor and a list of errors: the verifier's side alone. Definitions and proofs.
Main names:
  `Kind`: a type of sizes; the list of the sizes at which the description has a block of this
    kind; the two joints and the block at each size.
  `Kind.Know`: THE HYPOTHESIS OF A KIND: at every size of the list the block's reduction is
    round-by-round knowledge sound at its own errors.
  `Kind.Point`, `Kind.Local`, `Kind.OnOut`: the three facts on the verifier alone, each a
    proposition of its own.
  `Kind.good`: the four together give `KObj.BK.Good` at every size of the list: what a typed list of
    blocks asks (`LK.Each PG`).
  `BaseKind E`: a kind stated at the base: for each fixed tuple m of committed messages, over a
    signature `Sg s` that is a field. `BaseKind.Know`, `.Point`, `.Local`, `.OnOut`.
  `BaseKind.toKind`: the kind lifted over its signature, at the same errors (`sigLift_know`,
    Cb/Ld/LdSigLiftProofs.lean). `BaseKind.good`.
Limits: nothing here says that a kind's block is the step that the programs run, that its list of
sizes is the programs' schedule's, or that any hypothesis holds.

-/
import Johnson.E.KObj.Arrows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop Cb IOR

universe u

/-- A kind of block. -/
structure Kind : Type (max 1 (u + 1)) where
  /-- the record of sizes of a block of this kind (it may hold types: so any universe) -/
  Size  : Type u
  /-- the sizes at which the description has such a block: a written list -/
  sizes : List Size
  /-- the joint before the block, the joint behind it -/
  src   : Size → JK
  dst   : Size → JK
  /-- the block -/
  block : ∀ s, BK (src s) (dst s)

namespace Kind
variable (κ : Kind.{u})

/-- THE HOLE OF A KIND: «know» alone, at every size of the list. -/
def Know : Prop :=
  ∀ s ∈ κ.sizes, (κ.block s).R.red.Know (κ.src s).on (κ.src s).relR (κ.dst s).relR (κ.block s).ext
    (κ.block s).err

/-- Every message of the verifier's queries is a point query. -/
def Point : Prop := ∀ s ∈ κ.sizes, Nonempty (κ.block s).R.shape.IsPoint

/-- The verifier is local. -/
def Local : Prop := ∀ s ∈ κ.sizes, (κ.block s).R.IsLocal

/-- What the block leaves meets the next joint's condition. -/
def OnOut : Prop :=
  ∀ s ∈ κ.sizes, ∀ a τ x, (κ.block s).R.red.out a τ = some x → (κ.src s).on a → (κ.dst s).on x

variable {κ}

/-- The four together: every block of the kind has the property that the spine asks. -/
theorem good (hk : κ.Know) (hp : κ.Point) (hl : κ.Local) (ho : κ.OnOut) :
    ∀ s ∈ κ.sizes, (κ.block s).Good :=
  fun s hs => BK.good_of _ (hp s hs) (hl s hs) (ho s hs) (hk s hs)

end Kind

/-- A kind stated at the base, over a named signature. -/
structure BaseKind (E : Type) [Field E] : Type (max 1 (u + 1)) where
  Size  : Type u
  sizes : List Size
  /-- THE SIGNATURE: the committed messages are Sg s's -/
  Sg    : Size → Sig E
  Kc    : Size → Type
  St    : Size → Type
  St'   : Size → Type
  Wp    : Size → Type
  Wp'   : Size → Type
  E₀    : Size → ExtSpec
  E₀'   : Size → ExtSpec
  R     : ∀ s, IOR (St s) (E₀ s) (St' s) (E₀' s)
  A     : ∀ s, IOR.Rels (Kc s) (St s) (E₀ s) ((Sg s).Msg × Wp s)
  B     : ∀ s, IOR.Rels (Kc s) (St' s) (E₀' s) ((Sg s).Msg × Wp' s)
  ext   : ∀ s, (Sg s).Msg → St s × (E₀ s).Str → Tr (R s).shape → Wp' s → Wp s
  ε     : ∀ s, Err (R s).shape

namespace BaseKind
variable {E : Type} [Field E] (β : BaseKind.{u} E)

/-- THE HOLE OF A KIND AT THE BASE: «know» alone, at every size of the list, for every tuple of
committed messages. -/
def Know : Prop :=
  ∀ s ∈ β.sizes, ∀ m, (β.R s).red.Know (β.A s).on (fun a wp => (β.A s).relR a (m, wp))
    (fun b wp => (β.B s).relR b (m, wp)) (β.ext s m) (β.ε s)

def Point : Prop := ∀ s ∈ β.sizes, Nonempty (β.R s).shape.IsPoint
def Local : Prop := ∀ s ∈ β.sizes, (β.R s).IsLocal
def OnOut : Prop :=
  ∀ s ∈ β.sizes, ∀ a τ b, (β.A s).on a → (β.R s).red.out a τ = some b → (β.B s).on b

/-- The kind, lifted over its signature: the same reduction kept beside the oracle messages, the
same errors. -/
@[reducible] noncomputable def toKind : Kind.{u} where
  Size := β.Size
  sizes := β.sizes
  src := fun s => jOver (β.Sg s) (β.A s)
  dst := fun s => jOver (β.Sg s) (β.B s)
  block := fun s => BK.ofSig (β.Sg s) (β.R s) (β.A s) (β.B s) (β.ext s) (β.ε s)

variable {β}

/-- The hole at the base gives the hole over the signature, at the same errors. -/
theorem know_toKind (hk : β.Know) : β.toKind.Know :=
  fun s hs => sigLift_know E (β.Sg s) (β.Kc s) (β.St s) (β.St' s) (β.Wp s) (β.Wp' s) (β.E₀ s)
    (β.E₀' s) (β.R s) (β.A s) (β.B s) (β.ext s) (β.ε s) (hk s hs)

theorem point_toKind (hp : β.Point) : β.toKind.Point := hp

theorem local_toKind (hl : β.Local) : β.toKind.Local :=
  fun s hs => IsLocal.keepE (β.Sg s).ext (isLocal_keepX (hl s hs) (β.Sg s).Smp)

theorem onOut_toKind (ho : β.OnOut) : β.toKind.OnOut :=
  fun s hs a τ b hb ha => by
    obtain ⟨h1, h2, h3⟩ := keep_red_out (β.R s) (β.Sg s).Smp (β.Sg s).ext a τ b hb
    refine ⟨?_, ho s hs _ τ _ ha.2 h3⟩
    rw [h1, h2]
    exact ha.1

theorem good (hk : β.Know) (hp : β.Point) (hl : β.Local) (ho : β.OnOut) :
    ∀ s ∈ β.sizes, (β.toKind.block s).Good :=
  Kind.good (know_toKind hk) (point_toKind hp) (local_toKind hl) (onOut_toKind ho)

end BaseKind

#print axioms VerifiableInference.OnPublicFiles.Kind.good
#print axioms VerifiableInference.OnPublicFiles.BaseKind.good

end VerifiableInference.OnPublicFiles
