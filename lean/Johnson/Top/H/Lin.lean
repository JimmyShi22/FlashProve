-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/Lin.lean: the three kinds of round that are the own rounds of the test on a stored
table (LIN point; LOC on the table's columns; LIN zeta) as values of `Kind` (Johnson/Top/Kind.lean),
at any written list of sizes, each with its hypothesis and the three facts beside it.

Nothing new is proved: every line is a call of Cb/Pv/Lin.lean. A size is that file's record `Size
E`: data alone. The joints are the library's (`LdLinP.j1` to `j6`, Cb/Ld/LdLin.lean) with their
conditions moved into the relaxed relations; they hang on the size alone.
Main names:
  `kLinPt L`, `kLinLoc L`, `kLinZeta L`: the three kinds.
  `kLinPt_know`, `_point`, `_local`, `_onOut`, `_good`: under `P.FoldErr on0 εf` at every size of
    the list. The same for `kLinLoc`, without a premise, and for `kLinZeta`, for an injective
    `P.D.py`.
  `HLinPt`, `HLinLoc`, `HLinZeta`: closed, over the field `Cb.Gl.E`. `hLinPt`, `hLinLoc`,
    `hLinZeta`: they hold.
Limits: one instance. A batch of N slots is not a value of `Kind`: its statement is
`Cb.Pv.Lin.coreKB`. The three sendings between these rounds are of the kind SEND
(Johnson/Top/H/Send.lean). No list of sizes is written here: the values at which a description of
the programs' protocol has such blocks are built nowhere, so the conditions are proved of no
value. Nothing says that a block of a kind is the step that the programs run, or that its error is
small. Nothing on an honest prover.
-/
import Johnson.Top.Kind
import Cb.Pv.Lin
import Cb.Gl.GlField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop Cb IOR Cb.Pv.Lin

section
variable {E : Type} [Field E] [Fintype E]

/-- LIN point, at a written list of sizes. -/
@[reducible] noncomputable def kLinPt (L : List (Size E)) : Kind.{1} where
  Size := Size E
  sizes := L
  src := fun s => jOf (s.P.j1 s.on0).cf
  dst := fun s => jOf (s.P.j2 s.on0).cf
  block := fun s => ⟨s.P.pt, fun _ _ w => w.2, ((s.P.errPt s.εf, ()) : ℕ × Unit)⟩

/-- LOC on the table's columns, at a written list of sizes. -/
@[reducible] noncomputable def kLinLoc (L : List (Size E)) : Kind.{1} where
  Size := Size E
  sizes := L
  src := fun s => jOf (s.P.j3 s.on0).cf
  dst := fun s => jOf s.P.j4.cf
  block := fun s => ⟨s.P.loc, fun _ _ w => w.2, ((s.P.errLoc, ()) : ℕ × Unit)⟩

/-- LIN zeta, at a written list of sizes. -/
@[reducible] noncomputable def kLinZeta (L : List (Size E)) : Kind.{1} where
  Size := Size E
  sizes := L
  src := fun s => jOf s.P.j5.cf
  dst := fun s => jOf s.P.j6.cf
  block := fun s => ⟨s.P.zeta, fun _ _ w => w, ((s.P.errZeta, ()) : ℕ × Unit)⟩

variable (L : List (Size E))

theorem kLinPt_know (h : ∀ s ∈ L, s.P.FoldErr s.on0 s.εf) : (kLinPt L).Know :=
  fun s hs => hPt s (h s hs)

theorem kLinPt_point (h : ∀ s ∈ L, s.P.FoldErr s.on0 s.εf) : (kLinPt L).Point :=
  fun s hs => pt_point s (h s hs)

theorem kLinPt_local (h : ∀ s ∈ L, s.P.FoldErr s.on0 s.εf) : (kLinPt L).Local :=
  fun s hs => pt_isLocal s (h s hs)

theorem kLinPt_onOut : (kLinPt L).OnOut := fun _ _ _ _ _ _ _ => trivial

theorem kLinPt_good (h : ∀ s ∈ L, s.P.FoldErr s.on0 s.εf) :
    ∀ s ∈ L, ((kLinPt L).block s).Good :=
  Kind.good (kLinPt_know L h) (kLinPt_point L h) (kLinPt_local L h) (kLinPt_onOut L)

theorem kLinLoc_know : (kLinLoc L).Know := fun s _ => Cb.Pv.Lin.hLoc s

theorem kLinLoc_point : (kLinLoc L).Point := fun s _ => loc_point s

theorem kLinLoc_local : (kLinLoc L).Local := fun s _ => loc_isLocal s

theorem kLinLoc_onOut : (kLinLoc L).OnOut := fun _ _ _ _ _ _ _ => trivial

theorem kLinLoc_good : ∀ s ∈ L, ((kLinLoc L).block s).Good :=
  Kind.good (kLinLoc_know L) (kLinLoc_point L) (kLinLoc_local L) (kLinLoc_onOut L)

theorem kLinZeta_know (h : ∀ s ∈ L, Function.Injective s.P.D.py) : (kLinZeta L).Know :=
  fun s hs => hZeta s (h s hs)

theorem kLinZeta_point (h : ∀ s ∈ L, Function.Injective s.P.D.py) : (kLinZeta L).Point :=
  fun s hs => zeta_point s (h s hs)

theorem kLinZeta_local (h : ∀ s ∈ L, Function.Injective s.P.D.py) : (kLinZeta L).Local :=
  fun s hs => zeta_isLocal s (h s hs)

theorem kLinZeta_onOut : (kLinZeta L).OnOut := fun _ _ _ _ _ _ _ => trivial

theorem kLinZeta_good (h : ∀ s ∈ L, Function.Injective s.P.D.py) :
    ∀ s ∈ L, ((kLinZeta L).block s).Good :=
  Kind.good (kLinZeta_know L h) (kLinZeta_point L h) (kLinZeta_local L h) (kLinZeta_onOut L)

end

/-- The hypothesis of LIN point, closed. -/
def HLinPt : Prop :=
  ∀ L : List (Size Cb.Gl.E), (∀ s ∈ L, s.P.FoldErr s.on0 s.εf) → (kLinPt L).Know

theorem hLinPt : HLinPt := kLinPt_know

/-- The hypothesis of LOC on the table's columns, closed. -/
def HLinLoc : Prop := ∀ L : List (Size Cb.Gl.E), (kLinLoc L).Know

theorem hLinLoc : HLinLoc := kLinLoc_know

/-- The hypothesis of LIN zeta, closed. -/
def HLinZeta : Prop :=
  ∀ L : List (Size Cb.Gl.E), (∀ s ∈ L, Function.Injective s.P.D.py) → (kLinZeta L).Know

theorem hLinZeta : HLinZeta := kLinZeta_know

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.hLinPt
#print axioms VerifiableInference.OnPublicFiles.hLinLoc
#print axioms VerifiableInference.OnPublicFiles.hLinZeta
#print axioms VerifiableInference.OnPublicFiles.kLinPt_good
#print axioms VerifiableInference.OnPublicFiles.kLinLoc_good
#print axioms VerifiableInference.OnPublicFiles.kLinZeta_good
