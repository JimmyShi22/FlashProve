-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/LinkAlongM.lean: the pair of readings between the later chain queries of the link
over two interfaces, and between their leaf queries.

OnBytes/TypedOracleCompiler/Run/LinkAlong.lean carries codes from an interface L1 to an interface L2 along pairs of
partial maps that undo each other (`FbPair`, `LeafPair`). Here the two pairs are written.
  round k + 1:   ⟨k + 1, f2 none ρ, rt, p⟩ over L2 is read as ⟨k + 1, f2 none ρ, rt, pbF p⟩ over L1.
  a leaf:        ⟨body, salt⟩ over L2 is read as ⟨bd body, salt⟩ over L1.
No other chain query is read: none of round 0, none with another head. The link's first query is
written over L2 directly (OnBytes/TypedOracleCompiler/Run/LinkFirstAns.lean, ArmDirect.lean).
Parameters: pbF, a one-to-one correspondence of the two interfaces' plain parts under the link's
tag; bd, one of their bodies.

Main definitions: `selL`, `bkL`, `laterM` (an `FbPair L1 L2`); `leafM` (a `LeafPair L1 L2`).
Main theorems: `bkL_selL`, `selL_bkL` (each undoes the other); `selL_later`, `selL_zero`.

Not claimed. That a verifier over L2 asks only queries of these forms. That there is a pbF or a bd
at any two interfaces. Nothing on soundness.


-/
import OnBytes.TypedOracleCompiler.Run.LinkAlong

set_option autoImplicit false

namespace TypedOracleCompiler.Run.LinkAlongM
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open TypedOracleCompiler.Run.LinkAlong
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I1 X1 I2 X2 : Type} (L1 : BatchProtocolWithLeafBody I1 X1) (L2 : BatchProtocolWithLeafBody I2 X2)
  (pbF : PlainPart (shapeOf L2 .link) (annOf L2 .link) ≃ PlainPart (shapeOf L1 .link) (annOf L1 .link))

/-- A later chain query of the link over L2, read as one over L1. -/
def selL (q : FbIn 256 L2 .link) : Option (FbIn 256 L1 .link) :=
  match q.round, q.head with
  | k + 1, .f2 none ρ => some ⟨k + 1, .f2 none ρ, q.rt, pbF q.plain⟩
  | _, _ => none

/-- The way back. -/
def bkL (q : FbIn 256 L1 .link) : Option (FbIn 256 L2 .link) :=
  match q.round, q.head with
  | k + 1, .f2 none ρ => some ⟨k + 1, .f2 none ρ, q.rt, pbF.symm q.plain⟩
  | _, _ => none

/-- The reading at a later query of the form. -/
theorem selL_later (k : ℕ) (ρ : Bits) (rt : List (Dig 256))
    (p : PlainPart (shapeOf L2 .link) (annOf L2 .link)) :
    selL L1 L2 pbF ⟨k + 1, .f2 none ρ, rt, p⟩ = some ⟨k + 1, .f2 none ρ, rt, pbF p⟩ := rfl

/-- No query of round 0 is read. -/
theorem selL_zero (q : FbIn 256 L2 .link) (h : q.round = 0) : selL L1 L2 pbF q = none := by
  obtain ⟨round, head, rt, plain⟩ := q
  have h' : round = 0 := h
  subst h'
  rfl

/-- The way back undoes the reading. -/
theorem bkL_selL (a : FbIn 256 L2 .link) (b : FbIn 256 L1 .link)
    (h : selL L1 L2 pbF a = some b) : bkL L1 L2 pbF b = some a := by
  obtain ⟨round, head, rt, plain⟩ := a
  unfold selL at h
  split at h
  · rename_i k ρ e1 e2
    have e1' : round = k + 1 := e1
    have e2' : head = .f2 none ρ := e2
    rw [← Option.some.inj h, e1', e2']
    show some (⟨k + 1, .f2 none ρ, rt, pbF.symm (pbF plain)⟩ : FbIn 256 L2 .link) = _
    rw [Equiv.symm_apply_apply]
  · cases h

/-- The reading undoes the way back. -/
theorem selL_bkL (b : FbIn 256 L1 .link) (a : FbIn 256 L2 .link)
    (h : bkL L1 L2 pbF b = some a) : selL L1 L2 pbF a = some b := by
  obtain ⟨round, head, rt, plain⟩ := b
  unfold bkL at h
  split at h
  · rename_i k ρ e1 e2
    have e1' : round = k + 1 := e1
    have e2' : head = .f2 none ρ := e2
    rw [← Option.some.inj h, e1', e2']
    show some (⟨k + 1, .f2 none ρ, rt, pbF (pbF.symm plain)⟩ : FbIn 256 L1 .link) = _
    rw [Equiv.apply_symm_apply]
  · cases h

/-- **The pair for the link's later chain queries.** -/
def laterM : FbPair L1 L2 where
  sel := selL L1 L2 pbF
  bk := bkL L1 L2 pbF
  bk_sel := bkL_selL L1 L2 pbF
  sel_bk := selL_bkL L1 L2 pbF

/-- **The pair for leaf queries**, from a one-to-one correspondence of the bodies: the salt stays.
-/
def leafM (bd : L2.Bd ≃ L1.Bd) : LeafPair L1 L2 where
  sel := fun q => some ⟨bd q.body, q.salt⟩
  bk := fun q => some ⟨bd.symm q.body, q.salt⟩
  bk_sel := fun a b h => by
    rw [← Option.some.inj h]
    show some (⟨bd.symm (bd a.body), a.salt⟩ : LeafIn L2) = some a
    rw [Equiv.symm_apply_apply]
  sel_bk := fun b a h => by
    rw [← Option.some.inj h]
    show some (⟨bd (bd.symm b.body), b.salt⟩ : LeafIn L1) = some b
    rw [Equiv.apply_symm_apply]

end TypedOracleCompiler.Run.LinkAlongM
