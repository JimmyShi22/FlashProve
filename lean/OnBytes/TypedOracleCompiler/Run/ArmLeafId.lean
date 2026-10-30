-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/ArmLeafId.lean: bodies of leaves over a second interface, and a pair of readings of
leaf queries, that meet what the laws at leaves of `implArmD`'s family ask of them.

OnBytes/TypedOracleCompiler/Run/ArmLaws.lean shows the laws at leaves (`ownLeaf_armD`, `stoLeaf_armD`) for a pair G
of readings of leaf queries, a way e2 of writing the body of a leaf of an own tree over the second
interface L2, and a way embE2 for a stored symbol. It asks that G reads `e2 s x sym` as the format's
spelling of that leaf, reads `embE2 y` as the body `embX` of y, and keeps the salt. Here the three
are written, from a one-to-one correspondence bd of L2's bodies with bit strings: G is
`LinkAlongM.leafM` at bd (OnBytes/TypedOracleCompiler/Run/LinkAlongM.lean); a body over L2 is what bd reads as the
bit string. Where L2's bodies are bit strings, bd is the identity.

Main definitions.
 `ownAt bd e1`        the body over L2 that bd reads as the bit string that a way e1 writes for a
                     tree's form, a place and a column. At the use e1 is the format's spelling of
                     a leaf under 164.
 `stoAt bd a sB c`    the body over L2 that bd reads as the body `embX a sB c` of a stored symbol
                     (OnBytes/TypedOracleCompiler/StringsStoredAt.lean).
Main theorems.
 `ali_selO`, `ali_selS`   what is asked of G, e2 and embE2, at these three.
 `ali_liftT`, `ali_lift`  a way of writing a tree's columns, followed by a function f and lifted
                     over rounds' lists of trees, is the way lifted, followed by f.
 `ali_emb`            so bodies over the first interface that are a way e1, lifted, are carried by f
                     to bodies that are "e1, then f", lifted.

Not claimed. That there is a bd at any interface. That a compiled verifier's wire over L2 writes
these bodies. Nothing on soundness.


-/
import OnBytes.TypedOracleCompiler.Run.ArmLaws
import OnBytes.TypedOracleCompiler.Run.LinkAlongM
import OnBytes.TypedOracleCompiler.Slice.Batch3SWhole

set_option autoImplicit false

namespace TypedOracleCompiler.Run.ArmLeafId
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.LinkAlong TypedOracleCompiler.Run.LinkAlongM TypedOracleCompiler.Strings
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run
open _root_.Run.PQ (SgX)

section
variable {I0 X0 I2 X2 : Type} (L0 : _root_.Iop.BatchProtocol I0 X0) (L2 : BatchProtocolWithLeafBody I2 X2)
  (bd : L2.Bd ≃ (strung L0).Bd)

/-- The body over L2 of a leaf of an own tree, from a way e1 of writing it as a bit string. -/
def ownAt (e1 : Enc1 (List Bool)) : Enc1 (Body L2) := fun s x sym => bd.symm (e1 s x sym)

/-- The body over L2 of a stored symbol. -/
def stoAt (a sB : ℕ) (c : StrCode (ℕ × List UInt64)) : SgX → Body L2 :=
  fun y => bd.symm (embX a sB c y)

/-- The pair reads the body of a leaf of an own tree as the bit string and keeps the salt. -/
theorem ali_selO (e1 : Enc1 (List Bool)) (s : _root_.Fmt.Shape) (x : Fin (2 ^ s.a))
    (sym : Fin s.W → UInt64) (z : Bits) :
    (leafM (strung L0) L2 bd).sel ⟨ownAt L0 L2 bd e1 s x sym, z⟩ = some ⟨e1 s x sym, z⟩ := by
  show some (⟨bd (bd.symm (e1 s x sym)), z⟩ : LeafIn (strung L0)) = _
  rw [Equiv.apply_symm_apply]

/-- The pair reads the body of a stored symbol as the body `embX` of it, and keeps the salt. -/
theorem ali_selS (a sB : ℕ) (c : StrCode (ℕ × List UInt64)) (y : SgX) (z : Bits) :
    (leafM (strung L0) L2 bd).sel ⟨stoAt L0 L2 bd a sB c y, z⟩ = some ⟨embX a sB c y, z⟩ := by
  show some (⟨bd (bd.symm (embX a sB c y)), z⟩ : LeafIn (strung L0)) = _
  rw [Equiv.apply_symm_apply]

end

/-! ## A way, followed by a function, lifted -/

section
variable {A B : Type} (f : A → B) (e1 : Enc1 A)

/-- In a round's list of trees. -/
theorem ali_liftT : ∀ (ts : List _root_.Fmt.Shape) (p : PQ.PosT ts) (a : PQ.SymT ts p),
    liftT (fun s x sym => f (e1 s x sym)) ts p a = f (liftT e1 ts p a)
  | _ :: _, .inl _, _ => rfl
  | _ :: ts, .inr p, a => ali_liftT ts p a

/-- In a list of rounds. -/
theorem ali_lift (C : PQ.CK) : ∀ (ds : List PQ.RD) (p : OPos (PQ.uL C ds))
    (a : OSym (PQ.uL C ds) p),
    embLS C (liftT fun s x sym => f (e1 s x sym)) ds p a = f (embLS C (liftT e1) ds p a)
  | [], p, _ => p.elim
  | d :: _, .inl p, a => ali_liftT f e1 d.trees p a
  | _ :: ds, .inr q, a => ali_lift C ds q a

/-- Bodies that are a way e1, lifted, are carried by f to bodies that are "e1, then f", lifted. -/
theorem ali_emb (C : PQ.CK) (ds : List PQ.RD)
    (embS : (p : OPos (_root_.Run.Twin.up (PQ.SOf C ds))) →
      OSym (_root_.Run.Twin.up (PQ.SOf C ds)) p → A)
    (h : ∀ q a, embS (.inr q) a = embLS C (liftT e1) ds q a) (q : OPos (PQ.uL C ds))
    (a : OSym (PQ.uL C ds) q) :
    f (embS (.inr q) a) = embLS C (liftT fun s x sym => f (e1 s x sym)) ds q a := by
  rw [ali_lift, h]

end

end TypedOracleCompiler.Run.ArmLeafId
