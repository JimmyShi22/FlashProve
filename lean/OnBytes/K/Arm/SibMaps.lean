-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/SibMaps.lean: the maps of an object whose Link is the written link over letters agree
with the maps at which the entry's lax verifier is shown to say yes, if the letters are the
description's own, by proofs.

`sameRun_sib` (OnBytes/K/Arm/SameSib.lean) and `link_arm2` (OnBytes/K/Arm/LinkArm2.lean)
ask that the two ways of writing a symbol of the chain's own trees agree,
that the two ways of writing a plain part agree, and that the two ways of writing a stored table's
symbol agree. Over letters (a kit C, rounds' data ds, a depth a, a number salt of salt bytes) the
object's maps are: a leaf's own string (`StringsList.embT`), the identity, and `bodyS`'s. For proofs
only; the program does not import this file.

Main definitions: `pbEq`, `pbSib`.
Main theorems.
 `embT_sib`       `StringsList.embT salt C ds` agrees with `(ownES D hok).emb`.
 `embE_sib`       `(bodyS a salt).embE` is `(bodyS D.a D.base.plan.salt).embE`.
 `way_sib`        the identity on plain parts over the letters agrees with "the way `wayE` of plain
                  parts (OnBytes/TypedOracleCompiler/Run/RowsE2.lean), then back along `pbSib`".
 `trAns_sib_inj`  `OnBytes.Flat.trAns` is one to one.

What is not claimed. That the letters at any size are a description's. Nothing on soundness.


-/
import OnBytes.TypedOracleCompiler.Slice.PartChainStr
import OnBytes.TypedOracleCompiler.Run.RowsE2
import OnBytes.Flat.LinkSib

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Arm
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.RowsE2 TypedOracleCompiler.Run.EntryFb
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD SOf bodyS pbTo)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (SgX CK)

/-- Plain parts under two equal markings of one shape. -/
def pbEq {s : Shape} {A A' : RoundSplits s} (e : A = A') : PlainPart s A ≃ PlainPart s A' where
  toFun := pbTo e
  invFun := pbTo e.symm
  left_inv := fun z => by subst e; rfl
  right_inv := fun z => by subst e; rfl

variable (D : XD) (C : CK) (ds : List PQ.RD)

/-- Plain parts of the written link over letters, every round marked local by `Twin.allLo`, against
plain parts over the description's own letters under `RoundSplits.allLocal`. -/
def pbSib (hC : C = D.C) (hds : ds = D.ds) :
    PlainPart (_root_.Run.Twin.up (SOf C ds)) (_root_.Run.Twin.allLo (SOf C ds)) ≃
      PlainPart (_root_.Run.Twin.up (SOf D.C D.ds)) (RoundSplits.allLocal (_root_.Run.Twin.up (SOf D.C D.ds))) :=
  by
    subst hC hds
    exact pbEq (_root_.Run.Twin.allLo_eq (SOf D.C D.ds))

/-- **The chain's own symbols.** -/
theorem embT_sib (hok : TypedOracleCompiler.Run.PQ.ok D.base = true) (salt : ℕ) (hC : C = D.C)
    (hds : ds = D.ds) (hsalt : salt = D.base.plan.salt) :
    HEq (TypedOracleCompiler.StringsList.embT salt C ds) (ownES D hok).emb := by
  subst hC hds hsalt
  rfl

/-- **The stored tables' symbols.** -/
theorem embE_sib (a salt : ℕ) (ha : a = D.a) (hsalt : salt = D.base.plan.salt) :
    (bodyS a salt).embE = (bodyS D.a D.base.plan.salt).embE := by
  subst ha hsalt
  rfl

/-- **The plain parts.** -/
theorem way_sib {Sd : Type} (early : (List T3 × List T3) × Sd → (List T3 × List T3) × Sd)
    (e : _root_.Fmt.Entry) (hC : C = D.C) (hds : ds = D.ds) :
    HEq (id : PlainPart (_root_.Run.Twin.up (SOf C ds)) (_root_.Run.Twin.allLo (SOf C ds)) → _)
      (fun z => (pbSib D C ds hC hds).symm (wayE D early e z)) := by
  subst hC hds
  refine heq_of_eq (funext fun z => ?_)
  show z = (pbEq (_root_.Run.Twin.allLo_eq (SOf D.C D.ds))).symm (wayE D early e z)
  rw [wayE_pbTo]
  exact ((pbEq (_root_.Run.Twin.allLo_eq (SOf D.C D.ds))).symm_apply_apply z).symm

/-- **The typed answers as triples** (`OnBytes.Flat.trAns`, the function that stands in the instance
`recX` made of two records) are written one to one: `anT` reads them back. -/
theorem trAns_sib_inj {v s : ℕ} : Function.Injective (OnBytes.Flat.trAns (v := v) (s := s)) :=
  fun a b h => by rw [← OnBytes.Flat.anT_trAns a, ← OnBytes.Flat.anT_trAns b, h]

end OnBytes.K.Arm
