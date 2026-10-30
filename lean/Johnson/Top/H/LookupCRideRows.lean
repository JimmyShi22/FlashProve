-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/LookupCRideRows.lean: the lookup of a sub-proof with riders, as a kind of block whose
joint behind the block says the number of rows.

Johnson/Top/H/LookupCRide.lean has the kind kLookupCR: the lookup of a sub-proof with a family of
second claims that ride through it. By type the list of rows in its out-statement has any length. As
in Johnson/Top/H/LookupCRows.lean for the kind without riders, the number of rows is put into the
condition of the joint behind the block, and paid by the block's own run.

What the file states.
 - onAnd B P: the joint B with one clause P more in its condition on statements; relations and core
   are B's. knowAt_onAnd: a block that has all four facts of a block (KnowAt) from A to B has them
   from A to onAnd B P, with the same extractor and error counts, if every statement that its
   verifier puts out has P.
 - kLookupCRN L: the kind kLookupCR L, to the letter (reduction, extractor, error counts, the joint
   before the block), but for the joint behind the block: with the clause "the list of rows has
   length Fo.nRows r.c.h" in its condition.
 - lookupCRN_knowAt, lookupCRN_good: all four facts of a block at every caller of the list, and the
   property of a block over the caller's signature, under the premises of lookupCR_knowAt and
   lookupCR_good, to the letter.
 - lookupCRN_R: the reduction is that of the lookup without riders.

Limits. Those of LookupCRide.lean. The condition says the number of rows and nothing else of them.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Top.H.LookupCRide
import Johnson.Top.H.LookupCRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open Iop Prob Hiop IOR Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole
open Cb.Fo Cb.Rider

/-- A joint with one clause more in its condition on statements. -/
@[reducible] def onAnd {K X W : Type} {E : ExtSpec} (B : IOR.Rels K X E W)
    (P : X × E.Str → Prop) : IOR.Rels K X E W :=
  ⟨B.rel, B.relR, fun b => B.on b ∧ P b, B.core⟩

/-- A condition born of the run. -/
theorem knowAt_onAnd {K M Xi Xo Wi Wo : Type} {Ei Eo : ExtSpec} {R : IOR Xi Ei Xo Eo}
    {A : IOR.Rels K Xi Ei (M × Wi)} {B : IOR.Rels K Xo Eo (M × Wo)}
    {ext : M → Xi × Ei.Str → Tr R.shape → Wo → Wi} {ε : Err R.shape} (g : KnowAt R A B ext ε)
    (P : Xo × Eo.Str → Prop) (hP : ∀ a τ b, R.red.out a τ = some b → P b) :
    KnowAt R A (onAnd B P) ext ε :=
  knowAt_into g (fun b hb hr => hr.elim fun a ha => ha.elim fun τ hτ => ⟨hb, hP a τ b hτ.2⟩)
    fun _ _ _ _ hw => hw

/-- The lookup of a sub-proof with riders; the joint behind says the number of rows. -/
@[reducible] noncomputable def kLookupCRN (L : List LookupCRCaller) : BaseKind.{1} Cb.Gl.E :=
  { kLookupCR L with
    B := fun r => onAnd (withRider (forOut Cb.Gl.E r.c.h r.c.L r.c.R0 r.c.msg₀) r.tgt)
      fun b => b.1.2.2.length = Fo.nRows r.c.h }

theorem lookupCRN_knowAt (L : List LookupCRCaller) (hL : OkLookupC (callersCR L))
    (hs : SelLookupCR L) : (kLookupCRN L).KnowAtAll :=
  fun r hr => knowAt_onAnd (lookupCR_knowAt L hL hs r hr) _
    fun a τ b hb => Fo.out_rows_len r.c.h r.c.L r.c.Ex a τ b hb

theorem lookupCRN_good (L : List LookupCRCaller) (hL : OkLookupC (callersCR L))
    (hs : SelLookupCR L) : ∀ r ∈ L, ((kLookupCRN L).toKind.block r).Good :=
  BaseKind.good_of_knowAt (lookupCRN_knowAt L hL hs)

/-- The reduction is that of the lookup without riders. -/
theorem lookupCRN_R (L : List LookupCRCaller) (r : LookupCRCaller) :
    (kLookupCRN L).R r = (kLookupCN [r.c]).R r.c := rfl

#print axioms VerifiableInference.OnPublicFiles.knowAt_onAnd
#print axioms VerifiableInference.OnPublicFiles.lookupCRN_knowAt
#print axioms VerifiableInference.OnPublicFiles.lookupCRN_good

end VerifiableInference.OnPublicFiles
