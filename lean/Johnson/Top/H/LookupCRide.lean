-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/LookupCRide.lean: the lookup inside a sub-proof, with a second zero test on its
challenges, as a kind of block.

What the file states.
 - LookupCRCaller: a caller of such a lookup (LookupCCaller, Johnson/Top/H/LookupC.lean) with a
   family of riders: the family's index type, each member's cube, each member's choice of places
   of the key point, and the arrays, which read the caller's state and the committed
   messages. Data alone: no field is a proof.
 - kLookupCR L: the kind of block at a list L of such callers. Reduction, extractor and errors are
   kLookupC's, to the letter. The joint before the block is kLookupC's at the caller's own joint R0
   with the source ("every array is 0 on its cube") laid inside it. The joint behind the block is
   kLookupC's at R0 alone, with the target ("the multilinear extension of every array is 0 at the
   chosen places of the key point") beside it. So the source goes in and does not come out.
 - SelLookupCR L: each member's choice is of different places among 0, .., v'.
 - lookupCR_know_of: the hypothesis of the kind kLookupC at the callers of L gives the hypothesis of
   the kind kLookupCR at L. It is used as a black box.
 - lookupCR_point_of, lookupCR_local_of, lookupCR_onOut_of: the three facts on the verifier alone
   are kLookupC's.
 - HLookupCR, a closed proposition: for every list of callers with riders whose records are of the
   written list and whose choices are lawful, round-by-round knowledge soundness of each block.
   hLookupCR_of : HLookupC → HLookupCR, and hLookupCR : HLookupCR. HLookupCREvery,
   hLookupCREvery_of, hLookupCREvery: the same for every list whose records pass the test
   FoNums.ok.
 - lookupCR_knowAt, lookupCR_good: all four facts; the property of a block over the caller's
   signature.
 - lookupCR_R, lookupCR_eps: the reduction and the errors are kLookupC's, so lookupC_small and
   lookupC_plan speak of this kind too.

An empty use. The caller's joint R0 is free. If R0 itself, or the clause "each call's keys lie in
that call's table", gives the source, the statements on kLookupCR follow from those on kLookupC
alone and say nothing of the choice (Cb.Rider.forB_hollow). For no caller is it proved here that
the source can fail while the joint before the block holds, nor that an accepted output has the
whole joint behind the block.

What the file does not say: that a caller with riders exists whose data are a sub-proof's own; that
the programs' tests are these targets; that a later block takes a target up; anything on an honest
prover.
-/
import Johnson.Top.H.LookupC
import OnBytes.Tie.Pv.Lookup.Rider.ForB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open Iop Prob Hiop IOR Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole
open Cb.Fo Cb.Rider

/-! ### the caller with riders -/

/-- Who calls a lookup of a sub-proof and tests a family of arrays on its challenges: data alone. -/
structure LookupCRCaller : Type 1 where
  /-- the caller -/
  c   : LookupCCaller
  /-- the family -/
  ι   : Type
  /-- each member's cube -/
  g   : ι → ℕ
  /-- each member's choice of places of the key point; place 0 belongs to the top bit -/
  sel : ι → ℕ → ℕ
  /-- the arrays, read off the caller's state and the committed messages -/
  f   : ι → c.St₀ → c.Sg.Msg → ℕ → Cb.Gl.E

namespace LookupCRCaller

/-- The source: every array is 0 at every vertex of its cube. -/
def src (r : LookupCRCaller) : r.c.Sg.Msg → r.c.St₀ × r.c.Ex.Str → Prop :=
  fun m a => OnCubes r.g r.f a.1 m

/-- The target: the multilinear extension of every array is 0 at the chosen places of the point of
the claim on the keys. -/
def tgt (r : LookupCRCaller) :
    r.c.Sg.Msg → TX (r.c.St₀ × Cb.Gl.E) Cb.Gl.E (Option r.c.J₀) × r.c.Ex.Str → Prop :=
  fun m b => AtCoords r.g r.sel r.f b.1.1.1 b.1.2.1.pt m

end LookupCRCaller

/-! ### the kind -/

/-- The lookup of a sub-proof with riders as a kind of block, at a written list of callers. -/
@[reducible] noncomputable def kLookupCR (L : List LookupCRCaller) : BaseKind.{1} Cb.Gl.E where
  Size := LookupCRCaller
  sizes := L
  Sg := fun r => r.c.Sg
  Kc := fun r => r.c.Kc
  St := fun r => r.c.St₀
  St' := fun r => TX (r.c.St₀ × Cb.Gl.E) Cb.Gl.E (Option r.c.J₀)
  Wp := fun r => r.c.Wp
  Wp' := fun r => r.c.Wp
  E₀ := fun r => r.c.Ex
  E₀' := fun r => r.c.Ex
  R := fun r => (forB Cb.Gl.E r.c.h r.c.L V₀ V₀C (Ex := r.c.Ex)).R
  A := fun r => forIn Cb.Gl.E r.c.h r.c.L (withRider r.c.R0 r.src) r.c.msg₀
  B := fun r => withRider (forOut Cb.Gl.E r.c.h r.c.L r.c.R0 r.c.msg₀) r.tgt
  ext := fun _ _ _ _ wp => wp
  ε := fun r => (forB Cb.Gl.E r.c.h r.c.L V₀ V₀C (Ex := r.c.Ex)).e

/-- The callers of a list of callers with riders. -/
def callersCR (L : List LookupCRCaller) : List LookupCCaller := L.map (·.c)

/-- Each member's choice is of different places among 0, .., v'. -/
def SelLookupCR (L : List LookupCRCaller) : Prop :=
  ∀ r ∈ L, SelIn (FoNums.v' r.c.h) r.g r.sel

theorem mem_callersCR {L : List LookupCRCaller} {r : LookupCRCaller} (hr : r ∈ L) :
    r.c ∈ callersCR L := List.mem_map_of_mem hr

/-- From the hypothesis of the kind without riders to the hypothesis of the kind with riders: the
same reductions, extractors and errors. -/
theorem lookupCR_know_of (L : List LookupCRCaller) (hs : SelLookupCR L)
    (hK : (kLookupC (callersCR L)).Know) : (kLookupCR L).Know :=
  fun r hr m => forB_rider_know (hK r.c (mem_callersCR hr)) r.g r.sel (hs r hr) r.f m

theorem lookupCR_point_of (L : List LookupCRCaller) (hp : (kLookupC (callersCR L)).Point) :
    (kLookupCR L).Point := fun r hr => hp r.c (mem_callersCR hr)

theorem lookupCR_local_of (L : List LookupCRCaller) (hl : (kLookupC (callersCR L)).Local) :
    (kLookupCR L).Local := fun r hr => hl r.c (mem_callersCR hr)

theorem lookupCR_onOut_of (L : List LookupCRCaller) (ho : (kLookupC (callersCR L)).OnOut) :
    (kLookupCR L).OnOut := fun r hr a τ b ha hb => ho r.c (mem_callersCR hr) a τ b ha hb

/-- The reduction is that of the kind without riders. -/
theorem lookupCR_R (L : List LookupCRCaller) (r : LookupCRCaller) :
    (kLookupCR L).R r = (kLookupC (callersCR L)).R r.c := rfl

/-- The errors are those of the kind without riders. -/
theorem lookupCR_eps (L : List LookupCRCaller) (r : LookupCRCaller) :
    (kLookupCR L).ε r = (kLookupC (callersCR L)).ε r.c := rfl

/-- Knowledge soundness of the lookup of a sub-proof with riders, whoever calls it, at the written
sizes. -/
def HLookupCR : Prop :=
  ∀ L : List LookupCRCaller, AtSizesLookupC (callersCR L) → SelLookupCR L → (kLookupCR L).Know

/-- From the hypothesis of the kind without riders. -/
theorem hLookupCR_of : HLookupC → HLookupCR := fun H L hL hs =>
  lookupCR_know_of L hs (H (callersCR L) hL)

theorem hLookupCR : HLookupCR := hLookupCR_of hLookupC

/-- The same at every record of public numbers that passes the test FoNums.ok. -/
def HLookupCREvery : Prop :=
  ∀ L : List LookupCRCaller, OkLookupC (callersCR L) → SelLookupCR L → (kLookupCR L).Know

theorem hLookupCREvery_of : HLookupCEvery → HLookupCREvery := fun H L hL hs =>
  lookupCR_know_of L hs (H (callersCR L) hL)

theorem hLookupCREvery : HLookupCREvery := hLookupCREvery_of hLookupCEvery

/-- All four facts of a block, at every caller whose record passes the test. -/
theorem lookupCR_knowAt (L : List LookupCRCaller) (hL : OkLookupC (callersCR L))
    (hs : SelLookupCR L) : (kLookupCR L).KnowAtAll :=
  BaseKind.knowAtAll_iff.2
    ⟨lookupCR_know_of L hs (BaseKind.know_of_knowAt (lookupC_knowAt _ hL)),
      lookupCR_point_of L (lookupC_point _ hL), lookupCR_local_of L (lookupC_local _ hL),
      lookupCR_onOut_of L (lookupC_onOut _ hL)⟩

/-- Over its caller's signature every block of the kind has the property of a block. -/
theorem lookupCR_good (L : List LookupCRCaller) (hL : OkLookupC (callersCR L))
    (hs : SelLookupCR L) : ∀ r ∈ L, ((kLookupCR L).toKind.block r).Good :=
  BaseKind.good_of_knowAt (lookupCR_knowAt L hL hs)

#print axioms VerifiableInference.OnPublicFiles.lookupCR_know_of
#print axioms VerifiableInference.OnPublicFiles.hLookupCR_of
#print axioms VerifiableInference.OnPublicFiles.hLookupCR
#print axioms VerifiableInference.OnPublicFiles.hLookupCREvery
#print axioms VerifiableInference.OnPublicFiles.lookupCR_knowAt
#print axioms VerifiableInference.OnPublicFiles.lookupCR_good

end VerifiableInference.OnPublicFiles
