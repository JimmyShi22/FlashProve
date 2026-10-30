-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/Families.lean: the members of a group of sent oracle messages as a family over a
signature: which names are members and what is held of each; the family over the messages that an
earlier test keeps; and the group's conditions from conditions on the family.

The group's data are `Rows` (Johnson/Top/H/GroupRows.lean), made by `Rows.ofFn`
(Johnson/Top/H/MemberOf.lean). A later test of a chain stands over the signature of the messages
that the earlier tests have kept (`Sig.sub`, Cb/Ld/LdBatSig.lean). A family is written once, over
the whole signature, and cut down. Definitions, statements and proofs.
Main names:
  `Fam S s`: which names of S are members, and `MembAt` for each member.
  `Fam.rows F e`: the group's data at the joint radius e.
  `Fam.sub F kp`: the family over the messages with kp.
  `Fam.Ok F`: every member's change of shape has its laws; every member's two blocks lie on the
    cubes; the blocks of two different members do not overlap.
  `Fam.FitsAt F e`: the joint radius implies each member's own.
  `Fam.Ok.sub`, `Fam.FitsAt.sub`: both pass to the family over the messages with kp.
  `Fam.good`, `Fam.fits`: `Rows.Good` and `Grp.Fits` of `F.rows e`.
Limits: no family is written here. That a member of the cut-down family is kept is not asked: a
name that is not kept is no name of the smaller signature. A block is here a member's rows
themselves, as many as it has: not the aligned block of a power of two of rows that the layout of
the verifier written after the programs gives a member (OnBytes/Iop/Ground.lean). That such padded
blocks of two members do not overlap is not said here.

-/
import Johnson.Top.H.MemberOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes.Slice Cb

/-- The members of a group: which names, and what is held of each. -/
structure Fam (S : Sig GE) (s : Sg) where
  mem : S.O → Prop
  [dec : DecidablePred mem]
  mb : ∀ o, mem o → MembAt (S.om o) s

attribute [instance] Fam.dec

namespace Fam
variable {S : Sig GE} {s : Sg} (F : Fam S s)

/-- The group's data. -/
@[reducible] def rows (e : ℕ) : Rows S := Rows.ofFn s e F.mem F.mb

/-- The family over the messages with kp. -/
@[reducible] def sub (kp : S.O → Prop) [DecidablePred kp] : Fam (S.sub kp) s where
  mem := fun a => F.mem a.1
  mb := fun a k => F.mb a.1 k

/-- The conditions on a family. -/
structure Ok : Prop where
  laws : ∀ o k, (F.mb o k).view.Laws
  fitM : ∀ o k, (F.mb o k).oM + (F.mb o k).nM ≤ 2 ^ (s.h + s.g)
  apartM : ∀ o k o' k', o ≠ o' →
    (F.mb o k).oM + (F.mb o k).nM ≤ (F.mb o' k').oM ∨
      (F.mb o' k').oM + (F.mb o' k').nM ≤ (F.mb o k).oM
  fitZ : ∀ o k, (F.mb o k).oZ + (F.mb o k).nZ ≤ 2 ^ s.h
  apartZ : ∀ o k o' k', o ≠ o' →
    (F.mb o k).oZ + (F.mb o k).nZ ≤ (F.mb o' k').oZ ∨
      (F.mb o' k').oZ + (F.mb o' k').nZ ≤ (F.mb o k).oZ

/-- The joint radius implies each member's own. -/
def FitsAt (e : ℕ) : Prop := ∀ o k, (F.mb o k).Fits e

variable {F}

theorem Ok.sub (h : F.Ok) (kp : S.O → Prop) [DecidablePred kp] : (F.sub kp).Ok where
  laws := fun a k => h.laws a.1 k
  fitM := fun a k => h.fitM a.1 k
  apartM := fun a k a' k' n => h.apartM a.1 k a'.1 k' fun e => n (Subtype.ext e)
  fitZ := fun a k => h.fitZ a.1 k
  apartZ := fun a k a' k' n => h.apartZ a.1 k a'.1 k' fun e => n (Subtype.ext e)

theorem FitsAt.sub {e : ℕ} (h : F.FitsAt e) (kp : S.O → Prop) [DecidablePred kp] :
    (F.sub kp).FitsAt e := fun a k => h a.1 k

theorem good (e : ℕ) (hs : s.Sized) (h1 : 1 ≤ s.h + s.g) (h : F.Ok) : (F.rows e).Good where
  sized := hs
  view := fun a => h.laws a.1 a.2
  fitM := fun r => by
    have k := h.fitM r.1.1 r.1.2
    have i := r.2.isLt
    show (F.mb r.1.1 r.1.2).oM + r.2.val < 2 ^ (s.h + s.g)
    exact lt_of_lt_of_le (Nat.add_lt_add_left i _) k
  injM := apart_inj (A := {o // F.mem o}) (fun a => (F.mb a.1 a.2).nM) (fun a => (F.mb a.1 a.2).oM)
    fun a b n => h.apartM a.1 a.2 b.1 b.2 fun e => n (Subtype.ext e)
  fitZ := fun r => by
    have k := h.fitZ r.1.1 r.1.2
    have i := r.2.isLt
    show (F.mb r.1.1 r.1.2).oZ + r.2.val < 2 ^ s.h
    exact lt_of_lt_of_le (Nat.add_lt_add_left i _) k
  injZ := apart_inj (A := {o // F.mem o}) (fun a => (F.mb a.1 a.2).nZ) (fun a => (F.mb a.1 a.2).oZ)
    fun a b n => h.apartZ a.1 a.2 b.1 b.2 fun e => n (Subtype.ext e)
  one := h1

theorem fits {e : ℕ} (h : F.FitsAt e) : (F.rows e).G.Fits :=
  Rows.ofFn_fits s e F.mem F.mb h

end Fam

end Johnson.Top.H

#print axioms Johnson.Top.H.Fam.good
#print axioms Johnson.Top.H.Fam.fits
