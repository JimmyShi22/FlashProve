-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/LibLetters.lean: THE TWO OTHER RECORDS OF LETTERS, Wide AND More (Law/LibJoin.lean), AS THEOREMS AT THE SEAT's OWN LETTERS (Johnson/Stored/HeadSeatAt.lean: sizesOf h · requestOf s · the heard token y); beside Law/LibAtSeat.lean's same_at: STATED AND PROVED. WITH THEM: THE FOUR PARTS AT THE SEAT GIVE Policy.HeadCl AT Hd.npOf h | polOf h.
  wide_at        FullH h (Johnson/Road/HeadPlace.lean: the library's nine equations on the head's public numbers) and h.famF = 24 ⇒ Wide at sizesOf h. **NO PADDING IS NO PREMISE HERE**: the shape's ls IS la − lt (OnBytes/Model/HeadLayout.lean), 6 under FullH: a block has 64 features, and 202048 is a multiple of 64: JV = V. (JV = V follows from no test which the kind's planOk
                 names: it follows from the shape's make and FullH.)
  more_at        h.digSh = 8 · the record's tokens are the instance's (at every position below T) · y is the instance's next token ⇒ More (Req.of pol x): JVa = 131072 by computing; the checked tokens agree.
  headCl_at      HeadParts at the seat's letters ⇒ Policy.HeadCl (Hd.npOf h) (polOf h) Wz x (cellsN c).
WHAT IT DOES NOT SAY. PREMISES THAT STAY: FullH h · h.digSh = 8 (a public number; the plan's tests admit 7) · **THE RECORD IS THE INSTANCE's**: s.rowR = x.r · s.rowE = x.e · s.tokv's entries are x's tokens · y = x.y: the frame's tie: typed by nobody here · the tests on the plan and the request · y < V · tab is the library's EX on 16 bits · c.Wh is the output matrix · HeadParts itself (Law/LibParts.lean says whose
each part is). That cellsN c is what the committed integers spell. SmallH; "y = 0 if e < T". FULL SIZE ALONE. No chance in it.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.LibAtSeat
import Johnson.Desc.Kinds.Law.LibParts

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open OnBytes (E)
open Inst.Model (AcceptancePolicy Mat ppref Instance)
open Inst.Model.Head (Req)
open OnBytes.Road.Hd (FullH)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds.HeadJoin (Same Wide More cellsN)
open Norm (lt ls d lPd S2 T)

/-- A block has 64 features at the seat's sizes. -/
theorem s2_at (h : OnBytes.Model.Head.Shape) (hF : FullH h) :
    (letI := sizesOf h
     S2) = 64 := by
  show 2 ^ h.ls = 64
  unfold OnBytes.Model.Head.Shape.ls
  rw [hF.la, hF.lt]

/-- The vocabulary has no padding at the seat's sizes. -/
theorem jv_at (h : OnBytes.Model.Head.Shape) (hF : FullH h) : @JV (sizesOf h) = 202048 := by
  unfold JV
  rw [s2_at h hF]
  show (h.V + 64 - 1) / 64 * 64 = 202048
  rw [hF.V]

/-- **Wide at the seat's own letters.** -/
theorem wide_at (h : OnBytes.Model.Head.Shape) (hF : FullH h) (h24 : h.famF = 24) :
    @Wide (sizesOf h) :=
  @Wide.mk (sizesOf h) hF.d hF.V (jv_at h hF) h24 (by rw [s2_at h hF])

/-- **More at the seat's own letters.** -/
theorem more_at (h : OnBytes.Model.Head.Shape) (s : S) (y : Nat) (pol : AcceptancePolicy) (x : Instance ppref)
    (hF : FullH h) (h8 : h.digSh = 8) (htok : ∀ t, t < 1024 → s.tokv.getD t 0 = x.tok t)
    (hy : y = x.y.val) : @More (sizesOf h) (requestOf s) ⟨y⟩ (Req.of pol x) :=
  @More.mk (sizesOf h) (requestOf s) ⟨y⟩ _ h8
    (by
      unfold JVa
      rw [jv_at h hF]
      rfl)
    (fun t => by
      show x.tok (t + 1) = if t + 1 < 2 ^ h.lt then s.tokv.getD (t + 1) 0 else y
      rw [hF.lt]
      by_cases ht : t + 1 < 2 ^ 10
      · rw [if_pos ht, htok (t + 1) ht]
      · have ht' : ¬ t + 1 < ppref.T := ht
        rw [if_neg ht, hy]
        unfold Instance.tok
        rw [dif_neg ht'])

/-- **THE FOUR PARTS AT THE SEAT GIVE HeadCl AT Hd.npOf h | polOf h.** -/
theorem headCl_at (h : OnBytes.Model.Head.Shape) (work : Nat) (s : S) (y : Nat)
    (x : Instance ppref) (Wz : Mat) (floor : Nat) (tab : Nat → Nat) (c : NCells) (hF : FullH h)
    (h8 : h.digSh = 8) (hr : s.rowR = x.r) (he : s.rowE = x.e)
    (htok : ∀ t, t < 1024 → s.tokv.getD t 0 = x.tok t) (hy : y = x.y.val)
    (hplan : (parOf h work).ok = true) (hreq : (parOf h work).okStart (requestOf s) = true)
    (hyV : y < h.V) (htab : ∀ u, u < 2 ^ 16 → (tab u : Int) = Inst.Model.EX u)
    (hW : c.Wh = (Inst.Model.Layout.weightsOf ppref Inst.Model.Layout.kRef Wz).H)
    (P : @HeadParts (sizesOf h) (parOf h work).policy (requestOf s) ⟨y⟩ floor tab c) :
    _root_.Policy.HeadCl (OnBytes.Road.Hd.npOf h) (OnBytes.Road.Hd.polOf h) Wz x (cellsN c) :=
  @headCl_of_parts (sizesOf h) (parOf h work).policy (requestOf s) ⟨y⟩ h.tabS floor tab c
    (OnBytes.Road.Hd.polOf h) Wz x hplan hreq hyV (same_at h work s x hF hr he)
    (wide_at h hF (by
      letI := sizesOf h
      letI : Policy := (parOf h work).policy
      letI := requestOf s
      letI : Token := ⟨y⟩
      exact (planFacts (sT := h.tabS) hplan).hF))
    (more_at h s y _ x hF h8 htok hy) htab hW P

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.wide_at
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.more_at
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.headCl_at
