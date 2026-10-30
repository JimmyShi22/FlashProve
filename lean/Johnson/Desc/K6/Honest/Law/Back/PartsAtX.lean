-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K6/Honest/Law/Back/PartsAtX.lean: THE WAY BACK OF `headCl_atX`
(Johnson/Desc/Kinds/Law/HeadPartsAtX.lean). That theorem goes from the output head's parts, at a
request made of an instance, to the library's relation `Policy.HeadCl`. Here: from `Policy.HeadCl`
to three of the parts, under the same public premises. Statements with their proofs.

What it is not. An implication: CONDITIONAL on `FullH h` (the full size alone), h.digSh = 8, the
tests on the plan, `Head3 x`, "tab is the library's EX on 16 bits", "c.Wh is the index's output
matrix", and `Policy.HeadCl` itself. The part "small" is not here. That `cellsN c` is what the
committed integers spell is not here. No chance in it. Nothing on soundness, completeness or hiding.

  `tab_zero_of_EX`   a table that is the library's EX on 16 bits holds 2^24 in row 0
  `parts_atX`        CONDITIONAL: "idn" (`IdnPlain`); every place of every call's key table is a row
                     of the call's table, at every column; the rider's two lines are 0 at every
                     position

How. No arithmetic is done here. The four lemmas beneath are called at the letters sizesOf h, the
policy of parOf h work, reqX x and the token x.y; the structures of letters that they ask (`Same`,
`Wide`, `More`), the test on the request and "the token is below V" are made as `headCl_atX` makes
them.

-/
import Mathlib
import Inst.Model.TablesSanity
import Johnson.Desc.K6.Honest.Law.Back.KeysOfHeadCl
import Johnson.Desc.K6.Honest.Law.Back.IdnOfHeadCl

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open Inst.Model (AcceptancePolicy Mat Instance ppref)
open OnBytes.Road.Hd (FullH)
open VerifiableInference.Desc.Kinds.HeadJoin (cellsN)
open Norm (lt ls d S2 T)

/-- A table that is the library's EX on 16 bits holds 2^24 in row 0: by the library's tab9
(Inst/Model/TablesSanity.lean). -/
theorem tab_zero_of_EX (tab : Nat → Nat)
    (htab : ∀ u, u < 2 ^ 16 → (tab u : Int) = Inst.Model.EX u) : tab 0 = 2 ^ 24 := by
  have e : (tab 0 : Int) = 2 ^ 24 :=
    (htab 0 (by norm_num)).trans Inst.Model.TablesSanity.tab9.1
  exact_mod_cast e

/-- **THE LIBRARY's RELATION AT A REQUEST MADE OF THE INSTANCE GIVES THE THREE PARTS BACK**: the way
back of `headCl_atX` (Johnson/Desc/Kinds/Law/HeadPartsAtX.lean), under that theorem's own
premises. -/
theorem parts_atX (h : OnBytes.Model.Head.Shape) (work : Nat) (x : Instance ppref) (Wz : Mat)
    (tab : Nat → Nat) (c : NCells) (hF : FullH h) (h8 : h.digSh = 8)
    (hplan : (parOf h work).ok = true) (h3 : Inst.Model.Head3 x)
    (htab : ∀ u, u < 2 ^ 16 → (tab u : Int) = Inst.Model.EX u)
    (hW : c.Wh = (Inst.Model.Layout.weightsOf ppref Inst.Model.Layout.kRef Wz).H)
    (H : _root_.Policy.HeadCl (OnBytes.Road.Hd.npOf h) (OnBytes.Road.Hd.polOf h) Wz x (cellsN c)) :
    letI : Sizes := sizesOf h
    letI : Policy := (parOf h work).policy
    letI : Request := reqX x
    letI : Token := ⟨x.y.val⟩
    IdnPlain (sizesOf h) (parOf h work).policy (reqX x) c ∧
      (∀ call, call < 6 → ∀ col t, t < T → InTable tab call (keyTable c call col t)) ∧
      ∀ t, t < T → clipAt c.toCells (corner 0 t) = 0 ∧ tableAt c.toCells (corner 0 t) = 0 := by
  -- the test on the request, and "the token is below V": as headCl_atX has them
  have hreq : (parOf h work).okStart (reqX x) = true := okStart_atX h work x hF h3
  have hy : x.y.val < h.V := by
    rw [hF.V]
    exact x.y.isLt
  -- the tests on the plan say that row 0 of the table is to hold 2^24
  have h24 : h.famF = 24 := by
    letI := sizesOf h
    letI : Policy := (parOf h work).policy
    letI := reqX x
    letI : Token := ⟨x.y.val⟩
    exact (planFacts (sT := h.tabS) hplan).hF
  have h0 : tab 0 = 2 ^ h.famF := by
    rw [h24]
    exact tab_zero_of_EX tab htab
  -- the three structures of letters
  have S := same_atX h work x hF
  have Wd := wide_at h hF h24
  have M := more_atX h (OnBytes.Road.Hd.polOf h) x hF h8
  exact
    ⟨@idnPlain_of_headCl (sizesOf h) (parOf h work).policy (reqX x) c (OnBytes.Road.Hd.polOf h) Wz
        x S hF.d H,
      @calls_of_keys (sizesOf h) (parOf h work).policy (reqX x) ⟨x.y.val⟩ h.tabS tab c hplan h0
        (@keys_of_headCl (sizesOf h) (parOf h work).policy (reqX x) ⟨x.y.val⟩ h.tabS tab c
          (OnBytes.Road.Hd.polOf h) Wz x hplan hreq hy S Wd M htab hW H),
      @rider_of_headCl (sizesOf h) (parOf h work).policy (reqX x) ⟨x.y.val⟩ h.tabS c
        (OnBytes.Road.Hd.polOf h) Wz x hplan S Wd H⟩

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.tab_zero_of_EX
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.parts_atX
