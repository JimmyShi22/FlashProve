-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HonestOfHeadCl.lean: FROM THE LIBRARY's CLAUSES ON THE OUTPUT HEAD
(Policy/Seg/Head.lean: HeadCl: every key of the nine families is an entry of its table; the 17
identities; the ledger's two lines at every position; its two sums), at the library's structure of
cells made of the sub-protocol's (cellsN c), BACK TO WHAT THE HONEST SIDE OF THE SUB-PROTOCOL "the
output head's own rounds" IS ASKED OF ITS CELLS: the normalization's 17 identities at every position
((dataOf c).Holds), HonestHead c.toCells (Kinds/Law/OpenedHead.lean), and the nine keys' fields
(NineKeys, Kinds/Law/OutCallBack.lean). Statements and proofs, by calls.

What it is not. CONDITIONAL: HeadCl at cellsN c is a premise; so are the letters Same, Wide and
More, the tests on the plan and the request, "the next token is a token", "the table is the
library's EX on 16 bits", "c.Wh is the output matrix that the library reads, as functions", and the
library's clause Small. THE FULL SIZE ALONE (1,024 positions, width 5,120, vocabulary 202,048). One
way alone. The two sums and the 17 identities are 0 MODULO THE FIELD's PRIME: that they are 0 as
integers is not concluded here (what they mean over the integers: Honest/K6/Law/TraceCellsSays.lean,
at a trace). IT NAMES NO TRACE: at which cells HeadCl holds is not said here. No verifier's state,
no round and no run stands in it. It reads nothing of the honest prover's definitions. Nothing on
soundness, on completeness or on what a proof hides.

  honest_of_headCl   at any letters that meet Same, Wide and More.
  honest_atX         at the letters of a full-size shape h and a request made of an instance x.
CALLED: nine_of_headCl (Kinds/Law/LibBackWhole.lean), plain_of_lib (Kinds/Law/PlainOfLib.lean),
parts_of_plain, same_atX, more_atX, okStart_atX (Kinds/Law/HeadPartsAtX.lean), wide_at
(Kinds/Law/LibLetters.lean), holds_of_rows (Kinds/Law/NormJoint.lean), planFacts.
-/
import Johnson.Desc.Kinds.Law.PlainOfLib
import Johnson.Desc.Kinds.Law.LibBackWhole
import Johnson.Desc.Kinds.Law.HeadPartsAtX
import Johnson.Desc.Kinds.Law.OpenedHead
import Johnson.Desc.Kinds.Law.NormJoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open OnBytes (E)
open Inst.Model (ppref AcceptancePolicy Mat Instance)
open OnBytes.Road.Hd (FullH)
open VerifiableInference.Desc.Kinds.HeadJoin
open Norm (lt ls d S2 T)

/-- **THE LIBRARY's CLAUSES GIVE WHAT THE HONEST SIDE IS ASKED OF ITS CELLS.** CONDITIONAL: on all
the premises that the head of this file lists. -/
theorem honest_of_headCl [Sizes] [Policy] [Request] [Token] (sT : Nat) (tab : Nat → Nat)
    (c : NCells) (pol : AcceptancePolicy) (Wz : Mat) (x : Instance ppref) (hplan : planOk sT = true)
    (hreq : Request.ok = true) (hy : Token.y < V)
    (S : Same (Inst.Model.Head.Req.of pol x)) (Wd : Wide)
    (M : More (Inst.Model.Head.Req.of pol x))
    (htab : ∀ u, u < 2 ^ 16 → (tab u : Int) = Inst.Model.EX u)
    (hW : c.Wh = (Inst.Model.Layout.weightsOf ppref Inst.Model.Layout.kRef Wz).H)
    (small : Inst.Model.Head.Small (cellsN c))
    (h : _root_.Policy.HeadCl npOf pol Wz x (cellsN c)) :
    (dataOf c).Holds ∧ HonestHead c.toCells ∧ NineKeys tab c := by
  obtain ⟨hN, hG⟩ := nine_of_headCl sT tab c pol Wz x hplan hreq hy S Wd M htab hW small h
  have hP : IdnPlain ‹Sizes› ‹Policy› ‹Request› c :=
    plain_of_lib S Wd.d h.2.1 h.2.2.2.1 h.2.2.2.2
  obtain ⟨⟨hm, hc⟩, hr⟩ := parts_of_plain c hP
  exact ⟨holds_of_rows c hr, ⟨hG, hm, hc⟩, hN⟩

/-- **THE SAME AT A FULL-SIZE SHAPE AND A REQUEST MADE OF AN INSTANCE.** The letters are paid as
headCl_atX (Kinds/Law/HeadPartsAtX.lean) pays them on the way there. -/
theorem honest_atX (h : OnBytes.Model.Head.Shape) (work : Nat) (x : Instance ppref) (Wz : Mat)
    (tab : Nat → Nat) (c : NCells) (hF : FullH h) (h8 : h.digSh = 8)
    (hplan : (parOf h work).ok = true) (h3 : Inst.Model.Head3 x)
    (htab : ∀ u, u < 2 ^ 16 → (tab u : Int) = Inst.Model.EX u)
    (hW : c.Wh = (Inst.Model.Layout.weightsOf ppref Inst.Model.Layout.kRef Wz).H)
    (small : Inst.Model.Head.Small (cellsN c))
    (hcl : _root_.Policy.HeadCl (OnBytes.Road.Hd.npOf h) (OnBytes.Road.Hd.polOf h) Wz x
      (cellsN c)) :
    letI := VerifiableInference.Desc.Kinds.Head.sizesOf h
    letI : Policy := (parOf h work).policy
    letI := reqX x
    letI : Token := ⟨x.y.val⟩
    (dataOf c).Holds ∧ HonestHead c.toCells ∧ NineKeys tab c :=
  @honest_of_headCl (VerifiableInference.Desc.Kinds.Head.sizesOf h) (parOf h work).policy (reqX x)
    ⟨x.y.val⟩ h.tabS tab c
    (OnBytes.Road.Hd.polOf h) Wz x hplan (okStart_atX h work x hF h3)
    (by
      show x.y.val < h.V
      rw [hF.V]
      exact x.y.isLt)
    (same_atX h work x hF)
    (wide_at h hF (by
      letI := VerifiableInference.Desc.Kinds.Head.sizesOf h
      letI : Policy := (parOf h work).policy
      letI := reqX x
      letI : Token := ⟨x.y.val⟩
      exact (planFacts (sT := h.tabS) hplan).hF))
    (more_atX h _ x hF h8) htab hW small hcl

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.honest_of_headCl
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.honest_atX
