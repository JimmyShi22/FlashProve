-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3CallerHeadTests.lean: THE PREMISES ON PUBLIC DATA UNDER THE CALLER OF THE
LOOKUP ON THE HEAD's LINK's CALLS (HeadOK, K3CallerHead.lean; HeadTabs, K3CallerHeadParts.lean) AS
TWO BOOLS WITH CODE, and the theorems that a yes gives the premise. Definitions with code,
statements and proofs. NO SOUNDNESS IS CLAIMED.

OBJECT: no text that runs: two functions to Bool of a lookup's record and place.
USER: K3AsksHeadLaw.lean, K3HeadStated.lean (headOK_of).
LETTERS: floor, h, x, sT; K6's classes Sizes, Policy, Request.
Compiled with the whole library.



Main names:
  `headB floor h`: six calls · lt ≤ dT · lJ floor (callKeys c) + lt ≤ n_c at each c < 6.
  `headJustB floor h`: lJ floor (callKeys c) + lt = n_c at each c < 6 (more than HeadOK asks).
  `headTabsB x sT`: K6's planOk · its rowsOk at the record's own rows · k_c = bitsOf c.
  `headOK_of`, `headTabs_of`: a yes gives the premise.
Limits. A yes at a public record is an evaluation's matter, and hangs on how K6's classes are
filled from that record.
Not claimed: the soundness of any text that runs; anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallerHeadParts

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open Norm (lt)
open VerifiableInference.Desc.First.Look

variable [Sizes] [Policy] [Request]

def headB (floor : ℕ) (h : OnBytes.Model.Forest.Shape) : Bool :=
  h.NC == 6 && decide (lt ≤ h.dT) &&
    (List.range 6).all fun c => decide (lJ floor (callKeys c) + lt ≤ FoNums.nOf h c)

def headJustB (floor : ℕ) (h : OnBytes.Model.Forest.Shape) : Bool :=
  (List.range 6).all fun c => lJ floor (callKeys c) + lt == FoNums.nOf h c

def headTabsB (x : First.Look.Place) (sT : ℕ) : Bool :=
  planOk sT && rowsOk (rowH x) && (List.range 6).all fun c => FoNums.kOf x.fs c == bitsOf c

/-- **A yes of headB gives HeadOK.** -/
theorem headOK_of {set : OnBytes.Params.Setting} {x : First.Look.Place} {floor : ℕ}
    (hs : (P.ofPlace set false x).shape = some x.fs) (e : headB floor x.fs = true) :
    HeadOK set x floor := by
  unfold headB at e
  rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at e
  obtain ⟨⟨h1, h2⟩, h3⟩ := e
  exact ⟨hs, h1, h2, fun c hc => of_decide_eq_true (List.all_eq_true.1 h3 c (List.mem_range.2 hc))⟩

/-- **A yes of headTabsB gives HeadTabs.** -/
theorem headTabs_of {x : First.Look.Place} {sT : ℕ} (e : headTabsB x sT = true) :
    HeadTabs x sT := by
  unfold headTabsB at e
  rw [Bool.and_eq_true, Bool.and_eq_true] at e
  obtain ⟨⟨h1, h2⟩, h3⟩ := e
  exact ⟨h1, h2, fun c hc => beq_iff_eq.1 (List.all_eq_true.1 h3 c (List.mem_range.2 hc))⟩

#print axioms headOK_of
#print axioms headTabs_of

end VerifiableInference.Desc.Kinds.Head.Law
