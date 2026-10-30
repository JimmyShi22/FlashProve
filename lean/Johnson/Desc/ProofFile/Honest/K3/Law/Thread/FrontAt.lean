-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/FrontAt.lean: the honest side of the kind "lookup" (K3).
Conditional: from the promise of the table of borders at the border in front of a lookup's
sub-protocol to the state that the theorems on the lookup ask (`FrontOk`,
Honest/K3/Law/Thread/Front.lean). Theorems.

Terms. Honest/K3/GLOSSARY.md: see there promise, border, item, place and mark. In this file: the
table of borders is Johnson/Desc/First/Borders.lean, whose head calls it the table of joints; its
promise at a border is `onAt`.

What is shown.
  `onAt_pub`: at a state without a mark the promise holds every public test that is open or tied to
    an open item. The library has the two halves apart, at a place that is there: `Att.P.onAt_pub`
    (Johnson/Desc/First/Att/K05T2.lean: the open tests) and `onAt_tied`
    (Johnson/Desc/First/Att/Door/Law/K5LeftSmall.lean: those tied to the open items).
  `front_at_calls`: `FrontOk` at the sub-protocol of a link's lookup on the calls.
  `front_at_digits`: `FrontOk` at the sub-protocol of a link's lookup on the digits.

Hypotheses that remain, in the last two.
  `hK`: the meaning says at the lookups' own items what the lookups' layer says (the library's
    `K3At`, Johnson/Desc/First/Look/K3At.lean; it holds of the library's composed meaning:
    `k3At_mgAll`, Johnson/Desc/Sound/MgAt/K3At.lean).
  `hfit`: the test on the promise's table passes: public.
  `hk`, `hl`, `hs`, `hpc`, `hpa`: where the sub-protocol stands in the list of places and in its
    link: public.
  `hlook`: the public structure has the place.
  `hon`, `hu`: the promise at that border; the state bears no mark (`s.failed = none`). In
    `onAt_pub` these two are `h` and `hu`.

How the proof goes. A sorting by cases, and calls of the library's own lemmas.

Users. Honest/K3/Law/Thread/AtBorder.lean calls `front_at_calls` and `front_at_digits`;
Honest/K3/Law/Thread/SiteThr.lean calls `onAt_pub`.

Limits. All statements are implications. No instance of these hypotheses is exhibited in this file.
Lemmas on the verifier's side alone: no prover is named.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.First.Look.K3At
import Johnson.Desc.First.Look.K3CallsMean
import Johnson.Desc.Sound.DigitsRow
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.Front

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Aff)
open VerifiableInference.Desc (Place Strs Wit)
open VerifiableInference.Desc.K3 (seatCalls seatDigits pieceAt)
open VerifiableInference.Desc.First (ModelPart Item Numbers Meaning onAt pubHeld pubOfItems pubFit pubSets
  openSets
  start shift)
open VerifiableInference.Desc.First.Look (P Sent lookAt k3LookIn_onIn)
open VerifiableInference.Desc.Sound (MsgT digits_lookIn_open)
open VerifiableInference.OnPublicFiles (K3At K3Letters fLook_at calls_asks_open)

local notation "FS" => VerifiableInference.Desc.First.S
local notation "FPub" => VerifiableInference.Desc.First.Pub

/-- **At a state without a mark the promise holds every public test that is open or tied to
an open item.** -/
theorem onAt_pub {Pp Wt : Type} {N : Numbers} {Mg : Meaning Pp Wt} {links : List ModelPart}
    {p : Option Place}
    {O : List Item} {Q : List FPub} {a : Pp × FS} {y : Strs} (h : onAt N Mg links p O Q a y)
    (hu : a.2.failed = none) : ∀ q ∈ Q ++ pubOfItems O, Mg.pub q a = true := by
  obtain ⟨-, hm | ⟨h1, -, -, -⟩⟩ := h
  · exact absurd hu hm
  · simp only [Bool.and_eq_true] at h1
    have hp := h1.1.2
    unfold pubHeld at hp
    rw [List.all_eq_true] at hp
    exact hp

section
variable {Pp Cells Tok Cl : Type} {X : OnBytes.Model.Verify.Public} {D : Sent}
  {L : K3Letters Cells Tok}
  {Mg : Meaning Pp (Wit Cells Tok MsgT)}

/-- **The state in front of the sub-protocol of a link's lookup on the calls is as the theorems on
the lookup ask it.** Conditional on `K3At`, the table's test, the sub-protocol's place, the promise
at the border and no mark. No instance of these hypotheses is exhibited in this file. -/
theorem front_at_calls (hK : K3At X D L Mg) (claim : Aff → Cl) (N : Numbers) (links : List ModelPart)
    (ps : List Place) (k : Nat) (a : Place) (m : Nat) (sub : ModelPart)
    {x : VerifiableInference.Desc.First.Look.Place} (hfit : pubFit Mg.more links ps = true)
    (hk : ps[k]? = some a) (hl : a.link = some m) (hs : links[m]? = some sub)
    (hpc : a.piece = 2 + shift sub) (hpa : pieceAt X m false = 2 + shift sub)
    (hlook : lookAt X m false = some x) (z : Pp) (s : FS) (y : Strs)
    (hon : onAt N Mg links ps[k]? ((openSets links ps (start links))[k]?.getD [])
      ((pubSets Mg.more links ps)[k]?.getD []) (z, s) y)
    (hu : s.failed = none) :
    ∃ hh F, FrontOk (seatCalls claim)
      (P.ofPlace (OnBytes.Params.settingOf X.P.frame) false x) hh s F := by
  have hq := calls_asks_open Mg.more links ps k a m sub hfit hk hl hs hpc
    (.lookIn m (2 + shift sub)) (by simp)
  have hp := onAt_pub hon hu _ (List.mem_append_left _ hq)
  rw [← hpa] at hp
  exact front_calls claim rfl (k3LookIn_onIn (fLook_at hK m false hlook z s hp))

/-- **The same at the sub-protocol of a link's lookup on the digits.** Conditional on the same.
No instance of these hypotheses is exhibited in this file. -/
theorem front_at_digits (hK : K3At X D L Mg) (claim : Aff → Cl) (N : Numbers) (links : List ModelPart)
    (ps : List Place) (k : Nat) (a : Place) (m : Nat) (sub : ModelPart)
    {x : VerifiableInference.Desc.First.Look.Place} (hfit : pubFit Mg.more links ps = true)
    (hk : ps[k]? = some a) (hl : a.link = some m) (hs : links[m]? = some sub)
    (hpc : a.piece = 7 + shift sub) (hpa : pieceAt X m true = 7 + shift sub)
    (hlook : lookAt X m true = some x) (z : Pp) (s : FS) (y : Strs)
    (hon : onAt N Mg links ps[k]? ((openSets links ps (start links))[k]?.getD [])
      ((pubSets Mg.more links ps)[k]?.getD []) (z, s) y)
    (hu : s.failed = none) :
    ∃ hh F, FrontOk (seatDigits claim)
      (P.ofPlace (OnBytes.Params.settingOf X.P.frame) true x) hh s F := by
  have hq := digits_lookIn_open Mg.more links ps k a m sub hfit hk hl hs hpc
    (.lookIn m (7 + shift sub)) (by simp)
  have hp := onAt_pub hon hu _ (List.mem_append_left _ hq)
  rw [← hpa] at hp
  exact front_digits claim rfl (k3LookIn_onIn (fLook_at hK m true hlook z s hp))

end

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.onAt_pub
#print axioms ProofFile.Honest.K3.Law.AtThr.front_at_calls
#print axioms ProofFile.Honest.K3.Law.AtThr.front_at_digits
