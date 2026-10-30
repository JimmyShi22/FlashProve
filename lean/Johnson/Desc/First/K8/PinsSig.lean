-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/PinsSig.lean: THE SMALLNESS TEST AT THE TABLE OF JOINTS: FROM THE TABLE'S PINS
AND ITS PROMISE "NO COLLISION", WHICH SPEAK OF EACH SENDING'S OWN LIST, TO THE LAW'S, WHICH SPEAK OF
ONE LIST OF MEMBERS OF TWO SENDINGS.

The row of the block of the draw reads the items pin m 0 and pin m 1. The table's pin at a seat
says: every member of the plan's list ms that sits there is pinned, AT ITS OWN SENDING'S LIST
(`pinJT`, Johnson/Desc/Sound/MeaningSig.lean). The law `k08_rowT`
(Johnson/Desc/First/K8/LawTable.lean) has one signature over one list l with seats seat'. A member's
share of a signature hangs on its entry (shape and radius) and its seat alone: `pin_move`, `cf_move`
(Johnson/Desc/Sound/PinMove.lean). After the pattern of the lookup on the digits.
  `K8Sits`: WHAT IS ASKED OF THE LIST: every member of l has an alike member in ms; the table's
    reader of OOD samples hangs on entry and seat alone; every seat is one of the segment's first
    two sendings'; the seats fit the description.
  `smpAt`: the law's partial reader of OOD samples: the table's, at l as one sending, at the public
    part z.
  `k8_cfSig`: the promise "no collision" at the seats of the two sendings gives `CfSig` at l.
  `k8_pinSig`: pin m 0 and pin m 1 give `PinSig` at l.
  `k8_cf`, `k8_pins`: **so the law's own two: the library's "no collision" and `PinsAt`, at the
    total reader `totalOf` (Johnson/Desc/First/K8/LawPins.lean).**
Statements and proofs.
Limits. `K8Sits` is a premise: shown of no list here. Nothing on soundness.

-/
import Johnson.Desc.First.K8.LawPins
import Johnson.Desc.Sound.PinMove
import Johnson.Desc.Sound.MeaningSig
import Johnson.Desc.First.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open Cb OnBytes.Model OnBytes.Maker Johnson.Pack VerifiableInference.Desc.Sound

section
variable {P Cells Tok Xi : Type} (G : FileDescription Xi) (cs : OnBytes.Codes)
  (l : List (OnBytes.OracleShape × ℕ)) (seat' : Fin l.length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (smpT : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem) (N : Numbers) (m : ℕ)

/-- **What is asked of the list of members.** -/
structure K8Sits : Prop where
  some : ∀ i, ∃ y ∈ ms, Alike y ⟨⟨l, seat'⟩, i⟩
  bySeat : SmpBySeat cs smpT
  sent : ∀ i, ∃ t ∈ [0, 1], seat' i ∈ N.sent m t
  fits : SeatFits G cs l seat'

/-- The law's partial reader of OOD samples. -/
def smpAt (z : P) (s : S) (i : Fin l.length) : Option ((sigOf cs l).om i).Smp :=
  smpT (z, s) ⟨l, seat'⟩ i

variable {G cs l seat' smpT ms N m}

/-- The promise at the two sendings' seats, at the one list. -/
theorem k8_cfSig (T : K8Sits G cs l seat' smpT ms N m) (z : P) (s : S) (y : Strs)
    (h : ∀ t ∈ [0, 1], ∀ e ∈ N.sent m t, noCollJT cs G smpT ms e.1 e.2 (z, s) y) :
    CfSig G cs l seat' (smpAt cs l seat' smpT z) (fun _ => True) s y := by
  intro i _
  obtain ⟨u, hu, hA⟩ := T.some i
  obtain ⟨t, ht, hm⟩ := T.sent i
  have hs : SitsAt u (seat' i).1 (seat' i).2 := hA.2
  exact (cf_move cs G smpT u ⟨⟨l, seat'⟩, i⟩ hA (z, s) (T.bySeat (z, s) _ _ hA) y).1
    (h t ht (seat' i) hm u hu hs)

/-- The two pins, at the one list. -/
theorem k8_pinSig (T : K8Sits G cs l seat' smpT ms N m) (z : P) (s : S) (y : Strs)
    (w : Wit Cells Tok MsgT)
    (h : ∀ t ∈ [0, 1], ∀ e ∈ N.sent m t, pinJT cs G arr smpT ms e.1 e.2 (z, s) y w) :
    PinSig G cs l seat' (smpAt cs l seat' smpT z) arr (fun _ => True) s y w := by
  refine ⟨T.fits, fun i _ => ?_⟩
  obtain ⟨u, hu, hA⟩ := T.some i
  obtain ⟨t, ht, hm⟩ := T.sent i
  have hs : SitsAt u (seat' i).1 (seat' i).2 := hA.2
  exact (pin_move cs G arr smpT u ⟨⟨l, seat'⟩, i⟩ hA (z, s) (T.bySeat (z, s) _ _ hA) y w).1
    ((h t ht (seat' i) hm).2 u hu hs)

variable (σ0 : (sigOf cs l).Smp) {F : Frame}

/-- **The first half of the law's condition in front.** -/
theorem k8_cf (T : K8Sits G cs l seat' smpT ms N m) (z : P) (a : S × F.E.Str)
    (h : ∀ t ∈ [0, 1], ∀ e ∈ N.sent m t, noCollJT cs G smpT ms e.1 e.2 (z, a.1) (strsOf F a.2)) :
    (sigOf cs l).CF (totalOf cs l (smpAt cs l seat' smpT z) σ0 a.1)
      (wordsOf G cs l seat' (strsOf F a.2)) :=
  cf_of_cfSig cs l _ σ0 seat' G F a (k8_cfSig T z a.1 _ h)

/-- **The law's pins.** -/
theorem k8_pins (T : K8Sits G cs l seat' smpT ms N m) (z : P) (a : S × F.E.Str)
    (w : Wit Cells Tok MsgT)
    (h : ∀ t ∈ [0, 1], ∀ e ∈ N.sent m t,
      pinJT cs G arr smpT ms e.1 e.2 (z, a.1) (strsOf F a.2) w) :
    PinsAt cs l seat' arr G (totalOf cs l (smpAt cs l seat' smpT z) σ0) F a w :=
  pinsAt_of_pinSig cs l _ σ0 seat' arr G F a w (k8_pinSig arr T z a.1 _ w h)

end

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.k8_cfSig
#print axioms VerifiableInference.Desc.First.K8.k8_pinSig
#print axioms VerifiableInference.Desc.First.K8.k8_cf
#print axioms VerifiableInference.Desc.First.K8.k8_pins
