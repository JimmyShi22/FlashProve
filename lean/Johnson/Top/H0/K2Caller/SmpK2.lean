-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/SmpK2.lean: the code switch: THE HELD OOD SAMPLES OF THE TYPED
STATEMENT IN FRONT, AS A CLOSED TERM: the last letter of CarryK2.lean's sentence «carry» that read
the verifier's state. Definitions alone.

A typed OOD sample is a seed and its answers. The seed is no field of the verifier's state: the
state stores the sample ROWS. smpMade (Johnson/Top/H/SwitchInXMade.lean) makes the held samples
off these rows, over the letters of the switch's closing (two maps of names, a number of positions,
a stand-in). Here the same is written without these letters, at a typed structure r and the plain
letters.
  keptK2       the frame's entry for a held message's member, by the member's place in r.kept
  rowK2        the first stored sample row of that member's message in a statement
  FitsK2       a typed seed fits that row: its sample rows, carried to the open word's entries, are
               the vector of the row's form
  smp₀         a stand-in: the point 0, the factor 1, the answer 0
  smpK2        THE TERM: the seed: one that fits, BY CHOICE, where there is one, else the
               stand-in's; the answer: the row's target, read
LIMITS. Definitions. The seed is chosen, not computed. That a seed fits is not said here
(seedFits_of_goodS, from an invariant of the verifier's state). That it is smpMade:
SmpK2Is.lean. No soundness is claimed.
-/
import Johnson.Top.H0.K2Caller.CarryK2
import Johnson.Top.H0.K2Hands.TieLight

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan Johnson.Pack Johnson.Top.H Cb Iop IOR
open OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc.First.K2Hands

variable (r : SwRow) (H : r.OK)

/-- The frame's entry for a held message's member, by the member's place in r.kept. -/
def keptK2 (W : SwitchFrame) (k : (vecD (plainD r H)).held.K) : KeptPlace :=
  W.kept.getD (r.kept.idxOf k.1.1.val) ⟨0, 0, 0, 0, [], 0⟩

/-- The first stored sample row of that member's message in a statement. -/
def rowK2 (St : Statement) (W : SwitchFrame) (k : (vecD (plainD r H)).held.K) : OnBytes.Row :=
  (samplesOf St (keptK2 r H W k)).getD 0 default

/-- A typed seed fits that row. -/
def FitsK2 (St : Statement) (W : SwitchFrame) (k : (vecD (plainD r H)).held.K)
    (sd : ((vecD (plainD r H)).held.o k).Z.D) : Prop :=
  ∀ u, pushTo ((vecD (plainD r H)).held.sJ k) (((vecD (plainD r H)).held.o k).Z.mat sd u) =
    slotVec (plainR r H).s (plainR r H).Kp memK rowK (r.kept.idxOf k.1.1.val)
      (keptK2 r H W k).rowBits (formOn (rowK2 r H St W k))

/-- A stand-in for a held OOD sample: the point 0, the factor 1, the answer 0. -/
noncomputable def smp₀ : (vecD (plainD r H)).held.Smp := fun _ => ((fun _ => 0, 1), fun _ => 0)

open Classical in
/-- **The held OOD samples, off a front and its frame.** -/
noncomputable def smpK2 : _root_.Tw.K2.Front → SwitchFrame → (vecD (plainD r H)).held.Smp :=
  fun fx W k =>
    (if h : ∃ sd, FitsK2 r H fx.st W k sd then h.choose else (smp₀ r H k).1,
      fun _ => readE (rowK2 r H fx.st W k).target)

end VerifiableInference.Desc.First.K2Caller
