-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeySideDef.lean: THE STATE's SIDE OF THE LIBRARY's PROMISE ON THE KEY FILE, AS THE KEY FILE's
THREADS LAY IT (E2E/KeyRest.lean): four short definitions out of the library's own, at the library's
own seats and numbers. Definitions alone.

  `Side18 X k s`: THE FIRST CHAIN: the library's `ASideH` (Johnson/Top/Fire/Code/KeyASideAtFk.lean:
      its Bool on the state; the book places the pinned messages; the statement is in order; one tie
      on a mask; at two borders what the layer wants of what was heard), and from border 18 on its
      `E18` (KeyASideAll.lean)
  `Side₂ X k key s`: THE SHARED CHAIN: the library's `Tests₂` at its own letters (`T₂`,
      KeyASide2AtFk.lean) AT EVERY GOOD STATE OF THE FIRST CHAIN: one at which `Side18 X 19` holds.
      That heap reads the first chain's last state, which the shared chain's thread is not handed
  `Side₃ X P k z`: THE LAST CHAIN: the library's `Tests₃` at its own letters, and that the codes'
      lengths are in order at the state's codes (`T₃L`, KeyASide3AtFk.lean): on the chain's own
      state alone
  `KeyFits X x`: a test with code on the instance alone: the key fits the shape's index

Their payers: E2E/KeyStateSide.lean, KeyStateSide18.lean, KeyStateSide2.lean, KeySide3.lean; at the
threads: E2E/KeyMade.lean, KeyBehind.lean, KeyBehind3.lean.

Limits. Definitions: nothing is shown here. Where no good state of the first chain exists `Side₂`
holds of everything. 

-/
import Johnson.Top.Fire.Code.KeyASideAll
import Johnson.Top.Fire.Code.KeyASide2AtFk
import Johnson.Top.Fire.Code.KeyAtOff
import Johnson.Top.Fire.Code.KeyASide3AtFk

set_option autoImplicit false

namespace AtPublicFiles.KeyThread
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces)
open Johnson.RunOne.KeyRows23 (oneAt atSix shapeAt St₂ St₃ P₃)
open Johnson.RunOne.Law.StepSideAtFk (H₀ H₁)
open LPFD (ASideH E18 T₂ T₃L off₂N off₃N)

/-- **The first chain's.** -/
def Side18 (X : Source) (k : Nat) (s : FirstState) : Prop :=
  ASideH (oneAt X) atSix (H₀ X) (H₁ X) k s ∧ (18 ≤ k → E18 (oneAt X) s)

/-- **The shared chain's**, at every good state of the first chain. -/
def Side₂ (X : Source) (k : Nat) (key : OnBytes.TableKey) (s : St₂) : Prop :=
  ∀ e₁ : FirstState, Side18 X 19 e₁ → T₂ X atSix off₂N k ((⟨key⟩, e₁), s)

/-- **The last chain's.** -/
def Side₃ (X : Source) (P : LaterPlaces) (k : Nat) (z : P₃ × St₃) : Prop :=
  T₃L X P atSix off₂N off₃N k z

/-- The key fits the shape's index. -/
def KeyFits (X : Source) (x : Xi) : Prop := x.key.fits (shapeAt X).fold.index = true

end AtPublicFiles.KeyThread
