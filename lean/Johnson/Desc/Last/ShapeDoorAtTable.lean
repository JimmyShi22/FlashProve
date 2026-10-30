-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/ShapeDoorAtTable.lean: THE DOOR AT `fillZ` (Johnson/Desc/Last/ShapeDoor.lean)
CALLED AT THE TABLE'S OWN JOINT: the first half of the joint between the shared and the last chain
(`onZero₃OfEnd₂`, Johnson/Desc/Sound/BordersLastQProofs.lean) with `door_fillZ` for its premise on
`PL.shape 0`. One statement and its proof.

Why. ShapeDoor.lean says that `door_fillZ` is that premise to the letter, at On₂ := the shared
chain's promise at its last border. Here Lean holds the two against each other.

Main name (namespace `VerifiableInference.Desc.Last`).
  **`onZero₃_fillZ`**: the shared chain is as long as its table; the start's yes gives "no mark" at
    the first chain's last record; `DoorOwed p fs (onQ₂ … at the last border) start₃`; the shared
    chain's promise on Omega goes over to the whole strings: then the shared chain's promise at its
    last border and the start's yes give the last chain's promise at border 0, at PL :=
    `fillZ p R fs`, at the record that the start makes.

Limits. Those of ShapeDoor.lean: all four premises are owed; no member. The last border is written
as the table writes it, 1 + T.l₂.length. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Last.ShapeDoor
import Johnson.Desc.Sound.BordersLastQProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Last
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Third
open _root_.Desc.K14 (St)

/-- **The promise goes forward into the last chain at `fillZ`.** -/
theorem onZero₃_fillZ {C : CK} {D : WholeD} {all : List LeftT} {Y P S₁ X₁ X₂ Cl Wt : Type}
    (p : P₁₄) (R : List Fmt.DeclaredRound) (fs : P × S₁ → First.S)
    (start₃ : P → S₁ → St → Option S₃)
    (T : Three C D all Y (P × S₁) ((P × S₁) × St) ((P × S₁ × St) × S₃) X₁ X₂ Cl Wt)
    (N : NumbersS) (Mg : MeaningS St (P × S₁) Wt) (ML : MeaningL S₃ Wt) (Pm : PromMeaning St)
    (Oc : P × S₁ → Strs → Prop) (split : Bool)
    (hlen : 1 + T.l₂.length = (sharedPlaces split).length)
    (hStart : ∀ q s₁ s₂ s, start₃ q s₁ s₂ = some s → Mg.unmarked1 (q, s₁))
    (H : DoorOwed p fs (onQ₂ N Pm Oc split T.p₂ T.l₂ (1 + T.l₂.length)) start₃)
    (hPO : ∀ b : ((P × S₁) × St) × (EAll D all).Str,
      (PromS.noColl .oOmega).holds N Pm ((actQ N T.p₂ T.l₂ (1 + T.l₂.length)).2 b).1
        (strsOfAct (frameAt D all D.key₂ T.ft₂) ((actQ N T.p₂ T.l₂ (1 + T.l₂.length)).2 b)) →
      (PromS.noColl .oOmega).holds N Pm b.1.2 (strsOf (frameAt D all D.key₃ T.ft₃) b.2))
    (b : ((P × S₁) × St) × (EAll D all).Str) (s : S₃)
    (hb : onQ₂ N Pm Oc split T.p₂ T.l₂ (1 + T.l₂.length) b)
    (hs : start₃ b.1.1.1 b.1.1.2 b.1.2 = some s) :
    onQ₃ (Fr := frameAt D all D.key₃ T.ft₃) N Mg Pm (fillZ p R fs) Oc 0
      (((b.1.1.1, b.1.1.2, b.1.2), s), b.2) :=
  onZero₃OfEnd₂ C D all Y P S₁ St S₃ X₁ X₂ Cl Wt start₃ T N Mg ML Pm (fillZ p R fs) Oc split hlen
    hStart (fun b s hb hs => door_fillZ H b s hb hs) hPO b s hb hs

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.onZero₃_fillZ
