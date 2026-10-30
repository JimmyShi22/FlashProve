-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/RwAtReached.lean: THE PREMISE hR3 OF THE LINK's LAW AT THE COMPOSED
MEANING's OWN PUBLIC SENTENCE (`rwAt 𝔇 m`), WITH ITS TWO FACTS ON THE STATE IN FRONT OF THE ONE
EQUATION's PIECE DRAWN OUT OF "REACHED", NOT OUT OF THE PROMISE. Theorems.

WHY. LaidAt.lean says of the two facts (`TwoFacts p s`: the rows owed are the batching
round's; what is said to be laid is what the record and the tables foretell): "they pass from piece
to piece only through the conditions at the boundaries: where these are the table's own promise, the
facts stay names at the table's door". By report no item of the promise
carries them. But the second form of the conditions (`onTR`) holds a second conjunct: the state is
REACHED. A state that is reached at number k + 2 has come by a yes of sub-protocol number k and a
yes of number k + 1 (the inductive definition's own inversion): where these are the link's batching
sub-protocol and the one behind it, `TwoBlocks` (LinkAtSort.lean: the first yes MAKES the
two facts, the second KEEPS them) gives them.

What is said.
  `reach_back`: the inversion: what is reached at k + 1 has come by a yes of sub-protocol number k
    from a state reached at k.
  `facts_reached`: **TwoFacts at every state reached at k + 2**, from TwoBlocks and the two
    sub-protocols' numbers in the list.
  `rw_of_facts`: hR3 at K9.rowsFit from TwoFacts in front (rows_of_yes over the bridge
    rowsFit_iff, RwRides.lean).
  `rwAt_hR3_reached`: **hR3 AT Rw := rwAt 𝔇 m AND on2 := onTR … (k + 2)**, in the very form of the
    law's premise, where the condition's second conjunct gives "reached" (hRz).

Limits. PREMISES: `TwoBlocks L p` (paid in LinkAtSort.lean at each sort of link from the sort's
Take and one
sentence on the lookup's runs) · the two numbers in the list (closed facts) · hRz: what the
condition's letter Rz says of a state gives Reach over the sub-protocols themselves (at
Rz := RchAt it is rchAt_raw) · hrw · the law's own hb₃ hpe. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.RwRides
import Johnson.Desc.First.Link.Law.LinkAtSort
import Johnson.Top.H0.Walk.Reach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning)
open Johnson.Desc.First.Walk.Tied (Reach StepYes)
open _root_.Run (ckP)

/-- **The inversion.** -/
theorem reach_back {T Cl P : Type} {ft : ℕ} {bs : List (Block T Cl)} {start : P → T} {k : ℕ}
    {z : P} {s' : T} (h : Reach ft bs start (k + 1) (z, s')) :
    ∃ s b, Reach ft bs start k (z, s) ∧ bs[k]? = some b ∧ StepYes ft b s s' := by
  cases h with
  | succ h1 hb hy => exact ⟨_, _, h1, hb, hy⟩

/-- **THE TWO FACTS AT EVERY STATE REACHED BEHIND THE LINK's FIRST TWO SUB-PROTOCOLS.** -/
theorem facts_reached {P : Type} (L : Link S Claim) (p : Where) (TB : TwoBlocks L p) {ft : ℕ}
    {bs : List (Block S Claim)} {start : P → S} {k : ℕ} (hk : bs[k]? = some L.batchB)
    (hk1 : bs[k + 1]? = some L.behindB) {z : P} {s : S}
    (h : Reach ft bs start (k + 1 + 1) (z, s)) : TwoFacts p s := by
  obtain ⟨s₁, b₂, h1, hb₂, R₂, c₂, _, hs₂⟩ := reach_back h
  obtain ⟨s₀, b₁, _, hb₁, R₁, c₁, _, hs₁⟩ := reach_back h1
  obtain rfl : L.behindB = b₂ := Option.some.inj (hk1.symm.trans hb₂)
  obtain rfl : L.batchB = b₁ := Option.some.inj (hk.symm.trans hb₁)
  exact (TB.2 ft s₁ R₂ c₂ s _ hs₂).2 (TB.1 ft s₀ R₁ c₁ s₁ _ hs₁).2

section
variable {Cl W : Type} {F : Frame}

/-- **hR3 from the two facts in front.** -/
theorem rw_of_facts (u : HTailF2) (p pw : Where) (b₃ : Block S Cl)
    (hb₃ : ∀ ft s rs cols x, b₃.step ft s rs cols = .ok x →
      (K9.oneEquation (Cl := Cl) atS pw).step ft s rs cols = .ok x)
    (pe : Piece (ckP .two) F S Cl W) (hpe : pe.b = below b₃) (on2 : S × F.E.Str → Prop)
    (hon2 : ∀ a, on2 a → TwoFacts p a.1) :
    ∀ a τ b', on2 a → pe.ior.red.out a τ = some b' → K9.rowsFit p.rows a.1 = true :=
  fun a τ b' ha hout => (rowsFit_iff p.rows u a.1).2
    (rows_of_yes u p pw b₃ hb₃ pe hpe on2 hon2 a τ b' ha hout)

end

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) {F : Frame}
  (Mg₀ : Meaning P (Wit (CellsQ rows cols) Tok MsgT)) (links : List ModelPart) (pl : List Place)
  (z : P) (Rz : ℕ → S × F.E.Str → Prop) (k m : ℕ)

local notation "onK" => onTR 𝔇.N (mgAll 𝔇 Mg₀) links pl (fun s : S => (z, s)) Rz

/-- **hR3 AT THE COMPOSED MEANING's OWN SENTENCE AND THE TABLE's OWN CONDITION.** -/
theorem rwAt_hR3_reached (u : HTailF2) (L : Link S Claim) (p pw : Where) (TB : TwoBlocks L p)
    (hrw : ∀ s, 𝔇.rw m s = K9.rowsFit p.rows s) {ft : ℕ} {bs : List (Block S Claim)}
    {start : P → S} (hk : bs[k]? = some L.batchB) (hk1 : bs[k + 1]? = some L.behindB)
    (hRz : ∀ a, Rz (k + 1 + 1) a → Reach ft bs start (k + 1 + 1) (z, a.1))
    (b₃ : Block S Claim)
    (hb₃ : ∀ ft s rs cols x, b₃.step ft s rs cols = .ok x →
      (K9.oneEquation (Cl := Claim) atS pw).step ft s rs cols = .ok x)
    (pe : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT)) (hpe : pe.b = below b₃) :
    ∀ a τ b', onK (k + 1 + 1) a → pe.ior.red.out a τ = some b' → rwAt 𝔇 m a := by
  intro a τ b' ha hout
  show 𝔇.rw m a.1 = true
  rw [hrw]
  exact rw_of_facts u p pw b₃ hb₃ pe hpe (onK (k + 1 + 1))
    (fun a ha => facts_reached L p TB hk hk1 (hRz a ha.2)) a τ b' ha hout

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.reach_back
#print axioms VerifiableInference.Desc.LinkJoin.facts_reached
#print axioms VerifiableInference.Desc.LinkJoin.rw_of_facts
#print axioms VerifiableInference.Desc.LinkJoin.rwAt_hR3_reached
