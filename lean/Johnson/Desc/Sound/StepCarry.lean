-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/StepCarry.lean: A BLOCK's LAW FOR A BATCH, AT ONE FILLING OF THE SHARED TABLE's
LETTERS, CARRIED TO ANOTHER. Theorems; general in the block, the border and both fillings.

WHY. The rule that sums the shared chain's blocks (LedgerPaysOwn,
Johnson/Desc/Sound/SharedJointCountLedgerOwn.lean) asks every block's law at ONE promise's meaning
Pm and ONE items' meaning Mg. Files that have typed their block's law at a filling of their own need
not turn it: LeadsB is monotone with the yes at hand (Johnson/Desc/Plain/BothConseq.lean).

  promQ_carry   the shared promise at border k passes from Pm' to Pm, clause by clause: the stored
                table's promise; "shown" and "no collision" at every tenant; the book-keeping at k;
                "nothing is left".
  step_carry    **the carriage**: the law at (Pm, Mg) gives the law at (Pm', Mg'), at the same key,
                extractor and errors, from four premises: (f) in front Pm' gives Pm · (b) inside
                Pm' in front, at a yes, Pm behind gives Pm' behind: WHAT THE BLOCK HANDS ON FOR
                CERTAIN · (r') behind, inside Pm', Mg's items follow from Mg''s · (r) in front,
                inside Pm', Mg''s items follow from Mg's.
  step_carryN   the same for the law at ONE list of errors that bears the split for n slots
                (LeadsBN): by LeadsBN.conseq (Johnson/Desc/Plain/KeyAlone.lean).
What is not claimed. That any two fillings meet the four. Nothing on soundness.

-/
import Johnson.Desc.Plain.BothConseq
import Johnson.Desc.Sound.SharedJointCountRowB
import Johnson.Desc.Plain.KeyAlone

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open Iop OnBytes.Maker OnBytes.Flat
open _root_.Run.PQ (CK)
open VerifiableInference.Desc.Shared (NumbersS MeaningS PromMeaning PromS promsAt)

variable {P₁ S₂ Cl Wt κ : Type} {C : CK} {Fr : Frame} (N : NumbersS)
  (Mg Mg' : MeaningS S₂ P₁ Wt) (Pm Pm' : PromMeaning S₂) (Oc : P₁ → Strs → Prop) (split : Bool)
  (p : Piece C Fr (P₁ × S₂) Cl Wt) (l : List (Piece C Fr (P₁ × S₂) Cl Wt))
  (ext : ℕ → (P₁ × S₂) × Fr.E.Str → Wt → Wt)

/-- The shared promise, clause by clause. -/
theorem promQ_carry (k : ℕ) (v : (actQ N p l k).1)
    (h : ∀ c ∈ promsAt split k, c.holds N Pm' v.1 (strsOfAct Fr v) →
      c.holds N Pm v.1 (strsOfAct Fr v))
    (hq : promQ N Pm' split p l k v) : promQ N Pm split p l k v :=
  fun c hc => h c hc (hq c hc)

/-- **The carriage.** -/
theorem step_carry (k : ℕ) (x : Piece C Fr (P₁ × S₂) Cl Wt)
    (key : (P₁ × S₂) × Fr.E.Str → κ) (δK δO : Err (uLT C x.ds))
    (H : x.ior.red.LeadsB key (onQ₂ N Pm Oc split p l k) (stepAt N Mg Pm Oc split p l ext k) δK δO)
    (hf : ∀ a, onQ₂ N Pm' Oc split p l k a → onQ₂ N Pm Oc split p l k a)
    (hb : ∀ a τ b, onQ₂ N Pm' Oc split p l k a → x.ior.red.out a τ = some b →
      onQ₂ N Pm Oc split p l (k + 1) b → onQ₂ N Pm' Oc split p l (k + 1) b)
    (hr' : ∀ a τ b w, onQ₂ N Pm' Oc split p l k a → x.ior.red.out a τ = some b →
      onQ₂ N Pm' Oc split p l (k + 1) b → relQ₂ N Mg' split p l (k + 1) b w →
      relQ₂ N Mg split p l (k + 1) b w)
    (hr : ∀ a w, onQ₂ N Pm' Oc split p l k a → relQ₂ N Mg split p l k a w →
      relQ₂ N Mg' split p l k a w) :
    x.ior.red.LeadsB key (onQ₂ N Pm' Oc split p l k) (stepAt N Mg' Pm' Oc split p l ext k) δK δO :=
  H.conseq hf fun a τ b ha ho hq =>
    ⟨hb a τ b ha ho hq.1, fun w hw =>
      hr a _ ha (hq.2 w (hr' a τ b w ha ho (hb a τ b ha ho hq.1) hw))⟩

/-- **The carriage, at one list of errors for n slots.** -/
theorem step_carryN (k : ℕ) (x : Piece C Fr (P₁ × S₂) Cl Wt)
    (key : (P₁ × S₂) × Fr.E.Str → κ) (n : ℕ) (ε : Err (uLT C x.ds))
    (H : x.ior.red.LeadsBN key (onQ₂ N Pm Oc split p l k) (stepAt N Mg Pm Oc split p l ext k) n ε)
    (hf : ∀ a, onQ₂ N Pm' Oc split p l k a → onQ₂ N Pm Oc split p l k a)
    (hb : ∀ a τ b, onQ₂ N Pm' Oc split p l k a → x.ior.red.out a τ = some b →
      onQ₂ N Pm Oc split p l (k + 1) b → onQ₂ N Pm' Oc split p l (k + 1) b)
    (hr' : ∀ a τ b w, onQ₂ N Pm' Oc split p l k a → x.ior.red.out a τ = some b →
      onQ₂ N Pm' Oc split p l (k + 1) b → relQ₂ N Mg' split p l (k + 1) b w →
      relQ₂ N Mg split p l (k + 1) b w)
    (hr : ∀ a w, onQ₂ N Pm' Oc split p l k a → relQ₂ N Mg split p l k a w →
      relQ₂ N Mg' split p l k a w) :
    x.ior.red.LeadsBN key (onQ₂ N Pm' Oc split p l k) (stepAt N Mg' Pm' Oc split p l ext k) n ε :=
  H.conseq hf fun a τ b ha ho hq =>
    ⟨hb a τ b ha ho hq.1, fun w hw =>
      hr a _ ha (hq.2 w (hr' a τ b w ha ho (hb a τ b ha ho hq.1) hw))⟩

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.step_carry
#print axioms VerifiableInference.Desc.Sound.step_carryN
