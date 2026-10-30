-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/LedgerBesideAll.lean: A TEST LAID BESIDE THE PROMISE's BOOK-KEEPING, OVER A WHOLE
ROW OF LAWS FOR A BATCH. clause_beside (Johnson/Desc/Sound/LedgerBeside.lean) lifts one clause for
one statement. HERE the like for the form in which the ledger ends (EachLawsBN at onQ₂ | stepAt,
Johnson/Desc/Sound/KeysByMake.lean, SharedJointCountRowB.lean): where each piece's accepting step
hands the test on for certain, the whole row's laws stand at the promise with the test beside, at
the same keys, errors and extractor.

  on_beside       inside the promise with X beside: inside the promise, and X.
  eachLawsBN_beside   **the rule.**
What is not claimed. No soundness; no level.

-/
import Johnson.Desc.Sound.LedgerBeside
import Johnson.Desc.Sound.SharedJoinPlain
import Johnson.Desc.Sound.SharedJointCountRowB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK)
open _root_.Iop (Reduction Err)
open VerifiableInference.Desc.Shared
open Desc.Plain

variable {P₁ S₂ Cl Wt : Type} {C : CK} {Fr : Frame} (N : NumbersS) (Mg : MeaningS S₂ P₁ Wt)
  (Pm : PromMeaning S₂) (Oc : P₁ → Strs → Prop) (split : Bool)
  (p : Piece C Fr (P₁ × S₂) Cl Wt) (l : List (Piece C Fr (P₁ × S₂) Cl Wt)) (X : ℕ → S₂ → Bool)

theorem on_beside (k : ℕ) (a : (P₁ × S₂) × Fr.E.Str) :
    onQ₂ N (besideP Pm X) Oc split p l k a ↔ onQ₂ N Pm Oc split p l k a ∧ X k a.1.2 = true :=
  ⟨fun h => ⟨⟨((promQ_beside N Pm split p l X k _).1 h.1).1, h.2⟩,
      ((promQ_beside N Pm split p l X k _).1 h.1).2⟩,
    fun h => ⟨(promQ_beside N Pm split p l X k _).2 ⟨h.1.1, h.2⟩, h.1.2⟩⟩

/-- **A test beside, over the whole row.** -/
theorem eachLawsBN_beside {κ : Type} (key : ℕ → (P₁ × S₂) × Fr.E.Str → κ)
    (ext : ℕ → (P₁ × S₂) × Fr.E.Str → Wt → Wt) (n : ℕ) :
    ∀ (m : List (Piece C Fr (P₁ × S₂) Cl Wt)) (k : ℕ),
      (∀ i x, m[i]? = some x → ∀ a τ b, onQ₂ N (besideP Pm X) Oc split p l (k + i) a →
        x.ior.red.out a τ = some b → X (k + i + 1) b.1.2 = true) →
      EachLawsBN key (onQ₂ N Pm Oc split p l) (stepAt N Mg Pm Oc split p l ext) n k m →
      EachLawsBN key (onQ₂ N (besideP Pm X) Oc split p l)
        (stepAt N Mg (besideP Pm X) Oc split p l ext) n k m
  | [], _, _, _ => trivial
  | x :: m, k, hX, ⟨h1, _, h3⟩ =>
    ⟨h1.conseq (fun a ha => ((on_beside N Pm Oc split p l X k a).1 ha).1)
        (fun a τ b ha hb hq =>
          ⟨(on_beside N Pm Oc split p l X (k + 1) b).2 ⟨hq.1, hX 0 x rfl a τ b ha hb⟩, hq.2⟩),
      fun _ _ _ hq => hq.1,
      eachLawsBN_beside key ext n m (k + 1)
        (fun i y hy a τ b ha hb => by
          have e : k + 1 + i = k + (i + 1) := by omega
          rw [e] at ha ⊢
          exact hX (i + 1) y hy a τ b ha hb) h3⟩

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.on_beside
#print axioms VerifiableInference.Desc.Sound.eachLawsBN_beside
