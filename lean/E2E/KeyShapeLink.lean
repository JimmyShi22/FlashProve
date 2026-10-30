--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyShapeLink.lean: THE SIX SUB-PROTOCOLS OF A LOOKUP'S LINK, AND "rng.0.rows", ON THE KEY FILE'S
FIRST CHAIN'S SHAPE, IN ONE FORM; and from that form to (B1) and (B2) of
Johnson/Desc/ProofFile/Honest/Thread/Shape.lean. Definitions, statements and proofs, by calls.
NOTHING IS SHOWN OF ANY PROVER.

What is defined.
  **`ExactAt ft sh blk g`**: where g returns at a state's shape and the step's own tests on rounds
    and columns pass, the sub-protocol's decision returns a state of the shape that g returns. It is
    a premise's form; it is none of the library's goals.
  `gLink Q i`: the six guards of lookup number i's link, in the order of the link's flat list: laid
    · the sub-protocol in front of the rounds · the lookup's own · the one behind its rounds ·
    behind the batching's place · cleared.
What is shown.
  **`carries_of_exact`**, **`returns_of_exact`**: `ExactAt` at the member behind a border gives
    `Carries` and `Returns` there, whatever the shape's named tests on values are: NONE IS SPENT.
  **`link_exact`**: each of the six is exact, at every lookup number, at all public values.
  `layRows_exactAt`: so is "rng.0.rows".

Limits.
- The lookup is `lookAt Q.one i`: number i of the chain's own list, or a default value where there
  is none.
- The two sendings in front and the chain's back half are not here. No shape's run is evaluated.
- Nothing on completeness, on soundness or on what is hidden.


-/
import E2E.KeyShapeHear
import E2E.KeyShapeLayer
import E2E.KeyShapeLayRows

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyShape
open OnBytes
open ProofFile.Honest (Shape Carries Returns)
open VerifiableInference.Desc (Block Link noDigest OpenedColumn step_iff)
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.Key

/-! ## 1. From one exact lemma at a sub-protocol to (B1) and (B2) -/

section
variable {S Cl Sh : Type}

/-- **Where the guards return at a state's shape and the step's own tests on rounds and columns
pass, the sub-protocol's decision returns a state of the shape that the guards return.** -/
def ExactAt (ft : ℕ) (sh : S → Sh) (blk : Block S Cl) (g : Sh → Except String Sh) : Prop :=
  ∀ s t rs cols, g (sh s) = .ok t → blk.Fits ft rs cols →
    ∃ s', blk.decide s (rs.map noDigest) (blk.shown ft rs cols) = .ok s' ∧ sh s' = t

theorem carries_of_exact {bs : List (Block S Cl)} {ft : ℕ} {Z : Shape S} {b : ℕ}
    (h : ∀ blk, bs[b]? = some blk → ExactAt ft Z.sh blk (Z.g b)) : Carries bs ft Z b := by
  intro blk hb s rs cols s' n t hs hg
  obtain ⟨hfit, hdec, -⟩ := (step_iff ft blk s s' rs cols n).1 hs
  obtain ⟨s'', e, r⟩ := h blk hb s t rs cols hg hfit
  rw [hdec] at e
  obtain rfl := Except.ok.inj e
  exact r.symm

theorem returns_of_exact {bs : List (Block S Cl)} {ft : ℕ} {Z : Shape S} {b : ℕ}
    (h : ∀ blk, bs[b]? = some blk → ExactAt ft Z.sh blk (Z.g b)) : Returns bs ft Z b := by
  intro blk hb s rs cols t hg hfit _
  obtain ⟨s', e, -⟩ := h blk hb s t rs cols hg hfit
  exact ⟨s', e⟩

end

/-! ## 2. The six sub-protocols of a lookup's link, and "rng.0.rows" -/

variable (Q : Pub1) {Bk : Type} (bk : BackOf → Bk)

/-- The six guards of lookup number i's link, in the order of the link's flat list. -/
def gLink (i : ℕ) : List (Sh₁ Bk → Except String (Sh₁ Bk)) :=
  [gLaid, gCaller Q i, gHear Q i, gLayer Q i, .ok, gCleared]

/-- **Each of the six is exact.** -/
theorem link_exact (i ft k : ℕ) (blk : Block FirstState Claim)
    (g : Sh₁ Bk → Except String (Sh₁ Bk))
    (hb : (lookupLink Q.one Q.set i (lookAt Q.one i)).blocksInOrder[k]? = some blk)
    (hg : (gLink Q i)[k]? = some g) : ExactAt ft (sh₁ Q bk) blk g := by
  intro s t rs cols h hfit
  match k, hb, hg with
  | 0, hb, hg =>
    obtain rfl := Option.some.inj hb
    obtain rfl := Option.some.inj hg
    exact laid_exact Q bk i (lookAt Q.one i) s t h
  | 1, hb, hg =>
    obtain rfl := Option.some.inj hb
    obtain rfl := Option.some.inj hg
    exact caller_exact Q bk i _ _ s t h
  | 2, hb, hg =>
    obtain rfl := Option.some.inj hb
    obtain rfl := Option.some.inj hg
    exact hear_exact Q bk i ft rs cols _ s t h hfit
  | 3, hb, hg =>
    obtain rfl := Option.some.inj hb
    obtain rfl := Option.some.inj hg
    exact layer_exact Q bk i _ _ s t h
  | 4, hb, hg =>
    obtain rfl := Option.some.inj hb
    obtain rfl := Option.some.inj hg
    exact behind_exact Q bk i (lookAt Q.one i) s t h
  | 5, hb, hg =>
    obtain rfl := Option.some.inj hb
    obtain rfl := Option.some.inj hg
    exact cleared_exact Q bk i (lookAt Q.one i) s t h
  | k + 6, _, hg => cases hg

theorem layRows_exactAt (ft : ℕ) : ExactAt ft (sh₁ Q bk) (layRows Q.one) (gLayRows Q) :=
  fun s t _ _ h _ => layRows_exact Q bk _ _ s t h

end AtPublicFiles.KeyShape

#print axioms AtPublicFiles.KeyShape.carries_of_exact
#print axioms AtPublicFiles.KeyShape.returns_of_exact
#print axioms AtPublicFiles.KeyShape.link_exact
#print axioms AtPublicFiles.KeyShape.layRows_exactAt
