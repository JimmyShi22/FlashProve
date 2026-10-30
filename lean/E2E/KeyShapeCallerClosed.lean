-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyShapeCallerClosed.lean: THE SUB-PROTOCOL IN FRONT OF A LOOKUP's ROUNDS ("caller"), ON THE
FIRST CHAIN's SHAPE, AS ONE CLOSED FORM: what its guard (`gCaller`, E2E/KeyShapeFirst.lean) returns,
written without an iteration. A statement on a guard on shapes and its proof: NOTHING IS SHOWN OF
ANY PROVER, and nothing of the verifier's sub-protocol itself: that is `caller_exact`'s.

What for. At the full size the guard takes some 17,800 mask entries one by one and asks the length
of the list of the hidden values' homes: Lean's kernel carries neither. Here both takings are
Johnson/Desc/Ground/Shape/TakeMany.lean's `take_many`, and the length is E2E/KeyLookupAround.lean's
`homes_size`: CALLED. What is left to evaluate at written sizes are a few clauses on numbers.

  `ledger_with_ne`: a ledger laid in at one message leaves another message's ledger.
  `ownAt`, `idxAt`: the entries handed out, as formulas over `List.range`.
  **`callerT`**: the shape behind, written.
  **`caller_closed`**: where the mark on the statement is true, no ledger of a lookup is open, i
    lookups are through, the two messages are two, their ledgers are in step and have room, and
    every part of the lookup's face has a level: `gCaller Q i a = .ok (callerT …)`.

Limits.
- Enough, not needed.
- The list of homes stays a formula in the shape behind: whoever reads it at the full size wants
  laws on `homesFrom`, not an evaluation.


-/
import E2E.KeyShapeFirst
import Johnson.Desc.Ground.Shape.TakeMany

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.AtFiles
open OnBytes OnBytes.Params
open VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.K3 (Face faceOfLkp fromKeys homesFrom homes)
open AtPublicFiles.KeyShape (Sh₁ Pub1 gCaller lookAt msgOf freshLed)

/-- A ledger laid in at one message leaves another message's ledger. -/
theorem ledger_with_ne (a : CoreSh) (o o' : Nat) (l : Ledger) (h : o' ≠ o) :
    ((withLedger a o l).st.oracles[o']?).bind (·.ledger) =
      (a.st.oracles[o']?).bind (·.ledger) := by
  unfold withLedger modAt
  dsimp only
  rw [List.getElem?_map, List.getElem?_zipIdx]
  cases a.st.oracles[o']? with
  | none => rfl
  | some x =>
    show (some (if 0 + o' = o then _ else x)).bind (·.ledger) = _
    rw [Nat.zero_add, if_neg h]

variable {Bk : Type} (Q : Pub1)

/-- The entries of the own message that lookup i's hidden values get. -/
def ownAt (i : Nat) (l : Ledger) (k : Nat) : List Slot :=
  ((List.range ((faceOfLkp (lookAt Q.one i)).slots -
      2 * (faceOfLkp (lookAt Q.one i)).parts.length)).map fun j => freeNo l.rows (k + j)).map
    fun j => ⟨msgOf Q.one, j⟩

/-- The entries of the index-mask message. -/
def idxAt (i idx : Nat) (l : Ledger) (k : Nat) : List Slot :=
  ((List.range (2 * (faceOfLkp (lookAt Q.one i)).parts.length)).map fun j =>
    freeNo l.rows (k + j)).map fun j => ⟨idx, j⟩

/-- **The shape behind**, written. l₁, k₁: the own message's ledger, and how many of its entries are
handed out; l₂, k₂: the index-mask message's. -/
def callerT (i : Nat) (a : Sh₁ Bk) (l₁ : Ledger) (k₁ : Nat) (l₂ : Ledger) (k₂ : Nat) : Sh₁ Bk :=
  (withLedger (withLedger a.1 (msgOf Q.one) (behind l₁ k₁
      ((faceOfLkp (lookAt Q.one i)).slots - 2 * (faceOfLkp (lookAt Q.one i)).parts.length)))
      a.2.idx (behind l₂ k₂ (2 * (faceOfLkp (lookAt Q.one i)).parts.length)),
    { a.2 with look := { a.2.look with
        led := some (some (freshLed (faceOfLkp (lookAt Q.one i)).slots)), heard := none
        home := homesFrom (fromKeys (faceOfLkp (lookAt Q.one i))) (ownAt Q i l₁ k₁)
          (idxAt Q i a.2.idx l₂ k₂) } })

/-- **THE CLOSED FORM.** -/
theorem caller_closed (i : Nat) (a : Sh₁ Bk) (l₁ : Ledger) (k₁ : Nat) (l₂ : Ledger) (k₂ : Nat)
    (ht : a.2.tidy = true) (hled : a.2.look.led.isNone = true) (hk : a.2.look.keys.length = i)
    (hne : a.2.idx ≠ msgOf Q.one)
    (h1 : (a.1.st.oracles[msgOf Q.one]?).bind (·.ledger) = some l₁) (s1 : InStep l₁ k₁)
    (n1 : (faceOfLkp (lookAt Q.one i)).slots - 2 * (faceOfLkp (lookAt Q.one i)).parts.length ≤
      l₁.left)
    (h2 : (a.1.st.oracles[a.2.idx]?).bind (·.ledger) = some l₂) (s2 : InStep l₂ k₂)
    (n2 : 2 * (faceOfLkp (lookAt Q.one i)).parts.length ≤ l₂.left)
    (hp : ∀ v ∈ (faceOfLkp (lookAt Q.one i)).parts, 1 ≤ v) :
    gCaller Q i a = .ok (callerT Q i a l₁ k₁ l₂ k₂) := by
  have e1 := take_many a.1 (msgOf Q.one) _ l₁ k₁ h1 s1 n1
  have e2 := take_many (withLedger a.1 (msgOf Q.one) (behind l₁ k₁
      ((faceOfLkp (lookAt Q.one i)).slots - 2 * (faceOfLkp (lookAt Q.one i)).parts.length)))
    a.2.idx _ l₂ k₂ ((ledger_with_ne a.1 _ _ _ hne).trans h2) s2 n2
  have hlen : (homesFrom (fromKeys (faceOfLkp (lookAt Q.one i))) (ownAt Q i l₁ k₁)
      (idxAt Q i a.2.idx l₂ k₂)).length = (faceOfLkp (lookAt Q.one i)).slots := by
    have := AtPublicFiles.KeyLookup.homes_size hp (o := ownAt Q i l₁ k₁) (k := idxAt Q i a.2.idx l₂ k₂)
      (by unfold ownAt; rw [List.length_map, List.length_map, List.length_range])
      (by unfold idxAt; rw [List.length_map, List.length_map, List.length_range])
    unfold homes at this
    rwa [List.size_toArray] at this
  unfold gCaller
  dsimp only
  rw [if_pos (by rw [ht, hled, hk]; simp), e1]
  dsimp only
  rw [e2]
  dsimp only
  rw [if_pos (by
    show ((homesFrom (fromKeys (faceOfLkp (lookAt Q.one i))) (ownAt Q i l₁ k₁)
      (idxAt Q i a.2.idx l₂ k₂)).length == _) = true
    rw [hlen]
    exact beq_self_eq_true _)]
  rfl

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.ledger_with_ne
#print axioms AtPublicFiles.AtFiles.caller_closed
