-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/SentLaw.lean: when `Johnson.G.OfPlan.sentAt` (Johnson/G/RoundsOfPlan.lean) returns,
and when the `mapM` of it over a chain's sendings returns: at every name and every offset.

Statements. General.
  `sentAt_isOk`: it returns where the label has a tag and the oracle messages can be placed in
    trees.
  `sentAt_no`: it refuses where the label has no tag.
  `mapM_isOk`: a `mapM` returns where its routine returns at every member.
  **`sent_of`**: a chain's `mapM` of `sentAt` returns, from (ht) the list of its labels' tags, (hs)
    every one is a tag, (hL) at every sending the oracle messages can be placed in trees.

Limits. WHICH trees `sentAt` returns is not said: only that it returns. The three facts are
premises. No closed fact. Nothing on soundness.

-/
import Johnson.G.RoundsOfPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Unfolds
open Johnson.G.OfPlan (SendTag sendTag)

/-- `sentAt` returns where the label has a tag and the oracle messages can be placed in trees. -/
theorem sentAt_isOk {at_ : String} {codes : OnBytes.Codes} {off : Nat} {x : Johnson.G.Sending}
    (h : (sendTag x.label).isSome = true)
    (hL : (OnBytes.layTrees codes x.sent.toArray).isSome = true) :
    (Johnson.G.OfPlan.sentAt at_ codes off x).isOk = true := by
  obtain ⟨t, e⟩ := Option.isSome_iff_exists.1 h
  unfold Johnson.G.OfPlan.sentAt
  rw [e]
  cases eL : OnBytes.layTrees codes x.sent.toArray with
  | none =>
    rw [eL] at hL
    cases hL
  | some L => rfl

/-- It refuses where the label has no tag. -/
theorem sentAt_no {at_ : String} {codes : OnBytes.Codes} {off : Nat} {x : Johnson.G.Sending}
    (h : sendTag x.label = none) : (Johnson.G.OfPlan.sentAt at_ codes off x).isOk = false := by
  unfold Johnson.G.OfPlan.sentAt
  rw [h]
  rfl

/-- A `mapM` returns where its routine returns at every member. -/
theorem mapM_isOk {α β : Type} (f : α → Except String β) : ∀ l : List α,
    (∀ x ∈ l, (f x).isOk = true) → (l.mapM f).isOk = true
  | [], _ => by
    rw [List.mapM_nil]
    rfl
  | a :: l, h => by
    rw [List.mapM_cons]
    have ha := h a List.mem_cons_self
    have ih := mapM_isOk f l fun x hx => h x (List.mem_cons_of_mem _ hx)
    cases ea : f a with
    | error e =>
      rw [ea] at ha
      cases ha
    | ok b =>
      cases el : l.mapM f with
      | error e =>
        rw [el] at ih
        cases ih
      | ok bs => rfl

/-- **A chain's `mapM` of `sentAt` returns**, from the list of its labels' tags, every one a tag,
and a test on its trees. -/
theorem sent_of (at_ : String) (off : Nat) (C : Johnson.G.ChainSends) (ts : List (Option SendTag))
    (ht : (C.sends.map (·.label)).map sendTag = ts) (hs : ts.all Option.isSome = true)
    (hL : (C.sends.all fun x => (OnBytes.layTrees C.codes x.sent.toArray).isSome) = true) :
    (C.sends.mapM (Johnson.G.OfPlan.sentAt at_ C.codes off)).isOk = true := by
  refine mapM_isOk _ _ fun x hx => sentAt_isOk ?_ (List.all_eq_true.1 hL x hx)
  have h1 : sendTag x.label ∈ (C.sends.map (·.label)).map sendTag :=
    List.mem_map.2 ⟨x.label, List.mem_map.2 ⟨x, hx, rfl⟩, rfl⟩
  rw [ht] at h1
  exact List.all_eq_true.1 hs _ h1

end Johnson.Unfolds

#print axioms Johnson.Unfolds.sentAt_isOk
#print axioms Johnson.Unfolds.sentAt_no
#print axioms Johnson.Unfolds.mapM_isOk
#print axioms Johnson.Unfolds.sent_of
