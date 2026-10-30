-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/Travels.lean: what a sending leaves behind as a property of the statement alone,
that it travels along effects which keep shapes, marks and sample rows, and so holds behind a
segment's later moment and behind the first segment's opening.

Main names: Pinned (a message is marked, its sample rows are on its own tables, and of a list at
most one member, as a vector of the sample map, meets them); SameSamples; Pinned.travels;
pinned_behind; joinP_same, joinAll_same, joinOwnP_same, newGroupP_same; pinned_later, pinned_commit,
pinned_first.

What is not claimed. The premises of the joined law stand: the tests on the plan, rounds that fit,
seeds that read as joint seeds which are not bad. The blocks at the first chain's record are not
treated. Nothing on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.Around
import Johnson.Desc.K1.Law.KeepsOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice
open VerifiableInference.Desc.First.Send (joinOwnP joinAll)

variable {L Cl : Type}

/-- **A message is pinned**, at a statement: it is marked as sampled, its sample rows are on its own
tables, and two members of the list that both meet all its sample rows are one vector of the sample
map. -/
def Pinned (Lst : (Part → Nat → GE) → Prop) (m : Msg) (S : Statement) (o : Nat) : Prop :=
  ∃ x, S.oracles[o]? = some x ∧ x.sampled = true ∧
    (∀ r ∈ x.sampleRows.toList, Means.RowIn S { code := 0, members := #[o] } r) ∧
    ∀ w w' : Means.Words GE, Lst (w o) → Lst (w' o) →
      Means.AllSay rdE S x.sampleRows.toList w → Means.AllSay rdE S x.sampleRows.toList w' →
      m.vec (w o) = m.vec (w' o)

/-- Every message has the mark and the sample rows that it had. -/
def SameSamples (S S' : Statement) : Prop :=
  ∀ j : Nat, (S'.oracles[j]?).map (fun x : OnBytes.Oracle => (x.sampled, x.sampleRows)) =
    (S.oracles[j]?).map fun x : OnBytes.Oracle => (x.sampled, x.sampleRows)

theorem SameSamples.trans {S S' S'' : Statement} (h1 : SameSamples S S')
    (h2 : SameSamples S' S'') : SameSamples S S'' := fun j => (h2 j).trans (h1 j)

/-- **It travels.** -/
theorem Pinned.travels {Lst : (Part → Nat → GE) → Prop} {m : Msg} {S S' : Statement} {o : Nat}
    (h : Pinned Lst m S o) (hE : Means.Extends S S') (hs : SameSamples S S') :
    Pinned Lst m S' o := by
  obtain ⟨x, hx, h1, h2, h3⟩ := h
  have e := hs o
  rw [hx] at e
  obtain ⟨x', hx', e⟩ := Option.map_eq_some_iff.1 e
  obtain ⟨e1, e2⟩ := Prod.mk.inj e
  refine ⟨x', hx', e1.trans h1, ?_, ?_⟩
  · rw [e2]
    exact fun r hr => Means.RowIn.extends hE (fun _ c => c) (h2 r hr)
  · rw [e2]
    exact fun w w' a b c d => h3 w w' a b
      (fun r hr => (Means.says_extends rdE hE (h2 r hr) w).1 (c r hr))
      (fun r hr => (Means.says_extends rdE hE (h2 r hr) w').1 (d r hr))

/-- **Behind the sending's yes every new sampled message is pinned.** -/
theorem pinned_behind (P : Par) (Lst : Nat → (Part → Nat → GE) → Prop) (owed : Option Nat)
    (d d' : DState L) (r₁ r₂ : Fmt.RoundView) (ids : Array Nat) (hB : planOkOwn P = true)
    (hfit : roundsFit (rounds P) [r₁, r₂] = true)
    (hyes : decideSend P owed d [r₁, r₂] = .ok (ids, d')) (ρ : Seeds P) (hρ : ReadsAs P r₁ ρ)
    (hgood : ¬ Bad P Lst ρ) (k : Fin (shapesOf P).length) (hk : sampledAt P k)
    (hne : ∃ u, Lst k.val u) :
    Pinned (Lst k.val) (msgAt P k) d'.st (d.st.oracles.size + k.val) := by
  obtain ⟨u, hu⟩ := hne
  obtain ⟨x, hx, hs, _⟩ := unique_behind P Lst owed d d' r₁ r₂ ids hB hfit hyes ρ hρ hgood k hk
    (fun _ => u) (fun _ => u) hu hu
  refine ⟨x, hx, hs, behind_rows_on P owed d d' r₁ r₂ ids hB hfit hyes _ x hx
    (Nat.le_add_right _ _), fun w w' a b c e => ?_⟩
  obtain ⟨x', hx', _, h3⟩ := unique_behind P Lst owed d d' r₁ r₂ ids hB hfit hyes ρ hρ hgood k hk
    w w' a b
  obtain rfl : x = x' := Option.some.inj (hx.symm.trans hx')
  exact h3 c e

/-! ## The effects around the sending -/

theorem joinP_same (d d' : DState L) (g o : Nat) (kept : Bool)
    (h : Ground.joinP d g o kept = some d') :
    Means.Extends d.st d'.st ∧ SameSamples d.st d'.st := by
  unfold Ground.joinP at h
  split at h
  · obtain ⟨G, _, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨Means.extends_withMessageInGroup _ _ _ _ _, fun j => Means.map_modify _ _ _ _ _ fun _ => rfl⟩
  · cases h

theorem joinAll_same (p : GPar) (g : Nat) : ∀ (l : List (ReqMessage × Nat)) (d d' : DState L),
    joinAll groundG p g l d = some d' → Means.Extends d.st d'.st ∧ SameSamples d.st d'.st
  | [], d, d', h => by
    obtain rfl : d = d' := Option.some.inj h
    exact ⟨Means.Extends.refl _, fun _ => rfl⟩
  | x :: l, d, d', h => by
    obtain ⟨d₁, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨a1, a2⟩ := joinP_same d d₁ _ _ _ h1
    obtain ⟨b1, b2⟩ := joinAll_same p g l d₁ d' h2
    exact ⟨a1.trans b1, a2.trans b2⟩

theorem joinOwnP_same (p : GPar) (d d' : DState L) (f f' : ReqFrame) (sent : List ReqMessage)
    (ids : Array Nat) (h : joinOwnP groundG p d f sent ids = some (f', d')) :
    Means.Extends d.st d'.st ∧ SameSamples d.st d'.st := by
  unfold joinOwnP at h
  split at h
  · obtain ⟨d₁, h1, e⟩ := Option.map_eq_some_iff.1 h
    obtain rfl : d₁ = d' := (Prod.mk.inj e).2
    exact joinAll_same p _ _ d d₁ h1
  · cases h

theorem newGroupP_size (d d' : DState L) (a b g : Nat)
    (h : Ground.newGroupP d a b = some (g, d')) : d'.st.oracles = d.st.oracles := by
  unfold Ground.newGroupP at h
  split at h
  · obtain rfl : _ = d' := (Prod.mk.inj (Option.some.inj h)).2
    rfl
  · cases h

/-! ## Behind the kind's two other decisions -/

/-- **Behind a yes of a later moment.** -/
theorem pinned_later (P : Par) (Lst : Nat → (Part → Nat → GE) → Prop) (owed : Option Nat)
    (c c' : ChainCheck) (w w' : DState Unit) (r₁ r₂ : Fmt.RoundView) (hB : planOkOwn P = true)
    (hfit : roundsFit (rounds P) [r₁, r₂] = true)
    (hyes : laterOwn P owed c w [r₁, r₂] = .ok (c', w')) (ρ : Seeds P) (hρ : ReadsAs P r₁ ρ)
    (hgood : ¬ Bad P Lst ρ) (k : Fin (shapesOf P).length) (hk : sampledAt P k)
    (hne : ∃ u, Lst k.val u) :
    Pinned (Lst k.val) (msgAt P k) w'.st (w.st.oracles.size + k.val) := by
  obtain ⟨ids, d₁, f', h1, h2, _⟩ := laterOwn_ok P owed c c' w w' _ hyes
  obtain ⟨a1, a2⟩ := joinOwnP_same _ _ _ _ _ _ _ h2
  exact (pinned_behind P Lst owed w d₁ r₁ r₂ ids hB hfit h1 ρ hρ hgood k hk hne).travels a1 a2

/-- **Behind a yes of the block of a later moment.** -/
theorem pinned_commit (P : Par) (Lst : Nat → (Part → Nat → GE) → Prop) (link moment : Nat)
    (arrays : Option (List Nat)) (s s' : Owing (L3.St (DState Unit))) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hB : planOkOwn P = true)
    (hfit : roundsFit (rounds P) [r₁, r₂] = true)
    (hyes : (commitOwn P link moment arrays : Block _ Cl).decide s [r₁, r₂] gs = .ok s')
    (ρ : Seeds P) (hρ : ReadsAs P r₁ ρ) (hgood : ¬ Bad P Lst ρ) (k : Fin (shapesOf P).length)
    (hk : sampledAt P k) (hne : ∃ u, Lst k.val u) :
    Pinned (Lst k.val) (msgAt P k) s'.held.w.st (s.held.w.st.oracles.size + k.val) := by
  obtain ⟨ids, d₁, f', h1, h2⟩ := commitOwn_ok P link moment arrays s s' _ gs hyes
  obtain ⟨a1, a2⟩ := joinOwnP_same _ _ _ _ _ _ _ h2
  exact (pinned_behind P Lst s.owed s.held.w d₁ r₁ r₂ ids hB hfit h1 ρ hρ hgood k hk hne).travels
    a1 a2

/-- **Behind a yes of the first segment's opening.** -/
theorem pinned_first (P : Par) (Lst : Nat → (Part → Nat → GE) → Prop) (owed : Option Nat)
    (c c' : ChainCheck) (d d' : DState Unit) (r₁ r₂ : Fmt.RoundView) (hB : planOkOwn P = true)
    (hfit : roundsFit (rounds P) [r₁, r₂] = true)
    (hyes : firstOwn P owed c d [r₁, r₂] = .ok (c', d')) (ρ : Seeds P) (hρ : ReadsAs P r₁ ρ)
    (hgood : ¬ Bad P Lst ρ) (k : Fin (shapesOf P).length) (hk : sampledAt P k)
    (hne : ∃ u, Lst k.val u) :
    Pinned (Lst k.val) (msgAt P k) d'.st (d.st.oracles.size + k.val) := by
  obtain ⟨g, d₁, ids, d₂, h0, h1, f₁, own, mine, f₂, h2⟩ := firstOwn_ok P owed c c' d d' _ hyes
  obtain ⟨a1, a2⟩ := joinOwnP_same _ _ _ _ _ _ _ h2
  have := (pinned_behind P Lst owed d₁ d₂ r₁ r₂ ids hB hfit h1 ρ hρ hgood k hk hne).travels a1 a2
  rwa [newGroupP_size d d₁ _ _ g h0] at this

end VerifiableInference.Desc.K1
