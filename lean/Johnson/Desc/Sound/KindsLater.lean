-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/KindsLater.lean: the laws that are asked of the shared chain's and of the last
chain's sub-protocols, KIND BY KIND. Two definitions, and rules over letters with their proofs.

Why. The proof file's rows ask the first chain's laws kind by kind (`KindTiedR`,
`eachTiedR_of_kinds`: Johnson/Desc/Sound/TiedR.lean), but the two later chains' laws as whole rows
(`EachLawsBN`: Johnson/Desc/Sound/KeysByMake.lean; `EachOwn`: Johnson/Desc/Sound/Spine.lean). Here
each of the two rows is cut along a list of places, as the first chain's is.

What is said. ps is a list of places; piece number i of the row l stands at place number i.
  `KindLawsBN key on Q N ps l K`: every piece of l at a place of kind K has its law for a batch of
    N slots (`LeadsBN`), at its own number and its own error bounds.
  `eachLawsBN_of_kinds`: all kinds' shares, and the hand-over of the condition at the numbers of
    the row's pieces (one premise, free of kinds), give `EachLawsBN`.
  `KindOwn on means In Out O₀ ps l K`: every piece of l at a place of kind K has its own law
    (`Piece.Own`) and keeps the items that ride past it (`Piece.Frames`), at its own number.
  `eachOwn_of_kinds`: all kinds' shares give `EachOwn`.
  `kindLawsBN_of_each`, `kindOwn_of_each`: THE CUT LOSES NOTHING: each row gives every kind's share.
  `eachLawsBN_iff_kinds`, `eachOwn_iff_kinds`: both ways, where the row is no longer than ps.
  `sharedPlaces_kinds`, `lastPlaces_kinds`: the shared chain's list of places holds the kinds K1,
    K12, K14 and `frame` alone; the last chain's list K12, K14 and `frame` alone.
  `kindLawsBN_of_four`, `kindOwn_of_three`: so, at these two lists, the shares at these four (three)
    values give the share at every value of `KindName`.

Limits. Rules over letters: no law is paid and no member is shown. At a kind without a place in ps
a share asks nothing. That piece number i holds the sub-protocol of place number i is said nowhere
here: whoever pays a share reads it off the row l. `frame` is a value of `KindName`, and no kind of
sub-protocol: its share is asked like the others.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.KeysByMake
import Johnson.Desc.Sound.Spine
import Johnson.Desc.Last.BordersLast

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (KindName Place)
open VerifiableInference.Desc.Shared (sharedPlaces)
open VerifiableInference.Desc.Last (lastPlaces)

/-- The kinds in the shared chain's list of places. -/
theorem sharedPlaces_kinds (split : Bool) : ∀ a ∈ sharedPlaces split,
    a.kind = .frame ∨ a.kind = .K1 ∨ a.kind = .K12 ∨ a.kind = .K14 := by
  cases split <;> decide

/-- The kinds in the last chain's list of places. -/
theorem lastPlaces_kinds : ∀ a ∈ lastPlaces,
    a.kind = .frame ∨ a.kind = .K12 ∨ a.kind = .K14 := by
  decide

section Batch
variable {S Cl W κ : Type} {C : CK} {F : Frame} (key : ℕ → S × F.E.Str → κ)
  (on : ℕ → S × F.E.Str → Prop) (Q : ℕ → S × F.E.Str → S × F.E.Str → Prop) (N : ℕ)

/-- **One kind's share of a shared chain's laws.** -/
def KindLawsBN (ps : List Place) (l : List (Piece C F S Cl W)) (K : KindName) : Prop :=
  ∀ (i : ℕ) (q : Piece C F S Cl W) (a : Place), l[i]? = some q → ps[i]? = some a → a.kind = K →
    q.ior.red.LeadsBN (key i) (on i) (Q i) N q.err

/-- Place by place. -/
theorem eachLawsBN_of_places : ∀ (l : List (Piece C F S Cl W)) (k₀ : ℕ),
    (∀ (i : ℕ) (q : Piece C F S Cl W), l[i]? = some q →
      q.ior.red.LeadsBN (key (k₀ + i)) (on (k₀ + i)) (Q (k₀ + i)) N q.err ∧
        ∀ a b, on (k₀ + i) a → Q (k₀ + i) a b → on (k₀ + i + 1) b) →
    EachLawsBN key on Q N k₀ l
  | [], _, _ => trivial
  | p :: l, k₀, h =>
    ⟨(h 0 p rfl).1, (h 0 p rfl).2, eachLawsBN_of_places l (k₀ + 1) fun i q hq => by
      have := h (i + 1) q (by simpa using hq)
      rwa [show k₀ + (i + 1) = k₀ + 1 + i by omega] at this⟩

/-- **The shared chain's row, kind by kind.** hand: the hand-over of the condition, at the numbers
of the row's pieces alone. -/
theorem eachLawsBN_of_kinds (ps : List Place) (l : List (Piece C F S Cl W))
    (hlen : l.length ≤ ps.length) (H : ∀ K, KindLawsBN key on Q N ps l K)
    (hand : ∀ (i : ℕ) (q : Piece C F S Cl W), l[i]? = some q →
      ∀ a b, on i a → Q i a b → on (i + 1) b) : EachLawsBN key on Q N 0 l :=
  eachLawsBN_of_places key on Q N l 0 fun i q hq => by
    have hi : i < l.length := (List.getElem?_eq_some_iff.1 hq).1
    have hp : i < ps.length := Nat.lt_of_lt_of_le hi hlen
    rw [Nat.zero_add]
    exact ⟨H _ i q ps[i] hq (List.getElem?_eq_getElem hp) rfl, hand i q hq⟩

/-- The row gives the law and the hand-over at every place. -/
theorem lawAt_of_eachLawsBN : ∀ (l : List (Piece C F S Cl W)) (k₀ : ℕ),
    EachLawsBN key on Q N k₀ l → ∀ (i : ℕ) (q : Piece C F S Cl W), l[i]? = some q →
      q.ior.red.LeadsBN (key (k₀ + i)) (on (k₀ + i)) (Q (k₀ + i)) N q.err ∧
        ∀ a b, on (k₀ + i) a → Q (k₀ + i) a b → on (k₀ + i + 1) b
  | [], _, _, i, q, hq => by simp at hq
  | p :: l, k₀, h, 0, q, hq => by
    obtain rfl : p = q := by simpa using hq
    exact ⟨h.1, h.2.1⟩
  | p :: l, k₀, h, i + 1, q, hq => by
    have := lawAt_of_eachLawsBN l (k₀ + 1) h.2.2 i q (by simpa using hq)
    rwa [show k₀ + 1 + i = k₀ + (i + 1) by omega] at this

/-- **The cut loses nothing.** -/
theorem kindLawsBN_of_each (ps : List Place) (l : List (Piece C F S Cl W))
    (h : EachLawsBN key on Q N 0 l) (K : KindName) : KindLawsBN key on Q N ps l K :=
  fun i q _ hq _ _ => by
    have := (lawAt_of_eachLawsBN key on Q N l 0 h i q hq).1
    rwa [Nat.zero_add] at this

/-- **The row is just all kinds' shares with the hand-over.** -/
theorem eachLawsBN_iff_kinds (ps : List Place) (l : List (Piece C F S Cl W))
    (hlen : l.length ≤ ps.length) :
    EachLawsBN key on Q N 0 l ↔ (∀ K, KindLawsBN key on Q N ps l K) ∧
      ∀ (i : ℕ) (q : Piece C F S Cl W), l[i]? = some q →
        ∀ a b, on i a → Q i a b → on (i + 1) b :=
  ⟨fun h => ⟨kindLawsBN_of_each key on Q N ps l h, fun i q hq => by
      have := (lawAt_of_eachLawsBN key on Q N l 0 h i q hq).2
      rwa [Nat.zero_add] at this⟩,
    fun h => eachLawsBN_of_kinds key on Q N ps l hlen h.1 h.2⟩

/-- **At the shared chain's list of places four shares are all.** -/
theorem kindLawsBN_of_four (split : Bool) (l : List (Piece C F S Cl W))
    (h₀ : KindLawsBN key on Q N (sharedPlaces split) l .frame)
    (h₁ : KindLawsBN key on Q N (sharedPlaces split) l .K1)
    (h₁₂ : KindLawsBN key on Q N (sharedPlaces split) l .K12)
    (h₁₄ : KindLawsBN key on Q N (sharedPlaces split) l .K14) (K : KindName) :
    KindLawsBN key on Q N (sharedPlaces split) l K :=
  fun i q a hq ha _ => by
    rcases sharedPlaces_kinds split a (List.mem_of_getElem? ha) with e | e | e | e
    · exact h₀ i q a hq ha e
    · exact h₁ i q a hq ha e
    · exact h₁₂ i q a hq ha e
    · exact h₁₄ i q a hq ha e

end Batch

section Own
variable {S Cl W ι : Type} {C : CK} {F : Frame} (on : ℕ → S × F.E.Str → Prop)
  (means : ι → S × F.E.Str → W → Prop) (In Out : ℕ → ι → Prop) (O₀ : ι → Prop)

/-- **One kind's share of a chain's laws at a table of items.** -/
def KindOwn (ps : List Place) (l : List (Piece C F S Cl W)) (K : KindName) : Prop :=
  ∀ (i : ℕ) (q : Piece C F S Cl W) (a : Place), l[i]? = some q → ps[i]? = some a → a.kind = K →
    q.Own (on i) (on (i + 1)) means (In i) (Out i) ∧
      q.Frames (on i) (on (i + 1)) means (openAfter In Out O₀ i) (In i)

/-- Place by place. -/
theorem eachOwn_of_places : ∀ (l : List (Piece C F S Cl W)) (k₀ : ℕ),
    (∀ (i : ℕ) (q : Piece C F S Cl W), l[i]? = some q →
      q.Own (on (k₀ + i)) (on (k₀ + i + 1)) means (In (k₀ + i)) (Out (k₀ + i)) ∧
        q.Frames (on (k₀ + i)) (on (k₀ + i + 1)) means (openAfter In Out O₀ (k₀ + i))
          (In (k₀ + i))) →
    EachOwn on means In Out O₀ k₀ l
  | [], _, _ => trivial
  | p :: l, k₀, h =>
    ⟨(h 0 p rfl).1, (h 0 p rfl).2, eachOwn_of_places l (k₀ + 1) fun i q hq => by
      have := h (i + 1) q (by simpa using hq)
      rwa [show k₀ + (i + 1) = k₀ + 1 + i by omega] at this⟩

/-- **The row at a table of items, kind by kind.** -/
theorem eachOwn_of_kinds (ps : List Place) (l : List (Piece C F S Cl W))
    (hlen : l.length ≤ ps.length) (H : ∀ K, KindOwn on means In Out O₀ ps l K) :
    EachOwn on means In Out O₀ 0 l :=
  eachOwn_of_places on means In Out O₀ l 0 fun i q hq => by
    have hi : i < l.length := (List.getElem?_eq_some_iff.1 hq).1
    have hp : i < ps.length := Nat.lt_of_lt_of_le hi hlen
    rw [Nat.zero_add]
    exact H _ i q ps[i] hq (List.getElem?_eq_getElem hp) rfl

/-- The row gives both at every place. -/
theorem ownAt_of_eachOwn : ∀ (l : List (Piece C F S Cl W)) (k₀ : ℕ),
    EachOwn on means In Out O₀ k₀ l → ∀ (i : ℕ) (q : Piece C F S Cl W), l[i]? = some q →
      q.Own (on (k₀ + i)) (on (k₀ + i + 1)) means (In (k₀ + i)) (Out (k₀ + i)) ∧
        q.Frames (on (k₀ + i)) (on (k₀ + i + 1)) means (openAfter In Out O₀ (k₀ + i))
          (In (k₀ + i))
  | [], _, _, i, q, hq => by simp at hq
  | p :: l, k₀, h, 0, q, hq => by
    obtain rfl : p = q := by simpa using hq
    exact ⟨h.1, h.2.1⟩
  | p :: l, k₀, h, i + 1, q, hq => by
    have := ownAt_of_eachOwn l (k₀ + 1) h.2.2 i q (by simpa using hq)
    rwa [show k₀ + 1 + i = k₀ + (i + 1) by omega] at this

/-- **The cut loses nothing.** -/
theorem kindOwn_of_each (ps : List Place) (l : List (Piece C F S Cl W))
    (h : EachOwn on means In Out O₀ 0 l) (K : KindName) : KindOwn on means In Out O₀ ps l K :=
  fun i q _ hq _ _ => by
    have := ownAt_of_eachOwn on means In Out O₀ l 0 h i q hq
    rwa [Nat.zero_add] at this

/-- **The row is just all kinds' shares.** -/
theorem eachOwn_iff_kinds (ps : List Place) (l : List (Piece C F S Cl W))
    (hlen : l.length ≤ ps.length) :
    EachOwn on means In Out O₀ 0 l ↔ ∀ K, KindOwn on means In Out O₀ ps l K :=
  ⟨kindOwn_of_each on means In Out O₀ ps l, eachOwn_of_kinds on means In Out O₀ ps l hlen⟩

/-- **At the last chain's list of places three shares are all.** -/
theorem kindOwn_of_three (l : List (Piece C F S Cl W))
    (h₀ : KindOwn on means In Out O₀ lastPlaces l .frame)
    (h₁₂ : KindOwn on means In Out O₀ lastPlaces l .K12)
    (h₁₄ : KindOwn on means In Out O₀ lastPlaces l .K14) (K : KindName) :
    KindOwn on means In Out O₀ lastPlaces l K :=
  fun i q a hq ha _ => by
    rcases lastPlaces_kinds a (List.mem_of_getElem? ha) with e | e | e
    · exact h₀ i q a hq ha e
    · exact h₁₂ i q a hq ha e
    · exact h₁₄ i q a hq ha e

end Own

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.eachLawsBN_of_kinds
#print axioms VerifiableInference.Desc.Sound.kindLawsBN_of_each
#print axioms VerifiableInference.Desc.Sound.eachOwn_of_kinds
#print axioms VerifiableInference.Desc.Sound.kindOwn_of_each
#print axioms VerifiableInference.Desc.Sound.eachLawsBN_iff_kinds
#print axioms VerifiableInference.Desc.Sound.eachOwn_iff_kinds
#print axioms VerifiableInference.Desc.Sound.kindLawsBN_of_four
#print axioms VerifiableInference.Desc.Sound.kindOwn_of_three
