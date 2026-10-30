-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/HearFrame.lean: A FRAME FOR HEARINGS ON SHAPES: what a hearing in the monad
Hear (Johnson/Desc/Kinds/HeadParts.lean: from the ledger of hidden scalars and the rounds not yet
read: nothing, or a value, the ledger behind and the rounds that are left) does to the ledger's
shape (LedSh, Parts.lean), and which shape its value has. General laws; nothing is evaluated.
  1 **`HearSh x sh f`**: x: a hearing; sh: the shape of what it hands back; f: its step on the
    ledger's shape: where x returns and f returns, f returns the shape of x's value and the shape of
    the ledger behind. `HearSh.pure`; **`HearSh.bind`**: the frame is closed under bind, where the
    continuation's step hangs on the value through its shape alone; `HearSh.map`: a weaker shape of
    the value.
  2 The parts that leave the ledger: `HearSh.need`, `HearSh.round` (n scalars, k elements),
    `HearSh.stretch`, `HearSh.ledger`, `HearSh.lay`.
  3 Hidden scalars: `hidSh`, `slotsSh`, `LedSh.moved`, `ledSh_moved`, `hideS`, **`HearSh.hide`**: n
    scalars are laid under the next n numbers: the step asks that these slots are there and free
    (freeB), moves the next free number on and fills them (by Parts.lean's hide_of_B). `mapM_sh`,
    `HearSh.hiddenFrom`.
Limits. THE WEAK FORM: every law stands under the step's own return: a return of the hearing alone
does not give that the ledger's arrays have their sizes, which the step on shapes asks. That a
hearing returns where its step does is not said here. HearSh x sh f holds of every hearing at a step
that never returns, and of every step at a hearing that never returns. THE STEPS GIVEN FOR need,
round, stretch AND hiddenFrom ALWAYS RETURN, also where the hearing refuses (nothing is there; no
round is left; the round has other counts; fewer rounds are left than the stretch asks; a slot is
not shown): of these four the frame gives "carries" alone. Of the rounds nothing is kept but counts.
Nothing on soundness, completeness or hiding.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Shape.Parts
import Johnson.Desc.Kinds.HeadParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes OnBytes.Model VerifiableInference.Desc
open VerifiableInference.Desc.Kinds (Hear Hid)

/-! ## 1 The frame -/

/-- **A hearing on shapes.** x: a hearing; sh: the shape of what it hands back; f: its step on the
ledger's shape. Where x returns and f returns, f returns the shape of x's value and the shape of the
ledger behind. -/
def HearSh {α β : Type} (x : Hear α) (sh : α → β) (f : LedSh → Option (β × LedSh)) : Prop :=
  ∀ F rs a G left y, x F rs = some (a, G, left) → f (ledSh F) = some y → y = (sh a, ledSh G)

theorem HearSh.pure {α β : Type} (a : α) (sh : α → β) :
    HearSh (Pure.pure a : Hear α) sh fun L => some (sh a, L) := by
  intro F rs a' G left y hx hf
  obtain ⟨rfl, rfl, -⟩ : a = a' ∧ F = G ∧ rs = left := by
    have e : (a, F, rs) = (a', G, left) := Option.some.inj hx
    exact ⟨congrArg (·.1) e, congrArg (·.2.1) e, congrArg (·.2.2) e⟩
  exact (Option.some.inj hf).symm

/-- **The frame is closed under bind**, where the continuation's step hangs on the value through its
shape alone. -/
theorem HearSh.bind {α β γ δ : Type} {x : Hear α} {k : α → Hear γ} {sh : α → β} {sh' : γ → δ}
    {f : LedSh → Option (β × LedSh)} {kS : β → LedSh → Option (δ × LedSh)}
    (hx : HearSh x sh f) (hk : ∀ a, HearSh (k a) sh' (kS (sh a))) :
    HearSh (x >>= k) sh' fun L => (f L).bind fun y => kS y.1 y.2 := by
  intro F rs c H left y h hf
  have h' : (match x F rs with
    | some (a, G, l) => k a G l
    | none => none) = some (c, H, left) := h
  cases hxx : x F rs with
  | none =>
    rw [hxx] at h'
    cases h'
  | some q =>
    obtain ⟨a, G, l⟩ := q
    rw [hxx] at h'
    obtain ⟨y₁, h1, h2⟩ := Option.bind_eq_some_iff.1 hf
    obtain rfl := hx F rs a G l y₁ hxx h1
    exact hk a G l c H left y h' h2

/-- A weaker shape of the value. -/
theorem HearSh.map {α β γ : Type} {x : Hear α} {sh : α → β} {f : LedSh → Option (β × LedSh)}
    (hx : HearSh x sh f) (g : β → γ) :
    HearSh x (fun a => g (sh a)) fun L => (f L).map fun y => (g y.1, y.2) := by
  intro F rs a G left y h hf
  obtain ⟨y₁, h1, rfl⟩ := Option.map_eq_some_iff.1 hf
  rw [hx F rs a G left y₁ h h1]

/-! ## 2 The parts that leave the ledger -/

theorem HearSh.need {α β : Type} (o : Option α) (sh : α → β) (b : β)
    (h : ∀ a, o = some a → sh a = b) : HearSh (Hear.need o) sh fun L => some (b, L) := by
  intro F rs a G left y hx hf
  obtain ⟨a', ha, e⟩ := Option.map_eq_some_iff.1 hx
  obtain ⟨rfl, rfl, -⟩ : a' = a ∧ F = G ∧ rs = left :=
    ⟨congrArg (·.1) e, congrArg (·.2.1) e, congrArg (·.2.2) e⟩
  rw [← Option.some.inj hf, h a' ha]

/-- The next round: n scalars, k elements. -/
theorem HearSh.round (n k : Nat) :
    HearSh (Hear.round n k) (fun x => (x.1.length, x.2.length)) fun L => some ((n, k), L) := by
  intro F rs a G left y hx hf
  cases rs with
  | nil => cases hx
  | cons r rest =>
    obtain ⟨a', ha, e⟩ := Option.map_eq_some_iff.1 hx
    obtain ⟨rfl, rfl, -⟩ : a' = a ∧ F = G ∧ rest = left :=
      ⟨congrArg (·.1) e, congrArg (·.2.1) e, congrArg (·.2.2) e⟩
    rw [← Option.some.inj hf]
    unfold Part.MaskedSum.roundOf at ha
    obtain ⟨s, -, hs⟩ := Option.bind_eq_some_iff.1 ha
    split at hs
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain rfl := Option.some.inj hs
      show ((n, k), ledSh F) = ((s.length, (r.drawn.elems.map E.ofTriple).length), ledSh F)
      rw [List.length_map, hc.1, hc.2]
    · cases hs

theorem HearSh.stretch (n : Nat) :
    HearSh (Hear.stretch n) List.length fun L => some (n, L) := by
  intro F rs a G left y hx hf
  unfold Hear.stretch at hx
  split at hx
  · cases hx
  · rename_i hl
    have e : (rs.take n, F, rs.drop n) = (a, G, left) := Option.some.inj hx
    obtain ⟨rfl, rfl⟩ : rs.take n = a ∧ F = G := ⟨congrArg (·.1) e, congrArg (·.2.1) e⟩
    rw [← Option.some.inj hf, List.length_take]
    congr 1
    omega

theorem HearSh.ledger : HearSh Hear.ledger ledSh fun L => some (L, L) := by
  intro F rs a G left y hx hf
  have e : (F, F, rs) = (a, G, left) := Option.some.inj hx
  obtain ⟨rfl, rfl⟩ : F = a ∧ F = G := ⟨congrArg (·.1) e, congrArg (·.2.1) e⟩
  exact (Option.some.inj hf).symm

theorem HearSh.lay (F₀ : Fork) :
    HearSh (Hear.lay F₀) (fun _ => ()) fun _ => some ((), ledSh F₀) := by
  intro F rs a G left y hx hf
  have e : ((), F₀, rs) = (a, G, left) := Option.some.inj hx
  obtain rfl : F₀ = G := congrArg (·.2.1) e
  exact (Option.some.inj hf).symm

/-! ## 3 Hidden scalars -/

/-- A hidden scalar's shape: its form's. -/
def hidSh (h : Hid) : AffSh := affSh h.var

/-- The forms "slot first", "slot first + 1", … : n of them. -/
def slotsSh (first n : Nat) : List AffSh := (List.range n).map fun j => AffSh.mk [] [first + j]

/-- The next free number moves on by n. -/
def LedSh.moved (L : LedSh) (n : Nat) : LedSh :=
  LedSh.mk L.ns L.shown L.factors L.got L.owed L.planClaims L.trees (L.next + n) L.coefs L.claims
    L.drawn L.handed L.shut

theorem ledSh_moved (F : Fork) (n : Nat) :
    ledSh { F with next := F.next + n } = (ledSh F).moved n := rfl

/-- n scalars are laid under the next n numbers, on the shape. -/
def hideS (n : Nat) (L : LedSh) : Option (List AffSh × LedSh) :=
  if freeB (L.moved n) L.next n then
    some (slotsSh L.next n, (L.moved n).setGot (fillB L.got L.next n))
  else none

theorem HearSh.hide (v : List E) :
    HearSh (Kinds.hide v) (fun a => a.toList.map hidSh) (hideS v.length) := by
  intro F rs a G left y hx hf
  unfold hideS at hf
  split at hf
  · rename_i hc
    obtain ⟨G', hG, e⟩ := Option.map_eq_some_iff.1 hx
    obtain ⟨rfl, rfl⟩ : _ = a ∧ G' = G := ⟨congrArg (·.1) e, congrArg (·.2.1) e⟩
    have hc' : freeB (ledSh { F with next := F.next + v.length }) F.next v.toArray.size = true := by
      rw [ledSh_moved, List.size_toArray]
      exact hc
    obtain ⟨H, hH, -, -, eH⟩ := hide_of_B hc' oneE
    obtain rfl : H = G' := Option.some.inj (hH.symm.trans hG)
    rw [← Option.some.inj hf, eH, ledSh_moved, List.size_toArray]
    refine Prod.ext ?_ rfl
    show slotsSh F.next v.length = _
    unfold slotsSh
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp [hidSh, affSh_slot]
  · cases hf

/-- What a mapM that returns hands back, seen through a shape that hangs on the argument alone. -/
theorem mapM_sh {α β γ : Type} (g : α → Option β) (sh : β → γ) (k : α → γ)
    (h : ∀ x y, g x = some y → sh y = k x) :
    ∀ (xs : List α) (l : List β), xs.mapM g = some l → l.map sh = xs.map k
  | [], l, hl => by
    have e : l = [] := by simpa using hl.symm
    subst e
    rfl
  | x :: xs, l, hl => by
    rw [List.mapM_cons] at hl
    cases hg : g x with
    | none => simp [hg] at hl
    | some y =>
      cases hm : xs.mapM g with
      | none => simp [hg, hm] at hl
      | some ys =>
        simp [hg, hm] at hl
        subst hl
        rw [List.map_cons, List.map_cons, h x y hg, mapM_sh g sh k h xs ys hm]

theorem HearSh.hiddenFrom (first n : Nat) :
    HearSh (Kinds.hiddenFrom first n) (fun a => a.toList.map hidSh)
      fun L => some (slotsSh first n, L) := by
  intro F rs a G left y hx hf
  obtain ⟨l, hl, e⟩ := Option.map_eq_some_iff.1 hx
  obtain ⟨rfl, rfl⟩ : l.toArray = a ∧ F = G := ⟨congrArg (·.1) e, congrArg (·.2.1) e⟩
  rw [← Option.some.inj hf]
  refine Prod.ext ?_ rfl
  show slotsSh first n = l.map hidSh
  refine (mapM_sh _ hidSh (fun j => AffSh.mk [] [first + j]) (fun j y hy => ?_) _ l hl).symm
  obtain ⟨x, -, rfl⟩ := Option.map_eq_some_iff.1 hy
  exact affSh_slot (first + j)

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.HearSh.pure
#print axioms VerifiableInference.Desc.First.Shape.HearSh.bind
#print axioms VerifiableInference.Desc.First.Shape.HearSh.map
#print axioms VerifiableInference.Desc.First.Shape.HearSh.need
#print axioms VerifiableInference.Desc.First.Shape.HearSh.round
#print axioms VerifiableInference.Desc.First.Shape.HearSh.stretch
#print axioms VerifiableInference.Desc.First.Shape.HearSh.ledger
#print axioms VerifiableInference.Desc.First.Shape.HearSh.lay
#print axioms VerifiableInference.Desc.First.Shape.ledSh_moved
#print axioms VerifiableInference.Desc.First.Shape.HearSh.hide
#print axioms VerifiableInference.Desc.First.Shape.mapM_sh
#print axioms VerifiableInference.Desc.First.Shape.HearSh.hiddenFrom
#print axioms VerifiableInference.Desc.First.Shape.HearSh
#print axioms VerifiableInference.Desc.First.Shape.hidSh
#print axioms VerifiableInference.Desc.First.Shape.slotsSh
#print axioms VerifiableInference.Desc.First.Shape.LedSh.moved
#print axioms VerifiableInference.Desc.First.Shape.hideS
