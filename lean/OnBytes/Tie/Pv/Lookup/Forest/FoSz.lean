-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoSz.lean.
How many elements each round of a stretch of the byte-level verifier's run sends and draws.

A run of a routine of the byte-level verifier is described by the list of the calls that it makes of
the channel's routines (Ev, Evs). Read as rounds of plain data (Fo.flEv), such a list has sizes: for
each round the number of elements sent and the number drawn. This file gives the words in which
these sizes are said and put together, stretch by stretch.

The point of the file: ON A VIEW THE ROUNDS BETWEEN TWO CONTEXTS ARE FIXED BY THE TWO CONTEXTS. So
the sizes may be found on any list of calls that leads from the one context to the other, and hold
of every other such list. A lemma that describes a stretch need not hand its sizes on.

Defines:
  szEv l: the sizes of the rounds of the calls l. No reading enters.
  SzOn c c' p: some row of rounds leads from the context c to c' and has the sizes p.
States:
  flEv_sz: the sizes of Fo.flEv ρ l are szEv l, for every reading ρ.
  szEv_append: the sizes of two rows of rounds, one after the other.
  SzOn.nil, SzOn.append, SzOn.of, SzOn.clean.
  took_unique: on a view the rounds between two contexts are fixed.
  SzOn.any: on a view, EVERY row of rounds from c to c' has the sizes p, under every reading.
  SzOn.view: on a view, the rounds that lie between c and c' have the sizes p.
  foldlM_sz: a loop's sizes are its steps' sizes, one after the other.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoRds

set_option autoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.PscRun

/-- The sizes of the rounds, from the number of elements already received of the open message. -/
def szGo : ℕ → List Ev → List (ℕ × ℕ)
  | _, [] => []
  | a, .sum _ :: l => szGo (a + 1) l
  | a, .read _ v :: l => szGo (a + v.size) l
  | a, .ans _ _ :: l => (a, 1) :: szGo 0 l
  | a, .ansNZ _ _ :: l => (a, 1) :: szGo 0 l
  | a, .empty _ :: l => (a, 0) :: szGo 0 l
  | a, .point _ _ v :: l => (a, v.size) :: szGo 0 l

/-- For each round: how many elements are sent, how many are drawn. -/
def szEv (l : List Ev) : List (ℕ × ℕ) := szGo 0 l

section
variable {K : Type} [CommRing K] (ρ : Reading K)

theorem flGo_sz : ∀ (l : List Ev) (acc : List K),
    (flGo ρ acc l).map (fun r => (r.1.length, r.2.length)) = szGo acc.length l
  | [], _ => rfl
  | .sum x :: l, acc => by
    show (flGo ρ (acc ++ [ρ.val x]) l).map _ = szGo (acc.length + 1) l
    rw [flGo_sz l]
    simp
  | .read _ v :: l, acc => by
    show (flGo ρ (acc ++ v.toList.map ρ.val) l).map _ = szGo (acc.length + v.size) l
    rw [flGo_sz l]
    simp
  | .ans _ x :: l, acc => by
    show (acc.length, 1) :: (flGo ρ [] l).map _ = (acc.length, 1) :: szGo 0 l
    rw [flGo_sz l]
    rfl
  | .ansNZ _ x :: l, acc => by
    show (acc.length, 1) :: (flGo ρ [] l).map _ = (acc.length, 1) :: szGo 0 l
    rw [flGo_sz l]
    rfl
  | .empty _ :: l, acc => by
    show (acc.length, 0) :: (flGo ρ [] l).map _ = (acc.length, 0) :: szGo 0 l
    rw [flGo_sz l]
    rfl
  | .point _ _ v :: l, acc => by
    show (acc.length, (v.toList.map ρ.val).length) :: (flGo ρ [] l).map _ =
      (acc.length, v.size) :: szGo 0 l
    rw [flGo_sz l]
    simp

/-- The sizes of the rounds of plain data, under every reading. -/
theorem flEv_sz (l : List Ev) :
    (flEv ρ l).map (fun r => (r.1.length, r.2.length)) = szEv l := flGo_sz ρ l []

end

theorem szEv_append {l₁ : List Ev} (h : Rds l₁) (l₂ : List Ev) :
    szEv (l₁ ++ l₂) = szEv l₁ ++ szEv l₂ := by
  induction h with
  | nil => rfl
  | read n v r x _ ih => exact congrArg ((0 + v.size, 1) :: ·) ih
  | readNZ n v r x _ ih => exact congrArg ((0 + v.size, 1) :: ·) ih
  | values n v r _ ih => exact congrArg ((0 + v.size, 0) :: ·) ih
  | sum mu r x _ ih => exact congrArg ((0 + 1, 1) :: ·) ih
  | ans r x _ ih => exact congrArg ((0, 1) :: ·) ih
  | point r n v _ ih => exact congrArg ((0, v.size) :: ·) ih

/-- Some row of rounds leads from c to c' and has the sizes p. -/
def SzOn (c c' : Ctx) (p : List (ℕ × ℕ)) : Prop := ∃ l, Evs l c c' ∧ Rds l ∧ szEv l = p

theorem SzOn.of {c c' : Ctx} {l : List Ev} (he : Evs l c c') (hl : Rds l) : SzOn c c' (szEv l) :=
  ⟨l, he, hl, rfl⟩

theorem SzOn.nil (c : Ctx) : SzOn c c [] := ⟨[], rfl, Rds.nil, rfl⟩

theorem SzOn.append {c c₁ c' : Ctx} {p q : List (ℕ × ℕ)} (h1 : SzOn c c₁ p) (h2 : SzOn c₁ c' q) :
    SzOn c c' (p ++ q) := by
  obtain ⟨l₁, e1, r1, s1⟩ := h1
  obtain ⟨l₂, e2, r2, s2⟩ := h2
  exact ⟨l₁ ++ l₂, (evs_append _ _ _ _).2 ⟨_, e1, e2⟩, r1.append r2,
    by rw [szEv_append r1, s1, s2]⟩

theorem SzOn.clean {c c' : Ctx} {p : List (ℕ × ℕ)} (h : SzOn c c' p) (hc : Clean c) : Clean c' := by
  obtain ⟨l, e, r, _⟩ := h
  obtain ⟨_, ht, _⟩ := rds_took Reading.gl r hc e
  exact ht.2.1

/-- On a view the rounds between two contexts are fixed by the contexts. -/
theorem took_unique {c c' : Ctx} {rv rv' : List Fmt.RoundView} (h : Took c rv c') (h' : Took c rv' c') :
    rv = rv' := List.append_cancel_right (h.2.2.symm.trans h'.2.2)

/-- On a view the rounds that lie between c and c' have the sizes p. -/
theorem SzOn.view {c c' : Ctx} {p : List (ℕ × ℕ)} (h : SzOn c c' p) (hc : Clean c)
    {rv : List Fmt.RoundView} (ht : Took c rv c') :
    rv.map (fun r => ((sentOf r).length, (drawnOf r).length)) = p := by
  obtain ⟨l, e, r, s⟩ := h
  obtain ⟨rv', ht', hf⟩ := rds_took Reading.gl r hc e
  rw [took_unique ht ht', ← s, ← flEv_sz Reading.gl l, hf, List.map_map]
  refine List.map_congr_left fun x _ => ?_
  simp [rdRV]

/-- On a view every row of rounds from c to c' has the sizes p, under every reading. -/
theorem SzOn.any {K : Type} [CommRing K] (ρ : Reading K) {c c' : Ctx} {p : List (ℕ × ℕ)}
    (h : SzOn c c' p) (hc : Clean c) {l : List Ev} (hl : Rds l) (he : Evs l c c') :
    (flEv ρ l).map (fun r => (r.1.length, r.2.length)) = p := by
  obtain ⟨rv, ht, hf⟩ := rds_took ρ hl hc he
  rw [← h.view hc ht, hf, List.map_map]
  refine List.map_congr_left fun x _ => ?_
  simp [rdRV]

/-- A loop's sizes are its steps' sizes, one after the other. -/
theorem foldlM_sz {α σ : Type} (f : σ → α → SubM σ) (p : α → List (ℕ × ℕ))
    (hf : ∀ (s s' : σ) (a : α) (F G : Fork) (c c' : Ctx),
      f s a F c = .ok ((s', G), c') → Clean c → SzOn c c' (p a)) :
    ∀ (l : List α) (s s' : σ) (F G : Fork) (c c' : Ctx),
      (l.foldlM f s) F c = .ok ((s', G), c') → Clean c → SzOn c c' (l.flatMap p)
  | [], s, s', F, G, c, c', h, _ => by
    have e := (foldlM_nil_ok f s F c _).1 h
    have e3 : c' = c := congrArg (fun x : (σ × Fork) × Ctx => x.2) e
    rw [e3]
    exact SzOn.nil c
  | a :: l, s, s', F, G, c, c', h, hc => by
    obtain ⟨s₁, F₁, c₁, h1, h2⟩ := (foldlM_cons_ok f s a l F c _).1 h
    have z1 := hf s s₁ a F F₁ c c₁ h1 hc
    rw [List.flatMap_cons]
    exact z1.append (foldlM_sz f p hf l s₁ s' F₁ G c₁ c' h2 (z1.clean hc))

end Fo
