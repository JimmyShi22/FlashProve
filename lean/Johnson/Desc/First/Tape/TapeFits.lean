-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Tape/TapeFits.lean: what is left of the strict maker of a tape behind the test
that every block's step asks first. Statements, each a definition of its own name, with their
proofs. No axiom beyond Lean's three usual ones; no Mathlib.

Why. `Block.step` (Johnson/Desc/Block.lean) asks `roundsFit` of a block's declared rounds and the
view's rounds before the block's own `decide` is called: each round shows just the items that its
entry cuts, and drew as many elements, positions and matrix entries as its entry says. The maker of
a tape (`roundT`, `tapeT`, Johnson/Desc/First/Tape/Tape.lean) asks some of that once more. Here it
is shown, for all views, which of its clauses follow: so a kind that is called through `Block.step`
may say of such a clause "also asked by roundsFit" by a lemma and not by a run.

Main names:
  `roundFit e r`: one round's share of `roundsFit`, at a declared round that opens nothing.
  `entryT rule e`: **the test on the entry alone** that is left of `roundT`: no view is read.
  `notZeroT r e`: `roundT`'s seventh clause: the one clause that is left on the view.
  `Fits.Clause1`, `Clause2`, `Clause3`, `Elems`, `Lengths`: a statement a clause.
  `Fits.Round`, `Fits.Tape`: **behind the fit, the maker returns just where `entryT` holds of
    the entries and `notZeroT` of the rounds.**
  `Fits.NoDigest`, `Fits.Step`: the premise is met by what `decide` is handed.

Limits: the declared rounds are `{ entry := e }`: they open no stored part and no tree. `roundsFit`
and `itemOf` are Block.lean's. Beside what is told under "Why", `roundsFit`
asks three things more of a round (every drawn position is below 2 ^ logN; every drawn matrix entry
is -1, 0 or 1; `drawsMarkedNonzeroHaveNonzeroWords`: the drawn elements that the entry marks as never 0 are not 0, by the
format's own list): `roundFit` has them; behind the maker's clauses 2 and 3 the first two are idle:
a round of a tape draws neither; that `drawsMarkedNonzeroHaveNonzeroWords` gives the maker's seventh clause is not shown here.
The statements say when the maker RETURNS, not what the tape holds. Nothing is said of the flat
function that runs on the tape, of soundness, or of hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Block
import Johnson.Desc.First.Tape.Tape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Tape
open OnBytes OnBytes.K.Kc

/-- One round's share of `roundsFit`, at the declared round `{ entry := e }`. -/
def roundFit (e : Fmt.Entry) (r : Fmt.RoundView) : Bool :=
  r.vals.map itemOf == e.cut.filter (· != .root) && r.drawn.elems.length == e.drawE &&
    r.drawn.poss.length == e.poss && r.drawn.trits.length == e.trits &&
    r.drawn.poss.all (· < 2 ^ e.logN) &&
    r.drawn.trits.all (fun t => t == -1 || t == 0 || t == 1) &&
    drawsMarkedNonzeroHaveNonzeroWords { entry := e } r

/-- The entries as declared rounds that open nothing. -/
def plain (es : List Fmt.Entry) : List Fmt.DeclaredRound := es.map fun e => { entry := e }

/-- **The test on the entry alone**: what is left of `roundT`'s clauses 2 to 6 behind the fit. -/
def entryT (rule : TapeRule) (e : Fmt.Entry) : Bool :=
  e.poss == 0 && e.trits == 0 &&
    ((e.rows == 0 && e.name != Model.RoundName.batSigma.name) || rule.rows e) &&
    Params.kindOf e.name == some (rule.kind e.name) &&
    (e.msg % 24 == 0 && e.roots == 0 && e.answers == 0 && e.count == 1)

/-- `roundT`'s seventh clause. -/
def notZeroT (r : Fmt.RoundView) (e : Fmt.Entry) : Bool :=
  (r.drawn.elems.drop (e.drawE - e.drawNZ)).all fun x => !isZeroE (E.ofTriple x)

namespace Fits

/-! ## The statements -/

/-- Clause 1 (as many elements are drawn as the entry says) follows. -/
def Clause1 : Prop := ∀ (e : Fmt.Entry) (r : Fmt.RoundView), roundFit e r = true →
  (r.drawn.elems.length == e.drawE) = true

/-- Clause 2: its half on the view (no position is drawn) is its half on the entry. -/
def Clause2 : Prop := ∀ (e : Fmt.Entry) (r : Fmt.RoundView), roundFit e r = true →
  r.drawn.poss.isEmpty = (e.poss == 0)

/-- Clause 3: its half on the view (no matrix entry is drawn) is its half on the entry. -/
def Clause3 : Prop := ∀ (e : Fmt.Entry) (r : Fmt.RoundView), roundFit e r = true →
  r.drawn.trits.isEmpty = (e.trits == 0)

/-- `elemsOf`'s third arm, and the count in clause 6: where the entry has no root and no answer,
every item is an element, and there are msg / 24 of them. -/
def Elems : Prop := ∀ (e : Fmt.Entry) (r : Fmt.RoundView), roundFit e r = true →
  e.roots = 0 → e.answers = 0 → ∃ sent, elemsOf r.vals = some sent ∧ sent.length = e.msg / 24

/-- `tapeT`'s last arm (as many rounds as entries) follows. -/
def Lengths : Prop := ∀ (ds : List Fmt.DeclaredRound) (rs : List Fmt.RoundView), roundsFit ds rs = true →
  ds.length = rs.length

/-- **A round.** Behind the fit `roundT` returns just where the test on the entry alone and the
seventh clause hold. -/
def Round : Prop := ∀ (rule : TapeRule) (e : Fmt.Entry) (r : Fmt.RoundView), roundFit e r = true →
  (roundT rule r e).isSome = (entryT rule e && notZeroT r e)

/-- **A stretch.** Behind `roundsFit` the maker of the tape returns just where the test on the entry
alone holds of every entry and the seventh clause of every round with its entry. -/
def Tape : Prop := ∀ (rule : TapeRule) (es : List Fmt.Entry) (rs : List Fmt.RoundView),
  roundsFit (plain es) rs = true →
  (tapeT rule rs es).isSome =
    (es.all (entryT rule) && (rs.zip es).all fun x => notZeroT x.1 x.2)

/-- The fit does not read the sealed digest, which `Block.step` strikes before `decide`. -/
def NoDigest : Prop := ∀ (ds : List Fmt.DeclaredRound) (rs : List Fmt.RoundView),
  roundsFit ds (rs.map noDigest) = roundsFit ds rs

/-- Where a block's step returns, the rounds that its `decide` was handed fit its declared
rounds. -/
def Step : Prop := ∀ (S Cl : Type) (b : Block S Cl) (firstTree : Nat) (s : S) (rs : List Fmt.RoundView)
  (cols : List OpenedColumn) (x : S × Nat), b.step firstTree s rs cols = .ok x →
  roundsFit b.rounds (rs.map noDigest) = true

end Fits

/-! ## The proofs -/

theorem roundFit_parts {e : Fmt.Entry} {r : Fmt.RoundView} (h : roundFit e r = true) :
    r.vals.map itemOf = e.cut.filter (· != .root) ∧ r.drawn.elems.length = e.drawE ∧
      r.drawn.poss.length = e.poss ∧ r.drawn.trits.length = e.trits := by
  simp only [roundFit, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2⟩

theorem roundsFit_cons (e : Fmt.Entry) (ds : List Fmt.DeclaredRound) (r : Fmt.RoundView) (rs : List Fmt.RoundView) :
    roundsFit ({ entry := e } :: ds) (r :: rs) = (roundFit e r && roundsFit ds rs) := rfl

theorem clause1 : Fits.Clause1 := fun _ _ h => by
  simp [(roundFit_parts h).2.1]

theorem isEmpty_eq {α : Type} (l : List α) (n : Nat) (h : l.length = n) :
    l.isEmpty = (n == 0) := by
  subst h
  cases l <;> simp

theorem clause2 : Fits.Clause2 := fun _ _ h => isEmpty_eq _ _ (roundFit_parts h).2.2.1

theorem clause3 : Fits.Clause3 := fun _ _ h => isEmpty_eq _ _ (roundFit_parts h).2.2.2

theorem filter_elems (n : Nat) :
    (List.replicate n Fmt.Item.e).filter (· != Fmt.Item.root) = List.replicate n Fmt.Item.e := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, List.filter_cons, ih]

theorem cut_elems (e : Fmt.Entry) (hr : e.roots = 0) (ha : e.answers = 0) :
    e.cut.filter (· != Fmt.Item.root) = List.replicate (e.msg / 24) Fmt.Item.e := by
  have : e.cut = List.replicate (e.msg / 24) Fmt.Item.e := by
    simp [Fmt.Entry.cut, hr, ha]
  rw [this, filter_elems]

theorem elemsOf_elems : ∀ (l : List Fmt.ItemValue) (n : Nat),
    l.map itemOf = List.replicate n Fmt.Item.e → ∃ s, elemsOf l = some s ∧ s.length = n
  | [], 0, _ => ⟨[], rfl, rfl⟩
  | [], _ + 1, h => by simp [List.replicate_succ] at h
  | _ :: _, 0, h => by simp at h
  | g :: l, n + 1, h => by
    simp only [List.map_cons, List.replicate_succ, List.cons.injEq] at h
    obtain ⟨s, hs, hn⟩ := elemsOf_elems l n h.2
    cases g with
    | e x => exact ⟨E.ofTriple x :: s, by simp [elemsOf, hs], by simp [hn]⟩
    | f x => exact absurd h.1 (by simp [itemOf])
    | word x => exact absurd h.1 (by simp [itemOf])
    | root d => exact absurd h.1 (by simp [itemOf])
    | answer x => exact absurd h.1 (by simp [itemOf])

theorem elems : Fits.Elems := fun e r h hr ha =>
  elemsOf_elems r.vals (e.msg / 24) ((roundFit_parts h).1.trans (cut_elems e hr ha))

theorem lengths : Fits.Lengths := by
  intro ds
  induction ds with
  | nil =>
    intro rs h
    cases rs with
    | nil => rfl
    | cons r rs => simp [roundsFit] at h
  | cons d ds ih =>
    intro rs h
    cases rs with
    | nil => simp [roundsFit] at h
    | cons r rs =>
      simp only [roundsFit, Bool.and_eq_true] at h
      simp [ih rs h.2]

theorem msg_eq (m : Nat) : (m == 24 * (m / 24)) = (m % 24 == 0) := by
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq]
  omega

theorem isSome_ite {α : Type} (c : Bool) (a : α) :
    (if c = true then some a else none).isSome = c := by
  cases c <;> rfl

theorem round : Fits.Round := by
  intro rule e r h
  by_cases h0 : e.roots = 0 ∧ e.answers = 0
  · obtain ⟨s, hs, hn⟩ := elems e r h h0.1 h0.2
    have h1 := clause1 e r h
    have h2 := clause2 e r h
    have h3 := clause3 e r h
    simp only [roundT, hs, isSome_ite, h1, h2, h3, hn, msg_eq, entryT, notZeroT, Bool.and_self,
      Bool.true_and, Bool.and_assoc]
  · have hz : (e.roots == 0 && e.answers == 0) = false := by
      rw [Bool.eq_false_iff]
      intro hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact h0 hc
    have hR : entryT rule e = false := by
      simp only [entryT, Bool.and_assoc]
      rw [← Bool.and_assoc (e.roots == 0), hz]
      simp
    rw [hR, Bool.false_and]
    cases hE : elemsOf r.vals with
    | none => simp [roundT, hE]
    | some s =>
      simp only [roundT, hE, isSome_ite, Bool.and_assoc]
      rw [← Bool.and_assoc (e.roots == 0), hz]
      simp

theorem tapeT_cons (rule : TapeRule) (r : Fmt.RoundView) (rs : List Fmt.RoundView) (e : Fmt.Entry)
    (es : List Fmt.Entry) : (tapeT rule (r :: rs) (e :: es)).isSome =
      ((roundT rule r e).isSome && (tapeT rule rs es).isSome) := by
  simp only [tapeT]
  cases roundT rule r e <;> cases tapeT rule rs es <;> rfl

theorem tape : Fits.Tape := by
  intro rule es
  induction es with
  | nil =>
    intro rs h
    cases rs with
    | nil => simp [tapeT]
    | cons r rs => simp [plain, roundsFit] at h
  | cons e es ih =>
    intro rs h
    cases rs with
    | nil => simp [plain, roundsFit] at h
    | cons r rs =>
      have h' : (roundFit e r && roundsFit (plain es) rs) = true := h
      rw [Bool.and_eq_true] at h'
      rw [tapeT_cons, round rule e r h'.1, ih rs h'.2]
      simp only [List.all_cons, List.zip_cons_cons]
      generalize entryT rule e = a
      generalize notZeroT r e = n
      generalize es.all (entryT rule) = A
      generalize ((rs.zip es).all fun x => notZeroT x.1 x.2) = N
      cases a <;> cases n <;> cases A <;> cases N <;> rfl

theorem noDigest_fit : Fits.NoDigest := by
  intro ds
  induction ds with
  | nil =>
    intro rs
    cases rs <;> rfl
  | cons d ds ih =>
    intro rs
    cases rs with
    | nil => rfl
    | cons r rs => simp only [List.map_cons, roundsFit, drawsMarkedNonzeroHaveNonzeroWords, noDigest, ih rs]

theorem step : Fits.Step := by
  intro S Cl b firstTree s rs cols x h
  rw [noDigest_fit]
  cases hf : roundsFit b.rounds rs with
  | true => rfl
  | false => simp [Block.step, need, hf, bind, Except.bind] at h

end VerifiableInference.Desc.First.Tape
