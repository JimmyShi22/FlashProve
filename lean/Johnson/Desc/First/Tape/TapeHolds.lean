-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Tape/TapeHolds.lean: what the tape holds where the strict maker of one returns.
Statements, each a definition of its own name, with their proofs. No axiom beyond Lean's three usual
ones; no Mathlib.

Why. A kind that hears elements runs a flat function on a tape (`tapeT`, `flRun`,
Johnson/Desc/First/Tape/Tape.lean). A law on such a kind speaks of the view's rounds. TapeFits.lean
says for all views WHEN the maker returns. Here it is said WHAT it returns: the tape is a function
of the view's items and drawn elements and of the plan's entries, written out; nothing else of a
round is read.

Main names:
  `readT r e sent`: the one round that the maker can return at a view's round r with the entry e,
    where the round's items are the elements `sent`.
  `clausesT rule r e sent`: what the return vouches for: the maker's seven clauses.
  `Holds.Round`: where `roundT` returns, the items are elements, it returns `readT`, and the seven
    clauses hold.
  `Holds.Tape`: **where `tapeT` returns, there are as many rounds as entries and as members of
    the tape, member i is `readT` of round i and entry i, and the seven clauses hold there.**
  `Holds.One`: two views with the same items and the same drawn elements, positions and matrix
    entries, round by round, give the same tape.
  `Holds.NoDigest`: the sealed digest is not read.
  `Holds.Run`: `flRun` returns just where the maker returns a tape and the flat function returns on
    it and uses it up.
  `Holds.sillyYes`, `Holds.sillyNo`: two makers that must not meet `Holds.Tape` and `Fits.Tape`
    together: shown.

Limits: nothing is said of the flat function that runs on the tape, of soundness, or of hiding. That
an item's or a drawn element's three words are below the field's prime is not asked by the maker and
not said here: `E.ofTriple` is applied to the words as they stand in the view. `Holds.Tape` alone is
met by a maker that never returns: it is the half "what", to be read with TapeFits.lean's
`Fits.Tape`, the half "when": see `sillyNo`.

Uses of the library's plain functions, to be counted (none runs in a context): the records
`FlatRound`, `Tape` and the type `Fl` (OnBytes/K/Kc/Flat.lean); `Fork` (OnBytes/Model/Hide.lean), as
a letter alone; `Fmt.RoundView`, `Fmt.Entry`, `Fmt.ItemValue` (Fmt/); `E.ofTriple` (OnBytes/Field/).

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Tape.TapeFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Tape
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Fork)

/-- The round that the maker returns, if it returns. -/
def readT (r : Fmt.RoundView) (e : Fmt.Entry) (sent : List E) : FlatRound :=
  { name := some e.name, nz := e.drawNZ, rows := e.rows, sent := sent,
    drawn := r.drawn.elems.map E.ofTriple }

/-- What the maker's return vouches for: its seven clauses: those on the entry alone as `entryT`,
the seventh as `notZeroT` (TapeFits.lean). -/
def clausesT (rule : TapeRule) (r : Fmt.RoundView) (e : Fmt.Entry) (sent : List E) : Prop :=
  r.drawn.elems.length = e.drawE ∧ r.drawn.poss = [] ∧ r.drawn.trits = [] ∧
    e.msg = 24 * sent.length ∧ entryT rule e = true ∧ notZeroT r e = true

namespace Holds

/-- A round. -/
def Round : Prop := ∀ (rule : TapeRule) (r : Fmt.RoundView) (e : Fmt.Entry) (x : FlatRound),
  roundT rule r e = some x →
    ∃ sent, elemsOf r.vals = some sent ∧ x = readT r e sent ∧ clausesT rule r e sent

/-- **A stretch.** For a maker m of tapes. -/
def TapeOf (m : TapeRule → List Fmt.RoundView → List Fmt.Entry → Option K.Kc.Tape) : Prop :=
  ∀ (rule : TapeRule) (rs : List Fmt.RoundView) (es : List Fmt.Entry) (t : K.Kc.Tape),
    m rule rs es = some t →
      rs.length = es.length ∧ t.length = rs.length ∧
        ∀ (i : Nat) (r : Fmt.RoundView) (e : Fmt.Entry), rs[i]? = some r → es[i]? = some e →
          ∃ sent, elemsOf r.vals = some sent ∧ t[i]? = some (readT r e sent) ∧
            clausesT rule r e sent

def Tape : Prop := TapeOf tapeT

/-- What of a round is read. -/
def alike (r r' : Fmt.RoundView) : Prop :=
  r.vals = r'.vals ∧ r.drawn.elems = r'.drawn.elems ∧ r.drawn.poss = r'.drawn.poss ∧
    r.drawn.trits = r'.drawn.trits

/-- Round by round; as many. -/
def alikeAll : List Fmt.RoundView → List Fmt.RoundView → Prop
  | [], [] => True
  | r :: rs, r' :: rs' => alike r r' ∧ alikeAll rs rs'
  | _, _ => False

/-- The tape is a function of what is read. -/
def One : Prop := ∀ (rule : TapeRule) (rs rs' : List Fmt.RoundView) (es : List Fmt.Entry),
  alikeAll rs rs' → tapeT rule rs es = tapeT rule rs' es

/-- The sealed digest is not read. -/
def NoDigest : Prop := ∀ (rule : TapeRule) (rs : List Fmt.RoundView) (es : List Fmt.Entry),
  tapeT rule (rs.map noDigest) es = tapeT rule rs es

/-- A flat function on a stretch. -/
def Run : Prop := ∀ (α : Type) (rule : TapeRule) (f : Fl α) (es : List Fmt.Entry) (F : Fork)
  (rs : List Fmt.RoundView) (a : α) (G : Fork), flRun rule f es F rs = some (a, G) ↔
    ∃ t, tapeT rule rs es = some t ∧ f F t = some (a, G, [])

/-- "When", for a maker m: TapeFits.lean's `Fits.Tape` with the maker as a letter. -/
def WhenOf (m : TapeRule → List Fmt.RoundView → List Fmt.Entry → Option K.Kc.Tape) : Prop :=
  ∀ (rule : TapeRule) (es : List Fmt.Entry) (rs : List Fmt.RoundView), roundsFit (plain es) rs = true →
    (m rule rs es).isSome = (es.all (entryT rule) && (rs.zip es).all fun x => notZeroT x.1 x.2)

/-- A maker that returns the empty tape on everything. -/
def sillyYes : TapeRule → List Fmt.RoundView → List Fmt.Entry → Option K.Kc.Tape := fun _ _ _ => some []

/-- A maker that never returns. -/
def sillyNo : TapeRule → List Fmt.RoundView → List Fmt.Entry → Option K.Kc.Tape := fun _ _ _ => none

end Holds

theorem roundT_holds : Holds.Round := by
  intro rule r e x h
  cases hE : elemsOf r.vals with
  | none => simp [roundT, hE] at h
  | some sent =>
    refine ⟨sent, rfl, ?_⟩
    simp only [roundT, hE] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hc
      obtain ⟨⟨⟨⟨⟨⟨h1, h2, h2'⟩, h3, h3'⟩, h4⟩, h5⟩, ⟨⟨hm, hr⟩, ha⟩, hn⟩, h7⟩ := hc
      have hmod : e.msg % 24 = 0 := by omega
      refine ⟨(Option.some.inj h).symm, h1, h2, h3, hm, ?_, h7⟩
      simp only [entryT, Bool.and_eq_true, beq_iff_eq]
      exact ⟨⟨⟨⟨h2', h3'⟩, h4⟩, h5⟩, ⟨⟨hmod, hr⟩, ha⟩, hn⟩
    · exact absurd h (by simp)

theorem tapeT_holds : Holds.Tape := by
  intro rule rs
  induction rs with
  | nil =>
    intro es t h
    cases es with
    | nil =>
      have : t = [] := by simpa [tapeT] using h.symm
      subst this
      exact ⟨rfl, rfl, fun i r e hr _ => by simp at hr⟩
    | cons e es => simp [tapeT] at h
  | cons r rs ih =>
    intro es t h
    cases es with
    | nil => simp [tapeT] at h
    | cons e es =>
      simp only [tapeT] at h
      cases hx : roundT rule r e with
      | none => simp [hx] at h
      | some x =>
        cases ht : tapeT rule rs es with
        | none => simp [hx, ht] at h
        | some t' =>
          simp only [hx, ht, Option.some.injEq] at h
          subst h
          obtain ⟨h1, h2, h3⟩ := ih es t' ht
          refine ⟨by simp [h1], by simp [h2], ?_⟩
          intro i r0 e0 hr he
          cases i with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hr he
            subst hr
            subst he
            obtain ⟨sent, hs, hx', hc⟩ := roundT_holds rule r e x hx
            exact ⟨sent, hs, by simp [hx'], hc⟩
          | succ i =>
            simp only [List.getElem?_cons_succ] at hr he
            obtain ⟨sent, hs, hx', hc⟩ := h3 i r0 e0 hr he
            exact ⟨sent, hs, by simpa using hx', hc⟩

theorem roundT_alike (rule : TapeRule) (r r' : Fmt.RoundView) (e : Fmt.Entry) (h : Holds.alike r r') :
    roundT rule r e = roundT rule r' e := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [roundT, h1, h2, h3, h4]

theorem tapeT_one : Holds.One := by
  intro rule rs
  induction rs with
  | nil =>
    intro rs' es h
    cases rs' with
    | nil => rfl
    | cons _ _ => exact absurd h (by simp [Holds.alikeAll])
  | cons r rs ih =>
    intro rs' es h
    cases rs' with
    | nil => exact absurd h (by simp [Holds.alikeAll])
    | cons r' rs' =>
      have h' : Holds.alike r r' ∧ Holds.alikeAll rs rs' := h
      cases es with
      | nil => rfl
      | cons e es => simp only [tapeT, roundT_alike rule r r' e h'.1, ih rs' es h'.2]

theorem noDigest_alike (r : Fmt.RoundView) : Holds.alike (noDigest r) r := ⟨rfl, rfl, rfl, rfl⟩

theorem tapeT_noDigest : Holds.NoDigest := by
  intro rule rs es
  apply tapeT_one
  induction rs with
  | nil => exact True.intro
  | cons r rs ih => exact ⟨noDigest_alike r, ih⟩

theorem flRun_holds : Holds.Run := by
  intro α rule f es F rs a G
  constructor
  · intro h
    cases ht : tapeT rule rs es with
    | none => simp [flRun, ht] at h
    | some t =>
      refine ⟨t, rfl, ?_⟩
      simp only [flRun, ht] at h
      cases hf : f F t with
      | none => simp [hf] at h
      | some y =>
        obtain ⟨b, H, l⟩ := y
        cases l with
        | nil =>
          simp only [hf, Option.some.injEq, Prod.mk.injEq] at h
          rw [h.1, h.2]
        | cons _ _ => simp [hf] at h
  · rintro ⟨t, ht, hf⟩
    simp [flRun, ht, hf]

/-- The true maker meets both halves. -/
theorem tapeT_both : Holds.TapeOf tapeT ∧ Holds.WhenOf tapeT := ⟨tapeT_holds, tape⟩

/-- A round in which nothing is sent and one element is drawn. -/
def roundOne : Fmt.RoundView := ⟨[], ⟨[(0, 0, 0)], [], [], none⟩⟩

/-- An entry under which nothing is sent and nothing is drawn. -/
def entryNone : Fmt.Entry := { name := "" }

/-- THE SILLY MEMBER THAT SAYS YES TO ALL does not meet "what": at one round and one entry its tape
has no member. -/
theorem sillyYes_not : ¬ Holds.TapeOf Holds.sillyYes := by
  intro h
  have := (h {} [roundOne] [entryNone] [] rfl).2.1
  simp at this

/-- THE SILLY MEMBER THAT SAYS NO TO ALL meets "what", idly, and does not meet "when": at no round
and no entry the true test says yes. -/
theorem sillyNo_what : Holds.TapeOf Holds.sillyNo := by
  intro _ _ _ _ h
  exact absurd h (by simp [Holds.sillyNo])

theorem sillyNo_not : ¬ Holds.WhenOf Holds.sillyNo := by
  intro h
  have := h {} [] [] rfl
  simp [Holds.sillyNo] at this

end VerifiableInference.Desc.First.Tape
