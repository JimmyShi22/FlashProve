-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/PlayTwo.lean: A TOOL ON THE FRAME's OWN `play`
(Honest/Frame.lean): what a part of TWO rounds whose stops never stop shows, played alone, as a
plain term in its two moves. Definitions; statements with their proofs. General: no kind is named.

  `colsAt`          the columns of a round's tables at the lists of positions that are asked of them
  `cols_some`       the frame's own look-up (`shownOf`, Honest/Side.lean) over tables that were all
                    sent is `colsAt`
  `play_two`        THE TOOL: two steps at one name and address, numbered 0 and 1, the second the
                    last, with such stops: what they show at two challenges and at lists of
                    positions: the first move says its message at the stand; if it has the round's
                    shape, the second says its own at the state that has heard the first challenge
                    and at what was shown with the first round behind it, the opened columns as they
                    were; if that has its round's shape: the two rounds' items and columns. One
                    symbol else

By: the frame's `stop_none` (Honest/Law/ToyPlay.lean): a step whose two stops are constant "none"
never stops. NEAR, NOT CALLED: the frame's own `play_two` (the same file; `ProofFile.Honest.play_two`:
ANOTHER LEMMA OF THIS NAME, in the frame's namespace): where both moves say a message of the stated
shape, what `play` returns, as an equation: here: what is SHOWN at lists of positions, with the arms
where a move refuses or a shape does not fit.

Limits. A tool on definitions. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.Side
import Johnson.Desc.ProofFile.Honest.Law.ToyPlay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Oracle)

variable {W X : Type}

/-- A round's tables' columns at the lists of positions that are asked of them. -/
def colsAt (T : List Table) (asks : List (List Nat)) : List (List (Nat × List UInt64)) :=
  T.zipIdx.map fun y => ((asks[y.2]?).getD []).map fun p => (p, y.1.col p)

theorem cols_some (asks : List (List Nat)) : ∀ (T : List Table) (n : Nat),
    ((T.map some).zipIdx n).map (fun y =>
        match y.1 with
        | some t => ((asks[y.2]?).getD []).map fun p => (p, t.col p)
        | none => []) =
      (T.zipIdx n).map fun y => ((asks[y.2]?).getD []).map fun p => (p, y.1.col p)
  | [], _ => rfl
  | t :: T, n => by
    simp only [List.map_cons, List.zipIdx_cons]
    rw [cols_some asks T (n + 1)]

/-- **The tool.** -/
theorem play_two (nm : String) (ad : Addr) (d₁ d₂ : Fmt.DeclaredRound) (o₁ o₂ : List Oracle)
    (bad hid : List Fmt.Drawn → List Fmt.Drawn → Option String) (hb : ∀ f o, bad f o = none)
    (hh : ∀ f o, hid f o = none) (mv₁ mv₂ : Move Unit W X) (x₁ x₂ : Fmt.Drawn) (m : Mid W X)
    (asks : List (List (List Nat))) :
    (play [⟨nm, ad, d₁, o₁, bad, hid, 0, false, some mv₁⟩,
        ⟨nm, ad, d₂, o₂, bad, hid, 1, true, some mv₂⟩] [x₁, x₂] [] m).toOption.map
        (fun y => shownOf y.1 asks) =
      (mv₁.say () ⟨m.seen, m.opened⟩ m.st).toOption.bind fun a₁ =>
        if a₁.fits d₁ o₁ then
          (mv₂.say () ⟨m.seen ++ [⟨a₁.vals.map Said.got, x₁⟩], m.opened⟩
            { m.st.hears x₁ with own := mv₁.hand (m.st.hears x₁) }).toOption.bind fun a₂ =>
            if a₂.fits d₂ o₂ then
              some [⟨a₁.vals.map Said.got, colsAt a₁.tables ((asks[0]?).getD [])⟩,
                ⟨a₂.vals.map Said.got, colsAt a₂.tables ((asks[1]?).getD [])⟩]
            else none
        else none := by
  have s₁ := stop_none (s := (⟨nm, ad, d₁, o₁, bad, hid, 0, false, some mv₁⟩ : Step W X)) hb hh
  have s₂ := stop_none (s := (⟨nm, ad, d₂, o₂, bad, hid, 1, true, some mv₂⟩ : Step W X)) hb hh
  cases h₁ : mv₁.say () ⟨m.seen, m.opened⟩ m.st with
  | error e => simp [play, Step.tell, Mid.shown, s₁, h₁, Except.bind, Except.toOption]
  | ok a₁ =>
    by_cases f₁ : a₁.fits d₁ o₁ = true
    · cases h₂ : mv₂.say () ⟨m.seen ++ [⟨a₁.vals.map Said.got, x₁⟩], m.opened⟩
          { m.st.hears x₁ with own := mv₁.hand (m.st.hears x₁) } with
      | error e =>
        simp [play, Step.tell, Mid.shown, Step.hear, s₁, s₂, h₁, h₂, f₁, Except.bind, Except.map,
          Except.toOption]
      | ok a₂ =>
        by_cases f₂ : a₂.fits d₂ o₂ = true
        · simp [play, Step.tell, Mid.shown, Step.hear, s₁, s₂, h₁, h₂, f₁, f₂, Except.bind,
            Except.map, Except.toOption, shownOf, colsAt]
          exact ⟨cols_some _ _ 0, cols_some _ _ 0⟩
        · simp [play, Step.tell, Mid.shown, Step.hear, s₁, s₂, h₁, h₂, f₁, f₂, Except.bind,
            Except.map, Except.toOption]
    · simp [play, Step.tell, Mid.shown, s₁, h₁, f₁, Except.bind, Except.toOption]

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.cols_some
#print axioms ProofFile.Honest.K2.Law.play_two
#print axioms ProofFile.Honest.K2.Law.colsAt
