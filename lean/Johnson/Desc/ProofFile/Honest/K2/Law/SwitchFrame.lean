-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/SwitchFrame.lean: the kind "the code switch" (K2): WHAT THE TWO
ROUNDS SHOW (`coreShows`, Honest/K2/Law/SwitchMoves.lean) IS ONE FUNCTION OF WHAT THE SENDING SHOWS
(`senderShows`, Honest/K2/Exact.lean). Definitions; statements with their proofs. A step toward the
statement in Honest/K2/Exact.lean: it says nothing on coins' laws.

  `zipIdx_fst`      a tool: a list's members numbered, mapped by a function that reads the member
                    alone: the list mapped
  `frameOf`         what the frame makes of what a sending shows, at two rounds: its test on the
                    first message's shape (no item but roots; the tables' stated lengths and widths)
                    and on the second's (answers alone, roots aside; no table); then the two rounds
                    as shown. It reads the rounds and what the sending shows: nothing else
  `coreShows_eq`    `coreShows` is: the two public tests on the sizes; the data, or the one symbol
                    where it is refused; `senderShows` at that data; `frameOf`

How. `coreShows_eq`: by cases on the two public tests, the data and the sender's two returns; its
last two steps are `simp` at the lemmas and definitions named there.

Limits. Nothing on what the sender lays. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.SwitchMoves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Oracle itemOf)
open VerifiableInference.Desc.K2.Honest (Sizes)

/-- A tool: numbering a list's members is lost on a function that reads the member alone. -/
theorem zipIdx_fst {α β : Type} (f : α → β) : ∀ (T : List α) (n : Nat),
    ((T.zipIdx n).map fun t => f t.1) = T.map f
  | [], _ => rfl
  | a :: T, n => by
    rw [List.zipIdx_cons, List.map_cons, List.map_cons, zipIdx_fst f T (n + 1)]

/-- **What the frame makes of what a sending shows.** -/
def frameOf (d₁ d₂ : Fmt.DeclaredRound) (o₁ o₂ : List Oracle)
    (y : List ((Nat × Nat) × List (Nat × List UInt64)) × List Cb.Gl.E) : Option (List Shown) :=
  if (([] : List Fmt.Item) == d₁.items.filter (· != .root) &&
      y.1.map (·.1) == o₁.map fun o => (o.logLength, o.words)) then
    if ((y.2.map Said.answer).map (fun v => itemOf v.got) == d₂.items.filter (· != .root) &&
        ([] : List (Nat × Nat)) == o₂.map fun o => (o.logLength, o.words)) then
      some [⟨[], y.1.map (·.2)⟩, ⟨(y.2.map Said.answer).map Said.got, []⟩]
    else none
  else none

/-- **What the two rounds show is `frameOf` of what the sending shows**, behind the two public tests
on the sizes; nothing where the data is refused. At every coin c of the sending. -/
theorem coreShows_eq (Sd : Sender) (Z : Sizes) (others : Array OnBytes.OracleNotice) (k : Nat)
    (d₁ d₂ : Fmt.DeclaredRound) (o₁ o₂ : List Oracle) (x₁ : Fmt.Drawn)
    (asks : List (List (List Nat))) (Dx : Except String (Nat → Nat → Nat → Cb.Gl.E))
    (c : Cs (sendingDue Z.codes (switchSent Z others) (switchFresh Z others k))) :
    coreShows Sd Z others k d₁ d₂ o₁ o₂ x₁ asks Dx c =
      if !Z.serves then none else
      if !Z.roomy then none else
      Dx.toOption.bind fun D =>
        (senderShows Sd Z.codes (switchSent Z others) (switchFresh Z others k) D x₁.elems
          ((asks[0]?).getD []) c).bind (frameOf d₁ d₂ o₁ o₂) := by
  unfold coreShows
  by_cases c₁ : (!Z.serves) = true
  · rw [if_pos c₁, if_pos c₁]
  rw [if_neg c₁, if_neg c₁]
  by_cases c₂ : (!Z.roomy) = true
  · rw [if_pos c₂, if_pos c₂]
  rw [if_neg c₂, if_neg c₂]
  cases Dx with
  | error e => rfl
  | ok D =>
    show ((Sd.tables Z.codes (switchSent Z others) (switchFresh Z others k) D c).toOption.bind _) =
      (senderShows Sd Z.codes (switchSent Z others) (switchFresh Z others k) D x₁.elems
        ((asks[0]?).getD []) c).bind (frameOf d₁ d₂ o₁ o₂)
    unfold senderShows
    cases hT : Sd.tables Z.codes (switchSent Z others) (switchFresh Z others k) D c with
    | error e => rfl
    | ok T =>
      cases hA : Sd.answers Z.codes (switchSent Z others) (switchFresh Z others k) D c
          x₁.elems with
      | error e =>
        simp [Except.toOption]
      | ok A =>
        have hz : List.map (fun x : Table × Nat => (x.1.logLength, x.1.words)) T.zipIdx =
            List.map (fun t : Table => (t.logLength, t.words)) T :=
          zipIdx_fst (fun t : Table => (t.logLength, t.words)) T 0
        simp [Except.toOption, frameOf, Sending.fits, colsAt, hz, List.map_map,
          Function.comp_def]

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.zipIdx_fst
#print axioms ProofFile.Honest.K2.Law.frameOf
#print axioms ProofFile.Honest.K2.Law.coreShows_eq
