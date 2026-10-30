-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/SwitchMoves.lean: the kind "the code switch" (K2): THE PART's
TWO MOVES BY NAME, AND WHAT THEY SHOW TOGETHER AS ONE TERM IN THE SENDER's TABLES AND ANSWERS AT ONE
DATA. Definitions; statements with their proofs. A step toward the statement in
Honest/K2/Exact.lean: it says nothing on coins' laws.

  `SwitchCoins`     what the part is handed of coins
  `moveOne`, `moveTwo`   the two moves of `switchPart` (Honest/K2/Part.lean), that text again;
                    `switchPart_moves`: they are its moves
  `coreShows`       what the two rounds show, of the main rows' data (or a refusal in its stead),
                    the first challenge, the positions and the sending's coins: the two public
                    tests on the sizes; the tables; the frame's test on the first message's shape;
                    the answers; its test on the second's; the columns and the answers. One symbol
                    else
  `says_core`       the two moves, the second at a state with the first's input that has heard one
                    challenge more, show `coreShows` at the first move's data

Limits. Nothing on what the sender lays. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.ShowsTwo
import Johnson.Desc.ProofFile.Honest.K2.Exact

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Oracle)
open VerifiableInference.Desc.K2.Honest (Sizes)

/-- What the part is handed of coins. -/
abbrev SwitchCoins (Z : Sizes) (others : Array OnBytes.OracleNotice) (k : Nat)
    (carries : List (String × Due)) : Type :=
  Handed (sendingDue Z.codes (switchSent Z others) (switchFresh Z others k)) [] carries

/-- The part's first move. -/
def moveOne (Sd : Sender) (Z : Sizes) (others : Array OnBytes.OracleNotice) (k : Nat)
    (carries : List (String × Due)) : Move (SwitchCoins Z others k carries) SwitchAsk Unit :=
  ⟨fun c _ t =>
      if !Z.serves then .error "the switch's rest does not lie in main rows" else
      if !Z.roomy then .error "the sizes do not fit a switch" else
      (switchRowsAt Z carries c.2.2 t 0).bind fun D =>
      (Sd.tables Z.codes (switchSent Z others) (switchFresh Z others k) D c.1).map fun T =>
        ⟨[], T⟩,
    fun t => t.own⟩

/-- Its second. -/
def moveTwo (Sd : Sender) (Z : Sizes) (others : Array OnBytes.OracleNotice) (k : Nat)
    (carries : List (String × Due)) : Move (SwitchCoins Z others k carries) SwitchAsk Unit :=
  ⟨fun c _ t =>
      (switchRowsAt Z carries c.2.2 t 1).bind fun D =>
      (Sd.answers Z.codes (switchSent Z others) (switchFresh Z others k) D c.1
        ((t.lately 1).flatMap (·.elems))).map fun A => ⟨A.map .answer, []⟩,
    fun t => t.own⟩

theorem switchPart_moves (Sd : Sender) (Z : Sizes) (others : Array OnBytes.OracleNotice) (k : Nat)
    (carries : List (String × Due)) :
    (switchPart Sd Z others k carries).moves =
      [moveOne Sd Z others k carries, moveTwo Sd Z others k carries] := rfl

/-- **What the two rounds show**, of one data. -/
def coreShows (Sd : Sender) (Z : Sizes) (others : Array OnBytes.OracleNotice) (k : Nat)
    (d₁ d₂ : Fmt.DeclaredRound) (o₁ o₂ : List Oracle) (x₁ : Fmt.Drawn)
    (asks : List (List (List Nat))) (Dx : Except String (Nat → Nat → Nat → Cb.Gl.E))
    (c : Cs (sendingDue Z.codes (switchSent Z others) (switchFresh Z others k))) :
    Option (List Shown) :=
  if !Z.serves then none else
  if !Z.roomy then none else
  Dx.toOption.bind fun D =>
  (Sd.tables Z.codes (switchSent Z others) (switchFresh Z others k) D c).toOption.bind fun T =>
    if (⟨[], T⟩ : Sending).fits d₁ o₁ then
      (Sd.answers Z.codes (switchSent Z others) (switchFresh Z others k) D c
        x₁.elems).toOption.bind fun A =>
        if (⟨A.map .answer, []⟩ : Sending).fits d₂ o₂ then
          some [⟨[], colsAt T ((asks[0]?).getD [])⟩,
            ⟨(A.map Said.answer).map Said.got, colsAt [] ((asks[1]?).getD [])⟩]
        else none
    else none

theorem says_core (Sd : Sender) (Z : Sizes) (others : Array OnBytes.OracleNotice) (k : Nat)
    (carries : List (String × Due)) (d₁ d₂ : Fmt.DeclaredRound) (o₁ o₂ : List Oracle)
    (x₁ : Fmt.Drawn) (asks : List (List (List Nat)))
    (c : Cs (sendingDue Z.codes (switchSent Z others) (switchFresh Z others k)))
    (ca : CsAll carries) (s : Seen) (s' : Sending → Seen) (t t' : State SwitchAsk Unit)
    (hi : t'.input = t.input) (hh : t'.heard = t.heard ++ [x₁]) :
    (((moveOne Sd Z others k carries).say (c, (), ca) s t).toOption.bind fun a₁ =>
        if a₁.fits d₁ o₁ then
          ((moveTwo Sd Z others k carries).say (c, (), ca) (s' a₁) t').toOption.bind fun a₂ =>
            if a₂.fits d₂ o₂ then
              some [⟨a₁.vals.map Said.got, colsAt a₁.tables ((asks[0]?).getD [])⟩,
                ⟨a₂.vals.map Said.got, colsAt a₂.tables ((asks[1]?).getD [])⟩]
            else none
        else none) =
      coreShows Sd Z others k d₁ d₂ o₁ o₂ x₁ asks (switchRowsAt Z carries ca t 0) c := by
  have h₂ : switchRowsAt Z carries ca t' 1 = switchRowsAt Z carries ca t 0 :=
    switchRowsAt_again Z carries ca t t' x₁ hi hh
  have h₃ : (t'.lately 1).flatMap (·.elems) = x₁.elems := by
    unfold State.lately
    rw [hh]
    simp
  unfold coreShows moveOne moveTwo
  dsimp only
  rw [h₂, h₃]
  by_cases c₁ : (!Z.serves) = true
  · simp [c₁, Except.toOption]
  · by_cases c₂ : (!Z.roomy) = true
    · simp [c₁, c₂, Except.toOption]
    · cases hD : switchRowsAt Z carries ca t 0 with
      | error e => simp [c₁, c₂, Except.toOption, Except.bind]
      | ok D =>
        cases hT : Sd.tables Z.codes (switchSent Z others) (switchFresh Z others k) D c with
        | error e => simp [c₁, c₂, hT, Except.toOption, Except.bind, Except.map]
        | ok T =>
          cases hA : Sd.answers Z.codes (switchSent Z others) (switchFresh Z others k) D c
              x₁.elems with
          | error e => simp [c₁, c₂, hT, hA, Except.toOption, Except.bind, Except.map]
          | ok A => simp [c₁, c₂, hT, hA, Except.toOption, Except.bind, Except.map]

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.switchPart_moves
#print axioms ProofFile.Honest.K2.Law.says_core
#print axioms ProofFile.Honest.K2.Law.SwitchCoins
#print axioms ProofFile.Honest.K2.Law.moveOne
#print axioms ProofFile.Honest.K2.Law.moveTwo
#print axioms ProofFile.Honest.K2.Law.coreShows
