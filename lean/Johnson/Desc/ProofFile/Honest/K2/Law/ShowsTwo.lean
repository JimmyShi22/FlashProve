-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/ShowsTwo.lean: A TOOL ON THE FRAME's OWN `Part.steps` AND
`play` (Honest/Frame.lean): what a part of just two moves whose stops never stop shows, played alone
at two rounds, as a plain term in its two moves. Statements with their proofs. General: no kind is
named.

  `steps_two`       the steps of a part of two moves at two rounds, written out
  `shows_two`       what such a part shows at two challenges (`play_two`,
                    Honest/K2/Law/PlayTwo.lean, at these steps)

Limits. A tool on definitions. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.PlayTwo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Oracle)

variable {V W X : Type}

theorem steps_two (p : Part V W X) {mv₁ mv₂ : Move (Handed p.takes p.spends p.carries) W X}
    (hm : p.moves = [mv₁, mv₂]) (nm : String) (ad : Addr) (d₁ d₂ : Fmt.DeclaredRound)
    (o₁ o₂ : List Oracle) (v : Option V) (c : p.Coins) :
    p.steps nm ad [(d₁, o₁), (d₂, o₂)] v c =
      [⟨nm, ad, d₁, o₁, p.bad, fun f o => v.bind fun w => p.hid w f o, 0, false,
          some ⟨fun _ => mv₁.say c, mv₁.hand⟩⟩,
        ⟨nm, ad, d₂, o₂, p.bad, fun f o => v.bind fun w => p.hid w f o, 1, true,
          some ⟨fun _ => mv₂.say c, mv₂.hand⟩⟩] := by
  unfold Part.steps
  rw [hm]
  rfl

theorem shows_two (p : Part V W X) {mv₁ mv₂ : Move (Handed p.takes p.spends p.carries) W X}
    (hm : p.moves = [mv₁, mv₂]) (hb : ∀ f o, p.bad f o = none) (hh : ∀ w f o, p.hid w f o = none)
    (nm : String) (ad : Addr) (d₁ d₂ : Fmt.DeclaredRound) (o₁ o₂ : List Oracle) (v : Option V)
    (c : p.Coins) (x₁ x₂ : Fmt.Drawn) (m : Mid W X) (asks : List (List (List Nat))) :
    (play (p.steps nm ad [(d₁, o₁), (d₂, o₂)] v c) [x₁, x₂] [] m).toOption.map
        (fun y => shownOf y.1 asks) =
      (mv₁.say c ⟨m.seen, m.opened⟩ m.st).toOption.bind fun a₁ =>
        if a₁.fits d₁ o₁ then
          (mv₂.say c ⟨m.seen ++ [⟨a₁.vals.map Said.got, x₁⟩], m.opened⟩
            { m.st.hears x₁ with own := mv₁.hand (m.st.hears x₁) }).toOption.bind fun a₂ =>
            if a₂.fits d₂ o₂ then
              some [⟨a₁.vals.map Said.got, colsAt a₁.tables ((asks[0]?).getD [])⟩,
                ⟨a₂.vals.map Said.got, colsAt a₂.tables ((asks[1]?).getD [])⟩]
            else none
        else none := by
  rw [steps_two p hm]
  exact play_two nm ad d₁ d₂ o₁ o₂ p.bad _ hb
    (fun f o => by
      cases v with
      | none => rfl
      | some w => exact hh w f o)
    ⟨fun _ => mv₁.say c, mv₁.hand⟩ ⟨fun _ => mv₂.say c, mv₂.hand⟩ x₁ x₂ m asks

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.steps_two
#print axioms ProofFile.Honest.K2.Law.shows_two
