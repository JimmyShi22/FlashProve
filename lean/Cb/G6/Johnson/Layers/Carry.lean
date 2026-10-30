-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/G6/Johnson/Layers/Carry.lean: a rule for `Doomed` (Iop/Rbr.lean): a protocol whose messages can
be carried, round by round, to those of a doomed protocol is doomed, with the same numbers.

Definitions, one statement and its proof. No protocol occurs here.
Why: in the Lean model of the C++ verifier (OnBytes/Model/Psc.lean: `pscRound`;
OnBytes/Iop/Psc.lean: `Weight.complete`) a round of the masked sumcheck leaves out one coefficient
of its polynomial, which the running claim fixes. The library's block (Cb/Ld/LdPsc.lean) has all
coefficients sent. A prover of such short rounds is a prover of the library's rounds that completes
each polynomial from what went before.

Main names:
  `Carry s s'`: the messages of a shape s are carried, round by round and knowing all that went
    before in s, to messages of a shape s', and the draws of s to draws of s'.
  `Carry.tr`: the transcript of s' that a transcript of s is carried to.
  `Carry.Inj`: each round's map of draws is injective.
  `errTo`: the errors of s' read as errors of s, round for round.
  `Doomed.carry`: if s' is doomed towards bad', the maps of draws are injective, and bad' of the
    carried transcript gives bad, then s is doomed towards bad, with the same numbers.

Limits: nothing is assumed. Three limits of the rule. (a) "The same numbers" are counts of draws.
Where a map of draws is not onto (E without 0 into E) the same count stands over a smaller set of
draws: as a chance it is larger. The denominators are those of s. (b) The rule neither merges nor
splits rounds. Where scalars ride with the next message, or one side has a round with an empty draw,
the two shapes must first be made of one length (idle rounds; a message that is a pair, of which the
map takes a part). (c) A round's map of draws may not depend on that round's own message. It may
depend on all rounds before. The file does not say that a carrying exists between two given shapes:
between shapes of different lengths the type `Carry` is empty. Nothing on zero knowledge; "masked"
is a name.

-/
import Iop.Rbr

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.L5.Layers
open Iop Prob

/-- A count along an injection. -/
theorem cnt_le_of_inj {α β : Type} [Finite α] [Finite β] {P : α → Prop} {Q : β → Prop} (f : α → β)
    (hf : Function.Injective f) (h : ∀ a, P a → Q (f a)) : cnt P ≤ cnt Q :=
  Nat.card_le_card_of_injective (fun x : {a // P a} => (⟨f x.1, h x.1 x.2⟩ : {b // Q b}))
    (fun _ _ e => Subtype.ext (hf (congrArg (fun z : {b // Q b} => z.1) e)))

/-- Messages and draws of s carried to those of s', each round knowing the rounds before it. -/
def Carry : Shape → Shape → Type
  | [], [] => Unit
  | [], _ :: _ => Empty
  | _ :: _, [] => Empty
  | r :: s, r' :: s' => (r.Msg → r'.Msg) × (r.Chal → r'.Chal) × (r.Msg → r.Chal → Carry s s')

/-- The carried transcript. -/
def Carry.tr : {s s' : Shape} → Carry s s' → Tr s → Tr s'
  | [], [], _, _ => ()
  | [], _ :: _, K, _ => K.elim
  | _ :: _, [], K, _ => K.elim
  | _ :: _, _ :: _, (g, e, k), (m, c, τ) => (g m, e c, Carry.tr (k m c) τ)

/-- Every map of draws is injective. -/
def Carry.Inj : {s s' : Shape} → Carry s s' → Prop
  | [], [], _ => True
  | [], _ :: _, K => K.elim
  | _ :: _, [], K => K.elim
  | _ :: _, _ :: _, (_, e, k) => Function.Injective e ∧ ∀ m c, Carry.Inj (k m c)

/-- The errors of s', round for round, as errors of s. -/
def errTo : (s s' : Shape) → Err s' → Err s
  | [], _, _ => ()
  | _ :: s, [], _ => (0, errTo s [] ())
  | _ :: s, _ :: s', (e, ε) => (e, errTo s s' ε)

/-- The rule. -/
theorem Doomed.carry : ∀ {s s' : Shape} (K : Carry s s') (ε' : Err s') (bad : Tr s → Prop)
    (bad' : Tr s' → Prop), K.Inj → (∀ τ, bad' (K.tr τ) → bad τ) → Doomed s' ε' bad' →
    Doomed s (errTo s s' ε') bad
  | [], [], _, _, _, _, _, h, hd => h () hd
  | [], _ :: _, K, _, _, _, _, _, _ => K.elim
  | _ :: _, [], K, _, _, _, _, _, _ => K.elim
  | _ :: _, _ :: _, (g, e, k), (_, ε'), bad, bad', hI, h, hd => fun m =>
      le_trans
        (cnt_le_of_inj e hI.1 fun c hc hd' =>
          hc (Doomed.carry (k m c) ε' (fun τ => bad (m, c, τ)) (fun τ' => bad' (g m, e c, τ'))
            (hI.2 m c) (fun τ hτ => h (m, c, τ) hτ) hd'))
        (hd (g m))

end Johnson.L5.Layers
