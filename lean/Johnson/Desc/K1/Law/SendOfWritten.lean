-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/SendOfWritten.lean: K01_law, J1: THE STRETCH OF THE FILE's DATA AT A BLOCK THAT DECLARES A SENDING's TWO ROUNDS IS [d₁, d₂] WITH d₁.entry = seedEntry P AND d₁.kind = .seeds: from the framework's own WrittenAs, by the kind-free
stretch_tags (Johnson/Desc/Sound/StretchTags.lean). The twin, for a sending, of Johnson/Desc/K13/Law/DeclaredOfWritten.lean, lemma for lemma. No number of a plan is named.
  send_of_tags · send_of_written
Nothing on soundness.
-/
import Johnson.Desc.Sound.StretchTags
import Johnson.Desc.K1.Law.GoodSend4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Maker OnBytes.Flat
open OnBytes.Params (Rounds)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K13.Law (tagR tagD stretch_tags)
open _root_.Desc.K14.Law (roundsIn)

theorem kind_seed (P : Par) : Fmt.kindOf (seedEntry P).name = some .seeds := by
  show Fmt.kindOf "SEND seed" = some .seeds
  decide

/-- **From the tags of a sending's declared rounds.** -/
theorem send_of_tags (P : Par) (L : List RDT) (h : L.map tagR = (rounds P).map tagD) :
    ∃ d₁ d₂, L = [d₁, d₂] ∧ d₁.entry = seedEntry P ∧ d₁.kind = .seeds := by
  unfold rounds at h
  match L, h with
  | [], h => simp at h
  | [_], h => simp at h
  | [d₁, d₂], h =>
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
    obtain ⟨h1, _⟩ := h
    have e1 : d₁.entry = seedEntry P := congrArg Prod.fst h1
    have e2 : some d₁.kind = Fmt.kindOf (seedEntry P).name := congrArg Prod.snd h1
    rw [kind_seed] at e2
    exact ⟨d₁, d₂, rfl, e1, Option.some.inj e2⟩
  | _ :: _ :: _ :: _, h => simp at h

/-- **The stretch at a block with a sending's declared rounds.** -/
theorem send_of_written {T Cl : Type} (a : ℕ) (R₁ R₂ R₃ : Rounds)
    {e : List (List ByteArray × ByteArray)} (bs : List (Block T Cl))
    (hW : WrittenAs e (bs.flatMap (·.rounds)) R₁) (k : ℕ) (x : Block T Cl) (hx : bs[k]? = some x)
    (hroom : roundsIn (bs.take k) + x.rounds.length < roundsIn bs) (P : Par)
    (hr : x.rounds = rounds P) :
    ∃ d₁ d₂, ((dataOf a R₁ R₂ R₃).ds₁.drop (roundsIn (bs.take k))).take x.rounds.length =
      [d₁, d₂] ∧ d₁.entry = seedEntry P ∧ d₁.kind = .seeds :=
  send_of_tags P _ (by rw [stretch_tags a R₁ R₂ R₃ bs hW k x hx hroom, hr])

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.send_of_tags
#print axioms VerifiableInference.Desc.K1.send_of_written
