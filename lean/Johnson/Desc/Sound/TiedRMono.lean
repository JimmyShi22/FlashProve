-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
lean/Johnson/Desc/Sound/TiedRMono.lean: THE SECOND FORM OF THE CHAIN OF PROMISES IS ANTITONE IN THE
    CONDITION Rch: in `TiedAtR` (ChainOfPromisesR.lean) Rch k a stands among the PREMISES of the
    five ties and nowhere else: so a tie
shown with a weaker condition in hand holds with a stronger one in hand.
  `TiedAtR.mono`: (∀ a, Rch' k a → Rch k a) → TiedAtR … Rch k q → TiedAtR … Rch' k q.
      **`KindTiedR.mono`**: the like for one kind's share (TiedR.lean).
Use. The tower may lay a rider beside "reached" (a fact of the public part that stays along the
    chain) without any kind's files retyping its law.
Limits. A rule over letters. The hand-on (`HandsOn`) is NOT antitone: it is owed anew at the
    stronger condition.
Limits: that file's. A joining of rules: no member is known. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.TiedR

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound

open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (KindName)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers start)

/-- A tie shown with the weaker condition in hand holds with the stronger one in hand. -/
theorem TiedAtR.mono {A Cl P W : Type} {C : CK} {Fr : Frame} {N : Numbers} {Mg : Meaning P W}
    {links : List ModelPart} {ps : List Place} {get : A → P × First.S}
    {Rch Rch' : ℕ → A × Fr.E.Str → Prop} {k : ℕ} {q : Piece C Fr A Cl W}
    (hr : ∀ a, Rch' k a → Rch k a) (h : TiedAtR N Mg links ps get Rch k q) :
    TiedAtR N Mg links ps get Rch' k q := by
  obtain ⟨o, o', R, R', hl, t1, t2, t3, t4, t5, hMark, hDec⟩ := h
  exact ⟨o, o', R, R', hl, fun a ha h' => t1 a ha (hr a h'), fun a τ b ha h' => t2 a τ b ha (hr a
      h'),
    fun a τ b w ha h' => t3 a τ b w ha (hr a h'), fun a τ b w ha h' => t4 a τ b w ha (hr a h'),
    fun a τ b w i ha h' => t5 a τ b w i ha (hr a h'), hMark, hDec⟩

/-- **One kind's share likewise.** -/
theorem KindTiedR.mono {Cl P W : Type} {C : CK} {Fr : Frame} {N : Numbers} {Mg : Meaning P W}
    {links : List ModelPart} {ps : List Place} {Rch Rch' : ℕ → (P × First.S) × Fr.E.Str → Prop}
    {E : ℕ → (P × First.S) × Fr.E.Str → (P × First.S) × Fr.E.Str → W → W}
    {l : List (Piece C Fr (P × First.S) Cl W)} {K : KindName}
    (hr : ∀ k a, Rch' k a → Rch k a) (h : KindTiedR N Mg links ps Rch E l K) :
    KindTiedR N Mg links ps Rch' E l K :=
  fun i q a hq ha hk => TiedAtR.mono (hr i) (h i q a hq ha hk)

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.TiedAtR.mono
#print axioms VerifiableInference.Desc.Sound.KindTiedR.mono
