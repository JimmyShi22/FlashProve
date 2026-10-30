-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/TiedRMonoOn.lean.
WHAT IT DOES NOT SHOW. No soundness. NO LAW OF ANY SUB-PROTOCOL. Book-keeping on the second form of
the chain of promises alone. No example.
WORDS. "The second form": the chain of promises with a condition Rch beside the table's promise at
every border (Desc/Sound/ChainOfPromisesR.lean: TiedAtR; Desc/Sound/TiedR.lean: KindTiedR).
"Unmarked": the verifier's state bears no mark of failure.
LETTERS. No "there is". Rch: the condition under which the law is had; Rch': the condition under
which it is wanted. Kind-free.
OBJECT. TiedAtR's five ties: each has, side by side, the table's promise at the state in front, the
condition there, and "unmarked" there.
USER. A kind's law whose own condition needs, of the state in front, "unmarked" or a clause of the
promise, where the law's proof hands on the condition Rch alone: it is had at Rch := "Rch' and
unmarked" and brought back here. First: the next token's kind's debt "carry 23"
(Law/K7CarryAtHead.lean).
WHAT IT IS. A LAW AT Rch IS A LAW AT Rch' WHEREVER Rch FOLLOWS FROM THE PROMISE, Rch' AND "UNMARKED"
TOGETHER.
TiedAtR.monoOn: at one sub-protocol. KindTiedR.monoOn: at a kind's share. KindTiedR.of_unmarked: the
case Rch := "Rch' and unmarked".
NEAREST RELATIVE: Desc/Sound/TiedRMono.lean: TiedAtR.mono, KindTiedR.mono: the
like where Rch follows from Rch' ALONE; the proofs here are theirs with two premises more handed on.

-/
import Johnson.Desc.Sound.TiedR

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound

open OnBytes.Maker
open _root_.Run.PQ (CK)
open VerifiableInference.Desc (Place KindName)
open VerifiableInference.Desc.First (ModelPart Meaning Numbers)

/-- **At one sub-protocol.** -/
theorem TiedAtR.monoOn {A Cl P W : Type} {C : CK} {Fr : Frame} {N : Numbers} {Mg : Meaning P W}
    {links : List ModelPart} {ps : List Place} {get : A → P × First.S}
    {Rch Rch' : ℕ → A × Fr.E.Str → Prop} {k : ℕ} {q : Piece C Fr A Cl W}
    (hr : ∀ a, onQ N Mg links ps get k a → Rch' k a → ¬ (get a.1).2.failed ≠ none → Rch k a)
    (h : TiedAtR N Mg links ps get Rch k q) : TiedAtR N Mg links ps get Rch' k q := by
  obtain ⟨o, o', R, R', hl, t1, t2, t3, t4, t5, hMark, hDec⟩ := h
  exact ⟨o, o', R, R', hl, fun a ha h' hm => t1 a ha (hr a ha h' hm) hm,
    fun a τ b ha h' hm => t2 a τ b ha (hr a ha h' hm) hm,
    fun a τ b w ha h' hm => t3 a τ b w ha (hr a ha h' hm) hm,
    fun a τ b w ha h' hm => t4 a τ b w ha (hr a ha h' hm) hm,
    fun a τ b w i ha h' hm => t5 a τ b w i ha (hr a ha h' hm) hm, hMark, hDec⟩

/-- **At a kind's share.** -/
theorem KindTiedR.monoOn {Cl P W : Type} {C : CK} {Fr : Frame} {N : Numbers} {Mg : Meaning P W}
    {links : List ModelPart} {ps : List Place} {Rch Rch' : ℕ → (P × First.S) × Fr.E.Str → Prop}
    {E : ℕ → (P × First.S) × Fr.E.Str → (P × First.S) × Fr.E.Str → W → W}
    {l : List (Piece C Fr (P × First.S) Cl W)} {K : KindName}
    (hr : ∀ k a, onQ N Mg links ps (fun a => a) k a → Rch' k a → ¬ a.1.2.failed ≠ none → Rch k a)
    (h : KindTiedR N Mg links ps Rch E l K) : KindTiedR N Mg links ps Rch' E l K :=
  fun i q a hq ha hk => TiedAtR.monoOn (hr i) (h i q a hq ha hk)

/-- **A law under "reached and unmarked" is a law under "reached".** -/
theorem KindTiedR.of_unmarked {Cl P W : Type} {C : CK} {Fr : Frame} {N : Numbers}
    {Mg : Meaning P W} {links : List ModelPart} {ps : List Place}
    {Rch : ℕ → (P × First.S) × Fr.E.Str → Prop}
    {E : ℕ → (P × First.S) × Fr.E.Str → (P × First.S) × Fr.E.Str → W → W}
    {l : List (Piece C Fr (P × First.S) Cl W)} {K : KindName}
    (h : KindTiedR N Mg links ps (fun k a => Rch k a ∧ ¬ a.1.2.failed ≠ none) E l K) :
    KindTiedR N Mg links ps Rch E l K :=
  KindTiedR.monoOn (fun _ _ _ h' hm => ⟨h', hm⟩) h

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.TiedAtR.monoOn
#print axioms VerifiableInference.Desc.Sound.KindTiedR.monoOn
#print axioms VerifiableInference.Desc.Sound.KindTiedR.of_unmarked
