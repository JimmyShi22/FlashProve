-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/BordersSidesOnR.lean: "THE RIDERS STAY", WITH THE CONDITION Rch BESIDE THE
PROMISE: the second form of Johnson/Desc/Sound/BordersSidesOn.lean. One definition, three theorems.
A RULE OVER LETTERS. A file BESIDE the table of joints: it turns nothing of it.

Why. `ReadsOkAtQ k` ("an item that rides past sub-protocol k reads of the witness only what the
table says that it reads") is asked at every statement inside the table's promise at border k. Where
an item's sentence reads the witness through a reader that takes the verifier's state, the lemma
that pays it may want a fact on that state which the promise says no more, since it is had from Rch
(Johnson/Desc/Sound/ChainOfPromisesR.lean; Johnson/Desc/First/FoldFacts.lean).

What is said. `ReadsOkAtQR k`: `ReadsOkAtQ k` with ONE PREMISE MORE: Rch k a.
`readsOkAtR_of_readsOkAt`: the first form gives the second, for nothing. `framesOfSidesOnR`: the
riders stay, between `onR k` and `onR (k + 1)`. `t5R_of_sides`: the fifth tie of `TiedAtR`, to the
letter; there the premise "what holds behind holds in front at one witness" is asked inside the same
fence: the promise and Rch in front, no mark, the piece accepts, the promise behind.

Limits. Those of the two files named. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.BordersSidesOn
import Johnson.Desc.Sound.ChainOfPromisesR

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound

open OnBytes.Maker Fo.Peel Cb Johnson.Pack OnBytes.Slice
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers Comp start)

/-- **A rider reads of the witness only what the table says, asked inside the promise and Rch.** -/
def ReadsOkAtQR {A P Cells Tok : Type} {Fr : Frame} (arr : ℕ → ℕ → ℕ) (N : Numbers)
    (Mg : Meaning P (Wit Cells Tok MsgT)) (links : List ModelPart) (ps : List Place)
    (get : A → P × First.S) (Rch : ℕ → A × Fr.E.Str → Prop) (k : ℕ) : Prop :=
  ∀ (i : Item) (a : A × Fr.E.Str) (w w' : Wit Cells Tok MsgT), onQ N Mg links ps get k a →
    Rch k a → (get a.1).2.failed = none →
    openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
    (∀ c ∈ i.reads arr N links, sameQ c w w') → meansQ N Mg get i a w → meansQ N Mg get i a w'

theorem readsOkAtR_of_readsOkAt {A P Cells Tok : Type} {Fr : Frame} (arr : ℕ → ℕ → ℕ)
    (N : Numbers) (Mg : Meaning P (Wit Cells Tok MsgT)) (links : List ModelPart) (ps : List Place)
    (get : A → P × First.S) (Rch : ℕ → A × Fr.E.Str → Prop) (k : ℕ)
    (h : ReadsOkAtQ (Fr := Fr) arr N Mg links ps get k) :
    ReadsOkAtQR arr N Mg links ps get Rch k :=
  fun i a w w' ha _ => h i a w w' ha

section
variable (cs : OnBytes.Codes) {Xi P Cells Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : P × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → P × First.S → Option Cells)
  (c₀ : Cells) (tokOf : P × First.S → Tok)

/-- **The riders stay, between the two conditions with Rch beside the promise.** -/
theorem framesOfSidesOnR {A Cl : Type} {C : CK} {Fr : Frame} (N : Numbers)
    (Mg : Meaning P (Wit Cells Tok MsgT)) (links : List ModelPart) (ps : List Place)
    (get : A → P × First.S) (Rch : ℕ → A × Fr.E.Str → Prop) (k : ℕ)
    (q : Piece C Fr A Cl (Wit Cells Tok MsgT))
    (hr : ReadsOkAtQR arr N Mg links ps get Rch k) (hc : RidersClearQ arr N links ps)
    (hm : ∀ a τ b, q.ior.red.out a τ = some b → (get a.1).2.failed = none)
    (hx : ∀ a τ b w, q.ior.red.out a τ = some b →
      q.ext a τ w = extQAt cs G arr smp ms decT c₀ tokOf N links ps get k a b w)
    (hs : ∀ a τ b w i, q.ior.red.out a τ = some b →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ N Mg get i b w → meansQ N Mg get i a w) :
    q.Frames (onR N Mg links ps get Rch k) (onR N Mg links ps get Rch (k + 1)) (meansQ N Mg get)
      (openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k) (insQ links ps k) := by
  intro a τ b w i ha hb _ ho hn hw
  rw [hx a τ b w hb]
  exact hr i a w _ ha.1 ha.2 (hm a τ b hb) ho hn
    (fun c hcc => extQAt_keeps cs G arr smp ms decT c₀ tokOf N links ps get k a b w c
      (hc k i ho hn c hcc))
    (hs a τ b w i hb ho hn hw)

/-- **The fifth tie of `TiedAtR`, from the sides.** -/
theorem t5R_of_sides {A Cl : Type} {C : CK} {Fr : Frame} (N : Numbers)
    (Mg : Meaning P (Wit Cells Tok MsgT)) (links : List ModelPart) (ps : List Place)
    (get : A → P × First.S) (Rch : ℕ → A × Fr.E.Str → Prop) (k : ℕ)
    (q : Piece C Fr A Cl (Wit Cells Tok MsgT))
    (hr : ReadsOkAtQR arr N Mg links ps get Rch k) (hc : RidersClearQ arr N links ps)
    (hx : ∀ a τ b w, q.ior.red.out a τ = some b →
      q.ext a τ w = extQAt cs G arr smp ms decT c₀ tokOf N links ps get k a b w)
    (hs : ∀ a τ b w i, onQ N Mg links ps get k a → Rch k a → (get a.1).2.failed = none →
      q.ior.red.out a τ = some b → onQ N Mg links ps get (k + 1) b →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ N Mg get i b w → meansQ N Mg get i a w) :
    ∀ a τ b w i, onQ N Mg links ps get k a → Rch k a → ¬ (get a.1).2.failed ≠ none →
      q.ior.red.out a τ = some b → onQ N Mg links ps get (k + 1) b →
      relQ N Mg links ps get (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ N Mg get i a (q.ext a τ w) := by
  intro a τ b w i ha hR hm hb hon hall ho hn
  have hm' : (get a.1).2.failed = none := Classical.not_not.1 hm
  rw [hx a τ b w hb]
  exact hr i a w _ ha hR hm' ho hn
    (fun c hcc => extQAt_keeps cs G arr smp ms decT c₀ tokOf N links ps get k a b w c
      (hc k i ho hn c hcc))
    (hs a τ b w i ha hR hm' hb hon ho hn (hall i (Or.inl ⟨ho, hn⟩)))

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.readsOkAtR_of_readsOkAt
#print axioms VerifiableInference.Desc.Sound.framesOfSidesOnR
#print axioms VerifiableInference.Desc.Sound.t5R_of_sides
