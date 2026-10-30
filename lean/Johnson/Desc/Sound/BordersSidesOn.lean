-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/BordersSidesOn.lean: "AN ITEM's MEANING READS THE WITNESS THROUGH THE COMPONENTS
THAT THE TABLE NAMES FOR IT", ASKED INSIDE THE PROMISE AND WITHOUT A MARK. One definition, two
theorems. A file BESIDE the table of joints: it turns nothing of it.

Why. `framesOfSides` (Johnson/Desc/Sound/BordersSides.lean) takes `ReadsOkQ`, which binds EVERY
record. A sentence that finds a message's seat through the record's own book reads, at a record
outside the promise, whatever seat that book names: there `ReadsOkQ` is false of it, though at an
unmarked record inside the promise the book's places are the plan's. But what is owed for the items
that ride (`Piece.Frames`, Johnson/Desc/Sound/Spine.lean) is owed only at statements at which the
promise in front of the block holds and from which the block says yes, and only of the items that
ride there. A MARKED RECORD IS INSIDE EVERY PROMISE, with whatever book: so the promise alone does
not fence enough; but a block that refuses every marked record has no yes from one. So the same
proof goes through from less.

What is said. `ReadsOkAtQ k`: `ReadsOkQ`'s clause, asked at the statements with `onQ k` whose record
bears no mark, and of the items that are open at border k and that block number k does not close.
`readsOkAt_of_readsOk`: the elder premise gives it, at every k. `framesOfSidesOn`:
`framesOfSides`'s conclusion from it, at a piece that has no yes from a marked record (hm).

Limits. (1) A rule over letters: it pays nothing by itself. (2) hm is a fact on the block's text (a
guard in front of it): a premise here. (3) Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.BordersSides

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Fo.Peel Cb Johnson.Pack OnBytes.Slice
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers Comp start)

/-- **Inside the promise in front of block number k, at a record without a mark, an item that rides
there reads the witness through the components that the table names for it.** -/
def ReadsOkAtQ {A P Cells Tok : Type} {Fr : Frame} (arr : ℕ → ℕ → ℕ) (N : Numbers)
    (Mg : Meaning P (Wit Cells Tok MsgT)) (links : List ModelPart) (ps : List Place)
    (get : A → P × First.S) (k : ℕ) : Prop :=
  ∀ (i : Item) (a : A × Fr.E.Str) (w w' : Wit Cells Tok MsgT), onQ N Mg links ps get k a →
    (get a.1).2.failed = none →
    openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
    (∀ c ∈ i.reads arr N links, sameQ c w w') → meansQ N Mg get i a w → meansQ N Mg get i a w'

/-- The premise that binds every record gives it. -/
theorem readsOkAt_of_readsOk {A P Cells Tok : Type} {Fr : Frame} (arr : ℕ → ℕ → ℕ) (N : Numbers)
    (Mg : Meaning P (Wit Cells Tok MsgT)) (links : List ModelPart) (ps : List Place)
    (get : A → P × First.S) (k : ℕ) (h : ReadsOkQ arr N links Mg) :
    ReadsOkAtQ (Fr := Fr) arr N Mg links ps get k :=
  fun i _ w w' _ _ _ _ hc hw => h i _ _ w w' hc hw

section
variable (cs : OnBytes.Codes) {Xi P Cells Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : P × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → P × First.S → Option Cells)
  (c₀ : Cells) (tokOf : P × First.S → Tok)

/-- **WHAT IS LEFT OF `Piece.Frames` AT BLOCK NUMBER k IS THE STATEMENT's SIDE, AT ONE w**: from the
reading asked inside the promise and without a mark. -/
theorem framesOfSidesOn {A Cl : Type} {C : CK} {Fr : Frame} (N : Numbers)
    (Mg : Meaning P (Wit Cells Tok MsgT)) (links : List ModelPart) (ps : List Place)
    (get : A → P × First.S) (k : ℕ) (q : Piece C Fr A Cl (Wit Cells Tok MsgT))
    (hr : ReadsOkAtQ (Fr := Fr) arr N Mg links ps get k) (hc : RidersClearQ arr N links ps)
    (hm : ∀ a τ b, q.ior.red.out a τ = some b → (get a.1).2.failed = none)
    (hx : ∀ a τ b w, q.ior.red.out a τ = some b →
      q.ext a τ w = extQAt cs G arr smp ms decT c₀ tokOf N links ps get k a b w)
    (hs : ∀ a τ b w i, q.ior.red.out a τ = some b →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ N Mg get i b w → meansQ N Mg get i a w) :
    q.Frames (onQ N Mg links ps get k) (onQ N Mg links ps get (k + 1)) (meansQ N Mg get)
      (openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k) (insQ links ps k) := by
  intro a τ b w i ha hb _ ho hn hw
  rw [hx a τ b w hb]
  exact hr i a w _ ha (hm a τ b hb) ho hn
    (fun c hcc => extQAt_keeps cs G arr smp ms decT c₀ tokOf N links ps get k a b w c
      (hc k i ho hn c hcc))
    (hs a τ b w i hb ho hn hw)

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.readsOkAt_of_readsOk
#print axioms VerifiableInference.Desc.Sound.framesOfSidesOn
