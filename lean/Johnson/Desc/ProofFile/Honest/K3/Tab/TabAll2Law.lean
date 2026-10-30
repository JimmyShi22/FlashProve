-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Tab/TabAll2Law.lean:
the reader of the input with all four sorts off tables is `boundWit`, and the lots over it are the
lots at `boundWit`. Theorems without a hypothesis.

Terms. Honest/K3/GLOSSARY.md; Honest/K3/Tab/TabAll2.lean.

What is shown.
  `tabSourcesAll2_eq`, `sourcesAtTabAll2_eq`: the letters off tables are `ownSourcesBound` and
    `sourcesAtBound` (Honest/K3/WitBound.lean).
  `tabWitAll2_eq`: the main theorem: `tabWitAll2 cells weights req Z s` is
    `boundWit cells weights req Z s`, at every site.
  `theLotKeepTabAll2_eq`, `theLotInstKeepTabAll2_eq`: the lots are `theLotKeepBound` and
    `theLotInstKeepBound` (Honest/K3/LotInstKeepBound.lean): so every law of these carries over by
    one rewriting.

By. `layersTab_eq` (Honest/K3/Tab/TabGLaw.lean), `attnTab_eq` (Honest/K3/Tab/TabALaw.lean),
`headTab_eq` (Honest/K3/Tab/TabHLaw.lean), `tabAsk_eq` (Honest/K3/Law/DigitsTab.lean).

Imported. Honest/K3/Tab/TabAll2.lean and these four (Honest/K3/Tab/TabALaw.lean through
TabAll2.lean).

Limits. The equations say that the terms are equal, not how long either takes.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Tab.TabAll2
import Johnson.Desc.ProofFile.Honest.K3.Tab.TabGLaw
import Johnson.Desc.ProofFile.Honest.K3.Tab.TabHLaw
import Johnson.Desc.ProofFile.Honest.K3.Law.DigitsTab

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3

variable {X : Type} {W₀ Rc Xi Tr : Type}

theorem tabSourcesAll2_eq (X : OnBytes.Model.Verify.Public) (cells : Tr → Cells)
    (weights : W₀ → Weights) (pubH : Xi → OnBytes.Ends.H.PubH) :
    tabSourcesAll2 X cells weights pubH = ownSourcesBound X cells weights pubH := by
  have h1 : TabG.layersTab X = (ownSourcesBound X cells weights pubH).layers := by
    funext g C W
    exact TabG.layersTab_eq X cells weights pubH g C W
  have h2 : TabA.attnTab X = (ownSourcesBound X cells weights pubH).attention := by
    funext g C
    exact TabA.attnTab_eq X cells weights pubH g C
  have h3 : (fun x C W => TabH.headTab X (pubH x) C W) =
      (ownSourcesBound X cells weights pubH).head := by
    funext x C W
    exact TabH.headTab_eq X cells weights pubH x C W
  unfold tabSourcesAll2
  rw [h1, h2, h3]

theorem sourcesAtTabAll2_eq (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) :
    sourcesAtTabAll2 cells weights req Z = sourcesAtBound cells weights req Z :=
  tabSourcesAll2_eq Z.p.X cells weights _

/-- **The reader off tables is `boundWit`, at every site.** -/
theorem tabWitAll2_eq (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) (s : Site) :
    tabWitAll2 (Rc := Rc) cells weights req Z s = boundWit cells weights req Z s := by
  unfold tabWitAll2 boundWit
  cases s.rng with
  | none =>
    show (fastFill (Rc := Rc) (sourcesAtTabAll2 cells weights req Z)).wit s =
      (fastFill (Rc := Rc) (sourcesAtBound cells weights req Z)).wit s
    rw [sourcesAtTabAll2_eq]
  | some r =>
    funext t heard
    exact tabAsk_eq _ _ _ _ _

/-- **The lot is `theLotKeepBound`.** -/
theorem theLotKeepTabAll2_eq (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (get : X → RowOwn)
    (set : X → RowOwn → X) :
    theLotKeepTabAll2 (Rc := Rc) cells weights req get set =
      theLotKeepBound cells weights req get set := by
  have h : ∀ Z, tabWitAll2 (Rc := Rc) cells weights req Z = boundWit cells weights req Z :=
    fun Z => funext fun s => tabWitAll2_eq cells weights req Z s
  unfold theLotKeepTabAll2 theLotKeepBound
  simp only [h]

/-- **The lot at the proof file's own instance is `theLotInstKeepBound`.** -/
theorem theLotInstKeepTabAll2_eq (cells : Tr → Cells) (weights : W₀ → Weights)
    (get : X → RowOwn) (set : X → RowOwn → X) :
    theLotInstKeepTabAll2 (Rc := Rc) cells weights get set =
      theLotInstKeepBound cells weights get set := by
  have h : ∀ Z,
      tabWitAll2 (Rc := Rc) cells weights (reqAt Z) Z = boundWit cells weights (reqAt Z) Z :=
    fun Z => funext fun s => tabWitAll2_eq cells weights (reqAt Z) Z s
  unfold theLotInstKeepTabAll2 theLotInstKeepBound
  simp only [h]

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.tabSourcesAll2_eq
#print axioms ProofFile.Honest.K3.sourcesAtTabAll2_eq
#print axioms ProofFile.Honest.K3.tabWitAll2_eq
#print axioms ProofFile.Honest.K3.theLotKeepTabAll2_eq
#print axioms ProofFile.Honest.K3.theLotInstKeepTabAll2_eq
