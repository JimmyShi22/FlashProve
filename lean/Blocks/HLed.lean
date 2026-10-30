-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/HLed.lean: the honest prover's copy of the record of claims, up to the closing of a segment.

The record (`Ledger`, Blocks/Form.lean) is the verifier's list of deferred claims of a segment:
LIN(f): the value of the form f is 0; REL(f; terms): the value of f is a sum of products c · o_i ·
o_j of values of opened forms. The shape of the closing (Blocks/ClosingBlock.lean) depends on how
many there are, and its honest prover needs the values of the opened forms and the terms of the REL.
`HLed` (the number of LIN, the values, the terms; no pad) and `HLed.Of` (the copy belongs to the
record) are in Blocks/LookupHon.lean, `HLed.len` in Blocks/LookupStage.lean. (Words of this library:
lean/GLOSSARY.md.) Here:
 * `Ledger.addLins`, `Ledger.wf_push`; `HLed.addLins`, `HLed.Of.push`; the counts after every
   operation (`HLed.len_addProd`, ..).
 * `HLed.Good h led y`: the copy belongs to the record, every term of a REL names an opened form on
   record, and all recorded claims are true. Every operation whose new claims are true preserves it
   (`Good.addRel`: if its terms name forms among those that it opens).
 * `HLed.toClose`, `HLed.Good.honLedger`: from `Good`, the three counts, and the pads of the closing
   at their places, the honest relation before the closing (`Closing.HonLedger`).
-/
import Blocks.LookupStage
import Blocks.ClosingBlock

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Blocks

/-! ## 1. The record -/

namespace Ledger

variable {N E : Type}

/-- The record with more claims LIN. -/
def addLins (x : Ledger N E) (fs : List (Form N E)) : Ledger N E := ⟨x.lin ++ fs, x.opn, x.rel⟩

theorem wf_addLins (x : Ledger N E) (fs : List (Form N E)) : (x.addLins fs).wf = x.wf := rfl

theorem true_addLins [Fintype N] [CommRing E] (x : Ledger N E) (fs : List (Form N E)) (y : N → E) :
    (x.addLins fs).True y ↔ x.True y ∧ ∀ f ∈ fs, Form.val y f = 0 := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨fun g hg => h1 g (List.mem_append_left _ hg), h2⟩,
      fun f hf => h1 f (List.mem_append_right _ hf)⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨fun g hg => ?_, h2⟩
    rcases List.mem_append.mp hg with hg | hg
    · exact h1 g hg
    · exact h3 g hg

/-- Carrying the record along a map of entries changes neither the terms nor the number of opened
forms. -/
theorem wf_push [Fintype N] [CommRing E] {N' : Type} [DecidableEq N']
    (σ : N → N') (x : Ledger N E) : (x.push σ).wf = x.wf := by
  unfold wf push
  simp only [List.all_map, List.length_map]
  rfl

end Ledger

/-! ## 2. The copy -/

namespace HLed

variable {N E : Type}

def addLins (h : HLed E) (n : ℕ) : HLed E := ⟨h.nl + n, h.ov, h.tm⟩

theorem len_addProd [One E] (h : HLed E) (e0 e1 : E) :
    (h.addProd e0 e1).len = (h.len.1, h.len.2.1 + 2, h.len.2.2 + 1) := by
  simp [len, addProd]

theorem len_addLin (h : HLed E) : h.addLin.len = (h.len.1 + 1, h.len.2.1, h.len.2.2) := rfl

theorem len_addLins (h : HLed E) (n : ℕ) :
    (h.addLins n).len = (h.len.1 + n, h.len.2.1, h.len.2.2) := rfl

theorem len_addRel (h : HLed E) (vs : List E) (ts : List (E × ℕ × ℕ)) :
    (h.addRel vs ts).len = (h.len.1, h.len.2.1 + vs.length, h.len.2.2 + 1) := by
  simp [len, addRel]

variable [Fintype N] [CommRing E]

theorem Of.addLins {h : HLed E} {led : Ledger N E} {y : N → E}
    (H : h.Of led y) (fs : List (Form N E)) :
    (h.addLins fs.length).Of (led.addLins fs) y := by
  refine ⟨?_, H.2.1, H.2.2⟩
  show (led.lin ++ fs).length = h.nl + fs.length
  rw [List.length_append, H.1]

/-- If the copy belongs to the record on the entries y' (σ n), it belongs to the carried record on
y'. -/
theorem Of.push {N' : Type} [Fintype N'] [DecidableEq N'] (σ : N → N') {h : HLed E}
    {led : Ledger N E} {y' : N' → E} (H : h.Of led fun n => y' (σ n)) : h.Of (led.push σ) y' := by
  refine ⟨?_, ?_, ?_⟩
  · show (led.lin.map (Form.push σ)).length = h.nl
    rw [List.length_map]
    exact H.1
  · show (led.opn.map (Form.push σ)).map (fun f => Form.val y' f) = h.ov
    rw [List.map_map, ← H.2.1]
    exact List.map_congr_left fun f _ => Form.val_push σ f y'
  · show (led.rel.map fun r => (Form.push σ r.1, r.2)).map (fun r => r.2) = h.tm
    rw [List.map_map, ← H.2.2]
    rfl

/-- What the honest relation of a cut (`Cut`, Blocks/Stage.lean) says of the record: the copy
belongs to it, every term of a REL names an opened form that is on record, and all recorded claims
are true. -/
def Good (h : HLed E) (led : Ledger N E) (y : N → E) : Prop :=
  h.Of led y ∧ led.wf = true ∧ led.True y

variable {h : HLed E} {led : Ledger N E} {y : N → E}

theorem good_empty (y : N → E) : (⟨0, [], []⟩ : HLed E).Good (Ledger.empty : Ledger N E) y :=
  ⟨⟨rfl, rfl, rfl⟩, rfl, Ledger.true_empty y⟩

theorem Good.addProd (H : h.Good led y) {f a b : Form N E}
    (hf : Form.val y f = Form.val y a * Form.val y b) :
    (h.addProd (Form.val y a) (Form.val y b)).Good (led.addProd f a b) y :=
  ⟨H.1.addProd f a b,
    Ledger.wf_addProd H.2.1 f a b,
    (Ledger.true_addProd H.2.1 f a b y).mpr ⟨H.2.2, hf⟩⟩

theorem Good.addLin (H : h.Good led y) {f : Form N E} (hf : Form.val y f = 0) :
    h.addLin.Good (led.addLin f) y :=
  ⟨H.1.addLin f, H.2.1, (Ledger.true_addLin led f y).mpr ⟨H.2.2, hf⟩⟩

theorem Good.addLins (H : h.Good led y) {fs : List (Form N E)} (hf : ∀ f ∈ fs, Form.val y f = 0) :
    (h.addLins fs.length).Good (led.addLins fs) y :=
  ⟨H.1.addLins fs, H.2.1, (Ledger.true_addLins led fs y).mpr ⟨H.2.2, hf⟩⟩

theorem Good.addRel (H : h.Good led y) {f : Form N E} {os : List (Form N E)} {ts : List (E × ℕ × ℕ)}
    (hts : ∀ t ∈ ts, t.2.1 < os.length ∧ t.2.2 < os.length)
    (hf : Form.val y f = termSum (fun i => Form.val y (os.getD i 0)) ts) :
    (h.addRel (os.map fun g => Form.val y g) ts).Good (led.addRel f os ts) y :=
  ⟨H.1.addRel f os ts,
    Ledger.wf_addRel H.2.1 f hts,
    (Ledger.true_addRel H.2.1 f os ts y).mpr ⟨H.2.2, hf⟩⟩

theorem Good.push {N' : Type} [Fintype N'] [DecidableEq N'] (σ : N → N')
    {y' : N' → E} (H : h.Good led fun n => y' (σ n)) : h.Good (led.push σ) y' :=
  ⟨H.1.push σ, (Ledger.wf_push σ led).trans H.2.1, (Ledger.true_push σ led y').mpr H.2.2⟩

end HLed

/-! ## 3. The step to the closing -/

namespace HLed

variable {N E P : Type} [Fintype N] [DecidableEq N] [Field E] [Fintype E] [DecidableEq E]

/-- What the honest prover of the closing takes from its copy of the record. -/
def toClose (h : HLed E) (nR nO : ℕ) : Closing.HClose E (Fin nR) nO :=
  (fun o => h.ov.getD o 0, fun r => h.tm.getD r [])

/-- Before the closing. If the copy is good for the record, the record has nL LIN, nO opened forms
and nR REL, and the pads of the closing are at their places, then the record belongs to the honest
state of the closing. -/
theorem Good.honLedger {h : HLed E} {led : Ledger N E} {y : N → E} (H : h.Good led y) {nL nO nR : ℕ}
    (hlen : h.len = (nL, nO, nR)) (pl : Closing.Places N (Fin nR) nO)
    (pp : Closing.Places P (Fin nR) nO) {π : P → E} (haux : ∀ k, y (pl.aux k) = π (pp.aux k))
    (hopn : ∀ o, y (pl.opn o) = π (pp.opn o)) :
    Closing.HonLedger nL pl pp (h.toClose nR nO) π led y := by
  have hl := H.1.len.trans hlen
  refine ⟨⟨congrArg Prod.fst hl, congrArg (fun q => q.2.1) hl, congrArg (fun q => q.2.2) hl⟩, haux,
    hopn, fun o => ?_, fun r => ?_, H.2.2⟩
  · show h.ov.getD o 0 = _
    rw [← H.1.2.1, ← map_zero (Form.val y)]
    exact List.getD_map led.opn (0 : Form N E) (fun f => Form.val y f)
  · show h.tm.getD r [] = _
    rw [← H.1.2.2]
    exact List.getD_map led.rel ((0 : Form N E), ([] : List (E × ℕ × ℕ))) (fun r => r.2)

end HLed

end Blocks

