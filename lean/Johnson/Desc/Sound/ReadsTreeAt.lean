-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/ReadsTreeAt.lean: THE CONDITIONS ON LETTERS "a tenant's pin, its promise and its leaves' showing read the oracles through that tenant's tree alone", which the rules on what rides ask (Johnson/Desc/Sound/OcRides.lean: LettersReadBelow ·
OmegaCrosses.lean: ReadsTree · PointMake.lean, RidesMake.lean: the premise on pin₁), PAID AT THE FILLED MEANING (Johnson/Desc/Sound/MeaningSig.lean: pinJT, noCollJT, shownJT, decodesOf, pinWOf). Small lemmas.

  wordOf_col: a tenant's committed word is a function of its tree's columns. wordsOf_col, shownAt_col, pinAt_col, cfAt_col: so are a member's word, its showing, its pin and its condition.
  pinJT_col, noCollJT_col, shownJT_col: THE THREE LETTERS AT TENANT t OF TREE j: of two readings of the oracles that agree at tree j's columns, what holds at the one holds at the other.
  decodesOf_cell, pinWOf_cell: "the table decodes" and the cells' pin read the stored table alone.
  readsTree_sig: ReadsTree (OmegaCrosses.lean) at meaningSigS and promSigS.

Limits. The codes, the members, arr, the samples' readers, the decoder are letters.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.BordersSharedFill
import Johnson.Desc.Sound.OmegaCrosses

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Cb Johnson.Pack OnBytes.Slice
open VerifiableInference.Desc.Shared

section
variable {Xi : Type} (G : FileDescription Xi)

/-- A tenant's committed word is a function of its tree's columns. -/
theorem wordOf_col (y y' : Strs) (j t : ℕ) (h : ∀ x, y'.col j x = y.col j x) :
    wordOf G y' j t = wordOf G y j t := by
  funext x
  show (G.oracleAt j).bind (fun o => o.cut t (y'.col j x)) = _
  rw [h x]
  rfl

variable (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ)

theorem wordsOf_col (y y' : Strs) (i : Fin l.length) (h : ∀ x, y'.col (seat i).1 x = y.col (seat i).1 x) :
    wordsOf G cs l seat y' i = wordsOf G cs l seat y i := by
  unfold wordsOf wordAt
  rw [wordOf_col G y y' (seat i).1 (seat i).2 h]

theorem shownAt_col (y y' : Strs) (i : Fin l.length) (h : ∀ x, y'.col (seat i).1 x = y.col (seat i).1 x)
    (hs : ShownAt G cs l seat y i) : ShownAt G cs l seat y' i := by
  unfold ShownAt at hs ⊢
  rw [wordOf_col G y y' (seat i).1 (seat i).2 h]
  exact hs

variable {A Cells Tok : Type} (smp : A → (i : Fin l.length) → Option ((sigOf cs l).om i).Smp)
  (arr : ℕ → ℕ → ℕ)

theorem pinAt_col (y y' : Strs) (i : Fin l.length) (a : A) (w : Wit Cells Tok MsgT)
    (h : ∀ x, y'.col (seat i).1 x = y.col (seat i).1 x) (hp : PinAt G cs l seat smp arr i a y w) :
    PinAt G cs l seat smp arr i a y' w := by
  obtain ⟨z, hz, hs, hd⟩ := hp
  refine ⟨z, hz, shownAt_col G cs l seat y y' i h hs, ?_⟩
  rw [wordsOf_col G cs l seat y y' i h]
  exact hd

theorem cfAt_col (y y' : Strs) (i : Fin l.length) (a : A)
    (h : ∀ x, y'.col (seat i).1 x = y.col (seat i).1 x) (hp : CfAt G cs l seat smp i a y) :
    CfAt G cs l seat smp i a y' := by
  obtain ⟨z, hz, hs, hc⟩ := hp
  refine ⟨z, hz, shownAt_col G cs l seat y y' i h hs, ?_⟩
  rw [wordsOf_col G cs l seat y y' i h]
  exact hc

end

section
variable (cs : OnBytes.Codes) {Xi A Cells Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp) (ms : List Mem)

/-- **The pin of tenant t of tree j reads the oracles through tree j alone.** -/
theorem pinJT_col (j t : ℕ) (a : A) (y y' : Strs) (w : Wit Cells Tok MsgT)
    (h : ∀ x, y'.col j x = y.col j x) (hp : pinJT cs G arr smp ms j t a y w) :
    pinJT cs G arr smp ms j t a y' w :=
  ⟨hp.1, fun x hx hs => pinAt_col G cs x.1.l x.1.seat (fun z => smp z x.1) arr y y' x.2 a w
    (by
      have e : (x.1.seat x.2).1 = j := congrArg Prod.fst hs
      rw [e]
      exact h) (hp.2 x hx hs)⟩

/-- So does its promise. -/
theorem noCollJT_col (j t : ℕ) (a : A) (y y' : Strs) (h : ∀ x, y'.col j x = y.col j x)
    (hp : noCollJT cs G smp ms j t a y) : noCollJT cs G smp ms j t a y' :=
  fun x hx hs => cfAt_col G cs x.1.l x.1.seat (fun z => smp z x.1) y y' x.2 a
    (by
      have e : (x.1.seat x.2).1 = j := congrArg Prod.fst hs
      rw [e]
      exact h) (hp x hx hs)

/-- So does its leaves' showing. -/
theorem shownJT_col (j t : ℕ) (y y' : Strs) (h : ∀ x, y'.col j x = y.col j x)
    (hp : shownJT cs G ms j t y) : shownJT cs G ms j t y' :=
  ⟨hp.1, fun x hx hs => shownAt_col G cs x.1.l x.1.seat y y' x.2
    (by
      have e : (x.1.seat x.2).1 = j := congrArg Prod.fst hs
      rw [e]
      exact h) (hp.2 x hx hs)⟩

variable (decT : (ℕ → Option (ℕ × List UInt64)) → A → Option Cells)

/-- "The table decodes" reads the stored table alone. -/
theorem decodesOf_cell (a : A) (y y' : Strs) (h : ∀ x, y'.cell x = y.cell x) (hp : decodesOf decT a y) :
    decodesOf decT a y' := by
  have e : y'.cell = y.cell := funext h
  unfold decodesOf at hp ⊢
  rw [e]
  exact hp

/-- So does the cells' pin. -/
theorem pinWOf_cell (a : A) (y y' : Strs) (w : Wit Cells Tok MsgT) (h : ∀ x, y'.cell x = y.cell x)
    (hp : pinWOf decT a y w) : pinWOf decT a y' w := by
  have e : y'.cell = y.cell := funext h
  unfold pinWOf at hp ⊢
  rw [e]
  exact hp

end

/-- **ReadsTree at the filled letters of the shared chain's table.** -/
theorem readsTree_sig (cs : OnBytes.Codes) {Xi S₂ P₁ Cells Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
    (smp₂ : S₂ → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (decT₂ : (ℕ → Option (ℕ × List UInt64)) → S₂ → Option Cells)
    (stOf : S₂ → OnBytes.Statement) (bookOf : S₂ → OnBytes.TreeBook)
    (Mg : MeaningS S₂ P₁ (Wit Cells Tok MsgT)) (Pm : PromMeaning S₂) :
    ReadsTree (meaningSigS cs G arr smp₂ ms decT₂ Mg) (promSigS cs G smp₂ ms stOf bookOf Pm) :=
  ⟨fun j t y y' h hp => shownJT_col cs G ms j t y y' h hp,
    fun j t s y y' h hp => noCollJT_col cs G smp₂ ms j t s y y' h hp,
    fun j t s y y' w h hp => pinJT_col cs G arr smp₂ ms j t s y y' w h hp⟩

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.pinJT_col
#print axioms VerifiableInference.Desc.Sound.noCollJT_col
#print axioms VerifiableInference.Desc.Sound.shownJT_col
#print axioms VerifiableInference.Desc.Sound.decodesOf_cell
#print axioms VerifiableInference.Desc.Sound.pinWOf_cell
#print axioms VerifiableInference.Desc.Sound.readsTree_sig
