-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/PartsOfValues.lean: seven parts of the library's ledger of a layers' sub-proof hold
of entries y, if the forms that the library lists in them are worth 0 at y. Bookkeeping.

The library's ledger has eleven parts (LayCl, Cb/Pv/Lay/End/LayEnd.lean); clAt
(Cb/Pv/Lay/End/LayHEnd.lean) and restAt (Cb/Pv/Lay/End/LayAll.lean) fill eight of them off a last
statement e of the chain. Each of the eight is, by definition, the ledger ledOf of a list of forms
(Cb/Pv/Lay/End/Led.lean), and ledOf l holds of y exactly if every form of l is worth 0 at y
(ledOf_holds). Here that is said part by part, for seven of the eight, with every form written in
the library's own names at the letters that the library's definitions put in. So the statements
show at which names and at which record a comparison with another text's claims has to be made:
  sq, bat, led, hot: the names namesAt P.nr (readsAt Y ιN); the record eAt P.toOwnPar P.wPart e
    (zt e); the sumchecks' own claims u1At P.nr (b1 e).2 and u2At P.nr (b2 e).2;
  terms: the names namesT P.tp (readsT Y ιT); the record termsEAt P.tp (b3 e).2;
  gated: the names gNamesAt P.fp (gReadsAt Y ιG); the record gatedEAt P.fp (b5 e).2 (b6 e).2; the
    sumchecks' own claims prodU P.fp.gp (b5 e).2 and prodU P.fp.rt.L (b6 e).2;
  stack: no names and no record: upForm of the sumcheck's own row, and rowF P.ip (b4 e).2 at the
    two form parts.

Main names:
  `clF`: the ledger, part by part, with any letters R for the three parts that stay letters.
  `parts_are`: what the eight parts are, each by definition.
  `sq_holds`, `bat_holds`, `led_holds`, `terms_holds`, `gated_holds`, `hot_holds`, `stack_holds`.
Limits. Implications between statements on lists of forms, at any entries y. That any form is worth
0 is a premise, the sumchecks' own claims among them. The part merge is named in parts_are alone.
Nothing ties these forms to a program's claims; nothing on true reads or on soundness.


-/
import Cb.Pv.Lay.End.LayAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open TWhole Cb Cb.Sub Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open Inst.Model (Scl)

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type} (P : FullPar E M X)
  {Nm J₂ : Type} [Fintype J₂] [DecidableEq J₂] (Y : LateLay Nm J₂) (ιN : NormsNm → Nm)
  (ιT : TermsNm → Nm) (ιG : GatedNm → Nm) (R : (tailF P).s7.Nx → Rest3 E (P.J ⊕ J₂)) (sG : ℕ)
  (zt : (tailF P).s7.Nx → ℕ → E) (b B : ℕ) (e : (tailF P).s7.Nx)

/-- The library's ledger of a layers' sub-proof, part by part, off the last statement e. R: the
three parts that stay letters in the library. -/
noncomputable abbrev clF : LayCl E (P.J ⊕ J₂) :=
  clAt P.toOwnPar P.wPart Y ιN (restAt P Y ιT ιG R sG) zt b B e

omit [Fintype J₂] in
/-- What the eight parts are: each equation holds by definition. -/
theorem parts_are :
    (clF P Y ιN ιT ιG R sG zt b B e).sq = sqAt P.toOwnPar P.wPart Y ιN e (zt e) b B ∧
    (clF P Y ιN ιT ιG R sG zt b B e).bat = batAt P.toOwnPar P.wPart Y ιN e (zt e) ∧
    (clF P Y ιN ιT ιG R sG zt b B e).led = rowsAt P.toOwnPar P.wPart Y ιN e (zt e) ∧
    (clF P Y ιN ιT ιG R sG zt b B e).terms = termsLedAt P.toOwnPar P.wPart Y ιT e ∧
    (clF P Y ιN ιT ιG R sG zt b B e).gated =
      gatedLedOf P.fp Y ιG ((tailF P).b5 e).2 ((tailF P).b6 e).2 sG ∧
    (clF P Y ιN ιT ιG R sG zt b B e).hot = hotAt P.toOwnPar Y ιN ∧
    (clF P Y ιN ιT ιG R sG zt b B e).stack = stackLedAt P.toOwnPar P.wPart e ∧
    (clF P Y ιN ιT ιG R sG zt b B e).merge = mergeLed P.wp0 e.2 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

variable (y : P.J ⊕ J₂ → E)

/-- The part sq: the claim that the product layer of the squares leaves; "the two end values are
one"; the end value against the reads of the stream's limbs. -/
theorem sq_holds (h1 : Blocks.Form.val y (u1At P.nr ((tailF P).b1 e).2) = 0)
    (h2 : Blocks.Form.val y
      (cSame (namesAt P.nr (readsAt Y ιN)) (eAt P.toOwnPar P.wPart e (zt e))) = 0)
    (h3 : Blocks.Form.val y
      (Cb.Pv.Lay.End.cEnd (namesAt P.nr (readsAt Y ιN)) (eAt P.toOwnPar P.wPart e (zt e))
        (P.D.lL + 1) b B P.D.nNu) = 0) :
    Ledger.Holds (clF P Y ιN ιT ιG R sG zt b B e).sq y := by
  have k : Ledger.Holds (sqAt P.toOwnPar P.wPart Y ιN e (zt e) b B) y := by
    unfold sqAt
    refine (ledOf_holds _ y).2 fun f hf => ?_
    simp only [clNorms, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
  exact k

/-- The part bat: the hidden sum of the token sumcheck of the row products is the batch of the
hidden products. -/
theorem bat_holds (h : Blocks.Form.val y
      (cBatch (namesAt P.nr (readsAt Y ιN)) (eAt P.toOwnPar P.wPart e (zt e)) P.D.nNu) = 0) :
    Ledger.Holds (clF P Y ιN ιT ιG R sG zt b B e).bat y := by
  have k : Ledger.Holds (batAt P.toOwnPar P.wPart Y ιN e (zt e)) y := by
    unfold batAt
    refine (ledOf_holds _ y).2 fun f hf => ?_
    rw [List.mem_singleton.mp hf]
    exact h
  exact k

/-- The part led: the claim that the token sumcheck of the row products leaves, and the claims of
clLedger behind its head. u: any form; the list behind the head does not read it. -/
theorem led_holds (hu : Blocks.Form.val y (u2At P.nr ((tailF P).b2 e).2) = 0)
    (u : Blocks.Form (P.J ⊕ J₂) E)
    (h : ∀ q ∈ (clLedger (namesAt P.nr (readsAt Y ιN)) (eAt P.toOwnPar P.wPart e (zt e)) u
      P.D).tail, Blocks.Form.val y q = 0) :
    Ledger.Holds (clF P Y ιN ιT ιG R sG zt b B e).led y := by
  have k : Ledger.Holds (rowsAt P.toOwnPar P.wPart Y ιN e (zt e)) y := by
    unfold rowsAt
    refine (ledOf_holds _ y).2 fun f hf => ?_
    rcases List.mem_cons.mp hf with rfl | hf'
    · exact hu
    · exact h f hf'
  exact k

/-- The part terms: the claims on the end values of the sumcheck of the terms. -/
theorem terms_holds
    (h : ∀ q ∈ termsCl (namesT P.tp (readsT Y ιT)) (termsEAt P.tp ((tailF P).b3 e).2) P.D,
      Blocks.Form.val y q = 0) :
    Ledger.Holds (clF P Y ιN ιT ιG R sG zt b B e).terms y := by
  have k : Ledger.Holds (termsLedAt P.toOwnPar P.wPart Y ιT e) y := by
    unfold termsLedAt termsLed
    exact (ledOf_holds _ y).2 h
  exact k

/-- The part gated: the claims that the two product layers of the gated products leave, and the four
claims on their end values. -/
theorem gated_holds (h5 : Blocks.Form.val y (prodU P.fp.gp ((tailF P).b5 e).2) = 0)
    (h6 : Blocks.Form.val y (prodU P.fp.rt.L ((tailF P).b6 e).2) = 0)
    (h : ∀ q ∈ gatedCl (gNamesAt P.fp (gReadsAt Y ιG))
      (gatedEAt P.fp ((tailF P).b5 e).2 ((tailF P).b6 e).2) P.D sG, Blocks.Form.val y q = 0) :
    Ledger.Holds (clF P Y ιN ιT ιG R sG zt b B e).gated y := by
  have k : Ledger.Holds
      (gatedLedOf P.fp Y ιG ((tailF P).b5 e).2 ((tailF P).b6 e).2 sG) y := by
    unfold gatedLedOf gatedLed
    refine (ledOf_holds _ y).2 fun f hf => ?_
    rcases (mem_two_two _ _ _ _).1 hf with rfl | rfl | hf'
    · exact h5
    · exact h6
    · exact h f hf'
  exact k

/-- The part hot: the selectors' entries of each routed layer sum to 1. -/
theorem hot_holds
    (h : ∀ q ∈ clHot (E := E) (namesAt P.nr (readsAt Y ιN)) P.D, Blocks.Form.val y q = 0) :
    Ledger.Holds (clF P Y ιN ιT ιG R sG zt b B e).hot y := by
  have k : Ledger.Holds (hotAt P.toOwnPar Y ιN) y := by
    unfold hotAt
    exact (ledOf_holds _ y).2 h
  exact k

/-- The part stack: the claim that the batched sumcheck leaves, and the claims on the end values of
the form parts of its two sides. -/
theorem stack_holds
    (h1 : Blocks.Form.val y (upForm (J₂ := J₂) (Cb.Sub.formU P.ip.inn.toSum.T.par
      (fun _ b _ _ => PEmpty.elim b) ((tailF P).b4 e).2)) = 0)
    (h2 : Blocks.Form.val y (rowF P.ip (J₂ := J₂) ((tailF P).b4 e).2 (.inl (.inl ()))) = 0)
    (h3 : Blocks.Form.val y (rowF P.ip (J₂ := J₂) ((tailF P).b4 e).2 (.inr (.inl ()))) = 0) :
    Ledger.Holds (clF P Y ιN ιT ιG R sG zt b B e).stack y := by
  have k : Ledger.Holds (stackLedAt (J₂ := J₂) P.toOwnPar P.wPart e) y := by
    unfold stackLedAt stackLed
    refine (ledOf_holds _ y).2 fun f hf => ?_
    simp only [stackCl, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
  exact k

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.parts_are
#print axioms OnBytes.Road.K4.sq_holds
#print axioms OnBytes.Road.K4.bat_holds
#print axioms OnBytes.Road.K4.led_holds
#print axioms OnBytes.Road.K4.terms_holds
#print axioms OnBytes.Road.K4.gated_holds
#print axioms OnBytes.Road.K4.hot_holds
#print axioms OnBytes.Road.K4.stack_holds
