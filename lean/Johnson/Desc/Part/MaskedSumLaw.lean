-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Part/MaskedSumLaw.lean: the part "the masked sumcheck": what the law of kind K5 asks of
the part, as three named statements (each a def of type Prop). Nothing is proved in this file;
Part/MaskedSumTie.lean proves the three.

The field's words are read by a reading (OnBytes/Model/HideLaws.lean: Reading K, a map that takes the
program's 0, 1, sum, difference and product to K's). Each statement speaks of every reading, so no
test "a word is below the prime" is asked: a reading need not be one-to-one.

Main names:
  `PartHearLaw`: the fold is the typed verifier's. The last running claim that hear computes reads as
    the last value of the typed short sumcheck's output (plainOut) on the transcript made of the same
    lists, at all lists of the lengths that readAll asks.
  `PartRowLaw`: the row is the typed row claim. Where row returns at a record that is as hear gives
    it (`AsHeard`), its form is worth 0 in a world exactly if the typed row claim (UHolds) holds of
    that output, under the three equations (D1), (D2), (D4) of the library's plain_row, with the
    part's record in the place of OnBytes/Model's.
  `PartReturns`: the hearing refuses nothing but a shape: shapeOk, the rounds are the call's entries
    (`Fits`), the start form names filled slots alone, the end values' slots are free: then hear
    returns.

Limits. No statement of the three has a refusal of hear as its premise. PartRowLaw stands under (D1),
(D2), (D4), HFixs.OK, "the reading of beta is not 0", AsHeard and "row returns": that they can be met
together at a caller is that caller's to show; nothing in this file shows it. By reading, a part that
says yes to all and hands back a fixed record fails the first statement, and a part that never returns
fails the third.
Sources: the statements name plain records and pure functions of the library alone, no routine that
runs in a context: OnBytes/Model/HideLaws.lean (Reading, World, Aff.value); OnBytes/Tie/Pv/Att/Tr.lean
(plainOut); Cb/Pv/Att/Plain.lean (PlainSc); HFixs.OK, ldPartIni, pDummy, PscPar.UHolds; Hd.place.
Nothing is claimed on soundness (the typed chain's is the library's), completeness or hiding.

-/
import OnBytes.Tie.Pv.Att.RowTie
import Johnson.Desc.Part.MaskedSumShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Part.MaskedSum
open OnBytes OnBytes.Model
open Iop Prob Cb TWhole Johnson.L5.Layers Cb.Pv.Att OnBytes.Tie.Pv.Att

/-- The part's variables for the degrees of a typed plain sumcheck: each summed plainly, with d + 1 coefficients; Y, read at 0, last. -/
def varsOf (degs : List Nat) (DY : Nat) : List Var := degs.map (fun d => Var.plain (d + 1)) ++ [.point zeroE (DY + 1)]

/-- **The fold is the typed verifier's.** -/
def PartHearLaw : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (ρ : Reading K) (T : PlainSc K) (st : T.St) (t mu eps : E)
    (rs : List (List E × E)) (sentY : List E) (beta : E) (hβ : ρ.val beta ≠ 0) (vals : T.A → K),
    (∀ i, 1 ≤ T.deg i) → rs.map (·.1.length) = List.ofFn T.deg → sentY.length = T.DY →
    (plainOut ρ T st t mu eps rs sentY beta hβ vals).fin =
      ρ.val (after (varsOf (List.ofFn T.deg) T.DY) (rs ++ [(sentY, beta)]) (addE mu (mulE eps t)))

/-- The record is as the hearing gives it, of these lists. -/
structure AsHeard (h : Heard) (degs : List Nat) (DY : Nat) (mu : E) (rs : List (List E × E)) (sentY : List E)
    (beta : E) : Prop where
  vars : h.vars = varsOf degs DY
  r : h.r = rs.map (·.2) ++ [beta]
  claim : h.claim = after (varsOf degs DY) (rs ++ [(sentY, beta)]) (addE mu (mulE h.eps h.target))

/-- **The row is the typed row claim.** -/
def PartRowLaw : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (ρ : Reading K) (T : PlainSc K), (∀ i, 1 ≤ T.deg i) →
    (∀ st, HFixs.OK _ (T.fix st)) → ∀ (W : World K) (h : Heard) (rs : List (List E × E)) (sentY : List E) (beta : E)
    (hβ : ρ.val beta ≠ 0) (vals : T.A → K) (mu S0 : E) (st : T.St) (m : T.J → K) (F G : Fork) (f : Aff),
    AsHeard h (List.ofFn T.deg) T.DY mu rs sentY beta →
    rs.map (·.1.length) = List.ofFn T.deg → sentY.length = T.DY →
    row h S0 {} F = some (f, G) →
    T.our.par.W st m = OnBytes.Road.Hd.place W.slot (T.our.par.vars st) h.first →
    T.our.par.inc st m = ρ.val h.target - h.start.value ρ W →
    T.S st (ldPartIni T.nv T.deg (pDummy K T.DY) (plainOut ρ T st h.target mu h.eps rs sentY beta hβ vals).pt)
      (plainOut ρ T st h.target mu h.eps rs sentY beta hβ vals).vals = ρ.val S0 →
    (f.value ρ W = 0 ↔ T.our.par.UHolds (plainOut ρ T st h.target mu h.eps rs sentY beta hβ vals) m)

/-- The n slots from first on are there and free. -/
def Free (F : Fork) (first n : Nat) : Prop :=
  F.gotF.size = F.ns ∧ first + n ≤ F.ns ∧ ∀ j, first ≤ j → j < first + n → F.gotF.getD j true = false

/-- **The hearing refuses nothing but a shape.** -/
def PartReturns : Prop :=
  ∀ (C : Aff) (lead : Nat) (vs : List Var) (e : Ends) (F : Fork) (rs : List Fmt.RoundView),
    shapeOk ⟨lead, vs, some e⟩ = true → Fits (entries ⟨lead, vs, some e⟩) rs → (F.publicPart C).isSome →
    Free F (F.next + ownSlots (vs ++ [.point zeroE (e.dY + 1)])) e.n →
    (hear C ⟨lead, vs, some e⟩ F rs).isSome

end VerifiableInference.Desc.Part.MaskedSum
