-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3Base.lean: the kind "lookup" (K3): WHAT THE KIND's ASSEMBLY ASKS BESIDE
THE MEANING: of the public parameters (`K3PlanR`) and of the maker's pieces (`K3Pieces`); with the
numbers and the constants of the fifty places. Definitions and one reading; free of every structure
over the
meaning, so that the kind's assembly and the files on the pieces stand over it.

Main names:
  `k3K l d`: the number of segment l's lookup argument (d: on the digits) in the full size's list
    of places. `k3Const`: what the kind's lot lays there.
  `K3Pieces`: the facts on the maker's pieces
    and on the constants.
  `K3PlanR`: what is asked of the public parameters alone. AGAINST `K3Plan` (K3Means.lean) THREE
    THINGS DIFFER: the field dig; no free prime pp (the law's test comes at `Cb.Gl.p`); what
    the list of rounds sends is `Dl.up` in att's `AttOK` too. THE FIELD dig IS THE VERIFIER's DOOR's
    OWN TEST, BY NAME: `K3Asks.digRow X Dl = true`
    (Johnson/Desc/First/Look/K3Asks.lean: said there, not shown here: no Mathlib, no radius, no free
    prime), and what the list of rounds sends is `Dl.up`. The rule: the field is
    the test that verify() runs, by name: that the door evaluates this row at K3's places is the
    condition of that rule: not shown here. `K3PlanR.digB`: it gives the
    law's test at every radius (`asks_digB`, K3AsksPlan.lean).

Limits: definitions and one reading. Nothing on soundness by itself; nothing on hiding.


-/
import Johnson.P5K3R.SitsAddr
import Johnson.P5K3R.SitsRounds
import Johnson.Desc.First.Look.K3AsksPlan
import Johnson.Desc.First.Look.K3FillWorth
import Johnson.Desc.First.Look.K3HeadStated
import Johnson.Desc.First.Look.K3CallerLayTests
import Johnson.Desc.First.Look.K3AttInst

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open Cb.Fo.Pin
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Pub Part Meaning Numbers openSets pubSets start
  sampledIn shift pubFit)
open VerifiableInference.Desc.Kinds.Head.Law (HeadAdr)

/-- The number of segment l's lookup argument in the full size's list of places. -/
abbrev k3K (l : ℕ) (d : Bool) : ℕ := 14 * l + IM.k3Ix l d + 2

section
variable {P Cells Tok : Type} {Fr : Frame} (X : Verify.Public)
  (codes : Codes) (shape : Params.ReqShape)
  (pieces : List (Piece (ckP .two) Fr (P × Desc.First.S) ProofFile.Cl (Desc.Wit Cells Tok MsgT)))

/-- What the kind's lot lays at segment l's lookup argument: on the digits (d), or on the calls. -/
abbrev k3Const (l : ℕ) (d : Bool) : Option (Desc.Block Desc.First.S ProofFile.Cl) :=
  Desc.K3.theStated K3Lot.ofForm (K3Lot.readersAt X) X codes shape (IM.k3Place l d)

/-- **The facts on the maker's pieces and on the constants.** -/
structure K3Pieces : Prop where
  planOk : ∀ l < 25, ∀ d b', k3Const X codes shape l d = some b' → b'.planOk = true
  back : ∀ l < 25, ∀ d q, pieces[k3K l d]? = some q → q.back = []
  cap : ∀ l < 25, ∀ d q, pieces[k3K l d]? = some q → q.err = Err.cap 128 (uLT (ckP .two) q.ds)
  rounds : ∀ l < 25, ∀ d q, pieces[k3K l d]? = some q → ∀ p, placeAt X l d = some p →
    List.Forall₂ SameAs q.ds p.rounds

end

section
variable [Desc.Kinds.Head.Sizes] [Desc.Kinds.Head.Policy]
variable {Cells Tok : Type} (X : Verify.Public) (Dl : Desc.K3Asks.Sent)
  (L : K3Letters Cells Tok)

local notation "SET" => Params.settingOf X.P.frame

/-- **What is asked of the public parameters alone.** -/
structure K3PlanR (floor : ℕ) : Prop where
  dig : Desc.K3Asks.digRow X Dl = true
  att : ∀ l < 24, l % 2 = 1 →
    ∃ x A tl, attAt X l = some (x, A, tl) ∧ AttOK SET x A tl Dl.up L.rad
  lay : ∀ l < 24, l % 2 = 0 → ∃ x tl, layAt X l = some x ∧ tlAt X l = some tl ∧ LayOK SET x ∧
    (Forest.planeCols x.fs x.lm).toBool = true
  head : ∃ x, Desc.Kinds.Head.Law.headAt X = some x ∧
    Desc.Kinds.Head.Law.headB floor x.fs = true ∧ (Forest.planeCols x.fs x.lm).toBool = true
  head24 : headLink X = 24
  entries : ∀ l < 25, ∀ p, placeAt X l false = some p → p.entries.isSome = true

variable {X Dl L}

/-- **The door's row gives the law's test, at every radius.** -/
theorem K3PlanR.digB {floor : ℕ} (h : K3PlanR X Dl L floor) (rad : OracleShape → ℕ) :
    ∀ l < 25, ∃ x tl, digAt X l = some (x, tl) ∧ digB SET x tl Dl.up rad Cb.Gl.p = true := by
  intro l hl
  have e : Desc.K3Asks.linksOf X = 25 := by
    have h24 := h.head24
    unfold headLink at h24
    unfold Desc.K3Asks.linksOf
    omega
  exact Desc.K3Asks.asks_digB h.dig rad l (by omega)

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.K3PlanR.digB
