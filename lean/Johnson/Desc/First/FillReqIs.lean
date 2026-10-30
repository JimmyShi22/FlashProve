-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/FillReqIs.lean: "THE REQUEST's WORDS IN THE RECORD ARE THE PUBLIC PART's": one
conjunct more of "in order", as a layer of the filling. Small; no Mathlib. A file BESIDE the table
of joints: it turns nothing of it.

Why. The items that speak of the model's relation read the request off what was handed to the chain
(the public part); some kinds' laws conclude at the record's own words (`S.req`, of which the
tokens and the two positions are functions). Nothing in the promise said that the two are one
(Johnson/Desc/First/Borders.lean's head names it as nobody's). It is true of a lawful first record
by its make and tested at the chain's end; that no block writes the field between is each block's
files' to show.

What is said. `reqIsB ws s`: the record's words are ws. `fillReqIs reqW`: the layer: `inOrder` is
CONJOINED with `reqIsB (reqW a.1) a.2`; every other field as it was. reqW: the words of the public
part's request: a letter. `fillReqIs_inOrder` (rfl), `inOrder_req` (what a yes gives),
`reqIsB_first` (at the first record with the words ws laid), `reqIsB_same` (a step that leaves
`S.req` leaves the test).

Limits. (1) reqW is a letter. (2) That each block's yes leaves `S.req` is a fact on its text: not
here. (3) Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open VerifiableInference.Desc OnBytes OnBytes.Model

/-- The record's request's words are these. -/
def reqIsB (ws : Array UInt32) (s : S) : Bool := decide (s.req = ws)

/-- **The layer.** reqW: the words of the public part's request. -/
def fillReqIs {P W : Type} (reqW : P → Array UInt32) (Mg : Meaning P W) : Meaning P W :=
  { Mg with inOrder := fun a => Mg.inOrder a && reqIsB (reqW a.1) a.2 }

theorem fillReqIs_inOrder {P W : Type} (reqW : P → Array UInt32) (Mg : Meaning P W) (a : P × S) :
    (fillReqIs reqW Mg).inOrder a = (Mg.inOrder a && reqIsB (reqW a.1) a.2) := rfl

/-- "In order" at the layer gives the equation, and what was there. -/
theorem inOrder_req {P W : Type} (reqW : P → Array UInt32) (Mg : Meaning P W) (a : P × S)
    (h : (fillReqIs reqW Mg).inOrder a = true) : Mg.inOrder a = true ∧ a.2.req = reqW a.1 := by
  rw [fillReqIs_inOrder, Bool.and_eq_true] at h
  exact ⟨h.1, of_decide_eq_true h.2⟩

/-- At any record with the words ws laid. -/
theorem reqIsB_first (ws : Array UInt32) (s : S) : reqIsB ws (s.withReq ws) = true :=
  decide_eq_true rfl

/-- A step that leaves the words leaves the test. -/
theorem reqIsB_same (ws : Array UInt32) {s s' : S} (h : s'.req = s.req) :
    reqIsB ws s' = reqIsB ws s := by
  unfold reqIsB
  rw [h]

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.inOrder_req
#print axioms VerifiableInference.Desc.First.reqIsB_first
#print axioms VerifiableInference.Desc.First.reqIsB_same
