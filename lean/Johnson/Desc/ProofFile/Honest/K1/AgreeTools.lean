-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/AgreeTools.lean: THE SHARED "SENDING" (the kind K1) IN THE FRAME
FOR THE HONEST SIDE: FIVE TOOLS ON RowData's CALLS AND ON THE OPENING's FILLING firstFill
(Honest/K1/PlaceFirst.lean), for "agree" at the opening's main rows (Honest/K1/AgreeFirst.lean).
Statements and proofs; no definition.

  asE_inl       asE at an element of the base field is its image in the extension field
  ask_gives_at  where RowData.ask returns, it returns RowData.at_'s value
  at_lays       where at_ answers, the filling lays
  first_at_any  firstFill reads no challenge: at_ is the same at any two lists heard
  first_inl     what firstFill answers is an element of the base field

Limits. The readers R and the filling D are bound variables. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.PlaceFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice OnBytes.Means VerifiableInference.Desc

theorem asE_inl (x : GF) : asE (some (.inl x)) = algebraMap GF GE x := by
  show toE (ofF x, 0, 0) = _
  have h := toE_ofF (ofF x)
  rw [toF_ofF] at h
  exact h

theorem ask_gives_at (D : RowData) (R : Readers) (hd : List Fmt.Drawn) (a : MsgAddr) (r j : Nat)
    (o : Option (GF ⊕ GE)) (h : D.ask R hd a r j = .ok o) : D.at_ R hd a r j = o := by
  unfold RowData.ask at h
  split at h
  · cases h
  · split at h
    · cases h
    · exact Except.ok.inj h

theorem at_lays (D : RowData) (R : Readers) (hd : List Fmt.Drawn) (a : MsgAddr) (r j : Nat)
    (y : GF ⊕ GE) (h : D.at_ R hd a r j = some y) : D.lays a r j = true := by
  unfold RowData.at_ at h
  split at h
  · assumption
  · cases h

theorem first_at_any (S : OnBytes.HonestTrace.Sz) (q : Params.First) (R : Readers)
    (hd hd' : List Fmt.Drawn) (a : MsgAddr) (r j : Nat) :
    (firstFill S q).at_ R hd a r j = (firstFill S q).at_ R hd' a r j := by
  unfold RowData.at_
  rfl

theorem first_inl (S : OnBytes.HonestTrace.Sz) (q : Params.First) (R : Readers)
    (hd : List Fmt.Drawn) (a : MsgAddr) (r j : Nat) (y : GF ⊕ GE)
    (h : (firstFill S q).at_ R hd a r j = some y) : ∃ x, y = .inl x := by
  unfold RowData.at_ at h
  split at h
  · have e := Option.some.inj h
    rw [← e]
    unfold firstFill firstData laidData cellsVals
    dsimp only
    repeat' split
    all_goals exact ⟨_, rfl⟩
  · cases h

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.asE_inl
#print axioms ProofFile.Honest.K1.ask_gives_at
#print axioms ProofFile.Honest.K1.at_lays
#print axioms ProofFile.Honest.K1.first_at_any
#print axioms ProofFile.Honest.K1.first_inl
