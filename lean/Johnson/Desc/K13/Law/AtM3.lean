-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/AtM3.lean: where kind K13's joined block at the first chain's state says yes.
Statements with their proofs.
Main names:
  `frontB_ok`, `battB_ok`, `quietB_ok`: the three blocks, at any lens.
  `rowOfClaim_member`: the claim that is made of a row, read back, is the row.
  `dOf`, `owedOf`: what the lens at the first chain's state hands to the kind.
  `atM3_ok`: where `atM3 P` says yes: the batching's text has answered on the pile; in front the
    rows on the table (`S.rows`) are the pile; behind they are the one row that the text handed on.
Used of `verify-on-bytes`: `memberClaim`, as a pure function.

What is not claimed. What the front and the quiet part test is not told here. A law with a pin that
fixes no more than was committed (Johnson/Desc/K13/Law/Agree.lean) has to spend the front's test on
the pile's form, which `frontB_ok` drops. Nothing on the block behind W's commitment. Nothing on
soundness.

-/
import Johnson.Desc.K13.AtS
import Johnson.Desc.K13.Law.Law

set_option autoImplicit false
set_option relaxedAutoImplicit false
-- one proof serves the lens with and without the arm "between": one alternative stays unused
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S rowOfClaim)

variable {Cl : Type}

/-- A step of a text that answers or refuses, written with `Except.bind`. -/
theorem ebind_ok {α β : Type} {x : Ans α} {f : α → Ans β} {y : β} :
    x.bind f = .ok y ↔ ∃ a, x = .ok a ∧ f a = .ok y := bind_ok

/-- The claim that is made of a row, read back, is the row. -/
theorem rowOfClaim_member (r : TensorRow) : rowOfClaim (memberClaim r) = r := by
  cases r with
  | mk g psi masks target =>
    simp only [rowOfClaim, memberClaim, List.map_map, Function.comp_def, List.map_id']

/-- The statement with the book, as the lens hands it to the kind. -/
def dOf (s : S) : St := { st := s.st, book := s.book, roots := s.roots, opened := [], loc := () }

section AnyLens
variable {T : Type} (X : Lens T) (P : Where)

/-- Where the front says yes, the chain has come to its end. -/
theorem frontB_ok {t t' : T} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (frontB (Cl := Cl) X P).decide t rs gs = .ok t') : X.enter t = some t' := by
  simp only [frontB, still, bind_ok, there_ok, pure_ok, Lens.part] at h
  obtain ⟨t₁, h1, _, _, _, _, rfl⟩ := h
  exact h1

/-- Where the batching's block says yes, the text has answered at the part, and its row is laid as
the claim. -/
theorem battB_ok {t t' : T} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (claimCombinationBlock (Cl := Cl) X P).decide t rs gs = .ok t') :
    ∃ (p : Part) (out : TensorRow × St), X.get? t = some p ∧
      batt p.owed P.lin.kCol P.rows p.pile p.indexMasks p.d rs = .ok out ∧
      t' = X.set t { p with owed := none, lin := some { claim := memberClaim out.1 }, d := out.2 }
    := by
  simp only [claimCombinationBlock, bind_ok, there_ok, need_ok, pure_ok, Lens.part] at h
  obtain ⟨p, hp, _, _, out, ho, rfl⟩ := h
  exact ⟨p, out, hp, ho, rfl⟩

/-- Where the quiet block says yes, it has laid what W's message holds, and nothing else. -/
theorem quietB_ok {t t' : T} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (quietB (Cl := Cl) X P).decide t rs gs = .ok t') :
    ∃ (p : Part) (msg : Array OracleNotice), X.get? t = some p ∧ t' = X.set t { p with msg := msg }
    := by
  simp only [quietB, still, bind_ok, there_ok, need_ok, pure_ok, Lens.part] at h
  obtain ⟨p, hp, _, _, msg, _, rfl⟩ := h
  exact ⟨p, msg, hp, rfl⟩

end AnyLens

/-- The debt of rows, as the lens hands it to the kind. -/
def owedOf (s : S) : Option Nat := if s.noneWaits then none else s.rowsOwed

/-- **Where the joined block says yes**: the chain stood in front of its end; the batching's text
has answered on the pile; behind it the one row is what that text handed on. -/
theorem atM3_ok {P : Where} {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (atM3 (Cl := Cl) P).decide s rs gs = .ok s') :
    ∃ out : TensorRow × St,
      batt (owedOf s) P.lin.kCol P.rows s.out.pending s.out.indexMasks (dOf s)
        (rs.take (2 + P.lin.kCol)) = .ok out ∧
      s.rows = s.out.pending ∧ s'.rows = [out.1] := by
  have h' : (((frontB (Cl := Cl) atS P).decide s ((rs.take (2 + P.lin.kCol)).take 0)
      ((gs.take ((frontB (Cl := Cl) atS P).andThen "the front and the batching"
        (claimCombinationBlock atS P)).openings).take (frontB (Cl := Cl) atS P).openings)).bind fun s₁ =>
      (claimCombinationBlock (Cl := Cl) atS P).decide s₁ ((rs.take (2 + P.lin.kCol)).drop 0)
        ((gs.take ((frontB (Cl := Cl) atS P).andThen "the front and the batching"
          (claimCombinationBlock atS P)).openings).drop (frontB (Cl := Cl) atS P).openings)).bind (fun s₂ =>
                      (quietB (Cl := Cl) atS P).decide s₂ (rs.drop (2 + P.lin.kCol))
                        (gs.drop ((frontB (Cl := Cl) atS P).andThen "the front and the batching"
                          (claimCombinationBlock atS P)).openings)) = .ok s' := by
    have e : ((frontB (Cl := Cl) atS P).andThen "the front and the batching"
        (claimCombinationBlock atS P)).rounds.length = 2 + P.lin.kCol := by
      simp [Block.andThen, frontB, still, claimCombinationBlock, battRounds]
      omega
    rw [← e]
    exact h
  obtain ⟨s₂, h12, h3⟩ := ebind_ok.1 h'
  obtain ⟨s₁, h1, h2⟩ := ebind_ok.1 h12
  have he := frontB_ok atS P h1
  obtain ⟨p, out, hp, hb, rfl⟩ := battB_ok atS P h2
  obtain ⟨p', msg, hp', rfl⟩ := quietB_ok atS P h3
  have hs1 : s₁ = { s with here := .mem { msg := #[], ids := #[], lin := none } } ∧
      s.rows = s.out.pending := by
    cases hs : s.here with
    | fin a =>
      have e1 : atS.enter s = some s.enterMem := by simp only [atS, hs]
      rw [e1] at he
      refine ⟨?_, by simp only [S.rows, hs]⟩
      rw [← Option.some.inj he]
      simp only [S.enterMem, hs]
    | between =>
      first
        | (have e1 : atS.enter s = none := by simp only [atS, hs]
           rw [e1] at he
           cases he)
        | (have e1 : atS.enter s = some s.enterMem := by simp only [atS, hs]
           rw [e1] at he
           refine ⟨?_, by simp only [S.rows, hs]⟩
           rw [← Option.some.inj he]
           simp only [S.enterMem, hs])
    | lay a =>
      have e1 : atS.enter s = none := by simp only [atS, hs]
      rw [e1] at he
      cases he
    | att a =>
      have e1 : atS.enter s = none := by simp only [atS, hs]
      rw [e1] at he
      cases he
    | head a =>
      have e1 : atS.enter s = none := by simp only [atS, hs]
      rw [e1] at he
      cases he
    | mem a =>
      have e1 : atS.enter s = none := by simp only [atS, hs]
      rw [e1] at he
      cases he
  obtain ⟨rfl, hrows⟩ := hs1
  obtain rfl := Option.some.inj hp
  obtain rfl := Option.some.inj hp'
  refine ⟨out, hb, hrows, ?_⟩
  show [rowOfClaim (memberClaim out.1)] = [out.1]
  rw [rowOfClaim_member]

end VerifiableInference.Desc.K13.Law
