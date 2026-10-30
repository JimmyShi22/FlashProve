-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/RootsBehind.lean: each of the three blocks that stand behind the first chain's
own proximity test (the members' batching; W's commitment with the own group and (Eval); the
chain's end) adds to the record's count of roots just what its declared rounds send. Statements
with their proofs.

  rootsOf_battRounds, rootsOf_atM3   the batching's declared rounds send no root.
  atM3_roots      (atM3 P).decide s rs gs = .ok s' → s'.roots = s.roots + rootsOf (atM3 P).rounds
  trees_eq_lay    a sending's declared number of roots (Par.trees) is the number of trees of its
                  layout (layOf): both read one maker.
  atM4_roots      the like at atM4 P (K1.sendAtS P'): the one block of the three that sends.
  wAt_is, atM4_roots_w   what K1.wAt gives is K1.sendAtS at the numbers of W's place: so the like
                  holds at atM4 P w for that w.
  chainEnd_roots  the like at a chain's end whose carried record is the first chain's.
  under_roots     the sentence passes along Block.UnderR: so it holds of a block as a chain holds
                  it.
No test on the plan is spent: the sentences hold at every P and P'.
rootsOf: Johnson/G/RoundsOfPlan.lean.

What is not claimed. That a chain lays these blocks. Nothing on the trees' numbers or on the book.
Nothing on soundness.

-/
import Johnson.Desc.K13.Law.SeatedM4
import Johnson.Desc.K13.FirstEnd
import Johnson.Desc.Own.TreesAgree
import Johnson.G.RoundsOfPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes
open VerifiableInference.Desc.First (S endAsks)
open Johnson.G.OfPlan (rootsOf)

variable {Cl : Type}

/-! ## 1 The members' batching -/

theorem rootsOf_battRounds (P : Where) : rootsOf (battRounds P) = 0 := by
  unfold rootsOf battRounds
  simp [sigmaEntry, epsEntry, roundEntry]

theorem rootsOf_atM3 (P : Where) : rootsOf (atM3 (Cl := Cl) P).rounds = 0 := by
  show rootsOf (([] ++ battRounds P) ++ []) = 0
  rw [List.append_nil, List.nil_append]
  exact rootsOf_battRounds P

/-- **The members' batching leaves the count of roots, and declares none.** -/
theorem atM3_roots {P : Where} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (atM3 (Cl := Cl) P).decide s rs gs = .ok s') :
    s'.roots = s.roots + rootsOf (atM3 (Cl := Cl) P).rounds := by
  rw [rootsOf_atM3, Nat.add_zero]
  obtain ⟨_, _, _, _, rfl⟩ := atM3_rec h
  rfl

/-! ## 2 W's commitment -/

/-- The declared number of roots is the layout's number of trees. -/
theorem trees_eq_lay (P' : K1.Par) : P'.trees.length = (K1.layOf P').shapes.size := by
  unfold K1.Par.trees K1.layOf
  rw [Own.treesMade_eq]
  cases layTrees P'.codes P'.sent <;> simp

theorem rootsOf_atM4 (P : Where) (P' : K1.Par) :
    rootsOf (atM4 (Cl := Cl) P (K1.sendAtS P')).rounds = (K1.layOf P').shapes.size := by
  show rootsOf (K1.rounds P' ++ []) = _
  rw [List.append_nil, ← trees_eq_lay]
  simp [rootsOf, K1.rounds, K1.seedEntry, K1.answerEntry]

/-- A yes of the sending's decision is a yes on two rounds. -/
theorem sendAtS_two (P' : K1.Par) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (K1.sendAtS P' : Block S Cl).decide s rs gs = .ok s') : ∃ r₁ r₂, rs = [r₁, r₂] := by
  unfold K1.sendAtS at h
  dsimp only at h
  split at h
  · split at h
    · obtain ⟨y, hy, rfl⟩ := (K1.map_ok _ _ _).1 h
      obtain ⟨x, hx, rfl⟩ := (K1.map_ok _ _ _).1 hy
      match rs, hx with
      | [a, b], _ => exact ⟨a, b, rfl⟩
    · cases h
  · cases h

/-- **W's commitment adds just the roots that its rounds declare.** -/
theorem atM4_roots {P : Where} {P' : K1.Par} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (atM4 (Cl := Cl) P (K1.sendAtS P')).decide s rs gs = .ok s') :
    s'.roots = s.roots + rootsOf (atM4 (Cl := Cl) P (K1.sendAtS P')).rounds := by
  rw [rootsOf_atM4]
  have h' : ((K1.sendAtS P' : Block S Cl).decide s (rs.take 2) _).bind (fun m =>
      (rowsB (Cl := Cl) atS P).decide m (rs.drop 2) _) = .ok s' := h
  obtain ⟨s₁, h1, h2⟩ := ebind_ok.1 h'
  obtain ⟨r₁, r₂, e⟩ := sendAtS_two P' h1
  have h3 : (atM4 (Cl := Cl) P (K1.sendAtS P')).decide s [r₁, r₂] gs = .ok s' := by
    show ((K1.sendAtS P' : Block S Cl).decide s [r₁, r₂] _).bind (fun m =>
      (rowsB (Cl := Cl) atS P).decide m [] _) = .ok s'
    rw [← e, h1]
    exact h2
  exact (atM4_seated h3).roots

/-- What K1.wAt gives is K1's sending at the numbers of W's place, at the message that the shape
gives. -/
theorem wAt_is (q : Params.First) (gp : _root_.Desc.Plain.GPar) (piece : Nat) (w : Block S Cl) :
    K1.wAt q gp piece = some w ↔
      ∃ msg, linMessageW q.lin = some msg ∧ w = K1.sendAtS (K1.parW q gp piece msg) := by
  unfold K1.wAt
  rw [Option.map_eq_some_iff]
  exact ⟨fun ⟨m, h, e⟩ => ⟨m, h, e.symm⟩, fun ⟨m, h, e⟩ => ⟨m, h, e.symm⟩⟩

/-- **The like at whatever K1.wAt gives.** -/
theorem atM4_roots_w {P : Where} {q : Params.First} {gp : _root_.Desc.Plain.GPar} {piece : Nat}
    {w : Block S Cl} (hw : K1.wAt q gp piece = some w) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (atM4 (Cl := Cl) P w).decide s rs gs = .ok s') :
    s'.roots = s.roots + rootsOf (atM4 (Cl := Cl) P w).rounds := by
  obtain ⟨msg, _, rfl⟩ := (wAt_is q gp piece w).1 hw
  exact atM4_roots h

/-! ## 3 The chain's end -/

/-- **The chain's end leaves the record, and its sealing round sends no root.** -/
theorem chainEnd_roots (chain piece : Nat) (sealed : Bool) (inFront : List Fmt.DeclaredRound)
    (asks : S → ChainEnd.Clauses) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (ChainEnd.chainEnd (Cl := Cl) chain piece sealed inFront asks).decide s rs gs = .ok s') :
    s'.roots = s.roots +
      rootsOf (ChainEnd.chainEnd (S := S) (Cl := Cl) chain piece sealed inFront asks).rounds := by
  have hr : rootsOf
      (ChainEnd.chainEnd (S := S) (Cl := Cl) chain piece sealed inFront asks).rounds = 0 := by
    cases sealed <;> rfl
  rw [hr, Nat.add_zero]
  have h' : (ChainEnd.refuse (asks s)).map (fun _ => s) = .ok s' := h
  cases hq : ChainEnd.refuse (asks s) with
  | error e => rw [hq] at h'; cases h'
  | ok u => rw [hq] at h'; cases h'; rfl

/-! ## 4 Along UnderR -/

/-- The sentence passes to a block that has the same rounds and says yes only where this one
does. -/
theorem under_roots {c b : Block S Cl} (hc : c.UnderR b)
    (hb : ∀ s s' rs gs, b.decide s rs gs = .ok s' → s'.roots = s.roots + rootsOf b.rounds)
    {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : c.decide s rs gs = .ok s') : s'.roots = s.roots + rootsOf c.rounds := by
  rw [hc.1]
  exact hb s s' rs gs (hc.2 s rs gs s' h)

end VerifiableInference.Desc.K13.Law
