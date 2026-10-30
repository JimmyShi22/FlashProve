-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/SumLaw/Counts.lean: THE LAW OF THE MASKED SUMCHECK's HONEST PART:
NUMBERS OF THE CALL, AND THE COINS AT THE STATEMENTS' OWN INDICES: what a caller of the seven
statements of Honest/SumLaw/Statement.lean would else count anew. Statements with their proofs.
  1  The call as it stands in a run has the shape's numbers: `withPoints` keeps every variable's
     number of coefficients, so the sumcheck has as many slots of its own at the one as at the
     other.
  2  THE COINS, at the indices over which the statements' premises on the mask run: for
     i < ownSlots (J.callAt w fr).all, `hidingCoin c i` is the coin number lead + i of the first
     stretch; where the shape has end values, a member of `endRun c` reads as the coin of the
     second.
  3  HOW MANY ROUNDS THE PART SAYS, AS A NUMBER OF THE CALL: the shape's variables and one more
     without end values, and three more with them; as many as the call has entries.
  4 Tools. For a caller with another text of the verifier's sumcheck: a polynomial of a list hangs
     on the members' readings alone. For a caller that holds a lemma on the library's `Chain`
     (More.lean, 6): the challenges and the number of `polyMoves`, WHERE THE CHALLENGES ARE AS MANY
     AS THE VARIABLES.
Main names:
  `withPoints_ds`, `all_ds`, `ownSlots_callAt`: the first. `ownRun_eq`: the definition's own
    equation, for rewriting.
  `hidingCoin_at`, `endCoins_cast`, `endRun_coin`: **the second.**
  `sumGs_count`, `rounds_count`, `entries_count`, `rounds_entries`: **the third.**
  `polyOf_congr`, `polyOf_map`, `polyMoves_chal`, `polyMoves_length`: the fourth.

Limits. Those of Honest/SumLaw/Statement.lean. Nothing on soundness or on any property of a
protocol.
-/
import Johnson.Desc.ProofFile.Honest.SumLaw.More
import Johnson.Desc.ProofFile.Honest.SumLaw.LawEnds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.SumLaw
open OnBytes (E zeroE)
open OnBytes.Model (Reading)
open VerifiableInference.Desc.Part.MaskedSum
open Polynomial

variable {V W X : Type}

/-! ## 1 The call's numbers -/

/-- The run's points change no variable's number of coefficients. -/
theorem withPoints_ds : ∀ (vs : List Var) (zs : List E),
    (withPoints vs zs).map Var.d = vs.map Var.d
  | [], _ => rfl
  | .plain d :: vs, zs => congrArg (d :: ·) (withPoints_ds vs zs)
  | .point _ d :: vs, _ :: zs => congrArg (d :: ·) (withPoints_ds vs zs)
  | .point _ d :: vs, [] => congrArg (d :: ·) (withPoints_ds vs [])

/-- The variables of the call as it stands in a run have the shape's numbers of coefficients. -/
theorem all_ds (J : SumJob W X) (w : W) (fr : Front X) :
    (J.callAt w fr).all.map Var.d = J.shape.all.map Var.d := by
  cases he : J.shape.ends with
  | none =>
    have e : J.shape.all = J.shape.vs := by
      unfold Call.all
      simp only [he]
    rw [all_none J w fr he, e, withPoints_ds]
  | some e =>
    have e' : J.shape.all = J.shape.vs ++ [.point zeroE (e.dY + 1)] := by
      unfold Call.all
      simp only [he]
    rw [all_some J w fr e he, e', List.map_append, List.map_append, withPoints_ds]

/-- **The sumcheck has as many slots of its own at the call in a run as at the shape.** -/
theorem ownSlots_callAt (J : SumJob W X) (w : W) (fr : Front X) :
    ownSlots (J.callAt w fr).all = ownSlots J.shape.all := by
  have e : ∀ l : List Var, (l.map fun v => v.d - 1) = (l.map Var.d).map (· - 1) := by
    intro l
    rw [List.map_map]
    rfl
  rw [ownSlots_one_add, ownSlots_one_add, e, e, all_ds]

/-- The first stretch: the lead's coins, then one for each slot of the sumcheck's own: BY DEFINITION
(`ownRun`, Honest/Sum.lean). -/
theorem ownRun_eq (k : Call) : ownRun k = k.lead + ownSlots k.all := rfl

/-! ## 2 The coins, at the statements' own indices -/

/-- **`hidingCoin c i` is the coin number lead + i of the first stretch**, at every i over which the
statements' premise on the mask runs. -/
theorem hidingCoin_at {name endName : String} {J : SumJob W X} (c : SumCoins name endName J) (w : W)
    (fr : Front X) (i : Nat) (h : i < ownSlots (J.callAt w fr).all) :
    hidingCoin c i = c.2.1.1.e ⟨J.shape.lead + i, by
      rw [ownSlots_callAt] at h
      show J.shape.lead + i < J.shape.lead + ownSlots J.shape.all
      omega⟩ :=
  hidingCoin_coin c i _

/-- The end values' coins, where the end values are known by an equation: the coins are carried
over along the equation; at a shape whose end values are written out this is no step. -/
theorem endCoins_cast (endName : String) (ends : Option Ends) (e : Ends) (he : ends = some e)
    (cs : CsAll (endRuns endName ends)) (j : Nat) (h : j < e.n) :
    Reading.gl.val ((endCoins endName ends cs).getD j zeroE) =
      (he ▸ cs : CsAll (endRuns endName (some e))).1.e ⟨j, h⟩ := by
  subst he
  exact endCoins_coin endName e cs j h

/-- **A member of `endRun c` reads as the coin of the second stretch**, carried over along the
equation on the shape's end values. -/
theorem endRun_coin {name endName : String} {J : SumJob W X} (c : SumCoins name endName J)
    (e : Ends) (he : J.shape.ends = some e) (j : Nat) (h : j < e.n) :
    Reading.gl.val ((endRun c).getD j zeroE) =
      (he ▸ c.2.1.2 : CsAll (endRuns endName (some e))).1.e ⟨j, h⟩ :=
  endCoins_cast endName J.shape.ends e he c.2.1.2 j h

/-! ## 3 How many rounds -/

/-- The part's moves, as a number of the shape. -/
theorem sumGs_count (name endName : String) (J : SumJob W X) :
    (sumGs name endName J).length =
      J.shape.vs.length + (match J.shape.ends with
        | none => 1
        | some _ => 3) := by
  unfold sumGs
  cases J.shape.ends with
  | none =>
    rw [List.length_append, List.length_append, List.length_map, List.length_range]
    show 1 + J.shape.vs.length + 0 = J.shape.vs.length + 1
    omega
  | some e =>
    rw [List.length_append, List.length_append, List.length_map, List.length_range]
    show 1 + J.shape.vs.length + 2 = J.shape.vs.length + 3
    omega

/-- **How many rounds the part says**: the shape's variables and one more, or three more. -/
theorem rounds_count (name endName : String) (J : SumJob W X) (c : SumCoins name endName J)
    (t : State W X) (seen : Seen) (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView)
    (ha : alone (sumPart (V := V) name endName J) c t seen ds = some rounds) :
    rounds.length =
      J.shape.vs.length + (match J.shape.ends with
        | none => 1
        | some _ => 3) := by
  rw [alone_length (sumPart (V := V) name endName J) c t seen ds rounds ha,
    aloneFrom_length (C := SumCoins name endName J) c (sumPart (V := V) name endName J).moves t seen
      ds rounds ha]
  exact (moves_length (V := V) name endName J).trans (sumGs_count name endName J)

/-- The call's entries, counted. -/
theorem entries_count (k : Call) :
    (entries k).length =
      k.vs.length + (match k.ends with
        | none => 1
        | some _ => 3) := by
  unfold entries
  cases k.ends with
  | none =>
    rw [List.length_append, List.length_append, List.length_map]
    show 1 + k.vs.length + 0 = k.vs.length + 1
    omega
  | some e =>
    rw [List.length_append, List.length_append, List.length_map]
    show 1 + k.vs.length + 2 = k.vs.length + 3
    omega

/-- The part says as many rounds as the call, as it stands in the run, has entries. -/
theorem rounds_entries (name endName : String) (J : SumJob W X) (c : SumCoins name endName J)
    (t : State W X) (seen : Seen) (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (w : W)
    (fr : Front X) (ha : alone (sumPart (V := V) name endName J) c t seen ds = some rounds) :
    rounds.length = (entries (J.callAt w fr)).length := by
  rw [rounds_count name endName J c t seen ds rounds ha, entries_count]
  show _ = (withPoints J.shape.vs (J.points w fr)).length + _
  rw [withPoints_length]
  rfl

/-! ## 4 Two tools -/

/-- A polynomial of a list hangs on the members' readings alone. -/
theorem polyOf_congr {K : Type} [Field K] (ρ : Reading K) (a b : List E)
    (h : ∀ i, ρ.val (a.getD i zeroE) = ρ.val (b.getD i zeroE)) : polyOf ρ a = polyOf ρ b := by
  ext i
  rw [polyOf_coeff, polyOf_coeff, h]

/-- The same from lists that are read alike, member by member: the form in which the library's
Johnson/Desc/Part/MaskedSumTie.lean hands and asks it. -/
theorem polyOf_map {K : Type} [Field K] (ρ : Reading K) : ∀ (a b : List E),
    a.map ρ.val = b.map ρ.val → polyOf ρ a = polyOf ρ b
  | [], [], _ => rfl
  | x :: a, y :: b, h => by
    rw [List.map_cons, List.map_cons, List.cons.injEq] at h
    show C (ρ.val x) + X * polyOf ρ a = C (ρ.val y) + X * polyOf ρ b
    rw [h.1, polyOf_map ρ a b h.2]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- The challenges of `polyMoves`, read: where the challenges are as many as the variables (else
`polyMoves` stops at the shorter list). -/
theorem polyMoves_chal {K : Type} [Field K] (ρ : Reading K) (poly : List E → List E) :
    ∀ (vs : List Var) (past rs : List E), vs.length = rs.length →
      (polyMoves ρ vs poly past rs).map (·.2) = rs.map ρ.val
  | [], _, [], _ => rfl
  | v :: vs, past, r :: rs, h => by
    show ρ.val r :: (polyMoves ρ vs poly (past ++ [r]) rs).map (·.2) = ρ.val r :: rs.map ρ.val
    rw [polyMoves_chal ρ poly vs _ rs (by simp only [List.length_cons] at h; omega)]
  | [], _, _ :: _, h => by simp only [List.length_cons, List.length_nil] at h; omega
  | _ :: _, _, [], h => by simp only [List.length_cons, List.length_nil] at h; omega

/-- Their number, under the same premise. -/
theorem polyMoves_length {K : Type} [Field K] (ρ : Reading K) (poly : List E → List E)
    (vs : List Var) (past rs : List E) (h : vs.length = rs.length) :
    (polyMoves ρ vs poly past rs).length = rs.length := by
  have := congrArg List.length (polyMoves_chal ρ poly vs past rs h)
  rw [List.length_map, List.length_map] at this
  exact this

end ProofFile.Honest.SumLaw

#print axioms ProofFile.Honest.SumLaw.withPoints_ds
#print axioms ProofFile.Honest.SumLaw.all_ds
#print axioms ProofFile.Honest.SumLaw.ownSlots_callAt
#print axioms ProofFile.Honest.SumLaw.ownRun_eq
#print axioms ProofFile.Honest.SumLaw.hidingCoin_at
#print axioms ProofFile.Honest.SumLaw.endCoins_cast
#print axioms ProofFile.Honest.SumLaw.endRun_coin
#print axioms ProofFile.Honest.SumLaw.sumGs_count
#print axioms ProofFile.Honest.SumLaw.rounds_count
#print axioms ProofFile.Honest.SumLaw.entries_count
#print axioms ProofFile.Honest.SumLaw.rounds_entries
#print axioms ProofFile.Honest.SumLaw.polyOf_congr
#print axioms ProofFile.Honest.SumLaw.polyOf_map
#print axioms ProofFile.Honest.SumLaw.polyMoves_chal
#print axioms ProofFile.Honest.SumLaw.polyMoves_length
