-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Held.lean: the kind's written counts are shares of at most 2^-k of their
rounds' challenges, from a
Boolean test on the rounds' entries and kinds.

Main names:
  `rowOk`, `heldTN_of_rows`: the two comparisons of HeldTN (Att/K05Bears.lean) at one round, with
    the number of hash
    blocks written out (the library's planDraws_law).
  `pick`, `k5Held`: the test: the typed count is errOf (Att/K05Rounds.lean); the share that is
    tried: at the draw of the
    point "as many as coordinates" over the field's size; elsewhere the count over the number of the
      round's typed values.
  `held_of_check`: a yes of the test on the written rounds' own entries and kinds gives HeldTN.
  `kindAt`: the kind that an evaluation may take at an entry. `zOf`, `eZ_eq`: the count at the draw
    of the point in
    numbers is the letters' count, where 4 variables number a bit and the record is the letters'.

Limits: the test is run nowhere in this file. That a file's written rounds have the kinds of kindAt
is not shown.
Sources: Att/K05Bears.lean; Att/K05Rounds.lean; Att/K05Condition.lean; Run/PlanDraws.lean;
OnBytes/Slice/RatesToy.lean.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Bears
import Johnson.Desc.First.Att.K05Rounds
import Johnson.Desc.First.Att.K05Condition
import OnBytes.Slice.RatesToy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Maker Run Fo.Peel Cb.Pv.Att
open scoped ENNReal

/-- The two comparisons at one round. -/
def rowOk (k e : ℕ) (en : Fmt.Entry) (kd : Fmt.Kind) (n D : ℕ) : Bool :=
  Decidable.decide (en.logN ≤ 64) && Decidable.decide (0 < D) &&
    Decidable.decide (e * D ≤ n * nVals (Fmt.dsOf en kd)) &&
    Decidable.decide ((2 ^ 128 + 1) ^ Fmt.blocksFor (Fmt.wordsAtMost en kd) * n * 2 ^ k ≤
      (2 ^ 128) ^ Fmt.blocksFor (Fmt.wordsAtMost en kd) * D * 2 ^ en.work)

theorem heldTN_of_rows {k : ℕ} : ∀ (ds : List RDT) (s' : Shape) (ε : Err s'),
    List.Forall₂ (fun e (d : RDT) => ∃ n D, rowOk k e d.entry d.kind n D = true) (errList ε) ds → HeldTN k ds s' ε
  | [], _, _, _ => trivial
  | d :: ds, _ :: s', ε, h => by
    rcases (show List.Forall₂ _ (ε.1 :: errList ε.2) (d :: ds) from h) with _ | ⟨⟨n, D, h1⟩, h2⟩
    simp only [rowOk, Bool.and_eq_true, decide_eq_true_eq] at h1
    obtain ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩ := h1
    refine ⟨⟨a1, n, D, a2, a3, ?_⟩, heldTN_of_rows ds s' ε.2 h2⟩
    rw [(planDraws_law .two d.entry d.kind a1).2]
    exact a4
  | _ :: _, [], _, h => by cases h

/-- The share that is tried. -/
def pick (e : ℕ) (en : Fmt.Entry) (kd : Fmt.Kind) : ℕ × ℕ :=
  if en.name = "ZERO" then (en.drawE, Fmt.Fld.two.p ^ 3) else (e, nVals (Fmt.dsOf en kd))

/-- The test. -/
def k5Held (k z : ℕ) (rs : List (Fmt.Entry × Fmt.Kind)) : Bool :=
  rs.all fun r => rowOk k (errOf z r.1) r.1 r.2 (pick (errOf z r.1) r.1 r.2).1 (pick (errOf z r.1) r.1 r.2).2

theorem held_of_check {M X : Type} (A : AttOwn GE M X) (Ex : ExtSpec) (k : ℕ) (ds : List RDT)
    (he : errList (A.ch.eps Ex) = (ds.map (·.entry)).map (errOf A.tail.eZ))
    (hc : k5Held k A.tail.eZ (ds.map fun d => (d.entry, d.kind)) = true) : HeldTN k ds _ (A.ch.eps Ex) := by
  refine heldTN_of_rows ds _ _ ?_
  rw [he, List.map_map, List.forall₂_map_left_iff]
  refine List.forall₂_same.2 fun d hd => ?_
  have := List.all_eq_true.1 hc (d.entry, d.kind) (List.mem_map.2 ⟨d, hd, rfl⟩)
  exact ⟨_, _, this⟩

/-- The kind that is taken at an entry. -/
def kindAt (e : Fmt.Entry) : Fmt.Kind := if e.drawE = 0 then .nothing else .elems

/-- The count at the draw of the point, as the library's letters have it, in numbers. -/
def zOf (x : Params.AttentionRounds) : ℕ :=
  (2 * x.lgk + 2 * x.lt + 4) * (Fmt.Fld.two.p ^ 3) ^ (2 * x.lgk + 2 * x.lt + 4 - 1)

/-- It is the letters' count, where 4 variables number a bit and the record is the letters'. -/
theorem eZ_eq {M X : Type} (P : OwnPar GE M X) (Mn : Means GE P.D P.C P.kap) (hk : P.kap = 4) (rows : ℕ) :
    (P.own Mn).tail.eZ = zOf (OnBytes.Tie.Pv.Att.recOf P rows) := by
  show (P.D.lg + P.D.lT + (P.kap + P.D.lg + P.D.lT)) * Fintype.card GE ^ (P.D.lg + P.D.lT + (P.kap + P.D.lg + P.D.lT) - 1) =
    (2 * P.D.lg + 2 * P.D.lT + 4) * (Fmt.Fld.two.p ^ 3) ^ (2 * P.D.lg + 2 * P.D.lT + 4 - 1)
  rw [card_GE, hk, show P.D.lg + P.D.lT + (4 + P.D.lg + P.D.lT) = 2 * P.D.lg + 2 * P.D.lT + 4 by omega]


end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.eZ_eq
#print axioms VerifiableInference.Desc.First.Att.P.held_of_check
