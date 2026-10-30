-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K06ToyParts.lean: TWO JOINTS FOR K06_law's TOY (Law/K06Toy.lean), general in the seat and the sizes.
  decide_returns      THE CONVERSE OF decide_hears: where given returns, the strict reading of the rounds returns, the hearing returns and uses the rounds up, and the seat's two layings return: the kind's
                      decision goes on, to the record behind the three layings.
  letters_of_lookup   under the tests on the plan and PointsOk: the letters that fromLookup makes are the weights that they are taken for (WeightsOk), zt has lt coordinates, remLow's weights obey the
                      block law: the lines of rowHalf, cut out.
WHAT IT IS NOT. Nothing on soundness. That any of the premises can be met: Law/K06Toy.lean.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.OpenedSent
import Johnson.Desc.Kinds.Law.OpenedAtTruth
import Johnson.Desc.Kinds.Law.HonestCells
import Johnson.Desc.Kinds.Law.K07MemberAt
import Johnson.Desc.Kinds.Law.RowRides

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E okE zeroE oneE)
open OnBytes.Model (Aff Fork World)
open Norm (lt ls d lPd T S2)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Tape (tapeT)

/-- **Where the block's decision goes on**: the converse of decide_hears. -/
theorem decide_returns {S Cl : Type} (cl : Form → Cl) (L : Seat S) (link piece : Nat) (p : Par)
    (s s1 s2 : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (g : Given)
    (t : OnBytes.K.Kc.Tape) (H : HeardAll) (F1 : Fork)
    (hg : given p L s = .ok g)
    (ht : tapeT { rows := fun e => e.name == "BAT-sigma" } rs
      ((p.declare rounds).map (·.entry)) = some t)
    (hh : hear (L.ledger s) rs = some (H, F1, []))
    (e1 : L.setLedger s F1 = .ok s1) (e2 : L.setHeard s1 H = .ok s2) :
    ∃ w, (kind cl L link piece p).decide s rs gs = .ok (L.setWeightClaim s2 w) := by
  have key : decideBy (fun _ => rounds) (fun _ => hear) (fun _ _ => forTheMerge) p L s rs
      = .ok (L.setWeightClaim s2
        ((fun (_ : Given) (_ : Behind) => forTheMerge) g ⟨H.1, H.2.1, H.2.2⟩)) := by
    unfold decideBy
    simp only [hg, ht, hh, e1, e2, named, need, bind, Except.bind, pure, Except.pure,
      List.isEmpty_nil, if_true]
  exact ⟨_, key⟩

/-- The letters that fromLookup makes are the weights that they are taken for (the lines of rowHalf). -/
theorem letters_of_lookup [Sizes] [Policy] [Request] [Token] (sT floor : Nat) (zx : Point)
    (zk : Nat → Point) (hplan : planOk sT = true) (hP : PointsOk floor zx zk) :
    letI := (fromLookup floor zx zk).norm
    letI := (fromLookup floor zx zk).head
    WeightsOk ∧ (FinalNorm.zt).size = lt ∧
      ∀ x, x < d →
        FinalNorm.ew .remLow x = FinalNorm.ewh .remLow (x / S2) * eq FinalNorm.zl (x % S2) := by
  have P := planFacts hplan
  have hV : 0 < V := by have := P.hV2; omega
  have L := Came.fromLookup_law floor zx zk hV (Came.lens_small hplan) hP
  have hdS : S2 ∣ d := Nat.dvd_of_mod_eq_zero P.hdS
  letI : FinalNorm.In := (fromLookup floor zx zk).norm
  letI : In := (fromLookup floor zx zk).head
  have hS2 : ∀ k : Key, S2 ∣ len k := S2_dvd_len P
  exact ⟨⟨fun k x hx => L.block (.inr k) (hS2 k) x hx, fun k => L.wsum (.inr k), L.wx, L.below⟩,
    L.zt, fun x hx => L.block (.inl .remLow) hdS x hx⟩

end VerifiableInference.Desc.Kinds.Head.Law
