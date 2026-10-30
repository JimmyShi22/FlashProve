-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFK9R/TritsOfSums.lean: AT EACH OF THE 25 BUILT SEGMENTS OF THE BLANK GROUND THE NUMBER OF
TRITS THAT THE SMALLNESS TEST's DRAW DECLARES (the sum of the matrices' columns times the number of
combinations) IS THE WRITTEN ONE OF THE SEGMENT's KIND: REDUCED TO TWO SUMS OF COLUMNS. From the
goals' scope, the reading of the files, the return of `ProofFile.pubPlain` and the return of
`ProofFile.blankBy`: no opening of the description. Definitions with code, statements and proofs.

Why. `k8_rounds_at` and `k8_lists_at` (Johnson/AtFull/Rounds/K8.lean: the smallness test's rounds)
have a premise ht : k8TritsB G = true, shown there of no G. 128 · 24086 = 3083008, 128 · 10248 =
1311744, 128 · 20703 = 2649984: so ht is: 128 combinations, and three sums of columns.

THE END OF `trits_of_sums` IS THIS FILE's OWN TEXT, NOT ht: `tritsOf` and `tritsW` are HAND COPIES
of K8.lean's k8TritsOf and k8TritsW (this file does not import K8.lean). That the two tests are one
is rfl by reading; until one line over both files has met Lean
(example : P1K8L.k8TritsB G = (G.built.toList.all fun X => LPFK9.tritsOf X ==
LPFK9.tritsW X.kind) := rfl) nothing shows it.

  `colSum tl`, `tritsOf X`, `tritsW kind`: the sum of the columns; times tau; the written numbers.
  `colSum_head`: **in scope the head's sum is 20703**: the plan's matrices are the written ones
    (`plan_in_scope`, Johnson/Desc/Kinds/Law/HeadPlanWritten.lean); a closed fact.
  `trits_of_sums`: **MAIN.** The "all" runs over 25 members (`IM.ground_gets`), whose kinds are 0,
    1, 2 at 2 g, 2 g + 1, 24 (`IM.ground_named`) and whose structures are the plans'
    (`IM.ground_tails`); 128 combinations at each: `Meaning.Tau.tau_in_scope`
    (Johnson/Goal/Numbers/TauInScope.lean).
Limits. **sL AND sA FIRST: each is "at every plan of the public part the sum of the columns is a
closed number": AN EQUATION THAT CAN BE FALSE: THE TWO PLACES AT WHICH THE MAIN THEOREM COULD BE
IDLE. They are shown of nothing here; at the stored full-size example an evaluation made elsewhere
shows the columns 5990 (three times), 3200, 324, 256, 1536, 400, 400 and 7200, 360, 640, 512, 1536:
evaluated, not proved.** The numerals are sizes of plans: functions of the parameter and layout
files. At the second hash function alone. No soundness statement.

-/
import Johnson.IMR.K8Seat
import Johnson.IMR.PureJoin
import Johnson.Goal.Numbers.TauInScope
import Johnson.Desc.Kinds.Law.HeadPlanWritten
import Johnson.Desc.Ok.PlanWritten.PublicAtLaws
import Johnson.Desc.ProofFile.Law.MakerPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LPFK9
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc.Kinds.Head.Law.InScope (matsW plan_in_scope)

/-- The sum of the matrices' columns. -/
def colSum (tl : HTailF2) : ℕ := (tl.mats.toList.map (·.k)).foldl (· + ·) 0

/-- The number of trits that a built segment's draw declares. -/
def tritsOf (X : LinkH) : ℕ := colSum X.tl * X.tl.tau

/-- The written numbers of trits, by the segment's kind. -/
def tritsW (kind : ℕ) : ℕ :=
  if kind == 2 then 2649984 else if kind == 1 then 1311744 else 3083008

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy}

/-- **The head's sum.** -/
theorem colSum_head {lay : Option ByteArray} {X : Verify.Public}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hX : Verify.publicOf P.pol P.KL lay = .ok X) : colSum X.H.tl = 20703 := by
  unfold colSum
  rw [(plan_in_scope hS hR hX).mats]
  decide +kernel

/-- **THE TEST's YES, FROM THE TWO SUMS.** -/
theorem trits_of_sums {lay : ByteArray} {Z : ProofFile.Pub} {G : ProofFile.Ground}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G)
    (sL : ∀ (g : ℕ) (hp : Layer.HPlan2), Z.p.X.G[g]? = some hp → colSum hp.tl = 24086)
    (sA : ∀ (g : ℕ) (a : Attention.Plan), Z.p.X.A[g]? = some a → colSum a.seam.tl = 10248) :
    (G.built.toList.all fun X => tritsOf X == tritsW X.kind) = true := by
  have hX : Verify.publicOf P.pol P.KL (some lay) = .ok Z.p.X :=
    (VerifiableInference.PlanWritten.publicOfO_older P.pol P.KL (some lay)).symm.trans
      (ProofFile.Law.pub_public hZ)
  have eW : G.W = Z.p.X := ProofFile.Law.blankBy_W hG
  obtain ⟨tL, tA, tH⟩ := Meaning.Tau.tau_in_scope hS hR hX
  obtain ⟨h25, -⟩ := IM.ground_gets hS hR hZ hG
  obtain ⟨nLA, lH, nH, kH, -⟩ := IM.ground_named hS hR hZ hG
  obtain ⟨gLA, lH', gH, eH, -⟩ := IM.ground_tails hS hR hZ hG
  obtain rfl : lH = lH' := Option.some.inj (nH.symm.trans gH)
  rw [List.all_eq_true]
  intro X hXm
  obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hXm
  have hl25 : l < 25 := by
    rw [Array.length_toList, h25] at hl
    exact hl
  have hat : G.built[l]? = some G.built.toList[l] := by
    rw [← Array.getElem?_toList, List.getElem?_eq_getElem hl]
  generalize G.built.toList[l] = X at hat
  rw [beq_iff_eq]
  by_cases h24 : l = 24
  · subst h24
    obtain rfl : X = lH := Option.some.inj (hat.symm.trans nH)
    unfold tritsOf tritsW
    rw [kH, eH, eW, colSum_head hS hR hX, tH]
    rfl
  · obtain ⟨a0, a1, n0, k0, -, -, n1, k1, -⟩ := nLA (l / 2) (by omega)
    obtain ⟨hp, a, b0, b1, hGg, hAg, m0, e0, -, -, -, -, m1, e1, -⟩ := gLA (l / 2) (by omega)
    rw [eW] at hGg hAg
    obtain rfl : a0 = b0 := Option.some.inj (n0.symm.trans m0)
    obtain rfl : a1 = b1 := Option.some.inj (n1.symm.trans m1)
    rcases Nat.mod_two_eq_zero_or_one l with ev | od
    · rw [show 2 * (l / 2) = l by omega] at n0
      obtain rfl : X = a0 := Option.some.inj (hat.symm.trans n0)
      unfold tritsOf tritsW
      rw [k0, e0, sL _ _ hGg, tL _ _ hGg]
      rfl
    · rw [show 2 * (l / 2) + 1 = l by omega] at n1
      obtain rfl : X = a1 := Option.some.inj (hat.symm.trans n1)
      unfold tritsOf tritsW
      rw [k1, e1, sA _ _ hAg, tA _ _ hAg]
      rfl

end LPFK9

#print axioms LPFK9.colSum_head
#print axioms LPFK9.trits_of_sums
