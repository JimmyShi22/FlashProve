-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/DebtBoth.lean: THE DEBT ON THE POSITIONS ASKED, AT EVERY LIST
OF CHALLENGES THAT IS DUE, at the second member of a proximity test (the kind K12) on the shared
chain, at the bound `budBoth` (Sim/ExactFirstOwn.lean). Statements and proofs; no definition.

What for. The frame's rule (`owed_of_threads`, Johnson/Desc/ProofFile/Honest/Law/OwedRule.lean)
takes `BudDebts` for a premise: a list's bound at every part, at every list of challenges that the
rounds can draw, at the part's own stretch of it and at the positions that the declared rounds read
of its tables: no input, no coin, no run. What holds at a run (`Lettered.owedAt`) comes out of that
rule.

  `debt_rest`    the text of the field `bud₂` at the member number 1, behind its cut
  `debt_first_earlier`   at number 0 nothing is owed where the fresh table has come earlier

By what. `bud_rest_file`, `trees_rest` (Sim/BudRestAtRun.lean); `first_moves_len`
(FirstPlayAtRun.lean); `members_of_seat` (Sim/ExactSide.lean); `side_is_testSide`
(Sim/BudOwnIsDebt.lean); `planOk_shaped`, `shaped_len` (TreeInFront.lean); `both_rest`,
`first_owes_nothing` (Sim/BudBoth.lean); `budBoth_of_testBud` (Sim/FirstPubOwnAtHead.lean).

Limits.
- THE CUT IS A LETTER HERE. `bud₂` hands its caller an arbitrary cut of the chain at the side's
  sub-protocol; the premises O, hold and ha speak of that cut. Whoever has them at another
  cut must carry them over: by `cut_at_place` (TreeInFront.lean) a plan that passes has one cut at
  a place. That step: `debt_rest_all` (Sim/DebtAtO.lean), not here.
- ALL PREMISES ARE PUBLIC, AND ALL ARE NAMED PREMISES HERE. At the test on G_omega the head pays
  hplan, hzip, hc, hst, hk, hT, hen (Sim/DebtAtO.lean). Who could pay O, hold, ha there, and any of
  them at G_u, has not been sought.
- The shared chain alone (the tests on G_u and G_omega). The first and the last chain's tests lie
  under the fields `bud₁` and `bud₃`: no twin is typed.
- The bound at number 1 is the containment `budOpened` (Sim/ExactPlan.lean). That it gives the count
  `budRest` (Sim/Row.lean): `rest_of_opened` (Sim/BudCount.lean), not here.
- `BudDebts` itself is concluded by no theorem here: at one row, `budDebts_one_row_both`
  (Sim/DebtAtO.lean).
- Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.BudBoth
import Johnson.Desc.ProofFile.Honest.K12.Sim.BudRestAtRun
import Johnson.Desc.ProofFile.Honest.K12.FirstPlayAtRun
import Johnson.Desc.ProofFile.Honest.K12.Sim.ExactSide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (FileDescription Block)
open H2K.Pub (sgOf)
open Johnson.G.OfPlan (rootsOf)

/-- **The text of `BudDebts.bud₂` at the second member of a proximity test on the shared chain, at
the bound `budBoth`**: at every list of challenges that is due; no input, no coin, no run. General
in the description. The premises are those of `bud_rest_file`, all public, at sent := the trees in
front of the sub-protocol; hplan; hzip and hc, so that the seated side's second member is
`restMember J Js`. -/
theorem debt_rest {Xi V W X Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    (L : Lettered Bk F.S₂ F.Cl V W X Pb) (J : TestJob W X) (Js : SimJob Pb)
    (hpl : L.place = J.p.place) (hrow : L.row = testPairs J Js) (hbud : L.bud = budBoth Js)
    (hp : Js.p = J.p) (hplan : F.planOk = true) (σ : Side F.S₂ F.Cl V W X Pb)
    (hσ : L.side F.shared.blocksInOrder = some σ) (pre t : List (Block F.S₂ F.Cl))
    (hcut : F.shared.blocksInOrder = pre ++ σ.block :: t)
    (hzip : σ.block.rounds.zip σ.block.oracles = J.laid)
    (hc : (H2K.JointK.laidOf J.p).length = firstLen J.p.nums.stages + restLen J.p.nums.stages)
    (depths : List ℕ) (src₀ : ℕ → Fmt.TreeSource)
    (O : OpensFit J σ.block.rounds depths src₀ (rootsOf (pre.flatMap (·.rounds))))
    (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = s :: next :: rest) (hk : s.k = (sgOf s).h + (sgOf s).g)
    (hT : tablesFitB J = true)
    (hold : ∀ k, k < depths.length → ∀ n, ProofFile.Honest.srcOf 1 (src₀ k) = (1, n) →
      n < rootsOf (pre.flatMap (·.rounds)))
    (hen : firstLen J.p.nums.stages ≤ J.laid.length)
    (ha : ∀ i, (depthAt J (firstLen J.p.nums.stages + i)).isSome = true →
      aloneB F pre t (rootsOf (pre.flatMap (·.rounds)) +
        sentBefore J (firstLen J.p.nums.stages + i)) = true) :
    ∀ u ∈ σ.members, u.number = 1 → ∀ n,
      n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number → ∀ ρ : Draws, ρ.due F = true →
      L.bud u.number ((ρ.shared.drop n).take u.rounds.length)
        (asksFrom (treeAsks F ρ 1) (u.rounds.map (·.2.length))
          (((rowsOfChain F.shared.blocksInOrder).take n).map (·.2.length)).sum) := by
  intro u hu h1 n hn ρ hρ
  have hσ' : testSide F.shared.blocksInOrder J Js [] = some σ :=
    (side_is_testSide L J Js hpl hrow _).symm.trans hσ
  have hm : σ.members = [firstMember J Js, restMember J Js] :=
    members_of_seat _ J Js [] σ hσ' hzip s next rest hst hc
  rw [hm] at hu
  have hu' : u = restMember J Js := by
    rcases List.mem_cons.1 hu with rfl | hu2
    · exact absurd h1 Nat.zero_ne_one
    · rcases List.mem_cons.1 hu2 with rfl | hu3
      · rfl
      · cases hu3
  subst hu'
  have hrow' : σ.row = testPairs J Js := by
    unfold testSide Side.seated at hσ'
    obtain ⟨b, -, rfl⟩ := Option.map_eq_some_iff.1 hσ'
    rfl
  have hr : σ.roundsTo 1 = firstLen J.p.nums.stages := by
    unfold Side.roundsTo
    rw [hrow']
    show (firstPart J : Part V W X).moves.length + 0 = firstLen J.p.nums.stages
    rw [Nat.add_zero, first_moves_len]
  have hn' : n = (pre.flatMap (·.rounds)).length + firstLen J.p.nums.stages := by
    rw [hn]
    show _ + σ.roundsTo 1 = _
    rw [hr]
  subst hn'
  have hshb : σ.block.shaped = true := planOk_shaped hplan σ.block
    (by rw [hcut]; exact List.mem_append_right _ List.mem_cons_self)
  have hlen : σ.block.rounds.length = J.laid.length := by
    rw [← hzip, List.length_zip, shaped_len σ.block hshb, Nat.min_self]
  have hN := trees_rest J pre t σ.block
    (fun x hx => planOk_shaped hplan x (by rw [hcut]; exact List.mem_append_left _ hx)) hzip hT hen
  rw [← hcut] at hN
  rw [hbud]
  refine (both_rest Js _ _).2 ?_
  rw [hp, hN]
  exact bud_rest_file (V := V) J Js pre t σ.block hcut depths src₀ _ O s next rest hst hk hT
    hold hlen hen ρ hρ ha

/-- **At the first member, where the fresh table has come earlier**: nothing is owed. The challenges
and the positions are letters. -/
theorem debt_first_earlier {Xi V W X Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    (L : Lettered Bk F.S₂ F.Cl V W X Pb) (Js : SimJob Pb) (hbud : L.bud = budBoth Js)
    (ho : Js.own = false) (n : ℕ) (hn : n = 0) (ds : List Fmt.Drawn)
    (asks : List (List (List ℕ))) : L.bud n ds asks := by
  subst hn
  rw [hbud]
  exact budBoth_of_testBud Js ds asks (first_owes_nothing Js ho ds asks)

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.debt_rest
#print axioms ProofFile.Honest.K12.Light.debt_first_earlier
