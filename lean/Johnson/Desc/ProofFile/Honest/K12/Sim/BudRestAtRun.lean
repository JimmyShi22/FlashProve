-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/BudRestAtRun.lean: the fourth of the six hypotheses of the
frame's sentence on a member (`ExactMember`, Johnson/Desc/ProofFile/Honest/Small/Field.lean), at the
SECOND member of a proximity test on the shared chain, with `budOpened` (Sim/ExactPlan.lean) for the
letter bud: as a conclusion at one run of the frame's `runC`
(Johnson/Desc/ProofFile/Honest/Walk.lean), at the run's own challenges and positions. General in the
description. It imports Mathlib.

`budOpened` says: the positions asked of a tree that the part sends are among those that the next
reading round samples. Sim/BudOwn.lean has it where "the positions read of a tree" are those that
the test's own declared rounds read, and names what lacks: that no round outside the test reads such
a tree. Here that is one public premise, the test with code `aloneB` (ReadsInBlock.lean).

  `bud_sub`      `budOpened` at the list that `asksFrom` makes of one function goes over to a
                 function that lists no more
  `bud_rest_file`   `budOpened` at the frame's own list `asksFrom (treeAsks F ρ 1) …`, at the second
                 part's own stretch of a list of challenges that passes `Draws.due`
  `trees_rest`   the trees that the shared chain states in front of the second member: those in
                 front of the sub-protocol, and those that the first member's rounds send
  `bud_rest_at_run`   the same at `r.run.drawnAt` and `r.run.askedAt`

The premises of `bud_rest_at_run`, sorted.
- Public, on the description and the place: `F.planOk`; the sub-protocol's declared rounds and
  oracle messages are the test's (hzip); `OpensFit` (ColsTerm.lean); two stages or more and k = h +
  g at the first; `tablesFitB`; the trees in front have smaller numbers (hold); the first member's
  rounds are among the test's (hen); `aloneB` at each tree that the second part sends (ha).
- Public, on the challenges: `ρ.due`.
- On the filling and the book: `ready` has returned; `StandsAt`
  (Johnson/Desc/ProofFile/Honest/Law/OwedParts.lean) at the second member.
- On the run: `runC` has returned. That the part was called is not asked.

By what. `bud_own_rest`, `sent_sum`, `roots_fit` (Sim/BudOwn.lean), `bud_of_asksFrom`,
`asksFrom_at` (Sim/BudRun.lean), `asks_in_block` (ReadsInBlock.lean), `rows_len`, `rows_sum`,
`told_len`, `planOk_shaped`, `shaped_len` (TreeInFront.lean); `stretch_back`
(Law/OwedParts.lean), `at_shared`, `drawnAt_of`, `askedAt_of`, `runC_asks` (Law/RunAtFile.lean),
`steps_pairs` (Law/StratRun.lean), `steps_shaped`, `drawsFit_length` (Law/Along.lean), `ready_ok`
(Law/Run.lean).

Limits. Positions alone. `aloneB` and `OpensFit` are premises: they are shown of no description
here. Of each round root number 0 alone is bound, as in `budOpened`. A conditional on "`ready` and
`runC` have returned". The shared chain alone. One list of challenges: one request. Nothing on
completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.BudOwn
import Johnson.Desc.ProofFile.Honest.K12.ReadsInBlock
import Johnson.Desc.ProofFile.Honest.K12.TreeInFront
import Johnson.Desc.ProofFile.Honest.Law.OwedParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (FileDescription Block)
open H2K.Pub (sgOf)
open Johnson.G.OfPlan (rootsOf)

/-- `budOpened` goes over to a function that lists no more. -/
theorem bud_sub (stages : List Fmt.M1.Stage) (ds : List Fmt.Drawn) (T T' : ℕ → List ℕ)
    (roots : List ℕ) (n : ℕ) (hB : budOpened stages 1 ds (asksFrom T' roots n))
    (hsub : ∀ i, 0 < roots.getD i 0 → ∀ q ∈ T (n + (roots.take i).sum),
      q ∈ T' (n + (roots.take i).sum)) : budOpened stages 1 ds (asksFrom T roots n) :=
  bud_of_asksFrom stages ds T roots n fun i hi q hq =>
    hB rfl i q (by rw [asksFrom_at, if_pos hi]; exact hsub i hi q hq)

/-- **`budOpened` at the frame's own list, where the test's sub-protocol alone opens the trees that
the second part sends.** b: the sub-protocol. sent: how many trees the chain states in front. -/
theorem bud_rest_file {Xi V W X Pb : Type} {F : FileDescription Xi} (J : TestJob W X) (Js : SimJob Pb)
    (pre t : List (Block F.S₂ F.Cl)) (b : Block F.S₂ F.Cl)
    (hcut : F.shared.blocksInOrder = pre ++ b :: t) (depths : List ℕ) (src₀ : ℕ → Fmt.TreeSource) (sent : ℕ)
    (O : OpensFit J b.rounds depths src₀ sent) (s next : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: next :: rest)
    (hk : s.k = (sgOf s).h + (sgOf s).g) (hT : tablesFitB J = true)
    (hold : ∀ k, k < depths.length → ∀ n, srcOf 1 (src₀ k) = (1, n) → n < sent)
    (hlen : b.rounds.length = J.laid.length)
    (hen : firstLen J.p.nums.stages ≤ J.laid.length) (ρ : Draws) (hρ : ρ.due F = true)
    (ha : ∀ i, (depthAt J (firstLen J.p.nums.stages + i)).isSome = true →
      aloneB F pre t (sent + sentBefore J (firstLen J.p.nums.stages + i)) = true) :
    budOpened J.p.nums.stages 1
      ((ρ.shared.drop ((pre.flatMap (·.rounds)).length + firstLen J.p.nums.stages)).take
        (restMember (V := V) J Js).rounds.length)
      (asksFrom (treeAsks F ρ 1) ((restMember (V := V) J Js).rounds.map (·.2.length))
        (sent + sentBefore J (firstLen J.p.nums.stages))) := by
  have hρ' := hρ
  unfold Draws.due at hρ'
  simp only [Bool.and_eq_true] at hρ'
  have h2 : drawsFit (F.shared.blocksInOrder.flatMap (·.rounds)) ρ.shared = true := hρ'.1.1.2
  have htot := ProofFile.Honest.drawsFit_length _ _ h2
  rw [hcut, List.flatMap_append, List.flatMap_cons, List.length_append, List.length_append]
    at htot
  have hrl : (restMember (V := V) J Js).rounds.length =
      b.rounds.length - firstLen J.p.nums.stages := by
    show (J.laid.drop (firstLen J.p.nums.stages)).length = _
    rw [List.length_drop, hlen]
  -- the sub-protocol's stretch, cut at the first member's end
  have hds : (ρ.shared.drop ((pre.flatMap (·.rounds)).length + firstLen J.p.nums.stages)).take
      (restMember (V := V) J Js).rounds.length =
      (((ρ.shared.drop (pre.flatMap (·.rounds)).length).take b.rounds.length).drop
        (firstLen J.p.nums.stages)) := by
    rw [List.drop_take, List.drop_drop, hrl]
  have h1 : (((ρ.shared.drop (pre.flatMap (·.rounds)).length).take b.rounds.length).take
      (firstLen J.p.nums.stages)).length = firstLen J.p.nums.stages := by
    rw [List.length_take, List.length_take, List.length_drop]
    omega
  rw [hds]
  refine bud_sub _ _ _ _ _ _ (bud_own_rest (V := V) J Js b.rounds depths src₀ sent 1 0 O s next
    rest hst hk hT hold (fun _ _ => none) (fun _ => none) _ _ h1) fun i hi q hq => ?_
  rw [List.take_append_drop]
  have hil : i < ((restMember (V := V) J Js).rounds.map (·.2.length)).length := by
    by_contra hc
    rw [List.getD_eq_default _ _ (by omega)] at hi
    omega
  have hroots : ∀ i, i < ((restMember (V := V) J Js).rounds.map (·.2.length)).length →
      ((restMember (V := V) J Js).rounds.map (·.2.length)).getD i 0 =
        if (depthAt J (firstLen J.p.nums.stages + i)).isSome = true then 1 else 0 :=
    fun i hi => roots_fit J hT _ i hi
  have hsome : (depthAt J (firstLen J.p.nums.stages + i)).isSome = true := by
    have h := hroots i hil
    by_contra hc
    rw [if_neg hc] at h
    omega
  rw [Nat.add_assoc, sent_sum J _ _ hroots i (Nat.le_of_lt hil)] at hq ⊢
  exact asks_in_block pre t b hcut ρ hρ _ (ha i hsome) q hq

/-- The trees that the shared chain states in front of the second member. -/
theorem trees_rest {S Cl W X : Type} (J : TestJob W X) (pre t : List (Block S Cl))
    (b : Block S Cl) (hsh : ∀ x ∈ pre, x.shaped = true)
    (hzip : b.rounds.zip b.oracles = J.laid) (hT : tablesFitB J = true)
    (hen : firstLen J.p.nums.stages ≤ J.laid.length) :
    (((rowsOfChain (pre ++ b :: t)).take
      ((pre.flatMap (·.rounds)).length + firstLen J.p.nums.stages)).map (·.2.length)).sum =
      rootsOf (pre.flatMap (·.rounds)) + sentBefore J (firstLen J.p.nums.stages) := by
  have e : rowsOfChain (pre ++ b :: t) = rowsOfChain pre ++ (J.laid ++ rowsOfChain t) := by
    unfold rowsOfChain
    rw [List.flatMap_append, List.flatMap_cons, hzip]
  rw [e, ← rows_len pre hsh, List.take_append, List.take_of_length_le (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left, List.map_append, List.sum_append, rows_sum pre hsh, told_len pre hsh,
    List.take_append_of_le_length hen]
  congr 1
  have hroots : ∀ i, i < ((J.laid.drop 0).map (·.2.length)).length →
      ((J.laid.drop 0).map (·.2.length)).getD i 0 =
        if (depthAt J (0 + i)).isSome = true then 1 else 0 := fun i hi => roots_fit J hT 0 i hi
  have h := sent_sum J 0 _ hroots (firstLen J.p.nums.stages)
    (by rw [List.length_map, List.drop_zero]; exact hen)
  rw [List.drop_zero, Nat.zero_add, ← List.map_take] at h
  have h0 : sentBefore J 0 = 0 := rfl
  rw [h0, Nat.zero_add] at h
  exact h

/-- **`budOpened` at one run's own challenges and positions, at the second member.** -/
theorem bud_rest_at_run {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true) (hρ : ρ.due F = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (J : TestJob (Common W₀ Rc Ky) X₀) (Js : SimJob Pb)
    (σ : Side F.S₂ F.Cl V (Common W₀ Rc Ky) X₀ Pb) (pre t : List (Block F.S₂ F.Cl))
    (S : StandsAt F.shared.blocksInOrder R.shared σ (restMember J Js) pre t (firstLen J.p.nums.stages))
    (hzip : σ.block.rounds.zip σ.block.oracles = J.laid) (depths : List ℕ)
    (src₀ : ℕ → Fmt.TreeSource)
    (O : OpensFit J σ.block.rounds depths src₀ (rootsOf (pre.flatMap (·.rounds))))
    (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = s :: next :: rest) (hk : s.k = (sgOf s).h + (sgOf s).g)
    (hT : tablesFitB J = true)
    (hold : ∀ k, k < depths.length → ∀ n, srcOf 1 (src₀ k) = (1, n) →
      n < rootsOf (pre.flatMap (·.rounds)))
    (hen : firstLen J.p.nums.stages ≤ J.laid.length)
    (ha : ∀ i, (depthAt J (firstLen J.p.nums.stages + i)).isSome = true →
      aloneB F pre t (rootsOf (pre.flatMap (·.rounds)) +
        sentBefore J (firstLen J.p.nums.stages + i)) = true) :
    budOpened J.p.nums.stages 1 (r.run.drawnAt ⟨σ.block.place, 1⟩)
      (r.run.askedAt ⟨σ.block.place, 1⟩) := by
  have Q := (F.planOk_ok).1 hpl
  have hp := Q.places
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  have o₁ := steps_shaped s1 Q.blocks₁
  have o₂ := steps_shaped s2 Q.blocks₂
  have o₃ := steps_shaped s3 Q.blocks₃
  have hcut : F.shared.blocksInOrder = pre ++ σ.block :: t := S.cut
  have hstr : InStretch R.shared ⟨σ.block.place, 1⟩
      ((pre.flatMap (·.rounds)).length + firstLen J.p.nums.stages)
      (restMember (V := V) J Js).rounds.length := S.str
  obtain ⟨ha', -, -, -⟩ := stretch_back hstr S.pos S.fits
  have hA := at_shared hrun hR o₁ o₂ o₃ hp ha'
  have e1 : ((R.shared.drop ((pre.flatMap (·.rounds)).length + firstLen J.p.nums.stages)).take
      (restMember (V := V) J Js).rounds.length).map (·.oracles.length) =
      (restMember (V := V) J Js).rounds.map (·.2.length) := by
    have g := congrArg (List.map (·.2.length)) S.own
    rw [List.map_map] at g
    exact g
  have e2 : (R.shared.take ((pre.flatMap (·.rounds)).length + firstLen J.p.nums.stages)).map
      (·.oracles.length) = ((rowsOfChain F.shared.blocksInOrder).take
        ((pre.flatMap (·.rounds)).length + firstLen J.p.nums.stages)).map (·.2.length) := by
    rw [← steps_pairs s2, ← List.map_take, List.map_map]
    rfl
  have hshb : σ.block.shaped = true := planOk_shaped hpl σ.block
    (by rw [hcut]; exact List.mem_append_right _ List.mem_cons_self)
  have hlen : σ.block.rounds.length = J.laid.length := by
    rw [← hzip, List.length_zip, shaped_len σ.block hshb, Nat.min_self]
  have hN := trees_rest J pre t σ.block
    (fun x hx => planOk_shaped hpl x (by rw [hcut]; exact List.mem_append_left _ hx)) hzip hT hen
  rw [← hcut] at hN
  rw [drawnAt_of hA hstr,
    askedAt_of hA hstr (treeAsks F ρ 1) (runC_asks hrun hR o₁ o₂ o₃ 1), e1, e2, hN]
  exact bud_rest_file (V := V) J Js pre t σ.block hcut depths src₀ _ O s next rest hst hk hT
    hold hlen hen ρ hρ ha

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.bud_sub
#print axioms ProofFile.Honest.K12.Light.bud_rest_file
#print axioms ProofFile.Honest.K12.Light.trees_rest
#print axioms ProofFile.Honest.K12.Light.bud_rest_at_run
