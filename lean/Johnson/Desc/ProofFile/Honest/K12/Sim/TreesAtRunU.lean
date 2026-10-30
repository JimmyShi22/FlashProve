-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/TreesAtRunU.lean: THE CLAUSE trees of the condition at the
second part's entry (`OnFreeT`, Sim/TreesExact.lean), AT A RUN, at the proximity test on G_u: BY A
LAW. General in the description, the book, the filling, the plan, the place and the state on entry.
The conclusion has the letters of the premise hTrees of `onFreeT_head_U` (OnFreeTAtHeadU.lean) and
`onFreeT_head_U_six` (OnFreeTAtHeadUSix.lean), at the place's own list of first trees.

A conditional: nothing here shows that `ready` or `runC` returns, that the part is called, or that a
filling holds the two sendings' sides.

OF WHAT KIND IT IS. Its premise hb (`bookCutsU`, CutOfBookAt.lean: a test with code on the book's
entries) is a tie between what one part is handed of a run's values and what another part is handed
of them. The statement names no value and states no law over random values: a tie between terms.

The premises, sorted. On the run: hR, hrun, hc, S. On the filling: hgU, hgO: its sides at the two
sendings' places are the lifted sendings' parts. The tie of values: hb. Public at the plan: hpl;
where the test and the two sendings stand (hσ, hcutU, hcutO, hpU, hpO, hinU, hinO, hat); what the
sendings declare (hdU, hdO); the checks hQ, hcf, hfr, hroom, hwU, hwO; the two first trees' sources
(hsrc).

  `depths_U`     clause (a): the job's two trees have the place's declared depths
  `trees_at_run_U`   the statement

The chain, link by link. What the front lists of a tree is the played table's columns at the
positions asked (`tree_of_round_at_run`, Sim/TreeNumberAtRun.lean); the played table is the
sender's, at the sender's stand and own values (`sending_at_run`, Sim/SendersAtRun.lean); its column
is the sending's column (`col_sent`, TableIsColumn.lean); the sender's own values are the cut of its
row of the book's look-up (`own_of_lendPart`, Sim/SenderInFront.lean); the job's tree's column at
the carried values is that same column (`tree0_lent_U`, `tree1_lent_U`, CutOfBookAt.lean), at o_u's
tree by "the same vector" (`same_vector`, Sim/SameVectorAtRun.lean). The shared chain's look-up by
its text: the frame's authors' `look_shared` (Honest/Law/Along.lean).

Limits. The first member carries no vector of its own (`none`): a caller whose job has a letter
there must set it so. Both rounds of each sending lie in front of the test's sub-protocol (hinU,
hinO). The test on G_u alone. Of the walk (`runC`). That hsrc holds under the library's head is
shown nowhere here. It moves no count. Nothing on completeness, soundness or hiding.
The stand is the state that `midSharedAtW` (Honest/MidW.lean) returns. That `runC`'s own walk goes
through that state is not said here.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.SendersAtRun
import Johnson.Desc.ProofFile.Honest.K12.Sim.SenderInFront
import Johnson.Desc.ProofFile.Honest.K12.Sim.TreeNumberAtRun
import Johnson.Desc.ProofFile.Honest.K12.Sim.SameVectorAtRun
import Johnson.Desc.ProofFile.Honest.K12.TableIsColumn
import Johnson.Desc.ProofFile.Honest.K12.CutOfBookAt
import Johnson.Desc.ProofFile.Honest.Thread.PaysLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (Block FileDescription Oracle)
open VerifiableInference.Desc.K12 (P12 T12)
open Johnson.G.OfPlan (rootsOf)
open ProofFile.Honest
open ProofFile.Honest.Small (play_lengths)
open ProofFile.Honest.K14 (SendJob SendPub jobU jobOmega sendingPart sentTables liftSend sendTablesAt
  SendDeclared sendPlace sendingsFit takesOf columnOf Ask)

/-- Clause (a): the job's two trees have the place's declared depths, where the place declares two
first trees. -/
theorem depths_U {W X : Type} (A : SendPub) (p : P12) (door : W → Front X → T12)
    (weights : W → Weights) (rand : W → TableRand) (v? : Option (W → Front X → ℕ → OnBytes.E))
    (h2 : p.nums.first.length = 2) (w : W) (fr : Front X) (mem : ℕ → Stretch)
    (Pz : Johnson.Prover.Link.PS) :
    ((jobAtU A p door weights rand v?).toRun.toTest.trees₀ w fr mem Pz).map (·.1) =
      p.nums.first.map (·.1.a) := by
  rw [trees₀_many]
  obtain ⟨a, b, hab⟩ := List.length_eq_two.1 h2
  show [depthOf p 0, depthOf p 1] = _
  unfold depthOf
  rw [hab]
  rfl

/-- **THE CLAUSE trees, AT A RUN, AT THE TEST ON G_u: BY A LAW.** The premises are sorted in the
file's head. -/
theorem trees_at_run_U {Xi W₀ Rc Ky Tr X₀ Y Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (A : SendPub) (p : P12) (door : Common W₀ Rc Ky → Front X₀ → T12)
    (weights : Common W₀ Rc Ky → Weights) (rand : Common W₀ Rc Ky → TableRand)
    (J : TestJob (Common W₀ Rc Ky) X₀)
    (hJ : J = (jobAtU A p door weights rand none).toRun.toTest) (Js : SimJob Pb)
    (σ : Side F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Pb) (hσ : σ.block.place = p.place)
    (pre' t' : List (Block F.S₂ F.Cl))
    (S : StandsAt F.shared.blocksInOrder R.shared σ (restMember J Js) pre' t' (firstLen J.p.nums.stages))
    (hc : r.called ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩ = true)
    -- the two sendings: where they stand, what the filling holds there, what they declare
    (preU tU preO tO : List (Block F.S₂ F.Cl)) (bU bO : Block F.S₂ F.Cl)
    (hcutU : F.shared.blocksInOrder = preU ++ bU :: tU) (hcutO : F.shared.blocksInOrder = preO ++ bO :: tO)
    (hpU : bU.place = sendPlace 2) (hpO : bO.place = sendPlace 5)
    (hgU : (P.shared.find? fun g => g.place == bU.place) = some ⟨bU.place,
      [(liftSend (askOf A weights rand) (sendingPart (jobU A)) :
        Part Empty (Common W₀ Rc Ky) X₀)]⟩)
    (hgO : (P.shared.find? fun g => g.place == bO.place) = some ⟨bO.place,
      [(liftSend (askOf A weights rand) (sendingPart (jobOmega A)) :
        Part Empty (Common W₀ Rc Ky) X₀)]⟩)
    (hdU : SendDeclared bU (jobU A)) (hdO : SendDeclared bO (jobOmega A))
    (hinU : (preU.flatMap (·.rounds)).length + 2 ≤ (pre'.flatMap (·.rounds)).length)
    (hinO : (preO.flatMap (·.rounds)).length + 2 ≤ (pre'.flatMap (·.rounds)).length)
    -- the tie of values
    (hb : bookCutsU Bk A p = true)
    -- public checks
    (hQ : sendingsFit A.P = true) (hcf : colFitsU A p = true) (hfr : freshFitsU A p = true)
    (hroom : 2 * (stage₀ p).k + 1 ≤ (stage₀ p).h + (stage₀ p).Z.l)
    (hwU : widthFits (jobU A) 0 = true) (hwO : widthFits (jobOmega A) 1 = true)
    (hat : A.atPoint < (preU.flatMap (·.rounds)).length)
    (hsrc : p.nums.first.map (fun o => ProofFile.Honest.srcOf 1 o.2) =
      [(1, rootsOf (preU.flatMap (·.rounds)) + 0), (1, rootsOf (preO.flatMap (·.rounds)) + 1)])
    (st : List (ℕ × ℕ × List UInt64)) :
    ∀ m ca, midSharedAtW F Bk P w₀ rc x k ρ
        ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩ = .ok (some m) →
      carriedAt Bk k 1 ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩
          (restMember (V := Empty) J Js).part = .ok ca →
      (J.trees₀ m.st.input (restFront J m) (stretches _ ca) (rowsAt J (stretches _ ca) m)).map
          (·.1) = p.nums.first.map (·.1.a) ∧
        ∀ (i : ℕ) (o' : Fmt.Shape × Fmt.TreeSource) (Tr' : Tree), p.nums.first[i]? = some o' →
          (J.trees₀ m.st.input (restFront J m) (stretches _ ca)
            (rowsAt J (stretches _ ca) m))[i]? = some Tr' →
          ∃ cols, (r.run.beforeAt st
              ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩).treeCols
                (ProofFile.Honest.srcOf 1 o'.2).1 (ProofFile.Honest.srcOf 1 o'.2).2 = some cols ∧
            ∀ q ∈ cols, q.2 = Tr'.2 q.1 := by
  intro m ca hm hca
  subst hJ
  have hlen2 : p.nums.first.length = 2 := by
    have g := congrArg List.length hsrc
    rw [List.length_map] at g
    exact g
  refine ⟨depths_U A p door weights rand none hlen2 _ _ _ _, ?_⟩
  -- the stand in front of the second part
  obtain ⟨m', hm', -, hheard, -, -, -, -, -, -, -⟩ :=
    frame_at_run hpl hR hrun σ _ pre' t' _ _ S rfl hc st
  obtain rfl : m = m' := Option.some.inj (Except.ok.inj (hm.symm.trans hm'))
  obtain ⟨a₂, zN, m'', ha, hzN, -, hzm, hm''⟩ := played_at_run hpl hR hrun σ _ pre' t' _ _ S rfl hc
  obtain rfl : m = m'' := Option.some.inj (Except.ok.inj (hm.symm.trans hm''))
  have hinp := (walk_mid ha hzN hzm).1
  have hLen : m.st.heard.length = (pre'.flatMap (·.rounds)).length +
      firstLen (jobAtU A p door weights rand none).toRun.toTest.p.nums.stages := by
    rw [hheard, walk_len _ _ _ a₂ zN hzN, List.length_take]
    exact Nat.min_eq_left (Nat.le_trans (Nat.le_add_right _ _) S.fits)
  -- what the second part is lent
  obtain ⟨c, hl, rfl⟩ := exMap_ok (show (lendPart Bk (Bk.rowsOf 1) (k.look 1) ⟨σ.block.place, 1⟩
    (restPart (jobAtU A p door weights rand none).toRun.toTest :
      Part Empty (Common W₀ Rc Ky) X₀)).map (·.2.2) = .ok ca from hca)
  rw [hσ, look_shared] at hl
  -- the two sendings, as played
  obtain ⟨dU₀, dU₁, osU, rU, oU, fU₀, fU₁, -⟩ := hdU.rounds
  obtain ⟨dO₀, dO₁, osO, rO, oO, fO₀, fO₁, -⟩ := hdO.rounds
  obtain ⟨aU, zU, mU, cU, xU₀, xU₁, sU, pU, -, eU, lU, -, -, qU, -, -⟩ :=
    sending_at_run hpl hR hrun σ _ pre' t' _ S hc
    preU bU tU hcutU (jobU A) (askOf A weights rand) hgU dU₀ dU₁ osU (by rw [rU, oU]; rfl) fU₀ fU₁
    (by omega)
  obtain ⟨aO, zO, mO, cO, xO₀, xO₁, sO, pO, -, eO, lO, -, -, qO, -, -⟩ :=
    sending_at_run hpl hR hrun σ _ pre' t' _ S hc
    preO bO tO hcutO (jobOmega A) (askOf A weights rand) hgO dO₀ dO₁ osO (by rw [rO, oO]; rfl)
    fO₀ fO₁ (by omega)
  have hU : (sharedLook Bk k.shared ⟨sendPlace 2, 0⟩).2.cut ⟨0, 0⟩
      (takesOf (jobU A).Q.codes (jobU A).Q.sent (jobU A).sort) = some cU.1.1 := by
    rw [← hpU]
    exact own_of_lendPart (lendRow_cons_ok lU).1
  have hOm : (sharedLook Bk k.shared ⟨sendPlace 5, 0⟩).2.cut ⟨0, 0⟩
      (takesOf (jobOmega A).Q.codes (jobOmega A).Q.sent (jobOmega A).sort) = some cO.1.1 := by
    rw [← hpO]
    exact own_of_lendPart (lendRow_cons_ok lO).1
  -- the two tables
  obtain ⟨TU, hTU, colU⟩ := col_sent (jobU A)
    ((jobU A).rows ⟨askOf A weights rand mU.st.input, mU.st.heard, ()⟩ (coinsE cU.1.1).toArray) 0
    hwU
  obtain ⟨TO, hTO, colO⟩ := col_sent (jobOmega A)
    ((jobOmega A).rows ⟨askOf A weights rand mO.st.input, mO.st.heard, ()⟩
      (coinsE cO.1.1).toArray) 1 hwO
  have fU := tree_of_round_at_run hpl hR hrun σ _ pre' t' _ _ S rfl hc st preU bU tU hcutU
    (by omega) _ qU 0 (some TU) (by
      show ((sendTablesAt (jobU A) cU.1.1 _ _).map some)[0]? = _
      rw [List.getElem?_map]
      exact congrArg (Option.map some) hTU)
  have fO := tree_of_round_at_run hpl hR hrun σ _ pre' t' _ _ S rfl hc st preO bO tO hcutO
    (by omega) _ qO 1 (some TO) (by
      show ((sendTablesAt (jobOmega A) cO.1.1 _ _).map some)[1]? = _
      rw [List.getElem?_map]
      exact congrArg (Option.map some) hTO)
  -- "the same vector"
  have kU := walk_laid_drawn _ _ _ aU zU pU
  rw [start_laid sU, List.map_nil, List.nil_append] at kU
  have hhU := walk_hears _ _ _ _ aU zU (start_hears sU) pU mU eU
  rw [kU] at hhU
  have hv := same_vector A (askOf A weights rand) (jobAtU A p door weights rand none).toRun.toTest
    m mU ρ.shared _ _ hheard (hhU.trans (List.nil_append _))
    ((walk_mid sU pU eU).1.trans hinp.symm) hat (by omega)
  -- the two first trees
  obtain ⟨a, b, hab⟩ := List.length_eq_two.1 hlen2
  rw [hab] at hsrc
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsrc
  obtain ⟨sa, sb⟩ := hsrc
  intro i o' Tr' ho hT
  rw [hab] at ho
  match i, ho, hT with
  | 0, ho, hT =>
    obtain rfl : a = o' := Option.some.inj ho
    rw [sa]
    refine ⟨_, fU, fun q hq => ?_⟩
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hq
    show TU.col y = Tr'.2 y
    have e := tree0_lent_U Bk (Bk.rowsOf 1) (sharedLook Bk k.shared) A p door weights rand none
      cU.1.1 hU cO.1.1 hOm hQ m.st.input _ _ y c hl hb hcf hfr hroom hv
    rw [List.getD_eq_getElem?_getD] at e
    exact (colU y).trans (e.symm.trans
      (congrArg (fun z : Option Tree => (z.getD (0, fun _ => [])).2 y) hT))
  | 1, ho, hT =>
    obtain rfl : b = o' := Option.some.inj ho
    rw [sb]
    refine ⟨_, fO, fun q hq => ?_⟩
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hq
    show TO.col y = Tr'.2 y
    have e := tree1_lent_U Bk (Bk.rowsOf 1) (sharedLook Bk k.shared) A p door weights rand none
      cU.1.1 hU cO.1.1 hOm hQ m.st.input
      (restFront (jobAtU A p door weights rand none).toRun.toTest m)
      ⟨askOf A weights rand mO.st.input, mO.st.heard, ()⟩ y c hl hb hcf hfr
    rw [List.getD_eq_getElem?_getD] at e
    exact (colO y).trans (e.symm.trans
      (congrArg (fun z : Option Tree => (z.getD (0, fun _ => [])).2 y) hT))
  | _ + 2, ho, _ => cases ho

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.depths_U
#print axioms ProofFile.Honest.K12.Light.trees_at_run_U
