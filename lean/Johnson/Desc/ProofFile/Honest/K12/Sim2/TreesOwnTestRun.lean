-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the clause trees at the request's own test, at a run.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/TreesOwnTestRun.lean: the clause trees of OnFreeTD at a called
part of the last chain, at a job of three members: the index-mask message's tree and W's, sent in the
first chain, and Omega's, sent in the shared chain.

  first_round_at_shared, sending_tree_in_front   a sending of the shared chain, seen from the last
  tree_of_sending_member   its tree at the job
  lent_agrees              a run of an owner's coins against the owner's own cut
  trees_at_own_test        the clause, from hI, hW, hO: what ties each member to its sender at this run

Limits. A conditional on a run. The clause reads the input and the carried values: no later law may
take it as a hypothesis on a run and then speak of the random values as sampled anew. Nothing on
completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.TreesOwnTest
import Johnson.Desc.ProofFile.Honest.K12.Sim.SenderInFront
import Johnson.Desc.ProofFile.Honest.K12.TableIsColumn
import Johnson.Desc.ProofFile.Honest.K14.SendingsPlay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block FileDescription Oracle Place)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof ProofFile.Honest.K12.Light
open Johnson.Prover.Send (col)

/-- **What a one-part half's first round said, as played, in front of a later round of the shared
chain**: first_round_at_first at that chain. -/
theorem first_round_at_shared {Xi W₀ Rc Ky Tr X₀ Y : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} (hR : ready F Bk P w₀ rc x k = .ok R)
    (pre : List (Block F.S₂ F.Cl)) (b : Block F.S₂ F.Cl) (t : List (Block F.S₂ F.Cl))
    (hcut : F.shared.blocksInOrder = pre ++ b :: t) (hb : b.rounds ≠ [])
    (pl : Place) (p : Part Empty (Common W₀ Rc Ky) X₀)
    (mv : Move p.Coins (Common W₀ Rc Ky) X₀) (hmv : p.moves[0]? = some mv)
    (hg : (P.shared.find? fun g => g.place == b.place) = some ⟨pl, [p]⟩)
    (n : ℕ) (hn : (pre.flatMap (·.rounds)).length < n) (L : Lay)
    (a₁ y : ChainProgress F.S₂ F.Cl (Common W₀ Rc Ky) X₀) (hal : a₁.laid = [])
    (hn₂ : n ≤ R.shared.length)
    (hw : walk L (R.shared.take n) (ρ.shared.take n) a₁ = .ok y)
    (hsome : y.mid.isSome = true) :
    ∃ (zᵢ : ChainProgress F.S₂ F.Cl (Common W₀ Rc Ky) X₀) (mᵢ : ProofFile.Honest.Mid (Common W₀ Rc Ky) X₀)
      (c : p.Coins) (q : Played) (z : Sending),
      walk L (R.shared.take (pre.flatMap (·.rounds)).length)
          (ρ.shared.take (pre.flatMap (·.rounds)).length) a₁ = .ok zᵢ ∧
      zᵢ.mid = some mᵢ ∧
      lendPart Bk (Bk.rowsOf 1) (sharedLook Bk k.shared) ⟨b.place, 0⟩ p = .ok c ∧
      y.laid[(pre.flatMap (·.rounds)).length]? = some q ∧
      q.tables = z.tables.map some ∧
      mv.say c mᵢ.shown mᵢ.st = .ok z := by
  obtain ⟨c, l₁, l₂, hl, hsh, hl₁, hor⟩ := block_steps_at_ready hR pre b t hcut _ hg
  obtain ⟨hlp, -⟩ := lendRow_cons_ok hl
  obtain ⟨d, ds, hd⟩ : ∃ d ds, b.rounds = d :: ds := by
    cases hr : b.rounds with
    | nil => exact absurd hr hb
    | cons d ds => exact ⟨d, ds, rfl⟩
  obtain ⟨o, os, ho⟩ : ∃ o os, b.oracles = o :: os := by
    cases hr : b.oracles with
    | nil =>
      rw [hr, hd] at hor
      cases hor
    | cons o os => exact ⟨o, os, rfl⟩
  have e1 : (⟨pl, [p]⟩ :
      Placed Empty (Common W₀ Rc Ky) X₀).steps b (Face.shared.sees R.common) c =
      p.steps b.name ⟨b.place, 0⟩
          ((b.rounds.zip b.oracles).take p.moves.length) (Face.shared.sees R.common) c.1 ++ [] := rfl
  obtain ⟨mv₀, ms, hms⟩ : ∃ mv₀ ms, p.moves = mv₀ :: ms := by
    cases hp : p.moves with
    | nil =>
      rw [hp] at hmv
      cases hmv
    | cons a l => exact ⟨a, l, rfl⟩
  obtain ⟨s, rest, e2⟩ : ∃ s rest,
      p.steps b.name ⟨b.place, 0⟩
          ((b.rounds.zip b.oracles).take p.moves.length) (Face.shared.sees R.common) c.1 = s :: rest := by
    unfold Part.steps
    rw [hms, hd, ho]
    exact ⟨_, _, rfl⟩
  have hs0 : (p.steps b.name ⟨b.place, 0⟩
        ((b.rounds.zip b.oracles).take p.moves.length) (Face.shared.sees R.common) c.1)[0]? = some s := by
    rw [e2]
    rfl
  have hs : (R.shared.take n)[(pre.flatMap (·.rounds)).length]? = some s := by
    rw [List.getElem?_take_of_lt hn, hsh, e1, e2, ← hl₁,
      List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  -- the cut of the walk
  have hlen := walk_len L _ _ a₁ y hw
  obtain ⟨hi, hsi⟩ := List.getElem?_eq_some_iff.1 hs
  obtain ⟨zᵢ, w1, w2, -, -⟩ := walk_cut hal hw (pre.flatMap (·.rounds)).length (Nat.le_of_lt hi)
  have hdrop : (R.shared.take n).drop (pre.flatMap (·.rounds)).length =
      s :: (R.shared.take n).drop ((pre.flatMap (·.rounds)).length + 1) := by
    rw [← hsi, List.getElem_cons_drop]
  have hid : (pre.flatMap (·.rounds)).length < (ρ.shared.take n).length := by
    rw [hlen]
    exact hi
  have ddrop : (ρ.shared.take n).drop (pre.flatMap (·.rounds)).length =
      (ρ.shared.take n)[(pre.flatMap (·.rounds)).length] ::
        (ρ.shared.take n).drop ((pre.flatMap (·.rounds)).length + 1) := by
    rw [List.getElem_cons_drop]
  rw [hdrop, ddrop] at w2
  obtain ⟨x', z₁, hx, hz, hw'⟩ := walk_cons_ok w2
  have hs₁ : zᵢ.mid.isSome = true := mid_back L _ _ zᵢ y w2 hsome
  obtain ⟨mᵢ, hmi⟩ := Option.isSome_iff_exists.1 hs₁
  have h2 : s.tell none mᵢ = .ok x' := by
    unfold ChainProgress.say at hx
    rw [hmi] at hx
    exact hx
  obtain ⟨z, hz', -, hzt, -, -⟩ := tell_move _ _ _ _ _ c.1 0 s hs0 mv hmv mᵢ x' h2
  have hlaidz := walk_laid_drawn L _ _ a₁ zᵢ w1
  rw [hal, List.map_nil, List.nil_append] at hlaidz
  have hzl : zᵢ.laid.length = (pre.flatMap (·.rounds)).length := by
    have := congrArg List.length hlaidz
    rw [List.length_map, List.length_take, List.length_take] at this
    have h5 : (ρ.shared.take n).length = (R.shared.take n).length := hlen
    rw [List.length_take] at h5 hi
    omega
  obtain ⟨tl, htl⟩ := walk_laid_prefix L _ _ z₁ y hw'
  have hq := heard_laid hz
  refine ⟨zᵢ, mᵢ, c.1, ⟨s.name, s.addr.place, s.addr.part, x'.told, x'.vals, x'.tables,
    (ρ.shared.take n)[(pre.flatMap (·.rounds)).length]⟩, z, ?_, hmi, hlp, ?_, ?_, hz'⟩
  · rw [List.take_take, List.take_take, Nat.min_eq_left (Nat.le_of_lt hn)] at w1
    exact w1
  · have gen : ∀ (a b : List Played) (e : Played) (i : ℕ), a.length = i →
        (a ++ ([e] ++ b))[i]? = some e := by
      intro a b e i h
      subst h
      simp
    rw [← htl, hq, List.append_assoc]
    exact gen _ _ _ _ hzl
  · exact hzt

/-- **What the front of a called part of the last chain lists of a tree of the shared chain that a
sending sent**: columns of the sending's written column. -/
theorem sending_tree_in_front {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (σ : Side F.S₃ F.Cl V (Local W₀ Rc Xi Tr) Y Pb) (u : Member V (Local W₀ Rc Xi Tr) Y Pb)
    (pre' t' : List (Block F.S₃ F.Cl)) (i : ℕ) (S : StandsAt F.second.blocksInOrder R.second σ u pre' t' i)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true)
    (pre : List (Block F.S₂ F.Cl)) (b : Block F.S₂ F.Cl) (t : List (Block F.S₂ F.Cl))
    (hcut : F.shared.blocksInOrder = pre ++ b :: t) (hb : b.rounds ≠ [])
    (J : ProofFile.Honest.K14.SendJob) (wit : Common W₀ Rc Ky → ProofFile.Honest.K14.Ask)
    (hg : (P.shared.find? fun g => g.place == b.place) =
      some ⟨b.place, [(ProofFile.Honest.K14.liftSend wit (ProofFile.Honest.K14.sendingPart J) : Part Empty (Common W₀ Rc Ky) X₀)]⟩)
    (μ j : ℕ) (hw : widthFits J μ = true)
    (hj : Johnson.G.OfPlan.rootsOf (pre.flatMap (·.rounds)) + μ = j) (st : List (ℕ × ℕ × List UInt64)) :
    ∃ (mᵢ : ProofFile.Honest.Mid (Common W₀ Rc Ky) X₀)
      (c : (ProofFile.Honest.K14.liftSend wit (ProofFile.Honest.K14.sendingPart J) : Part Empty (Common W₀ Rc Ky) X₀).Coins)
      (cols : List (ℕ × List UInt64)),
      lendPart Bk (Bk.rowsOf 1) (sharedLook Bk k.shared) ⟨b.place, 0⟩
        (ProofFile.Honest.K14.liftSend wit (ProofFile.Honest.K14.sendingPart J)) = .ok c ∧
      mᵢ.st.input = R.common ∧ mᵢ.st.heard = ρ.shared.take (pre.flatMap (·.rounds)).length ∧
      (r.run.beforeAt st ⟨σ.block.place, u.number⟩).treeCols 1 j = some cols ∧
      ∀ q ∈ cols, q.2 = ProofFile.Honest.K14.columnOf J.Q.codes J.Q.sent
        (J.rows (mᵢ.st.narrow wit fun _ => ()) (coinsE c.1).toArray) μ q.1 := by
  have Q := (F.planOk_ok).1 hpl
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  have o₁ := steps_shaped s1 Q.blocks₁
  have o₂ := steps_shaped s2 Q.blocks₂
  have o₃ := steps_shaped s3 Q.blocks₃
  obtain ⟨-, lS, -⟩ := runC_laidAs hrun hR o₁ o₂ o₃
  obtain ⟨m₁, m₂, m, a₁, z₁, a₂, z₂, a₃, y, -, -, -, -, ha₂, hz₂, hl₂, hm₂, -⟩ :=
    played_at_second hpl hR hrun σ u pre' t' i _ S rfl hc
  have hlen : R.shared.length = (F.shared.blocksInOrder.flatMap (·.rounds)).length := by
    rw [chainSteps_length _ _ s2, List.length_flatMap]
  have hlt : (pre.flatMap (·.rounds)).length < R.shared.length := by
    rw [hlen, hcut, List.flatMap_append, List.flatMap_cons, List.length_append, List.length_append]
    have : 0 < b.rounds.length := List.length_pos_iff.2 hb
    omega
  have hρ : ρ.shared.take R.shared.length = ρ.shared := by
    rw [← lS.1]
    exact List.take_length
  have hw' : walk ⟨1, 0, P.storedWords w₀ rc, treeOwn⟩ (R.shared.take R.shared.length)
      (ρ.shared.take R.shared.length) a₂ = .ok z₂ := by
    rw [List.take_length, hρ]
    exact hz₂
  obtain ⟨mv, hmv, hs⟩ : ∃ mv, (ProofFile.Honest.K14.liftSend wit (ProofFile.Honest.K14.sendingPart J) :
      Part Empty (Common W₀ Rc Ky) X₀).moves[0]? = some mv ∧ ∀ c sn t, mv.say c sn t =
        .ok ⟨[], ProofFile.Honest.K14.sentTables J.Q.codes J.Q.sent
          (J.rows (t.narrow wit fun _ => ()) (coinsE c.1).toArray)⟩ :=
    ⟨_, rfl, fun _ _ _ => rfl⟩
  obtain ⟨zᵢ, mᵢ, c, q, z, hwi, hmi, hlend, hq, hqT, hsay⟩ := first_round_at_shared hR pre b t hcut
    hb b.place (ProofFile.Honest.K14.liftSend wit (ProofFile.Honest.K14.sendingPart J)) mv hmv hg _ hlt _ a₂ z₂
    (start_laid ha₂) (Nat.le_refl _) hw' (by rw [hm₂]; rfl)
  have hz := Except.ok.inj ((hs c _ _).symm.trans hsay)
  subst hz
  obtain ⟨T, hT, hcol⟩ := col_sent J (J.rows (mᵢ.st.narrow wit fun _ => ()) (coinsE c.1).toArray) μ hw
  obtain ⟨-, -, -, -, -, -, hbf, -⟩ := frame_at_second hpl hR hrun σ u pre' t' i _ S rfl hc st
  have hq' : r.run.played.2.1[(pre.flatMap (·.rounds)).length]? = some q := by
    rw [← hl₂]
    exact hq
  have hμ : μ < q.tables.length := by
    rw [hqT, List.length_map]
    exact (List.getElem?_eq_some_iff.1 hT).1
  have hat := tab_at_round r.run.played.2.1 _ μ q hq' hμ
  have hsh : r.run.played.2.1.map (·.tables.length) =
      (R.shared.take R.shared.length).map (·.oracles.length) := by
    rw [List.take_length]
    exact laidAs_tables lS
  rw [tables_in_front hpl hR pre b t hcut _ (Nat.le_of_lt hlt) _ hsh, hj, hqT, List.getElem?_map, hT]
    at hat
  refine ⟨mᵢ, c, colsOfT (some T) (treeAsks F ρ 1 j), hlend, ?_, ?_, ?_, ?_⟩
  · exact (walk_mid ha₂ hwi hmi).1
  · have a3 := walk_hears _ _ _ _ a₂ zᵢ (start_hears ha₂) hwi mᵢ hmi
    have a4 := walk_laid_drawn _ _ _ a₂ zᵢ hwi
    rw [start_laid ha₂, List.map_nil, List.nil_append] at a4
    rw [a4] at a3
    exact a3.trans (List.nil_append _)
  · rw [hbf, treeCols_at F ρ _ _ _ st 1 j (by decide)]
    show (((allTabs r.run.played.2.1)[j]?).map _) = _
    rw [hat]
    rfl
  · intro q' hq''
    obtain ⟨x', -, rfl⟩ := List.mem_map.1 hq''
    exact hcol x'

/-! ## Omega's member -/

section OmegaMember
open OnBytes.Slice (GE ofE toE lst readE)
open Johnson.Prover.Send (shapeAt)
open ProofFile.Honest.K14 (SendJob jobOmega Ask columnOf symbolsOf sendingsFit)

variable {W X : Type}

/-- **A sending's tree with one message, without mask rows.** The job's tree number 2 holds the third
member's main rows. Jm: the member's sending, J: the sender's; they have one Q and one sort. -/
theorem tree_of_sending_member {Pq : Desc.K14.P14} (hQ : sendingsFit Pq = true) (J Jm : SendJob)
    (hJ : J.Q = (ProofFile.Honest.K14.jobU ⟨Pq, 0⟩).Q ∧ J.sort = (ProofFile.Honest.K14.jobU ⟨Pq, 0⟩).sort ∨
      J.Q = (jobOmega ⟨Pq, 0⟩).Q ∧ J.sort = (jobOmega ⟨Pq, 0⟩).sort)
    (hq : Jm.Q = J.Q) (hso : Jm.sort = J.sort) (high : Bool) (hs₀ : J.sort 0 = .plain high)
    (B : ManyJob W X) (hk : B.s₀.h ≤ B.s₀.k) (w : W) (fr : Front X) (C : TestCoins)
    (m₀ m₁ : Mem W X) (at_ : Addr) (fs : Option ℕ × Option ℕ) (ask : W → Ask)
    (hm : B.mems = [m₀, m₁, memOfSending Jm at_ 0 fs ask none])
    (d : ℕ) (ht : B.trees[2]? = some (d, [.main 2]))
    (hbase : (memOfSending (X := X) Jm at_ 0 fs ask none).shape.base = false)
    (hoff : ∀ y ∈ [m₀, m₁], ∀ b,
      (memOfSending (X := X) Jm at_ 0 fs ask none).shape.mainFirst ≤ b →
      b < (memOfSending (X := X) Jm at_ 0 fs ask none).shape.mainFirst +
        (memOfSending (X := X) Jm at_ 0 fs ask none).shape.mainRows →
      ¬ (y.shape.mainFirst ≤ b ∧ b < y.shape.mainFirst + y.shape.mainRows))
    (hin : (memOfSending (X := X) Jm at_ 0 fs ask none).shape.mainFirst +
      (memOfSending (X := X) Jm at_ 0 fs ask none).shape.mainRows ≤ 2 ^ B.s₀.k)
    (st : State Ask Unit) (cs : Array OnBytes.E)
    (hv : Jm.data ⟨ask w, fr.heard, ()⟩ 0 = J.data st 0)
    (same : SameCut J 0 cs (C.mem 2))
    (hc : sameCode (J.Q.codes.base.getD (Light.shapeAt J 0).code default) B.s₀.C = true)
    (hmine : mineOf J 0 = [0]) (hmask : (Light.shapeAt J 0).maskRows = 0) (x : ℕ) :
    ((B.toRun.toTest.trees₀ w fr C.mem (B.toRun.toTest.first w fr C)).getD 2 (0, fun _ => [])).2 x =
      columnOf J.Q.codes J.Q.sent (J.rows st cs) 0 x := by
  obtain ⟨Q₁, so₁, da₁⟩ := Jm
  obtain ⟨Q₂, so₂, da₂⟩ := J
  dsimp only at hq hso hv
  subst hq hso
  have k0 : 0 < Q₁.sent.size := lt_of_mine (J := ⟨Q₁, so₁, da₂⟩) (μ := 0) (by rw [hmine]; simp)
  have hCc := code_of_same hc
  have hl := congrArg Fmt.M1.Code.l hCc
  have hr := congrArg Fmt.M1.Code.r hCc
  simp only at hl hr
  rw [tree_column B w fr C.mem _ 2 d _ ht x, columnOf_mine, hmine]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [hmask, symbolsOf_none, List.append_nil, symbolsOf_field, hCc]
  refine member_main B hk w fr C [m₀, m₁] [] _ hm hbase hoff hin
    (fun r j => readE ((SendJob.rows ⟨Q₁, so₁, da₂⟩ st cs 0).main r j))
    (fun r t => readE ((SendJob.rows ⟨Q₁, so₁, da₂⟩ st cs 0).mainTail r t))
    (fun r hr' j hj => ?_) (fun r hr' t ht' => ?_) x
  · have hj' : j < (Q₁.codes.base.getD (Light.shapeAt ⟨Q₁, so₁, da₂⟩ 0).code default).ell := by
      rw [hl]
      exact hj
    have e := entries_same Pq hQ ⟨Q₁, so₁, da₂⟩ hJ 0 k0 high hs₀ (da₂ st 0) cs (C.mem 2) same
      (.main r j) (mem_main hr' hj')
    have e2 := lst_tabE _ _ (ProofFile.Honest.K14.laid Q₁.codes (Light.shapeAt ⟨Q₁, so₁, da₂⟩ 0)
      (da₁ ⟨ask w, fr.heard, ()⟩ 0) (fun i => OnBytes.E.ofTriple (ofE ((C.mem 2).e i))) (so₁ 0)).main
      r j hr' hj'
    refine e2.trans ?_
    rw [hv]
    exact e
  · have ht'' : t < (Q₁.codes.base.getD (Light.shapeAt ⟨Q₁, so₁, da₂⟩ 0).code default).r := by
      rw [hr]
      exact ht'
    have e := entries_same Pq hQ ⟨Q₁, so₁, da₂⟩ hJ 0 k0 high hs₀ (da₂ st 0) cs (C.mem 2) same
      (.mainTail r t) (mem_mainTail hr' ht'')
    have e2 := lst_tabE _ _ (ProofFile.Honest.K14.laid Q₁.codes (Light.shapeAt ⟨Q₁, so₁, da₂⟩ 0)
      (da₁ ⟨ask w, fr.heard, ()⟩ 0) (fun i => OnBytes.E.ofTriple (ofE ((C.mem 2).e i))) (so₁ 0)).mainTail
      r t hr' ht''
    refine e2.trans ?_
    rw [hv]
    exact e

end OmegaMember

/-! ## What the book lends, against a sender's purse -/

/-- A run of an owner's coins, against the owner's own cut of them. -/
theorem lent_agrees {d t A N : Due} (L : Cs d) (c : Cs t) (x : Cs N)
    (hown : L.cut ⟨0, 0⟩ t = some c) (hx : L.cut A N = some x)
    (hf : A.f + N.f ≤ t.f) (he : A.e + N.e ≤ t.e) :
    (∀ i, i < N.f → K1.cf c (A.f + i) = (stretchOf x).f i) ∧
      (∀ i, i < N.e → K1.ce c (A.e + i) = (stretchOf x).e i) := by
  unfold Cs.cut at hown hx
  split at hown
  · split at hx
    · obtain rfl := Option.some.inj hown
      obtain rfl := Option.some.inj hx
      refine ⟨fun i hi => ?_, fun i hi => ?_⟩
      · unfold K1.cf stretchOf
        rw [dif_pos (by omega : A.f + i < t.f)]
        simp only [dif_pos hi]
        exact congrArg _ (Fin.ext (Nat.zero_add _))
      · unfold K1.ce stretchOf
        rw [dif_pos (by omega : A.e + i < t.e)]
        simp only [dif_pos hi]
        exact congrArg _ (Fin.ext (Nat.zero_add _))
    · cases hx
  · cases hown

/-! ## The clause at a run, from the members' ties -/

section Clause
open OnBytes.Slice (codeOf)
open Johnson.Prover.Send (mainSyms maskSyms Rows)
open ProofFile.Honest.K14 (SendJob jobOmega Ask columnOf sendingsFit)

variable {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type}

/-- **The clause trees at the request's own test, at a run**, at a job of three members whose trees
are the place's: the index-mask message's, W's with the first fold's fresh table, Omega's, each sent in
an earlier chain. What ties each member to its sender at this run is handed in: hI, hW, hO. -/
theorem trees_at_own_test {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (σ : Side F.S₃ F.Cl V (Local W₀ Rc Xi Tr) Y Pb) (u : Member V (Local W₀ Rc Xi Tr) Y Pb)
    (pre' t' : List (Block F.S₃ F.Cl)) (i : ℕ) (S : StandsAt F.second.blocksInOrder R.second σ u pre' t' i)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) (st : List (ℕ × ℕ × List UInt64))
    -- the job
    (B : ManyJob (Local W₀ Rc Xi Tr) Y) (hk : B.s₀.h ≤ B.s₀.k) (Pq : Desc.K14.P14)
    (hQ : sendingsFit Pq = true) (a a' : ℕ) (m₀ m₁ : Mem (Local W₀ Rc Xi Tr) Y) (at_ : Addr)
    (fs : Option ℕ × Option ℕ) (ask : Local W₀ Rc Xi Tr → Ask)
    (hm : B.mems = [m₀, m₁, memOfSending (jobOmega ⟨Pq, a'⟩) at_ 0 fs ask none])
    (d₀ d₁ d₂ : ℕ)
    (ht : B.trees = [(d₀, [.mask 0]), (d₁, [.main 1, .mask 1, .fresh]), (d₂, [.main 2])])
    (os : List (Fmt.Shape × Fmt.TreeSource)) (hd : [d₀, d₁, d₂] = os.map (·.1.a))
    (j₀ j₁ j₂ : ℕ) (hsrc : os.map (fun o => ProofFile.Honest.srcOf 2 o.2) = [(0, j₀), (0, j₁), (1, j₂)])
    -- the state and the members' stretches
    (m : ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) Y) (mem : ℕ → Stretch)
    -- the first chain's two senders
    (preI preW : List (Block F.S₁ F.Cl)) (bI bW : Block F.S₁ F.Cl) (tI tW : List (Block F.S₁ F.Cl))
    (hcutI : F.first.blocksInOrder = preI ++ bI :: tI) (hcutW : F.first.blocksInOrder = preW ++ bW :: tW)
    (hbI : bI.rounds ≠ []) (hbW : bW.rounds ≠ [])
    (wit : Local W₀ Rc Xi Tr → K1.PlaceIn Xi) (JI JW : K1.SendJob (K1.PlaceIn Xi) Y)
    (hgI : (P.first.find? fun g => g.place == bI.place) =
      some (K1.placeHalf (V := Local W₀ Rc Xi Tr) wit JI))
    (hgW : (P.first.find? fun g => g.place == bW.place) =
      some (K1.placeHalf (V := Local W₀ Rc Xi Tr) wit JW))
    (τI τW kI : ℕ) (shI shW : OnBytes.TreeShape) (hτI : JI.P.trees[τI]? = some shI)
    (hτW : JW.P.trees[τW]? = some shW)
    (hWI : columnWidth JI.P τI = shI.mainWidth + shI.maskWidth)
    (hWW : columnWidth JW.P τW = shW.mainWidth + shW.maskWidth)
    (hjI : treesTo F.first.blocksInOrder preI.length + τI = j₀)
    (hjW : treesTo F.first.blocksInOrder preW.length + τW = j₁)
    -- what the two members are, of their senders' rows at this run
    (hI : ∀ (mᵢ : ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) Y)
      (c : ((K1.sendPart (V := Local W₀ Rc Xi Tr) JI).lift id wit id fun _ y => y :
        Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).Coins),
      lendPart Bk (Bk.rowsOf 0) (k.look 0) ⟨bI.place, 0⟩
        ((K1.sendPart (V := Local W₀ Rc Xi Tr) JI).lift id wit id fun _ y => y) = .ok c →
      mᵢ.st.input = R.own → mᵢ.st.heard = ρ.first.take (preI.flatMap (·.rounds)).length →
      m₀.rows m.st.input (restFront B.toRun.toTest m) (mem 0) =
        psOfRows JI.P kI (JI.rows c.1 mᵢ.shown (mᵢ.st.narrow wit id) 0 kI))
    (hW : ∀ (mᵢ : ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) Y)
      (c : ((K1.sendPart (V := Local W₀ Rc Xi Tr) JW).lift id wit id fun _ y => y :
        Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).Coins),
      lendPart Bk (Bk.rowsOf 0) (k.look 0) ⟨bW.place, 0⟩
        ((K1.sendPart (V := Local W₀ Rc Xi Tr) JW).lift id wit id fun _ y => y) = .ok c →
      mᵢ.st.input = R.own → mᵢ.st.heard = ρ.first.take (preW.flatMap (·.rounds)).length →
      m₁.rows m.st.input (restFront B.toRun.toTest m) (mem 1) =
          psOfRows JW.P 0 (JW.rows c.1 mᵢ.shown (mᵢ.st.narrow wit id) 0 0) ∧
        (∀ r < 2 ^ B.s₀.h, ∀ j < B.s₀.Z.l, (JW.rows c.1 mᵢ.shown (mᵢ.st.narrow wit id) 0 1).mask r j =
          (rowsAt B.toRun.toTest mem m).fM r j) ∧
        ∀ r < 2 ^ B.s₀.h, ∀ q < B.s₀.Z.r, (JW.rows c.1 mᵢ.shown (mᵢ.st.narrow wit id) 0 1).maskTl r q =
          (rowsAt B.toRun.toTest mem m).fT r q)
    -- public, at the two senders
    (hinZ₀ : m₀.shape.maskFirst + m₀.shape.maskRows ≤ 2 ^ B.s₀.h)
    (hnI : m₀.shape.maskRows = (Johnson.Prover.Send.shapeAt JI.P kI).maskRows)
    (hzI : codeOf (JI.P.codes.mask.getD (Johnson.Prover.Send.shapeAt JI.P kI).maskCode default) =
      B.s₀.Z)
    (hmineI : (List.range JI.P.sent.size).filter (fun k =>
      ((VerifiableInference.Desc.Own.treesMade JI.P.codes JI.P.sent).getD {}).tree[k]? == some τI) =
        [kI])
    (hmainI : (Johnson.Prover.Send.shapeAt JI.P kI).mainRows = 0)
    (hbase₁ : m₁.shape.base = false)
    (hoffM : ∀ b, m₁.shape.mainFirst ≤ b → b < m₁.shape.mainFirst + m₁.shape.mainRows →
      ¬ (m₀.shape.mainFirst ≤ b ∧ b < m₀.shape.mainFirst + m₀.shape.mainRows))
    (hoffZ : ∀ b, m₁.shape.maskFirst ≤ b → b < m₁.shape.maskFirst + m₁.shape.maskRows →
      ¬ (m₀.shape.maskFirst ≤ b ∧ b < m₀.shape.maskFirst + m₀.shape.maskRows))
    (hinM : m₁.shape.mainFirst + m₁.shape.mainRows ≤ 2 ^ B.s₀.k)
    (hinZ : m₁.shape.maskFirst + m₁.shape.maskRows ≤ 2 ^ B.s₀.h)
    (hnM : m₁.shape.mainRows = (Johnson.Prover.Send.shapeAt JW.P 0).mainRows)
    (hnZ : m₁.shape.maskRows = (Johnson.Prover.Send.shapeAt JW.P 0).maskRows)
    (hdW : (Johnson.Prover.Send.shapeAt JW.P 0).mainDeg = 3)
    (hzC : codeOf (JW.P.codes.base.getD (Johnson.Prover.Send.shapeAt JW.P 0).code default) = B.s₀.C)
    (hzZ : codeOf (JW.P.codes.mask.getD (Johnson.Prover.Send.shapeAt JW.P 0).maskCode default) =
      B.s₀.Z)
    (hzF : codeOf (JW.P.codes.mask.getD (Johnson.Prover.Send.shapeAt JW.P 1).maskCode default) =
      B.s₀.Z)
    (hnF : (Johnson.Prover.Send.shapeAt JW.P 1).maskRows = 2 ^ B.s₀.h)
    (hmF : (Johnson.Prover.Send.shapeAt JW.P 1).mainRows = 0)
    (hmineW : (List.range JW.P.sent.size).filter (fun k =>
      ((VerifiableInference.Desc.Own.treesMade JW.P.codes JW.P.sent).getD {}).tree[k]? == some τW) =
        [0, 1])
    -- the shared chain's sender
    (preO : List (Block F.S₂ F.Cl)) (bO : Block F.S₂ F.Cl) (tO : List (Block F.S₂ F.Cl))
    (hcutO : F.shared.blocksInOrder = preO ++ bO :: tO) (hbO : bO.rounds ≠ [])
    (witO : Common W₀ Rc Ky → Ask)
    (hgO : (P.shared.find? fun g => g.place == bO.place) =
      some ⟨bO.place, [(ProofFile.Honest.K14.liftSend witO (ProofFile.Honest.K14.sendingPart (jobOmega ⟨Pq, a⟩)) :
        Part Empty (Common W₀ Rc Ky) X₀)]⟩)
    (hwO : widthFits (jobOmega ⟨Pq, a⟩) 0 = true)
    (hjO : Johnson.G.OfPlan.rootsOf (preO.flatMap (·.rounds)) + 0 = j₂)
    (hO : ∀ (mᵢ : ProofFile.Honest.Mid (Common W₀ Rc Ky) X₀)
      (c : (ProofFile.Honest.K14.liftSend witO (ProofFile.Honest.K14.sendingPart (jobOmega ⟨Pq, a⟩)) :
        Part Empty (Common W₀ Rc Ky) X₀).Coins),
      lendPart Bk (Bk.rowsOf 1) (sharedLook Bk k.shared) ⟨bO.place, 0⟩
        (ProofFile.Honest.K14.liftSend witO (ProofFile.Honest.K14.sendingPart (jobOmega ⟨Pq, a⟩))) = .ok c →
      mᵢ.st.input = R.common → mᵢ.st.heard = ρ.shared.take (preO.flatMap (·.rounds)).length →
      (jobOmega ⟨Pq, a'⟩).data ⟨ask m.st.input, (restFront B.toRun.toTest m).heard, ()⟩ 0 =
          (jobOmega ⟨Pq, a⟩).data (mᵢ.st.narrow witO fun _ => ()) 0 ∧
        SameCut (jobOmega ⟨Pq, a⟩) 0 (coinsE c.1).toArray (mem 2))
    (hbaseO : (memOfSending (X := Y) (jobOmega ⟨Pq, a'⟩) at_ 0 fs ask none).shape.base = false)
    (hoffO : ∀ y ∈ [m₀, m₁], ∀ b,
      (memOfSending (X := Y) (jobOmega ⟨Pq, a'⟩) at_ 0 fs ask none).shape.mainFirst ≤ b →
      b < (memOfSending (X := Y) (jobOmega ⟨Pq, a'⟩) at_ 0 fs ask none).shape.mainFirst +
        (memOfSending (X := Y) (jobOmega ⟨Pq, a'⟩) at_ 0 fs ask none).shape.mainRows →
      ¬ (y.shape.mainFirst ≤ b ∧ b < y.shape.mainFirst + y.shape.mainRows))
    (hinO : (memOfSending (X := Y) (jobOmega ⟨Pq, a'⟩) at_ 0 fs ask none).shape.mainFirst +
      (memOfSending (X := Y) (jobOmega ⟨Pq, a'⟩) at_ 0 fs ask none).shape.mainRows ≤ 2 ^ B.s₀.k)
    (hcO : sameCode ((jobOmega ⟨Pq, a⟩).Q.codes.base.getD
      (Light.shapeAt (jobOmega ⟨Pq, a⟩) 0).code default) B.s₀.C = true)
    (hmineO : mineOf (jobOmega ⟨Pq, a⟩) 0 = [0])
    (hmaskO : (Light.shapeAt (jobOmega ⟨Pq, a⟩) 0).maskRows = 0) :
    TreesAt B.toRun.toTest 2 os mem m (r.run.beforeAt st ⟨σ.block.place, u.number⟩) := by
  obtain ⟨o₀, o₁, o₂, hos⟩ : ∃ o₀ o₁ o₂, os = [o₀, o₁, o₂] := by
    have hl := congrArg List.length hsrc
    rw [List.length_map] at hl
    match os, hl with
    | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
  subst hos
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsrc hd
  obtain ⟨s₀, s₁, s₂⟩ := hsrc
  obtain ⟨e₀, e₁, e₂⟩ := hd
  have hT : B.toRun.toTest.trees₀ m.st.input (restFront B.toRun.toTest m) mem
      (rowsAt B.toRun.toTest mem m) = B.trees.map fun T =>
        Light.treeOf B.s₀ (T.1, T.2.flatMap (selsOf B.s₀ (B.mems.map (·.shape))))
          (rowsAt B.toRun.toTest mem m) :=
    trees₀_many B _ _ mem _
  refine ⟨?_, fun n o T ho hTn => ?_⟩
  · rw [hT, ht]
    show [d₀, d₁, d₂] = _
    rw [e₀, e₁, e₂]
    rfl
  · have hcol : ∀ (n : ℕ) (T : Tree) (z : ℕ), (B.toRun.toTest.trees₀ m.st.input
        (restFront B.toRun.toTest m) mem (rowsAt B.toRun.toTest mem m))[n]? = some T →
        T.2 z = ((B.toRun.toTest.trees₀ m.st.input (restFront B.toRun.toTest m) mem
          (B.toRun.toTest.first m.st.input (restFront B.toRun.toTest m)
            (carriedCoins B.toRun.toTest mem))).getD n (0, fun _ => [])).2 z := by
      intro n T z h
      show _ = ((B.toRun.toTest.trees₀ m.st.input (restFront B.toRun.toTest m) mem
        (rowsAt B.toRun.toTest mem m)).getD n (0, fun _ => [])).2 z
      rw [List.getD_eq_getElem?_getD, h]
      rfl
    match n, ho, hTn with
    | 0, ho, hTn =>
      obtain rfl : o₀ = o := Option.some.inj ho
      rw [s₀]
      obtain ⟨mᵢ, c, cols, hl, hin, hh, hf, hq⟩ := k1_tree_in_front hpl hR hrun σ u pre' t' i S hc
        preI bI tI hcutI hbI wit JI hgI τI j₀ shI hτI hWI hjI st
      refine ⟨cols, hf, fun q hq' => ?_⟩
      rw [hq q hq', hcol 0 T q.1 hTn]
      exact (tree_of_mask_member B m.st.input (restFront B.toRun.toTest m)
        (carriedCoins B.toRun.toTest mem) m₀ _ hm d₀ (by rw [ht]; rfl) hinZ₀ JI.P kI τI _
        (hI mᵢ c hl hin hh) hnI hzI hmineI hmainI q.1).symm
    | 1, ho, hTn =>
      obtain rfl : o₁ = o := Option.some.inj ho
      rw [s₁]
      obtain ⟨mᵢ, c, cols, hl, hin, hh, hf, hq⟩ := k1_tree_in_front hpl hR hrun σ u pre' t' i S hc
        preW bW tW hcutW hbW wit JW hgW τW j₁ shW hτW hWW hjW st
      refine ⟨cols, hf, fun q hq' => ?_⟩
      obtain ⟨w1, w2, w3⟩ := hW mᵢ c hl hin hh
      rw [hq q hq', hcol 1 T q.1 hTn]
      exact (tree_of_riding_member B hk m.st.input (restFront B.toRun.toTest m)
        (carriedCoins B.toRun.toTest mem) m₀ m₁ _ hm d₁ (by rw [ht]; rfl) hbase₁ hoffM hoffZ hinM hinZ
        JW.P τW _ w1 hnM hnZ hdW hzC hzZ hzF hnF hmF hmineW w2 w3 q.1).symm
    | 2, ho, hTn =>
      obtain rfl : o₂ = o := Option.some.inj ho
      rw [s₂]
      obtain ⟨mᵢ, c, cols, hl, hin, hh, hf, hq⟩ := sending_tree_in_front hpl hR hrun σ u pre' t' i S hc
        preO bO tO hcutO hbO (jobOmega ⟨Pq, a⟩) witO hgO 0 j₂ hwO hjO st
      refine ⟨cols, hf, fun q hq' => ?_⟩
      obtain ⟨o1, o2⟩ := hO mᵢ c hl hin hh
      rw [hq q hq', hcol 2 T q.1 hTn]
      exact (tree_of_sending_member hQ (jobOmega ⟨Pq, a⟩) (jobOmega ⟨Pq, a'⟩) (.inr ⟨rfl, rfl⟩) rfl rfl
        _ rfl B hk m.st.input (restFront B.toRun.toTest m)
        (carriedCoins B.toRun.toTest mem) m₀ m₁ at_ fs ask hm d₂ (by rw [ht]; rfl) hbaseO hoffO hinO
        _ _ o1 o2 hcO hmineO hmaskO q.1).symm
    | _ + 3, ho, _ => cases ho

end Clause

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.first_round_at_shared
#print axioms ProofFile.Honest.K12.Sim2.trees_at_own_test
#print axioms ProofFile.Honest.K12.Sim2.tree_of_sending_member
#print axioms ProofFile.Honest.K12.Sim2.lent_agrees
#print axioms ProofFile.Honest.K12.Sim2.sending_tree_in_front
