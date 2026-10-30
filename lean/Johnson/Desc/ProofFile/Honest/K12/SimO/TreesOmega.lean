-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator at the proximity test on G_omega: the first opening's columns at a run.
/-
Johnson/Desc/ProofFile/Honest/K12/SimO/TreesOmega.lean: the columns that a run's front lists of the three trees that the test's first switch opens, at the test's own first part's table and at the two trees of the sending: the first step, on the first part's own table.

  `fresh_col_eq`       the column of a tree that holds the fresh table alone is `freshCol`
  `length_freshCol`, `canonW_freshCol`   its length; its words are written forms
  `msgAt_zero_tables`, `msgAt_one_tables`   "BAT" sends no table; the first fold's first round sends the one table whose columns are `freshCol`
  `own_table_played`   the same of the first part's play

Limits. Conditional: nothing here says that a run reaches the part. No property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.SimO.FiveOwn
import Johnson.Desc.ProofFile.Honest.K12.TreesSentBeforeTestFromSentTable
import Johnson.Desc.ProofFile.Honest.K12.KeptLaw4
import Johnson.Desc.ProofFile.Honest.K12.Sim.PlayedFirst
import Johnson.Desc.ProofFile.Honest.K12.TreeIsColumn
import Johnson.Desc.ProofFile.Honest.K12.Sim.TreesAtRunU

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open ProofFile.Honest (Part Played Table Step play)
open ProofFile.Honest.K14 (SendDeclared sendingsFit takesOf columnOf sendTablesAt)

variable {V W X : Type}

theorem fresh_col_eq (s : Fmt.M1.Stage) (P : PS) (x : ℕ) :
    wordsAt (symOf s P x) ((List.range (2 ^ s.h)).map fun r => ⟨.fresh, r, false⟩) =
      freshCol (sgOf s) P x := by
  rw [freshWords]
  unfold freshCol Johnson.Prover.Link.wordsOf wr
  rw [List.flatMap_map]
  rfl

theorem length_wordsOf : ∀ l : List Fmt.M1.E, (Johnson.Prover.Link.wordsOf l).length = 3 * l.length
  | [] => rfl
  | a :: l => by
    show (words3 a ++ Johnson.Prover.Link.wordsOf l).length = _
    rw [List.length_append, length_wordsOf l]
    show 3 + _ = _
    simp only [List.length_cons]
    omega

theorem length_freshCol (s : Sg) (P : PS) (x : ℕ) : (freshCol s P x).length = 3 * 2 ^ s.h := by
  unfold freshCol wr
  rw [length_wordsOf, List.length_map, List.length_range]

theorem canonW_freshCol (s : Sg) (P : PS) (x : ℕ) : CanonW (freshCol s P x) := by
  intro w hw
  unfold freshCol Johnson.Prover.Link.wordsOf wr at hw
  obtain ⟨e, he, hw'⟩ := List.mem_flatMap.1 hw
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 he
  exact canonW_words3 _ w hw'

theorem msgAt_zero_tables (J : TestJob W X) (w : W) (fr : Front X) (K : TestCoins) (D : ℕ → Fmt.Drawn) :
    (msgAt J w fr K D 0).tables = [] := rfl

theorem msgAt_one_tables (J : TestJob W X) (hfr : J.fresh = none) (s next : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: next :: rest) (hk : s.h ≤ s.k) (w : W)
    (fr : Front X) (K : TestCoins) (D : ℕ → Fmt.Drawn) :
    ∃ Tb : Table, (msgAt J w fr K D 1).tables = [Tb] ∧
      ∀ x, Tb.col x = freshCol (sgOf s) (J.first w fr K) x := by
  have hd : depthAt J 1 = some s.Z.a := by
    unfold depthAt
    rw [hfr, hst]
    rfl
  have hlF := firstFold_length (s :: next :: rest) J w fr K D s hk
  have htr : (testAll J w fr K D).tr.getD 1 (fun _ => []) = freshCol (sgOf s) (J.first w fr K) := by
    have e := testAll_tr J w fr K D s next rest hst hk
    rw [hfr] at e
    simp only [Option.isNone_none, ↓reduceIte] at e
    have e1 := congrArg (·[1]?) e
    simp only at e1
    rw [List.getElem?_take_of_lt (by omega)] at e1
    rw [List.getD_eq_getElem?_getD, e1]
    cases hf : firstFold (s :: next :: rest) J w fr K D s with
    | nil =>
      rw [hf] at hlF
      simp at hlF
    | cons a l => rfl
  refine ⟨⟨s.Z.a, (freshCol (sgOf s) (J.first w fr K) 0).length,
    fun x k => toF ((freshCol (sgOf s) (J.first w fr K) x).getD k.val 0)⟩, ?_, fun x => ?_⟩
  · unfold msgAt
    dsimp only
    rw [hd, htr]
    rfl
  · exact col_of_sym _ _ _ x (by rw [length_freshCol, length_freshCol]) (canonW_freshCol _ _ x)

/-- **What the first part's play lays at its first two rounds.** -/
theorem own_table_played (J : TestJob W X) (hfr : J.fresh = none) (name : String) (ad : ProofFile.Honest.Addr)
    (v : Option V) (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (m : ProofFile.Honest.Mid W X) (D : ℕ → Fmt.Drawn)
    (ds : List Fmt.Drawn) (T : FirstTies J s next rest D ds) (hk : s.h ≤ s.k)
    (c : (firstPart J : Part V W X).Coins) (y : List Played × ProofFile.Honest.Mid W X)
    (hy : play ((firstPart J : Part V W X).steps name ad (J.laid.take (firstLen J.p.nums.stages)) v c)
      ds [] m = .ok y) :
    ∃ (q₀ q₁ : Played) (Tb : Table), y.1[0]? = some q₀ ∧ q₀.tables = [] ∧ y.1[1]? = some q₁ ∧
      q₁.tables = [some Tb] ∧
      ∀ x, Tb.col x = freshCol (sgOf s) (J.first m.st.input (frontBy m 0) (firstRd J c)) x := by
  have hrs : (J.laid.take (firstLen J.p.nums.stages)).length = firstLen J.p.nums.stages := by
    rw [List.length_take]
    exact Nat.min_eq_left T.enough
  obtain ⟨hl, hm⟩ := steps_at J (firstPart J : Part V W X) (firstRd J) 0
    (firstLen J.p.nums.stages) (first_moves J) name ad (J.laid.take (firstLen J.p.nums.stages)) hrs
    v c
  have hH : Heard m 0 D := ⟨Nat.zero_le _, Nat.zero_le _, fun n hn => absurd hn (Nat.not_lt_zero n)⟩
  have hown : ∀ n (h : n < ds.length), ds[n] = D (0 + n) := fun n h => by
    rw [Nat.zero_add]
    exact T.own n h
  obtain ⟨hp, -, -, -⟩ := play_test J (fun _ => firstRd J c) D _ 0 ds [] m y hm hy hH hown
  rw [hl] at hp
  have hn : firstLen J.p.nums.stages = 2 + s.k := by rw [T.stages]; rfl
  obtain ⟨Tb, hT, hcol⟩ := msgAt_one_tables J hfr s next rest T.stages hk m.st.input (frontBy m 0)
    (firstRd J c) D
  have e0 := congrArg (·[0]?) hp
  have e1 := congrArg (·[1]?) hp
  simp only [List.getElem?_map] at e0 e1
  rw [List.getElem?_range (by omega)] at e0 e1
  simp only [Option.map_some] at e0 e1
  obtain ⟨q₀, h0, h0'⟩ := Option.map_eq_some_iff.1 e0
  obtain ⟨q₁, h1, h1'⟩ := Option.map_eq_some_iff.1 e1
  refine ⟨q₀, q₁, Tb, h0, ?_, h1, ?_, hcol⟩
  · have := congrArg (·.2.1) h0'
    simpa [shownOf, shownAt, msgAt_zero_tables] using this
  · have := congrArg (·.2.1) h1'
    simpa [shownOf, shownAt, hT] using this



/-- `agree_own` at a job that is not written out. -/
theorem agree_job (J : TestJob W X) (hfr : J.fresh = none) (Bk : ProofFile.Honest.ProverCoinCounts)
    (look : ProofFile.Honest.Addr → (d : ProofFile.Honest.Due) × ProofFile.Honest.Cs d)
    (c₁ : (firstPart J : Part V W X).Coins) (c₂ : (restPart J : Part V W X).Coins)
    (own : (look ⟨J.p.place, 0⟩).2.cut ⟨0, 0⟩ (firstPart J : Part V W X).takes = some c₁.1)
    (k₁ : ProofFile.Honest.lend look (firstPart J : Part V W X).carries (ProofFile.Honest.carryE Bk ⟨J.p.place, 0⟩) = .ok c₁.2.2)
    (k₂ : ProofFile.Honest.lend look (restPart J : Part V W X).carries (ProofFile.Honest.carryE Bk ⟨J.p.place, 0 + 1⟩) = .ok c₂.2.2)
    (w : W) (fr : Front X) (e₂ : ProofFile.Honest.Ahead)
    (hf : (ProofFile.Honest.carryE Bk ⟨J.p.place, 0 + 1⟩)[J.members.length]? = some e₂)
    (ho : e₂.owner = ⟨J.p.place, 0⟩) (hst : e₂.start = ⟨0, 0⟩)
    (hmem : ∀ t, t < J.members.length → ∃ a a', (ProofFile.Honest.carryE Bk ⟨J.p.place, 0⟩)[t]? = some a ∧
      (ProofFile.Honest.carryE Bk ⟨J.p.place, 0 + 1⟩)[t]? = some a' ∧ a.owner = a'.owner ∧ a.start = a'.start ∧
      a.count = a'.count)
    (hrows : ∀ mem mem' : ℕ → Stretch, (∀ t, t < J.members.length → mem t = mem' t) →
      μOf (sgOf J.s₀) (J.rows₀ w fr mem) = μOf (sgOf J.s₀) (J.rows₀ w fr mem')) :
    Agree J w fr J.s₀ (firstRd J c₁) (restCoins J c₂) := by
  obtain ⟨p, ms, fresh, r, ro, tr⟩ := J
  obtain rfl : fresh = none := hfr
  exact agree_own p ms r ro tr Bk look c₁ c₂ own k₁ k₂ w fr e₂ hf ho hst hmem hrows

/-- The first fresh table's column reads the coefficients and the tails alone. -/
theorem freshCol_agree (J : TestJob W X) (s : Fmt.M1.Stage) (hs : J.s₀ = s) (w w' : W) (fr fr' : Front X)
    (K₁ K₂ : TestCoins)
    (e1 : hideAt ((sgOf s).h + (sgOf s).g) K₁.hide = hideAt ((sgOf s).h + (sgOf s).g) K₂.hide)
    (e2 : K₁.tails = K₂.tails) (y : ℕ) :
    freshCol (sgOf s) (J.first w fr K₁) y = freshCol (sgOf s) (J.first w' fr' K₂) y := by
  subst hs
  show Johnson.Prover.Link.wordsOf (wr _ (freshSym _ (packedN _ (hideAt _ K₁.hide)) K₁.tails y)) =
    Johnson.Prover.Link.wordsOf (wr _ (freshSym _ (packedN _ (hideAt _ K₂.hide)) K₂.tails y))
  rw [e1, e2]

/-- What a part is lent, from its pieces. -/
theorem lendPart_of_parts {Bk : ProofFile.Honest.ProverCoinCounts} {rows : List (ProofFile.Honest.Addr × ProofFile.Honest.Due)}
    {look : ProofFile.Honest.Addr → (d : ProofFile.Honest.Due) × ProofFile.Honest.Cs d} {a : ProofFile.Honest.Addr} {p : Part V W X}
    {c : p.Coins} (h1 : p.takes = ProofFile.Honest.dueAt rows a)
    (h2 : (look a).2.cut ⟨0, 0⟩ p.takes = some c.1)
    (h3 : ProofFile.Honest.lend look p.spends (ProofFile.Honest.spentE Bk a) = .ok c.2.1)
    (h4 : ProofFile.Honest.lend look p.carries (ProofFile.Honest.carryE Bk a) = .ok c.2.2) :
    ProofFile.Honest.lendPart Bk rows look a p = .ok c := by
  unfold ProofFile.Honest.lendPart
  simp only
  rw [if_neg (by simp [h1])]
  split
  · rename_i hn
    rw [h2] at hn
    cases hn
  · rename_i own hs
    rw [h2] at hs
    obtain rfl := Option.some.inj hs
    have e3 : ProofFile.Honest.lend look p.spends
        ((Bk.ahead.filter fun e => e.spender == a).filter (·.once)) = .ok c.2.1 := h3
    have e4 : ProofFile.Honest.lend look p.carries
        ((Bk.ahead.filter fun e => e.spender == a).filter (!·.once)) = .ok c.2.2 := h4
    rw [e3]
    show (ProofFile.Honest.lend look p.carries _).map _ = _
    rw [e4]
    rfl

/-- `same_vector` (Sim/SameVectorAtRun.lean) at the sending of o_omega. -/
theorem same_vector_omega {W X : Type} (A : ProofFile.Honest.K14.SendPub) (ask : W → ProofFile.Honest.K14.Ask) (J : TestJob W X)
    (m mb : ProofFile.Honest.Mid W X) (ρs : List Fmt.Drawn) (n N : ℕ) (hm : m.st.heard = ρs.take n)
    (hb : mb.st.heard = ρs.take N) (hi : mb.st.input = m.st.input) (h1 : A.atPoint < N)
    (h2 : A.atPoint + firstLen J.p.nums.stages < m.st.heard.length) :
    vecAt (ProofFile.Honest.K14.jobOmega A) 0 ask none m.st.input (restFront J m) =
      (ProofFile.Honest.K14.jobOmega A).data { input := ask mb.st.input, heard := mb.st.heard, own := () } 0 := by
  have hlen : m.st.heard.length ≤ n := by
    rw [hm]
    exact List.length_take_le _ _
  show (ProofFile.Honest.K14.jobOmega A).data
    ⟨ask m.st.input, m.st.heard.take (m.st.heard.length - firstLen J.p.nums.stages), ()⟩ 0 = _
  rw [hi]
  refine congrFun (data_same (ProofFile.Honest.K14.jobOmega_readsBelow A) _ _ _ ?_) 0
  rw [List.take_take, Nat.min_eq_left (by omega), hm, hb, List.take_take, List.take_take,
    Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]

/-- **The clause on the first opening's columns, at a run, at the test on G_omega.** Premises, sorted: on the run: hR, hrun, hc, S; on the filling: hg, hgO; on the book: hb, and e₂, hf, ho, hst, hmem on the first part's own coins; public at the plan: the rest. -/
theorem trees_at_run_omega {Xi W₀ Rc Ky Tr X₀ Y Pb : Type} {F : FileDescription Xi} {Bk : ProofFile.Honest.ProverCoinCounts}
    {P : ProofFile.Honest.Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : ProofFile.Honest.Coins Bk}
    {ρ : ProofFile.Honest.Draws} {R : ProofFile.Honest.Ready W₀ Rc Xi Ky Tr X₀ Y} {r : ProofFile.Honest.RunC F}
    (hpl : F.planOk = true) (hR : ProofFile.Honest.ready F Bk P w₀ rc x k = .ok R)
    (hrun : ProofFile.Honest.runC F Bk P w₀ rc x k ρ = .ok r)
    (A : ProofFile.Honest.K14.SendPub) (p : P12) (door : ProofFile.Honest.Common W₀ Rc Ky → Front X₀ → T12)
    (weights : ProofFile.Honest.Common W₀ Rc Ky → Weights) (rand : ProofFile.Honest.Common W₀ Rc Ky → TableRand)
    (J : TestJob (ProofFile.Honest.Common W₀ Rc Ky) X₀)
    (hJ : J = (jobAtOmega A p door weights rand none).toRun.toTest) (Js : SimJob Pb)
    (σ : ProofFile.Honest.Side F.S₂ F.Cl Empty (ProofFile.Honest.Common W₀ Rc Ky) X₀ Pb) (hσ : σ.block.place = p.place)
    (pre' t' : List (Block F.S₂ F.Cl))
    (S : ProofFile.Honest.StandsAt F.shared.blocksInOrder R.shared σ (restMember J Js : ProofFile.Honest.Member Empty _ _ _).guarded
      pre' t' (firstLen J.p.nums.stages))
    (hc : r.called ⟨σ.block.place, 1⟩ = true)
    (hg : (P.shared.find? fun g => g.place == σ.block.place) =
      some (proverSideOfProximityTest J : ProofFile.Honest.Placed Empty _ _).needsField)
    (hlaid : σ.block.rounds.zip σ.block.oracles = J.laid)
    (preO tO : List (Block F.S₂ F.Cl)) (bO : Block F.S₂ F.Cl)
    (hcutO : F.shared.blocksInOrder = preO ++ bO :: tO) (hpO : bO.place = ProofFile.Honest.K14.sendPlace 5)
    (hgO : (P.shared.find? fun g => g.place == bO.place) = some ⟨bO.place,
      [(ProofFile.Honest.K14.liftSend (askOf A weights rand) (ProofFile.Honest.K14.sendingPart (ProofFile.Honest.K14.jobOmega A)) :
        Part Empty (ProofFile.Honest.Common W₀ Rc Ky) X₀)]⟩)
    (hdO : SendDeclared bO (ProofFile.Honest.K14.jobOmega A))
    (hinO : (preO.flatMap (·.rounds)).length + 2 ≤ (pre'.flatMap (·.rounds)).length)
    (hb : bookCutsOmega Bk A p = true) (hQ : sendingsFit A.P = true) (hcf : colFitsOmega A p = true)
    (hw0 : widthFits (ProofFile.Honest.K14.jobOmega A) 0 = true) (hw1 : widthFits (ProofFile.Honest.K14.jobOmega A) 1 = true)
    (hat : A.atPoint < (preO.flatMap (·.rounds)).length)
    (e₂ : ProofFile.Honest.Ahead) (hf : (ProofFile.Honest.carryE Bk ⟨J.p.place, 0 + 1⟩)[J.members.length]? = some e₂)
    (ho : e₂.owner = ⟨J.p.place, 0⟩) (hst : e₂.start = ⟨0, 0⟩)
    (hmem : ∀ t, t < J.members.length → ∃ a a', (ProofFile.Honest.carryE Bk ⟨J.p.place, 0⟩)[t]? = some a ∧
      (ProofFile.Honest.carryE Bk ⟨J.p.place, 0 + 1⟩)[t]? = some a' ∧ a.owner = a'.owner ∧ a.start = a'.start ∧
      a.count = a'.count)
    (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (D : ℕ → Fmt.Drawn)
    (T : FirstTies J s next rest D
      ((ρ.shared.drop (pre'.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages)))
    (hk : s.h ≤ s.k)
    (hrows : ∀ (w : ProofFile.Honest.Common W₀ Rc Ky) (fr : Front X₀) (mem mem' : ℕ → Stretch),
      (∀ t, t < J.members.length → mem t = mem' t) →
      μOf (H2K.Pub.sgOf s) (J.rows₀ w fr mem) = μOf (H2K.Pub.sgOf s) (J.rows₀ w fr mem'))
    (os : List (Fmt.Shape × Fmt.TreeSource))
    (hsrc : os.map (fun o => ProofFile.Honest.srcOf 1 o.2) =
      [(1, Johnson.G.OfPlan.rootsOf (preO.flatMap (·.rounds)) + 0),
       (1, Johnson.G.OfPlan.rootsOf (preO.flatMap (·.rounds)) + 1),
       (1, Johnson.G.OfPlan.rootsOf (pre'.flatMap (·.rounds)))])
    (hdep : [depthOf p 0, depthOf p 1, (p.nums.stages.headD default).Z.a] = os.map (·.1.a))
    (st : List (ℕ × ℕ × List UInt64)) :
    ∀ m ca, ProofFile.Honest.midSharedAtW F Bk P w₀ rc x k ρ ⟨σ.block.place, 1⟩ = .ok (some m) →
      ProofFile.Honest.carriedAt Bk k 1 ⟨σ.block.place, 1⟩
        (restPart J : Part Empty (ProofFile.Honest.Common W₀ Rc Ky) X₀).needsField = .ok ca →
      (J.trees₀ m.st.input (restFront J m) (ProofFile.Honest.K12.stretches _ ca)
          (rowsAt J (ProofFile.Honest.K12.stretches _ ca) m)).map (·.1) = os.map (·.1.a) ∧
        ∀ (i : ℕ) (o' : Fmt.Shape × Fmt.TreeSource) (Tr' : Tree), os[i]? = some o' →
          (J.trees₀ m.st.input (restFront J m) (ProofFile.Honest.K12.stretches _ ca)
            (rowsAt J (ProofFile.Honest.K12.stretches _ ca) m))[i]? = some Tr' →
          ∃ cols, (r.run.beforeAt st ⟨σ.block.place, 1⟩).treeCols
                (ProofFile.Honest.srcOf 1 o'.2).1 (ProofFile.Honest.srcOf 1 o'.2).2 = some cols ∧
            ∀ q ∈ cols, q.2 = Tr'.2 q.1 := by
  intro m ca hm hca
  subst hJ
  have hfr : (jobAtOmega A p door weights rand none).toRun.toTest.fresh = none := rfl
  refine ⟨by
    rw [trees₀_many]
    exact hdep, ?_⟩
  -- the stand in front of the second part
  obtain ⟨m', hm', -, hheard, -, -, -, -, -, -, -⟩ :=
    frame_at_run hpl hR hrun σ _ pre' t' _ _ S rfl hc st
  obtain rfl : m = m' := Option.some.inj (Except.ok.inj (hm.symm.trans hm'))
  obtain ⟨a₂, zN, m'', ha, hzN, -, hzm, hm''⟩ := played_at_run hpl hR hrun σ _ pre' t' _ _ S rfl hc
  obtain rfl : m = m'' := Option.some.inj (Except.ok.inj (hm.symm.trans hm''))
  have hinp := (ProofFile.Honest.walk_mid ha hzN hzm).1
  -- what the second part is lent
  obtain ⟨c, hl, rfl⟩ := ProofFile.Honest.exMap_ok (show (ProofFile.Honest.lendPart Bk (Bk.rowsOf 1) (k.look 1) ⟨σ.block.place, 1⟩
          (restPart (jobAtOmega A p door weights rand none).toRun.toTest :
            Part Empty (ProofFile.Honest.Common W₀ Rc Ky) X₀).needsField).map (·.2.2) = .ok ca from hca)
  have hl' : ProofFile.Honest.lendPart Bk (Bk.rowsOf 1) (k.look 1) ⟨σ.block.place, 1⟩
      (restPart (jobAtOmega A p door weights rand none).toRun.toTest :
        Part Empty (ProofFile.Honest.Common W₀ Rc Ky) X₀) = .ok c := by
    obtain ⟨g1, g2, g3⟩ := ProofFile.Honest.lendPart_ok hl
    have ow0 := lendPart_own hl
    exact lendPart_of_parts g1 ow0 g2 g3
  rw [hσ, ProofFile.Honest.look_shared] at hl'
  -- the sending, as played
  obtain ⟨dO₀, dO₁, osO, rO, oO, fO₀, fO₁, -⟩ := hdO.rounds
  obtain ⟨aO, zO, mO, cO, xO₀, xO₁, sO, pO, -, eO, lO, -, -, qO, -, -⟩ :=
    sending_at_run hpl hR hrun σ _ pre' t' _ S hc
    preO bO tO hcutO (ProofFile.Honest.K14.jobOmega A) (askOf A weights rand) hgO dO₀ dO₁ osO (by rw [rO, oO]; rfl) fO₀ fO₁
    (by omega)
  have hOm : (ProofFile.Honest.sharedLook Bk k.shared ⟨ProofFile.Honest.K14.sendPlace 5, 0⟩).2.cut ⟨0, 0⟩
      (takesOf (ProofFile.Honest.K14.jobOmega A).Q.codes (ProofFile.Honest.K14.jobOmega A).Q.sent (ProofFile.Honest.K14.jobOmega A).sort) = some cO.1.1 := by
    rw [← hpO]
    exact own_of_lendPart (ProofFile.Honest.lendRow_cons_ok lO).1
  obtain ⟨T0, hT0, col0⟩ := col_sent (ProofFile.Honest.K14.jobOmega A)
    ((ProofFile.Honest.K14.jobOmega A).rows ⟨askOf A weights rand mO.st.input, mO.st.heard, ()⟩ (coinsE cO.1.1).toArray) 0 hw0
  obtain ⟨T1, hT1, col1⟩ := col_sent (ProofFile.Honest.K14.jobOmega A)
    ((ProofFile.Honest.K14.jobOmega A).rows ⟨askOf A weights rand mO.st.input, mO.st.heard, ()⟩ (coinsE cO.1.1).toArray) 1 hw1
  have f0 := tree_of_round_at_run hpl hR hrun σ _ pre' t' _ _ S rfl hc st preO bO tO hcutO
    (by omega) _ qO 0 (some T0) (by
      show ((sendTablesAt (ProofFile.Honest.K14.jobOmega A) cO.1.1 _ _).map some)[0]? = _
      rw [List.getElem?_map]
      exact congrArg (Option.map some) hT0)
  have f1 := tree_of_round_at_run hpl hR hrun σ _ pre' t' _ _ S rfl hc st preO bO tO hcutO
    (by omega) _ qO 1 (some T1) (by
      show ((sendTablesAt (ProofFile.Honest.K14.jobOmega A) cO.1.1 _ _).map some)[1]? = _
      rw [List.getElem?_map]
      exact congrArg (Option.map some) hT1)
  -- "the same vector"
  have kO := ProofFile.Honest.walk_laid_drawn _ _ _ aO zO pO
  rw [ProofFile.Honest.start_laid sO, List.map_nil, List.nil_append] at kO
  have hhO := ProofFile.Honest.walk_hears _ _ _ _ aO zO (ProofFile.Honest.start_hears sO) pO mO eO
  rw [kO] at hhO
  have hLen : m.st.heard.length = (pre'.flatMap (·.rounds)).length +
      firstLen (jobAtOmega A p door weights rand none).toRun.toTest.p.nums.stages := by
    rw [hheard, ProofFile.Honest.walk_len _ _ _ a₂ zN hzN, List.length_take]
    exact Nat.min_eq_left (Nat.le_trans (Nat.le_add_right _ _) S.fits)
  have hv := same_vector_omega A (askOf A weights rand) (jobAtOmega A p door weights rand none).toRun.toTest
    m mO ρ.shared _ _ hheard (hhO.trans (List.nil_append _))
    ((ProofFile.Honest.walk_mid sO pO eO).1.trans hinp.symm) hat (by omega)
  -- the first part's own table
  obtain ⟨c₀, m₀, m₂, y, hl₀, hm₂, hplay, hy, -, -, hy1⟩ :=
    first_play_guarded hpl _ hR σ _ pre' t' S hg hlaid hrun hc
  obtain rfl : m = m₂ := Option.some.inj (Except.ok.inj (hm.symm.trans hm₂))
  obtain ⟨q₀, q₁, Tb, h0, tb0, h1, tb1, hcol⟩ := own_table_played _ hfr σ.block.name ⟨σ.block.place, 0⟩ none
    s next rest m₀ D _ T hk c₀.1 y hplay
  have hnp := T.stages
  have hn2 : firstLen (jobAtOmega A p door weights rand none).toRun.toTest.p.nums.stages = 2 + s.k := by
    rw [hnp]
    rfl
  have hNn : (pre'.flatMap (·.rounds)).length + 1 <
      (pre'.flatMap (·.rounds)).length +
        firstLen (jobAtOmega A p door weights rand none).toRun.toTest.p.nums.stages := by omega
  have hy0 : r.run.played.2.1[(pre'.flatMap (·.rounds)).length]? = some q₀ := by
    rw [hy1, List.getElem?_drop, Nat.add_zero, List.getElem?_take_of_lt (by omega)] at h0
    exact h0
  have hy1' : r.run.played.2.1[(pre'.flatMap (·.rounds)).length + 1]? = some q₁ := by
    rw [hy1, List.getElem?_drop, List.getElem?_take_of_lt hNn] at h1
    exact h1
  have Q := (F.planOk_ok).1 hpl
  obtain ⟨-, -, -, -, -, s1, s2, s3⟩ := ProofFile.Honest.ready_ok hR
  obtain ⟨-, l2, -⟩ := ProofFile.Honest.runC_laidAs hrun hR (ProofFile.Honest.steps_shaped s1 Q.blocks₁)
    (ProofFile.Honest.steps_shaped s2 Q.blocks₂) (ProofFile.Honest.steps_shaped s3 Q.blocks₃)
  have hsh : (r.run.played.2.1.take ((pre'.flatMap (·.rounds)).length +
        firstLen (jobAtOmega A p door weights rand none).toRun.toTest.p.nums.stages)).map (·.tables.length) =
      (R.shared.take ((pre'.flatMap (·.rounds)).length +
        firstLen (jobAtOmega A p door weights rand none).toRun.toTest.p.nums.stages)).map (·.oracles.length) := by
    rw [List.map_take, List.map_take, ProofFile.Honest.laidAs_tables l2]
  have hfront := tables_in_front hpl hR pre' σ.block t' S.cut _ (Nat.le_add_right _ _) _ hsh
  have hq' : (r.run.played.2.1.take ((pre'.flatMap (·.rounds)).length +
      firstLen (jobAtOmega A p door weights rand none).toRun.toTest.p.nums.stages))[(pre'.flatMap (·.rounds)).length + 1]? =
      some q₁ := by
    rw [List.getElem?_take_of_lt hNn]
    exact hy1'
  have htab := tab_at_round _ _ 0 q₁ hq' (by rw [tb1]; exact Nat.zero_lt_one)
  have hsum : (((r.run.played.2.1.take ((pre'.flatMap (·.rounds)).length +
        firstLen (jobAtOmega A p door weights rand none).toRun.toTest.p.nums.stages)).take
        ((pre'.flatMap (·.rounds)).length + 1)).map (·.tables.length)).sum =
      Johnson.G.OfPlan.rootsOf (pre'.flatMap (·.rounds)) := by
    have hq0 : (r.run.played.2.1.take ((pre'.flatMap (·.rounds)).length +
        firstLen (jobAtOmega A p door weights rand none).toRun.toTest.p.nums.stages))[(pre'.flatMap (·.rounds)).length]? =
        some q₀ := by
      rw [List.getElem?_take_of_lt (by omega)]
      exact hy0
    rw [List.take_add_one, hq0, List.map_append, List.sum_append, hfront]
    simp [tb0]
  rw [hsum, tb1, Nat.add_zero] at htab
  have fT := treeCols_at_run hpl hR hrun σ _ pre' t' _ _ S rfl hc st (Johnson.G.OfPlan.rootsOf (pre'.flatMap (·.rounds)))
  rw [htab] at fT
  -- the first part's coins against what the second carries
  have hcar := carried_of_row k σ.block.place _ _ c₀ hl₀
  have ecar : c.2.2 = c₀.2.1.2.2 := Except.ok.inj (hca.symm.trans hcar)
  have hplace : (jobAtOmega A p door weights rand none).toRun.toTest.p.place = σ.block.place := hσ.symm
  rw [← hplace] at hl₀
  obtain ⟨g1, g2⟩ := ProofFile.Honest.lendRow_cons_ok hl₀
  obtain ⟨g3, -⟩ := ProofFile.Honest.lendRow_cons_ok g2
  obtain ⟨-, -, k1⟩ := ProofFile.Honest.lendPart_ok g1
  obtain ⟨-, -, k2⟩ := ProofFile.Honest.lendPart_ok g3
  have ow := lendPart_own g1
  have hs0 : (jobAtOmega A p door weights rand none).toRun.toTest.s₀ = s := by
    unfold TestJob.s₀
    rw [hnp]
    rfl
  have Ag := agree_job (V := Empty) _ hfr Bk (ProofFile.Honest.sharedLook Bk k.shared) c₀.1 c₀.2.1 ow k1 k2
    m₀.st.input (frontBy m₀ 0) e₂ hf ho hst hmem (by rw [hs0]; exact hrows _ _)
  rw [hs0] at Ag
  have Ag' := agree_carried (V := Empty) _ _ _ _ _ c₀.2.1 Ag
  have hfreshEq : ∀ y', freshCol (H2K.Pub.sgOf s) ((jobAtOmega A p door weights rand none).toRun.toTest.first
        m₀.st.input (frontBy m₀ 0)
        (firstRd (V := Empty) (jobAtOmega A p door weights rand none).toRun.toTest c₀.1)) y' =
      freshCol (H2K.Pub.sgOf s) (rowsAt (jobAtOmega A p door weights rand none).toRun.toTest
        (ProofFile.Honest.K12.stretches _ c.2.2) m) y' := by
    intro y'
    rw [ecar]
    exact freshCol_agree _ s hs0 _ _ _ _ _ _ Ag'.hide (Ag'.tails hfr) y'
  -- the three trees
  have hlen3 : os.length = 3 := by
    have g := congrArg List.length hsrc
    rw [List.length_map] at g
    exact g
  obtain ⟨a, b, d, hab⟩ := List.length_eq_three.1 hlen3
  rw [hab] at hsrc
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsrc
  obtain ⟨sa, sb, sd⟩ := hsrc
  intro i o' Tr' hoi hT
  rw [hab] at hoi
  match i, hoi, hT with
  | 0, hoi, hT =>
    obtain rfl : a = o' := Option.some.inj hoi
    rw [sa]
    refine ⟨_, f0, fun q hq => ?_⟩
    obtain ⟨y', -, rfl⟩ := List.mem_map.1 hq
    show T0.col y' = Tr'.2 y'
    have e := tree0_lent_Omega Bk (Bk.rowsOf 1) (ProofFile.Honest.sharedLook Bk k.shared) A p door weights rand none
      cO.1.1 hOm hQ m.st.input _ _ y' c hl' hb hcf hv
    rw [List.getD_eq_getElem?_getD] at e
    exact (col0 y').trans (e.symm.trans
      (congrArg (fun z : Option Tree => (z.getD (0, fun _ => [])).2 y') hT))
  | 1, hoi, hT =>
    obtain rfl : b = o' := Option.some.inj hoi
    rw [sb]
    refine ⟨_, f1, fun q hq => ?_⟩
    obtain ⟨y', -, rfl⟩ := List.mem_map.1 hq
    show T1.col y' = Tr'.2 y'
    have e := tree1_lent_Omega Bk (Bk.rowsOf 1) (ProofFile.Honest.sharedLook Bk k.shared) A p door weights rand none
      cO.1.1 hOm hQ m.st.input (restFront (jobAtOmega A p door weights rand none).toRun.toTest m)
      ⟨askOf A weights rand mO.st.input, mO.st.heard, ()⟩ y' c hl' hb hcf
    rw [List.getD_eq_getElem?_getD] at e
    exact (col1 y').trans (e.symm.trans
      (congrArg (fun z : Option Tree => (z.getD (0, fun _ => [])).2 y') hT))
  | 2, hoi, hT =>
    obtain rfl : d = o' := Option.some.inj hoi
    rw [sd]
    refine ⟨_, fT, fun q hq => ?_⟩
    obtain ⟨y', -, rfl⟩ := List.mem_map.1 hq
    show Tb.col y' = Tr'.2 y'
    rw [trees₀_many] at hT
    obtain rfl : _ = Tr' := Option.some.inj hT
    show Tb.col y' = wordsAt (symOf (jobAtOmega A p door weights rand none).s₀ _ y')
      (((List.range (2 ^ (jobAtOmega A p door weights rand none).s₀.h)).map fun r => (⟨.fresh, r, false⟩ : Sel)) ++ [])
    rw [List.append_nil, fresh_col_eq, hcol]
    have hb0 : (jobAtOmega A p door weights rand none).s₀ = s := hs0
    rw [hb0]
    exact hfreshEq y'
  | _ + 3, hoi, _ => cases hoi

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.trees_at_run_omega
#print axioms ProofFile.Honest.K12.Light.lendPart_of_parts
#print axioms ProofFile.Honest.K12.Light.same_vector_omega
#print axioms ProofFile.Honest.K12.Light.fresh_col_eq
#print axioms ProofFile.Honest.K12.Light.length_freshCol
#print axioms ProofFile.Honest.K12.Light.canonW_freshCol
#print axioms ProofFile.Honest.K12.Light.msgAt_zero_tables
#print axioms ProofFile.Honest.K12.Light.msgAt_one_tables
#print axioms ProofFile.Honest.K12.Light.own_table_played
