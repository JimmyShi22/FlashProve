-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/M1/BudTestO.lean: what the row of the proximity test on G_omega owes to `BudDebts`, at every due list of challenges, under
the head, in the road of Honest/K12/Sim/AloneAtU.lean. `budDebts_one_row_both` (Honest/K12/Sim/DebtAtO.lean) names a premise `hold`
that CANNOT BE MET HERE: the first fold sends its own table, so the job's third tree is the chain's tree number 7, which is
not below the 7 trees in front (Honest/K12/Sim/BudOwn.lean's head says as much of an earlier case). What the proof needs is
less: that no tree of the job has the number of a tree that the second part sends. So `own_reads_tr`, `bud_own`,
`bud_rest_file` and `debt_rest` are taken here at that weaker premise.

  `own_reads_apart`, `bud_own_apart`, `bud_rest_apart`   the library's three at the weaker premise

  `frontWO`, `behindWO`, `aloneWO`, `srcsO`   the written rounds in front and behind; `aloneB` in written letters; the sources
      of the test's two first trees
  `roots_WO`, `opens_WO`, `far_WO`, `alone_WO`, `apart_WO`   closed facts, by Lean's kernel
  `no_WO`        the tests can say no
  `cut_WO`, `alone_is_WO`, `premises_at_O`   from the written description to the proof file's own
  `budOwed₂_at_O`   **`BudOwed₂` at a list at the test's place with the two parts and the bound `budBoth`**

Limits. The written values are WP's; that the proof file's description has them is `decl_at_laid`'s and
`alike_shared_at_laid`'s word. A run of one request. No property of the protocol is claimed: nothing is said on its soundness,
completeness, binding or hiding.
-/
import Johnson.M1.BudShareCore
import Johnson.Desc.ProofFile.Honest.K12.Sim.DebtAtO
import Johnson.Desc.ProofFile.Honest.K12.Sim.AloneAtU

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK
open Johnson.Prover.Link
open OnBytes.LinkSim.AtText (oNext)
open ProofFile.Honest.K12.Light

variable {W X Pb : Type}

/-- `own_reads_tr`, where no tree of the job has the number of the tree that round r sends. -/
theorem own_reads_apart (J : TestJob W X) (decls : List Fmt.DeclaredRound) (depths : List ℕ)
    (src₀ : ℕ → Fmt.TreeSource) (sent chain firstTree : ℕ) (F : OpensFit J decls depths src₀ sent)
    (s : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: rest)
    (stored : ℕ → ℕ → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (VerifiableInference.Desc.Place × Table)) (D : ℕ → Fmt.Drawn)
    (Rs : List Fmt.Drawn) (hD : ∀ n (h : n < Rs.length), Rs[n] = D n) (r : ℕ)
    (hr : (depthAt J r).isSome = true)
    (apart : ∀ k, k < depths.length → ∀ n, srcOf chain (src₀ k) = (chain, n) → n ≠ sent + sentBefore J r) :
    ∀ q ∈ readsOf chain firstTree stored tree decls Rs,
      q.src = some (chain, sent + sentBefore J r) → q.pos ∈ openedTr D rest s 1 (r - 1) := by
  intro q hq hsrc
  obtain ⟨x', hx', h1, h2⟩ := reads_plan chain firstTree stored tree D decls Rs 0 F.stored
    (fun n hn => by rw [Nat.zero_add]; exact hD n hn) q hq
  rw [F.opens] at hx'
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hx'
  rw [hsrc] at h1
  have h1' : (chain, sent + sentBefore J r) = srcOf chain (srcBy J src₀ sent x.2.2) :=
    Option.some.inj h1
  have hx0 := hx
  unfold opensTest at hx
  rw [hst] at hx
  rcases opens_tr D rest s 1 (frontTrees depths) x hx with ⟨y, hy, rfl⟩ | ⟨r', hr', hle, he⟩
  · exfalso
    unfold frontTrees at hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    have hk := (F.olds _ hx0 z.2 rfl).1
    exact apart z.2 hk _ h1'.symm rfl
  · rw [hr'] at h1'
    have e : sent + sentBefore J r = sent + sentBefore J r' := congrArg Prod.snd h1'
    have hs' := (F.senders x hx0 r' hr').2
    obtain rfl := sentBefore_inj J r r' hr hs' (by omega)
    rw [← he]
    exact h2

/-- `bud_own`, at the same premise at the rounds that the second part sends at. -/
theorem bud_own_apart (J : TestJob W X) (decls : List Fmt.DeclaredRound) (depths : List ℕ)
    (src₀ : ℕ → Fmt.TreeSource) (sent chain firstTree : ℕ) (F : OpensFit J decls depths src₀ sent)
    (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = s :: next :: rest) (hk : s.k = (H2K.Pub.sgOf s).h + (H2K.Pub.sgOf s).g)
    (apart : ∀ i, (depthAt J (firstLen J.p.nums.stages + i)).isSome = true →
      ∀ k, k < depths.length → ∀ n, srcOf chain (src₀ k) = (chain, n) →
        n ≠ sent + sentBefore J (firstLen J.p.nums.stages + i))
    (stored : ℕ → ℕ → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (VerifiableInference.Desc.Place × Table))
    (ds₁ ds : List Fmt.Drawn) (h1 : ds₁.length = firstLen J.p.nums.stages) (roots : List ℕ)
    (hroots : ∀ i, i < roots.length → roots.getD i 0 =
      if (depthAt J (firstLen J.p.nums.stages + i)).isSome = true then 1 else 0) :
    budOpened J.p.nums.stages 1 ds
      (asksFrom (fun m => ((readsOf chain firstTree stored tree decls (ds₁ ++ ds)).filter fun q =>
        q.src == some (chain, m)).map (·.pos)) roots
        (sent + sentBefore J (firstLen J.p.nums.stages))) := by
  refine bud_of_asksFrom _ ds _ roots _ fun i hi q hq => ?_
  have hil : i < roots.length := by
    by_contra hc
    rw [List.getD_eq_default _ _ (by omega)] at hi
    omega
  have hsome : (depthAt J (firstLen J.p.nums.stages + i)).isSome = true := by
    have h := hroots i hil
    by_contra hc
    rw [if_neg hc] at h
    omega
  rw [Nat.add_assoc, sent_sum J _ roots hroots i (Nat.le_of_lt hil)] at hq
  obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
  obtain ⟨hm, hs⟩ := List.mem_filter.1 hq'
  have h := own_reads_apart J decls depths src₀ sent chain firstTree F s (next :: rest) hst stored
    tree (fun n => (ds₁ ++ ds).getD n noDraw) (ds₁ ++ ds)
    (fun n hn => (List.getD_eq_getElem _ _ hn).symm) (firstLen J.p.nums.stages + i) hsome
    (apart i hsome) q' hm (eq_of_beq hs)
  have hn₀ : firstLen J.p.nums.stages = 2 + s.k := by rw [hst]; rfl
  have e : firstLen J.p.nums.stages + i - 1 = 1 + ((H2K.Pub.sgOf s).h + (H2K.Pub.sgOf s).g) + i := by
    rw [hn₀, hk]
    omega
  rw [e] at h
  have hc : openedTr (laterOf J.p.nums.stages ds) (next :: rest) s 1
      (1 + ((H2K.Pub.sgOf s).h + (H2K.Pub.sgOf s).g) + i) =
      openedTr (fun n => (ds₁ ++ ds).getD n noDraw) (next :: rest) s 1
        (1 + ((H2K.Pub.sgOf s).h + (H2K.Pub.sgOf s).g) + i) :=
    openedTr_congr _ _ (next :: rest) s 1 _ fun n hn => by
      unfold oNext at hn
      show ds.getD (n - firstLen J.p.nums.stages) noDraw = (ds₁ ++ ds).getD n noDraw
      rw [List.getD_append_right _ _ _ _ (by rw [h1, hn₀, hk]; omega), h1]
  have hd : J.p.nums.stages.drop 1 = next :: rest := by rw [hst]; rfl
  have hh : J.p.nums.stages.headD default = s := by rw [hst]; rfl
  rw [hd, hh, hc]
  exact h

/-- `bud_rest_file`, at the same premise. -/
theorem bud_rest_apart {Xi V : Type} {F : VerifiableInference.Desc.FileDescription Xi} (J : TestJob W X) (Js : SimJob Pb)
    (pre t : List (VerifiableInference.Desc.Block F.S₂ F.Cl)) (b : VerifiableInference.Desc.Block F.S₂ F.Cl)
    (hcut : F.shared.blocksInOrder = pre ++ b :: t) (depths : List ℕ) (src₀ : ℕ → Fmt.TreeSource) (sent : ℕ)
    (O : OpensFit J b.rounds depths src₀ sent) (s next : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: next :: rest)
    (hk : s.k = (H2K.Pub.sgOf s).h + (H2K.Pub.sgOf s).g) (hT : tablesFitB J = true)
    (apart : ∀ i, (depthAt J (firstLen J.p.nums.stages + i)).isSome = true →
      ∀ k, k < depths.length → ∀ n, srcOf 1 (src₀ k) = (1, n) →
        n ≠ sent + sentBefore J (firstLen J.p.nums.stages + i))
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
  refine bud_sub _ _ _ _ _ _ (bud_own_apart J b.rounds depths src₀ sent 1 0 O s next
    rest hst hk apart (fun _ _ => none) (fun _ => none) _ _ h1 _
    fun i hi => roots_fit J hT _ i hi) fun i hi q hq => ?_
  rw [List.take_append_drop]
  have hil : i < ((restMember (V := V) (Pb := Pb) J Js).rounds.map (·.2.length)).length := by
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

end ProofFile.Honest.K12

namespace ProofFile.Honest.K12.Light.AtO
open VerifiableInference.Desc (FileDescription Block Place Alike₂ alike₂_rounds)
open VerifiableInference.Desc.K12 (P12)
open P2Law.ProofPlan (WP declProofFull)
open H2K.Member (piOFull)
open Johnson.G.OfPlan (rootsOf)
open ProofFile.Honest.K14 (decl_at_laid alike_shared_at_laid)
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest.K12.Light.AtU (places_WU)
open Johnson.M1 (BudOwed₂)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl} {pO : P12}

/-- The written declared rounds in front of the test on G_omega in the shared chain. -/
def frontWO : List Fmt.DeclaredRound := (WP.shared.blocksInOrder.take 10).flatMap (·.rounds)

/-- Those behind it. -/
def behindWO : List Fmt.DeclaredRound := (WP.shared.blocksInOrder.drop 11).flatMap (·.rounds)

/-- `aloneB` (ReadsInBlock.lean) in written letters. -/
def aloneWO (k : ℕ) : Bool :=
  (openedOf 0 declProofFull.1 ++ openedOf 1 frontWO ++ openedOf 1 behindWO ++
    openedOf 2 declProofFull.2.2).all (·.1 != (1, k))

/-- The sources of the test's first trees: two of the chain's, and the own table, which the test itself sends. -/
def srcsO : List Fmt.TreeSource := [.own 1, .own 2, .own 7]

/-! ## 1 By an evaluation in Lean's kernel, at written values -/

set_option maxRecDepth 1000000 in
theorem roots_WO : rootsOf frontWO = 7 := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem opens_WO : (WP.shared.blocksInOrder[10]?).map (fun b =>
             opensFitB true piOFull.nums.stages b.rounds [22, 13, 13] srcsO 7) = some true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem far_WO : (none :: depths true piOFull.nums.stages).length ≤
    firstLen piOFull.nums.stages + 40 := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem alone_WO : (List.range 40).all (fun i =>
    !(ProofFile.Honest.K12.depthOf true piOFull.nums.stages (firstLen piOFull.nums.stages + i)).isSome ||
      aloneWO (7 + ((List.range (firstLen piOFull.nums.stages + i)).filter fun j =>
        (ProofFile.Honest.K12.depthOf true piOFull.nums.stages j).isSome).length)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **The trees that the second part sends stand behind the job's three**: each has a number above 7. -/
theorem apart_WO : (List.range 40).all (fun i =>
    !(ProofFile.Honest.K12.depthOf true piOFull.nums.stages (firstLen piOFull.nums.stages + i)).isSome ||
      decide (7 < 7 + ((List.range (firstLen piOFull.nums.stages + i)).filter fun j =>
        (ProofFile.Honest.K12.depthOf true piOFull.nums.stages j).isSome).length)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The tests can say no: with one argument of `opens_WO` turned. -/
theorem no_WO : (WP.shared.blocksInOrder[10]?).map (fun b =>
             [opensFitB true piOFull.nums.stages b.rounds [22, 13, 13] srcsO 8,
               opensFitB true piOFull.nums.stages b.rounds [22, 12, 13] srcsO 7,
               opensFitB true piOFull.nums.stages b.rounds [22, 13, 13] [.own 0, .own 2, .own 7] 7,
               opensFitB false piOFull.nums.stages b.rounds [22, 13, 13] srcsO 7]) =
    some [false, false, false, false] := by
  decide +kernel

/-! ## 2 From the written description to the proof file's own, under the head -/

theorem cut_WO (h : P5J.AtMg o Z D r₀ Zp Np cF)
    (pre t : List (Block (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl))
    (b : Block (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl)
    (hcut : (P5J.F0T o Zp Np cF).shared.blocksInOrder = pre ++ b :: t)
    (hb : b.place = ⟨2, none, 10, .K12⟩) :
    pre.flatMap (·.rounds) = frontWO ∧ t.flatMap (·.rounds) = behindWO ∧
      (WP.shared.blocksInOrder[10]?).map (·.rounds) = some b.rounds := by
  have A := alike_shared_at_laid h.scope h.laid
  rw [hcut] at A
  have A1 := List.forall₂_take_append _ pre (b :: t) A
  have A2 := List.forall₂_drop_append _ pre (b :: t) A
  obtain ⟨bW, tl, hbW, htl, hd⟩ := List.forall₂_cons_right_iff.1 A2
  have hget : WP.shared.blocksInOrder[pre.length]? = some bW := by
    have e := congrArg List.head? hd
    rw [List.head?_drop] at e
    exact e
  have hpl : (WP.shared.blocksInOrder.map (·.place))[pre.length]? = some ⟨2, none, 10, .K12⟩ := by
    rw [List.getElem?_map, hget]
    exact congrArg some (hbW.1.trans hb)
  rw [places_WU] at hpl
  have hlt : pre.length < 12 := (List.getElem?_eq_some_iff.1 hpl).1
  have only : ∀ n, n < 12 → ([⟨2, none, 0, .frame⟩, ⟨2, none, 1, .K14⟩, ⟨2, none, 2, .K1⟩,
      ⟨2, none, 3, .K14⟩, ⟨2, none, 4, .K14⟩, ⟨2, none, 5, .K1⟩, ⟨2, none, 6, .K14⟩,
      ⟨2, none, 7, .K14⟩, ⟨2, none, 8, .K14⟩, ⟨2, none, 9, .K12⟩, ⟨2, none, 10, .K12⟩,
      ⟨2, none, 11, .frame⟩] : List Place)[n]? = some ⟨2, none, 10, .K12⟩ → n = 10 := by decide
  have h10 : pre.length = 10 := only _ hlt hpl
  rw [h10] at A1 hd hget
  have h11 : WP.shared.blocksInOrder.drop 11 = tl := by
    have e := congrArg List.tail hd
    rw [List.tail_drop] at e
    exact e
  refine ⟨(alike₂_rounds _ _ A1).symm, ?_, ?_⟩
  · unfold behindWO
    rw [h11]
    exact (alike₂_rounds _ _ htl).symm
  · rw [hget]
    exact congrArg some hbW.2.1

theorem alone_is_WO (h : P5J.AtMg o Z D r₀ Zp Np cF)
    (pre t : List (Block (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl))
    (b : Block (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl)
    (hcut : (P5J.F0T o Zp Np cF).shared.blocksInOrder = pre ++ b :: t)
    (hb : b.place = ⟨2, none, 10, .K12⟩) (k : ℕ) :
    aloneB (P5J.F0T o Zp Np cF) pre t k = aloneWO k := by
  obtain ⟨e1, e2, -⟩ := cut_WO h pre t b hcut hb
  unfold aloneB aloneWO
  rw [decl_at_laid h.scope h.laid, e1, e2]

/-- **The premises hold at the proof file's own description, under the head.** -/
theorem premises_at_O (h : P5J.AtMg o Z D r₀ Zp Np cF) (hO : (fourOf Np).O = some pO) {W X : Type}
    (J : TestJob W X) (hJ : J.p = pO) (hfr : J.fresh.isNone = true)
    (pre t : List (Block (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl))
    (b : Block (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl)
    (hcut : (P5J.F0T o Zp Np cF).shared.blocksInOrder = pre ++ b :: t) (hb : b.place = J.p.place) :
    OpensFit J b.rounds [22, 13, 13] (fun k => srcsO.getD k (.own 0))
        (rootsOf (pre.flatMap (·.rounds))) ∧
      (∀ i, (depthAt J (firstLen J.p.nums.stages + i)).isSome = true →
        ∀ k, k < [22, 13, 13].length → ∀ n,
          ProofFile.Honest.srcOf 1 ((fun k => srcsO.getD k (.own 0)) k) = (1, n) →
          n ≠ rootsOf (pre.flatMap (·.rounds)) + sentBefore J (firstLen J.p.nums.stages + i)) ∧
      ∀ i, (depthAt J (firstLen J.p.nums.stages + i)).isSome = true →
        aloneB (P5J.F0T o Zp Np cF) pre t (rootsOf (pre.flatMap (·.rounds)) +
          sentBefore J (firstLen J.p.nums.stages + i)) = true := by
  have hpl : J.p.place = ⟨2, none, 10, .K12⟩ := by
    rw [hJ]
    obtain ⟨nO, -, rfl⟩ := omega_of_four hO
    exact H2K.JointK.place_of_p12At _ _
  obtain ⟨e1, -, e3⟩ := cut_WO h pre t b hcut (hb.trans hpl)
  have hst : J.p.nums.stages = piOFull.nums.stages := by
    rw [hJ]
    exact congrArg (·.stages) (nums_head_O h hO)
  have h3 : rootsOf (pre.flatMap (·.rounds)) = 7 := by
    rw [e1]
    exact roots_WO
  have hdep : ∀ r, depthAt J r = ProofFile.Honest.K12.depthOf true piOFull.nums.stages r := fun r => by
    unfold depthAt ProofFile.Honest.K12.depthOf
    rw [hfr, hst]
  rw [h3]
  refine ⟨opensFit_of_B J _ _ _ _ ?_, ?_, ?_⟩
  · obtain ⟨bW, hbW, er⟩ := Option.map_eq_some_iff.1 e3
    have q := opens_WO
    rw [hbW] at q
    have q' : opensFitB true piOFull.nums.stages bW.rounds [22, 13, 13] srcsO 7 = true :=
      Option.some.inj q
    rw [er] at q'
    rw [hfr, hst]
    exact q'
  · intro i hi j hj n hn
    rw [hst] at hi ⊢
    rw [hdep] at hi
    have hsb : sentBefore J (firstLen piOFull.nums.stages + i) =
        ((List.range (firstLen piOFull.nums.stages + i)).filter fun j =>
          (ProofFile.Honest.K12.depthOf true piOFull.nums.stages j).isSome).length := by
      unfold sentBefore
      simp only [hdep]
    rw [hsb]
    have hlt : i < 40 := by
      by_contra hc
      have hf := far_WO
      have hn' : ProofFile.Honest.K12.depthOf true piOFull.nums.stages
          (firstLen piOFull.nums.stages + i) = none := by
        unfold ProofFile.Honest.K12.depthOf
        exact List.getD_eq_default _ _ (by omega)
      rw [hn'] at hi
      cases hi
    have hh := List.all_eq_true.1 apart_WO i (List.mem_range.2 hlt)
    rw [hi] at hh
    simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq] at hh
    have hn7 : n ≤ 7 := by
      match j, hj, hn with
      | 0, _, hn =>
        have e : (1 : ℕ) = n := congrArg Prod.snd hn
        omega
      | 1, _, hn =>
        have e : (2 : ℕ) = n := congrArg Prod.snd hn
        omega
      | 2, _, hn =>
        have e : (7 : ℕ) = n := congrArg Prod.snd hn
        omega
    omega
  · intro i hi
    rw [alone_is_WO h pre t b hcut (hb.trans hpl)]
    rw [hst] at hi ⊢
    rw [hdep] at hi
    have hsb : sentBefore J (firstLen piOFull.nums.stages + i) =
        ((List.range (firstLen piOFull.nums.stages + i)).filter fun j =>
          (ProofFile.Honest.K12.depthOf true piOFull.nums.stages j).isSome).length := by
      unfold sentBefore
      simp only [hdep]
    rw [hsb]
    by_cases hlt : i < 40
    · have hh := List.all_eq_true.1 alone_WO i (List.mem_range.2 hlt)
      rw [hi] at hh
      simpa using hh
    · exfalso
      have hf := far_WO
      have hn : ProofFile.Honest.K12.depthOf true piOFull.nums.stages
          (firstLen piOFull.nums.stages + i) = none := by
        unfold ProofFile.Honest.K12.depthOf
        exact List.getD_eq_default _ _ (by omega)
      rw [hn] at hi
      cases hi

/-! ## 3 What the row owes -/

/-- **The test's row on G_omega owes nothing more to `BudDebts`.** -/
theorem budOwed₂_at_O {W₀ Rc Ky X₀ : Type} (h : P5J.AtMg o Z D r₀ Zp Np cF)
    (hO : (fourOf Np).O = some pO) (Js : SimJob Ky) (J : TestJob (Common W₀ Rc Ky) X₀)
    (hp : J.p = pO) (hJ : Js.p = pO) (hfr : J.fresh.isNone = true) (ho : Js.own = true) {Bk : ProverCoinCounts}
    (L : Lettered Bk (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (hpl : L.place = J.p.place) (hrow : L.row = testPairs J Js) (hbud : L.bud = budBoth Js) :
    BudOwed₂ (P5J.F0T o Zp Np cF) L := by
  intro σ hσ u hu pre t n hcut hn ρ hρ
  have hp' : Js.p = J.p := hJ.trans hp.symm
  rw [hbud]
  refine both_of J Js hp' u.number _ _ (fun e => ?_) fun e => ?_
  · have hd := debt_first_O h hO Js J hp hJ { L with bud := testBud Js } hpl hrow rfl σ hσ u
      hu e pre t n hcut hn ρ hρ
    rw [e] at hd
    exact hd
  · have T := firstPubOwn_at h hO Js J hp hfr hJ ho
    have hOk : StagesOk Js.p.nums.stages = true :=
      stagesOk_at_place h Js (Or.inr (Or.inl (by rw [hJ]; exact hO)))
    subst hp
    have hstW : J.p.nums.stages = piOFull.nums.stages := congrArg (·.stages) (nums_head_O h hO)
    obtain ⟨s, next, rest, hlit⟩ : ∃ s t rest, piOFull.nums.stages = s :: t :: rest := ⟨_, _, _, rfl⟩
    have hst : J.p.nums.stages = s :: next :: rest := hstW.trans hlit
    have hk : s.k = (H2K.Pub.sgOf s).h + (H2K.Pub.sgOf s).g :=
      (Nat.add_sub_cancel' ((stages_low _ hOk).1 s
        (by rw [hp', hst]; exact List.mem_cons_self))).symm
    have hσt : testSide (P5J.F0T o Zp Np cF).shared.blocksInOrder J Js [] = some σ :=
      (side_is_testSide L J Js hpl hrow _).symm.trans hσ
    obtain ⟨b, hf, -, hr, hor⟩ := find_gomega h hO
    have hbl : σ.block = b := by
      unfold testSide Side.seated at hσt
      rw [hf] at hσt
      obtain rfl := Option.some.inj hσt
      rfl
    have hzip : σ.block.rounds.zip σ.block.oracles = J.laid := by
      rw [hbl, hr, hor]
      exact zip_laid J.p (planOk_head_O h hO)
    have hm : σ.members = [firstMember J Js, restMember J Js] :=
      members_of_seat _ J Js [] σ hσt hzip s next rest hst (count_head_O h hO)
    rw [hm] at hu
    have hu' : u = restMember J Js := by
      rcases List.mem_cons.1 hu with rfl | hu2
      · exact absurd e Nat.zero_ne_one
      · rcases List.mem_cons.1 hu2 with rfl | hu3
        · rfl
        · cases hu3
    subst hu'
    have hrow' : σ.row = testPairs J Js := by
      unfold testSide Side.seated at hσt
      obtain ⟨b', -, rfl⟩ := Option.map_eq_some_iff.1 hσt
      rfl
    have hrT : σ.roundsTo 1 = firstLen J.p.nums.stages := by
      unfold Side.roundsTo
      rw [hrow']
      show (firstPart J : Part Empty (Common W₀ Rc Ky) X₀).moves.length + 0 = firstLen J.p.nums.stages
      rw [Nat.add_zero, first_moves_len]
    have hn' : n = (pre.flatMap (·.rounds)).length + firstLen J.p.nums.stages := by
      rw [hn]
      show _ + σ.roundsTo 1 = _
      rw [hrT]
    subst hn'
    have hplan := h.laid.planOk
    have hshb : σ.block.shaped = true := planOk_shaped hplan σ.block
      (by rw [hcut]; exact List.mem_append_right _ List.mem_cons_self)
    have hlen : σ.block.rounds.length = J.laid.length := by
      rw [← hzip, List.length_zip, shaped_len σ.block hshb, Nat.min_self]
    have hN := trees_rest J pre t σ.block
      (fun x hx => planOk_shaped hplan x (by rw [hcut]; exact List.mem_append_left _ hx)) hzip T.tables
      T.enough
    rw [← hcut] at hN
    have hb : σ.block.place = J.p.place := (side_place hσ).trans hpl
    obtain ⟨O, hap, ha⟩ := premises_at_O h hO J rfl hfr pre t σ.block hcut hb
    rw [hN]
    exact bud_rest_apart (V := Empty) J Js pre t σ.block hcut _ _ _ O s next rest hst hk T.tables hap hlen
      T.enough ρ hρ ha

end ProofFile.Honest.K12.Light.AtO

#print axioms ProofFile.Honest.K12.own_reads_apart
#print axioms ProofFile.Honest.K12.bud_own_apart
#print axioms ProofFile.Honest.K12.bud_rest_apart
#print axioms ProofFile.Honest.K12.Light.AtO.apart_WO
#print axioms ProofFile.Honest.K12.Light.AtO.roots_WO
#print axioms ProofFile.Honest.K12.Light.AtO.opens_WO
#print axioms ProofFile.Honest.K12.Light.AtO.alone_WO
#print axioms ProofFile.Honest.K12.Light.AtO.no_WO
#print axioms ProofFile.Honest.K12.Light.AtO.premises_at_O
#print axioms ProofFile.Honest.K12.Light.AtO.budOwed₂_at_O
