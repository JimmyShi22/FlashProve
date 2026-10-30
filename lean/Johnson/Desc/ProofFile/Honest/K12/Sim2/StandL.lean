-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: what a run gives at the first chain's last test (the place L).
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/StandL.lean: at the proximity test that closes the first chain,
at a run of the frame's walking prover, under the head: the five clauses le, leS, heardFit, heard,
fold of the condition at the second part (FiveAt, Sim2/Clauses.lean) and the frame's bound on the
positions asked at both members. No property of the protocol is claimed.

  carryRows_congr, rowsL_congr   jobL's rows read the stretches of the job's members alone
  draws_fit_first_chain        a stretch of the first chain's challenges has the declared form
  aloneInFirstChain, asks_in_first_chain, bound_rest_first_chain, bound_rest_at_first_chain   aloneB, asks_in_block, bud_rest_file,
                   bud_rest_at_run (ReadsInBlock.lean, Sim/BudRestAtRun.lean) at the first chain
  seat_at_last_test      where the second member stands, and the place's public ties
  five_clauses_at_last_test, five_L   the five clauses: at any job at L; at jobL at any state on entry
  writtenRoundsInFront, writtenRoundsBehind, written_index_of_last_test, written_alone, written_senders_in_front, written_roots_in_front, written_opens_fit, written_depths_end, written_trees_sent, written_tests_can_say_no
                   closed facts at the written description, by Lean's kernel
  cut_at_last_test, premises_at_last_test   from the written description to the proof file's own
  bound_at_second_member, bound_at_first_member, bud_L   the bound: at the second member; the first; at jobL

What is left as a premise, and why. The head h; ρ.due, public. ready and runC have returned, and for
five_L the part is called: these are the run's. hg: the prover's first list holds the test's half at
the side's place, the filling's. hT (five_L alone): tiesB, a test on the book. Js.p, Js.own, hσ: the
simulators' job and its seat. The bound asks no «called». Everything else that five_at_first asks
(the stand, the laid rounds, h + g = k, FirstTies, the challenges' form, what the rows read) is paid.

Limits.
- A conditional with no member: no full-size run is evaluated, and nothing shows that ready or runC
  returns at a prover and a book that lend these parts.
- five_L is at any state on entry: it says nothing on which one is the verifier's. Its clause fold
  speaks of that state. At a wiped state the job's own rec₀ is the wiped one.
- J.p is the seated place (fourOf Np).L. Under the head that is not shown to be the written place
  piLFull: they agree in what reads_head_L names. The kernel's facts are at piLFull and the written
  description WP; the theorems carry them over by cut_at_last_test, reads_head_L and decl_at_laid.
- One request. Of the walk (runC), not of play (run). Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.FiveAtFirst
import Johnson.Desc.ProofFile.Honest.K12.AtProof.LotAtDoor
import AtFullSide.K12.FirstAnyAtHeadL
import Johnson.Desc.ProofFile.Honest.K12.Sim.FrameAtFirst
import Johnson.Desc.ProofFile.Honest.K12.Sim.BudRestAtRun
import Johnson.Desc.ProofFile.Honest.K12.Sim.BudBoth
import Johnson.Desc.ProofFile.Honest.K12.OpensFitB
import Johnson.Desc.ProofFile.Honest.K14.WrittenAtHead
import Johnson.Desc.ProofFile.Honest.K12.Sim2.Clauses

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (FileDescription Block Place Chain)
open VerifiableInference.Desc.K12 (P12 T12)
open VerifiableInference.Desc.First (S)
open ProofFile.Honest
open ProofFile.Honest.K12.AtProof
open ProofFile.Honest.K12.Light
open Johnson.Prover.Link (μOf rowOf PS)
open H2K.Pub (sgOf)
open H2K.Member (piLFull)
open P2Law.ProofPlan (WP declProofFull)
open VerifiableInference.Desc (Alike₂ alike₂_rounds)

variable {W₀ Rc Xi Tr X : Type}

/-- The carrying message's rows read the stretches of the job's members alone. -/
theorem carryRows_congr (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : K2.Closing) (p : K2.SwitchPlace) (w : Local W₀ Rc Xi Tr) (heard : List Fmt.Drawn)
    (mem mem' : ℕ → Stretch) (hh : ∀ t, t < (membersL p).length → mem t = mem' t) :
    carryRows D readers closing p w heard mem = carryRows D readers closing p w heard mem' := by
  have hl : (membersL p).length = p.front.length + 1 := by
    unfold membersL
    simp
  unfold carryRows
  rw [hh p.front.length (by omega)]
  refine congrArg (fun z => Except.bind z _)
    (congrArg (closing p (D w.x) (readers w) heard) (funext fun n => ?_))
  split
  · rename_i x hn
    have hlt : n < p.front.length := (List.getElem?_eq_some_iff.1 hn).1
    rw [hh n (by omega)]
  · rfl

/-- So do the first stage's rows. -/
theorem rowsL_congr (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : K2.Closing) (p : K2.SwitchPlace) (w : Local W₀ Rc Xi Tr) (fr : Front X)
    (mem mem' : ℕ → Stretch) (hh : ∀ t, t < (membersL p).length → mem t = mem' t) :
    rowsL D readers closing p w fr mem = rowsL D readers closing p w fr mem' := by
  unfold rowsL
  rw [carryRows_congr D readers closing p w _ mem mem' hh]

/-- A stretch of the first chain's challenges that passes Draws.due has the declared form. -/
theorem draws_fit_first_chain {F : FileDescription Xi} {ρ : Draws} (hρ : ρ.due F = true)
    (pre t : List (Block F.S₁ F.Cl)) (b : Block F.S₁ F.Cl)
    (hcut : F.first.blocksInOrder = pre ++ b :: t) (n : ℕ) (hn : n ≤ b.rounds.length) :
    drawsFit (b.rounds.take n) ((ρ.first.drop (pre.flatMap (·.rounds)).length).take n) = true := by
  unfold Draws.due at hρ
  simp only [Bool.and_eq_true] at hρ
  have h2 : drawsFit (F.first.blocksInOrder.flatMap (·.rounds)) ρ.first = true := hρ.1.1.1
  rw [hcut, List.flatMap_append, List.flatMap_cons] at h2
  have h3 := (drawsFit_cut (pre.flatMap (·.rounds)).length _ _ h2).2
  rw [List.drop_left] at h3
  have h4 := (drawsFit_cut b.rounds.length _ _ h3).1
  rw [List.take_left] at h4
  have h5 := (drawsFit_cut n _ _ h4).1
  rw [List.take_take, Nat.min_eq_left hn] at h5
  exact h5

section BudFirst
open Johnson.G.OfPlan (rootsOf)

/-- aloneB (ReadsInBlock.lean) at the first chain: no round of the file outside the sub-protocol
between pre and t of the first list opens the first chain's tree number k. -/
def aloneInFirstChain {Xi : Type} (F : FileDescription Xi) (pre t : List (Block F.S₁ F.Cl)) (k : ℕ) : Bool :=
  (openedOf 0 (pre.flatMap (·.rounds)) ++ openedOf 0 (t.flatMap (·.rounds)) ++
    openedOf 1 F.roundsDeclaredByBlocks.2.1 ++ openedOf 2 F.roundsDeclaredByBlocks.2.2).all (·.1 != (0, k))

/-- asks_in_block (ReadsInBlock.lean) at the first chain. -/
theorem asks_in_first_chain {Xi : Type} {F : FileDescription Xi} (pre t : List (Block F.S₁ F.Cl))
    (b : Block F.S₁ F.Cl) (hcut : F.first.blocksInOrder = pre ++ b :: t) (ρ : Draws)
    (hρ : ρ.due F = true) (k : ℕ) (ha : aloneInFirstChain F pre t k = true) :
    ∀ x ∈ treeAsks F ρ 0 k, x ∈ ((readsOf 0 0 (fun _ _ => none) (fun _ => none) b.rounds
      ((ρ.first.drop (pre.flatMap (·.rounds)).length).take b.rounds.length)).filter fun q =>
        q.src == some (0, k)).map (·.pos) := by
  intro x hx
  unfold treeAsks at hx
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
  obtain ⟨hq, hs⟩ := List.mem_filter.1 hq
  have hs' : q.src = some (0, k) := beq_iff_eq.1 hs
  have off : ∀ e ∈ openedOf 0 (pre.flatMap (·.rounds)) ++ openedOf 0 (t.flatMap (·.rounds)) ++
      openedOf 1 F.roundsDeclaredByBlocks.2.1 ++ openedOf 2 F.roundsDeclaredByBlocks.2.2, e.1 ≠ (0, k) := fun e he =>
    bne_iff_ne.1 (List.all_eq_true.1 ha e he)
  unfold Draws.due at hρ
  simp only [Bool.and_eq_true] at hρ
  have h2 : drawsFit (F.first.blocksInOrder.flatMap (·.rounds)) ρ.first = true := hρ.1.1.1
  have hlen := ProofFile.Honest.drawsFit_length _ _ h2
  rw [hcut, List.flatMap_append, List.flatMap_cons, List.length_append, List.length_append]
    at hlen
  unfold allBare bareReads at hq
  rcases List.mem_append.1 hq with hq | hq
  · rcases List.mem_append.1 hq with hq | hq
    · have hq' : q ∈ readsOf 0 0 (fun _ _ => none) (fun _ => none)
          (pre.flatMap (·.rounds) ++ (b.rounds ++ t.flatMap (·.rounds)))
          (ρ.first.take (pre.flatMap (·.rounds)).length ++
            ((ρ.first.drop (pre.flatMap (·.rounds)).length).take b.rounds.length ++
              (ρ.first.drop (pre.flatMap (·.rounds)).length).drop b.rounds.length)) := by
        rw [List.take_append_drop, List.take_append_drop, ← List.flatMap_cons,
          ← List.flatMap_append, ← hcut]
        exact hq
      rw [readsOf_append 0 0 _ _ _ _ _ _ (by rw [List.length_take]; omega),
        readsOf_append 0 0 _ _ _ _ _ _ (by rw [List.length_take, List.length_drop]; omega)] at hq'
      rcases List.mem_append.1 hq' with h | h
      · exact absurd hs' (reads_off 0 0 _ _ _ _ (0, k) (fun e he => off e
          (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ he)))) q h)
      · rcases List.mem_append.1 h with h | h
        · exact List.mem_map.2 ⟨q, List.mem_filter.2 ⟨h, hs⟩, rfl⟩
        · exact absurd hs' (reads_off 0 0 _ _ _ _ (0, k) (fun e he => off e
            (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ he)))) q h)
    · exact absurd hs' (reads_off 1 0 _ _ _ _ (0, k) (fun e he => off e
        (List.mem_append_left _ (List.mem_append_right _ he))) q hq)
  · exact absurd hs' (reads_off 2 F.lastChainFirstTreeNumber _ _ _ _ (0, k) (fun e he => off e
                    (List.mem_append_right _ he)) q hq)

/-- bud_rest_file (Sim/BudRestAtRun.lean) at the first chain. -/
theorem bound_rest_first_chain {V W Y Pb : Type} {F : FileDescription Xi} (J : TestJob W Y) (Js : SimJob Pb)
    (pre t : List (Block F.S₁ F.Cl)) (b : Block F.S₁ F.Cl)
    (hcut : F.first.blocksInOrder = pre ++ b :: t) (depths : List ℕ) (src₀ : ℕ → Fmt.TreeSource) (sent : ℕ)
    (O : OpensFit J b.rounds depths src₀ sent) (s next : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: next :: rest)
    (hk : s.k = (sgOf s).h + (sgOf s).g) (hT : tablesFitB J = true)
    (hold : ∀ k, k < depths.length → ∀ n, srcOf 0 (src₀ k) = (0, n) → n < sent)
    (hlen : b.rounds.length = J.laid.length)
    (hen : firstLen J.p.nums.stages ≤ J.laid.length) (ρ : Draws) (hρ : ρ.due F = true)
    (ha : ∀ i, (depthAt J (firstLen J.p.nums.stages + i)).isSome = true →
      aloneInFirstChain F pre t (sent + sentBefore J (firstLen J.p.nums.stages + i)) = true) :
    budOpened J.p.nums.stages 1
      ((ρ.first.drop ((pre.flatMap (·.rounds)).length + firstLen J.p.nums.stages)).take
        (restMember (V := V) J Js).rounds.length)
      (asksFrom (treeAsks F ρ 0) ((restMember (V := V) J Js).rounds.map (·.2.length))
        (sent + sentBefore J (firstLen J.p.nums.stages))) := by
  have hρ' := hρ
  unfold Draws.due at hρ'
  simp only [Bool.and_eq_true] at hρ'
  have h2 : drawsFit (F.first.blocksInOrder.flatMap (·.rounds)) ρ.first = true := hρ'.1.1.1
  have htot := ProofFile.Honest.drawsFit_length _ _ h2
  rw [hcut, List.flatMap_append, List.flatMap_cons, List.length_append, List.length_append]
    at htot
  have hrl : (restMember (V := V) J Js).rounds.length =
      b.rounds.length - firstLen J.p.nums.stages := by
    show (J.laid.drop (firstLen J.p.nums.stages)).length = _
    rw [List.length_drop, hlen]
  have hds : (ρ.first.drop ((pre.flatMap (·.rounds)).length + firstLen J.p.nums.stages)).take
      (restMember (V := V) J Js).rounds.length =
      (((ρ.first.drop (pre.flatMap (·.rounds)).length).take b.rounds.length).drop
        (firstLen J.p.nums.stages)) := by
    rw [List.drop_take, List.drop_drop, hrl]
  have h1 : (((ρ.first.drop (pre.flatMap (·.rounds)).length).take b.rounds.length).take
      (firstLen J.p.nums.stages)).length = firstLen J.p.nums.stages := by
    rw [List.length_take, List.length_take, List.length_drop]
    omega
  rw [hds]
  refine bud_sub _ _ _ _ _ _ (bud_own_rest (V := V) J Js b.rounds depths src₀ sent 0 0 O s next
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
  exact asks_in_first_chain pre t b hcut ρ hρ _ (ha i hsome) q hq

/-- **budOpened at one run's own challenges and positions, at the second member, at the first
chain**: bud_rest_at_run (Sim/BudRestAtRun.lean) there. That the part was called is not asked. -/
theorem bound_rest_at_first_chain {W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true) (hρ : ρ.due F = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (J : TestJob (Local W₀ Rc Xi Tr) Y) (Js : SimJob Pb)
    (σ : Side F.S₁ F.Cl V (Local W₀ Rc Xi Tr) Y Pb) (pre t : List (Block F.S₁ F.Cl))
    (S : StandsAt F.first.blocksInOrder R.first σ (restMember J Js) pre t (firstLen J.p.nums.stages))
    (hzip : σ.block.rounds.zip σ.block.oracles = J.laid) (depths : List ℕ)
    (src₀ : ℕ → Fmt.TreeSource)
    (O : OpensFit J σ.block.rounds depths src₀ (rootsOf (pre.flatMap (·.rounds))))
    (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = s :: next :: rest) (hk : s.k = (sgOf s).h + (sgOf s).g)
    (hT : tablesFitB J = true)
    (hold : ∀ k, k < depths.length → ∀ n, srcOf 0 (src₀ k) = (0, n) →
      n < rootsOf (pre.flatMap (·.rounds)))
    (hen : firstLen J.p.nums.stages ≤ J.laid.length)
    (ha : ∀ i, (depthAt J (firstLen J.p.nums.stages + i)).isSome = true →
      aloneInFirstChain F pre t (rootsOf (pre.flatMap (·.rounds)) +
        sentBefore J (firstLen J.p.nums.stages + i)) = true) :
    budOpened J.p.nums.stages 1 (r.run.drawnAt ⟨σ.block.place, 1⟩)
      (r.run.askedAt ⟨σ.block.place, 1⟩) := by
  have Q := (F.planOk_ok).1 hpl
  have hp := Q.places
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  have o₁ := steps_shaped s1 Q.blocks₁
  have o₂ := steps_shaped s2 Q.blocks₂
  have o₃ := steps_shaped s3 Q.blocks₃
  have hcut : F.first.blocksInOrder = pre ++ σ.block :: t := S.cut
  have hstr : InStretch R.first ⟨σ.block.place, 1⟩
      ((pre.flatMap (·.rounds)).length + firstLen J.p.nums.stages)
      (restMember (V := V) J Js).rounds.length := S.str
  obtain ⟨ha', -, -, -⟩ := stretch_back hstr S.pos S.fits
  have hA := at_first hrun hR o₁ o₂ o₃ hp ha'
  have e1 : ((R.first.drop ((pre.flatMap (·.rounds)).length + firstLen J.p.nums.stages)).take
      (restMember (V := V) J Js).rounds.length).map (·.oracles.length) =
      (restMember (V := V) J Js).rounds.map (·.2.length) := by
    have g := congrArg (List.map (·.2.length)) S.own
    rw [List.map_map] at g
    exact g
  have e2 : (R.first.take ((pre.flatMap (·.rounds)).length + firstLen J.p.nums.stages)).map
      (·.oracles.length) = ((rowsOfChain F.first.blocksInOrder).take
        ((pre.flatMap (·.rounds)).length + firstLen J.p.nums.stages)).map (·.2.length) := by
    rw [← steps_pairs s1, ← List.map_take, List.map_map]
    rfl
  have hshb : σ.block.shaped = true := planOk_shaped_first hpl σ.block
    (by rw [hcut]; exact List.mem_append_right _ List.mem_cons_self)
  have hlen : σ.block.rounds.length = J.laid.length := by
    rw [← hzip, List.length_zip, shaped_len σ.block hshb, Nat.min_self]
  have hN := trees_rest J pre t σ.block
    (fun x hx => planOk_shaped_first hpl x (by rw [hcut]; exact List.mem_append_left _ hx)) hzip hT
    hen
  rw [← hcut] at hN
  rw [drawnAt_of hA hstr,
    askedAt_of hA hstr (treeAsks F ρ 0) (runC_asks hrun hR o₁ o₂ o₃ 0), e1, e2, hN]
  exact bound_rest_first_chain (V := V) J Js pre t σ.block hcut depths src₀ _ O s next rest hst hk hT
    hold hlen hen ρ hρ ha

end BudFirst

section AtHead
open Johnson.G.OfPlan (rootsOf)
variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}

local notation "𝔽" => P5J.F0T OnBytes.secondHashFunction Zp Np cF

theorem rest_rounds_at_last_test : restLen piLFull.nums.stages ≠ 0 := by decide +kernel

/-- **Where the second member's rounds stand at L, from what the prover's first list holds**, with
the public ties that the place gives. -/
theorem seat_at_last_test (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) {Ky X₀ Y : Type} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst} {k : Coins Bk}
    {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ Y} (hR : ready 𝔽 Bk P w₀ rc x k = .ok R)
    (J : TestJob (Local W₀ Rc ProofFile.Inst Tr) Y) (hp : J.p = (fourOf Np).L)
    (hfrN : J.fresh.isNone = false)
    (Js : SimJob ProofFile.Inst) (hs : Js.p = (fourOf Np).L) (ho : Js.own = false)
    (fs : List (Fall S))
    (σ : Side S ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Y ProofFile.Inst)
    (hσ : testSide cF.blocksInOrder J Js fs = some σ)
    (hg : (P.first.find? fun g => g.place == σ.block.place) = some (proverSideOfProximityTest J)) :
    ∃ (pre t : List (Block S ProofFile.Cl)) (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage),
      StandsAt cF.blocksInOrder R.first σ (restMember J Js) pre t (firstLen J.p.nums.stages) ∧
      σ.block.rounds.zip σ.block.oracles = J.laid ∧
      σ.block.place = J.p.place ∧
      σ.block.rounds.length = (H2K.JointK.laidOf J.p).length ∧
      σ.block.oracles.length = σ.block.rounds.length ∧
      J.p.nums.stages = s :: next :: rest ∧ s.k = (sgOf s).h + (sgOf s).g ∧
      FormPub J.p s next rest := by
  have Fc := facts_head_L h
  rw [← hp] at Fc
  obtain ⟨f1, f2, -, -, -⟩ :=
    (first_any_head_L (V := Local W₀ Rc ProofFile.Inst Tr) h J Js hp hfrN hs ho).2.2 fs σ hσ
  have hσ' := hσ
  unfold testSide Side.seated at hσ'
  obtain ⟨b, hb, e⟩ := Option.map_eq_some_iff.1 hσ'
  have hblk : σ.block ∈ (𝔽).first.blocksInOrder := by
    rw [← e]
    exact List.mem_of_find?_eq_some hb
  have hrow : σ.row = testPairs J Js := by rw [← e]
  have hmem : restMember J Js ∈ σ.members := by
    have f2' : σ.members = [firstMember J Js, restMember J Js] := f2
    rw [f2']
    simp
  obtain ⟨s, next, rest, hst⟩ : ∃ s next rest, J.p.nums.stages = s :: next :: rest := by
    have hform := Fc.form
    unfold formPubB at hform
    cases hs' : J.p.nums.stages with
    | nil => rw [hs'] at hform; cases hform
    | cons a l =>
      cases l with
      | nil => rw [hs'] at hform; cases hform
      | cons b' r' => exact ⟨a, b', r', rfl⟩
  have FP := formPub_of_B J.p s next rest hst Fc.form
  have hk : s.k = (sgOf s).h + (sgOf s).g := by
    have := FP.hk
    show s.k = s.h + (s.k - s.h)
    omega
  have l2 : (restPart J : Part (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Y).moves.length =
      restLen J.p.nums.stages := by
    rw [rest_moves J s next rest hst]
    exact (List.length_map _).trans List.length_range
  have hpos : (restPart J : Part (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Y).moves.length
      ≠ 0 := by
    rw [l2, hp, (reads_head_L h).1]
    exact rest_rounds_at_last_test
  obtain ⟨pre, t, S⟩ := stands_rest_own h.laid.planOk hR J Js σ hblk hrow f1 hmem hpos
    (proverSideOfProximityTest J) hg rfl
  obtain ⟨b', hf, hpl', hr, hor⟩ := find_last h
  have hb' : b = b' := by
    rw [hp] at hb
    exact Option.some.inj (hb.symm.trans hf)
  have eb : σ.block = b' := by rw [← hb', ← e]
  have hzip : σ.block.rounds.zip σ.block.oracles = J.laid := by
    rw [eb, hr, hor]
    show _ = H2K.JointK.laidOf J.p
    rw [hp]
    exact zip_laid _ (facts_head_L h).plan
  have hsh : σ.block.shaped = true := planOk_shaped_first h.laid.planOk σ.block hblk
  have hol := shaped_len σ.block hsh
  have hlenb : σ.block.rounds.length = (H2K.JointK.laidOf J.p).length := by
    show _ = J.laid.length
    rw [← hzip, List.length_zip, hol, Nat.min_self]
  exact ⟨pre, t, s, next, rest, S, hzip, by rw [eb, hpl', hp], hlenb, hol, hst, hk, FP⟩

/-- **The five clauses at a run, at any job at the place L whose fresh table came earlier.** -/
theorem five_clauses_at_last_test (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) {Ky X₀ Y : Type} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst} {k : Coins Bk}
    {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {r : RunC 𝔽}
    (hρ : ρ.due 𝔽 = true) (hR : ready 𝔽 Bk P w₀ rc x k = .ok R)
    (J : TestJob (Local W₀ Rc ProofFile.Inst Tr) Y) (hp : J.p = (fourOf Np).L) (f : Addr × ℕ)
    (hfr : J.fresh = some f)
    (hrows : ∀ (w : Local W₀ Rc ProofFile.Inst Tr) (fr : Front Y) (mem mem' : ℕ → Stretch),
      (∀ t, t < J.members.length → mem t = mem' t) → J.rows₀ w fr mem = J.rows₀ w fr mem')
    (Js : SimJob ProofFile.Inst) (hs : Js.p = (fourOf Np).L) (ho : Js.own = false)
    (fs : List (Fall S))
    (σ : Side S ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Y ProofFile.Inst)
    (hσ : testSide cF.blocksInOrder J Js fs = some σ)
    (hg : (P.first.find? fun g => g.place == σ.block.place) = some (proverSideOfProximityTest J))
    (hT : tiesB Bk J.p.place J.members.length = true)
    (hrun : runC 𝔽 Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, 1⟩ = true)
    (st : List (ℕ × ℕ × List UInt64)) :
    ∃ (c : RowCoins [(firstPart J : Part (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Y),
        restPart J]) (m : ProofFile.Honest.Mid (Local W₀ Rc ProofFile.Inst Tr) Y),
      midAtW 𝔽 Bk P w₀ rc x k ρ ⟨σ.block.place, 1⟩ = .ok (some m) ∧
      carriedAt Bk k 0 ⟨σ.block.place, 1⟩
        (restMember (V := Local W₀ Rc ProofFile.Inst Tr) J Js).part = .ok c.2.1.2.2 ∧
      m.st.input = R.own ∧
      FiveAt J (stretches _ c.2.1.2.2) m (r.run.beforeAt st ⟨σ.block.place, 1⟩) := by
  have hfrN : J.fresh.isNone = false := by rw [hfr]; rfl
  have Fc := facts_head_L h
  rw [← hp] at Fc
  obtain ⟨pre, t, s, next, rest, S, hzip, -, hlenb, hol, hst, hk, FP⟩ :=
    seat_at_last_test h hR J hp hfrN Js hs ho fs σ hσ hg
  have hcut : cF.blocksInOrder = pre ++ σ.block :: t := S.cut
  have g0 := draws_fit_first_chain (F := 𝔽) hρ pre t σ.block hcut (firstLen J.p.nums.stages)
    (by rw [hlenb]; exact Fc.enough)
  have e1 : ((H2K.JointK.laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1) =
      σ.block.rounds.take (firstLen J.p.nums.stages) := by
    have hz : H2K.JointK.laidOf J.p = σ.block.rounds.zip σ.block.oracles := hzip.symm
    rw [List.map_take, hz, List.map_fst_zip (by rw [hol])]
  have hfit : drawsFit (((H2K.JointK.laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1))
      ((ρ.first.drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages)) = true := by
    rw [e1]
    exact g0
  have hlen : ((ρ.first.drop (pre.flatMap (·.rounds)).length).take
      (firstLen J.p.nums.stages)).length = firstLen J.p.nums.stages := by
    have hh := ProofFile.Honest.drawsFit_length _ _ hfit
    rw [hh, List.length_map, List.length_take]
    exact Nat.min_eq_left Fc.enough
  have T : FirstTies J s next rest (byNo ((ρ.first.drop (pre.flatMap (·.rounds)).length).take
      (firstLen J.p.nums.stages)))
      ((ρ.first.drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages)) :=
    ⟨hst, Fc.enough, FP.sorts, by rw [tablesFitB_eq, hfrN]; exact Fc.tab, hlen,
      fun n hn => (List.getD_eq_getElem _ _ hn).symm⟩
  obtain ⟨c, m, hm, hca, hin, le, leS, hF, hH, hFold⟩ := five_at_first (F := 𝔽) h.laid.planOk J f
    hfr Js hR σ pre t S hg hzip hT s next rest _ T hk
    (fun w fr mem mem' hh => congrArg _ (hrows w fr mem mem' hh)) hfit hrun hc st
  exact ⟨c, m, hm, hca, hin, ⟨le, leS, hF, hH, hFold⟩⟩

/-- **five_L: the five clauses at a run at the job of the lot, at any state on entry.** -/
theorem five_L (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) {Ky X₀ Y : Type} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst} {k : Coins Bk}
    {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {r : RunC 𝔽}
    (hρ : ρ.due 𝔽 = true) (hR : ready 𝔽 Bk P w₀ rc x k = .ok R)
    (door : Local W₀ Rc ProofFile.Inst Tr → Front Y → T12) (D : RowDataOf ProofFile.Inst)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (closing : K2.Closing) (pl : K2.SwitchPlace)
    (Js : SimJob ProofFile.Inst) (hs : Js.p = H2U.p12OfMade Zp.made) (ho : Js.own = false)
    (fs : List (Fall S))
    (σ : Side S ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Y ProofFile.Inst)
    (hσ : testSide cF.blocksInOrder (jobL (H2U.p12OfMade Zp.made) door D readers closing pl) Js fs = some σ)
    (hg : (P.first.find? fun g => g.place == σ.block.place) =
      some (proverSideOfProximityTest (jobL (H2U.p12OfMade Zp.made) door D readers closing pl)))
    (hT : tiesB Bk (H2U.p12OfMade Zp.made).place (membersL pl).length = true)
    (hrun : runC 𝔽 Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, 1⟩ = true)
    (st : List (ℕ × ℕ × List UInt64)) :
    ∃ (c : RowCoins [(firstPart (jobL (H2U.p12OfMade Zp.made) door D readers closing pl) :
          Part (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Y),
        restPart (jobL (H2U.p12OfMade Zp.made) door D readers closing pl)])
      (m : ProofFile.Honest.Mid (Local W₀ Rc ProofFile.Inst Tr) Y),
      midAtW 𝔽 Bk P w₀ rc x k ρ ⟨σ.block.place, 1⟩ = .ok (some m) ∧
      carriedAt Bk k 0 ⟨σ.block.place, 1⟩
        (restMember (V := Local W₀ Rc ProofFile.Inst Tr)
          (jobL (H2U.p12OfMade Zp.made) door D readers closing pl) Js).part = .ok c.2.1.2.2 ∧
      m.st.input = R.own ∧
      FiveAt (jobL (H2U.p12OfMade Zp.made) door D readers closing pl) (stretches _ c.2.1.2.2) m
        (r.run.beforeAt st ⟨σ.block.place, 1⟩) :=
  five_clauses_at_last_test h hρ hR _ (numbersL_at_head h) _ rfl
    (fun w fr mem mem' hh => rowsL_congr D readers closing pl w fr mem mem' hh)
    Js (hs.trans (numbersL_at_head h)) ho fs σ hσ hg hT hrun hc st

/-! ## The written rounds around L: closed facts by Lean's kernel -/

/-- The written declared rounds in front of the test at L in the first chain. -/
def writtenRoundsInFront : List Fmt.DeclaredRound := (WP.first.blocksInOrder.take 354).flatMap (·.rounds)

/-- Those behind it. -/
def writtenRoundsBehind : List Fmt.DeclaredRound := (WP.first.blocksInOrder.drop 355).flatMap (·.rounds)

set_option maxRecDepth 1000000 in
theorem written_index_of_last_test : ((WP.first.blocksInOrder.map (·.place)).zipIdx.filter
    fun x => x.1 == piLFull.place).map (·.2) = [354] := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- No round outside the test opens the trees that its second part sends. -/
theorem written_alone : (openedOf 0 writtenRoundsInFront ++ openedOf 0 writtenRoundsBehind ++
    openedOf 1 declProofFull.2.1 ++ openedOf 2 declProofFull.2.2).all
      (fun e => !(e.1.1 == 0 && decide (77 ≤ e.1.2) && decide (e.1.2 ≤ 81))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem written_senders_in_front : rootsOf (writtenRoundsInFront.filter fun r => r.entry.roots != 0) = 77 := by
  decide +kernel

theorem written_roots_in_front : rootsOf writtenRoundsInFront = 77 := by
  rw [Johnson.KB8.rootsOf_filter]
  exact written_senders_in_front

set_option maxRecDepth 1000000 in
theorem written_opens_fit : (WP.first.blocksInOrder[354]?).map (fun b =>
             opensFitB false piLFull.nums.stages b.rounds [23] [.own 76] 77) = some true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem written_depths_end : (none :: depths false piLFull.nums.stages).length ≤
    firstLen piLFull.nums.stages + 40 := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The trees that the second part sends have the numbers 77 to 81. -/
theorem written_trees_sent : (List.range 40).all (fun i =>
    !(ProofFile.Honest.K12.depthOf false piLFull.nums.stages (firstLen piLFull.nums.stages + i)).isSome ||
      (decide (77 ≤ 77 + ((List.range (firstLen piLFull.nums.stages + i)).filter fun j =>
          (ProofFile.Honest.K12.depthOf false piLFull.nums.stages j).isSome).length) &&
        decide (77 + ((List.range (firstLen piLFull.nums.stages + i)).filter fun j =>
          (ProofFile.Honest.K12.depthOf false piLFull.nums.stages j).isSome).length ≤ 81))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The test can say no: a round of the last two chains opens tree 82, and a round in front opens tree 75. -/
theorem written_tests_can_say_no : ((openedOf 1 declProofFull.2.1 ++ openedOf 2 declProofFull.2.2).any
      (·.1 == (0, 82)), (openedOf 0 writtenRoundsInFront).any (·.1 == (0, 75))) = (true, true) := by
  decide +kernel

attribute [local irreducible] P2Law.ProofPlan.WP

/-- Where a place stands once in a list, an index that holds it is that one. -/
theorem index_of_single_place {α : Type} [BEq α] [LawfulBEq α] (l : List α) (a : α) (n m : ℕ)
    (h : (l.zipIdx.filter fun x => x.1 == a).map (·.2) = [m]) (hn : l[n]? = some a) : n = m := by
  have hmem : (a, n) ∈ l.zipIdx := List.mem_zipIdx_iff_getElem?.2 hn
  have hf : (a, n) ∈ l.zipIdx.filter fun x => x.1 == a :=
    List.mem_filter.2 ⟨hmem, beq_self_eq_true _⟩
  have hm := List.mem_map_of_mem (f := fun x : α × ℕ => x.2) hf
  rw [h] at hm
  simpa using hm

/-- From the written description to the proof file's own, at the first chain. -/
theorem cut_at_last_test (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF)
    (pre t : List (Block (𝔽).S₁ (𝔽).Cl)) (b : Block (𝔽).S₁ (𝔽).Cl)
    (hcut : (𝔽).first.blocksInOrder = pre ++ b :: t) (hb : b.place = piLFull.place) :
    pre.flatMap (·.rounds) = writtenRoundsInFront ∧ t.flatMap (·.rounds) = writtenRoundsBehind ∧
      (WP.first.blocksInOrder[354]?).map (·.rounds) = some b.rounds := by
  have A := (ProofFile.Honest.K14.planAlike_at_laid h.scope h.laid).first
  rw [hcut] at A
  have A1 := List.forall₂_take_append _ pre (b :: t) A
  have A2 := List.forall₂_drop_append _ pre (b :: t) A
  obtain ⟨bW, tl, hbW, htl, hd⟩ := List.forall₂_cons_right_iff.1 A2
  have hget : WP.first.blocksInOrder[pre.length]? = some bW := by
    have e := congrArg List.head? hd
    rw [List.head?_drop] at e
    exact e
  have hpl : (WP.first.blocksInOrder.map (·.place))[pre.length]? = some piLFull.place := by
    rw [List.getElem?_map, hget]
    exact congrArg some (hbW.1.trans hb)
  have h354 : pre.length = 354 := index_of_single_place _ _ _ _ written_index_of_last_test hpl
  rw [h354] at A1 hd hget
  have h355 : WP.first.blocksInOrder.drop 355 = tl := by
    have e := congrArg List.tail hd
    rw [List.tail_drop] at e
    exact e
  refine ⟨(alike₂_rounds _ _ A1).symm, ?_, ?_⟩
  · unfold writtenRoundsBehind
    rw [h355]
    exact (alike₂_rounds _ _ htl).symm
  · rw [hget]
    exact congrArg some hbW.2.1

/-- **The public premises of bound_rest_at_first_chain hold at the proof file's own description, under the
head**, at every job at L whose fresh table has come earlier, at every cut at the test's place. -/
theorem premises_at_last_test (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) {W Y : Type} (J : TestJob W Y)
    (hJ : J.p = (fourOf Np).L) (hfr : J.fresh.isNone = false)
    (pre t : List (Block (𝔽).S₁ (𝔽).Cl)) (b : Block (𝔽).S₁ (𝔽).Cl)
    (hcut : (𝔽).first.blocksInOrder = pre ++ b :: t) (hb : b.place = J.p.place) :
    OpensFit J b.rounds [23] (fun k => [Fmt.TreeSource.own 76].getD k (.own 0))
        (rootsOf (pre.flatMap (·.rounds))) ∧
      (∀ k, k < [23].length → ∀ n,
        ProofFile.Honest.srcOf 0 ((fun k => [Fmt.TreeSource.own 76].getD k (.own 0)) k) = (0, n) →
        n < rootsOf (pre.flatMap (·.rounds))) ∧
      ∀ i, (depthAt J (firstLen J.p.nums.stages + i)).isSome = true →
        aloneInFirstChain 𝔽 pre t (rootsOf (pre.flatMap (·.rounds)) +
          sentBefore J (firstLen J.p.nums.stages + i)) = true := by
  have hpl : J.p.place = piLFull.place := by
    rw [hJ]
    exact H2K.JointK.place_of_p12At _ _
  obtain ⟨e1, e2, e3⟩ := cut_at_last_test h pre t b hcut (hb.trans hpl)
  have hst : J.p.nums.stages = piLFull.nums.stages := by
    rw [hJ]
    exact (reads_head_L h).1
  have h3 : rootsOf (pre.flatMap (·.rounds)) = 77 := by
    rw [e1]
    exact written_roots_in_front
  have hdep : ∀ r, depthAt J r = ProofFile.Honest.K12.depthOf false piLFull.nums.stages r := fun r => by
    unfold depthAt ProofFile.Honest.K12.depthOf
    rw [hfr, hst]
  rw [h3]
  refine ⟨opensFit_of_B J _ _ _ _ ?_, ?_, ?_⟩
  · obtain ⟨bW, hbW, er⟩ := Option.map_eq_some_iff.1 e3
    have q := written_opens_fit
    rw [hbW] at q
    have q' : opensFitB false piLFull.nums.stages bW.rounds [23] [.own 76] 77 = true :=
      Option.some.inj q
    rw [er] at q'
    rw [hfr, hst]
    exact q'
  · intro j hj n hn
    match j, hj, hn with
    | 0, _, hn =>
      have e : (76 : ℕ) = n := congrArg Prod.snd hn
      omega
  · intro i hi
    rw [hst] at hi ⊢
    rw [hdep] at hi
    have hsb : sentBefore J (firstLen piLFull.nums.stages + i) =
        ((List.range (firstLen piLFull.nums.stages + i)).filter fun j =>
          (ProofFile.Honest.K12.depthOf false piLFull.nums.stages j).isSome).length := by
      unfold sentBefore
      simp only [hdep]
    rw [hsb]
    have hlt : i < 40 := by
      by_contra hc
      have hf := written_depths_end
      have hn : ProofFile.Honest.K12.depthOf false piLFull.nums.stages
          (firstLen piLFull.nums.stages + i) = none := by
        unfold ProofFile.Honest.K12.depthOf
        exact List.getD_eq_default _ _ (by omega)
      rw [hn] at hi
      cases hi
    have hh := List.all_eq_true.1 written_trees_sent i (List.mem_range.2 hlt)
    rw [hi] at hh
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hh
    unfold aloneInFirstChain
    rw [e1, e2, ProofFile.Honest.K14.decl_at_laid h.scope h.laid]
    refine List.all_eq_true.2 fun e he => ?_
    have ha := List.all_eq_true.1 written_alone e he
    refine bne_iff_ne.2 fun hE => ?_
    rw [hE] at ha
    simp at ha
    omega

/-- **bud at a run at L, at the second member**: called or not. -/
theorem bound_at_second_member (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) {Ky X₀ Y : Type} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst} {k : Coins Bk}
    {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {r : RunC 𝔽}
    (hρ : ρ.due 𝔽 = true) (hR : ready 𝔽 Bk P w₀ rc x k = .ok R)
    (J : TestJob (Local W₀ Rc ProofFile.Inst Tr) Y) (hp : J.p = (fourOf Np).L)
    (hfrN : J.fresh.isNone = false)
    (Js : SimJob ProofFile.Inst) (hs : Js.p = (fourOf Np).L) (ho : Js.own = false)
    (fs : List (Fall S))
    (σ : Side S ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Y ProofFile.Inst)
    (hσ : testSide cF.blocksInOrder J Js fs = some σ)
    (hg : (P.first.find? fun g => g.place == σ.block.place) = some (proverSideOfProximityTest J))
    (hrun : runC 𝔽 Bk P w₀ rc x k ρ = .ok r) :
    budBoth Js 1 (r.run.drawnAt ⟨σ.block.place, 1⟩) (r.run.askedAt ⟨σ.block.place, 1⟩) := by
  have Fc := facts_head_L h
  rw [← hp] at Fc
  obtain ⟨pre, t, s, next, rest, S, hzip, hpl, -, -, hst, hk, -⟩ :=
    seat_at_last_test h hR J hp hfrN Js hs ho fs σ hσ hg
  have hcut : cF.blocksInOrder = pre ++ σ.block :: t := S.cut
  obtain ⟨O, hold, ha⟩ := premises_at_last_test h J hp hfrN pre t σ.block hcut hpl
  have hB := bound_rest_at_first_chain (F := 𝔽) h.laid.planOk hρ hR hrun J Js σ pre t S hzip [23] _ O s
    next rest hst hk (by rw [tablesFitB_eq, hfrN]; exact Fc.tab) hold Fc.enough ha
  refine (both_rest Js _ _).2 ?_
  rw [hs, ← hp]
  exact hB

/-- **The same at the first member**: nothing is owed there where the fresh table came earlier. -/
theorem bound_at_first_member (Js : SimJob ProofFile.Inst) (ho : Js.own = false) (ds : List Fmt.Drawn)
    (asks : List (List (List ℕ))) : budBoth Js 0 ds asks :=
  budBoth_of_testBud Js ds asks (first_owes_nothing Js ho ds asks)

/-- **bud_L: at the job of the lot, at any state on entry, at both members.** -/
theorem bud_L (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) {Ky X₀ Y : Type} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst} {k : Coins Bk}
    {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {r : RunC 𝔽}
    (hρ : ρ.due 𝔽 = true) (hR : ready 𝔽 Bk P w₀ rc x k = .ok R)
    (door : Local W₀ Rc ProofFile.Inst Tr → Front Y → T12) (D : RowDataOf ProofFile.Inst)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (closing : K2.Closing) (pl : K2.SwitchPlace)
    (Js : SimJob ProofFile.Inst) (hs : Js.p = H2U.p12OfMade Zp.made) (ho : Js.own = false)
    (fs : List (Fall S))
    (σ : Side S ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Y ProofFile.Inst)
    (hσ : testSide cF.blocksInOrder (jobL (H2U.p12OfMade Zp.made) door D readers closing pl) Js fs = some σ)
    (hg : (P.first.find? fun g => g.place == σ.block.place) =
      some (proverSideOfProximityTest (jobL (H2U.p12OfMade Zp.made) door D readers closing pl)))
    (hrun : runC 𝔽 Bk P w₀ rc x k ρ = .ok r) (n : ℕ) (hn : n = 0 ∨ n = 1) :
    budBoth Js n (r.run.drawnAt ⟨σ.block.place, n⟩) (r.run.askedAt ⟨σ.block.place, n⟩) := by
  rcases hn with rfl | rfl
  · exact bound_at_first_member Js ho _ _
  · exact bound_at_second_member h hρ hR _ (numbersL_at_head h) rfl Js (hs.trans (numbersL_at_head h)) ho fs σ
      hσ hg hrun

end AtHead

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.carryRows_congr
#print axioms ProofFile.Honest.K12.Sim2.rowsL_congr
#print axioms ProofFile.Honest.K12.Sim2.draws_fit_first_chain
#print axioms ProofFile.Honest.K12.Sim2.seat_at_last_test
#print axioms ProofFile.Honest.K12.Sim2.five_clauses_at_last_test
#print axioms ProofFile.Honest.K12.Sim2.five_L
#print axioms ProofFile.Honest.K12.Sim2.writtenRoundsInFront
#print axioms ProofFile.Honest.K12.Sim2.writtenRoundsBehind
#print axioms ProofFile.Honest.K12.Sim2.written_index_of_last_test
#print axioms ProofFile.Honest.K12.Sim2.written_alone
#print axioms ProofFile.Honest.K12.Sim2.written_roots_in_front
#print axioms ProofFile.Honest.K12.Sim2.written_opens_fit
#print axioms ProofFile.Honest.K12.Sim2.written_trees_sent
#print axioms ProofFile.Honest.K12.Sim2.written_tests_can_say_no
#print axioms ProofFile.Honest.K12.Sim2.index_of_single_place
#print axioms ProofFile.Honest.K12.Sim2.cut_at_last_test
#print axioms ProofFile.Honest.K12.Sim2.premises_at_last_test
#print axioms ProofFile.Honest.K12.Sim2.bound_at_second_member
#print axioms ProofFile.Honest.K12.Sim2.bound_at_first_member
#print axioms ProofFile.Honest.K12.Sim2.bud_L
#print axioms ProofFile.Honest.K12.Sim2.aloneInFirstChain
#print axioms ProofFile.Honest.K12.Sim2.asks_in_first_chain
#print axioms ProofFile.Honest.K12.Sim2.bound_rest_first_chain
#print axioms ProofFile.Honest.K12.Sim2.bound_rest_at_first_chain
