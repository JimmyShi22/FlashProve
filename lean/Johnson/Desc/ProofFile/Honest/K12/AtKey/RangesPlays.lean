-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/RangesPlays.lean: the key file's test on the ranges plays at
the first chain's thread (laid₁, E2E/KeyRest.lean), from the thread's pair, and its new trees are
the thread's tables: PlaysS at member 15, general in the letter Said.

  trees_of_member   trees_of_thr (K12/TreesOfThr.lean) without hst and hrs: under Moved, the half
                    and the count of oracle messages they follow
  sendRound_behind  a tree behind all those of a first list of rounds is sent behind that list
  fixed_rng         at the thread's field fixed, the test's tree number τ is fixed by the
                    challenges in front of the test and seedRound τ more
  words_treeTable   the width of a sending's first table
  agree_rng         the two parts' readers agree, at the coins that the book lends, in scope
  old_rng           at a stand of the thread: each older tree that the test opens is at hand, at
                    the declared width
  playsS_rng        PlaysS at member 15

The premises of playsS_rng. hhalf: the half stands at the place. hTb: the thread's table behind tree
1 is the sending's (TbIsSent, E2E/KeyRangesWholeS.lean), asked from the pair. htb: the thread's
tables behind the trees 2, 3, 4 are the test's own (testTbl, K12/ScriptLots.lean), at the number of
rounds in front of the test and the constant yes; it is an equation of functions and reads no run.

By what. playsS_at_test (K12/AtFile/PlaysAtTest.lean), stages_plays, member15, seatOf_rngEntry
(E2E/KeyRangesK12.lean), trees15_laid (E2E/KeyRangesTrees.lean), rows_heard_rng (RangesHeard.lean),
the closed lines of RangesLinesKernel.lean.

Limits.
- NOT IN FRONT OF A LAW OVER COINS: each statement with Thr or ThrS as a premise, and the end
  PlaysS, which has that pair as a premise.
- That the pair holds at any run is not said here. At a thread that holds nowhere the theorem is
  idle.
- No guard stands at this test: it reads no opened column. So what it sends at a stand is made at
  the state on entry recRanges, which is made of the plan's public part; at a stand of the thread
  rec_of_thr (E2E/KeyRangesJob.lean) shows it to be the verifier's. At a run or a walk behind a
  refusal nothing here speaks of it.
- tb is a letter: htb and hTb are met by definition at a table that is laid out of these two texts,
  and they say nothing of a run there. That the play sends such tables is what PlaysS adds.
- PlaysS says nothing of what the rows hold: the rows' truth is RowsTrue (RangesAccepted.lean).
- In scope; at the written sizes.
- Nothing on completeness, soundness or hiding.
-/
import E2E.KeyRangesWholeS
import Johnson.Desc.ProofFile.Honest.K12.TreesOfThr
import Johnson.Desc.ProofFile.Honest.K12.AtFile.PlaysAtTest
import Johnson.Desc.ProofFile.Honest.K12.AtKey.RangesHeard
import Johnson.Desc.ProofFile.Honest.K12.AtKey.RangesLinesKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtKey
open VerifiableInference.Desc (Block Place sendRound)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.Key (Xi FirstState Claim enterRanges leaveRanges enterAndAsk
  rangesParams)
open OnBytes.Slice (GF)
open H2K.Member (piKRFull nKRFull)
open H2K.JointK (rngEntry keyFirstPre keyFirstPost keyFirst_cut)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription)
open AtPublicFiles.KeyBook (KeyPub fullPub keyBook)
open AtPublicFiles.KeyTest (sMsg)
open AtPublicFiles.KeyThread (KeyFill laid₁ D rangesTestJob jobRng_p jobRng_rows sentRanges TbIsSent purse_cut
  own1_hand member15 seatOf_rngEntry stages_KRJ stages_plays place_sourced fixed_laid listed_laid
  trees15_laid pre_length rootsOf rootsOf_cons sendRound_append treesTo_roots decls_split sent_codes
  sent_msgs)
open VerifierAndGoals (InScope)

/-- **trees_of_thr without hst and hrs.** -/
theorem trees_of_member {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb) {b : Nat}
    {blk : Block S Cl} (hblk : T.bs[b]? = some blk) (J : TestJob W X)
    (hfresh : J.fresh.isNone = false) (hR : RowsOfHeard J)
    (hk : ∀ a ∈ J.p.nums.stages, a.h ≤ a.k)
    (hpl : blk.place = J.p.place)
    (hhalf : (T.hs.find? fun g => g.place == blk.place) = some (proverSideOfProximityTest J))
    (hcount : (blk.oracles.flatMap id).length + 1 = J.p.nums.stages.length)
    (own₀ : X)
    (htable : ∀ τ, τ + 1 < J.p.nums.stages.length → T.table (.own (treesTo T.bs b + τ)) =
      testTbl T.chain J own₀ (T.front + roundsTo T.bs b) (fun _ _ _ => true) τ)
    (hfixed : ∀ τ, τ + 1 < J.p.nums.stages.length → T.fixed (.own (treesTo T.bs b + τ)) =
      T.front + roundsTo T.bs b + seedRound J.p.nums.stages τ) :
    ∀ k st m E ds y cols, Thr T b k st m E → drawsFit blk.rounds ds = true →
      T.Moved blk k m E ds y cols → T.Trees (T.fresh b) k y.2 (E.add y.1) := by
  intro k st m E ds y cols hT hd hMv σ hσ
  have hMv' := hMv
  unfold Thread.Moved at hMv'
  obtain ⟨⟨l, hl, -⟩, -⟩ := hMv'
  obtain ⟨ho, hr⟩ := ProofFile.Honest.Small.member_lengths hhalf hl
  obtain ⟨i, hi, -⟩ := K14.fresh_mem_own T hblk hσ
  have hi' : i + 1 < J.p.nums.stages.length := by omega
  obtain ⟨s, t, rest, hst⟩ : ∃ a b r, J.p.nums.stages = a :: b :: r := by
    cases hh : J.p.nums.stages with
    | nil =>
      rw [hh] at hi'
      simp only [List.length_nil] at hi'
      omega
    | cons a u =>
      cases u with
      | nil =>
        rw [hh] at hi'
        simp only [List.length_cons, List.length_nil] at hi'
        omega
      | cons b r => exact ⟨a, b, r, rfl⟩
  have hzl := ProofFile.Honest.Small.zip_length ho hr
  have l1 : (firstPart J : Part V W X).moves.length = firstLen J.p.nums.stages := by
    rw [first_moves]
    exact (List.length_map _).trans List.length_range
  have l2 : (restPart J : Part V W X).moves.length = restLen J.p.nums.stages := by
    rw [rest_moves J s t rest hst]
    exact (List.length_map _).trans List.length_range
  have hrs : (blk.rounds.zip blk.oracles).length =
      firstLen J.p.nums.stages + restLen J.p.nums.stages := by
    refine hzl.trans ?_
    show (firstPart J : Part V W X).moves.length + ((restPart J : Part V W X).moves.length + 0) = _
    rw [l1, l2, Nat.add_zero]
  exact trees_of_thr T hblk J hfresh hR hk s t rest hst hpl hhalf hrs hcount own₀ htable hfixed k st
    m E ds y cols hT hd hMv σ hσ

/-- **A tree behind all those of a first list of rounds is sent behind that list.** -/
theorem sendRound_behind : ∀ (l₁ l₂ : List Fmt.DeclaredRound) (j : Nat),
    sendRound (l₁ ++ l₂) (rootsOf l₁ + j) = (sendRound l₂ j).map (· + l₁.length)
  | [], l₂, j => by
    have e : rootsOf ([] : List Fmt.DeclaredRound) = 0 := rfl
    rw [List.nil_append, e, Nat.zero_add]
    cases sendRound l₂ j <;> rfl
  | r :: l, l₂, j => by
    have e : sendRound (r :: (l ++ l₂)) (rootsOf (r :: l) + j) =
        if rootsOf (r :: l) + j < r.entry.roots then some 0
        else (sendRound (l ++ l₂) (rootsOf (r :: l) + j - r.entry.roots)).map (· + 1) := rfl
    have hn : ¬ (r.entry.roots + rootsOf l + j < r.entry.roots) := by omega
    rw [List.cons_append, e, rootsOf_cons, if_neg hn,
      show r.entry.roots + rootsOf l + j - r.entry.roots = rootsOf l + j by omega,
      sendRound_behind l l₂ j]
    cases sendRound l₂ j with
    | none => rfl
    | some i =>
      show some (i + l.length + 1) = some (i + (l.length + 1))
      rfl

/-- The width of a sending's first table. -/
theorem words_treeTable (P : VerifiableInference.Desc.K1.Par) (Vr : Nat → Johnson.Prover.Send.Rows)
    (T : Table) (hT : (K1.treeTables P Vr)[0]? = some T) :
    T.words = (P.trees.getD 0 {}).mainWidth + (P.trees.getD 0 {}).maskWidth := by
  unfold K1.treeTables at hT
  rw [List.getElem?_map, List.getElem?_zipIdx] at hT
  cases ht : P.trees[0]? with
  | none =>
    rw [ht] at hT
    cases hT
  | some t =>
    rw [ht] at hT
    obtain rfl := Option.some.inj hT
    rw [List.getD_eq_getElem?_getD, ht]
    rfl

section
variable {W₀ Rc Cells M Smp Rec X' : Type} {Z : VerifierAndGoals.PublicFiles} {K₀ : KeyPub}
  (Xs : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
  (Pl : VerifiableInference.Desc.Key.LaterPlaces)
  (entry : Local W₀ Rc Xi Unit → Nat → Nat → GF) (groups : List (List Nat)) (first : Nat)

/-- The sending's first table has the written width, in scope. -/
theorem words_rng (hsrc : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (Vr : Nat → Johnson.Prover.Send.Rows) (T : Table)
    (hT : (K1.treeTables (sentRanges Xs entry groups first).P Vr)[0]? = some T) :
    T.words = msgWords := by
  have hc := sent_codes Xs N Pl entry groups first hsrc scope
  have hs := sent_msgs Xs N Pl entry groups first hsrc scope
  have e : (sentRanges Xs entry groups first).P.trees = parKR.trees := by
    unfold VerifiableInference.Desc.K1.Par.trees
    rw [hc, hs, sent_parKR]
    all_goals rfl
  rw [words_treeTable _ _ T hT, e]
  all_goals rfl

/-- **The two parts' readers agree**, at the coins that the book lends, in scope. -/
theorem agree_rng (hK : fullPub = some K₀) (hsrc : KeySourced Z Xs N Pl)
    (scope : InScope Z = true) (k : Coins (keyBook K₀))
    (c : RowCoins [(firstPart (rangesTestJob (X' := X') Xs N Pl entry groups first) :
      Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X'),
      restPart (rangesTestJob (X' := X') Xs N Pl entry groups first)])
    (hc : lendRow (keyBook K₀) ((keyBook K₀).rowsOf 0) (k.look 0)
      (rangesTestJob (X' := X') Xs N Pl entry groups first).p.place
      [(firstPart (rangesTestJob (X' := X') Xs N Pl entry groups first) :
        Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X'),
        restPart (rangesTestJob (X' := X') Xs N Pl entry groups first)] 0 = .ok c)
    (w : Local W₀ Rc Xi Unit) (fr : Front X') :
    Agree (rangesTestJob (X' := X') Xs N Pl entry groups first) w fr
      (rangesTestJob (X' := X') Xs N Pl entry groups first).s₀
      (firstRd (rangesTestJob (X' := X') Xs N Pl entry groups first) c.1)
      (restCoins (rangesTestJob (X' := X') Xs N Pl entry groups first) c.2.1) := by
  obtain rfl := AtPublicFiles.AtFiles.Full.nums_sourced hsrc scope
  obtain ⟨s₁, t₁, rest₁, hst, hk⟩ :=
    stages_KRJ (rangesTestJob (X' := X') Xs nKRFull Pl entry groups first) H2K.Member.params_KR
  have hk' : (rangesTestJob (X' := X') Xs nKRFull Pl entry groups first).s₀.k =
      (H2K.Pub.sgOf (rangesTestJob (X' := X') Xs nKRFull Pl entry groups first).s₀).h +
        (H2K.Pub.sgOf (rangesTestJob (X' := X') Xs nKRFull Pl entry groups first).s₀).g := by
    unfold TestJob.s₀
    rw [hst]
    exact hk
  exact agree_of_ties' _ (sMsg, 1) rfl (keyBook K₀) _ _ c hc _ _ (ties_ranges K₀ hK) hk'
    fun mem mem' h => congrArg _ (jobRng_rows Xs nKRFull Pl entry groups first _ _ mem mem' h)

variable (L : KeyFill (keyBook K₀) W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
  (hs : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X'))
  (tb : Fmt.TreeSource → Coins (keyBook K₀) → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)

/-- **At the thread's field fixed, with no slack**: the test's tree number τ is fixed by the
challenges in front of the test and seedRound τ more, in scope. -/
theorem fixed_rng (hsrc : KeySourced Z Xs N Pl) (scope : InScope Z = true) {τ : Nat} (hτ : τ < 3) :
    (laid₁ Xs N Pl L w₀ rc x hs tb).fixed (.own (2 + τ)) =
      (laid₁ Xs N Pl L w₀ rc x hs tb).front + roundsTo (laid₁ Xs N Pl L w₀ rc x hs tb).bs 15 +
        seedRound piKRFull.nums.stages τ := by
  have hl := listed_laid Xs N Pl L w₀ rc x hs tb hsrc.named
  have h2 : rootsOf (declsTo (laid₁ Xs N Pl L w₀ rc x hs tb).bs 15) = 2 :=
    (treesTo_roots _ (fun b hb => hl b hb) 15).symm.trans
      (trees15_laid Xs N Pl L w₀ rc x hs tb hsrc scope)
  have hcut : (laid₁ Xs N Pl L w₀ rc x hs tb).bs =
      keyFirstPre Xs.Y.k.oneTime Xs.Y.D.1 Xs.Y.told.1 Xs.set N ++
        rngEntry Xs.Y.k.oneTime N :: keyFirstPost Xs.Y.k.oneTime Xs.Y.D.1 Xs.Y.told.1 Xs.set N :=
    keyFirst_cut _ _ _ _ _
  have hdrop : (laid₁ Xs N Pl L w₀ rc x hs tb).bs.drop 15 =
      rngEntry Xs.Y.k.oneTime N :: keyFirstPost Xs.Y.k.oneTime Xs.Y.D.1 Xs.Y.told.1 Xs.set N := by
    rw [hcut]
    exact List.drop_left' (pre_length scope hsrc.named)
  have hr : (rngEntry Xs.Y.k.oneTime N).rounds =
      (proximityTestKind guardedProximityTestParts piKRFull : Block T12 Unit).rounds := by
    have e := (seatOf_rngEntry Xs.Y.k.oneTime N (bare (rangesParams N) false) rfl).rounds
    rw [← place_sourced hsrc scope]
    exact e
  have hf : ((laid₁ Xs N Pl L w₀ rc x hs tb).bs.drop 15).flatMap (·.rounds) =
      (proximityTestKind guardedProximityTestParts piKRFull : Block T12 Unit).rounds ++
        (keyFirstPost Xs.Y.k.oneTime Xs.Y.D.1 Xs.Y.told.1 Xs.set N).flatMap
          (fun b : Block FirstState Claim => b.rounds) := by
    refine (congrArg (List.flatMap (fun b : Block FirstState Claim => b.rounds)) hdrop).trans ?_
    rw [List.flatMap_cons, hr]
  have hsend : sendRound ((laid₁ Xs N Pl L w₀ rc x hs tb).bs.flatMap (·.rounds)) (2 + τ) =
      some (seedRound piKRFull.nums.stages τ + roundsTo (laid₁ Xs N Pl L w₀ rc x hs tb).bs 15) := by
    rw [decls_split _ 15, ← h2, sendRound_behind, hf,
      sendRound_append _ _ _ (Nat.lt_of_lt_of_le hτ roots_KR), seeds_KR τ hτ]
    all_goals rfl
  have e : Small.sentIn ((laid₁ Xs N Pl L w₀ rc x hs tb).bs.flatMap (·.rounds)) (2 + τ) =
      seedRound piKRFull.nums.stages τ + roundsTo (laid₁ Xs N Pl L w₀ rc x hs tb).bs 15 :=
    congrArg (fun o => Option.getD o 0) hsend
  rw [fixed_laid, e]
  omega

/-- **At a stand of the thread each older tree that the test opens is at hand, at the declared
width.** NOT IN FRONT OF A LAW OVER COINS. -/
theorem old_rng (hK : fullPub = some K₀) (hsrc : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {k : Coins (keyBook K₀)} {s : FirstState} {m : Mid (Local W₀ Rc Xi Unit) X'} {E : Env}
    (hT : Thr (laid₁ Xs N Pl L w₀ rc x hs tb) 15 k s m E)
    (hTb : TbIsSent Xs N Pl entry groups first L w₀ rc x hs tb k m) :
    ∀ d ∈ (proximityTestKind guardedProximityTestParts (rangesTestJob (X' := X') Xs N Pl entry groups first).p :
        Block T12 Unit).rounds, ∀ o ∈ d.opens, oldSrc E.sent o.2 = true →
      ∃ pt, E.tree o.2 = some pt ∧ pt.2.words = o.1.W := by
  obtain ⟨c₁, hown⟩ := purse_cut Xs N Pl entry groups first hK hsrc scope k
  have hTab := hTb c₁ hown
  obtain ⟨pt, hE, -, hsame⟩ := (laid₁ Xs N Pl L w₀ rc x hs tb).handAt_elim
    (hT.1.2 _ (own1_hand Xs N Pl L w₀ rc x hs tb hsrc scope))
  have hw : pt.2.words = msgWords := by
    unfold Table.same at hsame
    rw [Bool.and_eq_true, Bool.and_eq_true] at hsame
    rw [beq_iff_eq.1 hsame.1.2]
    exact words_rng Xs N Pl entry groups first hsrc scope _ _ hTab
  have hsent : E.sent = 2 := by
    obtain ⟨-, -, -, -, ⟨-, -, e, -⟩, -, -⟩ := hT
    rw [e, trees15_laid Xs N Pl L w₀ rc x hs tb hsrc scope]
  have hp : (rangesTestJob (X' := X') Xs N Pl entry groups first).p = piKRFull :=
    (jobRng_p Xs N Pl entry groups first).trans (place_sourced hsrc scope)
  intro d hd o ho hO
  rw [hp] at hd
  rw [hsent] at hO
  have a2 := List.all_eq_true.1 (List.all_eq_true.1 opened_KR d hd) o ho
  rw [hO] at a2
  cases hσ : o.2 with
  | own n =>
    rw [hσ] at a2
    have hn : n = 1 ∧ o.1.W = msgWords := by simpa using a2
    refine ⟨pt, ?_, hw.trans hn.2.symm⟩
    rw [hn.1]
    exact hE
  | taken a b =>
    rw [hσ] at a2
    simp at a2

/-- **Member 15 plays, and its new trees are the thread's tables.**
NOT IN FRONT OF A LAW OVER COINS. -/
theorem playsS_rng (hK : fullPub = some K₀) (hsrc : KeySourced Z Xs N Pl)
    (scope : InScope Z = true)
    (Said : Nat → Coins (keyBook K₀) → Mid (Local W₀ Rc Xi Unit) X' → Prop)
    (hhalf : (hs.find? fun g => g.place == (rangesTestJob (X' := X') Xs N Pl entry groups first).p.place) =
      some (proverSideOfProximityTest (rangesTestJob (X' := X') Xs N Pl entry groups first)))
    (hTb : ∀ k s m E, ThrS (laid₁ Xs N Pl L w₀ rc x hs tb) Said 15 k s m E →
      TbIsSent Xs N Pl entry groups first L w₀ rc x hs tb k m)
    (own₀ : X')
    (htb : ∀ τ, τ < 3 → tb (.own (2 + τ)) =
      testTbl 0 (rangesTestJob (X' := X') Xs N Pl entry groups first) own₀
        (roundsTo (D Xs N Pl).first.blocksInOrder 15) (fun _ _ _ => true) τ) :
    PlaysS (laid₁ Xs N Pl L w₀ rc x hs tb) Said 15 := by
  have hp : (rangesTestJob (X' := X') Xs N Pl entry groups first).p = piKRFull :=
    (jobRng_p Xs N Pl entry groups first).trans (place_sourced hsrc scope)
  have hfr : (rangesTestJob (X' := X') Xs N Pl entry groups first).fresh.isNone = false := rfl
  have hblk : (laid₁ Xs N Pl L w₀ rc x hs tb).bs[15]? = some (rngEntry Xs.Y.k.oneTime N) :=
    member15 scope hsrc.named
  have hseat := seatOf_rngEntry Xs.Y.k.oneTime N (rangesTestJob (X' := X') Xs N Pl entry groups first) rfl
  obtain ⟨s₁, t₁, rest₁, hst, hk, P⟩ :=
    stages_plays (rangesTestJob (X' := X') Xs N Pl entry groups first) hp hfr
  have hsent := trees15_laid Xs N Pl L w₀ rc x hs tb hsrc scope
  have hlen : (rangesTestJob (X' := X') Xs N Pl entry groups first).p.nums.stages.length = 4 := by
    rw [hp]
    exact len_KR
  have hT := trees_of_member (laid₁ Xs N Pl L w₀ rc x hs tb) hblk
    (rangesTestJob (X' := X') Xs N Pl entry groups first) hfr
    (rows_heard_rng entry groups first hsrc scope)
    (by
      rw [hp]
      exact hk_KR)
    hseat.place
    (by
      rw [hseat.place]
      exact hhalf)
    (by
      rw [hseat.oracles, hp]
      exact count_KR)
    own₀
    (fun τ hτ => by
      rw [hsent]
      have h3 : τ < 3 := by omega
      show tb (.own (2 + τ)) = testTbl 0 (rangesTestJob (X' := X') Xs N Pl entry groups first) own₀
        (0 + roundsTo (D Xs N Pl).first.blocksInOrder 15) (fun _ _ _ => true) τ
      rw [Nat.zero_add]
      exact htb τ h3)
    (fun τ hτ => by
      rw [hsent, hp]
      exact fixed_rng Xs N Pl L w₀ rc x hs tb hsrc scope (by omega))
  exact AtFile.playsS_at_test (laid₁ Xs N Pl L w₀ rc x hs tb) Said hblk
    (rangesTestJob (X' := X') Xs N Pl entry groups first) _ _ hseat s₁ t₁ rest₁ hst hk hhalf 2 P hsent
    (fun k _ m _ c _ hc => agree_rng Xs N Pl entry groups first hK hsrc scope k c hc _ _)
    (fun k st m E u => old_rng Xs N Pl entry groups first L w₀ rc x hs tb hK hsrc scope u.1
      (hTb k st m E u))
    fun k st m E ds y cols u hd hMv => hT k st m E ds y cols u.1 hd hMv

end

end ProofFile.Honest.K12.AtKey

#print axioms ProofFile.Honest.K12.AtKey.trees_of_member
#print axioms ProofFile.Honest.K12.AtKey.sendRound_behind
#print axioms ProofFile.Honest.K12.AtKey.words_treeTable
#print axioms ProofFile.Honest.K12.AtKey.words_rng
#print axioms ProofFile.Honest.K12.AtKey.agree_rng
#print axioms ProofFile.Honest.K12.AtKey.fixed_rng
#print axioms ProofFile.Honest.K12.AtKey.old_rng
#print axioms ProofFile.Honest.K12.AtKey.playsS_rng
