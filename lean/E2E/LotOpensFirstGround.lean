-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotOpensFirstGround.lean: for what the key file's first chain opens: what is general
in the thread, and closed facts at the written sizes. No thread of the key file is named here.

  mem_take_cut, mem_take_at, treesTo_mono, treesTo_succ_cut, treesTo_at_cut, mem_declsTo_cut, opener_of_mem
                 lists: a list of blocks cut at one member
  opens_of_cut, declared_of_cut   GENERAL IN THE THREAD: where no tree is taken over, one member r alone
                 declares openings, each opened source with its declared depth stands in a list L, and
                 each source of L is an own tree sent up to and with r: opensAvailable at EVERY border;
                 and DepthsDeclared at every border, where the thread's table has L's depths
  depthsAt_needs   A CONTROL: behind a member that opens a source at a depth, DepthsAt is false wherever the
                 table there, as the invariant reads it, has another depth
  post_shut      in the key file's first chain no round behind the ranges' test declares an opening: at all
                 letters, off the description's text (in front of it: IOP's pre_dry, E2E/KeyRangesFront.lean)
  rng_opens, rng_trees   BY THE KERNEL, at the written place piKRFull: the test's rounds open own 1, 2, 3, 4
                 at the depths 22, 19, 17, 20, and it states three oracle messages
  handed_of_lays, testTbl_depth_at, depth_rng   a test's text (testTbl, K12/ScriptLots.lean) at ok the constant
                 yes: where laysB says yes the frame lends at every k, and the table's depth is depthAt's;
                 at every job at piKRFull with jobRanges' members and word on the fresh table, at the
                 key file's book at the written sizes: 19, 17, 20 at tau = 0, 1, 2, AT ALL k, w, h
  covers_of_stated, treeTbl_depth   a sending's text (treeTbl, K1/ScriptLots.lean): where the book covers
                 the part's count, its depth is the tree's logN, at all k, w, h
  trees_eq, msg_logN   BY THE KERNEL: the multiplicities' one tree has depth 22 at the written sizes

After: IOP's trials E2E/KeyOpensLaw.lean, KeyDepthsAt.lean and K12/DepthsOfText.lean have the twins at the
shared chain; handed_of_lays and testTbl_depth_at go their road by lendPart_ok at the second part alone.

Limits. On logLength and on declared openings alone: nothing on a table's contents, on any run, on
completeness, soundness or hiding. ok is the constant yes: where ok says no testTbl is the table of no
word, of depth 0. All that binds whoever builds on K12/ScriptLots.lean (its head) binds here.
-/
import Johnson.Desc.K12.Law.SitsKeyChains
import Johnson.Desc.ProofFile.Honest.K12.ScriptLotsTie
import Johnson.Desc.ProofFile.Honest.K12.StepsAtKey
import Johnson.Desc.ProofFile.Honest.K1.ScriptLots
import Johnson.Desc.ProofFile.Honest.K1.ScriptAtLaw
import Johnson.Desc.ProofFile.Honest.Thread.OneState
import E2E.KeyBookLends
import E2E.KeyBookHeldK1Jobs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.FirstH.Lots
open ProofFile.Honest
open VerifiableInference.Desc (Block Place Link)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.Key (FirstState Claim firstChain)
open H2K.JointK (keyFirstPost rngEntry)
open H2K.Member (piKRFull nKRFull)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub atFull Stated Within lendPart_ok look_due)
open AtPublicFiles.KeyTest (jobRanges)

/-! ## 1 Lists -/

theorem mem_take_cut {α : Type} : ∀ (pre : List α) (r : α) (post : List α) (n : Nat) (b : α),
    b ∈ (pre ++ r :: post).take n → b ∈ pre ∨ (b = r ∧ pre.length < n) ∨ b ∈ post
  | _, _, _, 0, b, h => by simp at h
  | [], r, post, n + 1, b, h => by
    rw [List.nil_append, List.take_succ_cons] at h
    rcases List.mem_cons.1 h with rfl | h
    · exact Or.inr (Or.inl ⟨rfl, Nat.succ_pos n⟩)
    · exact Or.inr (Or.inr (List.mem_of_mem_take h))
  | a :: pre, r, post, n + 1, b, h => by
    rw [List.cons_append, List.take_succ_cons] at h
    rcases List.mem_cons.1 h with rfl | h
    · exact Or.inl List.mem_cons_self
    · rcases mem_take_cut pre r post n b h with h | ⟨h, hn⟩ | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr (Or.inl ⟨h, Nat.succ_lt_succ hn⟩)
      · exact Or.inr (Or.inr h)

theorem mem_take_at {α : Type} : ∀ (pre : List α) (r : α) (post : List α) (n : Nat),
    pre.length < n → r ∈ (pre ++ r :: post).take n
  | _, _, _, 0, h => absurd h (Nat.not_lt_zero _)
  | [], r, post, n + 1, _ => by
    rw [List.nil_append, List.take_succ_cons]
    exact List.mem_cons_self
  | a :: pre, r, post, n + 1, h => by
    rw [List.cons_append, List.take_succ_cons]
    exact List.mem_cons_of_mem _ (mem_take_at pre r post n (Nat.lt_of_succ_lt_succ h))

section
variable {S Cl : Type}

theorem treesTo_mono : ∀ (bs : List (Block S Cl)) {a b : Nat}, a ≤ b → treesTo bs a ≤ treesTo bs b
  | [], a, b, _ => by simp [treesTo]
  | _ :: _, 0, b, _ => by simp [treesTo]
  | _ :: _, a + 1, 0, h => absurd h (Nat.not_succ_le_zero a)
  | x :: bs, a + 1, b + 1, h => by
    have ih := treesTo_mono bs (Nat.le_of_succ_le_succ h)
    unfold treesTo at ih ⊢
    simp only [List.take_succ_cons, List.flatMap_cons, List.length_append]
    omega

theorem treesTo_succ_cut : ∀ (pre : List (Block S Cl)) (r : Block S Cl) (post : List (Block S Cl)),
    treesTo (pre ++ r :: post) (pre.length + 1) =
      treesTo (pre ++ r :: post) pre.length + (r.oracles.flatMap id).length
  | [], r, post => by simp [treesTo]
  | a :: pre, r, post => by
    have ih := treesTo_succ_cut pre r post
    unfold treesTo at ih ⊢
    simp only [List.cons_append, List.length_cons, List.take_succ_cons, List.flatMap_cons,
      List.length_append] at ih ⊢
    omega

/-- The trees sent up to and with the member at which a list is cut. -/
theorem treesTo_at_cut {bs pre post : List (Block S Cl)} {r : Block S Cl} {a t : Nat}
    (hcut : bs = pre ++ r :: post) (hl : pre.length = a) (h0 : treesTo bs a = t) :
    treesTo bs (pre.length + 1) = t + (r.oracles.flatMap id).length := by
  subst hcut
  subst hl
  rw [treesTo_succ_cut, h0]

/-- Behind the member its rounds are among the rounds in front of the border. -/
theorem mem_declsTo_cut {bs pre post : List (Block S Cl)} {r : Block S Cl} {n : Nat}
    (hcut : bs = pre ++ r :: post) (hn : pre.length < n) {d : Fmt.DeclaredRound} (hd : d ∈ r.rounds) :
    d ∈ declsTo bs n := by
  subst hcut
  unfold declsTo
  exact List.mem_flatMap.2 ⟨r, mem_take_at pre r post n hn, hd⟩

/-- A round in front of border n that opens something is the one member's, and n lies behind it. -/
theorem opener_of_mem {pre post : List (Block S Cl)} {r : Block S Cl}
    (hpre : ∀ d ∈ pre.flatMap (·.rounds), d.opens = [])
    (hpost : ∀ d ∈ post.flatMap (·.rounds), d.opens = []) {n : Nat} {d : Fmt.DeclaredRound}
    (hd : d ∈ declsTo (pre ++ r :: post) n) {o : Fmt.Shape × Fmt.TreeSource} (ho : o ∈ d.opens) :
    pre.length < n ∧ d ∈ r.rounds := by
  unfold declsTo at hd
  obtain ⟨b, hb, hdb⟩ := List.mem_flatMap.1 hd
  rcases mem_take_cut pre r post n b hb with h | ⟨rfl, hn⟩ | h
  · rw [hpre d (List.mem_flatMap.2 ⟨b, h, hdb⟩)] at ho
    cases ho
  · exact ⟨hn, hdb⟩
  · rw [hpost d (List.mem_flatMap.2 ⟨b, h, hdb⟩)] at ho
    cases ho

end

/-! ## 2 General in the thread -/

section
variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)
  {pre post : List (Block S Cl)} {r : Block S Cl} {L : List (Fmt.TreeSource × Nat)}

/-- **opensAvailable at every border.** -/
theorem opens_of_cut (hcut : T.bs = pre ++ r :: post) (htk : T.taken = [])
    (hpre : ∀ d ∈ pre.flatMap (·.rounds), d.opens = [])
    (hpost : ∀ d ∈ post.flatMap (·.rounds), d.opens = [])
    (hop : ∀ d ∈ r.rounds, ∀ o ∈ d.opens, (o.2, o.1.a) ∈ L)
    (htr : ∀ p ∈ L, ∃ j, p.1 = .own j ∧ j < treesTo T.bs (pre.length + 1)) (n : Nat) :
    T.opensAvailable n = true := by
  unfold Thread.opensAvailable
  refine List.all_eq_true.2 fun d hd => List.all_eq_true.2 fun o ho => decide_eq_true ?_
  rw [hcut] at hd
  obtain ⟨hn, hdr⟩ := opener_of_mem hpre hpost hd ho
  obtain ⟨j, hj, hlt⟩ := htr _ (hop d hdr o ho)
  have hj' : o.2 = .own j := hj
  unfold Thread.hand
  rw [htk, List.nil_append, hj']
  exact List.mem_map.2 ⟨j, List.mem_range.2 (Nat.lt_of_lt_of_le hlt (treesTo_mono T.bs hn)), rfl⟩

/-- **DepthsDeclared at every border**, where the thread's table has the list's depths. -/
theorem declared_of_cut (hcut : T.bs = pre ++ r :: post)
    (hpre : ∀ d ∈ pre.flatMap (·.rounds), d.opens = [])
    (hpost : ∀ d ∈ post.flatMap (·.rounds), d.opens = [])
    (hop : ∀ d ∈ r.rounds, ∀ o ∈ d.opens, (o.2, o.1.a) ∈ L)
    (hdp : ∀ p ∈ L, ∀ k w h, (T.table p.1 k w h).2.logLength = p.2) (n : Nat) :
    DepthsDeclared T n := by
  intro d hd o ho k w h
  rw [hcut] at hd
  obtain ⟨-, hdr⟩ := opener_of_mem hpre hpost hd ho
  exact hdp _ (hop d hdr o ho) k w h

/-- **A control: DepthsAt can say no.** Behind a member that opens σ at the declared depth a, it is false
wherever the table at σ, as the invariant reads it, has another depth. -/
theorem depthsAt_needs (hcut : T.bs = pre ++ r :: post) {n : Nat} (hn : pre.length < n)
    {σ : Fmt.TreeSource} {a : Nat}
    (hmem : (σ, a) ∈ (r.rounds.flatMap (·.opens)).map (fun o => (o.2, o.1.a))) (k : Coins Bk)
    (m : Mid W X) (hno : (T.tableAt σ k m).2.logLength ≠ a) : ¬ DepthsAt T n k m := by
  intro hd
  obtain ⟨o, ho, heq⟩ := List.mem_map.1 hmem
  obtain ⟨d, hdr, hod⟩ := List.mem_flatMap.1 ho
  have h2 : o.2 = σ := congrArg (·.1) heq
  have ha : o.1.a = a := congrArg (·.2) heq
  have h := hd d (mem_declsTo_cut hcut hn hdr) o hod
  rw [h2, ha] at h
  exact hno h

end

/-! ## 3 The key file's first chain: who opens -/

theorem k1_shut (P : VerifiableInference.Desc.K1.Par) :
    ∀ d ∈ VerifiableInference.Desc.K1.rounds P, d.opens = [] := by
  intro d hd
  simp only [VerifiableInference.Desc.K1.rounds, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl <;> rfl

section
variable (one : OnBytes.Params.OneTime) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root)
  (set : OnBytes.Params.Setting) (N : H2U.PlaceNums)

/-- **No round behind the ranges' test declares an opening.** -/
theorem post_shut : ∀ d ∈ (keyFirstPost one D told set N).flatMap (·.rounds), d.opens = [] := by
  intro d hd
  obtain ⟨b, hb, hdb⟩ := List.mem_flatMap.1 hd
  unfold keyFirstPost at hb
  rcases List.mem_append.1 hb with hb | hb
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hb
    have ha' : a ∈ VerifiableInference.Desc.Key.batchTableRows (·.keys) one
        VerifiableInference.Desc.Key.pieces
        (VerifiableInference.Desc.Key.rootsBefore D (VerifiableInference.Desc.Key.batchRound D)) ::
        (VerifiableInference.Desc.Key.sendW one VerifiableInference.Desc.Key.pieces
          (VerifiableInference.Desc.Key.rootsBefore D (VerifiableInference.Desc.Key.batchRound D))
          (VerifiableInference.Desc.Key.groupsTold told
            (VerifiableInference.Desc.Key.rootsBefore D
              (VerifiableInference.Desc.Key.lastSendRound D))
            (VerifiableInference.Desc.Key.rootsAt D
              (VerifiableInference.Desc.Key.lastSendRound D)))).toList := ha
    rcases List.mem_cons.1 ha' with rfl | ha'
    · have h : d ∈ (([] ++ []) ++ VerifiableInference.Desc.K13.battRounds _) ++ [] := hdb
      simp only [List.nil_append, List.append_nil, VerifiableInference.Desc.K13.battRounds,
        List.mem_cons, List.mem_replicate] at h
      rcases h with rfl | rfl | ⟨-, rfl⟩ <;> rfl
    · unfold VerifiableInference.Desc.Key.sendW at ha'
      cases hm : OnBytes.linMessageW one.lin with
      | none =>
        rw [hm] at ha'
        cases ha'
      | some msg =>
        rw [hm] at ha'
        obtain rfl := List.mem_singleton.1 ha'
        have h : d ∈ (([] ++ VerifiableInference.Desc.K1.rounds _) ++ []) ++ [] := hdb
        simp only [List.nil_append, List.append_nil] at h
        exact k1_shut _ d h
  · obtain rfl := List.mem_singleton.1 hb
    have h : d ∈ [VerifiableInference.Desc.ChainEnd.sealRound] := hdb
    obtain rfl := List.mem_singleton.1 h
    rfl

end

/-- **What the ranges' test's rounds open, with the declared depths.** By the kernel. -/
theorem rng_opens : ((proximityTestKind guardedProximityTestParts piKRFull : Block T12 Claim).rounds.flatMap (·.opens)).map
    (fun o => (o.2, o.1.a)) =
      [(Fmt.TreeSource.own 1, 22), (Fmt.TreeSource.own 2, 19), (Fmt.TreeSource.own 3, 17),
        (Fmt.TreeSource.own 4, 20)] := by
  decide +kernel

/-- **It states three oracle messages.** By the kernel. -/
theorem rng_trees : ((proximityTestKind guardedProximityTestParts piKRFull : Block T12 Claim).oracles.flatMap id).length = 3 := by
  decide +kernel

/-- The list: an opened source, its declared depth. -/
def openedFirst : List (Fmt.TreeSource × Nat) :=
  [(.own 1, 22), (.own 2, 19), (.own 3, 17), (.own 4, 20)]

theorem rngEntry_opens (one : OnBytes.Params.OneTime) :
    ∀ d ∈ (rngEntry one nKRFull).rounds, ∀ o ∈ d.opens, (o.2, o.1.a) ∈ openedFirst := by
  intro d hd o ho
  have hd' : d ∈ (proximityTestKind guardedProximityTestParts piKRFull : Block T12 Claim).rounds := hd
  have h : (o.2, o.1.a) ∈ ((proximityTestKind guardedProximityTestParts piKRFull : Block T12 Claim).rounds.flatMap (·.opens)).map
      (fun o => (o.2, o.1.a)) :=
    List.mem_map.2 ⟨o, List.mem_flatMap.2 ⟨d, hd', ho⟩, rfl⟩
  rw [rng_opens] at h
  exact h

theorem rngEntry_trees (one : OnBytes.Params.OneTime) :
    ((rngEntry one nKRFull).oracles.flatMap id).length = 3 := rng_trees

theorem openedFirst_own : ∀ p ∈ openedFirst, ∃ j, p.1 = .own j ∧ j < 5 := by
  intro p hp
  simp only [openedFirst, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact ⟨1, rfl, by decide⟩
  · exact ⟨2, rfl, by decide⟩
  · exact ⟨3, rfl, by decide⟩
  · exact ⟨4, rfl, by decide⟩

/-! ## 4 A test's text -/

section
open ProofFile.Honest.K12 (TestJob testTbl handedRest laysB laysB_congr restPart jobKR full_lays depthAt
  depths seedRound msgAt_table_is_psAt inB)
variable {W X : Type}

/-- **Where laysB says yes the frame lends the second part its coins at every k.** -/
theorem handed_of_lays (B : ProverCoinCounts) (J : TestJob W X) (hB : laysB B 0 J = true) (k : Coins B) :
    ∃ c, handedRest 0 J k = some c := by
  unfold laysB at hB
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true',
    List.all_eq_true] at hB
  obtain ⟨⟨-, a7⟩, a8⟩ := hB
  have hl : ∀ a, (k.look 0 a).1 = dueAt (B.rowsOf 0) a := fun a => look_due k 0 a
  obtain ⟨c, hc⟩ := lendPart_ok B (B.rowsOf 0) (k.look 0) ⟨J.p.place, 1⟩
    (restPart (V := Empty) J) a7
    (by rw [hl]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩)
    (fun e he hsp => by
      have q := a8 e he
      have hp : e.spender.place = J.p.place := by rw [hsp]
      rw [hp] at q
      simp only [beq_self_eq_true, Bool.not_true, Bool.false_or, inB, Bool.and_eq_true,
        decide_eq_true_eq] at q
      unfold Within
      rw [hl]
      exact q)
  refine ⟨c, ?_⟩
  unfold handedRest
  rw [hc]
  rfl

/-- **A test's text has depthAt's depth at all k, w, h**, at ok the constant yes. -/
theorem testTbl_depth_at {Bk : ProverCoinCounts} (J : TestJob W X) (hk : ∀ a ∈ J.p.nums.stages, a.h ≤ a.k)
    (hB : laysB Bk 0 J = true) (own₀ : X) (n₀ : Nat) {τ a : Nat}
    (hτ : τ + 1 < J.p.nums.stages.length)
    (ha : depthAt J (seedRound J.p.nums.stages τ) = some a) (k : Coins Bk) (w : W)
    (h : List Fmt.Drawn) :
    (testTbl 0 J own₀ n₀ (fun _ _ _ => true) τ k w h).2.logLength = a := by
  obtain ⟨c, hc⟩ := handed_of_lays Bk J hB k
  unfold testTbl
  simp only [hc, ↓reduceIte, msgAt_table_is_psAt J hk w _ _ _ hτ ha, List.head?_cons,
    Option.getD_some]

theorem hk_KR : ∀ a ∈ piKRFull.nums.stages, a.h ≤ a.k := by decide +kernel

theorem len_KR : piKRFull.nums.stages.length = 4 := by decide +kernel

/-- The depths at the three sending rounds. By the kernel. -/
theorem depthAt_KR : ∀ τ, τ < 3 →
    (none :: depths jobRanges.fresh.isNone piKRFull.nums.stages).getD
      (seedRound piKRFull.nums.stages τ) none = some ([19, 17, 20].getD τ 0) := by
  decide +kernel

/-- **At the key file's book, at every job at the written place with the skeleton's members and word
on the fresh table: the depths 19, 17, 20, at all k, w, h.** -/
theorem depth_rng (K₀ : KeyPub) (hK₀ : fullPub = some K₀) (J : TestJob W X) (hp : J.p = piKRFull)
    (hm : J.members = jobRanges.members) (hf : J.fresh = jobRanges.fresh) (own₀ : X) (n₀ : Nat)
    {τ : Nat} (hτ : τ < 3) (k : Coins (keyBook K₀)) (w : W) (h : List Fmt.Drawn) :
    (testTbl 0 J own₀ n₀ (fun _ _ _ => true) τ k w h).2.logLength = [19, 17, 20].getD τ 0 := by
  have hB : laysB (keyBook K₀) 0 J = true := by
    rw [laysB_congr (keyBook K₀) 0 J jobKR hp hm hf]
    have h := full_lays
    unfold atFull at h
    rw [hK₀] at h
    exact h
  refine testTbl_depth_at J (by rw [hp]; exact hk_KR) hB own₀ n₀ (by rw [hp, len_KR]; omega) ?_ k w h
  unfold depthAt
  rw [hp, hf]
  exact depthAt_KR τ hτ

end

/-! ## 5 A sending's text -/

section
open ProofFile.Honest.K1 (SendJob sendPart treeTbl treeTbl_some lentCut lentCut_isSome bookCovers dueR
  scriptTable treeTables wordlessTable)
variable {V W Wl X : Type}

/-- A part that states what the book has for it is covered. -/
theorem covers_of_stated (B : ProverCoinCounts) (J : SendJob W X)
    (hs : Stated B B.first ⟨J.P.place, 0⟩ (sendPart (V := V) J)) :
    bookCovers B 0 ⟨J.P.place, 0⟩ (dueR J.P J.ride) = true := by
  have e : dueR J.P J.ride = dueAt B.first ⟨J.P.place, 0⟩ := congrArg (·.1) hs
  unfold bookCovers
  have e' : dueAt (B.rowsOf 0) ⟨J.P.place, 0⟩ = dueR J.P J.ride := e.symm
  rw [e']
  exact decide_eq_true ⟨Nat.le_refl _, Nat.le_refl _⟩

/-- **A sending's text has the tree's depth at all k, w, h**, where the book covers the part. -/
theorem treeTbl_depth {Bk : ProverCoinCounts} (wit : Wl → W) (J : SendJob W X) (own₀ : X) (τ : Nat)
    (hc : bookCovers Bk 0 ⟨J.P.place, 0⟩ (dueR J.P J.ride) = true) (k : Coins Bk) (w : Wl)
    (h : List Fmt.Drawn) :
    (treeTbl 0 wit J own₀ τ k w h).2.logLength = (J.P.trees.map (·.logN)).getD τ 0 := by
  have hs := lentCut_isSome k 0 (Nat.zero_le 1) ⟨J.P.place, 0⟩ (dueR J.P J.ride)
  rw [hc] at hs
  obtain ⟨c, hcc⟩ := Option.isSome_iff_exists.1 hs
  rw [treeTbl_some 0 wit J own₀ τ k c hcc w h]
  unfold scriptTable treeTables
  rw [List.getElem?_map, List.getElem?_zipIdx, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases J.P.trees[τ]? <;> rfl

/-- A sending's trees read its codes and its messages alone. -/
theorem trees_eq (P : VerifiableInference.Desc.K1.Par) (cs : OnBytes.Codes)
    (ms : Array OnBytes.OracleNotice) (hc : P.codes = cs) (hs : P.sent = ms) :
    P.trees = ((VerifiableInference.Desc.Own.treesMade cs ms).map fun y => y.shapes.toList).getD [] := by
  unfold VerifiableInference.Desc.K1.Par.trees
  rw [hc, hs]

/-- The one tree of the multiplicities' sending has depth 22, at the written sizes. By the kernel. -/
theorem msg_logN : (((VerifiableInference.Desc.Own.treesMade Lk6.AtPlan.keyFull.codes
    (OnBytes.Wf.messageOf Lk6.AtPlan.keyFull.ranges.x)).map fun y => y.shapes.toList).getD []).map
      (·.logN) = [22] := by
  decide +kernel

end

end AtPublicFiles.FirstH.Lots

#print axioms AtPublicFiles.FirstH.Lots.opens_of_cut
#print axioms AtPublicFiles.FirstH.Lots.declared_of_cut
#print axioms AtPublicFiles.FirstH.Lots.depthsAt_needs
#print axioms AtPublicFiles.FirstH.Lots.treesTo_at_cut
#print axioms AtPublicFiles.FirstH.Lots.post_shut
#print axioms AtPublicFiles.FirstH.Lots.rng_opens
#print axioms AtPublicFiles.FirstH.Lots.rng_trees
#print axioms AtPublicFiles.FirstH.Lots.rngEntry_opens
#print axioms AtPublicFiles.FirstH.Lots.rngEntry_trees
#print axioms AtPublicFiles.FirstH.Lots.openedFirst_own
#print axioms AtPublicFiles.FirstH.Lots.handed_of_lays
#print axioms AtPublicFiles.FirstH.Lots.testTbl_depth_at
#print axioms AtPublicFiles.FirstH.Lots.depth_rng
#print axioms AtPublicFiles.FirstH.Lots.covers_of_stated
#print axioms AtPublicFiles.FirstH.Lots.treeTbl_depth
#print axioms AtPublicFiles.FirstH.Lots.trees_eq
#print axioms AtPublicFiles.FirstH.Lots.msg_logN
