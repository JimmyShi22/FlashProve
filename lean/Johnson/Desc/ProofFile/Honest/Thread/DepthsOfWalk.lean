-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/DepthsOfWalk.lean: `DepthsAt` at every stand of `WalkedTo`, at any thread
of the first or the shared chain, from the description's tests on the plan and from one test on the
prover's sides. Nothing is read of the field `table`: the walk itself says what it must be. Behind a
sub-protocol `Thread.Hand` says that each new tree is one that `play` told, whose depth the block states, and
`Table.same` compares depths. An older tree's table stays what it was, since the challenges that fix it
stay. `opened_fits` says that an opening is at the depth at which the tree is sent.

  `DepthsSent`   each tree that is at hand has the depth that the flat list states
  `half_of_rooted`   the head's test gives the premise `hhalf`
  `sent_at_block`   where a tree of a sub-protocol stands in `sentOf`
  `depthsSent_walk`   at every stand of the walk
  `depthsAt_walk`   `DepthsAt` there
  `depthsAt_first`, `depthsAt_shared`   the same at the description's two chains

The premise `hhalf` is that of `depth_by_play` (Honest/Small/DepthByPlay.lean): a sub-protocol has a part of the
prover's, or none of its rounds has a root. This file proves nothing about soundness, completeness,
hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.OpensOfPlan
import Johnson.Desc.ProofFile.Honest.Thread.WalkedTo
import Johnson.Desc.ProofFile.Honest.Thread.PaysLaw
import Johnson.Desc.ProofFile.Honest.Small.DepthByPlay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc
open ProofFile.Honest.Small

variable {S Cl V W X Pb Xi : Type} {Bk : ProverCoinCounts}

/-- **Each tree at hand has the depth that the flat list states.** A definition. -/
def DepthsSent (T : Thread Bk S Cl V W X Pb) (b : Nat) (k : Coins Bk) (m : Mid W X) : Prop :=
  ∀ j, j < treesTo T.bs b →
    ((sentOf T.bs)[j]?).map (·.1) = some (T.tableAt (.own j) k m).2.logLength

theorem fit_length : ∀ (l : List Fmt.DeclaredRound) (d : List Fmt.Drawn),
    drawsFit l d = true → d.length = l.length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [drawsFit] at h
  | _ :: _, [], h => by simp [drawsFit] at h
  | _ :: l, _ :: d, h => by
    simp only [drawsFit, Bool.and_eq_true] at h
    simp only [List.length_cons, fit_length l d h.2]

theorem sentOf_eq (bs : List (Block S Cl)) :
    sentOf bs = (bs.flatMap fun x => x.oracles.flatMap id).map fun o => (o.logLength, o.words) := by
  unfold sentOf
  induction bs with
  | nil => rfl
  | cons x l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, List.map_append, ih]
    congr 1
    induction x.oracles with
    | nil => rfl
    | cons a t ih2 =>
      rw [List.flatMap_cons, List.flatMap_cons, List.map_append, ih2]
      rfl

/-- **Where a tree of a sub-protocol stands.** -/
theorem sent_at_block {bs : List (Block S Cl)} {b j : Nat} {blk : Block S Cl}
    (hb : bs[b]? = some blk) (h1 : treesTo bs b ≤ j) :
    ((sentOf bs)[j]?).map (·.1) =
      (((bs.drop b).flatMap fun x => x.oracles.flatMap id)[j - treesTo bs b]?).map (·.logLength) := by
  have e : (bs.flatMap fun x => x.oracles.flatMap id) =
      ((bs.take b).flatMap fun x => x.oracles.flatMap id) ++
        ((bs.drop b).flatMap fun x => x.oracles.flatMap id) := by
    rw [← List.flatMap_append, List.take_append_drop]
  have hl : ((bs.take b).flatMap fun x => x.oracles.flatMap id).length = treesTo bs b := rfl
  rw [sentOf_eq, List.getElem?_map, e, List.getElem?_append_right (by rw [hl]; exact h1), hl,
    Option.map_map]
  cases ((bs.drop b).flatMap fun x => x.oracles.flatMap id)[j - treesTo bs b]? <;> rfl

/-- The head's test `rooted` is the premise of the laws below. -/
theorem half_of_rooted {bs : List (Block S Cl)} {hs : List (Placed V W X)}
    (h : rooted bs hs = true) :
    ∀ x ∈ bs, (hs.any fun g => g.place == x.place) = true ∨ ∀ d ∈ x.rounds, d.entry.roots = 0 := by
  intro x hx
  unfold rooted at h
  have h1 := List.all_eq_true.1 h x hx
  rw [Bool.or_eq_true] at h1
  rcases h1 with a | a
  · exact .inl a
  · exact .inr fun d hd => beq_iff_eq.1 (List.all_eq_true.1 a d hd)

/-- **At every stand of the walk.** -/
theorem depthsSent_walk (T : Thread Bk S Cl V W X Pb) (hfit : T.fits T.bs.length = true)
    (hhalf : ∀ x ∈ T.bs, (T.hs.any fun g => g.place == x.place) = true ∨
      ∀ d ∈ x.rounds, d.entry.roots = 0)
    {m₀ : Coins Bk → Mid W X} {k : Coins Bk} {b : Nat} {m : Mid W X}
    (hw : WalkedTo T m₀ k b m) : DepthsSent T b k m := by
  induction hw with
  | start =>
    intro j hj
    exact absurd hj (Nat.not_lt_zero _)
  | @next b blk m E ds y cols w hblk hs hf hd hM hH ih =>
    obtain ⟨⟨l, hl, hp⟩, -⟩ := hM
    have hin := (play_mid _ _ _ _ _ hp).1
    have hhe := play_heard _ _ _ _ _ hp
    have hf' : drawsFit (T.ahead ++ declsTo T.bs b) m.st.heard = true := hf
    have hlen : m.st.heard.length = T.front + roundsTo T.bs b := by
      rw [fit_length _ _ hf', List.length_append]
      rfl
    have hbl : b < T.bs.length := (List.getElem?_eq_some_iff.1 hblk).1
    have hfit' := hfit
    unfold Thread.fits at hfit'
    simp only [Bool.and_eq_true] at hfit'
    intro j hj
    by_cases hjb : j < treesTo T.bs b
    · have hmem : (Fmt.TreeSource.own j) ∈ T.hand b :=
        List.mem_append_right _ (List.mem_map.2 ⟨j, List.mem_range.2 hjb, rfl⟩)
      have hfx := of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1 hfit'.1.2 b
        (List.mem_range.2 (by omega))) _ hmem)
      have e : T.tableAt (.own j) k (y.2.took cols) = T.tableAt (.own j) k m := by
        show T.table _ k y.2.st.input (y.2.st.heard.take _) = T.table _ k m.st.input _
        rw [hin, hhe, List.take_append_of_le_length (by omega)]
      rw [e]
      exact ih j hjb
    · have hjb' : treesTo T.bs b ≤ j := Nat.le_of_not_lt hjb
      have hmem : (Fmt.TreeSource.own j) ∈ T.hand (b + 1) :=
        List.mem_append_right _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)
      have h1 := hH.2 _ hmem
      unfold Thread.handAt at h1
      have ht : (E.add y.1).tree (.own j) = ((tablesOf y.1)[j - treesTo T.bs b]?).bind id := by
        show (if j < E.sent then _ else _) = _
        rw [hs, if_neg hjb]
      rw [ht] at h1
      have hsh : ∀ x ∈ [blk], Listed x := by
        intro x hx
        obtain rfl := List.mem_singleton.1 hx
        have h2 := List.all_eq_true.1 hfit'.1.1.1.2 x (List.mem_of_getElem? hblk)
        simp only [Bool.and_eq_true] at h2
        exact ⟨beq_iff_eq.1 h2.1, beq_iff_eq.1 h2.2⟩
      have hmv := steps_moved_or hl fun x hx => by
        obtain rfl := List.mem_singleton.1 hx
        exact hhalf x (List.mem_of_getElem? hblk)
      have hdp := tables_depths l _ _ _ _ hp (steps_rooted hl hsh) hmv
      rw [steps_oracles_all hl] at hdp
      have hq := congrArg (fun L => L[j - treesTo T.bs b]?) hdp
      simp only [List.getElem?_map] at hq
      have hsent := sent_at_block hblk hjb'
      have hdrop : T.bs.drop b = blk :: T.bs.drop (b + 1) := by
        rw [List.drop_eq_getElem_cons hbl]
        congr 1
        exact (List.getElem_eq_iff hbl).2 hblk
      have hlt : j - treesTo T.bs b < (blk.oracles.flatMap id).length := by
        have e2 : treesTo T.bs (b + 1) = treesTo T.bs b + (blk.oracles.flatMap id).length := by
          unfold treesTo
          rw [List.take_add_one, List.flatMap_append, List.length_append, hblk]
          simp
        omega
      rw [hsent, hdrop, List.flatMap_cons, List.getElem?_append_left hlt]
      have hq' : ((tablesOf y.1)[j - treesTo T.bs b]?).map (fun t => t.map fun u => u.2.logLength) =
          ((blk.oracles.flatMap id)[j - treesTo T.bs b]?).map fun o => some o.logLength := by
        simpa using hq
      cases hto : (tablesOf y.1)[j - treesTo T.bs b]? with
      | none =>
        rw [hto] at h1
        cases h1
      | some t =>
        cases t with
        | none =>
          rw [hto] at h1
          cases h1
        | some u =>
          rw [hto] at h1 hq'
          have h3 : (u.1 == (T.tableAt (.own j) k (y.2.took cols)).1 &&
              u.2.same (T.tableAt (.own j) k (y.2.took cols)).2) = true := h1
          rw [Bool.and_eq_true] at h3
          have h4 := h3.2
          unfold Table.same at h4
          rw [Bool.and_eq_true, Bool.and_eq_true] at h4
          have hu : u.2.logLength = (T.tableAt (.own j) k (y.2.took cols)).2.logLength :=
            beq_iff_eq.1 h4.1.1
          cases hor : (blk.oracles.flatMap id)[j - treesTo T.bs b]? with
          | none =>
            rw [hor] at hq'
            cases hq'
          | some o =>
            rw [hor] at hq'
            have ho : u.2.logLength = o.logLength := by
              have := Option.some.inj (Option.some.inj hq')
              exact this
            show some o.logLength = _
            rw [← ho, hu]

/-- **\`DepthsAt\` at every stand of the walk**, on a chain other than the last. -/
theorem depthsAt_walk {F : FileDescription Xi} (hp : F.planOk = true) (T : Thread Bk S Cl V W X Pb)
    {i : Nat} (hi : (T.bs.flatMap (·.rounds), i) ∈ [(F.roundsDeclaredByBlocks.1, 0), (F.roundsDeclaredByBlocks.2.1, 1), (F.roundsDeclaredByBlocks.2.2, 2)])
    (hi2 : i ≠ 2)
    (hj : (sentOf T.bs, i) ∈
      [(sentOf F.first.blocksInOrder, 0), (sentOf F.shared.blocksInOrder, 1), (sentOf F.second.blocksInOrder, 2)])
    (hfit : T.fits T.bs.length = true)
    (hhalf : ∀ x ∈ T.bs, (T.hs.any fun g => g.place == x.place) = true ∨
      ∀ d ∈ x.rounds, d.entry.roots = 0)
    {m₀ : Coins Bk → Mid W X} {k : Coins Bk} {b : Nat} {m : Mid W X}
    (hw : WalkedTo T m₀ k b m) : DepthsAt T b k m := by
  intro d hd o ho
  have hor := roots_of_fits hfit
  have hav := opensAvailable_of_plan hp T hi hi2 hor b
  have hmem : o.2 ∈ T.hand b :=
    of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1 hav d hd) o ho)
  have hdm : d ∈ T.bs.flatMap (·.rounds) := by
    have e : T.bs.flatMap (·.rounds) = declsTo T.bs b ++ (T.bs.drop b).flatMap (·.rounds) := by
      unfold declsTo
      rw [← List.flatMap_append, List.take_append_drop]
    rw [e]
    exact List.mem_append_left _ hd
  have hfit' := hfit
  unfold Thread.fits at hfit'
  simp only [Bool.and_eq_true] at hfit'
  cases hs : o.2 with
  | taken ch n =>
    have hT := inTime_plan hp
    unfold BookPlan.inTime at hT
    have h1 := List.all_eq_true.1 hT (T.bs.flatMap (·.rounds), i) hi
    obtain ⟨r, hr⟩ := List.mem_iff_getElem?.1 hdm
    have h3 := List.all_eq_true.1 (List.all_eq_true.1 h1 (d, r) (by
      have e := mem_zipIdx_of _ 0 r d hr
      rw [Nat.zero_add] at e
      exact e)) o ho
    rw [hs] at h3
    have h4 : (i == 2 && decide (ch < 2) && (BookPlan.roundOfRoot
        (([F.roundsDeclaredByBlocks.1, F.roundsDeclaredByBlocks.2.1, F.roundsDeclaredByBlocks.2.2][ch]?).getD []) n).isSome) = true := h3
    rw [Bool.and_eq_true, Bool.and_eq_true] at h4
    exact absurd (beq_iff_eq.1 h4.1.1) hi2
  | own n =>
    rw [hs] at hmem
    rcases List.mem_append.1 hmem with ht | hr
    · have h2 := List.all_eq_true.1 hfit'.1.1.2 _ ht
      cases h2
    · obtain ⟨n', hn', e⟩ := List.mem_map.1 hr
      obtain rfl : n' = n := Fmt.TreeSource.own.inj e
      have hn := List.mem_range.1 hn'
      have hf := opened_fits hp hi hdm ho hj (by rw [hs]; rfl)
      rw [hs] at hf
      have hf' : (sentOf T.bs)[n']? = some (o.1.a, o.1.W) := hf
      have hD := depthsSent_walk T hfit hhalf hw n' hn
      rw [hf'] at hD
      exact (Option.some.inj hD).symm

/-- **At the description's first chain.** -/
theorem depthsAt_first {F : FileDescription Xi} (hp : F.planOk = true)
    (T : Thread Bk F.S₁ F.Cl V W X Pb) (hbs : T.bs = F.first.blocksInOrder)
    (hfit : T.fits T.bs.length = true)
    (hhalf : ∀ x ∈ T.bs, (T.hs.any fun g => g.place == x.place) = true ∨
      ∀ d ∈ x.rounds, d.entry.roots = 0)
    {m₀ : Coins Bk → Mid W X} {k : Coins Bk} {b : Nat} {m : Mid W X}
    (hw : WalkedTo T m₀ k b m) : DepthsAt T b k m :=
  depthsAt_walk hp T (i := 0) (by rw [hbs]; exact .head _) (by decide) (by rw [hbs]; exact .head _)
    hfit hhalf hw

/-- **At the description's shared chain.** -/
theorem depthsAt_shared {F : FileDescription Xi} (hp : F.planOk = true)
    (T : Thread Bk F.S₂ F.Cl V W X Pb) (hbs : T.bs = F.shared.blocksInOrder)
    (hfit : T.fits T.bs.length = true)
    (hhalf : ∀ x ∈ T.bs, (T.hs.any fun g => g.place == x.place) = true ∨
      ∀ d ∈ x.rounds, d.entry.roots = 0)
    {m₀ : Coins Bk → Mid W X} {k : Coins Bk} {b : Nat} {m : Mid W X}
    (hw : WalkedTo T m₀ k b m) : DepthsAt T b k m :=
  depthsAt_walk hp T (i := 1) (by rw [hbs]; exact .tail _ (.head _)) (by decide)
    (by rw [hbs]; exact .tail _ (.head _)) hfit hhalf hw

end ProofFile.Honest

#print axioms ProofFile.Honest.DepthsSent
#print axioms ProofFile.Honest.fit_length
#print axioms ProofFile.Honest.sentOf_eq
#print axioms ProofFile.Honest.sent_at_block
#print axioms ProofFile.Honest.half_of_rooted
#print axioms ProofFile.Honest.depthsSent_walk
#print axioms ProofFile.Honest.depthsAt_walk
#print axioms ProofFile.Honest.depthsAt_first
#print axioms ProofFile.Honest.depthsAt_shared
