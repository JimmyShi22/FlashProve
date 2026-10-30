-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
THE DEBT IS MOVED INTO NAMED PREMISES, NOT PAID.
E2E/KeyFreshTreePlace.lean: a test: that `Plays` at member 9 fails at
the key's thread, at the table's letter set to `oldArm`.

Why. `Plays` asks that the trees new at a member show the thread's table from that table's place. The
test on G_u sends trees of its own. `tbKey` has a letter for them; `fresh_nine` and `not_plays` stand at the letter
set to what the table said before it had one, `oldArm`: the two sendings alone. At another letter they do
not speak.

Main names.
  `gu_trees`: at the written places the test's block declares trees. By Lean's kernel.
  `oldArm`: the letter at the old text.
  `fresh_nine`: the first tree new at member 9, and at `oldArm` the table's place for it is «send o_omega»'s.
  `not_plays_of_place`: the cause, general in the thread and its tables: a table that says another place
    than the member's, at a new own tree.
  `not_plays`: FALSE WHEREVER PLAYABLE: where a thread stands at 9 and the member's steps return at a list
    of challenges that fits, at which nothing stops, `Plays` at 9 does not hold.

What this is not. It does not say that `Plays` at 9 is false: it is a ∀ under playability, and no thread
is shown to stand at 9 at a half that plays. At the halves with no part of E2E/KeyPartsIdle.lean the
premises of `not_plays` are not shown met: by reading, `hsteps` is false there, so `Plays` at 9 is true and empty
at those halves. No mend is proposed here.

NOT IN FRONT OF A LAW OVER COINS: `not_plays` bears this label; the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean. Its ground: it stands at a run's coins `k`, and `hT` ties the
thread's letters, of the first kind. None of these is the term that the committer makes. None: the
bar is flat. The rest name no coin.

Nothing on soundness, completeness, hiding or binding.

-/
import E2E.KeyAsksKey
import E2E.KeyDoorNine

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace AtPublicFiles.KeyFreshTrial
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (TableKey TreeLay)
open VerifiableInference.Desc (Place Block)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source LaterPlaces Claim sharedTests keyAsProof descriptionFromSource)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Honest (Eight flatOf_carried)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.AtFiles.Full (QK PF par_sourced later_sourced)
open AtPublicFiles.KeyBook (KeyPub keyBook)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeySharedThread (parKey sentKey randKey threadKey)
open AtPublicFiles.KeyAsksKey (tableKey)
open AtPublicFiles.KeyTreesKey (tbKey)

/-- **The test's block at the written places declares trees of its own.** By Lean's kernel. -/
theorem gu_trees : 0 < ((H2K.JointK.keyGu PF).oracles.flatMap id).length := by
  decide +kernel

/-- The place of that block. -/
theorem gu_place : (H2K.JointK.keyGu PF).place ≠ K14.sendPlace 5 := by
  decide +kernel

section General
variable {S Cl V W X : Type}

theorem treesTo_succ {bs : List (Block S Cl)} {b : Nat} {x : Block S Cl} (h : bs[b]? = some x) :
    treesTo bs (b + 1) = treesTo bs b + (x.oracles.flatMap id).length := by
  unfold treesTo
  rw [List.take_succ, h]
  simp

theorem treesTo_mono (bs : List (Block S Cl)) (a : Nat) : ∀ n, treesTo bs a ≤ treesTo bs (a + n)
  | 0 => Nat.le_refl _
  | n + 1 => by
    refine Nat.le_trans (treesTo_mono bs a n) ?_
    show treesTo bs (a + n) ≤ treesTo bs (a + n + 1)
    cases h : bs[a + n]? with
    | none =>
      unfold treesTo
      rw [List.take_succ, h]
      simp
    | some x =>
      rw [treesTo_succ h]
      omega

/-- Every step of one member is at that member's place. -/
theorem part_place (p : Part V W X) (name : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List VerifiableInference.Desc.Oracle)) (v : Option V) (c : p.Coins) :
    ∀ s ∈ p.steps name a rs v c, s.addr = a := by
  intro s hs
  unfold Part.steps at hs
  obtain ⟨r, -, rfl⟩ := List.mem_map.1 hs
  rfl

theorem row_place (name : String) (a : Place) (v : Option V) :
    ∀ (ps : List (Part V W X)) (j : Nat) (rs : List (Fmt.DeclaredRound × List VerifiableInference.Desc.Oracle))
      (c : RowCoins ps), ∀ s ∈ rowSteps name a v ps j rs c, s.addr.place = a
  | [], _, _, _ => fun _ hs => by cases hs
  | p :: ps, j, rs, c => fun s hs => by
    rcases List.mem_append.1 hs with h | h
    · rw [part_place p name ⟨a, j⟩ _ v c.1 s h]
    · exact row_place name a v ps (j + 1) _ c.2 s h

theorem steps_place {Bk : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {v : Option V} {b : Block S Cl} {hs : List (Placed V W X)} {l : List (Step W X)}
    (hl : chainSteps Bk rows look v [b] hs = .ok l) : ∀ s ∈ l, s.addr.place = b.place := by
  cases hf : hs.find? (fun h => h.place == b.place) with
  | none =>
    simp only [chainSteps, hf] at hl
    split at hl
    · cases hl
    · have e : (b.rounds.zip b.oracles).map (fun r => (⟨b.name, ⟨b.place, 0⟩, r.1, r.2,
          fun _ _ => none, fun _ _ => none, 0, false, none⟩ : Step W X)) ++ [] = l :=
        Except.ok.inj hl
      intro s hs'
      rw [← e] at hs'
      rcases List.mem_append.1 hs' with h | h
      · obtain ⟨r, -, rfl⟩ := List.mem_map.1 h
        rfl
      · cases h
  | some h =>
    obtain ⟨c, -, rfl⟩ := ProofFile.Honest.K13.chainSteps_one hf hl
    exact row_place _ _ _ _ _ _ _

/-- Every round played is at the place of one of the steps. -/
theorem play_place : ∀ (ss : List (Step W X)) (ds : List Fmt.Drawn) (back : List Fmt.RoundView)
    (m : Mid W X) (y : List Played × Mid W X), play ss ds back m = .ok y →
    ∀ p ∈ y.1, ∃ s ∈ ss, p.place = s.addr.place
  | [], [], _, m, y, h => by
    simp only [play] at h
    cases h
    intro p hp
    cases hp
  | [], _ :: _, _, _, _, h => by simp [play] at h
  | _ :: _, [], _, _, _, h => by simp [play] at h
  | s :: ss, d :: ds, back, m, y, h => by
    obtain ⟨x, m', z, -, -, hz, rfl⟩ := play_cons_ok h
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact ⟨s, List.mem_cons_self, rfl⟩
    · obtain ⟨t, ht, e⟩ := play_place ss ds back.tail m' z hz p hp
      exact ⟨t, List.mem_cons_of_mem _ ht, e⟩

/-- Every table among the rounds played stands with the place of the round that sent it. -/
theorem tables_place (ps : List Played) (i : Nat) (u : Place × Table)
    (h : ((tablesOf ps)[i]?).bind id = some u) : ∃ p ∈ ps, u.1 = p.place := by
  cases e : (tablesOf ps)[i]? with
  | none =>
    rw [e] at h
    cases h
  | some x =>
    rw [e] at h
    obtain rfl : x = some u := h
    have hm : (some u) ∈ tablesOf ps := List.mem_of_getElem? e
    obtain ⟨p, hp, hq⟩ := List.mem_flatMap.1 hm
    obtain ⟨t, -, ht⟩ := List.mem_map.1 hq
    cases t with
    | none => cases ht
    | some a =>
      obtain rfl : (p.place, a) = u := Option.some.inj ht
      exact ⟨p, hp, rfl⟩

/-- **The cause, in a form general in the thread**: where a thread stands at a member that can be played,
and the table that it names for a new tree at an own number from `E.sent` on says another place than
the member's, `Plays` does not hold there. FALSE WHEREVER PLAYABLE: of no thread does it say that it
stands.
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem not_plays_of_place {Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb) {b n : Nat}
    {blk : Block S Cl} {k : Coins Bk} {s : S} {m : Mid W X} {E : Env} {ds : List Fmt.Drawn}
    {l : List (Step W X)} (hblk : T.bs[b]? = some blk) (hT : Thr T b k s m E)
    (hd : drawsFit blk.rounds ds = true)
    (hstop : chainStopAt (T.φ.sees m.st.input) [blk] T.hs m.loc ds = none)
    (hsteps : chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees m.st.input) [blk] T.hs =
      .ok l)
    (hmem : Fmt.TreeSource.own n ∈ T.fresh b) (hn : E.sent ≤ n)
    (hplace : ∀ (m' : Mid W X), (T.tableAt (.own n) k m').1 ≠ blk.place) : ¬ Plays T b := by
  intro hP
  obtain ⟨y, cols, hMv, hTr⟩ := hP blk hblk k s m E ds l hT hd hstop hsteps
  have hh := hTr _ hmem
  obtain ⟨⟨l', hl', hy⟩, -⟩ := hMv
  obtain rfl : l' = l := Except.ok.inj (hl'.symm.trans hsteps)
  unfold Thread.handAt at hh
  obtain ⟨u, hu, hq⟩ := (Option.any_eq_true _ _).1 hh
  have he : u.1 = (T.tableAt (.own n) k y.2).1 := beq_iff_eq.1 (Bool.and_eq_true_iff.mp hq).1
  have ht : ((tablesOf y.1)[n - E.sent]?).bind id = some u := by
    have hu' : (if n < E.sent then E.tree (.own n)
        else ((tablesOf y.1)[n - E.sent]?).bind id) = some u := hu
    rw [if_neg (by omega)] at hu'
    exact hu'
  obtain ⟨p, hp, hpe⟩ := tables_place _ _ _ ht
  obtain ⟨t, ht', hte⟩ := play_place _ _ _ _ _ hy p hp
  have hb := steps_place hsteps t ht'
  exact hplace y.2 (by rw [← he, hpe, hte, hb])

end General

/-- **The letter set to what the table said before it had a letter**: every own tree past the first sending's
is «send o_omega»'s. Every statement below stands at it. -/
def oldArm {Bk : ProverCoinCounts} {W₀ Rc : Type} (Q : _root_.Desc.K14.P14) (weights : W₀ → Weights)
    (rand : Rc → TableRand) :
    Nat → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table :=
  fun n => sendTable (jobOmega ⟨Q, 0⟩) (witOf Q weights rand) (sendPlace 5) 1 (n - treesU Q)

section
variable {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K₀ : KeyPub) (K : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w : Common W₀ Rc TableKey)

/-- **The first tree new at member 9, and where the tables say it comes from.** -/
theorem fresh_nine {Z : VerifierAndGoals.PublicFiles} (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    {layO : TreeLay} (hQ : Plan2 (parKey Xs Pl) (sentKey Xs Pl) layO)
    (B : Eight (parKey Xs Pl)) :
    (Fmt.TreeSource.own (treesTo (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk (oldArm (parKey Xs Pl) K.weights (randKey K))) rest Kp Vd w).bs 9)) ∈ (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk (oldArm (parKey Xs Pl) K.weights (randKey K))) rest Kp Vd w).fresh 9 ∧
    ∀ (k : Coins (keyBook K₀)) (m : Mid (Common W₀ Rc TableKey) X₀),
      ((threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk (oldArm (parKey Xs Pl) K.weights (randKey K))) rest Kp Vd w).tableAt (.own (treesTo (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk (oldArm (parKey Xs Pl) K.weights (randKey K))) rest Kp Vd w).bs 9)) k m).1 = K14.sendPlace 5 := by
  have hP : Pl = PF := later_sourced hs scope
  obtain ⟨h9, -⟩ := AtPublicFiles.KeyDoorNine.seat_nine Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk (oldArm (parKey Xs Pl) K.weights (randKey K))) rest Kp Vd w B
  have hgu : 0 < ((H2K.JointK.keyGu Pl).oracles.flatMap id).length := by
    rw [hP]
    exact gu_trees
  have h10 := treesTo_succ h9
  constructor
  · unfold Thread.fresh Thread.hand
    refine List.mem_filter.2 ⟨?_, ?_⟩
    · refine List.mem_append_right _ (List.mem_map.2 ⟨_, List.mem_range.2 ?_, rfl⟩)
      show _ < treesTo _ (9 + 1)
      rw [h10]
      omega
    · have hn : ¬ (Fmt.TreeSource.own (treesTo (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk (oldArm (parKey Xs Pl) K.weights (randKey K))) rest Kp Vd w).bs 9) ∈
          (List.range (treesTo (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk (oldArm (parKey Xs Pl) K.weights (randKey K))) rest Kp Vd w).bs 9)).map Fmt.TreeSource.own) := by
        intro h
        obtain ⟨i, hi, e⟩ := List.mem_map.1 h
        cases e
        exact Nat.lt_irrefl _ (List.mem_range.1 hi)
      show (!((List.range (treesTo (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk (oldArm (parKey Xs Pl) K.weights (randKey K))) rest Kp Vd w).bs 9)).map Fmt.TreeSource.own).contains
        (Fmt.TreeSource.own (treesTo (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk (oldArm (parKey Xs Pl) K.weights (randKey K))) rest Kp Vd w).bs 9))) = true
      rw [Bool.not_eq_true', ← Bool.not_eq_true, List.contains_iff_mem]
      exact hn
  · intro k m
    have hge : treesU (parKey Xs Pl) ≤ treesTo (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk (oldArm (parKey Xs Pl) K.weights (randKey K))) rest Kp Vd w).bs 9 := by
      have F := flatOf_carried (Cl := Claim) (keyAsProof Xs.chains) (parKey Xs Pl) B.b1 B.b2 B.b3 B.b4
        B.b5 B.b6 B.b7 B.b8 (sharedTests Pl) VerifiableInference.Desc.K12.Seat.last B.made
      obtain ⟨-, t5, -, -⟩ := flat_counts F B.made
      have t5' := t5.trans (trees_b2 B.made)
      have hm := treesTo_mono (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk (oldArm (parKey Xs Pl) K.weights (randKey K))) rest Kp Vd w).bs 5 4
      exact t5' ▸ hm
    have hn : ¬ treesTo (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk (oldArm (parKey Xs Pl) K.weights (randKey K))) rest Kp Vd w).bs 9 < treesU (parKey Xs Pl) := by omega
    show (tbKey (parKey Xs Pl) K.weights (randKey K) tk (oldArm (parKey Xs Pl) K.weights (randKey K))
      (.own (treesTo (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk (oldArm (parKey Xs Pl) K.weights (randKey K))) rest Kp Vd w).bs 9)) k m.st.input _).1 = _
    unfold tbKey
    simp only [if_neg hn]
    split <;> rfl

/-- **FALSE WHEREVER PLAYABLE, AT THE LETTER `oldArm` ALONE.** Where a thread stands at 9, and the member's steps
return at a list of challenges that fits and at which nothing stops, `Plays` at 9 does not hold.
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem not_plays {Z : VerifierAndGoals.PublicFiles} (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    {layO : TreeLay} (hQ : Plan2 (parKey Xs Pl) (sentKey Xs Pl) layO) (B : Eight (parKey Xs Pl))
    {k : Coins (keyBook K₀)} {s : St} {m : Mid (Common W₀ Rc TableKey) X₀} {E : Env}
    {ds : List Fmt.Drawn} {l : List (Step _ X₀)}
    (hT : Thr (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk (oldArm (parKey Xs Pl) K.weights (randKey K))) rest Kp Vd w) 9 k s m E)
    (hd : drawsFit (H2K.JointK.keyGu Pl).rounds ds = true)
    (hstop : chainStopAt ((threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk (oldArm (parKey Xs Pl) K.weights (randKey K))) rest Kp Vd w).φ.sees m.st.input) [H2K.JointK.keyGu Pl] (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk (oldArm (parKey Xs Pl) K.weights (randKey K))) rest Kp Vd w).hs m.loc ds = none)
    (hsteps : chainSteps (keyBook K₀) ((keyBook K₀).rowsOf (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk (oldArm (parKey Xs Pl) K.weights (randKey K))) rest Kp Vd w).chain) (k.look (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk (oldArm (parKey Xs Pl) K.weights (randKey K))) rest Kp Vd w).chain)
      ((threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk (oldArm (parKey Xs Pl) K.weights (randKey K))) rest Kp Vd w).φ.sees m.st.input) [H2K.JointK.keyGu Pl] (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk (oldArm (parKey Xs Pl) K.weights (randKey K))) rest Kp Vd w).hs = .ok l) :
    ¬ Plays (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk (oldArm (parKey Xs Pl) K.weights (randKey K))) rest Kp Vd w) 9 := by
  have hPl : Pl = PF := later_sourced hs scope
  obtain ⟨h9, -⟩ := AtPublicFiles.KeyDoorNine.seat_nine Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk (oldArm (parKey Xs Pl) K.weights (randKey K))) rest Kp Vd w B
  obtain ⟨hmem, hplace⟩ := fresh_nine Xs Nr Pl K₀ K ℓ Nm Mg₀ tk rest Kp Vd w hs scope hQ B
  have hsent : E.sent = treesTo (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk (oldArm (parKey Xs Pl) K.weights (randKey K))) rest Kp Vd w).bs 9 := hT.2.2.2.2.1.2.2.1
  refine not_plays_of_place _ h9 hT hd hstop hsteps hmem (Nat.le_of_eq hsent) fun m' he => ?_
  rw [hplace k m', hPl] at he
  exact gu_place he.symm

end

end AtPublicFiles.KeyFreshTrial

#print axioms AtPublicFiles.KeyFreshTrial.gu_trees
#print axioms AtPublicFiles.KeyFreshTrial.gu_place
#print axioms AtPublicFiles.KeyFreshTrial.treesTo_succ
#print axioms AtPublicFiles.KeyFreshTrial.treesTo_mono
#print axioms AtPublicFiles.KeyFreshTrial.steps_place
#print axioms AtPublicFiles.KeyFreshTrial.play_place
#print axioms AtPublicFiles.KeyFreshTrial.tables_place
#print axioms AtPublicFiles.KeyFreshTrial.not_plays_of_place
#print axioms AtPublicFiles.KeyFreshTrial.fresh_nine
#print axioms AtPublicFiles.KeyFreshTrial.not_plays
