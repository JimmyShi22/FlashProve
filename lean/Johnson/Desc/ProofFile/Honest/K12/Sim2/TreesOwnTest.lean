-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the trees at the request's own test, member by member.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/TreesOwnTest.lean: what a job of several members holds in its
trees, against a sending's written column; and what the front of a called part of the last chain lists
of a tree that a sending of the kind K1 sent in the first chain. Work for the clause trees at the test
on the request's own group (TreesOwnTestRun.lean).

  first_round_at_first   what a one-part half's first round said, in front of a later round
  layRows_at, lst_tabG, mask_words, main_words   the stage's lists at any number of members
  k1_sender_at_run, k1_tree_in_front   a K1 sending's tables, seen from the last chain
  tree_column, zip_at_member, member_mask, member_main   a tree's pieces
  col_of_mine, k1_mask_syms, k1_main_syms, k1_fresh_syms   a piece against the sender's column
  tree_of_mask_member, tree_of_riding_member   the two trees of the first chain's messages

Limits. General in the job: what ties a member's rows to its sender's is a premise. Nothing on
completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.TreesL
import Johnson.Desc.ProofFile.Honest.K12.AtProof.JobW
import Johnson.Desc.ProofFile.Honest.K12.TreeIsColumn
import Johnson.Desc.ProofFile.Honest.K12.TreeIsColumnAt
import Johnson.Desc.ProofFile.Honest.K12.Sim.PlayedAtSecond
import Johnson.Desc.ProofFile.Honest.K12.Sim.FrameAtSecond
import Johnson.Desc.ProofFile.Honest.K12.Sim.TreeNumberAtRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block FileDescription Oracle Place)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof ProofFile.Honest.K12.Light
open Johnson.Prover.Send (col)

/-- **What a one-part half's first round said, as played, in front of a later round of the first
chain**: switch_in_front (Sim2/TreesL.lean), general in the part. -/
theorem first_round_at_first {Xi W₀ Rc Ky Tr X₀ Y : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} (hR : ready F Bk P w₀ rc x k = .ok R)
    (pre : List (Block F.S₁ F.Cl)) (b : Block F.S₁ F.Cl) (t : List (Block F.S₁ F.Cl))
    (hcut : F.first.blocksInOrder = pre ++ b :: t) (hb : b.rounds ≠ [])
    (pl : Place) (p : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y)
    (mv : Move p.Coins (Local W₀ Rc Xi Tr) Y) (hmv : p.moves[0]? = some mv)
    (hg : (P.first.find? fun g => g.place == b.place) = some ⟨pl, [p]⟩)
    (n : ℕ) (hn : (pre.flatMap (·.rounds)).length < n) (L : Lay)
    (a₁ y : ChainProgress F.S₁ F.Cl (Local W₀ Rc Xi Tr) Y) (hal : a₁.laid = [])
    (hn₂ : n ≤ R.first.length)
    (hw : walk L (R.first.take n) (ρ.first.take n) a₁ = .ok y)
    (hsome : y.mid.isSome = true) :
    ∃ (zᵢ : ChainProgress F.S₁ F.Cl (Local W₀ Rc Xi Tr) Y) (mᵢ : ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) Y)
      (c : p.Coins) (q : Played) (z : Sending),
      walk L (R.first.take (pre.flatMap (·.rounds)).length)
          (ρ.first.take (pre.flatMap (·.rounds)).length) a₁ = .ok zᵢ ∧
      zᵢ.mid = some mᵢ ∧
      lendPart Bk (Bk.rowsOf 0) (k.look 0) ⟨b.place, 0⟩ p = .ok c ∧
      y.laid[(pre.flatMap (·.rounds)).length]? = some q ∧
      q.tables = z.tables.map some ∧
      mv.say c mᵢ.shown mᵢ.st = .ok z := by
  obtain ⟨c, l₁, l₂, hl, hsh, hl₁, hor⟩ := block_steps_at_first hR pre b t hcut _ hg
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
      Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).steps b (Face.own.sees R.own) c =
      p.steps b.name ⟨b.place, 0⟩
          ((b.rounds.zip b.oracles).take p.moves.length) (Face.own.sees R.own) c.1 ++ [] := rfl
  obtain ⟨mv₀, ms, hms⟩ : ∃ mv₀ ms, p.moves = mv₀ :: ms := by
    cases hp : p.moves with
    | nil =>
      rw [hp] at hmv
      cases hmv
    | cons a l => exact ⟨a, l, rfl⟩
  obtain ⟨s, rest, e2⟩ : ∃ s rest,
      p.steps b.name ⟨b.place, 0⟩
          ((b.rounds.zip b.oracles).take p.moves.length) (Face.own.sees R.own) c.1 = s :: rest := by
    unfold Part.steps
    rw [hms, hd, ho]
    exact ⟨_, _, rfl⟩
  have hs0 : (p.steps b.name ⟨b.place, 0⟩
        ((b.rounds.zip b.oracles).take p.moves.length) (Face.own.sees R.own) c.1)[0]? = some s := by
    rw [e2]
    rfl
  have hs : (R.first.take n)[(pre.flatMap (·.rounds)).length]? = some s := by
    rw [List.getElem?_take_of_lt hn, hsh, e1, e2, ← hl₁,
      List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  -- the cut of the walk
  have hlen := walk_len L _ _ a₁ y hw
  obtain ⟨hi, hsi⟩ := List.getElem?_eq_some_iff.1 hs
  obtain ⟨zᵢ, w1, w2, -, -⟩ := walk_cut hal hw (pre.flatMap (·.rounds)).length (Nat.le_of_lt hi)
  have hdrop : (R.first.take n).drop (pre.flatMap (·.rounds)).length =
      s :: (R.first.take n).drop ((pre.flatMap (·.rounds)).length + 1) := by
    rw [← hsi, List.getElem_cons_drop]
  have hid : (pre.flatMap (·.rounds)).length < (ρ.first.take n).length := by
    rw [hlen]
    exact hi
  have ddrop : (ρ.first.take n).drop (pre.flatMap (·.rounds)).length =
      (ρ.first.take n)[(pre.flatMap (·.rounds)).length] ::
        (ρ.first.take n).drop ((pre.flatMap (·.rounds)).length + 1) := by
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
    have h5 : (ρ.first.take n).length = (R.first.take n).length := hlen
    rw [List.length_take] at h5 hi
    omega
  obtain ⟨tl, htl⟩ := walk_laid_prefix L _ _ z₁ y hw'
  have hq := heard_laid hz
  refine ⟨zᵢ, mᵢ, c.1, ⟨s.name, s.addr.place, s.addr.part, x'.told, x'.vals, x'.tables,
    (ρ.first.take n)[(pre.flatMap (·.rounds)).length]⟩, z, ?_, hmi, hlp, ?_, ?_, hz'⟩
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

/-! ## The stage's lists, at any number of members -/

section Lists
open OnBytes.Slice (GE ofE toE lst toE_ofE)
open Johnson.Prover.Send (Rows)
open Johnson.Prover.Link (PS symG symG_congr words3)
open Fmt.M1 (Stage)
open Fmt.M1.Own (PSt words)

/-- The row that a list of blocks lays at b is that of the first block that covers b. -/
theorem layRows_at (n len b : ℕ) (pre : List RowBlock) (B : RowBlock) (post : List RowBlock)
    (hb : b < n) (hoff : ∀ e ∈ pre, ¬ (e.first ≤ b ∧ b < e.first + e.count))
    (h : B.first ≤ b ∧ b < B.first + B.count) :
    (layRows n len (pre ++ B :: post)).getD b [] = B.rows.getD (b - B.first) [] := by
  unfold layRows
  rw [ProofFile.Honest.K12.Light.getD_range n _ _ b hb]
  have e : (pre ++ B :: post).findSome? (fun B =>
      if B.first ≤ b ∧ b < B.first + B.count then some (B.rows.getD (b - B.first) []) else none) =
      some (B.rows.getD (b - B.first) []) := by
    rw [List.findSome?_append]
    have hn : pre.findSome? (fun B =>
        if B.first ≤ b ∧ b < B.first + B.count then some (B.rows.getD (b - B.first) [])
        else none) = none := by
      rw [List.findSome?_eq_none_iff]
      intro e he
      rw [if_neg (hoff e he)]
    rw [hn, List.findSome?_cons, if_pos h]
    rfl
  rw [e]
  rfl

/-- An entry of a table of words, read back. -/
theorem lst_tabG (r n : ℕ) (f : ℕ → ℕ → GE) (i j : ℕ) (hi : i < r) (hj : j < n) :
    lst ((tabG r n f).getD i []) j = f i j := by
  unfold tabG
  rw [ProofFile.Honest.K12.Light.getD_range r _ _ i hi, lst_range n _ j hj, toE_ofE]

/-- **A member's mask rows, in the job's tree, are the sender's.** ms: the members' shapes and rows;
the member stands behind pre, whose blocks do not cover its rows. -/
theorem mask_words (s : Stage) (ms : List (MemShape × PSt)) (pre post : List (MemShape × PSt))
    (m : MemShape) (q : PSt) (hms : ms = pre ++ (m, q) :: post)
    (hoff : ∀ e ∈ pre, ∀ b, m.maskFirst ≤ b → b < m.maskFirst + m.maskRows →
      ¬ (e.1.maskFirst ≤ b ∧ b < e.1.maskFirst + e.1.maskRows))
    (hin : m.maskFirst + m.maskRows ≤ 2 ^ s.h) (P : PS)
    (hP : P.tabZ = (readPS s (layFirst s ms)).tabZ) (hT : P.tZ = (readPS s (layFirst s ms)).tZ)
    (mask tail : ℕ → ℕ → GE)
    (hW : ∀ r < m.maskRows, ∀ j < s.Z.l, lst (q.W.getD r []) j = mask r j)
    (hS : ∀ r < m.maskRows, ∀ j < s.Z.r, lst (q.Sg.getD r []) j = tail r j) (x : ℕ) :
    Light.wordsAt (symOf s P x)
        ((List.range m.maskRows).map fun r => ⟨.mask, m.maskFirst + r, false⟩) =
      (List.range m.maskRows).flatMap fun r =>
        words3 (ofE (symG s.Z (x % 2 ^ s.Z.a) (mask r) (tail r))) := by
  rw [Light.maskWords s P x _ _ hin]
  refine congrArg List.flatten (List.map_congr_left fun r hr => ?_)
  have hr' : r < m.maskRows := List.mem_range.1 hr
  have hlt : m.maskFirst + r < 2 ^ s.h := by omega
  have hcov : m.maskFirst ≤ m.maskFirst + r ∧ m.maskFirst + r < m.maskFirst + m.maskRows := by omega
  refine congrArg (fun y => words (ofE y)) (symG_congr _ _ _ _ _ _ (fun j hj => ?_) fun t ht => ?_)
  · rw [hP]
    show lst ((layRows (2 ^ s.h) s.Z.l (ms.map fun x => ⟨x.1.maskFirst, x.1.maskRows, x.2.W⟩)).getD
      ((m.maskFirst + r + 2 ^ s.h * j) % 2 ^ s.h) []) ((m.maskFirst + r + 2 ^ s.h * j) / 2 ^ s.h) = _
    rw [(split_idx s.h _ j hlt).1, (split_idx s.h _ j hlt).2, hms, List.map_append, List.map_cons,
      layRows_at _ _ _ _ _ _ hlt (fun e he => ?_) hcov]
    · show lst (q.W.getD (m.maskFirst + r - m.maskFirst) []) j = _
      rw [Nat.add_sub_cancel_left]
      exact hW r hr' j hj
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 he
      exact hoff a ha _ hcov.1 hcov.2
  · rw [hT]
    show lst ((layRows (2 ^ s.h) s.Z.r (ms.map fun x => ⟨x.1.maskFirst, x.1.maskRows, x.2.Sg⟩)).getD
      (m.maskFirst + r) []) t = _
    rw [hms, List.map_append, List.map_cons, layRows_at _ _ _ _ _ _ hlt (fun e he => ?_) hcov]
    · show lst (q.Sg.getD (m.maskFirst + r - m.maskFirst) []) t = _
      rw [Nat.add_sub_cancel_left]
      exact hS r hr' t ht
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 he
      exact hoff a ha _ hcov.1 hcov.2

/-- **A member's main rows, in the job's tree, are the sender's.** -/
theorem main_words (s : Stage) (hk : s.h ≤ s.k) (ms : List (MemShape × PSt))
    (pre post : List (MemShape × PSt)) (m : MemShape) (q : PSt) (hms : ms = pre ++ (m, q) :: post)
    (hoff : ∀ e ∈ pre, ∀ b, m.mainFirst ≤ b → b < m.mainFirst + m.mainRows →
      ¬ (e.1.mainFirst ≤ b ∧ b < e.1.mainFirst + e.1.mainRows))
    (hin : m.mainFirst + m.mainRows ≤ 2 ^ s.k) (P : PS)
    (hP : P.tabM = (readPS s (layFirst s ms)).tabM) (hT : P.tM = (readPS s (layFirst s ms)).tM)
    (main tail : ℕ → ℕ → GE)
    (hM : ∀ r < m.mainRows, ∀ j < s.C.l, lst (q.M.getD r []) j = main r j)
    (hR : ∀ r < m.mainRows, ∀ j < s.C.r, lst (q.Rh.getD r []) j = tail r j) (x : ℕ) :
    Light.wordsAt (symOf s P x)
        ((List.range m.mainRows).map fun r => ⟨.main, m.mainFirst + r, false⟩) =
      (List.range m.mainRows).flatMap fun r =>
        words3 (ofE (symG s.C x (main r) (tail r))) := by
  rw [Light.mainWords s hk P x _ _ hin]
  refine congrArg List.flatten (List.map_congr_left fun r hr => ?_)
  have hr' : r < m.mainRows := List.mem_range.1 hr
  have hlt : m.mainFirst + r < 2 ^ s.k := by omega
  have hcov : m.mainFirst ≤ m.mainFirst + r ∧ m.mainFirst + r < m.mainFirst + m.mainRows := by omega
  refine congrArg (fun y => words (ofE y)) (symG_congr _ _ _ _ _ _ (fun j hj => ?_) fun t ht => ?_)
  · rw [hP]
    show lst ((layRows (2 ^ s.k) s.C.l (ms.map fun x => ⟨x.1.mainFirst, x.1.mainRows, x.2.M⟩)).getD
      ((m.mainFirst + r + 2 ^ s.k * j) % 2 ^ s.k) []) ((m.mainFirst + r + 2 ^ s.k * j) / 2 ^ s.k) = _
    rw [(split_idx s.k _ j hlt).1, (split_idx s.k _ j hlt).2, hms, List.map_append, List.map_cons,
      layRows_at _ _ _ _ _ _ hlt (fun e he => ?_) hcov]
    · show lst (q.M.getD (m.mainFirst + r - m.mainFirst) []) j = _
      rw [Nat.add_sub_cancel_left]
      exact hM r hr' j hj
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 he
      exact hoff a ha _ hcov.1 hcov.2
  · rw [hT]
    show lst ((layRows (2 ^ s.k) s.C.r (ms.map fun x => ⟨x.1.mainFirst, x.1.mainRows, x.2.Rh⟩)).getD
      (m.mainFirst + r) []) t = _
    rw [hms, List.map_append, List.map_cons, layRows_at _ _ _ _ _ _ hlt (fun e he => ?_) hcov]
    · show lst (q.Rh.getD (m.mainFirst + r - m.mainFirst) []) t = _
      rw [Nat.add_sub_cancel_left]
      exact hR r hr' t ht
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 he
      exact hoff a ha _ hcov.1 hcov.2

end Lists

/-! ## A sender of the first chain, at a run -/

/-- **The tables that a sending of the kind K1 sent in the first chain**, seen from a called part of
the last chain. -/
theorem k1_sender_at_run {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (σ : Side F.S₃ F.Cl V (Local W₀ Rc Xi Tr) Y Pb) (u : Member V (Local W₀ Rc Xi Tr) Y Pb)
    (pre' t' : List (Block F.S₃ F.Cl)) (i : ℕ) (S : StandsAt F.second.blocksInOrder R.second σ u pre' t' i)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true)
    (pre : List (Block F.S₁ F.Cl)) (b : Block F.S₁ F.Cl) (t : List (Block F.S₁ F.Cl))
    (hcut : F.first.blocksInOrder = pre ++ b :: t) (hb : b.rounds ≠ [])
    (wit : Local W₀ Rc Xi Tr → K1.PlaceIn Xi) (J : K1.SendJob (K1.PlaceIn Xi) Y)
    (hg : (P.first.find? fun g => g.place == b.place) =
      some (K1.placeHalf (V := Local W₀ Rc Xi Tr) wit J)) :
    ∃ (mᵢ : ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) Y)
      (c : ((K1.sendPart (V := Local W₀ Rc Xi Tr) J).lift id wit id fun _ y => y :
        Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).Coins) (q : Played),
      lendPart Bk (Bk.rowsOf 0) (k.look 0) ⟨b.place, 0⟩
        ((K1.sendPart (V := Local W₀ Rc Xi Tr) J).lift id wit id fun _ y => y) = .ok c ∧
      r.run.played.1[(pre.flatMap (·.rounds)).length]? = some q ∧
      q.tables = (K1.treeTables J.P (J.rows c.1 mᵢ.shown (mᵢ.st.narrow wit id) 0)).map some ∧
      mᵢ.st.input = R.own ∧ mᵢ.st.heard = ρ.first.take (pre.flatMap (·.rounds)).length := by
  have Q := (F.planOk_ok).1 hpl
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  have o₁ := steps_shaped s1 Q.blocks₁
  have o₂ := steps_shaped s2 Q.blocks₂
  have o₃ := steps_shaped s3 Q.blocks₃
  obtain ⟨lS, -, -⟩ := runC_laidAs hrun hR o₁ o₂ o₃
  obtain ⟨m₁, m₂, m, a₁, z₁, a₂, z₂, a₃, y, ha₁, hz₁, hl₁, hm₁, -⟩ :=
    played_at_second hpl hR hrun σ u pre' t' i _ S rfl hc
  have hlen : R.first.length = (F.first.blocksInOrder.flatMap (·.rounds)).length := by
    rw [chainSteps_length _ _ s1, List.length_flatMap]
  have hlt : (pre.flatMap (·.rounds)).length < R.first.length := by
    rw [hlen, hcut, List.flatMap_append, List.flatMap_cons, List.length_append, List.length_append]
    have : 0 < b.rounds.length := List.length_pos_iff.2 hb
    omega
  have hρ : ρ.first.take R.first.length = ρ.first := by
    rw [← lS.1]
    exact List.take_length
  have hw : walk ⟨0, 0, P.storedWords w₀ rc, treeOwn⟩ (R.first.take R.first.length)
      (ρ.first.take R.first.length) a₁ = .ok z₁ := by
    rw [List.take_length, hρ]
    exact hz₁
  obtain ⟨zᵢ, mᵢ, c, q, z, hwi, hmi, hlend, hq, hqT, hsay⟩ := first_round_at_first hR pre b t hcut hb
    (K1.placeHalf (V := Local W₀ Rc Xi Tr) wit J).place
    ((K1.sendPart (V := Local W₀ Rc Xi Tr) J).lift id wit id fun _ y => y) _ rfl hg _ hlt _ a₁ z₁
    (start_laid ha₁) (Nat.le_refl _) hw (by rw [hm₁]; rfl)
  have hz : z = ⟨[], K1.treeTables J.P (J.rows c.1 mᵢ.shown (mᵢ.st.narrow wit id) 0)⟩ := by
    simp only [Move.lift] at hsay
    split at hsay
    · cases hsay
    · exact (Except.ok.inj hsay).symm
  subst hz
  refine ⟨mᵢ, c, q, hlend, ?_, hqT, (walk_mid ha₁ hwi hmi).1, ?_⟩
  · rw [← hl₁]
    exact hq
  · have a3 := walk_hears _ _ _ _ a₁ zᵢ (start_hears ha₁) hwi mᵢ hmi
    have a4 := walk_laid_drawn _ _ _ a₁ zᵢ hwi
    rw [start_laid ha₁, List.map_nil, List.nil_append] at a4
    rw [a4] at a3
    exact a3.trans (List.nil_append _)

/-- **What the front of a called part of the last chain lists of a tree of the first chain that a
sending of the kind K1 sent**: columns of the sending's written column. τ: the tree's number among the
sending's; j: among the chain's. -/
theorem k1_tree_in_front {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (σ : Side F.S₃ F.Cl V (Local W₀ Rc Xi Tr) Y Pb) (u : Member V (Local W₀ Rc Xi Tr) Y Pb)
    (pre' t' : List (Block F.S₃ F.Cl)) (i : ℕ) (S : StandsAt F.second.blocksInOrder R.second σ u pre' t' i)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true)
    (pre : List (Block F.S₁ F.Cl)) (b : Block F.S₁ F.Cl) (t : List (Block F.S₁ F.Cl))
    (hcut : F.first.blocksInOrder = pre ++ b :: t) (hb : b.rounds ≠ [])
    (wit : Local W₀ Rc Xi Tr → K1.PlaceIn Xi) (J : K1.SendJob (K1.PlaceIn Xi) Y)
    (hg : (P.first.find? fun g => g.place == b.place) =
      some (K1.placeHalf (V := Local W₀ Rc Xi Tr) wit J))
    (τ j : ℕ) (sh : OnBytes.TreeShape) (hτ : J.P.trees[τ]? = some sh)
    (hW : columnWidth J.P τ = sh.mainWidth + sh.maskWidth)
    (hj : treesTo F.first.blocksInOrder pre.length + τ = j) (st : List (ℕ × ℕ × List UInt64)) :
    ∃ (mᵢ : ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) Y)
      (c : ((K1.sendPart (V := Local W₀ Rc Xi Tr) J).lift id wit id fun _ y => y :
        Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).Coins) (cols : List (ℕ × List UInt64)),
      lendPart Bk (Bk.rowsOf 0) (k.look 0) ⟨b.place, 0⟩
        ((K1.sendPart (V := Local W₀ Rc Xi Tr) J).lift id wit id fun _ y => y) = .ok c ∧
      mᵢ.st.input = R.own ∧ mᵢ.st.heard = ρ.first.take (pre.flatMap (·.rounds)).length ∧
      (r.run.beforeAt st ⟨σ.block.place, u.number⟩).treeCols 0 j = some cols ∧
      ∀ q ∈ cols, q.2 = col J.P (J.rows c.1 mᵢ.shown (mᵢ.st.narrow wit id) 0) τ q.1 := by
  obtain ⟨mᵢ, c, q, hlend, hq, hqT, hin, hh⟩ :=
    k1_sender_at_run hpl hR hrun σ u pre' t' i S hc pre b t hcut hb wit J hg
  have Q := (F.planOk_ok).1 hpl
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  have o₁ := steps_shaped s1 Q.blocks₁
  have o₂ := steps_shaped s2 Q.blocks₂
  have o₃ := steps_shaped s3 Q.blocks₃
  obtain ⟨lS, -, -⟩ := runC_laidAs hrun hR o₁ o₂ o₃
  obtain ⟨-, -, -, -, -, -, hbf, -⟩ := frame_at_second hpl hR hrun σ u pre' t' i _ S rfl hc st
  have hlt : τ < J.P.trees.length := (List.getElem?_eq_some_iff.1 hτ).1
  have hTl : τ < q.tables.length := by
    rw [hqT, List.length_map]
    unfold K1.treeTables
    rw [List.length_map, List.length_zipIdx]
    exact hlt
  have hat := tab_at_round r.run.played.1 _ τ q hq hTl
  have hjl : ((r.run.played.1.take (pre.flatMap (·.rounds)).length).map (·.tables.length)).sum + τ =
      j := by
    have hsh : ∀ y ∈ pre, y.oracles.length = y.rounds.length := fun y hy => by
      have h1 := planOk_shaped_first hpl y (by rw [hcut]; simp [hy])
      unfold Block.shaped at h1
      simp only [Bool.and_eq_true, beq_iff_eq] at h1
      exact h1.1
    have hc' := rows_count pre hsh (b :: t)
    rw [← hcut] at hc'
    have ht : treesTo F.first.blocksInOrder pre.length =
        (pre.flatMap fun y => y.oracles.flatMap id).length := by
      unfold treesTo
      rw [hcut, List.take_left']
      rfl
    have e2 : (R.first.take (pre.flatMap (·.rounds)).length).map (·.oracles.length) =
        ((rowsOfChain F.first.blocksInOrder).take (pre.flatMap (·.rounds)).length).map (·.2.length) := by
      rw [← steps_pairs s1, ← List.map_take, List.map_map]
      rfl
    rw [← hj, ht, ← hc', ← e2, List.map_take, laidAs_tables lS, List.map_take]
  rw [hjl] at hat
  have hT : q.tables[τ]? = some (some (⟨sh.logN, sh.mainWidth + sh.maskWidth, fun x w =>
      OnBytes.Slice.toF ((col J.P (J.rows c.1 mᵢ.shown (mᵢ.st.narrow wit id) 0) τ x).getD w.val 0)⟩ :
        Table)) := by
    rw [hqT, List.getElem?_map]
    unfold K1.treeTables
    rw [List.getElem?_map, List.getElem?_zipIdx, hτ]
    simp only [Nat.zero_add]
    rfl
  rw [hT] at hat
  refine ⟨mᵢ, c, colsOfT (some ⟨sh.logN, sh.mainWidth + sh.maskWidth, fun x w =>
      OnBytes.Slice.toF ((col J.P (J.rows c.1 mᵢ.shown (mᵢ.st.narrow wit id) 0) τ x).getD w.val 0)⟩)
      (treeAsks F ρ 0 j), hlend, hin, hh, ?_, ?_⟩
  · rw [hbf, treeCols_at F ρ _ _ _ st 0 j (by decide)]
    show (((allTabs r.run.played.1)[j]?).map _) = _
    rw [hat]
    rfl
  · intro q' hq'
    obtain ⟨x', -, rfl⟩ := List.mem_map.1 hq'
    show Table.col _ x' = _
    exact table_column _ _ _ x' (by rw [column_length]; exact hW) (column_words_canonical _ _ _ _)

/-! ## A job's trees, piece by piece -/

section Pieces
open OnBytes.Slice (GE ofE toE lst toE_ofE)
open Johnson.Prover.Link (PS symG symG_congr words3)
open Fmt.M1 (Stage)
open Fmt.M1.Own (PSt words)

variable {W X : Type}

/-- A tree's column, off its pieces, at any number of members. -/
theorem tree_column (B : ManyJob W X) (w : W) (fr : Front X) (mem : ℕ → Stretch) (P : PS) (i d : ℕ)
    (ps : List Piece) (ht : B.trees[i]? = some (d, ps)) (x : ℕ) :
    ((B.toRun.toTest.trees₀ w fr mem P).getD i (0, fun _ => [])).2 x =
      Light.wordsAt (symOf B.s₀ P x) (ps.flatMap (selsOf B.s₀ (B.mems.map (·.shape)))) := by
  rw [trees₀_many, List.getD_eq_getElem?_getD, List.getElem?_map, ht]
  rfl

/-- The stage's lists at a member behind pre. -/
theorem zip_at_member (B : ManyJob W X) (w : W) (fr : Front X) (mem : ℕ → Stretch)
    (pre post : List (Mem W X)) (mt : Mem W X) (hm : B.mems = pre ++ mt :: post) :
    ∃ (a b : List (MemShape × PSt)),
      B.mems.zipIdx.map (fun m => (m.1.shape, m.1.rows w fr (mem m.2))) =
        a ++ (mt.shape, mt.rows w fr (mem pre.length)) :: b ∧
      ∀ e ∈ a, ∃ y ∈ pre, e.1 = y.shape := by
  rw [hm, List.zipIdx_append, List.map_append, List.zipIdx_cons, List.map_cons]
  refine ⟨pre.zipIdx.map fun m => (m.1.shape, m.1.rows w fr (mem m.2)),
    (post.zipIdx (pre.length + 1)).map fun m => (m.1.shape, m.1.rows w fr (mem m.2)), ?_,
    fun e he => ?_⟩
  · simp only [Nat.zero_add]
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 he
    refine ⟨a.1, ?_, rfl⟩
    have h := List.mem_map_of_mem (f := Prod.fst) ha
    rwa [List.zipIdx_map_fst] at h

/-- **A member's mask rows in the job's tree.** -/
theorem member_mask (B : ManyJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (pre post : List (Mem W X)) (mt : Mem W X) (hm : B.mems = pre ++ mt :: post)
    (hoff : ∀ y ∈ pre, ∀ b, mt.shape.maskFirst ≤ b → b < mt.shape.maskFirst + mt.shape.maskRows →
      ¬ (y.shape.maskFirst ≤ b ∧ b < y.shape.maskFirst + y.shape.maskRows))
    (hin : mt.shape.maskFirst + mt.shape.maskRows ≤ 2 ^ B.s₀.h)
    (mask tail : ℕ → ℕ → GE)
    (hW : ∀ r < mt.shape.maskRows, ∀ j < B.s₀.Z.l,
      lst ((mt.rows w fr (C.mem pre.length)).W.getD r []) j = mask r j)
    (hS : ∀ r < mt.shape.maskRows, ∀ j < B.s₀.Z.r,
      lst ((mt.rows w fr (C.mem pre.length)).Sg.getD r []) j = tail r j) (x : ℕ) :
    Light.wordsAt (symOf B.s₀ (B.toRun.toTest.first w fr C) x)
        (selsOf B.s₀ (B.mems.map (·.shape)) (.mask pre.length)) =
      (List.range mt.shape.maskRows).flatMap fun r =>
        words3 (ofE (symG B.s₀.Z (x % 2 ^ B.s₀.Z.a) (mask r) (tail r))) := by
  have hs : (B.mems.map (·.shape))[pre.length]? = some mt.shape := by
    rw [hm]
    simp
  have hsel : selsOf B.s₀ (B.mems.map (·.shape)) (.mask pre.length) =
      (List.range mt.shape.maskRows).map fun r => ⟨.mask, mt.shape.maskFirst + r, false⟩ := by
    simp only [selsOf, hs]
  rw [hsel]
  obtain ⟨a, b, hab, ha⟩ := zip_at_member B w fr C.mem pre post mt hm
  refine mask_words B.s₀ _ a b mt.shape _ hab (fun e he c h1 h2 => ?_) hin
    (B.toRun.toTest.first w fr C) rfl rfl mask tail hW hS x
  obtain ⟨y, hy, ey⟩ := ha e he
  rw [ey]
  exact hoff y hy c h1 h2

/-- **A member's main rows in the job's tree.** -/
theorem member_main (B : ManyJob W X) (hk : B.s₀.h ≤ B.s₀.k) (w : W) (fr : Front X) (C : TestCoins)
    (pre post : List (Mem W X)) (mt : Mem W X) (hm : B.mems = pre ++ mt :: post)
    (hbase : mt.shape.base = false)
    (hoff : ∀ y ∈ pre, ∀ b, mt.shape.mainFirst ≤ b → b < mt.shape.mainFirst + mt.shape.mainRows →
      ¬ (y.shape.mainFirst ≤ b ∧ b < y.shape.mainFirst + y.shape.mainRows))
    (hin : mt.shape.mainFirst + mt.shape.mainRows ≤ 2 ^ B.s₀.k)
    (main tail : ℕ → ℕ → GE)
    (hM : ∀ r < mt.shape.mainRows, ∀ j < B.s₀.C.l,
      lst ((mt.rows w fr (C.mem pre.length)).M.getD r []) j = main r j)
    (hR : ∀ r < mt.shape.mainRows, ∀ j < B.s₀.C.r,
      lst ((mt.rows w fr (C.mem pre.length)).Rh.getD r []) j = tail r j) (x : ℕ) :
    Light.wordsAt (symOf B.s₀ (B.toRun.toTest.first w fr C) x)
        (selsOf B.s₀ (B.mems.map (·.shape)) (.main pre.length)) =
      (List.range mt.shape.mainRows).flatMap fun r =>
        words3 (ofE (symG B.s₀.C x (main r) (tail r))) := by
  have hs : (B.mems.map (·.shape))[pre.length]? = some mt.shape := by
    rw [hm]
    simp
  have hsel : selsOf B.s₀ (B.mems.map (·.shape)) (.main pre.length) =
      (List.range mt.shape.mainRows).map fun r => ⟨.main, mt.shape.mainFirst + r, false⟩ := by
    simp only [selsOf, hs, hbase]
  rw [hsel]
  obtain ⟨a, b, hab, ha⟩ := zip_at_member B w fr C.mem pre post mt hm
  refine main_words B.s₀ hk _ a b mt.shape _ hab (fun e he c h1 h2 => ?_) hin
    (B.toRun.toTest.first w fr C) rfl rfl main tail hM hR x
  obtain ⟨y, hy, ey⟩ := ha e he
  rw [ey]
  exact hoff y hy c h1 h2

end Pieces

/-! ## A member that a sending of the kind K1 made -/

section K1Member
open OnBytes.Slice (GE ofE toE lst toE_ofE codeOf)
open Johnson.Prover.Send (mainSyms maskSyms shapeAt Rows)
open Johnson.Prover.Link (PS symG words3)

variable {W X : Type}

/-- The written column, off the messages of the tree. -/
theorem col_of_mine (Q : VerifiableInference.Desc.K1.Par) (V : ℕ → Rows) (τ x : ℕ) (l : List ℕ)
    (h : (List.range Q.sent.size).filter
      (fun k => ((VerifiableInference.Desc.Own.treesMade Q.codes Q.sent).getD {}).tree[k]? == some τ) =
        l) :
    col Q V τ x = l.flatMap (fun k => mainSyms Q V k x) ++ l.flatMap fun k => maskSyms Q V k x := by
  unfold col
  simp only [h]

/-- **Message k's mask rows in the job's tree.** -/
theorem k1_mask_syms (B : ManyJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (pre post : List (Mem W X)) (mt : Mem W X) (hm : B.mems = pre ++ mt :: post)
    (hoff : ∀ y ∈ pre, ∀ b, mt.shape.maskFirst ≤ b → b < mt.shape.maskFirst + mt.shape.maskRows →
      ¬ (y.shape.maskFirst ≤ b ∧ b < y.shape.maskFirst + y.shape.maskRows))
    (hin : mt.shape.maskFirst + mt.shape.maskRows ≤ 2 ^ B.s₀.h)
    (Q : VerifiableInference.Desc.K1.Par) (k : ℕ) (V : ℕ → Rows)
    (hrows : mt.rows w fr (C.mem pre.length) = psOfRows Q k (V k))
    (hn : mt.shape.maskRows = (shapeAt Q k).maskRows)
    (hz : codeOf (Q.codes.mask.getD (shapeAt Q k).maskCode default) = B.s₀.Z) (x : ℕ) :
    Light.wordsAt (symOf B.s₀ (B.toRun.toTest.first w fr C) x)
        (selsOf B.s₀ (B.mems.map (·.shape)) (.mask pre.length)) = maskSyms Q V k x := by
  have hl : (Q.codes.mask.getD (shapeAt Q k).maskCode default).ell = B.s₀.Z.l :=
    congrArg Fmt.M1.Code.l hz
  have hr : (Q.codes.mask.getD (shapeAt Q k).maskCode default).r = B.s₀.Z.r :=
    congrArg Fmt.M1.Code.r hz
  refine (member_mask B w fr C pre post mt hm hoff hin (V k).mask (V k).maskTl
    (fun r hr' j hj => ?_) (fun r hr' j hj => ?_) x).trans ?_
  · rw [hrows]
    show lst ((tabG (shapeAt Q k).maskRows _ (V k).mask).getD r []) j = _
    exact lst_tabG _ _ _ r j (hn ▸ hr') (by rw [hl]; exact hj)
  · rw [hrows]
    show lst ((tabG (shapeAt Q k).maskRows _ (V k).maskTl).getD r []) j = _
    exact lst_tabG _ _ _ r j (hn ▸ hr') (by rw [hr]; exact hj)
  · unfold maskSyms
    simp only [hz, hn]

/-- **The index-mask message's tree.** The job's tree number 0 holds the first member's mask rows, and
the sending's tree τ holds that message alone, without main rows. -/
theorem tree_of_mask_member (B : ManyJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (mt : Mem W X) (post : List (Mem W X)) (hm : B.mems = mt :: post) (d : ℕ)
    (ht : B.trees[0]? = some (d, [.mask 0]))
    (hin : mt.shape.maskFirst + mt.shape.maskRows ≤ 2 ^ B.s₀.h)
    (Q : VerifiableInference.Desc.K1.Par) (k τ : ℕ) (V : ℕ → Rows)
    (hrows : mt.rows w fr (C.mem 0) = psOfRows Q k (V k))
    (hn : mt.shape.maskRows = (shapeAt Q k).maskRows)
    (hz : codeOf (Q.codes.mask.getD (shapeAt Q k).maskCode default) = B.s₀.Z)
    (hmine : (List.range Q.sent.size).filter
      (fun k => ((VerifiableInference.Desc.Own.treesMade Q.codes Q.sent).getD {}).tree[k]? == some τ) =
        [k])
    (hmain : (shapeAt Q k).mainRows = 0) (x : ℕ) :
    ((B.toRun.toTest.trees₀ w fr C.mem (B.toRun.toTest.first w fr C)).getD 0 (0, fun _ => [])).2 x =
      col Q V τ x := by
  rw [tree_column B w fr C.mem _ 0 d _ ht x, col_of_mine Q V τ x [k] hmine]
  have e := k1_mask_syms B w fr C [] post mt hm (fun y hy => by cases hy) hin Q k V hrows hn hz x
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have e0 : mainSyms Q V k x = [] := by
    unfold mainSyms
    simp [hmain]
  rw [e0, List.nil_append]
  exact e

/-- **Message k's main rows in the job's tree**, over the extension field. -/
theorem k1_main_syms (B : ManyJob W X) (hk : B.s₀.h ≤ B.s₀.k) (w : W) (fr : Front X) (C : TestCoins)
    (pre post : List (Mem W X)) (mt : Mem W X) (hm : B.mems = pre ++ mt :: post)
    (hbase : mt.shape.base = false)
    (hoff : ∀ y ∈ pre, ∀ b, mt.shape.mainFirst ≤ b → b < mt.shape.mainFirst + mt.shape.mainRows →
      ¬ (y.shape.mainFirst ≤ b ∧ b < y.shape.mainFirst + y.shape.mainRows))
    (hin : mt.shape.mainFirst + mt.shape.mainRows ≤ 2 ^ B.s₀.k)
    (Q : VerifiableInference.Desc.K1.Par) (k : ℕ) (V : ℕ → Rows)
    (hrows : mt.rows w fr (C.mem pre.length) = psOfRows Q k (V k))
    (hn : mt.shape.mainRows = (shapeAt Q k).mainRows) (hd : (shapeAt Q k).mainDeg = 3)
    (hz : codeOf (Q.codes.base.getD (shapeAt Q k).code default) = B.s₀.C) (x : ℕ) :
    Light.wordsAt (symOf B.s₀ (B.toRun.toTest.first w fr C) x)
        (selsOf B.s₀ (B.mems.map (·.shape)) (.main pre.length)) = mainSyms Q V k x := by
  have hl : (Q.codes.base.getD (shapeAt Q k).code default).ell = B.s₀.C.l :=
    congrArg Fmt.M1.Code.l hz
  have hr : (Q.codes.base.getD (shapeAt Q k).code default).r = B.s₀.C.r :=
    congrArg Fmt.M1.Code.r hz
  refine (member_main B hk w fr C pre post mt hm hbase hoff hin (V k).mainE (V k).mainTlE
    (fun r hr' j hj => ?_) (fun r hr' j hj => ?_) x).trans ?_
  · rw [hrows]
    show lst ((tabG (shapeAt Q k).mainRows _ ((V k).main ((shapeAt Q k).mainDeg == 3))).getD r []) j = _
    rw [lst_tabG _ _ _ r j (hn ▸ hr') (by rw [hl]; exact hj), hd]
    rfl
  · rw [hrows]
    show lst ((tabG (shapeAt Q k).mainRows _ ((V k).mainTl ((shapeAt Q k).mainDeg == 3))).getD r []) j = _
    rw [lst_tabG _ _ _ r j (hn ▸ hr') (by rw [hr]; exact hj), hd]
    rfl
  · unfold mainSyms
    simp only [hz, hn, hd]
    rfl

/-- **A message's mask rows that are the first fold's fresh table.** -/
theorem k1_fresh_syms (s : Fmt.M1.Stage) (ms : List MemShape) (P : PS)
    (Q : VerifiableInference.Desc.K1.Par) (k : ℕ) (V : ℕ → Rows)
    (hn : (shapeAt Q k).maskRows = 2 ^ s.h)
    (hz : codeOf (Q.codes.mask.getD (shapeAt Q k).maskCode default) = s.Z)
    (hm : ∀ r < 2 ^ s.h, ∀ j < s.Z.l, (V k).mask r j = P.fM r j)
    (ht : ∀ r < 2 ^ s.h, ∀ q < s.Z.r, (V k).maskTl r q = P.fT r q) (x : ℕ) :
    Light.wordsAt (symOf s P x) (selsOf s ms .fresh) = maskSyms Q V k x := by
  show Light.wordsAt (symOf s P x) ((List.range (2 ^ s.h)).map fun r => ⟨.fresh, r, false⟩) = _
  rw [Light.freshWords]
  unfold maskSyms
  simp only [hz, hn]
  refine congrArg List.flatten (List.map_congr_left fun r hr => ?_)
  have hr' := List.mem_range.1 hr
  exact congrArg (fun y => words3 (ofE y)) (Johnson.Prover.Link.symG_congr _ _ _ _ _ _
    (fun j hj => (hm r hr' j hj).symm) fun t ht' => (ht r hr' t ht').symm)

/-- **W's tree.** The job's tree number 1 holds the second member's main and mask rows and the first
fold's fresh table; the sending's tree τ holds message 0 and the fresh message, in that order. -/
theorem tree_of_riding_member (B : ManyJob W X) (hk : B.s₀.h ≤ B.s₀.k) (w : W) (fr : Front X)
    (C : TestCoins) (m₀ mt : Mem W X) (post : List (Mem W X)) (hm : B.mems = m₀ :: mt :: post)
    (d : ℕ) (ht : B.trees[1]? = some (d, [.main 1, .mask 1, .fresh]))
    (hbase : mt.shape.base = false)
    (hoffM : ∀ b, mt.shape.mainFirst ≤ b → b < mt.shape.mainFirst + mt.shape.mainRows →
      ¬ (m₀.shape.mainFirst ≤ b ∧ b < m₀.shape.mainFirst + m₀.shape.mainRows))
    (hoffZ : ∀ b, mt.shape.maskFirst ≤ b → b < mt.shape.maskFirst + mt.shape.maskRows →
      ¬ (m₀.shape.maskFirst ≤ b ∧ b < m₀.shape.maskFirst + m₀.shape.maskRows))
    (hinM : mt.shape.mainFirst + mt.shape.mainRows ≤ 2 ^ B.s₀.k)
    (hinZ : mt.shape.maskFirst + mt.shape.maskRows ≤ 2 ^ B.s₀.h)
    (Q : VerifiableInference.Desc.K1.Par) (τ : ℕ) (V : ℕ → Rows)
    (hrows : mt.rows w fr (C.mem 1) = psOfRows Q 0 (V 0))
    (hnM : mt.shape.mainRows = (shapeAt Q 0).mainRows)
    (hnZ : mt.shape.maskRows = (shapeAt Q 0).maskRows) (hd : (shapeAt Q 0).mainDeg = 3)
    (hzC : codeOf (Q.codes.base.getD (shapeAt Q 0).code default) = B.s₀.C)
    (hzZ : codeOf (Q.codes.mask.getD (shapeAt Q 0).maskCode default) = B.s₀.Z)
    (hzF : codeOf (Q.codes.mask.getD (shapeAt Q 1).maskCode default) = B.s₀.Z)
    (hnF : (shapeAt Q 1).maskRows = 2 ^ B.s₀.h) (hmF : (shapeAt Q 1).mainRows = 0)
    (hmine : (List.range Q.sent.size).filter
      (fun k => ((VerifiableInference.Desc.Own.treesMade Q.codes Q.sent).getD {}).tree[k]? == some τ) =
        [0, 1])
    (hfm : ∀ r < 2 ^ B.s₀.h, ∀ j < B.s₀.Z.l,
      (V 1).mask r j = (B.toRun.toTest.first w fr C).fM r j)
    (hft : ∀ r < 2 ^ B.s₀.h, ∀ q < B.s₀.Z.r,
      (V 1).maskTl r q = (B.toRun.toTest.first w fr C).fT r q) (x : ℕ) :
    ((B.toRun.toTest.trees₀ w fr C.mem (B.toRun.toTest.first w fr C)).getD 1 (0, fun _ => [])).2 x =
      col Q V τ x := by
  have hm' : B.mems = [m₀] ++ mt :: post := hm
  rw [tree_column B w fr C.mem _ 1 d _ ht x, col_of_mine Q V τ x [0, 1] hmine]
  have e1 := k1_main_syms B hk w fr C [m₀] post mt hm' hbase
    (fun y hy b h1 h2 => by
      rw [List.mem_singleton.1 hy]
      exact hoffM b h1 h2) hinM Q 0 V hrows hnM hd hzC x
  have e2 := k1_mask_syms B w fr C [m₀] post mt hm'
    (fun y hy b h1 h2 => by
      rw [List.mem_singleton.1 hy]
      exact hoffZ b h1 h2) hinZ Q 0 V hrows hnZ hzZ x
  have e3 := k1_fresh_syms B.s₀ (B.mems.map (·.shape)) (B.toRun.toTest.first w fr C) Q 1 V hnF hzF
    hfm hft x
  have e0 : mainSyms Q V 1 x = [] := by
    unfold mainSyms
    simp [hmF]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, e0]
  rw [wordsAt_append, wordsAt_append]
  exact (congrArg₂ (· ++ ·) e1 (congrArg₂ (· ++ ·) e2 e3))

end K1Member

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.first_round_at_first
#print axioms ProofFile.Honest.K12.Sim2.k1_mask_syms
#print axioms ProofFile.Honest.K12.Sim2.tree_of_mask_member
#print axioms ProofFile.Honest.K12.Sim2.k1_main_syms
#print axioms ProofFile.Honest.K12.Sim2.k1_fresh_syms
#print axioms ProofFile.Honest.K12.Sim2.tree_of_riding_member
#print axioms ProofFile.Honest.K12.Sim2.tree_column
#print axioms ProofFile.Honest.K12.Sim2.member_mask
#print axioms ProofFile.Honest.K12.Sim2.member_main
#print axioms ProofFile.Honest.K12.Sim2.k1_tree_in_front
#print axioms ProofFile.Honest.K12.Sim2.layRows_at
#print axioms ProofFile.Honest.K12.Sim2.mask_words
#print axioms ProofFile.Honest.K12.Sim2.k1_sender_at_run
