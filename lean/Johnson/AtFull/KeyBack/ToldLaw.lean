-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/ToldLaw.lean: WHAT IS TOLD OF THE KEY FILE's THREE CHAINS RETURNS WHERE
`treesSent` RETURNS AT THEM. General laws on `ProofFile.toldChain` (Johnson/Desc/ProofFile/Told.lean) and
`Key.toldOfMade` (Johnson/Desc/Key/Source.lean). Statements with proofs. Nothing is evaluated.

`ProofFile.toldChain` can refuse at three places: the `mapM` of `toldAt`; its call of `treesSent`
(Johnson/G/RoundsOfPlan.lean); a guard that holds its own trees' depths and widths against
`treesSent`'s. `toldAt` and `sentAt` run over one list of trees in one order, with one round, depth
and width for each; the trees beside agree entry by entry; both lists are sorted by rounds, and the
sort keeps the order of equals. So where `treesSent` returns, the `mapM` returns and the guard holds
a list against itself.

  `tri₁`, `tri₂`: a tree as round, depth and width, on either side.
  `toldAt_of_sentAt`, `toldAt_mapM`: at a sending, and along a chain's sendings.
  `sorted_same`: the two sorted lists agree in depth and width (`List.map_mergeSort`, twice).
  `toldChain_returns`: where `treesSent` returns, `ProofFile.toldChain` returns. The unfolding of
    `toldChain` is the law `toldChain_of` (Johnson/Unfolds/ToldLaw.lean), which
    takes the `mapM`'s return and the guard's answer as premises; these two are paid here.
  `toldOfMade_returns`: from `TreesK` (Core.lean): that law and `toldOfChain_returns`
    (GroupsStruck.lean), at each of the three chains.
IT TAKES A RETURN TO GIVE A RETURN: that `treesSent` returns at any chain, or `TreesK` holds at any
m, is not shown here. `Key.sourceOf` is not shown to return: its other step, `declKOf`, is another
file's.
Limits. Nothing on the tables' values. Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.GroupsStruck
import Johnson.Unfolds.ToldLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open OnBytes OnBytes.Params
open Johnson.G (ChainSends Sending)
open Johnson.G.OfPlan
open VerifiableInference.Desc.Key

/-- A tree with its round, as round, depth and width. -/
abbrev tri₁ (q : Nat × ProofFile.Root) : Nat × Nat × Nat := (q.1, q.2.logLength, q.2.words)
/-- The same of a tree as `sentAt` gives it. -/
abbrev tri₂ (t : Sent) : Nat × Nat × Nat := (t.round, t.a, t.W)

/-- One sending: where `sentAt` returns, `ProofFile.toldAt` does, with the same rounds, depths, widths. -/
theorem toldAt_of_sentAt (a : String) (codes : Codes) (off : Nat) (x : Sending) (s : List Sent)
    (h : sentAt a codes off x = .ok s) :
    ∃ r, ProofFile.toldAt codes off x = some r ∧ r.map tri₁ = s.map tri₂ := by
  unfold sentAt at h
  dsimp only at h
  split at h
  · obtain ⟨tag, _, h⟩ := ok_of_bind h
    split at h
    · rename_i L hlt
      obtain ⟨L', hL', h⟩ := ok_of_bind h
      obtain rfl := Except.ok.inj hL'
      have hs := Except.ok.inj h
      unfold ProofFile.toldAt ProofFile.rootsOfSent
      rw [hlt]
      simp only [Option.map_some]
      refine ⟨_, rfl, ?_⟩
      rw [← hs]
      simp only [List.map_map]
      apply List.map_congr_left
      rintro ⟨t, i⟩ _
      rfl
    · obtain ⟨_, hy, _⟩ := ok_of_bind h
      exact nomatch hy
  · obtain ⟨_, hy, _⟩ := ok_of_bind h
    exact nomatch hy

/-- The same along a chain's sendings. -/
theorem toldAt_mapM (a : String) (codes : Codes) (off : Nat) :
    ∀ (xs : List Sending) (ls : List (List Sent)), xs.mapM (sentAt a codes off) = .ok ls →
      ∃ l, xs.mapM (ProofFile.toldAt codes off) = some l ∧ l.map (·.map tri₁) = ls.map (·.map tri₂)
  | [], ls, h => by
    rw [List.mapM_nil] at h
    obtain rfl := Except.ok.inj h
    exact ⟨[], by rw [List.mapM_nil]; rfl, rfl⟩
  | x :: xs, ls, h => by
    rw [List.mapM_cons] at h
    obtain ⟨s, hs, h⟩ := ok_of_bind h
    obtain ⟨ss, hss, h⟩ := ok_of_bind h
    obtain rfl := Except.ok.inj h
    obtain ⟨r, hr, hr'⟩ := toldAt_of_sentAt a codes off x s hs
    obtain ⟨l, hl, hl'⟩ := toldAt_mapM a codes off xs ss hss
    refine ⟨r :: l, ?_, ?_⟩
    · rw [List.mapM_cons, hr, hl]
      rfl
    · simp only [List.map_cons, hr', hl']

/-- Two lists with the same rounds, depths and widths, each sorted by rounds, agree in depth and
width, entry by entry. -/
theorem sorted_same (A : List (Nat × ProofFile.Root)) (B : List Sent) (hAB : A.map tri₁ = B.map tri₂) :
    List.map (fun r : ProofFile.Root => (r.logLength, r.words)) (List.map (fun x => x.2)
            (A.mergeSort fun a b => decide (a.1 ≤ b.1))) =
    List.map (fun t : Sent × Nat => (t.1.a, t.1.W))
      (B.mergeSort fun a b => decide (a.round ≤ b.round)).zipIdx := by
  have e1 : List.map (fun r : ProofFile.Root => (r.logLength, r.words)) (List.map (fun x => x.2)
            (A.mergeSort fun a b => decide (a.1 ≤ b.1))) =
      List.map (fun x => x.2) ((A.map tri₁).mergeSort fun a b => decide (a.1 ≤ b.1)) := by
    rw [← List.map_mergeSort (r := fun a b => decide (a.1 ≤ b.1)) (f := tri₁)
      (fun _ _ _ _ => rfl), List.map_map, List.map_map]
    rfl
  have e2 : List.map (fun t : Sent × Nat => (t.1.a, t.1.W))
      (B.mergeSort fun a b => decide (a.round ≤ b.round)).zipIdx =
      List.map (fun x => x.2) ((B.map tri₂).mergeSort fun a b => decide (a.1 ≤ b.1)) := by
    rw [← List.map_mergeSort (r := fun a b => decide (a.round ≤ b.round)) (f := tri₂)
      (fun _ _ _ _ => rfl), List.map_map]
    have e3 : (fun t : Sent × Nat => (t.1.a, t.1.W)) =
        ((fun x : Nat × Nat × Nat => x.2) ∘ tri₂) ∘ Prod.fst := rfl
    rw [e3, ← List.map_map, List.zipIdx_map_fst]
  rw [e1, e2, hAB]

/-- **Where `treesSent` returns, the tenants' table returns.** The unfolding of
`ProofFile.toldChain` is the law `toldChain_of`; paid here are its two premises on the
`mapM` of `toldAt` and on the guard. -/
theorem toldChain_returns (a : String) (c : ChainSends) (P : Fmt.Plan) (e : List Sent)
    (h : Option OracleNotice) (ts : List (Sent × Nat)) (ht : treesSent a c P e = .ok ts) :
    ∃ p, ProofFile.toldChain a c P e h = .ok p := by
  have hq := ht
  unfold treesSent at hq
  obtain ⟨ls, hls, hq⟩ := ok_of_bind hq
  have hts : ts = ((ls.flatten ++ e).mergeSort fun a b => decide (a.round ≤ b.round)).zipIdx := by
    dsimp only at hq
    split at hq
    · exact nomatch hq
    · split at hq
      · exact (Except.ok.inj hq).symm
      · obtain ⟨_, hy, _⟩ := ok_of_bind hq
        exact nomatch hy
  obtain ⟨l, hl, hl'⟩ := toldAt_mapM a c.codes _ c.sends ls hls
  refine ⟨_, Johnson.Unfolds.toldChain_of (held := h) hl ht ?_⟩
  unfold Johnson.Unfolds.mineW
  have hAB : (l.flatten ++ e.map fun t =>
      ((t.round, ⟨t.a, t.W, h.toList.map ProofFile.tenantOf⟩) : Nat × ProofFile.Root)).map tri₁ =
      (ls.flatten ++ e).map tri₂ := by
    rw [List.map_append, List.map_append, List.map_flatten, List.map_flatten, hl', List.map_map]
    rfl
  rw [hts, sorted_same _ _ hAB, bne_self_eq_false]

/-- **What is told of the key file's three chains returns, where `treesSent` returns at them.** -/
theorem toldOfMade_returns (m : Made) (t₀ t₁ t₂ : List (Sent × Nat)) (hT : TreesK m t₀ t₁ t₂) :
    ∃ T, toldOfMade m = .ok T := by
  obtain ⟨p₀, hp₀⟩ := toldChain_returns "the tenants, first chain" _ _ _ none _ (hT.first _)
  obtain ⟨p₁, hp₁⟩ := toldChain_returns "the tenants, shared chain" _ _ _
    ((shapeK m).testOmega.head?.map fun st => foldMaskNotice (ioppFoldShape st {})) _ (hT.shared _)
  obtain ⟨p₂, hp₂⟩ := toldChain_returns "the tenants, second chain" _ _ _ none _ (hT.second _)
  obtain ⟨u₀, hu₀⟩ := toldOfChain_returns _ _ _ _ _ _ hp₀
  obtain ⟨u₁, hu₁⟩ := toldOfChain_returns _ _ _ _ _ _ hp₁
  obtain ⟨u₂, hu₂⟩ := toldOfChain_returns _ _ _ _ _ _ hp₂
  refine ⟨(u₀, u₁, u₂), ?_⟩
  unfold toldOfMade toldOfPlans
  dsimp only
  refine bind_of_ok hu₀ ?_
  refine bind_of_ok hu₁ ?_
  exact bind_of_ok hu₂ rfl

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.toldAt_of_sentAt
#print axioms Johnson.AtFull.KeyBack.toldAt_mapM
#print axioms Johnson.AtFull.KeyBack.sorted_same
#print axioms Johnson.AtFull.KeyBack.toldChain_returns
#print axioms Johnson.AtFull.KeyBack.toldOfMade_returns
