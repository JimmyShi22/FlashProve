-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/GroupsStruck.lean: WHERE THE TENANTS' TABLE RETURNS, THE KEY FILE's TABLE
WITH THE GROUPS RETURNS. A general law on `Key.toldOfChain` (Johnson/Desc/Key/Source.lean).
Statements with proofs. Nothing is evaluated.

`toldOfChain` first calls `ProofFile.toldChain` (Johnson/Desc/ProofFile/Told.lean). Then it makes that
table anew with each tenant's groups laid in (`rootsWithGroups`, `groupsAtLabel`), and refuses
unless the new table, its groups struck (`withoutGroups`), is the first one. `rootsWithGroups` is
`ProofFile.rootsOfSent`'s text but for the field `groups`; `ProofFile.tenantOf` lays that field empty; the sort
by rounds keeps the round. So the guard holds a list against itself, whatever the groups are: what
`groupsAtLabel` and `stageOfLabel` answer at a label is not read for a return.

  `tenant_struck`, `roots_struck`, `more_struck`, `more_fixed`, `toldAt_struck`: striking undoes the
    laying, at a tenant, at a sending's trees, at the trees that go in a round of their own.
  `mapM_map`: `mapM` in `Option`, under a map of the answers. `some_of_elim`: a tool.
  `sorted_struck`: striking goes through the sort by rounds (`List.map_mergeSort`).
  `toldOfChain_returns`: the law, general in the words, the chain, the plan, the trees beside and
    the held message.
IT TAKES A RETURN TO GIVE A RETURN: that `ProofFile.toldChain` returns at any chain is not shown here.
Limits. Nothing on which groups the table bears. Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.Core

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open OnBytes OnBytes.Params
open Johnson.G (ChainSends Sending)
open Johnson.G.OfPlan
open VerifiableInference.Desc.Key

/-- A tenant with its groups laid and struck again is the tenant. -/
theorem tenant_struck (n : OracleNotice) (g : List Nat) :
    ({ ({ ProofFile.tenantOf n with groups := g } : VerifiableInference.Desc.SymbolComponent) with groups := [] } :
      VerifiableInference.Desc.SymbolComponent) = ProofFile.tenantOf n := rfl

/-- With the groups struck, the trees with groups are the trees. -/
theorem roots_struck (codes : Codes) (sent : List OracleNotice) (gs : List (List Nat)) :
    (rootsWithGroups codes sent gs).map (·.map withoutGroups) = ProofFile.rootsOfSent codes sent := by
  unfold rootsWithGroups ProofFile.rootsOfSent
  cases layTrees codes sent.toArray with
  | none => rfl
  | some L =>
    simp only [Option.map_some, List.map_map]
    congr 1
    apply List.map_congr_left
    intro t _
    simp only [Function.comp, withoutGroups, List.map_map]
    congr 1

/-- A tree whose tenants bear no groups is left as it is. -/
theorem more_struck (a W : Nat) (held : Option OracleNotice) :
    withoutGroups { logLength := a, words := W, tenants := held.toList.map ProofFile.tenantOf } =
      { logLength := a, words := W, tenants := held.toList.map ProofFile.tenantOf } := by
  simp only [withoutGroups, List.map_map]
  congr 1

/-- `mapM` in `Option`, under a map of the answers. -/
theorem mapM_map {α β γ : Type} (f : α → Option γ) (g : α → Option β) (φ : β → γ)
    (h : ∀ x, (g x).map φ = f x) : ∀ l : List α, (l.mapM g).map (·.map φ) = l.mapM f
  | [] => rfl
  | x :: l => by
    rw [List.mapM_cons, List.mapM_cons, ← h x, ← mapM_map f g φ h l]
    cases g x with
    | none => rfl
    | some b =>
      cases l.mapM g with
      | none => rfl
      | some bs => rfl

/-- The pair's second part with its groups struck. -/
abbrev strike (q : Nat × ProofFile.Root) : Nat × ProofFile.Root := (q.1, withoutGroups q.2)

/-- One sending's trees with groups, struck, are `ProofFile.toldAt`'s. -/
theorem toldAt_struck (codes : Codes) (off : Nat) (x : Sending) :
    ((rootsWithGroups codes x.sent (groupsAtLabel x.label)).map fun l =>
      l.map fun r => (x.entry - 1 - off, r)).map (·.map strike) = ProofFile.toldAt codes off x := by
  unfold ProofFile.toldAt
  rw [← roots_struck codes x.sent (groupsAtLabel x.label), Option.map_map, Option.map_map]
  congr 1
  funext l
  simp only [Function.comp, List.map_map]
  rfl

/-- An `Option` turned into an `Except` returns just where it is `some`. -/
theorem some_of_elim {α : Type} {x : Option α} {e : String} {v : α}
    (h : x.elim (Except.error e) Except.ok = .ok v) : x = some v := by
  cases x with
  | none => exact nomatch h
  | some w => exact congrArg some (Except.ok.inj h)

/-- The trees that go in a round of their own bear no groups: striking leaves them. -/
theorem more_fixed (e : List Sent) (h : Option OracleNotice) :
    (e.map fun t =>
      ((t.round, ⟨t.a, t.W, h.toList.map ProofFile.tenantOf⟩) : Nat × ProofFile.Root)).map strike =
    e.map fun t => (t.round, ⟨t.a, t.W, h.toList.map ProofFile.tenantOf⟩) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro t _
  simp only [Function.comp, strike, more_struck]

/-- The sort by rounds keeps the round, so striking goes through it. -/
theorem sorted_struck (lg : List (List (Nat × ProofFile.Root))) (more : List (Nat × ProofFile.Root))
    (hm : more.map strike = more) :
    List.map withoutGroups (List.map (fun x => x.2)
      ((lg.flatten ++ more).mergeSort fun a b => decide (a.1 ≤ b.1))) =
    List.map (fun x => x.2)
      (((lg.map (·.map strike)).flatten ++ more).mergeSort fun a b => decide (a.1 ≤ b.1)) := by
  have e1 : (lg.map (·.map strike)).flatten ++ more = (lg.flatten ++ more).map strike := by
    rw [List.map_append, List.map_flatten, hm]
  rw [e1, ← List.map_mergeSort (r := fun a b => decide (a.1 ≤ b.1)) (f := strike)
    (fun _ _ _ _ => rfl), List.map_map, List.map_map]
  rfl

/-- **Where the tenants' table returns, the table with the groups returns.** -/
theorem toldOfChain_returns (a : String) (c : ChainSends) (P : Fmt.Plan) (e : List Sent)
    (h : Option OracleNotice) (p : List ProofFile.Root) (hp : ProofFile.toldChain a c P e h = .ok p) :
    ∃ t, toldOfChain a c P e h = .ok t := by
  have hq := hp
  unfold ProofFile.toldChain at hq
  obtain ⟨l₀, hl₀, hq⟩ := ok_of_bind hq
  obtain ⟨theirs, _, hq⟩ := ok_of_bind hq
  have hl := some_of_elim hl₀
  rw [← mapM_map _ _ _ (toldAt_struck c.codes (P.entries.length - P.rounds.length)) c.sends] at hl
  obtain ⟨lg, hlg, hlg'⟩ := Option.map_eq_some_iff.1 hl
  have key := sorted_struck lg _ (more_fixed e h)
  rw [hlg'] at key
  have hpv : List.map (fun x => x.2) ((l₀.flatten ++ e.map fun t =>
      ((t.round, ⟨t.a, t.W, h.toList.map ProofFile.tenantOf⟩) : Nat × ProofFile.Root)).mergeSort
        fun a b => decide (a.1 ≤ b.1)) = p := by
    dsimp only at hq
    split at hq
    · obtain ⟨_, hy, _⟩ := ok_of_bind hq
      exact nomatch hy
    · exact Except.ok.inj hq
  rw [hpv] at key
  refine ⟨List.map (fun x => x.2) ((lg.flatten ++ e.map fun t =>
      ((t.round, ⟨t.a, t.W, h.toList.map ProofFile.tenantOf⟩) : Nat × ProofFile.Root)).mergeSort
        fun a b => decide (a.1 ≤ b.1)), ?_⟩
  unfold toldOfChain
  refine bind_of_ok hp ?_
  refine bind_of_ok (a := lg) ?_ ?_
  · dsimp only
    rw [hlg]
    rfl
  · dsimp only
    rw [key, bne_self_eq_false]
    rfl

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.tenant_struck
#print axioms Johnson.AtFull.KeyBack.roots_struck
#print axioms Johnson.AtFull.KeyBack.more_struck
#print axioms Johnson.AtFull.KeyBack.mapM_map
#print axioms Johnson.AtFull.KeyBack.toldAt_struck
#print axioms Johnson.AtFull.KeyBack.some_of_elim
#print axioms Johnson.AtFull.KeyBack.more_fixed
#print axioms Johnson.AtFull.KeyBack.sorted_struck
#print axioms Johnson.AtFull.KeyBack.toldOfChain_returns
