-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB8/Laws.lean: general laws on the declared rounds of a description's chains,
links and two kinds of block. Statements and proofs; nothing is evaluated.

Why. A file's declared rounds (`FileDescription.roundsDeclaredByBlocks`, Johnson/Desc/Block.lean) are the rounds of all
blocks of its three flat lists. To hold them against a written list one wants them as a plain
append of the parts that have rounds, free of what the blocks decide.

Main names.
  `flat_rounds`, `link_rounds`, `retype_rounds`: the rounds of a chain's flat list, of a link's,
    and of a chain at another type of claims.
  `k12_rounds_at`: the rounds of a proximity test's block at a place's numbers are what
    `H2U.roundsOfNums` gives, where the place's chain is the numbers' and rounds are given. It
    takes no yes of the block's test on the plan (the library's `K12.k12_rounds` does).
  `entriesG_eq`: the entries of a lookup's block are those of the plain list `lookupList`, where
    the setting fits (`Made.FieldFit`) and the planner's two tests on the numbers say yes. By the
    library's laws "it ends well" (Johnson/Desc/First/Look/EntriesMade.lean) and "what it adds"
    (`runs_lookup`, OnBytes/Params/PlanListsSum.lean; `finish_rounds`,
    OnBytes/Params/PlanningLaws.lean).

Limits. Nothing on any value. Nothing on what a block decides. Nothing on soundness.

-/
import Johnson.Desc.Key.Desc
import Johnson.Desc.K12.FrameLaws
import Johnson.Desc.First.Look.EntriesMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB8

open VerifiableInference.Desc
open OnBytes OnBytes.Params

/-! ## Lists -/

/-- A list is mapped, then each member laid out as a list: in one step. -/
theorem flatMap_map' {α β γ : Type} (f : α → β) (g : β → List γ) :
    ∀ l : List α, (l.map f).flatMap g = l.flatMap fun a => g (f a)
  | [] => rfl
  | a :: l => by
    rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, flatMap_map' f g l]

/-- Where the numbers that `zipIdx` adds are not read, they can be left out. -/
theorem zipIdx_flatMap {α γ : Type} (g : α → List γ) :
    ∀ (l : List α) (n : Nat), (l.zipIdx n).flatMap (fun x => g x.1) = l.flatMap g
  | [], _ => rfl
  | a :: l, n => by
    show ((a, n) :: l.zipIdx (n + 1)).flatMap (fun x => g x.1) = _
    rw [List.flatMap_cons, List.flatMap_cons, zipIdx_flatMap g l (n + 1)]

/-! ## Chains and links -/

section
variable {S Cl Cl' : Type}

/-- The rounds of a chain's flat list: first, front, the links, back, last. -/
theorem flat_rounds (c : Chain S Cl) :
    c.blocksInOrder.flatMap (·.rounds) = c.first.rounds ++ (c.front.flatMap (·.rounds) ++
               (c.links.flatMap (fun L => L.blocksInOrder.flatMap (·.rounds)) ++
                 (c.back.flatMap (·.rounds) ++ c.last.rounds))) := by
  simp only [Chain.blocksInOrder, List.flatMap_cons, List.flatMap_append, List.flatMap_nil,
    List.append_nil, List.append_assoc, List.flatMap_assoc, flatMap_map']

/-- The rounds of a link's flat list: what is heard, the batching, the closing. -/
theorem link_rounds (L : Link S Cl) :
    L.blocksInOrder.flatMap (·.rounds) = L.hear.flatMap (·.rounds) ++
      ((L.batch (claimsInBy L.each L.hear L.order)).rounds ++ L.close.flatMap (·.rounds)) := by
  simp only [Link.blocksInOrder, roundlessBlock, List.cons_append, List.flatMap_cons, List.flatMap_append,
    List.flatMap_nil, List.nil_append, List.append_nil, List.append_assoc]

/-- A chain without links has the same rounds at another type of claims. -/
theorem retype_rounds (c : Chain S Cl) (h : c.links = []) :
    (c.retype : Chain S Cl').blocksInOrder.flatMap (·.rounds) = c.blocksInOrder.flatMap (·.rounds) := by
  rw [flat_rounds, flat_rounds, h]
  simp only [Chain.retype, Block.retype, flatMap_map', List.flatMap_nil]

end

/-! ## The proximity test -/

/-- The fold that deals a list of trees to the rounds lays one list for each round. -/
theorem fold_length {α : Type} : ∀ (l : List Fmt.DeclaredRound) (acc : List (List α) × List α),
    (l.foldl (fun (acc : List (List α) × List α) r =>
      (acc.2.take r.entry.roots :: acc.1, acc.2.drop r.entry.roots)) acc).1.length =
      acc.1.length + l.length
  | [], _ => rfl
  | r :: l, acc => by
    rw [List.foldl_cons, fold_length l, List.length_cons, List.length_cons]
    omega

/-- Numbers that give rounds have a stage. -/
theorem stages_of_rounds {N : H2U.TestNums} {rs : List Fmt.DeclaredRound}
    (hr : H2U.roundsOfNums N = some rs) : ∃ s rest, N.stages = s :: rest := by
  unfold H2U.roundsOfNums at hr
  split at hr
  · rename_i s next rest hs
    exact ⟨s, next :: rest, hs⟩
  · cases hr

/-- **The rounds of a proximity test's block at a place's numbers.** -/
theorem k12_rounds_at {T Cl : Type} (X : K12.Parts T) {place : Place} {x : H2U.PlaceNums}
    {rs : List Fmt.DeclaredRound} (hc : place.chain = x.chain)
    (hr : H2U.roundsOfNums x.nums = some rs) :
    (K12.proximityTestKind X (H2U.proximityTestParametersAt place x) : Block T Cl).rounds = rs := by
  obtain ⟨s, rest, hs⟩ := stages_of_rounds hr
  obtain ⟨os, ho, hl⟩ : ∃ os, H2U.testOracles5 x.nums x.firstGroup = some os ∧
      os.length = rs.length := by
    refine ⟨_, by unfold H2U.testOracles5; rw [hr]; rfl, ?_⟩
    rw [List.length_reverse, fold_length]
    exact Nat.zero_add _
  obtain ⟨os', ho'⟩ : ∃ os', H2U.testOracles x.nums = some os' :=
    ⟨_, by unfold H2U.testOracles; rw [hr]; rfl⟩
  have e : H2U.proximityTestParametersAt place x = ⟨place, x.nums, x.idx, os, H2U.beforeOf x.chain x.nums, x.answers,
                          x.early⟩ := by
    unfold H2U.proximityTestParametersAt
    rw [hc, ho]
    simp
  rw [e]
  unfold K12.proximityTestKind
  split
  · rename_i first rest' rs' os'' h1 h2 h3
    have h2' : H2U.roundsOfNums x.nums = some rs' := h2
    have e2 : rs' = rs := Option.some.inj (h2'.symm.trans hr)
    subst e2
    simp only [Block.andThen, K12.Part.at, K12.asks, K12.stagesFrom_rounds, List.map_nil,
      List.nil_append, List.append_nil]
    rw [← List.map_append, List.take_append_drop, List.map_fst_zip (by omega)]
  · rename_i hno
    exact (hno s rest rs os' hs hr ho').elim

/-! ## The lookup -/

/-- **The entries of a lookup's block are those of the plain list.** -/
theorem entriesG_eq {set : Setting} {c : Scope} {f : K3.Face} (hf : First.Look.Made.FieldFit set c)
    (h1 : (decide (1 ≤ f.size.mu) && decide (f.size.mu ≤ 6) &&
      decide (2 ≤ (if f.size.live != 0 then f.size.live else 2 ^ min f.size.mu 6)) &&
      decide ((if f.size.live != 0 then f.size.live else 2 ^ min f.size.mu 6) ≤
        2 ^ min f.size.mu 6)) = true)
    (h2 : (decide (sumT ((if f.size.parts.isEmpty then [f.size.v] else f.size.parts).map (2 ^ ·)) <
        2 ^ (if f.size.live != 0 then f.size.live else 2 ^ min f.size.mu 6)) &&
      decide (2 ^ f.size.d * (2 ^ (if f.size.live != 0 then f.size.live
        else 2 ^ min f.size.mu 6) - 1) < set.p)) = true) :
    K3.entriesG set c f = some ((lookupList set f.size).map fun y => (y.round set c).entry) := by
  obtain ⟨P, e⟩ := First.Look.Made.finish_ends
    (First.Look.Made.ends_lookup (s := set) (c := c) f.size h1 h2)
    (First.Look.Made.good_lookup hf _)
  have r := (finish_rounds (runs_lookup f.size) e).2.1
  unfold K3.entriesG
  rw [e]
  show some (P.rounds.map (·.entry)) = _
  rw [r, List.map_map]
  rfl

end Johnson.KB8

#print axioms Johnson.KB8.flatMap_map'
#print axioms Johnson.KB8.zipIdx_flatMap
#print axioms Johnson.KB8.flat_rounds
#print axioms Johnson.KB8.link_rounds
#print axioms Johnson.KB8.retype_rounds
#print axioms Johnson.KB8.fold_length
#print axioms Johnson.KB8.stages_of_rounds
#print axioms Johnson.KB8.k12_rounds_at
#print axioms Johnson.KB8.entriesG_eq
