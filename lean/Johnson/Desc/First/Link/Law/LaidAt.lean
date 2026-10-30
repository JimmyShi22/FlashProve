-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/LaidAt.lean: THE TWO PUBLIC FACTS THAT THE ONE EQUATION's PIECE LEANS ON
(«the rows owed are the batching round's»; `LaidOk`), AT A LINK: BOTH HOLD BEHIND A YES OF THE
BATCHING's BLOCK, AND BOTH STAY OVER A YES OF THE FRAME's BLOCK BEHIND IT. Theorems on the blocks'
steps, over OwedRides.lean, LaidRides.lean and RelRuns.lean.

What is said.
  `TwoFacts p s`: the two facts. `rests_laid`: «`LaidOk` in front gives `LaidOk` behind» holds of
    the six writings of RelRuns.lean (the smallness test's equations make it; all else keeps it).
    `laid_made`: **behind a yes of the batching's block `LaidOk` holds**, if every run of the order
    keeps it and the run at an entry of the order stands under the smallness test's run of
    equations. `ran_holds`, `laid_kept`: it stays over a yes of the frame's block behind the
    batching. `facts_made`, `facts_kept`: **the two facts together**, from the runs' duties for
    both.

Limits. The runs' duties are premises: RelRuns.lean (at `rests_laid`) and KeepsAny.lean (at
`rests_owed`) pay them at each sort of link from the sort's Take, the lookup's runs' share aside.
THE TWO FACTS PASS FROM PIECE TO PIECE ONLY THROUGH THE CONDITIONS AT THE BOUNDARIES: where these
are the table's own promise, the facts stay names at the table's door, and these theorems are what
makes the promise ride. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LaidRides
import Johnson.Desc.First.Link.Law.RelRuns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Wrote)
open VerifiableInference.Desc.K9 (atS Where owedOf)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.JoinAtBlocks

/-- The two public facts. -/
def TwoFacts (p : Where) (s : S) : Prop := owedOf s = some p.rows ∧ LaidOk s

/-- What a run of the layers' own kind writes leaves the pair. -/
theorem pair_wrote {e e₁ : S} {a : First.LayOwn} {G : Fork} (hw : Wrote e a G e₁) :
    pairOf e₁ = pairOf e := by
  obtain ⟨h1, rfl⟩ := hw
  unfold pairOf S.tl? S.funs?
  rw [h1]

/-- A writing of the head's ledger leaves the pair. -/
theorem pair_head (s : S) (a : First.HeadOwn) (G : Fork) (h : s.here = .head a) :
    pairOf { s with here := .head { a with F := G } } = pairOf s := by
  unfold pairOf S.tl? S.funs?
  rw [h]

/-- «LaidOk in front gives LaidOk behind» holds of the six writings. -/
theorem rests_laid : RelRests fun e e₁ => LaidOk e → LaidOk e₁ where
  refl _ := id
  wrote _ _ _ _ hw := laidOk_congr (pair_wrote hw)
  head s a G h := laidOk_congr (pair_head s a G h)
  eq n e c e₁ h _ := k8Run_laid n e e₁ c h
  ls e e₁ h := k8LsTail_laid e e₁ h
  tests nU e e₁ h := k8Tests_laid nU e e₁ h

/-- **Behind a yes of the batching's block LaidOk holds.** -/
theorem laid_made (L : Link S Claim) (p : Where)
    (hb₁ : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (hk : ∀ o ∈ L.order, ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c, e₁) →
      LaidOk e → LaidOk e₁)
    (oE : ℕ × String) (hoE : oE ∈ L.order) (runE : ℕ → S → Except String (List Claim × S))
    (hAtE : At L oE runE) (hE : Under runE k8Run.2) (ft : ℕ) (s : S) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (s' : S) (k : ℕ) (h : L.batchB.step ft s rs cols = .ok (s', k)) :
    LaidOk s' := by
  obtain ⟨r, x, a, o, cls, _, _, _, _, hy⟩ := hb₁ ft s rs cols s' k h
  obtain ⟨u, c, c', ⟨e, q, G, hg, _, _, rfl⟩, ⟨rfl, _⟩, _⟩ := hy
  refine laidOk_congr (pair_set e _) ?_
  refine gather_made LaidOk (fun _ => []) [] (runsIn L.hear L.order) (fun r' hr' => ?_)
    ⟨(oE.2, runE), List.mem_filterMap.2 ⟨oE, hoE, ?_⟩, fun n e0 c0 e1 hr0 =>
      k8Run_laid n e0 e1 c0 (hE n e0 c0 e1 hr0)⟩ ([], _) (c, e)
    (fold_gstep L.each L.hear L.order ([], _) (c, e) hg)
  · obtain ⟨o', ho', e'⟩ := List.mem_filterMap.1 hr'
    obtain ⟨run, hrun, rfl⟩ := Option.map_eq_some_iff.1 e'
    exact hk o' ho' run hrun
  · rw [show ((L.hear[oE.1]?).bind fun b => b.claims.lookup oE.2) = some runE from hAtE]
    rfl

/-- Along a chain of yeses of the runs behind the batching a sentence that each keeps stays. -/
theorem ran_holds (Pp : S → Prop) (bs : List (Block S Claim)) :
    ∀ (order : List (ℕ × String)) (e e₁ : S), Ran bs order e e₁ →
      (∀ o ∈ order, ∀ run, ((bs[o.1]?).bind fun b => b.after.lookup o.2) = some run →
        ∀ x x₁, run x = .ok x₁ → Pp x → Pp x₁) → Pp e → Pp e₁
  | _, _, _, .nil _, _, h => h
  | _, _, _, .cons o l run e e' e₁ hl hr ht, hk, h =>
    ran_holds Pp bs l e' e₁ ht (fun o' ho' => hk o' (List.mem_cons_of_mem _ ho'))
      (hk o List.mem_cons_self run hl e e' hr h)

/-- LaidOk stays over a yes of the frame's block behind the batching. -/
theorem laid_kept (L : Link S Claim)
    (hk : ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ →
      LaidOk e → LaidOk e₁)
    (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (k : ℕ)
    (h : L.behindB.step ft s rs cols = .ok (s', k)) (hs : LaidOk s) : LaidOk s' := by
  obtain ⟨rs', gs, hd⟩ := step_decide L.behindB _ _ _ _ _ k h
  obtain ⟨cls, hy⟩ := (behind_isMoves atS L).dec _ _ _ _ hd
  obtain ⟨u, c, c', ⟨hq, _⟩, ⟨rfl, _⟩, _⟩ := hy
  exact ran_holds LaidOk L.hear L.orderAfter _ _
    (afterIn_ran L.hear L.orderAfter _ _ (Link.afterIn_of_runBehind hq)) hk hs

/-- **THE TWO FACTS BEHIND A YES OF THE BATCHING's BLOCK.** -/
theorem facts_made (L : Link S Claim) (p : Where) (hp : p.rows ≠ 0)
    (hb₁ : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (ho : MoveKeeps owedOf (.add (claimsInBy L.each L.hear L.order)))
    (hk : ∀ o ∈ L.order, ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c, e₁) →
      LaidOk e → LaidOk e₁)
    (oE : ℕ × String) (hoE : oE ∈ L.order) (runE : ℕ → S → Except String (List Claim × S))
    (hAtE : At L oE runE) (hE : Under runE k8Run.2) (ft : ℕ) (s : S) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (s' : S) (k : ℕ) (h : L.batchB.step ft s rs cols = .ok (s', k)) :
    TwoFacts p s' :=
  ⟨owed_made p hp _ L.batchB hb₁ (fun m hm => by
      obtain rfl := List.mem_singleton.1 hm
      exact ho) ft s rs cols s' k h,
    laid_made L p hb₁ hk oE hoE runE hAtE hE ft s rs cols s' k h⟩

/-- **THE TWO FACTS STAY OVER A YES OF THE FRAME's BLOCK BEHIND THE BATCHING.** -/
theorem facts_kept (L : Link S Claim) (p : Where) (ho : MoveKeeps owedOf (.quiet L.runBehind))
    (hk : ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ →
      LaidOk e → LaidOk e₁)
    (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (k : ℕ)
    (h : L.behindB.step ft s rs cols = .ok (s', k)) (hs : TwoFacts p s) : TwoFacts p s' :=
  ⟨(owed_kept _ L.behindB (behind_isMoves atS L) (fun m hm => by
      obtain rfl := List.mem_singleton.1 hm
      exact ho) ft s rs cols s' k h).trans hs.1,
    laid_kept L hk ft s rs cols s' k h hs.2⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.rests_laid
#print axioms VerifiableInference.Desc.LinkJoin.laid_made
#print axioms VerifiableInference.Desc.LinkJoin.laid_kept
#print axioms VerifiableInference.Desc.LinkJoin.facts_made
#print axioms VerifiableInference.Desc.LinkJoin.facts_kept
