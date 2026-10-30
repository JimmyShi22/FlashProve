-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/BkLink.lean: WHAT THE TABLE's PROMISE READS OF THE RECORD IS LEFT AS IT
WAS (`Rb`, RbRuns.lean) BY A YES OF THREE OF A LINK's LAST BLOCKS: THE BATCHING, THE FRAME's BLOCK
BEHIND IT, THE SHUTTING: the three whose rows close and open no class of rows and no pin. Theorems
on the blocks' steps.

What is said.
  `drawn_link`: the draw's return bears the link's number. `rb_batch`, `rb_behind`: **a yes of the
    batching's block, and of the frame's block behind it, stands in `Rb`**, from the same of every
    run of the link's two orders. `rb_shutB`: **so does a yes of the shutting, and it leaves the
    rows owed.**

Limits. The runs' share is a premise: RelRuns.lean pays it at each sort from `rests_rb`, the
lookup's runs' share aside. The one equation's block is not here: it lays a row. That the record's
half of the promise is handed on is other files' to show: these are stuff for it at 75 of the first
chain's blocks. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.RbRuns
import Johnson.Desc.First.Link.Law.ShapeRides
import Johnson.Desc.First.Link.Law.LaidAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (atS Where shut closed drawn drawnClean)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.JoinAtBlocks

/-- The draw's return bears the link's number. -/
theorem drawn_link (rows : ℕ) (chi : E) (owed : Option ℕ) (used : ℕ) (L : LinkCtx) (F : Fork)
    (o : K9.Drawn) (h : drawnClean rows chi owed used L F = .ok o) : o.L.link = L.link := by
  unfold drawnClean at h
  obtain ⟨o', ho, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain rfl : o' = o := Except.ok.inj h
  unfold drawn at ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  rw [← Except.ok.inj ho]

/-- **A yes of the batching's block stands in Rb.** -/
theorem rb_batch (L : Link S Claim) (p : Where)
    (hb₁ : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (hk : ∀ o ∈ L.order, ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c, e₁) → Rb e e₁)
    (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (k : ℕ)
    (h : L.batchB.step ft s rs cols = .ok (s', k)) : Rb s s' := by
  obtain ⟨r, x, a, o, cls, _, _, ha, hd, hy⟩ := hb₁ ft s rs cols s' k h
  obtain ⟨u, c, c', ⟨e, q, G, hg, hq, _, rfl⟩, ⟨rfl, _⟩, _⟩ := hy
  have h0 : Rb s (atS.set s { a with owed := o.owed, L := o.L, F := o.F }) :=
    rb_set s a _ ha rfl (drawn_link _ _ _ _ _ _ _ hd)
  have h1 : Rb s e := gather_holds (Rb s) (fun _ => []) [] (runsIn L.hear L.order)
    (fun r' hr' n e0 c0 e1 hr0 hx => by
      obtain ⟨o', ho', e'⟩ := List.mem_filterMap.1 hr'
      obtain ⟨run, hrun, rfl⟩ := Option.map_eq_some_iff.1 e'
      exact hx.trans (hk o' ho' run hrun n e0 c0 e1 hr0)) ([], _) (c, e)
    (fold_gstep L.each L.hear L.order ([], _) (c, e) hg) h0
  exact h1.trans (rb_set e q _ hq rfl rfl)

/-- **A yes of the frame's block behind the batching stands in Rb.** -/
theorem rb_behind (L : Link S Claim)
    (hk : ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ → Rb e e₁)
    (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (k : ℕ)
    (h : L.behindB.step ft s rs cols = .ok (s', k)) : Rb s s' := by
  obtain ⟨rs', gs, hd⟩ := step_decide L.behindB _ _ _ _ _ k h
  obtain ⟨cls, hy⟩ := (behind_isMoves atS L).dec _ _ _ _ hd
  obtain ⟨u, c, c', ⟨hq, _⟩, ⟨rfl, _⟩, _⟩ := hy
  exact ran_holds (Rb s) L.hear L.orderAfter _ _
    (afterIn_ran L.hear L.orderAfter _ _ (Link.afterIn_of_runBehind hq))
    (fun o ho run hl x x₁ hr hx => hx.trans (hk o ho run hl x x₁ hr)) (Rb.refl s)

/-- **A yes of the shutting stands in Rb, and leaves the rows owed.** -/
theorem rb_shutB {Cl : Type} (pw : Where) (piece : ℕ) (b₅ : Block S Cl)
    (hb₅ : ∀ ft s rs cols x, b₅.step ft s rs cols = .ok x →
      (shut (Cl := Cl) pw piece).step ft s rs cols = .ok x)
    (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (k : ℕ)
    (h : b₅.step ft s rs cols = .ok (s', k)) : Rb s s' ∧ s'.rowsOwed = s.rowsOwed := by
  obtain ⟨L, hL, rfl⟩ := shut_inv pw piece _ _ _ _ _ k (hb₅ _ _ _ _ _ h)
  exact ⟨rb_putLink s L _ hL rfl, (stand_putLink s _).2.1⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.rb_batch
#print axioms VerifiableInference.Desc.LinkJoin.rb_behind
#print axioms VerifiableInference.Desc.LinkJoin.rb_shutB
