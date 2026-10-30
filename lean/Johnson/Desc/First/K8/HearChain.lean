-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/HearChain.lean: THE SMALLNESS TEST, ITS FIRST HALF (the draw of the matrix): A
WHOLE MEMBER's DECISION ON THE FIRST CHAIN's SHAPE: one step with code on ChainSh
(Johnson/Desc/First/Shape/Chain.lean), with the laws both ways. General laws: nothing is evaluated.

  drawOf, drawOf_sh   what the decision reads, off the whole shape of the smallness test's record
                  (Johnson/Desc/First/Shape/Tail.lean).
  drawGuard p     THE MEMBER's Bool on the chain's shape.
  drawTl p n      THE MEMBER's UPDATE, on the record's shape: n entries and the first columns laid.
  drawG p n       THE STEP: no link is open: a refusal by name; else the Bool, then the update. It
                  names no position in the chain's shape: it goes by ChainSh's readers and setTl.
  **draw_carries**   a yes of the decision on one round: the step, at that round's number of
                  entries, RETURNS at the state's shape, and returns the shape behind.
  **draw_returns**   where the step returns at the state's shape the decision says yes on any one
                  round. It has no test on values.
  draw_carriesR, draw_returnsR   the two laws for the decision as one run. draw_carriesR asks that
                  a list of one round have n entries. draw_returnsR is draw_returns with its letters
                  in another order: on one round; n and the shape returned play no part in it.
  draw_no_round   on no round the decision says no, whatever the state.
  draw_count_matters   behind a yes on a round with another number of entries the step does not
                  return the shape behind. (That the R-laws would FAIL without "one round" and "n
                  entries" follows from these two only where a state is had at which the step
                  returns, or the decision says yes: none is shown here.)
  drawG_between   where the shape bears no record of the smallness test the step refuses.
Over draw_iff (Johnson/Desc/First/K8/HearShape.lean).

Limits. The decision alone: the frame's tests in front of it (the round's form, the mark) and the
member's runs of claims are not here. That a round of the plan's form has columns x tau entries is
the frame's test. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.K8.HearShape
import Johnson.Desc.First.Shape.Chain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open OnBytes.Model
open VerifiableInference.Desc.First.Shape

/-- What the draw's decision reads, off the whole shape of the record. -/
def drawOf (t : TailSh) : DrawSh :=
  DrawSh.mk t.funClosed t.cfF t.foldDrawn t.NM (t.mats.toList.map (·.k)) (t.mats.toList.map (·.m))
    t.tau (t.funs.map fun f => (f.mat, f.len, f.start)) t.cfFirst.toList

theorem drawOf_sh (tl : HTailF2) : drawOf (tailSh tl) = drawSh tl := by
  show DrawSh.mk _ _ _ _ _ _ _ ((tl.funs.toList.map funSh).map fun f => (f.mat, f.len, f.start)) _ =
    _
  rw [List.map_map]
  rfl

/-- **THE MEMBER's Bool.** -/
def drawGuard (p : Par) (a : ChainSh) : Bool := drawB p a.rowsOwed (a.tl.map drawOf)

/-- **THE MEMBER's UPDATE**, on the record's shape. n: the number of the round's entries. -/
def drawTl (p : Par) (n : Nat) (t : TailSh) : TailSh :=
  { t with cfF := n, cfFirst := firstColumns p }

/-- **THE STEP ON THE CHAIN's SHAPE.** -/
def drawG (p : Par) (n : Nat) (a : ChainSh) : Except String ChainSh :=
  match a.tl with
  | none => .error "the draw: no link is open"
  | some t =>
    if drawGuard p a then .ok (a.setTl (drawTl p n t))
    else .error "the draw: the shape does not pass"

theorem drawGuard_sh (p : Par) (s : S) :
    drawGuard p (chainSh s) = drawB p s.rowsOwed (s.tl?.map drawSh) := by
  show drawB p s.rowsOwed ((s.tl?.map tailSh).map drawOf) = _
  rw [Option.map_map]
  have e : (drawOf ∘ tailSh) = drawSh := funext drawOf_sh
  rw [e]

theorem tl_sh {s : S} {tl : HTailF2} (ht : s.tl? = some tl) :
    (chainSh s).tl = some (tailSh tl) := by
  show s.tl?.map tailSh = _
  rw [ht]
  rfl

/-- **A yes of the decision: the step returns, and returns the shape behind.** -/
theorem draw_carries {Cl : Type} {p : Par} {s s' : S} {r : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (approximateRangeProofDrawKind (Cl := Cl) atS p).decide s [r] gs = .ok s') :
    drawG p r.drawn.trits.length (chainSh s) = .ok (chainSh s') := by
  obtain ⟨hb, tl, ht, rfl⟩ := (draw_iff p s s' r gs).1 h
  unfold drawG
  rw [tl_sh ht]
  dsimp only
  rw [if_pos (by rw [drawGuard_sh]; exact hb), chainSh_putTl]
  rfl

/-- **Where the step returns the decision says yes**, on any one round. -/
theorem draw_returns {Cl : Type} (p : Par) (n : Nat) (s : S) (r : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) {t : ChainSh} (h : drawG p n (chainSh s) = .ok t) :
    ∃ s', (approximateRangeProofDrawKind (Cl := Cl) atS p).decide s [r] gs = .ok s' := by
  unfold drawG at h
  cases ht : s.tl? with
  | none =>
    have e : (chainSh s).tl = none := by
      show s.tl?.map tailSh = _
      rw [ht]
      rfl
    rw [e] at h
    cases h
  | some tl =>
    rw [tl_sh ht] at h
    dsimp only at h
    by_cases hb : drawGuard p (chainSh s) = true
    · rw [drawGuard_sh] at hb
      exact ⟨_, (draw_iff p s _ r gs).2 ⟨hb, tl, ht, rfl⟩⟩
    · rw [if_neg hb] at h
      cases h

/-- "Carries" for the decision as one run, at rounds of the plan's form. On no round, or on two, the
decision says no, so nothing is asked there. -/
theorem draw_carriesR {Cl : Type} (p : Par) (n : Nat) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hn : ∀ r, rs = [r] → r.drawn.trits.length = n) :
    ∀ s s' t, (approximateRangeProofDrawKind (Cl := Cl) atS p).decide s rs gs = .ok s' → drawG p n (chainSh s) = .ok t →
      t = chainSh s' := by
  intro s s' t hd hg
  obtain ⟨r, rfl⟩ := decide_one atS p s s' rs gs hd
  have e := draw_carries hd
  rw [hn r rfl, hg] at e
  exact Except.ok.inj e

/-- "Returns" for the decision as one run, on one round: draw_returns, its letters in another
order. -/
theorem draw_returnsR {Cl : Type} (p : Par) (n : Nat) (r : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    ∀ s t, drawG p n (chainSh s) = .ok t →
      ∃ s', (approximateRangeProofDrawKind (Cl := Cl) atS p).decide s [r] gs = .ok s' :=
  fun s _ hg => draw_returns p n s r gs hg

/-- On no round the decision says no, whatever the state. -/
theorem draw_no_round {Cl : Type} (p : Par) (s s' : S) (gs : List (List (Nat × List UInt64))) :
    (approximateRangeProofDrawKind (Cl := Cl) atS p).decide s [] gs ≠ .ok s' := by
  intro h
  obtain ⟨r, e⟩ := decide_one atS p s s' [] gs h
  cases e

/-- And the number of entries: a yes on a round with another number of entries, and the step does
not return the shape behind. -/
theorem draw_count_matters {Cl : Type} {p : Par} {n : Nat} {s s' : S} {r : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (approximateRangeProofDrawKind (Cl := Cl) atS p).decide s [r] gs = .ok s') (hn : r.drawn.trits.length ≠ n) :
    drawG p n (chainSh s) ≠ .ok (chainSh s') := by
  intro hg
  have hc := draw_carries h
  obtain ⟨hb, tl, ht, -⟩ := (draw_iff p s s' r gs).1 h
  have hb' : drawGuard p (chainSh s) = true := by rw [drawGuard_sh]; exact hb
  unfold drawG at hg hc
  rw [tl_sh ht] at hg hc
  dsimp only at hg hc
  rw [if_pos hb'] at hg hc
  have e := (Except.ok.inj hg).trans (Except.ok.inj hc).symm
  have e1 : ∀ x, ((chainSh s).setTl x).tl = some x := by
    intro x
    show (chainSh s).tl.map _ = _
    rw [tl_sh ht]
    rfl
  have e2 := congrArg ChainSh.tl e
  rw [e1, e1] at e2
  exact hn (congrArg TailSh.cfF (Option.some.inj e2)).symm

/-- Where the shape bears no record of the smallness test (a.tl = none) the step refuses. At a
state's shape that is so between links, and also wherever S.tl? is none: in the head's link before
it is opened, and at every place that is no link. -/
theorem drawG_between (p : Par) (n : Nat) (a : ChainSh) (h : a.tl = none) :
    drawG p n a = .error "the draw: no link is open" := by
  unfold drawG
  rw [h]

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.drawOf_sh
#print axioms VerifiableInference.Desc.First.K8.drawGuard_sh
#print axioms VerifiableInference.Desc.First.K8.tl_sh
#print axioms VerifiableInference.Desc.First.K8.draw_carries
#print axioms VerifiableInference.Desc.First.K8.draw_returns
#print axioms VerifiableInference.Desc.First.K8.draw_carriesR
#print axioms VerifiableInference.Desc.First.K8.draw_returnsR
#print axioms VerifiableInference.Desc.First.K8.draw_no_round
#print axioms VerifiableInference.Desc.First.K8.draw_count_matters
#print axioms VerifiableInference.Desc.First.K8.drawG_between
#print axioms VerifiableInference.Desc.First.K8.drawOf
#print axioms VerifiableInference.Desc.First.K8.drawGuard
#print axioms VerifiableInference.Desc.First.K8.drawTl
#print axioms VerifiableInference.Desc.First.K8.drawG
