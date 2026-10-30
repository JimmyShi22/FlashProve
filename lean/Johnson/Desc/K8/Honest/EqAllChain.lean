-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/EqAllChain.lean: THE SMALLNESS TEST: THE RUN OF CLAIMS THAT ITS BLOCK STATES
UNDER THE NAME "K8.equations", AT THE FIRST CHAIN's STATE, ON THE CHAIN's SHAPE
(Johnson/Desc/First/Shape/Chain.lean): one step with code on the shape, and the law. General laws:
nothing is evaluated.

  eqG front       THE STEP ON THE SHAPE: it refuses by name where no link is open, no list of tables
                  is laid or no record is heard; else the whole list's Bool (allB,
                  Johnson/Desc/K8/Honest/EqAllShape.lean), then the update (allRecU, allLedU,
                  Johnson/Desc/K8/Honest/EqAllUpdate.lean). front: the number that the gatherer
                  hands the run. It is a function of the chain's shape and that number alone.
  **equations_chain**   where the step returns t at the state's shape, and the three tests on
                  values pass at the state's own parts, the run returns; the state's shape behind
                  is t; ALL the claims' shapes are read off the shapes in front and behind
                  (allClaimsU; readsSh, Johnson/Desc/K8/Honest/EqAllReads.lean).
  equations_carries   a yes of the run, under the same: the step returned the shape behind.
Over eqAll_claims and the library's sits_equations (Johnson/Desc/First/TailClaims/K8Sits.lean).

Limits. One direction alone. equations_carries is weaker than "the run returns, the step returns:
the shapes agree": it takes the three tests on values besides. The letter p stands in hrun alone.
Nothing on the tests on values. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.K8.Honest.EqAllReads
import Johnson.Desc.First.Shape.Chain
import Johnson.Desc.First.TailClaims.K8Sits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law (St Ret partOf sits_equations)
open VerifiableInference.Desc.First.Shape
open OnBytes.Tie.Pv.Tail.Port (readsList)

/-- **THE STEP ON THE CHAIN's SHAPE.** -/
def eqG (front : Nat) (a : ChainSh) : Except String ChainSh :=
  match a.tl, a.led, a.tables with
  | some t, some L, some fs =>
    match t.heard with
    | some g =>
      if allB (L.claims + front) t fs L 0 then
        .ok ((a.setTl (allRecU (L.claims + front) 0 t fs L)).setLed (allLedU g L))
      else .error "K8.equations: the shape does not pass"
    | none => .error "K8.equations: no record is heard"
  | _, _, _ => .error "K8.equations: no link is open, or no list of tables is laid"

/-- **Where the step returns at the shapes and the three tests on values pass, the run returns, and
the state's shape behind is what the step returned.** -/
theorem equations_chain (p : K8.ParW) (run : Nat → S → Except String (List Claim × S))
    (hrun : ("K8.equations", run) ∈ (K8.whole p).claims) (front : Nat) (s : S) (q : K8Part)
    (hq : partOf s = some q) {t : ChainSh}
    (hg : eqG front (chainSh s) = .ok t)
    (v1 : q.tl.funsHeld q.funs = true)
    (v2 : (q.F.LS.extract q.tl.slotA q.tl.slotB).all isZeroE = true)
    (v3 : LiveCols q.tl q.funs q.F.theta) :
    ∃ cls s', run front s = .ok (cls, s') ∧ chainSh s' = t ∧
      ∃ g out F', q.tl.heard = some g ∧ (chainSh s').tl = some (tailSh out) ∧
        (chainSh s').led = some (ledSh F') ∧
        ∃ reads : List ClaimSh,
          readsSh (tailSh q.tl).blank (tailSh out).blank (ledBlank (ledSh F')) 0
            (readsList (tailSh q.tl).blank (eFs q.funs)) = some reads ∧
          cls.map claimSh = allClaimsU (tailSh q.tl) (tailSh out) (heardAll g) ++ reads := by
  obtain ⟨e1, e2, e3, -⟩ := part_sh hq
  unfold eqG at hg
  rw [e1, e2, e3] at hg
  dsimp only at hg
  cases hh : (tailSh q.tl).heard with
  | none =>
    rw [hh] at hg
    cases hg
  | some gs =>
    rw [hh] at hg
    dsimp only at hg
    by_cases hb : allB ((ledSh q.F).claims + front) (tailSh q.tl) (q.funs.toList.map funSh)
        (ledSh q.F) 0 = true
    · rw [if_pos hb] at hg
      obtain ⟨out, ⟨F', c⟩, e, hrec, g, hgq, hled, reads, hn, hcl⟩ :=
        eqAll_claims (front := q.F.nClaim + front) (cs := #[]) hb v1 v2 v3
      have egs : gs = heardAll g := by
        have : (tailSh q.tl).heard = some (heardAll g) := by
          show q.tl.heard.map heardAll = _
          rw [hgq]
          rfl
        rw [hh] at this
        exact Option.some.inj this
      have hs' : chainSh (k8PartP.set s { q with tl := out, F := F' }) = t := by
        rw [chainSh_k8set, ← Except.ok.inj hg, egs]
        dsimp only at hrec hled ⊢
        rw [hrec, hled]
        rfl
      refine ⟨c.toList, _, (sits_equations p run hrun front s _ _).2 ⟨q, out, F', hq, ?_, rfl⟩,
        hs', g, out, F', hgq, ?_, ?_, reads, hn, ?_⟩
      · unfold equations
        rw [e]
        rfl
      · rw [chainSh_k8set]
        show ((chainSh s).tl.map fun _ => tailSh out) = _
        rw [e1]
        rfl
      · rw [chainSh_k8set]
        show ((chainSh s).led.map fun _ => ledSh F') = _
        rw [e2]
        rfl
      · simpa using hcl
    · rw [if_neg hb] at hg
      cases hg

/-- A yes of the run, under the same: the step returned the shape behind. IT ASKS THE THREE TESTS ON
VALUES ON TOP OF THE RUN's OWN YES: that a return of the run gives them is owed (EqAllRun.lean's
Limits). -/
theorem equations_carries (p : K8.ParW) (run : Nat → S → Except String (List Claim × S))
    (hrun : ("K8.equations", run) ∈ (K8.whole p).claims) (front : Nat) (s s' : S) (q : K8Part)
    (cls : List Claim) (hq : partOf s = some q) {t : ChainSh}
    (hr : run front s = .ok (cls, s'))
    (hg : eqG front (chainSh s) = .ok t)
    (v1 : q.tl.funsHeld q.funs = true)
    (v2 : (q.F.LS.extract q.tl.slotA q.tl.slotB).all isZeroE = true)
    (v3 : LiveCols q.tl q.funs q.F.theta) : t = chainSh s' := by
  obtain ⟨cls', s'', e, h, -⟩ := equations_chain p run hrun front s q hq hg v1 v2 v3
  rw [hr] at e
  cases e
  exact h.symm

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.equations_chain
#print axioms VerifiableInference.Desc.First.K8.Honest.equations_carries
#print axioms VerifiableInference.Desc.First.K8.Honest.eqG
