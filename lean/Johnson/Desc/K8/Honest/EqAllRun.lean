-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/EqAllRun.lean: THE SMALLNESS TEST: WHAT ITS RUN OF CLAIMS "K8.equations" OWES
ON SHAPES (RunLaw, Johnson/Desc/First/Batch/Shape/ClaimShape.lean): the run on shapes as one term,
its premises by name, and the law. General laws: nothing is evaluated.

  eqClaimsG a t   THE CLAIMS' SHAPES, as a term in the shape in front (a) and the shape behind (t):
                  the keys' claim, the counts' claims and the ties (allClaimsU,
                  Johnson/Desc/K8/Honest/EqAllUpdate.lean), then the reads' (readsSh,
                  Johnson/Desc/K8/Honest/EqAllReads.lean).
  eqRunG n a      THE RUN ON SHAPES: the step on the chain's shape (eqG,
                  Johnson/Desc/K8/Honest/EqAllChain.lean), then eqClaimsG at the shape in front and
                  the step's value. A function of the number that the gatherer hands the run and the
                  chain's shape alone.
  EqPre s         THE RUN's PREMISES ON THE STATE: its three tests on values, at the state's own
                  parts: the tables' weights are held; the coefficients on the smallness test's
                  window of slots are 0; the live columns' condition on the batching element.
  **eqRun_follows**   where eqRunG returns y at the state's shape and EqPre holds, the run returns,
                  and y is its claims' shapes and the state's shape behind.
  eqRunLaw        the RunLaw: runG := eqRunG; pre := EqPre.

Limits. One direction alone: FROM A RETURN OF THE RUN NOTHING IS CONCLUDED WITHOUT EqPre: "a return
of the run gives its premises" is owed. That eqRunG returns at a shape which the chain reaches is
not shown here. Who pays EqPre is not said. Where no part is read EqPre holds and says nothing; in
eqRun_follows the step's return supplies the part. No law says that eqRunG's second refusal is out
of reach behind eqG's return. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.K8.Honest.EqAllChain
import Johnson.Desc.First.Batch.Shape.ClaimShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law (St Ret partOf sits_equations)
open VerifiableInference.Desc.First.Shape
open OnBytes.Tie.Pv.Tail.Port (readsList)

/-- The claims' shapes, of the shape in front (a) and the shape behind (t). -/
def eqClaimsG (a t : ChainSh) : Option (List ClaimSh) :=
  match a.tl, a.tables, t.tl, t.led with
  | some t0, some fs, some t1, some L1 =>
    t0.heard.bind fun g =>
      (readsSh t0.blank t1.blank (ledBlank L1) 0
        (readsList t0.blank ((fs.map FunSh.blank).toArray))).map fun reads =>
          allClaimsU t0 t1 g ++ reads
  | _, _, _, _ => none

/-- **THE RUN ON SHAPES**: the step on the chain's shape (eqG), then the claims' shapes as a term in
the shape in front and the step's value. -/
def eqRunG (n : Nat) (a : ChainSh) : Except String (List ClaimSh × ChainSh) :=
  (eqG n a).bind fun t =>
    match eqClaimsG a t with
    | some cs => .ok (cs, t)
    | none => .error "K8.equations: the claims' shapes cannot be said"

/-- **The run's premises on the state**: its three tests on values, at the state's own parts. WHERE
NO PART IS READ (partOf s = none) IT HOLDS AND SAYS NOTHING: "EqPre s" does not say that the three
tests pass at s unless a part is there. -/
def EqPre (s : S) : Prop :=
  ∀ q, partOf s = some q → q.tl.funsHeld q.funs = true ∧
    (q.F.LS.extract q.tl.slotA q.tl.slotB).all isZeroE = true ∧ LiveCols q.tl q.funs q.F.theta

/-- **Where the run on shapes returns y and the three tests on values hold, the run returns, and y
is its claims' shapes and the shape behind.** -/
theorem eqRun_follows (p : K8.ParW) (run : Nat → S → Except String (List Claim × S))
    (hrun : ("K8.equations", run) ∈ (K8.whole p).claims) (n : Nat) (s : S)
    (y : List ClaimSh × ChainSh) (hg : eqRunG n (chainSh s) = .ok y) (hp : EqPre s) :
    ∃ cs s', run n s = .ok (cs, s') ∧ y = (cs.map claimSh, chainSh s') := by
  unfold eqRunG at hg
  cases ht : eqG n (chainSh s) with
  | error e =>
    rw [ht] at hg
    cases hg
  | ok t =>
    rw [ht] at hg
    have hg' : (match eqClaimsG (chainSh s) t with
      | some cs => (.ok (cs, t) : Except String (List ClaimSh × ChainSh))
      | none => .error "K8.equations: the claims' shapes cannot be said") = .ok y := hg
    -- the part is read, since the step returned
    have hq : ∃ q, partOf s = some q := by
      refine part_of_sh ?_
      unfold eqG at ht
      unfold ChainSh.funs
      cases h1 : (chainSh s).tl <;> cases h2 : (chainSh s).led <;>
        cases h3 : (chainSh s).tables <;> rw [h1, h2, h3] at ht <;> first | cases ht | rfl
    obtain ⟨q, hq⟩ := hq
    obtain ⟨v1, v2, v3⟩ := hp q hq
    obtain ⟨cls, s', hr, hs, g, out, F', e1, e2, e3, reads, e4, e5⟩ :=
      equations_chain p run hrun n s q hq ht v1 v2 v3
    obtain ⟨a1, -, a3, -⟩ := part_sh hq
    have hc : eqClaimsG (chainSh s) t = some (cls.map claimSh) := by
      unfold eqClaimsG
      rw [← hs, a1, a3, e2, e3]
      have hh : (tailSh q.tl).heard = some (heardAll g) := by
        show q.tl.heard.map heardAll = _
        rw [e1]
        rfl
      show ((tailSh q.tl).heard.bind fun g =>
        (readsSh (tailSh q.tl).blank (tailSh out).blank (ledBlank (ledSh F')) 0
          (readsList (tailSh q.tl).blank (eFs q.funs))).map fun reads =>
            allClaimsU (tailSh q.tl) (tailSh out) g ++ reads) = _
      rw [hh, e4, e5]
      rfl
    rw [hc] at hg'
    exact ⟨cls, s', hr, by rw [← Except.ok.inj hg', hs]⟩

/-- **What the run "K8.equations" owes on shapes** (RunLaw,
Johnson/Desc/First/Batch/Shape/ClaimShape.lean): runG := eqRunG; pre := EqPre. -/
def eqRunLaw (p : K8.ParW) (run : Nat → S → Except String (List Claim × S))
    (hrun : ("K8.equations", run) ∈ (K8.whole p).claims) : K9.Shape.RunLaw run where
  runG := eqRunG
  pre := fun _ s => EqPre s
  carries := fun n s s' cs y hp hr hg => by
    obtain ⟨cs', s'', e, hy⟩ := eqRun_follows p run hrun n s y hg hp
    rw [hr] at e
    cases e
    exact hy
  returns := fun n s y hg hp => by
    obtain ⟨cs', s'', e, -⟩ := eqRun_follows p run hrun n s y hg hp
    exact ⟨_, e⟩

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.eqRun_follows
#print axioms VerifiableInference.Desc.First.K8.Honest.eqRunLaw
#print axioms VerifiableInference.Desc.First.K8.Honest.eqClaimsG
#print axioms VerifiableInference.Desc.First.K8.Honest.eqRunG
#print axioms VerifiableInference.Desc.First.K8.Honest.EqPre
