-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/FallFold.lean: A YES OF A SEGMENT's FUNCTION OF CLAIMS, CUT RUN BY RUN; AND WHAT IS
READ OF THE FIRST CHAIN's STATE INSIDE A FEED-FORWARD SEGMENT. Statements and proofs, generic: no kind's
run is named. For Johnson/Desc/K8/Honest/FallLayers.lean's statement.

  `bind_ok`      a bind that returns
  `runAll`, `claimsInBy_eq`   the frame's gatherer (Johnson/Desc/Block.lean: claimsInBy) as a recursion
      over the order
  `step_ok`      one run of the gathering that returns: the run that the blocks state at the entry
      returned; its claims are laid behind those gathered so far
  `lay_*`        at a state that stands in a feed-forward segment: what fork?, tl?, funs?, lookHeard?
      and the batching's lens read; where putFork, putTl, putLink and the lens's writing leave it
  `SameSums F G`  G has F's arrays, slots' number, sums, count of claims, batching element and plan's
      number; `SameSums.core`, `SameSums.frame`; from the library's relations `Core` and `OnlySide`
Limits: from a yes alone.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.FallCount
import Johnson.Desc.First.K4.RunsCore
import Johnson.Desc.First.TailClaims.EquationsTame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims

/-! ## The gatherer, run by run -/

theorem bind_ok {α β : Type} {x : Except String α} {f : α → Except String β} {y : β}
    (h : x.bind f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => exact absurd h (by simp [Except.bind])
  | ok a => exact ⟨a, rfl, h⟩

section
variable {T Cl : Type}

/-- The runs of an order, one after the other, from what is gathered so far. -/
def runAll (each : Nat × String → List Cl → T → Except String Unit) (bs : List (Block T Cl)) :
    List (Nat × String) → List Cl × T → Except String (List Cl × T)
  | [], x => .ok x
  | o :: os, x => (claimsInStep each bs x o).bind (runAll each bs os)

theorem fold_eq (each : Nat × String → List Cl → T → Except String Unit)
    (bs : List (Block T Cl)) : ∀ (os : List (Nat × String)) (acc : Except String (List Cl × T)),
    os.foldl (fun acc o => acc.bind fun x => claimsInStep each bs x o) acc =
      acc.bind (runAll each bs os)
  | [], acc => by cases acc <;> rfl
  | o :: os, acc => by
    rw [List.foldl_cons, fold_eq each bs os]
    cases acc <;> rfl

theorem claimsInBy_eq (each : Nat × String → List Cl → T → Except String Unit)
    (bs : List (Block T Cl)) (order : List (Nat × String)) (s : T) :
    claimsInBy each bs order s = runAll each bs order ([], s) :=
  fold_eq each bs order (.ok ([], s))

theorem step_ok {each : Nat × String → List Cl → T → Except String Unit} {bs : List (Block T Cl)}
    {x z : List Cl × T} {o : Nat × String} (h : claimsInStep each bs x o = .ok z) :
    ∃ run c e, ((bs[o.1]?).bind fun b => b.claims.lookup o.2) = some run ∧
      run x.1.length x.2 = .ok (c, e) ∧ z = (x.1 ++ c, e) := by
  unfold claimsInStep at h
  cases hl : ((bs[o.1]?).bind fun b => b.claims.lookup o.2) with
  | none =>
    rw [hl] at h
    exact absurd h (by simp [named, Except.bind])
  | some run =>
    rw [hl] at h
    simp only [named, Except.bind] at h
    split at h
    · rename_i y hy
      split at h
      · exact ⟨run, y.1, y.2, rfl, hy, (Except.ok.inj h).symm⟩
      · exact absurd h (by simp)
    · exact absurd h (by simp)

end

/-! ## Inside a feed-forward segment -/

theorem lay_fork (t : S) (A : LayOwn) (h : t.here = .lay A) : t.fork? = some A.F := by
  unfold S.fork?
  rw [h]

theorem lay_tl (t : S) (A : LayOwn) (h : t.here = .lay A) : t.tl? = some A.tl := by
  unfold S.tl?
  rw [h]

theorem lay_funs (t : S) (A : LayOwn) (h : t.here = .lay A) :
    t.funs? = A.own.map (·.funs) := by
  unfold S.funs?
  rw [h]

theorem lay_look (t : S) (A : LayOwn) (h : t.here = .lay A) : t.lookHeard? = A.lookHeard := by
  unfold S.lookHeard?
  rw [h]

theorem lay_putFork (t : S) (A : LayOwn) (G : Fork) (h : t.here = .lay A) :
    (t.putFork G).here = .lay { A with F := G } := by
  unfold S.putFork
  rw [h]

theorem lay_putTl (t : S) (A : LayOwn) (tl : HTailF2) (h : t.here = .lay A) :
    (t.putTl tl).here = .lay { A with tl := tl } := by
  unfold S.putTl
  rw [h]

theorem lay_putLink (t : S) (A : LayOwn) (L : LinkCtx) (h : t.here = .lay A) :
    (t.putLink L).here = .lay { A with L := L } := by
  unfold S.putLink
  rw [h]

theorem lay_set (t : S) (A : LayOwn) (q : K9.Part) (h : t.here = .lay A) :
    (K9.atS.set t q).here = .lay { A with L := q.L, F := q.F } :=
  lay_putFork _ _ q.F (lay_putLink t A q.L h)

theorem lay_part (t : S) (A : LayOwn) (h : t.here = .lay A) :
    ∃ x, K9.atS.get? t = some x ∧ x.F = A.F := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := t
  dsimp only at h
  subst h
  exact ⟨_, rfl, rfl⟩

/-! ## What the runs leave of the ledger -/

/-- G has F's arrays, number of slots, coefficients on the slots, constant, count of claims,
batching element and plan's number of claims. -/
structure SameSums (F G : Fork) : Prop where
  trees : G.trees = F.trees
  ns : G.ns = F.ns
  LS : G.LS = F.LS
  c0 : G.c0 = F.c0
  nClaim : G.nClaim = F.nClaim
  theta : G.theta = F.theta
  plan : G.planClaimsF = F.planClaimsF

theorem SameSums.refl (F : Fork) : SameSums F F := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem SameSums.trans {F G H : Fork} (a : SameSums F G) (b : SameSums G H) : SameSums F H :=
  ⟨b.trees.trans a.trees, b.ns.trans a.ns, b.LS.trans a.LS, b.c0.trans a.c0,
    b.nClaim.trans a.nClaim, b.theta.trans a.theta, b.plan.trans a.plan⟩

theorem SameSums.ofCore {F G : Fork} (h : OnBytes.Desc.First.K4.Core F G) : SameSums F G :=
  ⟨h.trees, h.ns, h.LS, h.c0, h.nClaim, h.theta, h.planClaimsF⟩

theorem SameSums.ofSide {F G : Fork} (h : Law.OnlySide F G) : SameSums F G :=
  ⟨h.trees, h.ns, h.LS, h.c0, h.nClaim, h.theta, h.plan⟩

theorem SameSums.paid (F : Fork) (i : Nat) : SameSums F (F.paid i) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem SameSums.core {F G : Fork} (h : SameSums F G) : K9L.core G = K9L.core F := by
  simp only [K9L.core, K9L.sums, h.trees, h.ns, h.LS, h.c0, h.nClaim, h.theta, h.plan]

theorem SameSums.frame {F G : Fork} (h : SameSums F G) :
    treesFrame G.trees = treesFrame F.trees := by
  rw [h.trees]

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.claimsInBy_eq
#print axioms VerifiableInference.Desc.First.K8.Honest.step_ok
#print axioms VerifiableInference.Desc.First.K8.Honest.lay_set
#print axioms VerifiableInference.Desc.First.K8.Honest.lay_part
#print axioms VerifiableInference.Desc.First.K8.Honest.SameSums.core
