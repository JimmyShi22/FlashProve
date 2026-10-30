-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/FallAfter.lean: BETWEEN THE ADDING AND THE SMALLNESS TEST's OWN TESTS NOTHING TURNS
WHAT `selfUnits` READS, AT A FEED-FORWARD SEGMENT. Statements and proofs. No prover.

The count of Johnson/Desc/K8/Honest/FallCount.lean asks `selfUnits`' "no" (`zeroUnitAt`) right behind the
batching block. The verifier asks `selfUnits` later: the frame's block behind the batching runs the
segment's tests, which cannot write, then "K8.lsTail", "free-slot" and "K8.tests"
(Johnson/Desc/Block.lean: Link.runBehind; Johnson/Desc/First/Driver/Chain.lean: orderAfterOf).

  `afterAll`, `afterIn_eq`, `after_ok`   the runs behind the batching, one by one
  `tl_putTl`, `fork_putTl`, `zeroUnitAt_eq`
  `zeroUnitAt_lsTail`   "K8.lsTail" leaves `zeroUnitAt`
  `zeroUnitAt_wrote`    so does a run that lays the ledger back as it was ("free-slot")
  `zeroUnitAt_tests`    a yes of "K8.tests" says that `zeroUnitAt` is false in front of it
  **`behind_layers`**   a yes of the frame's block behind the batching says that `zeroUnitAt` is false at
      the state behind the batching block: so where it is true there, the verifier refuses
WHICH RUN STANDS AT WHICH ENTRY IS A PREMISE, up to a guard: `LayersTies`
(Johnson/Desc/First/Link/Law/PayLayers.lean).
Limits. One direction: from a yes. That the verifier says yes where `zeroUnitAt` is false is not said:
the block asks much else. At a feed-forward segment alone.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.FallFold
import Johnson.Desc.K8.Honest.FallDraw
import Johnson.Desc.First.Link.Law.PayLayers
import Johnson.Desc.First.K4.RunsAtC
import Johnson.Desc.First.TailClaims.EquationsSelf
import Johnson.Desc.First.Driver.Chain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open OnBytes.Desc.First.K4 (Wrote)

/-! ## The runs behind the batching, one by one -/

section
variable {T Cl : Type}

/-- One run behind the batching, as an order names it. -/
def afterStep (bs : List (Block T Cl)) (x : T) (o : Nat × String) : Except String T :=
  (named (o.2 ++ ": no such run") ((bs[o.1]?).bind fun b => b.after.lookup o.2)).bind fun run =>
    match run x with
    | .ok y => .ok y
    | .error e => .error (o.2 ++ ": " ++ e)

/-- The runs of an order, one after the other. -/
def afterAll (bs : List (Block T Cl)) : List (Nat × String) → T → Except String T
  | [], x => .ok x
  | o :: os, x => (afterStep bs x o).bind (afterAll bs os)

theorem afterFold_eq (bs : List (Block T Cl)) : ∀ (os : List (Nat × String))
    (acc : Except String T),
    os.foldl (fun acc o => acc.bind fun x => afterStep bs x o) acc = acc.bind (afterAll bs os)
  | [], acc => by cases acc <;> rfl
  | o :: os, acc => by
    rw [List.foldl_cons, afterFold_eq bs os]
    cases acc <;> rfl

theorem afterIn_eq (bs : List (Block T Cl)) (order : List (Nat × String)) (s : T) :
    afterIn bs order s = afterAll bs order s :=
  afterFold_eq bs order (.ok s)

theorem after_ok {bs : List (Block T Cl)} {x z : T} {o : Nat × String}
    (h : afterStep bs x o = .ok z) :
    ∃ run, ((bs[o.1]?).bind fun b => b.after.lookup o.2) = some run ∧ run x = .ok z := by
  unfold afterStep at h
  cases hl : ((bs[o.1]?).bind fun b => b.after.lookup o.2) with
  | none =>
    rw [hl] at h
    exact absurd h (by simp [named, Except.bind])
  | some run =>
    rw [hl] at h
    simp only [named, Except.bind] at h
    split at h
    · rename_i y hy
      exact ⟨run, rfl, by rw [hy, Except.ok.inj h]⟩
    · exact absurd h (by simp)

end

/-! ## What the three runs leave -/

theorem tl_putTl (e : S) (tl tl' : HTailF2) (h : e.tl? = some tl) : (e.putTl tl').tl? = some tl' := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := e
  cases here with
  | lay x => rfl
  | att x => rfl
  | head x =>
    by_cases ho : x.opened = true
    · simp [S.putTl, S.tl?, ho]
    · simp [S.tl?, ho] at h
  | between => simp [S.tl?] at h
  | fin x => simp [S.tl?] at h
  | mem x => simp [S.tl?] at h

theorem fork_putTl (e : S) (tl' : HTailF2) : (e.putTl tl').fork? = e.fork? := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := e
  cases here with
  | lay x => rfl
  | att x => rfl
  | head x =>
    by_cases ho : x.opened = true
    · simp [S.putTl, S.fork?, ho]
    · simp [S.putTl, S.fork?, ho]
  | between => rfl
  | fin x => rfl
  | mem x => rfl

theorem zeroUnitAt_eq (nU : Array Nat) (s : S) (tl : HTailF2) (F : Fork) (h1 : s.tl? = some tl)
    (h2 : s.fork? = some F) : zeroUnitAt nU s = zeroUnit tl nU F := by
  unfold zeroUnitAt
  rw [(tlFork_iff s tl F).2 ⟨h1, h2⟩]

/-- "K8.lsTail" leaves the test's answer. -/
theorem zeroUnitAt_lsTail (nU : Array Nat) (e e₁ : S) (h : K9L.k8LsTail e = .ok e₁) :
    zeroUnitAt nU e₁ = zeroUnitAt nU e := by
  obtain ⟨F, tl, hF, htl, rfl⟩ := K9L.k8LsTail_ok e e₁ h
  rw [zeroUnitAt_eq nU e tl F htl hF,
    zeroUnitAt_eq nU _ _ F (tl_putTl e tl _ htl) (by rw [fork_putTl]; exact hF)]
  rfl

/-- A run that lays the ledger back as it was leaves the test's answer. -/
theorem zeroUnitAt_wrote (nU : Array Nat) (e e₁ : S) (a : LayOwn) (h : Wrote e a a.F e₁) :
    zeroUnitAt nU e₁ = zeroUnitAt nU e := by
  obtain ⟨h1, h2⟩ := h
  have h3 : e₁.here = .lay { a with F := a.F } := by rw [h2]
  rw [zeroUnitAt_eq nU e a.tl a.F (lay_tl e a h1) (lay_fork e a h1),
    zeroUnitAt_eq nU e₁ a.tl a.F (lay_tl e₁ _ h3) (lay_fork e₁ _ h3)]

/-- A yes of "K8.tests": in front of it the test's answer is "no weight is 0". -/
theorem zeroUnitAt_tests (nU : Array Nat) (e e₁ : S) (h : K9L.k8Tests nU e = .ok e₁) :
    zeroUnitAt nU e = false := by
  obtain ⟨F, tl, g, hF, htl, -, hself, -, -⟩ := K9L.k8Tests_ok nU e e₁ h
  have h2 := (Law.self_all tl nU F hself).2.1
  simp only [Bool.and_eq_true] at h2
  rw [zeroUnitAt_eq nU e tl F htl hF]
  unfold zeroUnit
  rw [h2.1.1.1.1]
  rfl

/-- **A yes of the frame's block behind the batching, at a feed-forward segment: no entry of the
vector of reads had the weight 0 behind the batching block.** -/
theorem behind_layers (L : Link S Claim) (p4 : OnBytes.Desc.First.K4.Par) (nU : Array Nat)
    (ties : LinkJoin.LayersTies L p4 nU) (hord : L.orderAfter = orderAfterOf .layers) (t t' : S)
    (h : L.runBehind t = .ok t') : zeroUnitAt nU t = false := by
  unfold Link.runBehind at h
  split at h
  · rw [hord, afterIn_eq] at h
    have ho3 : orderAfterOf .layers = [(4, "K8.lsTail"), (2, "free-slot"), (4, "K8.tests")] := rfl
    rw [ho3] at h
    simp only [afterAll] at h
    obtain ⟨z1, g1, h⟩ := bind_ok h
    obtain ⟨z2, g2, h⟩ := bind_ok h
    obtain ⟨z3, g3, h⟩ := bind_ok h
    obtain ⟨r1, a1, y1⟩ := after_ok g1
    obtain ⟨r2, a2, y2⟩ := after_ok g2
    obtain ⟨r3, a3, y3⟩ := after_ok g3
    have e1 := zeroUnitAt_lsTail nU t z1 (ties.tLs r1 a1 _ _ y1)
    obtain ⟨q2, l2, u2⟩ := ties.tFree r2 a2
    obtain ⟨a, w2⟩ := OnBytes.Desc.First.K4.freeSlotAtS l2 (u2 _ _ y2)
    have e2 := zeroUnitAt_wrote nU z1 z2 a w2
    have e3 := zeroUnitAt_tests nU z2 z3 (ties.tTests r3 a3 _ _ y3)
    rw [← e1, ← e2, e3]
  · exact absurd h (by simp)

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.zeroUnitAt_lsTail
#print axioms VerifiableInference.Desc.First.K8.Honest.zeroUnitAt_wrote
#print axioms VerifiableInference.Desc.First.K8.Honest.zeroUnitAt_tests
#print axioms VerifiableInference.Desc.First.K8.Honest.behind_layers
