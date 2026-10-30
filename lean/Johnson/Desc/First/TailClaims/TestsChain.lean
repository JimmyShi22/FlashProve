-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/TailClaims/TestsChain.lean: the smallness test's two runs behind the batching,
"K8.lsTail" and "K8.tests", as its sub-protocol states them (K8.whole,
Johnson/Desc/First/K8/Whole.lean), against the shape of the first chain's state (chainSh,
Johnson/Desc/First/Shape/Chain.lean): for each run ONE STEP ON THE SHAPE, and two laws. General
laws; nothing is evaluated.

The two laws, for a run f : S → Except String S, a step g on shapes and a test v on values:
  "carries": f s = .ok s' and g (chainSh s) = .ok t give t = chainSh s'.
  "returns": g (chainSh s) = .ok t and v s = true give an s' with f s = .ok s'.

  `partB a`: the shape says that a link is open: the smallness test's structure, the ledger and the
    list of tables are there. `part_there`: then the state's part is read (part_of_sh, Chain.lean).
  `lsTailG`: where partB accepts: the size of the kept coefficients is laid: as many as the ledger
    has between the test's own two slot numbers. **`lsTail_carries`**, **`lsTail_returns`** (no test
    on values).
  `testsGC nU`: where partB accepts: testsG (Johnson/Desc/First/TailClaims/TestsShape.lean) at the
    two components; its return is laid as the ledger's shape. `valsS nU`: the named tests on values,
    at the state's part. **`testsC_carries`**, **`testsC_returns`**.

What the runs are at the state is the library's sits_lsTail and sits_tests
(Johnson/Desc/First/TailClaims/K8Sits.lean).

Limits. That either step on shapes returns at a shape of the protocol is not shown. That a
description's seat lays these runs, and in which member's decision they are called, is not said
here. "Carries" takes the step's return as a premise: that the step returns wherever the run accepts
is not stated here. The refusals' words "no link is open" also cover an open link whose list of
tables is not laid yet. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.TailClaims.TestsShape
import Johnson.Desc.First.TailClaims.K8Sits
import Johnson.Desc.First.Shape.Chain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims.Law.Tests
open OnBytes OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law (partOf sits_lsTail sits_tests)
open VerifiableInference.Desc.First.Shape (LedSh ledSh TailSh tailSh ChainSh chainSh chainSh_k8set
  part_sh part_of_sh)

/-! ## 1 The part -/

/-- The shape says that a link is open and its list of tables is laid. -/
def partB (a : ChainSh) : Bool := a.tl.isSome && a.led.isSome && a.funs

theorem part_there {s : S} (h : partB (chainSh s) = true) : ∃ q, partOf s = some q :=
  part_of_sh h

theorem partB_of {s : S} {q : K8Part} (h : partOf s = some q) : partB (chainSh s) = true := by
  obtain ⟨h1, h2, -, h3⟩ := part_sh h
  simp [partB, h1, h2, h3]

theorem setTl_same {a : ChainSh} {t : TailSh} (h : a.tl = some t) : a.setTl t = a := by
  obtain ⟨m, n, tl, led, rest⟩ := a
  have h' : tl = some t := h
  subst h'
  rfl

theorem setLed_same {a : ChainSh} {L : LedSh} (h : a.led = some L) : a.setLed L = a := by
  obtain ⟨m, n, tl, led, rest⟩ := a
  have h' : led = some L := h
  subst h'
  rfl

theorem led_setTl (a : ChainSh) (t : TailSh) : (a.setTl t).led = a.led := rfl

/-! ## 2 "K8.lsTail" -/

/-- The update: the size of the kept coefficients. Where the structure or the ledger is missing: the
shape as it is (lsTailG asks partB in front, so it never comes to that there). -/
def lsTailU (a : ChainSh) : ChainSh :=
  match a.tl, a.led with
  | some t, some L => a.setTl { t with lsTail := min t.slotB L.coefs - t.slotA }
  | _, _ => a

/-- **The step on the shape.** -/
def lsTailG (a : ChainSh) : Except String ChainSh :=
  if partB a then .ok (lsTailU a) else .error "K8.lsTail: no link is open"

theorem lsTail_sh {s : S} {q : K8Part} (h : partOf s = some q) :
    chainSh (k8PartP.set s
      { q with tl := { q.tl with lsTail := q.F.LS.extract q.tl.slotA q.tl.slotB } }) =
      lsTailU (chainSh s) := by
  obtain ⟨h1, h2, -⟩ := part_sh h
  rw [chainSh_k8set, setLed_same (by rw [led_setTl]; exact h2)]
  unfold lsTailU
  rw [h1, h2]
  show (chainSh s).setTl { tailSh q.tl with
    lsTail := (q.F.LS.extract q.tl.slotA q.tl.slotB).size } = _
  rw [Array.size_extract]
  rfl

theorem lsTail_carries (p : K8.ParW) (run : S → Except String S)
    (h : ("K8.lsTail", run) ∈ (K8.whole p).after) (s s' : S) (t : ChainSh)
    (hr : run s = .ok s') (hg : lsTailG (chainSh s) = .ok t) : t = chainSh s' := by
  obtain ⟨q, hq, rfl⟩ := (sits_lsTail p run h s s').1 hr
  unfold lsTailG at hg
  rw [if_pos (partB_of hq)] at hg
  rw [lsTail_sh hq]
  exact (Except.ok.inj hg).symm

theorem lsTail_returns (p : K8.ParW) (run : S → Except String S)
    (h : ("K8.lsTail", run) ∈ (K8.whole p).after) (s : S) (t : ChainSh)
    (hg : lsTailG (chainSh s) = .ok t) : ∃ s', run s = .ok s' := by
  unfold lsTailG at hg
  by_cases hb : partB (chainSh s) = true
  · obtain ⟨q, hq⟩ := part_there hb
    exact ⟨_, (sits_lsTail p run h s _).2 ⟨q, hq, rfl⟩⟩
  · rw [if_neg hb] at hg
    cases hg

/-! ## 3 "K8.tests" -/

/-- **The step on the shape.** -/
def testsGC (nU : Array Nat) (a : ChainSh) : Except String ChainSh :=
  match a.tl, a.led with
  | some t, some L =>
    if a.funs then (testsG nU t L).map a.setLed else .error "K8.tests: no link is open"
  | _, _ => .error "K8.tests: no link is open"

/-- The named tests on values, at the state's part. -/
def valsS (nU : Array Nat) (s : S) : Bool := (partOf s).any fun q => valsAt nU q.tl q.F

theorem testsGC_at {nU : Array Nat} {s : S} {q : K8Part} (h : partOf s = some q) :
    testsGC nU (chainSh s) = (testsG nU (tailSh q.tl) (ledSh q.F)).map (chainSh s).setLed := by
  obtain ⟨h1, h2, -, h3⟩ := part_sh h
  unfold testsGC
  rw [h1, h2]
  simp only [h3, if_true]

theorem tests_sh {s : S} {q : K8Part} (h : partOf s = some q) (Fc : Fork) :
    chainSh (k8PartP.set s { q with F := Fc }) = (chainSh s).setLed (ledSh Fc) := by
  rw [chainSh_k8set, setTl_same (part_sh h).1]

theorem testsC_carries (p : K8.ParW) (run : S → Except String S)
    (h : ("K8.tests", run) ∈ (K8.whole p).after) (s s' : S) (t : ChainSh)
    (hr : run s = .ok s') (hg : testsGC p.nU (chainSh s) = .ok t) : t = chainSh s' := by
  obtain ⟨q, Fc, hq, ht, rfl⟩ := (sits_tests p run h s s').1 hr
  rw [testsGC_at hq, tests_carries ht] at hg
  rw [tests_sh hq]
  exact (Except.ok.inj hg).symm

theorem testsC_returns (p : K8.ParW) (run : S → Except String S)
    (h : ("K8.tests", run) ∈ (K8.whole p).after) (s : S) (t : ChainSh)
    (hg : testsGC p.nU (chainSh s) = .ok t) (hv : valsS p.nU s = true) :
    ∃ s', run s = .ok s' := by
  unfold valsS at hv
  cases hq : partOf s with
  | none => rw [hq] at hv; cases hv
  | some q =>
    rw [hq] at hv
    have hv' : valsAt p.nU q.tl q.F = true := hv
    rw [testsGC_at hq] at hg
    cases hG : testsG p.nU (tailSh q.tl) (ledSh q.F) with
    | error e => rw [hG] at hg; cases hg
    | ok u =>
      obtain ⟨Fc, hF, -⟩ := tests_shape hG hv'
      exact ⟨_, (sits_tests p run h s _).2 ⟨q, Fc, hq, hF, rfl⟩⟩

end VerifiableInference.Desc.First.TailClaims.Law.Tests

#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.part_there
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.lsTail_carries
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.lsTail_returns
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.testsC_carries
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.testsC_returns
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.partB
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.partB_of
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.setTl_same
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.setLed_same
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.led_setTl
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.lsTailU
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.lsTailG
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.lsTail_sh
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.testsGC
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.valsS
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.testsGC_at
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.tests_sh
