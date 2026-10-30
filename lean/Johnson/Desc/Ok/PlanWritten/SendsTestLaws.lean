-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ok/PlanWritten/SendsTestLaws.lean: what an accept and a reject of the tests on the
lists of sendings say (Johnson/Desc/Ok/PlanWritten/SendsTest.lean); that each has a member; the
written lists held against the library's two older written values; negative tests. A definition and
statements with their proofs.

  `sameSending_eq`, `sameSends_eq`, `sameChain_eq`, `sameThree_eq`: an accept of a comparison gives
    the equation of whole values: so no field and no sending is left out. `sameSending_self`,
    `sameSends_self`, `sameChain_self`, `sameThree_self`: each accepts a value and itself.
  `proofSends_of_is`, `proofSendsIs_of`, `proofSends_no`; `keySends_of_is`, `keySendsIs_of`,
    `keySends_no`; `sends_of_is`, `sendsIs_of`, `sends_no`: a test accepts just where the lists are
    the written ones; a reject says that a list differs.
  `sends_self`: the written lists pass.
  `litOfChain`; `written_lit`: of the chain, the entry's number and what is sent the new lists hold
    what the older written list holds (`sendsFullLit`, Johnson/G/SendsLit.lean), but for the copy's
    file's five sendings. `written_codes`: the codes are `codesFull0` and `codesFull2`
    (Johnson/G/PackLit.lean). `written_heads`, `written_seeds`: the files' names and the chains'
    numbers; every first entry bears the name "SEND seed".
  Negative tests, one a field: `reject_entry`, `reject_label`, `reject_sent`, `reject_seed`,
    `reject_behind`, `reject_shorter`, `reject_chain`, `reject_file`, `reject_codes`.
By evaluations in Lean's kernel (`decide +kernel`): the four statements `written_…`.

Limits. The labels and the two entries of a sending are held against no older written value: they
rest on one print of Lean's evaluator (the head of Johnson/G/SendsWritten.lean) and on one test by
evaluation at every build (Johnson/G/SendsWrittenGuard.lean: `sendsOf`'s lists at the full-size
example's files, as Johnson/G/KitFull.lean holds them, are the written ones, six lists of the seven:
the copy's file's list is not held). That the lists made at any public files pass is no theorem; at
other files it is the reference run's to show. Nothing on soundness.

-/
import Johnson.Desc.Ok.PlanWritten.SendsTest
import Johnson.G.SendsLit
import Johnson.G.PackLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten
open OnBytes Johnson.G

/-! ## An accept of a comparison is an equation of whole values -/

theorem sameSending_eq {a b : Sending} (h : sameSending a b = true) : a = b := by
  simp only [sameSending, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  cases a
  cases b
  simp only at h1 h2 h3 h4 h5
  subst h1 h2 h3 h4 h5
  rfl

theorem sameSends_eq : ∀ {l m : List Sending}, sameSends l m = true → l = m
  | [], [], _ => rfl
  | a :: l, b :: m, h => by
    simp only [sameSends, Bool.and_eq_true] at h
    rw [sameSending_eq h.1, sameSends_eq h.2]
  | [], _ :: _, h => by simp [sameSends] at h
  | _ :: _, [], h => by simp [sameSends] at h

theorem sameChain_eq {a b : ChainSends} (h : sameChain a b = true) : a = b := by
  simp only [sameChain, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have k4 := sameSends_eq h4
  cases a
  cases b
  simp only at h1 h2 h3 k4
  subst h1 h2 h3 k4
  rfl

theorem sameThree_eq {a b : ChainSends × ChainSends × ChainSends} (h : sameThree a b = true) :
    a = b := by
  simp only [sameThree, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact Prod.ext (sameChain_eq h1) (Prod.ext (sameChain_eq h2) (sameChain_eq h3))

theorem sameSending_self (a : Sending) : sameSending a a = true := by simp [sameSending]

theorem sameSends_self : ∀ l : List Sending, sameSends l l = true
  | [] => rfl
  | a :: l => by simp [sameSends, sameSending_self, sameSends_self l]

theorem sameChain_self (a : ChainSends) : sameChain a a = true := by
  simp [sameChain, sameSends_self]

theorem sameThree_self (a : ChainSends × ChainSends × ChainSends) : sameThree a a = true := by
  simp [sameThree, sameChain_self]

/-! ## The tests -/

/-- **An accept: the proof file's three lists are the written ones, whole.** -/
theorem proofSends_of_is {m : OfPlan.Made} (h : proofSendsIs m = true) :
    m.proof = proofSendsFull := sameThree_eq h

theorem proofSendsIs_of {m : OfPlan.Made} (h : m.proof = proofSendsFull) :
    proofSendsIs m = true := by
  unfold proofSendsIs
  rw [h]
  exact sameThree_self _

/-- What a reject says. -/
theorem proofSends_no {m : OfPlan.Made} (h : proofSendsIs m = false) :
    m.proof ≠ proofSendsFull := by
  intro e
  rw [proofSendsIs_of e] at h
  cases h

theorem keySends_of_is {m : OfPlan.Made} (h : keySendsIs m = true) : m.key = keySendsFull :=
  sameThree_eq h

theorem keySendsIs_of {m : OfPlan.Made} (h : m.key = keySendsFull) : keySendsIs m = true := by
  unfold keySendsIs
  rw [h]
  exact sameThree_self _

theorem keySends_no {m : OfPlan.Made} (h : keySendsIs m = false) : m.key ≠ keySendsFull := by
  intro e
  rw [keySendsIs_of e] at h
  cases h

theorem sends_of_is {m : OfPlan.Made} (h : sendsIs m = true) :
    m.key = keySendsFull ∧ m.proof = proofSendsFull := by
  unfold sendsIs at h
  rw [Bool.and_eq_true] at h
  exact ⟨keySends_of_is h.1, proofSends_of_is h.2⟩

theorem sendsIs_of {m : OfPlan.Made} (hk : m.key = keySendsFull)
    (hp : m.proof = proofSendsFull) : sendsIs m = true := by
  unfold sendsIs
  rw [keySendsIs_of hk, proofSendsIs_of hp]
  rfl

theorem sends_no {m : OfPlan.Made} (h : sendsIs m = false) :
    m.key ≠ keySendsFull ∨ m.proof ≠ proofSendsFull := by
  by_cases hk : m.key = keySendsFull
  · refine Or.inr fun hp => ?_
    rw [sendsIs_of hk hp] at h
    cases h
  · exact Or.inl hk

/-- The written lists pass, whatever stands beside them. -/
theorem sends_self (p : OnBytes.Model.Verify.Planned) :
    sendsIs ⟨p, keySendsFull, proofSendsFull⟩ = true := sendsIs_of rfl rfl

/-! ## The written lists against the library's two older written values -/

/-- A chain's sendings in the form of the older written list. n: the file's number there. -/
def litOfChain (n : Nat) (C : ChainSends) : List SendLit :=
  C.sends.map fun s => (n, C.chain, s.entry, s.sent)

/-- **The older written list, but for the copy's file's sendings, is what the new lists hold** of
the chain, the entry's number and what is sent. -/
theorem written_lit :
    (litOfChain 0 keySendsFull.1 ++ litOfChain 0 keySendsFull.2.1 ++
      litOfChain 0 keySendsFull.2.2 ++ litOfChain 2 proofSendsFull.1 ++
      litOfChain 2 proofSendsFull.2.1 ++ litOfChain 2 proofSendsFull.2.2) =
      sendsFullLit.filter (fun x => x.1 != 1) := by decide +kernel

/-- The chains' codes are the library's written codes of the two files. -/
theorem written_codes :
    ([keySendsFull.1.codes, keySendsFull.2.1.codes, keySendsFull.2.2.codes],
      [proofSendsFull.1.codes, proofSendsFull.2.1.codes, proofSendsFull.2.2.codes]) =
      ([codesFull0, codesFull0, codesFull0], [codesFull2, codesFull2, codesFull2]) := by
  decide +kernel

/-- The files' names, the chains' numbers, and how many sendings each has. -/
theorem written_heads :
    ([keySendsFull.1, keySendsFull.2.1, keySendsFull.2.2, proofSendsFull.1, proofSendsFull.2.1,
      proofSendsFull.2.2].map fun C => (C.file, C.chain)) =
      [("key", 0), ("key", 1), ("key", 2), ("proof", 0), ("proof", 1), ("proof", 2)] := by
  decide +kernel

/-- Every written sending's first entry bears the name "SEND seed". -/
theorem written_seeds :
    ([keySendsFull.1, keySendsFull.2.1, keySendsFull.2.2, proofSendsFull.1, proofSendsFull.2.1,
      proofSendsFull.2.2].all fun C => C.sends.all fun s => s.seed.name == "SEND seed") = true := by
  decide +kernel

/-! ## Negative tests: one a field; general in the value -/

theorem reject_entry (a : Sending) : sameSending a { a with entry := a.entry + 1 } = false := by
  cases h : sameSending a { a with entry := a.entry + 1 } with
  | false => rfl
  | true => exact absurd (congrArg Sending.entry (sameSending_eq h)) (by simp)

theorem reject_label (a : Sending) :
    sameSending a { a with label := a.label ++ "x" } = false := by
  cases h : sameSending a { a with label := a.label ++ "x" } with
  | false => rfl
  | true =>
    have e := congrArg (fun s : Sending => s.label.length) (sameSending_eq h)
    simp [String.length_append] at e

theorem reject_sent (a : Sending) (n : OracleNotice) :
    sameSending a { a with sent := n :: a.sent } = false := by
  cases h : sameSending a { a with sent := n :: a.sent } with
  | false => rfl
  | true =>
    exact absurd (congrArg (fun s : Sending => s.sent.length) (sameSending_eq h)) (by simp)

theorem reject_seed (a : Sending) :
    sameSending a { a with seed := { a.seed with roots := a.seed.roots + 1 } } = false := by
  cases h : sameSending a { a with seed := { a.seed with roots := a.seed.roots + 1 } } with
  | false => rfl
  | true =>
    exact absurd (congrArg (fun s : Sending => s.seed.roots) (sameSending_eq h)) (by simp)

theorem reject_behind (a : Sending) :
    sameSending a { a with behind := { a.behind with answers := a.behind.answers + 1 } } =
      false := by
  cases h : sameSending a { a with behind := { a.behind with answers := a.behind.answers + 1 } }
    with
  | false => rfl
  | true =>
    exact absurd (congrArg (fun s : Sending => s.behind.answers) (sameSending_eq h)) (by simp)

/-- A list that is one sending shorter is rejected, on either side. -/
theorem reject_shorter (a : Sending) (l : List Sending) :
    sameSends (a :: l) l = false ∧ sameSends l (a :: l) = false := by
  constructor
  · cases h : sameSends (a :: l) l with
    | false => rfl
    | true => exact absurd (congrArg List.length (sameSends_eq h)) (by simp)
  · cases h : sameSends l (a :: l) with
    | false => rfl
    | true => exact absurd (congrArg List.length (sameSends_eq h)) (by simp)

theorem reject_chain (C : ChainSends) : sameChain C { C with chain := C.chain + 1 } = false := by
  cases h : sameChain C { C with chain := C.chain + 1 } with
  | false => rfl
  | true => exact absurd (congrArg ChainSends.chain (sameChain_eq h)) (by simp)

theorem reject_file (C : ChainSends) : sameChain C { C with file := C.file ++ "x" } = false := by
  cases h : sameChain C { C with file := C.file ++ "x" } with
  | false => rfl
  | true =>
    have e := congrArg (fun c : ChainSends => c.file.length) (sameChain_eq h)
    simp [String.length_append] at e

theorem reject_codes (C : ChainSends) (c : Code) :
    sameChain C { C with codes := { C.codes with base := C.codes.base.push c } } = false := by
  cases h : sameChain C { C with codes := { C.codes with base := C.codes.base.push c } } with
  | false => rfl
  | true =>
    exact absurd (congrArg (fun c : ChainSends => c.codes.base.size) (sameChain_eq h)) (by simp)

end VerifiableInference.PlanWritten

#print axioms VerifiableInference.PlanWritten.sameSending_eq
#print axioms VerifiableInference.PlanWritten.sameSends_eq
#print axioms VerifiableInference.PlanWritten.sameChain_eq
#print axioms VerifiableInference.PlanWritten.sameThree_eq
#print axioms VerifiableInference.PlanWritten.sameSending_self
#print axioms VerifiableInference.PlanWritten.sameSends_self
#print axioms VerifiableInference.PlanWritten.sameChain_self
#print axioms VerifiableInference.PlanWritten.sameThree_self
#print axioms VerifiableInference.PlanWritten.proofSends_of_is
#print axioms VerifiableInference.PlanWritten.proofSendsIs_of
#print axioms VerifiableInference.PlanWritten.proofSends_no
#print axioms VerifiableInference.PlanWritten.keySends_of_is
#print axioms VerifiableInference.PlanWritten.keySendsIs_of
#print axioms VerifiableInference.PlanWritten.keySends_no
#print axioms VerifiableInference.PlanWritten.sends_of_is
#print axioms VerifiableInference.PlanWritten.sendsIs_of
#print axioms VerifiableInference.PlanWritten.sends_no
#print axioms VerifiableInference.PlanWritten.sends_self
#print axioms VerifiableInference.PlanWritten.written_lit
#print axioms VerifiableInference.PlanWritten.written_codes
#print axioms VerifiableInference.PlanWritten.written_heads
#print axioms VerifiableInference.PlanWritten.written_seeds
#print axioms VerifiableInference.PlanWritten.reject_entry
#print axioms VerifiableInference.PlanWritten.reject_label
#print axioms VerifiableInference.PlanWritten.reject_sent
#print axioms VerifiableInference.PlanWritten.reject_seed
#print axioms VerifiableInference.PlanWritten.reject_behind
#print axioms VerifiableInference.PlanWritten.reject_shorter
#print axioms VerifiableInference.PlanWritten.reject_chain
#print axioms VerifiableInference.PlanWritten.reject_file
#print axioms VerifiableInference.PlanWritten.reject_codes
