-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Ok/PlanWritten/Row.lean: over Johnson/Desc/Ok/PlanWritten/Rounds.lean: (1) WHAT OF THE
PLANNER's VALUE DOES NOT HANG ON THE DIGEST OF THE PUBLIC FILES: the sizes and codes, the seven
plans, the public part, the links, the sendings, the seven chains as read back but for the digest
and the bytes, the declared rounds and the depth are the same at every digest of 32 bytes; (2) a
general form, with code, for a test that holds one field of what the planner makes against a written
value, at one anchor, with the step to every digest; (3) a ride of many such tests with one call of
the planner.

ROW OR TOOL. EVERY DECLARATION HERE IS A TOOL AT THE PLANNER: rules for all files, all m, all
fields. None speaks of a description of the protocol.

Why. A description that is to name no hash by itself takes the digest of the public files as an
argument. Then whatever it takes of the planner's value must be shown not to hang on that argument,
or be tied to it. `madeOfAt` (Johnson/Desc/Ok/NumberPrices/AtDigest.lean) has the digest as a letter
c; `atDigest m c` is m put at c.

Definitions, statements and proofs.
  `kept_atDigest`: `atDigest m c` has m's sizes and codes (`made.sized`), m's lists of plans of the
    proof file and of the key file and the plan of the entry file, m's public part X, m's links and
    m's six sendings. By definition: `chainsAtCfg` (OnBytes/Tie/ChainsAtCfg.lean) turns the digest
    and the seven strings of parameter bytes in `made`, and each chain as read back is put at c.
    `ReadKept m' m`, `readKept_atDigest`: OF THE SEVEN CHAINS AS READ BACK: of each the plan, the
    items, and every field beside what was read of its parameter bytes (`given`) are kept: `atCfg`
    (OnBytes/Params/ReadBackAt.lean) turns the digest and the bytes in `given` alone. By definition.
    These are the plans that `declKOf` and `declPOf` read (six of the seven).
  `ChainsKept`, `chains_kept`: THE CLOSED RULE and its proof: for all files and all c, c' of 32
    bytes: where `madeOfAt` returns m at c, with short strings, and m' at c', eight fields of m' are
    m's (`kept_atDigest`'s), `ReadKept m' m` holds, and `declKOf`, `declPOf`, `roundsAt` and
    `depthOf` return at m' what they return at m (Johnson/Desc/Ok/PlanWritten/Rounds.lean).
  `Kept f`: a function f of what was made does not hang on the digest: `f (atDigest m c) = f m` for
    all m, c. `FieldIs f w pol lay KL`: at every c of 32 bytes `madeOfAt` returns an m with `f m =
    w`. A statement with free letters.
  `fieldOk f w pol lay KL`: THE TEST, with code: at 32 zero bytes in the digest's place all is made,
    the seven strings are short, and f of it is w, by a decidable equality. `anchor_of_fieldOk`,
    `fieldOk_of_made`: what a yes says at the anchor, both ways. `fieldIs_of_ok`: for a kept f a yes
    gives `FieldIs f w`. `fieldIs_unique`, `fieldOk_unique`: one value at most: so beside a yes at w
    the test says no at every other value: A PLANT IS REFUSED. `not_fieldIs_of_no`: where all is
    made with short strings and the test says no, `FieldIs f w` is false.
  `madeShort`, `fieldLines`, `rideFields note tests pol lay KL`: FOR A RUN: with ONE call of the
    planner: a first line (all is made, the strings are short), then a line for each named test on
    m. `of_rideFields`: what a true first line and a true line of a test give.

What of OnBytes/Model/ and OnBytes/Tie/ is used. Named: `Tie.shortB`; fields of
`Model.Verify.Planned`. Called: `Tie.short_of_test`. Through `madeOfAt`: `Tie.plannedAt`.

Limits. NOT KEPT: the digest itself (in `p.cfg`, in `made.configuration` and in each chain's
`given.cfg`) and the seven strings of parameter bytes (in `made` and in each chain's `given.bytes`).
All other fields of what was made are stated as kept. THE SECOND HASH FUNCTION: `madeOfAt` calls it
by name (`publicOf`); nothing here says what hangs on it. f AND THE TESTS OF A RIDE ARE FREE
LETTERS: a line can say true of what the planner did not make, if its f hides a refusal behind a
default or its test does not ask what its label says: a label is a string that nothing binds to its
test. Each instance's f and test are to be read: a projection, or a value in `Except` held against
`.ok w`; no default. No theorem here leads from a ride's true line to `FieldIs`: each instance has
to make that step (`of_rideFields`, then `fieldOk_of_made` or the like). `fieldOk_unique` says that
a plant is refused BESIDE A YES alone. That `madeOfAt` returns anywhere, with short strings, is a
run's to show: where it refuses `ChainsKept` says nothing. No written value of a field is laid here,
and no test here was run by anybody known to this file. A yes of `fieldOk` is evidence and no proof;
it would be a check of copying against this library's own planner, no second witness. Nothing at a c
that has not 32 bytes. Nothing on soundness.


-/
import Johnson.Desc.Ok.PlanWritten.Rounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten
open Johnson.G Johnson.G.OfPlan VerifiableInference.Number
open OnBytes.Tie (shortB short_of_test)

/-! ## What does not hang on the digest -/

/-- **m put at c has m's sizes and codes, seven plans, public part, links and sendings.** By
definition. -/
theorem kept_atDigest (m : Made) (c : ByteArray) :
    (atDigest m c).p.chains.made.sized = m.p.chains.made.sized ∧
      (atDigest m c).p.chains.made.proof = m.p.chains.made.proof ∧
      (atDigest m c).p.chains.made.key = m.p.chains.made.key ∧
      (atDigest m c).p.chains.made.entry = m.p.chains.made.entry ∧
      (atDigest m c).p.X = m.p.X ∧ (atDigest m c).p.built = m.p.built ∧
      (atDigest m c).key = m.key ∧ (atDigest m c).proof = m.proof :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Of the seven chains as read back, m' has what m has, but for the digest and the bytes**: of
each chain: the plan, the items, and every field beside what was read of its parameter bytes. -/
def ReadKept (m' m : Made) : Prop :=
  (m'.p.chains.key.oneTime.given.plan = m.p.chains.key.oneTime.given.plan ∧
      m'.p.chains.key.oneTime.given.items = m.p.chains.key.oneTime.given.items ∧
      { m'.p.chains.key.oneTime with given := m.p.chains.key.oneTime.given } =
        m.p.chains.key.oneTime) ∧
    (m'.p.chains.key.shared.given.plan = m.p.chains.key.shared.given.plan ∧
      m'.p.chains.key.shared.given.items = m.p.chains.key.shared.given.items ∧
      { m'.p.chains.key.shared with given := m.p.chains.key.shared.given } =
        m.p.chains.key.shared) ∧
    (m'.p.chains.key.second.given.plan = m.p.chains.key.second.given.plan ∧
      m'.p.chains.key.second.given.items = m.p.chains.key.second.given.items ∧
      { m'.p.chains.key.second with given := m.p.chains.key.second.given } =
        m.p.chains.key.second) ∧
    (m'.p.chains.link.given.plan = m.p.chains.link.given.plan ∧
      m'.p.chains.link.given.items = m.p.chains.link.given.items ∧
      { m'.p.chains.link with given := m.p.chains.link.given } = m.p.chains.link) ∧
    (m'.p.chains.proof.first.given.plan = m.p.chains.proof.first.given.plan ∧
      m'.p.chains.proof.first.given.items = m.p.chains.proof.first.given.items ∧
      { m'.p.chains.proof.first with given := m.p.chains.proof.first.given } =
        m.p.chains.proof.first) ∧
    (m'.p.chains.proof.shared.given.plan = m.p.chains.proof.shared.given.plan ∧
      m'.p.chains.proof.shared.given.items = m.p.chains.proof.shared.given.items ∧
      { m'.p.chains.proof.shared with given := m.p.chains.proof.shared.given } =
        m.p.chains.proof.shared) ∧
    (m'.p.chains.proof.second.given.plan = m.p.chains.proof.second.given.plan ∧
      m'.p.chains.proof.second.given.items = m.p.chains.proof.second.given.items ∧
      { m'.p.chains.proof.second with given := m.p.chains.proof.second.given } =
        m.p.chains.proof.second)

/-- m put at c has them. By definition. -/
theorem readKept_atDigest (m : Made) (c : ByteArray) : ReadKept (atDigest m c) m :=
  ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩,
    ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-- **THE CLOSED RULE: these fields are the same at every digest of 32 bytes.** -/
def ChainsKept : Prop :=
  ∀ (pol lay KL c c' : ByteArray) (m m' : Made), c.size = 32 → c'.size = 32 →
    shortB m.p = true → madeOfAt pol lay KL c = .ok m → madeOfAt pol lay KL c' = .ok m' →
      m'.p.chains.made.sized = m.p.chains.made.sized ∧
        m'.p.chains.made.proof = m.p.chains.made.proof ∧
        m'.p.chains.made.key = m.p.chains.made.key ∧
        m'.p.chains.made.entry = m.p.chains.made.entry ∧
        m'.p.X = m.p.X ∧ m'.p.built = m.p.built ∧ m'.key = m.key ∧ m'.proof = m.proof ∧
        ReadKept m' m ∧ declKOf m' = declKOf m ∧ declPOf m' = declPOf m ∧
        roundsAt m' = roundsAt m ∧ depthOf m' = depthOf m

/-- Its proof. -/
theorem chains_kept : ChainsKept := by
  intro pol lay KL c c' m m' hc hc' hb hm hm'
  obtain rfl : atDigest m c' = m' :=
    Except.ok.inj ((madeOfAt_at hc hc' (short_of_test hb) hm).symm.trans hm')
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8⟩ := kept_atDigest m c'
  exact ⟨k1, k2, k3, k4, k5, k6, k7, k8, readKept_atDigest m c', declKOf_atDigest m c',
    declPOf_atDigest m c', roundsAt_atDigest m c', depthOf_atDigest m c'⟩

/-! ## One field against a written value -/

/-- A function of what was made does not hang on the digest. -/
def Kept {α : Type} (f : Made → α) : Prop := ∀ (m : Made) (c : ByteArray), f (atDigest m c) = f m

/-- At every digest of 32 bytes all is made, and the field f of it is w. -/
def FieldIs {α : Type} (f : Made → α) (w : α) (pol lay KL : ByteArray) : Prop :=
  ∀ c : ByteArray, c.size = 32 → ∃ m, madeOfAt pol lay KL c = .ok m ∧ f m = w

/-- **THE TEST**, with code: at 32 zero bytes in the digest's place all is made, the seven strings
are short, and the field f of it is w. -/
def fieldOk {α : Type} [DecidableEq α] (f : Made → α) (w : α) (pol lay KL : ByteArray) : Bool :=
  match madeOfAt pol lay KL Fmt.zero32 with
  | .ok m => shortB m.p && decide (f m = w)
  | .error _ => false

/-- What a yes says at the anchor. -/
theorem anchor_of_fieldOk {α : Type} [DecidableEq α] {f : Made → α} {w : α}
    {pol lay KL : ByteArray} (h : fieldOk f w pol lay KL = true) :
    ∃ m, madeOfAt pol lay KL Fmt.zero32 = .ok m ∧ shortB m.p = true ∧ f m = w := by
  unfold fieldOk at h
  split at h
  · rename_i m hm
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 h
    exact ⟨m, hm, h1, of_decide_eq_true h2⟩
  · cases h

/-- The way back at the anchor. -/
theorem fieldOk_of_made {α : Type} [DecidableEq α] {f : Made → α} {w : α} {pol lay KL : ByteArray}
    {m : Made} (hm : madeOfAt pol lay KL Fmt.zero32 = .ok m) (hb : shortB m.p = true)
    (e : f m = w) : fieldOk f w pol lay KL = true := by
  unfold fieldOk
  rw [hm]
  show (shortB m.p && decide (f m = w)) = true
  exact Bool.and_eq_true_iff.2 ⟨hb, decide_eq_true e⟩

/-- **For a kept field a yes gives the statement at every digest of 32 bytes.** -/
theorem fieldIs_of_ok {α : Type} [DecidableEq α] {f : Made → α} {w : α} {pol lay KL : ByteArray}
    (hk : Kept f) (h : fieldOk f w pol lay KL = true) : FieldIs f w pol lay KL := by
  obtain ⟨m, hm, hb, hw⟩ := anchor_of_fieldOk h
  exact fun c hc => ⟨atDigest m c, madeOfAt_at rfl hc (short_of_test hb) hm, (hk m c).trans hw⟩

/-- The statement holds of one value at most. -/
theorem fieldIs_unique {α : Type} {f : Made → α} {w w' : α} {pol lay KL : ByteArray}
    (h : FieldIs f w pol lay KL) (h' : FieldIs f w' pol lay KL) : w = w' := by
  obtain ⟨m, hm, e⟩ := h Fmt.zero32 rfl
  obtain ⟨m', hm', e'⟩ := h' Fmt.zero32 rfl
  obtain rfl : m = m' := Except.ok.inj (hm.symm.trans hm')
  exact e.symm.trans e'

/-- **A PLANT IS REFUSED**: beside a yes at w the test says no at every other value. -/
theorem fieldOk_unique {α : Type} [DecidableEq α] {f : Made → α} {w w' : α}
    {pol lay KL : ByteArray} (h : fieldOk f w pol lay KL = true) (hne : w' ≠ w) :
    fieldOk f w' pol lay KL = false := by
  cases h' : fieldOk f w' pol lay KL with
  | false => rfl
  | true =>
    obtain ⟨m, hm, _, e⟩ := anchor_of_fieldOk h
    obtain ⟨m', hm', _, e'⟩ := anchor_of_fieldOk h'
    obtain rfl : m = m' := Except.ok.inj (hm.symm.trans hm')
    exact absurd (e'.symm.trans e) hne

/-- With code: at the anchor all is made and the strings are short. -/
def madeShort (pol lay KL : ByteArray) : Bool :=
  match madeOfAt pol lay KL Fmt.zero32 with
  | .ok m => shortB m.p
  | .error _ => false

/-- Where all is made with short strings and the test says no, the statement is false. -/
theorem not_fieldIs_of_no {α : Type} [DecidableEq α] {f : Made → α} {w : α}
    {pol lay KL : ByteArray} (hs : madeShort pol lay KL = true)
    (hn : fieldOk f w pol lay KL = false) : ¬ FieldIs f w pol lay KL := by
  intro H
  obtain ⟨m, hm, e⟩ := H Fmt.zero32 rfl
  unfold madeShort at hs
  unfold fieldOk at hn
  rw [hm] at hs hn
  have hs' : shortB m.p = true := hs
  have hn' : (shortB m.p && decide (f m = w)) = false := hn
  rw [hs', decide_eq_true e] at hn'
  cases hn'

/-! ## A ride of many tests, with one call of the planner -/

/-- A first line: all is made and the strings are short; then a line for each named test on what was
made. At a refusal all are false, and the first line holds the refusal's words. -/
def fieldLines (note : String) (tests : List (String × (Made → Bool))) (r : Except String Made) :
    List (String × Bool) :=
  match r with
  | .ok m =>
    (note ++ ": to say true: at 32 zero bytes all is made and the strings are short", shortB m.p) ::
      tests.map fun t => (t.1, t.2 m)
  | .error e => (note ++ ": refused: " ++ e, false) :: tests.map fun t => (t.1, false)

/-- **FOR A RUN**: with one call of the planner. note: a string that the first line gives back (why:
the head of Johnson/Desc/Ok/PlanWritten/Rounds.lean). -/
@[noinline] def rideFields (note : String) (tests : List (String × (Made → Bool)))
    (pol lay KL : ByteArray) : List (String × Bool) :=
  fieldLines note tests (madeOfAt pol lay KL Fmt.zero32)

/-- **What a ride's true first line gives**: something is made at the anchor, with short strings,
and the other lines are the tests' answers at it, in order. -/
theorem of_rideFields {note : String} {tests : List (String × (Made → Bool))}
    {pol lay KL : ByteArray}
    (h : ((rideFields note tests pol lay KL).map Prod.snd).head? = some true) :
    ∃ m, madeOfAt pol lay KL Fmt.zero32 = .ok m ∧ shortB m.p = true ∧
      ((rideFields note tests pol lay KL).map Prod.snd).tail = tests.map fun t => t.2 m := by
  unfold rideFields fieldLines at h ⊢
  split at h
  · rename_i m hm
    refine ⟨m, hm, Option.some.inj h, ?_⟩
    show (tests.map fun t => (t.1, t.2 m)).map Prod.snd = _
    rw [List.map_map]
    rfl
  · cases h

end VerifiableInference.PlanWritten

#print axioms VerifiableInference.PlanWritten.kept_atDigest
#print axioms VerifiableInference.PlanWritten.readKept_atDigest
#print axioms VerifiableInference.PlanWritten.chains_kept
#print axioms VerifiableInference.PlanWritten.anchor_of_fieldOk
#print axioms VerifiableInference.PlanWritten.fieldOk_of_made
#print axioms VerifiableInference.PlanWritten.fieldIs_of_ok
#print axioms VerifiableInference.PlanWritten.fieldIs_unique
#print axioms VerifiableInference.PlanWritten.fieldOk_unique
#print axioms VerifiableInference.PlanWritten.not_fieldIs_of_no
#print axioms VerifiableInference.PlanWritten.of_rideFields
