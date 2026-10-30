-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/ConfigureLaws.lean: the parameter bytes of an entry file's chain follow from the
lines of the parameter file and the digest of the public files alone. By the code (no theorem) the
digest takes in all three files.

`configure` (OnBytes/Params/Configure.lean) makes the parameter bytes of all seven chains from the
lines, the caller's shapes and the digest. `entryParams` (OnBytes/Params/Derive.lean) makes those of
the entry's chain from the lines and the digest, without the shapes.

Main definition: `entryBytesOf`. Main theorem. `configure_entry`: if `configure` returns a value,
`entryParams` on the same lines and digest returns that value's parameter bytes of the entry's
chain.

What is not claimed. Nothing on soundness, and nothing on the planner's bounds. The converse is not
stated: `entryParams` can return bytes where `configure` refuses. Nothing is said of the other six
chains. `entryParams` is code of this folder: no theorem says that it is the format's or the C++
programs' derivation, and tests alone compare its bytes with theirs, at stored lines and digests.
For proofs only; the program does not import this file.
-/
import OnBytes.Params.Configure

set_option autoImplicit false

namespace OnBytes.Params

/-- If two steps in a row return a value, the first has returned a value, and the second has
returned its value on that one. -/
theorem opt_bind {α β : Type} {x : Option α} {f : α → Option β} {b : β}
    (h : (x >>= f) = some b) : ∃ a, x = some a ∧ f a = some b := by
  cases x with
  | none => cases h
  | some a => exact ⟨a, rfl, h⟩

/-- The same for steps that can refuse with a name. -/
theorem exc_bind {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- What `orRefuse` returns was there. -/
theorem orRefuse_ok {α : Type} {x : Option α} {why : String} {a : α}
    (h : orRefuse x why = .ok a) : x = some a := by
  cases x with
  | none => cases h
  | some a0 =>
    cases h
    rfl

/-- If a step that stops on a condition, with the steps that follow it, returns a value, the steps
that follow have returned it. That the condition failed is not kept. -/
theorem opt_guard {β : Type} {c : Prop} [Decidable c] {next : PUnit → Option β} {b : β}
    (h : (if c then (none : Option PUnit) >>= next else pure PUnit.unit >>= next) = some b) :
    next PUnit.unit = some b := by
  split at h
  · cases h
  · exact h

/-- The same for steps that can refuse with a name. -/
theorem exc_guard {ε β : Type} {c : Prop} [Decidable c] {e : ε} {next : PUnit → Except ε β} {b : β}
    (h : (if c then (throw e : Except ε PUnit) >>= next else pure PUnit.unit >>= next) = .ok b) :
    next PUnit.unit = .ok b := by
  split at h
  · cases h
  · exact h

/-- If one of two steps is taken and what follows returns a value, it has returned it on some value.
That the step returned that value is not kept. -/
theorem opt_either {α β : Type} {c : Prop} [Decidable c] {x y : Option α} {next : α → Option β}
    {b : β} (h : (if c then x >>= next else y >>= next) = some b) : ∃ a, next a = some b := by
  split at h
  · obtain ⟨a, _, h⟩ := opt_bind h
    exact ⟨a, h⟩
  · obtain ⟨a, _, h⟩ := opt_bind h
    exact ⟨a, h⟩

/-- The same for steps that can refuse with a name. -/
theorem exc_either {ε α β : Type} {c : Prop} [Decidable c] {x y : Except ε α}
    {next : α → Except ε β} {b : β} (h : (if c then x >>= next else y >>= next) = .ok b) :
    ∃ a, next a = .ok b := by
  split at h
  · obtain ⟨a, _, h⟩ := exc_bind h
    exact ⟨a, h⟩
  · obtain ⟨a, _, h⟩ := exc_bind h
    exact ⟨a, h⟩

/-- The sizes of the test on the table hold the table that they were made for. -/
theorem linSized_table {s : Setting} {L : LinLines} {T : TableSize} {codes c : Codes}
    {x : LinSized} (h : linSized s L T codes = some (x, c)) : x.table = T := by
  unfold linSized at h
  extract_lets at h
  replace h := opt_guard h
  replace h := opt_guard h
  replace h := opt_guard h
  replace h := opt_guard h
  replace h := opt_guard h
  replace h := opt_guard h
  obtain ⟨⟨x1, y1, z1⟩, _, h⟩ := opt_bind h
  replace h := opt_guard h
  obtain ⟨stU, _, h⟩ := opt_bind h
  obtain ⟨stO, h⟩ := opt_either h
  obtain ⟨stW, _, h⟩ := opt_bind h
  repeat' split at h
  all_goals first
    | (cases h; rfl)
    | cases h

/-- The sizes of a proof's chains hold the table that follows from the lines. -/
theorem proofSized_table {l : Lines} {sub : Subproofs} {z : ProofSized}
    (h : proofSized l sub = some z) : deriveTable (settingOf l) l = some z.batch.table := by
  unfold proofSized at h
  extract_lets at h
  replace h := opt_guard h
  obtain ⟨link, _, h⟩ := opt_bind h
  obtain ⟨stages, _, h⟩ := opt_bind h
  obtain ⟨T, hT, h⟩ := opt_bind h
  split at h
  replace h := opt_guard h
  obtain ⟨⟨batch, c2⟩, hb, h⟩ := opt_bind h
  cases h
  exact hT.trans (congrArg some (linSized_table hb).symm)

/-- What `sized` returns holds the setting of the lines, and the link and the codes that `linkSized`
makes for the table that follows from the lines. -/
theorem sized_link {l : Lines} {x : Shapes} {z : Sized} (h : sized l x = .ok z) :
    z.set = settingOf l ∧ ∃ T, deriveTable (settingOf l) l = some T ∧
      linkSized (settingOf l) l T {} = some (z.link, z.entryCodes) := by
  unfold sized at h
  extract_lets at h
  replace h := exc_guard h
  obtain ⟨proof, hp, h⟩ := exc_bind h
  replace h := exc_guard h
  obtain ⟨key, _, h⟩ := exc_bind h
  replace h := exc_guard h
  obtain ⟨⟨link, codes⟩, hl, h⟩ := exc_bind h
  replace h := exc_guard h
  replace h := exc_guard h
  cases h
  exact ⟨rfl, _, proofSized_table (orRefuse_ok hp), orRefuse_ok hl⟩

/-- If `configure` returns a value, `entryParams` on the same lines and digest returns that value's
parameter bytes of the entry's chain. -/
theorem configure_entry {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat} {made : Configured}
    (h : configure l x cfg bits = .ok made) : entryParams l cfg = .ok made.entryLink := by
  unfold configure at h
  obtain ⟨z, hz, h⟩ := exc_bind h
  obtain ⟨proof, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨entry, he, h⟩ := exc_bind h
  obtain ⟨hs, T, hT, hl⟩ := sized_link hz
  have hm : made.entryLink = Fmt.paramsBytes entry.plan cfg
      [("codes", spellCodes z.entryCodes), ("the link", spellLink z.link.shape)] := by
    split at h
    · obtain ⟨_, _, h⟩ := exc_bind h
      replace h := exc_guard h
      replace h := exc_guard h
      replace h := exc_guard h
      replace h := exc_guard h
      replace h := exc_guard h
      replace h := exc_guard h
      replace h := exc_guard h
      cases h
      rfl
    · cases h
  rw [hs] at he
  have hsz : entrySized l = .ok (z.link, z.entryCodes, entry) := by
    unfold entrySized
    dsimp only
    rw [hT]
    show (orRefuse (linkSized (settingOf l) l T {}) >>= fun y =>
      finishHeld (settingOf l) .once (linkPlan y.1) >>= fun p =>
        (pure (y.1, y.2, p) : Except String (LinkSized × Codes × Planned))) = _
    rw [hl]
    show (finishHeld (settingOf l) .once (linkPlan z.link) >>= fun p =>
      (pure (z.link, z.entryCodes, p) : Except String (LinkSized × Codes × Planned))) = _
    rw [he]
    rfl
  unfold entryParams
  rw [hm, hsz]
  rfl

/-- The parameter bytes of an entry file's chain as a function of the three public files: the lines
that `readLines` reads from the parameter file, and the digest of the three files, the parameter
file first and the layout file second, go to `entryParams`. Nothing if a step refuses. The arguments
come in the digest's order, parameter file, layout file, scale file; `Model.Verify.planned` takes
the scale file second. It can return bytes for files that the program refuses. For statements only:
the program makes these bytes in `configure`. -/
def entryBytesOf (pol lay KL : ByteArray) : Option ByteArray :=
  (readLines pol).toOption.bind fun x =>
    (entryParams x.1 (configurationDigest [pol, lay, KL])).toOption

end OnBytes.Params

#print axioms OnBytes.Params.configure_entry
