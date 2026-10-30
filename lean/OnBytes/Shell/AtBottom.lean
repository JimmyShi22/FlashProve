-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Shell/AtBottom.lean: the operations on the outside world, unfolded to the calls of Lean's
library.

OnBytes/Shell/AtOps.lean speaks of the three operations as wholes. Here two of them are opened, as
far as Lean's logic goes: to `System.FilePath.metadata`, `symlinkMetadata`, `IO.FS.Handle.mk`,
`IO.FS.Handle.read`, `IO.getStdout`, `putStr` and `flush`, of which the logic knows only the types.

Main theorems.
- `readIO_bytes`: if `readIO p n` returned bytes, then `metadata p`, `Handle.mk p .read` and
  `readUpTo` returned one after another, each from the state that the one before it left.
- `readUpTo_zero`, `readUpTo_succ`: what a round of `readUpTo` is.
- `readIO_absent`: `readIO` answers `.absent` only if `readBody` and then `symlinkMetadata` threw.
- `outIO_true`: if `outIO l` returned true, then `getStdout`, `putStr` and `flush` returned, in this
  order.

What is not claimed. Nothing about compiled code, Lean's run-time or the operating system. Nothing
on what `metadata`, `Handle.read` or `putStr` do: for instance, that a read of k bytes returns at
most k bytes, that the bytes returned are the file's content, or that a line given to `putStr`
reaches anybody. Theorems only; the program does not import this file.
-/
import OnBytes.Shell.AtOps

namespace OnBytes.Shell

/-- No round is left: what has been read is returned. -/
theorem readUpTo_zero {h : IO.FS.Handle} {n : Nat} {acc bs : ByteArray} {s s' : World} :
    Run (readUpTo h n 0 acc) s bs s' ↔ acc = bs ∧ s = s' := run_pure

/-- One round: either enough bytes have been read, or `Handle.read` is called for the bytes that
are still needed, at most `readChunk` of them. An empty array stops the loop. Otherwise the bytes
are appended, and the next round starts in the state that the read left. -/
theorem readUpTo_succ {h : IO.FS.Handle} {n r : Nat} {acc bs : ByteArray} {s s' : World} :
    Run (readUpTo h n (r + 1) acc) s bs s' ↔
      (n ≤ acc.size ∧ acc = bs ∧ s = s') ∨
      (¬ n ≤ acc.size ∧ ∃ c s1, Run (h.read (min (n - acc.size) readChunk).toUSize) s c s1 ∧
        ((c.isEmpty = true ∧ acc = bs ∧ s1 = s') ∨
          (c.isEmpty = false ∧ Run (readUpTo h n r (acc ++ c)) s1 bs s'))) := by
  show Run (if n ≤ acc.size then pure acc
    else h.read (min (n - acc.size) readChunk).toUSize >>= fun c =>
      if c.isEmpty = true then pure acc else readUpTo h n r (acc ++ c)) s bs s' ↔ _
  by_cases hn : n ≤ acc.size
  · rw [if_pos hn, run_pure]
    exact ⟨fun h => Or.inl ⟨hn, h⟩, fun h => h.elim (fun h => h.2) fun h => absurd hn h.1⟩
  · rw [if_neg hn, run_bind]
    constructor
    · rintro ⟨c, s1, h1, h2⟩
      refine Or.inr ⟨hn, c, s1, h1, ?_⟩
      cases hc : c.isEmpty with
      | true =>
        rw [hc, if_pos rfl] at h2
        exact Or.inl ⟨rfl, run_pure.1 h2⟩
      | false =>
        rw [hc] at h2
        exact Or.inr ⟨rfl, h2⟩
    · rintro (⟨h0, -⟩ | ⟨-, c, s1, h1, h2⟩)
      · exact absurd h0 hn
      · refine ⟨c, s1, h1, ?_⟩
        rcases h2 with ⟨hc, h3⟩ | ⟨hc, h3⟩
        · rw [hc, if_pos rfl]
          exact run_pure.2 h3
        · rw [hc]
          exact h3

/-- If an action that is followed by a plain result throws, the action itself threw. -/
theorem throws_bind_pure {ε σ α β : Type} {x : EST ε σ α} {b : β} {s s' : Void σ} {e : ε}
    (h : (x >>= fun _ => (pure b : EST ε σ β)) s = EST.Out.error e s') :
    x s = EST.Out.error e s' := by
  have h2 : EST.bind x (fun _ => (pure b : EST ε σ β)) s = EST.Out.error e s' := h
  unfold EST.bind at h2
  split at h2
  · rename_i a s1 h1
    have h3 : (EST.Out.ok b s1 : EST.Out ε σ β) = EST.Out.error e s' := h2
    cases h3
  · rename_i e1 s1 h1
    cases h2
    exact h1

/-- The question whether a name exists is never answered with bytes. -/
theorem nameOf_ne_bytes {p : String} {b : ByteArray} {s s' : World} :
    ¬ Run (nameOf p) s (.bytes b) s' := by
  intro h
  rcases run_try.1 h with h | ⟨e, s1, -, h⟩
  · obtain ⟨md, s1, _, h⟩ := run_bind.1 h
    cases (run_pure.1 h).1
  · cases (run_pure.1 h).1

/-- An error is never turned into bytes. -/
theorem readOf_ne_bytes {p : String} (e : IO.Error) {b : ByteArray} {s s' : World} :
    ¬ Run (readOf p e) s (.bytes b) s' := by
  intro h
  cases e <;> first
    | exact nameOf_ne_bytes h
    | cases (run_pure.1 h).1

/-- If `readIO` returned bytes: `metadata` said that p is a regular file, `Handle.mk` returned a
handle, and `readUpTo` on it returned the bytes. -/
theorem readIO_bytes {p : String} {n : Nat} {bs : ByteArray} {s s' : World}
    (h : Run (readIO p n) s (.bytes bs) s') :
    ∃ md hd s1 s2, Run (System.FilePath.metadata p) s md s1 ∧ (md.type != .file) = false ∧
      Run (IO.FS.Handle.mk p .read) s1 hd s2 ∧ Run (readUpTo hd n n ByteArray.empty) s2 bs s' := by
  rcases run_try.1 h with h | ⟨e, s1, -, h⟩
  · unfold readBody at h
    obtain ⟨md, s1, h1, h⟩ := run_bind.1 h
    cases hm : (md.type != .file) with
    | true =>
      rw [hm, if_pos rfl] at h
      cases (run_pure.1 h).1
    | false =>
      rw [hm] at h
      obtain ⟨hd, s2, h2, h⟩ := run_bind.1 h
      obtain ⟨b, s3, h3, h⟩ := run_bind.1 h
      obtain ⟨h4, rfl⟩ := run_pure.1 h
      cases h4
      exact ⟨md, hd, s1, s2, h1, hm, h2, h3⟩
  · exact absurd h (readOf_ne_bytes e)

/-- If `readIO` returned `.absent`: `readBody` threw the error `noFileOrDirectory`, and the call of
`symlinkMetadata`, in the state that this throw left, threw too. -/
theorem readIO_absent {p : String} {n : Nat} {s s' : World} (h : Run (readIO p n) s .absent s') :
    ∃ fn c d s1 e, readBody p n s = EST.Out.error (.noFileOrDirectory fn c d) s1 ∧
      System.FilePath.symlinkMetadata p s1 = EST.Out.error e s' := by
  rcases run_try.1 h with h | ⟨e, s1, he, h⟩
  · unfold readBody at h
    obtain ⟨md, s1, h1, h⟩ := run_bind.1 h
    cases hm : (md.type != .file) with
    | true =>
      rw [hm, if_pos rfl] at h
      cases (run_pure.1 h).1
    | false =>
      rw [hm] at h
      obtain ⟨hd, s2, h2, h⟩ := run_bind.1 h
      obtain ⟨b, s3, h3, h⟩ := run_bind.1 h
      cases (run_pure.1 h).1
  · cases e with
    | noFileOrDirectory fn c d =>
      have h2 : Run (nameOf p) s1 .absent s' := h
      rcases run_try.1 h2 with h3 | ⟨e2, s2, he2, h3⟩
      · obtain ⟨md, s3, _, h4⟩ := run_bind.1 h3
        cases (run_pure.1 h4).1
      · obtain ⟨_, rfl⟩ := run_pure.1 h3
        refine ⟨fn, c, d, s1, e2, he, ?_⟩
        have h5 : (System.FilePath.symlinkMetadata p >>= fun _ =>
          (pure (FileRead.unreadable .noSuch) : IO FileRead)) s1 = EST.Out.error e2 s2 := he2
        exact throws_bind_pure h5
    | alreadyExists _ _ _ => cases (run_pure.1 h).1
    | otherError _ _ => cases (run_pure.1 h).1
    | resourceBusy _ _ => cases (run_pure.1 h).1
    | resourceVanished _ _ => cases (run_pure.1 h).1
    | unsupportedOperation _ _ => cases (run_pure.1 h).1
    | hardwareFault _ _ => cases (run_pure.1 h).1
    | unsatisfiedConstraints _ _ => cases (run_pure.1 h).1
    | illegalOperation _ _ => cases (run_pure.1 h).1
    | protocolError _ _ => cases (run_pure.1 h).1
    | timeExpired _ _ => cases (run_pure.1 h).1
    | interrupted _ _ _ => cases (run_pure.1 h).1
    | invalidArgument _ _ _ => cases (run_pure.1 h).1
    | permissionDenied _ _ _ => cases (run_pure.1 h).1
    | resourceExhausted _ _ _ => cases (run_pure.1 h).1
    | inappropriateType _ _ _ => cases (run_pure.1 h).1
    | noSuchThing _ _ _ => cases (run_pure.1 h).1
    | unexpectedEof => cases (run_pure.1 h).1
    | userError _ => cases (run_pure.1 h).1

/-- If `outIO` returned true: `getStdout` returned a stream, and that stream's `putStr`, on the line
with a line feed, and its `flush` returned, each without an exception. -/
theorem outIO_true {l : String} {s s' : World} (h : Run (outIO l) s true s') :
    ∃ (o : IO.FS.Stream) (s1 s2 : World), Run (IO.getStdout : IO IO.FS.Stream) s o s1 ∧
      Run (o.putStr (l.push '\n')) s1 () s2 ∧ Run o.flush s2 () s' := by
  rcases run_try.1 h with h | ⟨e, s1, -, h⟩
  · obtain ⟨o, s1, h1, h⟩ := run_bind.1 h
    obtain ⟨⟨⟩, s2, h2, h⟩ := run_bind.1 h
    obtain ⟨⟨⟩, s3, h3, h⟩ := run_bind.1 h
    obtain ⟨_, rfl⟩ := run_pure.1 h
    exact ⟨o, s1, s2, h1, h2, h3⟩
  · cases (run_pure.1 h).1

end OnBytes.Shell

#print axioms OnBytes.Shell.readIO_bytes
#print axioms OnBytes.Shell.readIO_absent
#print axioms OnBytes.Shell.outIO_true
