-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Chain/SessionLaws.lean: what a step of a session is, in terms of the strict reader.

Main theorems: `readIn_eq`, `readIn_view`, `acceptIn_eq`.
-/
import OnBytes.Chain.Session
import OnBytes.Chain.ReaderLaws

namespace OnBytes

/-- A reading step of a session is the strict reader at the format's hash, given the session's
record of vertices. The new record is the one that the reader returns. -/
theorem readIn_eq (S : Fmt.SpecX) (b : ByteArray) (i : Nat) (seen : Fmt.Seen) :
    (readIn S b i ⟨seen⟩).map (fun x => (x.1.out, x.1.next, x.2.seen)) =
      (Fmt.readChainX (m := Id) Fmt.formatHash S seen b i).map fun x => (x.1, x.2, x.1.seen) := by
  rw [← readChain_eq]
  show (match readChain S seen b i with
    | none => none
    | some (o, j) => some ((⟨o, viewOf S o, j⟩ : ChainRead), (⟨o.seen⟩ : Session))).map _ = _
  cases readChain S seen b i with
  | none => rfl
  | some x => rfl

/-- The view that a reading step returns is the view of Fmt/ of what it read. -/
theorem readIn_view (S : Fmt.SpecX) (b : ByteArray) (i : Nat) (s s' : Session) (r : ChainRead)
    (h : readIn S b i s = some (r, s')) : r.view = Fmt.viewX S r.out := by
  unfold readIn at h
  cases hr : readChain S s.seen b i with
  | none =>
    rw [hr] at h
    cases h
  | some x =>
    rw [hr] at h
    cases h
    exact viewOf_eq S x.1

/-- An accepting step of a session is `Chain.accepts`, given the session's record of vertices. -/
theorem acceptIn_eq {Y : Type} (c : Chain Y) (y : Y) (b : ByteArray) (i : Nat)
    (seen : Fmt.Seen) :
    (acceptIn c y b i ⟨seen⟩).map (fun x => (x.2.seen, x.1.next)) = c.accepts y seen b i := by
  unfold Chain.accepts Chain.read
  rw [← readChain_eq]
  show (match readChain c.spec seen b i with
    | none => none
    | some (o, j) =>
      if c.dec y (viewOf c.spec o) then
        some ((⟨o, viewOf c.spec o, j⟩ : ChainRead), (⟨o.seen⟩ : Session))
      else none).map _ = _
  cases readChain c.spec seen b i with
  | none => rfl
  | some x =>
    obtain ⟨o, j⟩ := x
    dsimp only
    rw [viewOf_eq]
    cases c.dec y (Fmt.viewX c.spec o) <;> rfl

end OnBytes
