-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/KeyFile.lean: the program's check of a key file, and the compiled verifier of the
library's theory, for the first of the file's three chains.

`Key.check` is the function that the program runs on a key file; "the program" is the Lean text
`verify-on-bytes` (OnBytes/Main.lean); this repository builds no stand-alone program from it. A key
file holds three chains. This file proves of the first, the one-time chain: if `Key.check` says yes,
then the program has read that chain under its own description, and the compiled verifier of the
protocol made from that description and the program's own decision on that chain accepts the typed
string that the library's typing makes from what was read.

The hypotheses are the test `limitsOfX` on the description, and a bound on the file's size. The test
is evaluated on the program's own description of the test key in OnBytes/Tie/TestKeyOneTime.lean.
For any other key it is a test to be evaluated; it hangs on the chain's parameters alone
(OnBytes/Tie/KeyRounds.lean).

The theorem says "if the check says yes"; that the check says yes on some file is not tested in this
directory. It starts at `Key.check`. From a whole call's exit code 0, `main_zero_port`
(OnBytes/K/Top.lean, from `Shell.Run (main args) s 0 s'`) has `PortYesAt`, of which `Key.check`'s
yes is a clause. Of the command `verify -key` nothing is said here.

Main definition: `oneTimeDec`.
Main theorems: `readKey_first`, `key_check_oneTime`.
It claims nothing on soundness. It says nothing of a key file's shared chain, which at the test key
is outside the limits (OnBytes/Tie/TestNotCovered.lean), nor of its second chain, which opens trees
that it has taken over, nor of how the one-time chain's seal and trees enter them. At the test key
the one-time chain sends two trees that it never opens (OnBytes/Tie/TestKeyOneTime.lean); by the
format page the second chain takes them over (docs/format/FORMAT.md, R13.7). Of such a tree
the compiled verifier knows the 32 bytes of its root and nothing more (OnBytes/Tie/OneChain.lean).
So this theorem does not say that the compiled verifier checks the key's table. A chain that breaks
no limit opens no stored table: nothing under the table's root is read in it, and the root enters
only through the chain's statement.
-/
import OnBytes.Key.File
import OnBytes.Tie.Session

set_option autoImplicit false

namespace OnBytes.Tie
open OnBytes.Proof

/-- If a reading made of two steps returns a value, then both steps have returned one. -/
theorem bind_ok {α β : Type} (x : Reading α) (f : α → Reading β) (s s' : Session) (b : β)
    (h : (x >>= f) s = .ok (b, s')) : ∃ a s1, x s = .ok (a, s1) ∧ f a s1 = .ok (b, s') := by
  have h' : (match x s with
    | .ok (a, s1) => f a s1
    | .error e => .error e) = .ok (b, s') := by
    have : (x >>= f) s = (x s >>= fun p => f p.1 p.2) := rfl
    rw [this] at h
    cases hx : x s with
    | error e => rw [hx] at h; cases h
    | ok p => rw [hx] at h; exact h
  cases hx : x s with
  | error e => rw [hx] at h'; cases h'
  | ok p =>
    rw [hx] at h'
    exact ⟨p.1, p.2, rfl, h'⟩

/-- If a needed value is returned, it was there, and the session has not changed. -/
theorem need_ok {α : Type} (why : String) (x : Option α) (s s' : Session) (a : α)
    (h : need why x s = .ok (a, s')) : x = some a ∧ s' = s := by
  unfold need at h
  cases x with
  | none => cases h
  | some y =>
    injection h with h1
    exact ⟨congrArg some (congrArg (·.1) h1), (congrArg (·.2) h1).symm⟩

/-- A chain that was read under a name for its refusal was read in the session. -/
theorem readNamed_ok (front : String) (S : Fmt.SpecX) (b : ByteArray) (i : ℕ) (s s' : Session)
    (r : ChainRead) (h : readNamed front S b i s = .ok (r, s')) :
    readIn S b i s = some (r, s') := by
  unfold readNamed at h
  cases hq : readIn S b i s with
  | none => rw [hq] at h; cases h
  | some y =>
    rw [hq] at h
    injection h with h1
    rw [h1]

/-- The tail that was read holds the first chain that it was given. -/
theorem readTail_first (p : TailPublic) (dry : FirstEnd) (first : ChainRead) (b : ByteArray)
    (s s' : Session) (r : TailRead) (h : readTail p dry first b s = .ok (r, s')) :
    r.first = first := by
  unfold readTail at h
  obtain ⟨_, _, _, h⟩ := bind_ok _ _ _ _ _ h
  obtain ⟨_, _, _, h⟩ := bind_ok _ _ _ _ _ h
  obtain ⟨_, _, _, h⟩ := bind_ok _ _ _ _ _ h
  obtain ⟨_, _, _, h⟩ := bind_ok _ _ _ _ _ h
  obtain ⟨_, _, _, h⟩ := bind_ok _ _ _ _ _ h
  obtain ⟨_, _, _, h⟩ := bind_ok _ _ _ _ _ h
  obtain ⟨_, _, _, h⟩ := bind_ok _ _ _ _ _ h
  obtain ⟨_, _, _, h⟩ := bind_ok _ _ _ _ _ h
  obtain ⟨_, _, _, h⟩ := bind_ok _ _ _ _ _ h
  obtain ⟨_, _, _, h⟩ := bind_ok _ _ _ _ _ h
  injection h with h1
  exact (congrArg (·.1.first) h1).symm

/-- The decision on a key's one-time chain: the chain's block succeeds on the view and uses up all
rounds. This is the test that `Key.check` itself makes (`judge`, by `Blk.runOn`);
`Key.oneTimeDecides` is not used here. -/
def oneTimeDec (p : Params.OneTime) (v : Fmt.View) : Bool :=
  ((Key.oneTime p).runOn (Key.startOf p) v).toOption.isSome

/-- What `Key.readKey` has done with the one-time chain if it returns. -/
theorem readKey_first (k : Params.KeyChains) (table : Params.TableName) (file : ByteArray) (j : ℕ)
    (s s' : Session) (t : TailRead) (h : Key.readKey k table file j s = .ok (t, s')) :
    ∃ rounds dry S s1,
      (Key.oneTime k.oneTime).dryRun (Key.startOf k.oneTime) = some (rounds, dry) ∧
      k.oneTime.describe table rounds = some S ∧ readIn S file j s = some (t.first, s1) := by
  unfold Key.readKey at h
  obtain ⟨⟨rounds, dry⟩, s1, h1, ha⟩ := bind_ok _ _ _ _ _ h
  obtain ⟨e1, rfl⟩ := need_ok _ _ _ _ _ h1
  dsimp only at ha
  obtain ⟨S, s2, h2, hb⟩ := bind_ok _ _ _ _ _ ha
  obtain ⟨e2, rfl⟩ := need_ok _ _ _ _ _ h2
  obtain ⟨first, s3, h3, hc⟩ := bind_ok _ _ _ _ _ hb
  obtain ⟨r, s4, h4, hd⟩ := bind_ok _ _ _ _ _ hc
  split at hd
  · obtain ⟨_, _, hth, _⟩ := bind_ok _ _ _ _ _ hd
    cases hth
  · obtain ⟨_, s5, _, he⟩ := bind_ok _ _ _ _ _ hd
    injection he with h5
    have e5 : r = t := congrArg (·.1) h5
    subst e5
    rw [readTail_first _ _ _ _ _ _ _ h4]
    exact ⟨rounds, dry, S, s3, e1, e2, readNamed_ok _ _ _ _ _ _ _ h3⟩

/-- If the program's check of a key file says yes, then the program has read the file's one-time
chain, from the byte j at which `Key.readTable` ends, under its own description. If that description
breaks no limit and the file has at most 2^32 - 160 bytes, the compiled verifier of the protocol
made from that description and the program's own decision on that chain (`oneTimeDec`) accepts what
was read of that chain. Of a tree that this chain sends and never opens, the compiled verifier knows
the root's 32 bytes alone. Nothing is said of the file's two later chains. -/
theorem key_check_oneTime (k : Params.KeyChains) (file : ByteArray) (table : Params.TableName)
    (h : Key.check k file = .ok table) :
    ∃ (j : ℕ) (rounds : Params.Rounds) (dry : FirstEnd) (S : Fmt.SpecX) (r : ChainRead)
      (s' : Session),
      Key.readTable k.oneTime.lin.fold.index k.oneTime.given.cfg file = .ok (table, j) ∧
      (Key.oneTime k.oneTime).dryRun (Key.startOf k.oneTime) = some (rounds, dry) ∧
      k.oneTime.describe table rounds = some S ∧
      readIn S file j Session.start = some (r, s') ∧
      (limitsOfX S = [] → file.size + 16 ≤ 2 ^ 32 - 144 →
        CompiledAccepts S.base (oneTimeDec k.oneTime) r.out) := by
  unfold Key.check at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i table' j hrt
        split at h
        · cases h
        · rename_i t ht
          split at h
          · cases h
          · rename_i hno
            injection h with h'
            subst h'
            have hrun : ∃ s', Key.readKey k table' file j Session.start = .ok (t, s') := by
              unfold Reading.fromStart at ht
              cases hq : Key.readKey k table' file j Session.start with
              | error e => rw [hq] at ht; cases ht
              | ok y =>
                rw [hq] at ht
                injection ht with hy
                exact ⟨y.2, by rw [← hy]⟩
            obtain ⟨s', hs'⟩ := hrun
            obtain ⟨rounds, dry, S, s1, e1, e2, e3⟩ := readKey_first k table' file j _ _ t hs'
            refine ⟨j, rounds, dry, S, t.first, s1, hrt, e1, e2, e3, fun hl hb => ?_⟩
            refine readIn_compiled S _ hl Session.start file j hb t.first s1 e3 ?_
            unfold Key.keyRefusal at hno
            dsimp only at hno
            split at hno
            · cases hno
            · rename_i real hj
              unfold judge at hj
              unfold oneTimeDec
              split at hj
              · rename_i a ha
                rw [ha]
                rfl
              · cases hj

end OnBytes.Tie

#print axioms OnBytes.Tie.key_check_oneTime
