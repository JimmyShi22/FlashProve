-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TieK/KeyOpen.lean: what the program has done with a key file if its check says yes: every
step of `Key.check`, `Key.readKey` and `Key.keyRefusal` as a named fact, for all three chains.

`Key.check` (OnBytes/Key/File.lean) is the function that the program `verify-on-bytes` runs on a key
file. OnBytes/Tie/KeyFile.lean opens it as far as the one-time chain. This file goes on through the
tail: it proves no more than what the text says, as one statement, so that a tie from the program's
yes to another verifier's yes can begin at named facts.

`KeyFacts` lists them: the one-time chain's field is the one in which the program computes, and its
public values are admitted; the table was read; the one-time chain's rounds come from a dry run of
its block, its description is made of them and the table; the strict reader has read it behind the
table, from the empty record of vertices; the tail was read at what that dry run has returned
(`readTail_open` opens it); no byte is left over; the one-time chain's block accepts its view and
returns an end, `real`; the tail's yes (`TailYes`) at `real`.

Main definition: `KeyFacts`.
Main theorems: `readKey_open`, `key_check_open`.
It claims nothing on soundness. The program does not import this file.

-/
import OnBytes.TieK.TailOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.TieK
open OnBytes.Proof OnBytes.Tie

/-- The facts of a key file's three chains' reading that has returned r, from the session s to
s'. -/
structure KeyReadFacts (k : Params.KeyChains) (table : Params.TableName) (file : ByteArray)
    (j : Nat) (s s' : Session) (r : TailRead) (rounds1 : Params.Rounds) (dry : FirstEnd)
    (spec1 : Fmt.SpecX) (s1 : Session) : Prop where
  first_dry : (Key.oneTime k.oneTime).dryRun (Key.startOf k.oneTime) = some (rounds1, dry)
  first_spec : k.oneTime.describe table rounds1 = some spec1
  first_read : readIn spec1 file j s = some (r.first, s1)
  tail_read : readTail (Key.tailPublic k table) dry r.first file s1 = .ok (r, s')
  whole : r.next = file.size

/-- **What `Key.readKey` has done if it returns.** -/
theorem readKey_open (k : Params.KeyChains) (table : Params.TableName) (file : ByteArray) (j : Nat)
    (s s' : Session) (r : TailRead) (h : Key.readKey k table file j s = .ok (r, s')) :
    ∃ rounds1 dry spec1 s1, KeyReadFacts k table file j s s' r rounds1 dry spec1 s1 := by
  unfold Key.readKey at h
  obtain ⟨⟨rounds1, dry⟩, t1, h1, g1⟩ := bind_ok _ _ _ _ _ h
  obtain ⟨e1, et1⟩ := need_ok _ _ _ _ _ h1
  subst et1
  dsimp only at g1
  obtain ⟨spec1, t2, h2, g2⟩ := bind_ok _ _ _ _ _ g1
  obtain ⟨e2, et2⟩ := need_ok _ _ _ _ _ h2
  subst et2
  obtain ⟨first, s1, h3, g3⟩ := bind_ok _ _ _ _ _ g2
  have e3 := readNamed_ok _ _ _ _ _ _ _ h3
  obtain ⟨r', t4, h4, g4⟩ := bind_ok _ _ _ _ _ g3
  split at g4
  · obtain ⟨_, _, hth, _⟩ := bind_ok _ _ _ _ _ g4
    cases hth
  · rename_i hsize
    obtain ⟨u5, t5, h5, g5⟩ := bind_ok _ _ _ _ _ g4
    injection h5 with h5'
    have et5 : t4 = t5 := congrArg (·.2) h5'
    subst et5
    injection g5 with hr
    have er : r' = r := congrArg (·.1) hr
    have es : t4 = s' := congrArg (·.2) hr
    subst er
    subst es
    have ef : r'.first = first := readTail_first _ _ _ _ _ _ _ h4
    have esize : r'.next = file.size := by
      simpa using hsize
    subst ef
    exact ⟨_, _, _, _, ⟨e1, e2, e3, h4, esize⟩⟩

/-- The facts of a check of a key file that said yes. -/
structure KeyFacts (k : Params.KeyChains) (file : ByteArray) (table : Params.TableName) (j : Nat)
    (r : TailRead) (s' : Session) (rounds1 : Params.Rounds) (dry : FirstEnd) (spec1 : Fmt.SpecX)
    (s1 : Session) (real : FirstEnd) (end2 : SharedEnd) : Prop where
  /-- the one-time chain's field is the one in which the program computes -/
  field_two : (k.oneTime.given.plan.field != .two) = false
  /-- the public values of the one-time chain are admitted -/
  admitted : (!Key.admitted k.oneTime) = false
  table_read :
    Key.readTable k.oneTime.lin.fold.index k.oneTime.given.cfg file = .ok (table, j)
  read : KeyReadFacts k table file j Session.start s' r rounds1 dry spec1 s1
  first_yes : (Key.oneTime k.oneTime).runOn (Key.startOf k.oneTime) r.first.view = .ok real
  tail_yes : TailYes (Key.tailPublic k table) real r end2

/-- **What the program has done with a key file if its check says yes.** -/
theorem key_check_open (k : Params.KeyChains) (file : ByteArray) (table : Params.TableName)
    (h : Key.check k file = .ok table) :
    ∃ j r s' rounds1 dry spec1 s1 real end2,
      KeyFacts k file table j r s' rounds1 dry spec1 s1 real end2 := by
  unfold Key.check at h
  dsimp only at h
  split at h
  · cases h
  · rename_i hfield
    split at h
    · cases h
    · rename_i hadm
      split at h
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
            obtain ⟨rounds1, dry, spec1, s1, hf⟩ := readKey_open _ _ _ _ _ _ _ hs'
            unfold Key.keyRefusal at hno
            dsimp only at hno
            split at hno
            · cases hno
            · rename_i real hj
              obtain ⟨end2, hy⟩ := tailRefusal_open _ _ _ hno
              exact ⟨j, t, s', rounds1, dry, spec1, s1, real, end2,
                ⟨eq_false_of_ne_true hfield, eq_false_of_ne_true hadm, hrt, hf,
                  judge_ok _ _ _ _ _ hj, hy⟩⟩

end OnBytes.TieK
