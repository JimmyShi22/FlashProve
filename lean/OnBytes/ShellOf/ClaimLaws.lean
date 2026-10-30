-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ShellOf/ClaimLaws.lean: what the exit codes 0 and 10 of a program over
OnBytes/ShellOf/Claim.lean mean, in Lean's model of IO, FOR EVERY KIT (so for every parser). For
proofs only: no program imports it. What is not claimed: all that OnBytes/ShellOf/Laws.lean's head
disclaims. The theorems go one way: the code 0 gives `runOf … = true`, the code 10 gives `runOf … =
false`; none says which code a call with `runOf … = true` returns (a line that cannot be written
ends it with 18).

-/
import OnBytes.ShellOf.Claim
import OnBytes.ShellOf.Laws

set_option autoImplicit false

namespace OnBytes.ShellOf.Claimed

open OnBytes.Tie (AskedE)
open OnBytes.Shell (World Steps opsIO)

/-! ## Small steps -/

theorem fits_cons_inv {w : Want} {ws : List Want} {bs : List ByteArray} (h : Fits (w :: ws) bs) :
    ∃ b t, bs = b :: t ∧ Fits ws t := by
  cases bs with
  | nil => exact False.elim h
  | cons b t => exact ⟨b, t, rfl, (show b.size ≤ w.cap ∧ Fits ws t from h).2⟩

theorem fits_nil_inv {bs : List ByteArray} (h : Fits [] bs) : bs = [] := by
  cases bs with
  | nil => rfl
  | cons b t => exact False.elim h

/-- Five files asked: five byte strings. -/
theorem fits_five {config key entry : String} {bs : List ByteArray}
    (h : Fits (wants config key entry) bs) : ∃ b1 b2 b3 b4 b5, bs = [b1, b2, b3, b4, b5] := by
  unfold wants at h
  obtain ⟨b1, t1, rfl, h1⟩ := fits_cons_inv h
  obtain ⟨b2, t2, rfl, h2⟩ := fits_cons_inv h1
  obtain ⟨b3, t3, rfl, h3⟩ := fits_cons_inv h2
  obtain ⟨b4, t4, rfl, h4⟩ := fits_cons_inv h3
  obtain ⟨b5, t5, rfl, h5⟩ := fits_cons_inv h4
  obtain rfl := fits_nil_inv h5
  exact ⟨b1, b2, b3, b4, b5, rfl⟩

/-- The one kind of arguments that gives a call. -/
theorem askC_some {args : List String} {a : String} {ws : List Want}
    (h : askC args = some (a, ws)) :
    ∃ id0 config key entry, args = [id0, config, key, entry] ∧
      Model.Verify.idAsked id0 = some a ∧ ws = wants config key entry := by
  unfold askC at h
  split at h
  · rename_i id0 config key entry
    obtain ⟨i, hi, he⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    exact ⟨id0, config, key, entry, rfl, hi, rfl⟩
  · cases h

/-! ## The call's truth value, case by case -/

theorem runOf_error {K : Kit} {cl : Claim} {key ent : ByteArray} {e : String}
    (h : K.state cl = .error e) : runOf K cl key ent = false := by
  simp only [runOf, h]

theorem runOf_ok_error {K : Kit} {cl : Claim} {key ent : ByteArray} {x : K.X} {e : String}
    (h : K.state cl = .ok x) (hp : K.parse cl key ent = .error e) :
    runOf K cl key ent = false := by
  simp only [runOf, h, hp]

theorem runOf_ok_ok {K : Kit} {cl : Claim} {key ent : ByteArray} {x : K.X} {a : AskedE}
    (h : K.state cl = .ok x) (hp : K.parse cl key ent = .ok a) :
    runOf K cl key ent = K.verify x a := by
  simp only [runOf, h, hp]

/-! ## The exit codes -/

/-- THE EXIT CODE 0, FOR EVERY KIT. Every letter under "there are" is pinned: id0, config, key,
entry by the arguments; id by `idAsked id0`; the five byte strings by the answers of the call's own
five reads (`Steps`); x by `state` at the claim ⟨id, the three public files' bytes⟩; a by the
parser. -/
theorem main_zero {K : Kit} {args : List String} {s s' : World}
    (h : Shell.Run (mainOf (bodyOf K) args) s 0 s') :
    ∃ (id0 config key entry id : String) (pol lay kl kb eb : ByteArray) (x : K.X) (a : AskedE),
      args = [id0, config, key, entry] ∧ Model.Verify.idAsked id0 = some id ∧
      Fits (wants config key entry) [pol, lay, kl, kb, eb] ∧
      Steps opsIO (reads (wants config key entry) [pol, lay, kl, kb, eb] ++
        said (K.gives x a ++ [K.word])) s s' ∧
      K.state ⟨id, ⟨pol, lay, kl⟩⟩ = .ok x ∧ K.parse ⟨id, ⟨pol, lay, kl⟩⟩ kb eb = .ok a ∧
      K.verify x a = true ∧ runOf K ⟨id, ⟨pol, lay, kl⟩⟩ kb eb = true := by
  obtain ⟨a, ws, bs, x, v, ha, hf, hs, -, hst, -, hc, hv⟩ := mainOf_zero h
  obtain ⟨id0, config, key, entry, rfl, hi, rfl⟩ := askC_some ha
  obtain ⟨pol, lay, kl, kb, eb, rfl⟩ := fits_five hf
  exact ⟨id0, config, key, entry, a, pol, lay, kl, kb, eb, x, v, rfl, hi, hf, hs, hst, hc, hv,
    (runOf_ok_ok (cl := ⟨a, ⟨pol, lay, kl⟩⟩) (key := kb) (ent := eb) hst hc).trans hv⟩

/-- THE EXIT CODE 10: the verifier's own no, on the bytes read, at the parser's value. -/
theorem main_ten {K : Kit} {args : List String} {s s' : World}
    (h : Shell.Run (mainOf (bodyOf K) args) s 10 s') :
    ∃ (id0 config key entry id : String) (pol lay kl kb eb : ByteArray) (x : K.X) (a : AskedE),
      args = [id0, config, key, entry] ∧ Model.Verify.idAsked id0 = some id ∧
      Steps opsIO (trace (bodyOf K) (wants config key entry) [pol, lay, kl, kb, eb] []
        (.no (K.stage x a))) s s' ∧
      K.state ⟨id, ⟨pol, lay, kl⟩⟩ = .ok x ∧ K.parse ⟨id, ⟨pol, lay, kl⟩⟩ kb eb = .ok a ∧
      K.verify x a = false ∧ runOf K ⟨id, ⟨pol, lay, kl⟩⟩ kb eb = false := by
  obtain ⟨e, evs, h1, h2, hm⟩ := mainOf_means h
  cases e with
  | no st =>
    obtain ⟨a, ws, bs, x, v, ha, hf, rfl, -, hst, -, hc, hv, rfl⟩ := hm
    obtain ⟨id0, config, key, entry, rfl, hi, rfl⟩ := askC_some ha
    obtain ⟨pol, lay, kl, kb, eb, rfl⟩ := fits_five hf
    exact ⟨id0, config, key, entry, a, pol, lay, kl, kb, eb, x, v, rfl, hi, h2, hst, hc, hv,
      (runOf_ok_ok (cl := ⟨a, ⟨pol, lay, kl⟩⟩) (key := kb) (ent := eb) hst hc).trans hv⟩
  | _ => exact absurd h1 (by simp only [End.code]; decide)

end OnBytes.ShellOf.Claimed
