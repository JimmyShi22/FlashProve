-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/PlanAtDigest.lean: what the planner's text with the digest as an argument (`plannedAt`,
OnBytes/Tie/ChainsAtCfg.lean) returns at any digest of 32 bytes, said from its answer at one written
string; and the entry's chain in it, where the parameter file says a ground's lines.

Why. A verifier that forms the digest of the three public files by a hash function that is drawn
plans at that function's own digest. A statement about it needs the plan at every digest, and data
that are fixed before the function is drawn and hold no answer of it.

Definitions, statements and proofs. The format's hash is called by no term of this file: its digest
is a letter. The earlier mode's hash, a fixed function, is called in `publicOf`, and so in
`plannedAt` and `planZero`, at every c alike. Every statement is at a call with a layout file.

Main names.
 `plannedAt_entry`     `Model.Verify.planned_entry` (OnBytes/Model/VerifyDerives.lean) with the
                       digest a letter: the entry's parameter bytes in the plan at c are
                       `Params.entryParams` on the parameter file's lines and c.
 `EntryGround.link_atCfg`  `link_at` (OnBytes/K/Left/Conv.lean) with the digest a letter. Asked:
                       `plannedAt` returns p at c; the seven chains in p hold c and one shape, and
                       the entry's chain is read from its own bytes (`SameChains p c`,
                       OnBytes/Tie/SameChains.lean); c has 32 bytes; the parameter file says the
                       ground's lines. Then the entry's parameter bytes in p are the ground's at c,
                       the entry's chain is the ground's put at c, and the shape of the stored
                       tables is the ground's.
 `shortB`, `short_of_test`, `test_of_short`, `shortB_at`  a test: each of a plan's seven strings of
                       parameter bytes has fewer than 2 ^ 64 bytes; it has one value at a plan put
                       at two digests of one length.
 `planZero`            the plan at 32 zero bytes.
 `plannedAt_of_zero`, `plan_of_zero`  if `planZero` returns p₀ and the test says yes of p₀, then at
                       every c of 32 bytes `plannedAt` returns p₀ with c as its digest and the seven
                       chains put at c.
 `planZero_of`         the way back: from an answer at any c of 32 bytes with short strings.

Which fields of a plan hold the digest: by `plan_of_zero` and the text of `chainsAtCfg`: the field
cfg; the planner's own copy and its seven strings of parameter bytes; and, in each of the seven
chains as read back, the digest and the parameter bytes. The public part, the links as built, and
every chain's plan, items, sizes, codes and shapes are p₀'s at every c. That these hold no digest of
another kind is not said.

Why 32 zero bytes. The format keeps that string for "no digest": by the head of
OnBytes/Tie/ChainsAtCfg.lean three tests of the program refuse it as the digest of the public files.
These are tests of the readers. The planner does not make them: `chainsOf_at` holds at that string.
No proof here reads which string it is, only that it has 32 bytes.

Not claimed. That `planZero` returns on any files, or that the test says yes: both are values that
an evaluation can give; the verifier program runs neither. That 32 zero bytes are no answer of a
hash function. The public part is made with the earlier mode's hash, a fixed function, by the text
of `publicOf`. Nothing on the readers, on what the stages behind the planner do with the digest, or
on soundness. For proofs only; the program does not import this file.

Terms: lean/GLOSSARY.md.


-/
import OnBytes.Tie.ChainsAtCfg
import OnBytes.Tie.EntryGround
import OnBytes.Tie.SameChains
import OnBytes.Model.VerifyDerives

set_option autoImplicit false

namespace OnBytes.Tie

open OnBytes.Params (exc_bind)
open OnBytes.Model OnBytes.Model.Verify

/-- If `plannedAt` returns p at a digest c, then `Params.readLines` reads lines l from the parameter
file, the digest in p is c, and `Params.entryParams` on l and c returns the parameter bytes of the
entry's chain in p. -/
theorem plannedAt_entry {pol KL lay c : ByteArray} {p : Planned}
    (h : plannedAt pol KL (some lay) c = .ok p) :
    ∃ l rest, Params.readLines pol = .ok (l, rest) ∧ p.cfg = c ∧
      Params.entryParams l c = .ok (p.chains.bytes .link) := by
  unfold plannedAt at h
  obtain ⟨X, hX, h⟩ := exc_bind h
  obtain ⟨chains, hc, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  cases h
  obtain ⟨rest, hr⟩ := polScan_frame (publicOf_scan hX)
  obtain ⟨shapes, hm⟩ := chainsOf_made hc
  exact ⟨X.P.frame, rest, hr, rfl, Params.configure_entry hm⟩

/-- Where `plannedAt` returns p at a digest c of 32 bytes, `SameChains p c` holds and the parameter
file says the ground's lines: the parameter bytes of the entry's chain in p are the ground's at c,
the chain as read back is the ground's parameters put at c, and the shape of the stored tables is
the ground's. -/
theorem EntryGround.link_atCfg (G : EntryGround) {pol KL lay c : ByteArray} {p : Planned}
    (h : plannedAt pol KL (some lay) c = .ok p) (hs : SameChains p c) (hc : c.size = 32)
    (hl : G.SaysLines pol) :
    p.chains.bytes .link = G.bytesAt c ∧ p.chains.link = linkAtCfg G.q c ∧
      p.chains.tableShape = G.q.link.table := by
  obtain ⟨l, rest, h1, -, h2⟩ := plannedAt_entry h
  have el : l = G.lines := by
    unfold EntryGround.SaysLines at hl
    rw [h1] at hl
    exact Option.some.inj hl
  rw [el, G.params_at] at h2
  have eb : p.chains.bytes .link = G.bytesAt c := (Except.ok.inj h2).symm
  have h3 := hs.2.2
  rw [eb] at h3
  have eq : p.chains.link = linkAtCfg G.q c := Option.some.inj (h3.symm.trans (G.read_at c hc))
  refine ⟨eb, eq, ?_⟩
  rw [tableShape_oneTime, hs.2.1.1, eq]
  rfl

/-- A test on a plan: each of its seven strings of parameter bytes has fewer than 2 ^ 64 bytes. -/
def shortB (p : Planned) : Bool :=
  [ChainName.keyOneTime, .keyShared, .keySecond, .link, .proofFirst, .proofShared,
    .proofSecond].all fun n => decide ((p.chains.bytes n).size < 2 ^ 64)

/-- What a yes of the test says. -/
theorem short_of_test {p : Planned} (h : shortB p = true) (n : ChainName) :
    (p.chains.bytes n).size < 2 ^ 64 := by
  unfold shortB at h
  rw [List.all_eq_true] at h
  exact of_decide_eq_true (h n (by cases n <;> simp))

/-- Seven short strings give a yes of the test. -/
theorem test_of_short {p : Planned} (h : ∀ n : ChainName, (p.chains.bytes n).size < 2 ^ 64) :
    shortB p = true := by
  unfold shortB
  rw [List.all_eq_true]
  exact fun n _ => decide_eq_true (h n)

/-- At a plan put at two digests of one length the test has one value. -/
theorem shortB_at (p : Planned) (c c' : ByteArray) (h : c.size = c'.size) :
    shortB { p with cfg := c, chains := chainsAtCfg p.chains c } =
      shortB { p with cfg := c', chains := chainsAtCfg p.chains c' } := by
  unfold shortB
  refine congrArg _ (funext fun n => ?_)
  show decide (((chainsAtCfg p.chains c).bytes n).size < 2 ^ 64) =
    decide (((chainsAtCfg p.chains c').bytes n).size < 2 ^ 64)
  rw [size_bytes_chainsAtCfg_any p.chains c c' h n]

/-- The planner's text at 32 zero bytes in the place of the digest of the three public files. The
format keeps that string for "no digest": tests of the program's readers refuse it; the planner does
not read which string it is given. For statements only: the program does not call this function. -/
def planZero (pol KL lay : ByteArray) : Except String Planned :=
  plannedAt pol KL (some lay) Fmt.zero32

/-- If `planZero` returns p₀ with seven short strings, then at every digest c of 32 bytes
`plannedAt` returns p₀ with c as its digest and the seven chains put at c. -/
theorem plannedAt_of_zero {pol KL lay c : ByteArray} {p₀ : Planned}
    (h₀ : planZero pol KL lay = .ok p₀) (hb : shortB p₀ = true) (hc : c.size = 32) :
    plannedAt pol KL (some lay) c = .ok { p₀ with cfg := c, chains := chainsAtCfg p₀.chains c } :=
  plannedAt_at (Fmt.size_zeros 32) hc (short_of_test hb) h₀

/-- So whatever `plannedAt` returns at c is p₀ with c as its digest and the seven chains put at c:
all its other fields are p₀'s. Which fields of a chain `chainsAtCfg` turns is that definition's
text. -/
theorem plan_of_zero {pol KL lay c : ByteArray} {p₀ p : Planned}
    (h₀ : planZero pol KL lay = .ok p₀) (hb : shortB p₀ = true) (hc : c.size = 32)
    (h : plannedAt pol KL (some lay) c = .ok p) :
    p = { p₀ with cfg := c, chains := chainsAtCfg p₀.chains c } :=
  Except.ok.inj (h.symm.trans (plannedAt_of_zero h₀ hb hc))

/-- The way back: if `plannedAt` returns p at some digest c of 32 bytes, with seven short strings,
then `planZero` returns p put at 32 zero bytes, and the test says yes of that. -/
theorem planZero_of {pol KL lay c : ByteArray} {p : Planned} (hc : c.size = 32)
    (hb : shortB p = true) (h : plannedAt pol KL (some lay) c = .ok p) :
    planZero pol KL lay =
        .ok { p with cfg := Fmt.zero32, chains := chainsAtCfg p.chains Fmt.zero32 } ∧
      shortB { p with cfg := Fmt.zero32, chains := chainsAtCfg p.chains Fmt.zero32 } = true := by
  have h0 := plannedAt_at hc (Fmt.size_zeros 32) (short_of_test hb) h
  have hs := plannedAt_at hc hc (short_of_test hb) h
  have e : p = { p with cfg := c, chains := chainsAtCfg p.chains c } :=
    Except.ok.inj (h.symm.trans hs)
  refine ⟨h0, ?_⟩
  rw [shortB_at p Fmt.zero32 c ((Fmt.size_zeros 32).trans hc.symm), ← e]
  exact hb

end OnBytes.Tie
