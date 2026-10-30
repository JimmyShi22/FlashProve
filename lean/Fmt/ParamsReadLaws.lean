-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/ParamsReadLaws.lean: reading the parameter bytes undoes their spelling: the statement, and the
bounds under which it is made.

The parameter bytes of a chain are the spelling (the encoding as bytes: `Params.bytes`,
Fmt/ParamsRead.lean) of the format's version, the plan (`Plan`, Fmt/Plan.lean), the configuration's
digest and the further items; `paramsRead` is their reader (decoder).

Why. The format page (docs/format/FORMAT.md; not held against the page as it ships), as this file
reads it, asks that whatever a verifier's decision reads, beside the two parties' messages, is read
out of the items of its chain's first query or computed from them. A run at a description (`Spec`,
Fmt/Rules8.lean) that was written down from sizes meets that only together with the fact that the
reader of the parameter bytes (Fmt/ParamsRead.lean: `paramsRead`) gives these very parameters back.
This file states that fact for all parameters within bounds. The proof is in
Fmt/ParamsReadLawsProofs.lean. No Mathlib.

1. What the file contains. Definitions that can be evaluated.
   The bounds, each a test that can be run. They are wider than the format's own bounds (the page
     limits the parameter bytes far below), on purpose; they ask only what spelling needs: that each
     number can be written in its word, each name in the page's characters; and the digest's 32
     bytes, which the reader asks. So the statement covers every set of parameters of the format,
     and more; fit is not the page's test.
   `okName s`: every character of the name lies from 0x20 to 0x7E (the page's rule on names).
   `nameFit s`: okName s, and the name has fewer than 2^64 bytes.
   `Entry.fit e`: nameFit of its name; each of its eleven words (`Entry.words`) is below 2^64.
   `Plan.fit P`: the bytes of the salt, of the nonce and of a listed position, the answers to a
     sample, the word "saved" and the number of entries are each below 2^64; every entry fits.
   `Params.fit p`: the plan fits; the configuration's digest has 32 bytes; every further item has a
     name that fits and a value of fewer than 2^64 bytes.

2. What is checked when the file compiles. Five tests (#guard).

3. Theorem stated.
   `Spec.params_back`: p.fit = true → paramsRead p.bytes = some p. (p.bytes: Fmt/ParamsRead.lean:
     the spelling by Fmt/Rules4.lean's `paramsBytes`.)

4. What is not claimed.
   The other direction is not claimed (what paramsRead accepts is spelled so, and in no other way).
   Nothing is claimed on whether a plan is a plan of the format (`Plan.ok`, Fmt/Rules4.lean;
     `Spec.ok`, Fmt/Rules8.lean): fit bounds sizes and names alone; a plan with a word "saved" of 7
     fits.
   It is not claimed that the bounds are needed. The reasons for them are given, not proved: a word
     of 2^64 or more is spelled modulo 2^64, so there the statement is false; for names outside the
     range the reader refuses. The last test evaluates one case, a salt of 2^64.

Terms: lean/GLOSSARY.md.
-/
import Fmt.ParamsRead

namespace Fmt

/-- A name within the page's rule: every character from 0x20 to 0x7E. -/
def okName (s : String) : Bool :=
  s.toList.all fun c => decide (32 ≤ c.toNat) && decide (c.toNat ≤ 126)

def nameFit (s : String) : Bool := okName s && decide ((ascii s).size < 2 ^ 64)

/-- the eleven words of an entry, in the page's order -/
def Entry.words (e : Entry) : List Nat :=
  [e.count, e.work, e.msg, e.roots, e.answers, e.drawE, e.drawNZ, e.poss, e.logN, e.trits, e.rows]

def Entry.fit (e : Entry) : Bool := nameFit e.name && e.words.all fun n => decide (n < 2 ^ 64)

def Plan.fit (P : Plan) : Bool :=
  ([P.salt, P.nonce, P.posB, P.samples, P.saved, P.entries.length].all fun n =>
      decide (n < 2 ^ 64)) &&
    P.entries.all Entry.fit

def Params.fit (p : Params) : Bool :=
  p.plan.fit && p.cfg.size == 32 && p.others.all fun x => nameFit x.1 && decide (x.2.size < 2 ^ 64)

/-- States that reading undoes spelling, for the parameters with `Params.fit`. -/
def Spec.params_back : Prop := ∀ p : Params, p.fit = true → paramsRead p.bytes = some p

-- the tests run: the page's toy plan of six rounds fits, both fields; a name with a line feed, a word of 2^64, a digest of 31 bytes do not
#guard [Fld.one, Fld.two].all fun f => (Params.fit ⟨Toy4.plan f, Toy4.cfg, [("toy: a table's length", u64n 1024)]⟩)
#guard !okName "a\nb" && okName "the format's version" && okName ""
#guard !(Entry.fit { name := "x", msg := 2 ^ 64 }) && Entry.fit { name := "x", msg := 2 ^ 64 - 1 }
#guard !(Params.fit ⟨Toy4.plan .two, zeroBytes 31, []⟩)
-- one case where the bound on words is needed: at a word of 2^64 the reader gives another plan back
-- (salt 0)
#guard ((paramsRead (Params.bytes ⟨{ Toy4.plan .two with salt := 2 ^ 64 }, Toy4.cfg, []⟩)).map (·.plan.salt)) == some 0

end Fmt
