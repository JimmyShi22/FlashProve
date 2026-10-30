-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/ToysClosed.lean: the two small test protocols' theorems at the C++ programs' parameters,
with no test left to run.

The two protocols are the product test (OnBytes/Toy/Product.lean) and the chain of links
(OnBytes/Toy/Links.lean). The theorems of OnBytes/Tie/Program.lean on them have a test as a
hypothesis: the chain's description breaks no limit (OnBytes/Tie/Limits.lean names the limits;
OnBytes/Tie/OneChain.lean says what the compiled verifier is).
Here that test is a theorem, for both protocols, each at the tiny and at
the full parameters of the C++ programs. So at these parameter bytes the theorems on the program's
verdicts hold for every file, with one hypothesis on the input alone, a bound on the file's size:
`file.size + 16 ≤ 2 ^ 32 - 144`. The format's hash takes at most 2^32 - 144 bytes (`Fmt.hDom`), and
the library asks for 16 bytes of room (`Run.smallB`).

Main definition: `ToyTied`.
Main theorems: `limits_product_tiny`, `limits_product_full`, `limits_links_tiny`,
`limits_links_full`; `product_tiny`, `product_full`, `links_tiny`, `links_full`. Beside them
`once_product_tiny` and its three kin: each of the four descriptions opens every tree that it sends
exactly once, which the limits do not ask.
It claims nothing on soundness. The parameter bytes are the library's own spelling (the field
`params` of its descriptions). That they are the bytes that the C++ programs wrote is tested by
evaluation (Fmt/M1TheirsSpec.lean, Fmt/M2Theirs.lean), not proved. That each theorem has a case, an honest file
that the program accepts, is tested too (OnBytes/Tie/TestCalls.lean, TestCallsFull.lean). The program's
own calls take a floor `bits` and refuse a public file whose target is below it
(OnBytes/Tie/Program.lean). At the tiny parameters they accept with `bits` 0 and do not accept with
128 (OnBytes/Tie/TestCalls.lean); at the full ones they accept with 128 (TestCallsFull.lean).
-/
import Fmt.M1SpecKnownProofs
import Fmt.M2SpecKnown
import OnBytes.Params.ToyDescriptions
import OnBytes.Tie.Program

set_option autoImplicit false

namespace OnBytes.Tie

/-- A description in order whose random bytes are in the file, and which meets the three limits
that look at the rounds alone, breaks no limit. -/
theorem limits_of (S : Fmt.Spec) (hok : S.ok = true) (hr : S.rand = .inFile)
    (h : (oneRoot S && ownOnly S && atMostOnce S) = true) : limitsOf S = [] := by
  have e : inFile S = S := by
    unfold inFile
    rw [← hr]
  simp only [Bool.and_eq_true] at h
  rw [← within_iff, within_eq, e, hok, h.1.1, h.1.2, h.2, hr]
  rfl

/-- The product test at the tiny parameters breaks no limit. -/
theorem limits_product_tiny : limitsOf Fmt.M1.Theirs.specTiny = [] :=
  limits_of _ Fmt.M1.theirs_spec.1 rfl (by decide +kernel)

/-- The product test at the full parameters breaks no limit. -/
theorem limits_product_full : limitsOf Fmt.M1.Theirs.specFull = [] :=
  limits_of _ Fmt.M1.theirs_spec.2.1 rfl (by decide +kernel)

/-- The chain of links at the tiny parameters breaks no limit. -/
theorem limits_links_tiny : limitsOf Fmt.M2.Theirs.specTiny = [] :=
  limits_of _ Fmt.M2.ok_tiny rfl (by decide +kernel)

/-- The chain of links at the full parameters breaks no limit. -/
theorem limits_links_full : limitsOf Fmt.M2.Theirs.specFull = [] :=
  limits_of _ Fmt.M2.ok_full rfl (by decide +kernel)

/-- The product test at the tiny parameters opens each tree that it sends exactly once. -/
theorem once_product_tiny : eachOnce Fmt.M1.Theirs.specTiny = true := by decide +kernel

/-- So does the product test at the full parameters. -/
theorem once_product_full : eachOnce Fmt.M1.Theirs.specFull = true := by decide +kernel

/-- So does the chain of links at the tiny parameters. -/
theorem once_links_tiny : eachOnce Fmt.M2.Theirs.specTiny = true := by decide +kernel

/-- So does the chain of links at the full parameters. -/
theorem once_links_full : eachOnce Fmt.M2.Theirs.specFull = true := by decide +kernel

/-- `SpecX.plain S` breaks the limits that S breaks and no other. -/
theorem limitsX_plain (S : Fmt.Spec) : limitsOfX (Fmt.SpecX.plain S) = limitsOf S := by
  have h : (Fmt.SpecX.plain S).stored.all (·.isEmpty) = true := by
    show (S.rounds.map fun _ => ([] : List Fmt.Stored)).all (·.isEmpty) = true
    rw [List.all_eq_true]
    intro x hx
    obtain ⟨_, _, rfl⟩ := List.mem_map.1 hx
    rfl
  unfold limitsOfX
  rw [if_pos h, List.append_nil]
  rfl

/-- What is proved of a file of a test protocol at a description S that breaks no limit: the
program's reader has read the whole file as one chain under S, and the compiled verifier of the
protocol made from S and the program's decision accepts what was read. -/
def ToyTied (S : Fmt.Spec) (c : Chain Unit) (file : ByteArray) : Prop :=
  c.spec = Fmt.SpecX.plain S ∧ ∃ o : Fmt.ChainOut,
    readChain (Fmt.SpecX.plain S) [] file 0 = some (o, file.size) ∧ CompiledAccepts S (c.dec ()) o

/-- The step that the four theorems below share: from what `product_compiled` or `links_compiled`
concludes to `ToyTied`. -/
theorem toy_tied (S : Fmt.Spec) (hl : limitsOf S = []) (c : Chain Unit) (o : Fmt.ChainOut)
    (file : ByteArray) (hs : c.spec = Fmt.SpecX.plain S)
    (hr : readChain c.spec [] file 0 = some (o, file.size))
    (hb : file.size + 16 ≤ 2 ^ 32 - 144)
    (himp : limitsOfX c.spec = [] → file.size + 16 ≤ 2 ^ 32 - 144 →
      CompiledAccepts c.spec.base (c.dec ()) o) : ToyTied S c file := by
  have h1 := himp (by rw [hs, limitsX_plain, hl]) hb
  rw [hs] at h1 hr
  exact ⟨hs, o, hr, h1⟩

/-- At the product test's tiny parameters, `ToyTied` holds of every file below about 2^32 bytes that
the program accepts. -/
theorem product_tiny (file : ByteArray) (hb : file.size + 16 ≤ 2 ^ 32 - 144)
    (h : Toy.product Fmt.M1.Theirs.specTiny.params file = .accepted) :
    ∃ c, (Toy.ProductPublic.read Fmt.M1.Theirs.specTiny.params).bind Toy.productChain = some c ∧
      ToyTied Fmt.M1.Theirs.specTiny c file := by
  obtain ⟨c, o, hc, hr, himp⟩ := product_compiled _ file h
  exact ⟨c, hc, toy_tied _ limits_product_tiny c o file (Params.product_spec_tiny hc) hr hb himp⟩

/-- The same as `product_tiny`, at the full parameters. -/
theorem product_full (file : ByteArray) (hb : file.size + 16 ≤ 2 ^ 32 - 144)
    (h : Toy.product Fmt.M1.Theirs.specFull.params file = .accepted) :
    ∃ c, (Toy.ProductPublic.read Fmt.M1.Theirs.specFull.params).bind Toy.productChain = some c ∧
      ToyTied Fmt.M1.Theirs.specFull c file := by
  obtain ⟨c, o, hc, hr, himp⟩ := product_compiled _ file h
  exact ⟨c, hc, toy_tied _ limits_product_full c o file (Params.product_spec_full hc) hr hb himp⟩

/-- The same as `product_tiny`, for the chain of links at the tiny parameters. -/
theorem links_tiny (file : ByteArray) (hb : file.size + 16 ≤ 2 ^ 32 - 144)
    (h : Toy.links Fmt.M2.Theirs.specTiny.params file = .accepted) :
    ∃ c, (Toy.LinksPublic.read Fmt.M2.Theirs.specTiny.params).bind Toy.linksChain = some c ∧
      ToyTied Fmt.M2.Theirs.specTiny c file := by
  obtain ⟨c, o, hc, hr, himp⟩ := links_compiled _ file h
  exact ⟨c, hc, toy_tied _ limits_links_tiny c o file (Params.links_spec_tiny hc) hr hb himp⟩

/-- The same as `product_tiny`, for the chain of links at the full parameters. -/
theorem links_full (file : ByteArray) (hb : file.size + 16 ≤ 2 ^ 32 - 144)
    (h : Toy.links Fmt.M2.Theirs.specFull.params file = .accepted) :
    ∃ c, (Toy.LinksPublic.read Fmt.M2.Theirs.specFull.params).bind Toy.linksChain = some c ∧
      ToyTied Fmt.M2.Theirs.specFull c file := by
  obtain ⟨c, o, hc, hr, himp⟩ := links_compiled _ file h
  exact ⟨c, hc, toy_tied _ limits_links_full c o file (Params.links_spec_full hc) hr hb himp⟩

end OnBytes.Tie

#print axioms OnBytes.Tie.product_tiny
#print axioms OnBytes.Tie.product_full
#print axioms OnBytes.Tie.links_tiny
#print axioms OnBytes.Tie.links_full
#print axioms OnBytes.Tie.limits_product_full
#print axioms OnBytes.Tie.limits_links_full
