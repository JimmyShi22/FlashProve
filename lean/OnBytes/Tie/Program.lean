-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Program.lean: three of the program's calls, and the compiled verifier of the library's
theory.

The program has calls for single files: a proof file of each of the two small test protocols, and an
entry file (OnBytes/Shell/Toys.lean). This file proves for each of the three: if the call's verdict
is "accepted", then the program's reader reads a chain in the file, and the compiled verifier
accepts what was read (`CompiledAccepts`, `CompiledAcceptsX`). In a proof file the chain begins at
byte 0 and ends the file. In an entry file it begins at some byte offset j, which is not shown to be
the one that `Entry.check` used.

The hypotheses are a test on the description that can be evaluated, `limitsOfX` or `withinX`, and a
bound on the file's size.

Main definitions: `ProductTied`, `LinksTied`, `EntryTied`.
Main theorems: `product_compiled`, `links_compiled`, `entry_compiled`, under given parameter bytes;
`shell_product`, `shell_links`, `shell_entry`, for the calls, which derive these bytes from the
public files. A public file has a line "target", the number at which its run is sized. `bits`, the
first argument of `Shell.product`, `Shell.links` and `Shell.entry` (on the command line: `-bits N`),
is a floor: the derivation refuses a file whose target is below it (OnBytes/Plan/ToyRuns.lean).
The three calls are test commands. The call `entry` works under the test key's two public files. On
the commands that verify a model's files there is no theorem here.
This file claims nothing on soundness (OnBytes/Tie/OneChain.lean says why nothing follows). It has
no theorem on a key file or on a proof file of a batch.
-/
import OnBytes.Shell.Toys
import OnBytes.Chain.ReaderLaws
import OnBytes.Tie.OneChain
import OnBytes.Tie.EntryFile

set_option autoImplicit false

namespace OnBytes.Tie

/-- If the program's reader has read a chain that breaks no limit from the start of a file below
about 2^32 bytes, and the decision is yes, the compiled verifier accepts it. -/
theorem whole_compiled (c : Chain Unit) (file : ByteArray) (o : Fmt.ChainOut) (j : ℕ)
    (hr : readChain c.spec [] file 0 = some (o, j))
    (hd : c.dec () (Fmt.viewX c.spec o) = true) (hl : limitsOfX c.spec = [])
    (hs : file.size + 16 ≤ 2 ^ 32 - 144) : CompiledAccepts c.spec.base (c.dec ()) o := by
  rw [readChain_eq] at hr
  exact plain_compiled c.spec (c.dec ()) hl [] file 0 hs o j hr hd

/-- If the product test's verdict under given parameter bytes is "accepted", the file was read whole
as one chain. If that chain breaks no limit and the file is below about 2^32 bytes, the compiled
verifier accepts what was read. -/
theorem product_compiled (params file : ByteArray) (h : Toy.product params file = .accepted) :
    ∃ (c : Chain Unit) (o : Fmt.ChainOut),
      (Toy.ProductPublic.read params).bind Toy.productChain = some c ∧
      readChain c.spec [] file 0 = some (o, file.size) ∧
      (limitsOfX c.spec = [] → file.size + 16 ≤ 2 ^ 32 - 144 →
        CompiledAccepts c.spec.base (c.dec ()) o) := by
  unfold Toy.product at h
  split at h
  · cases h
  · rename_i c hc
    split at h
    · cases h
    · rename_i o j hr
      split at h
      · cases h
      · rename_i hj
        have hj' : j = file.size := by simpa using hj
        subst hj'
        split at h
        · rename_i hd
          rw [viewOf_eq] at hd
          exact ⟨c, o, hc, hr, fun hl hs => whole_compiled c file o _ hr hd hl hs⟩
        · cases h

/-- The same as `product_compiled`, for the chain of links. -/
theorem links_compiled (params file : ByteArray) (h : Toy.links params file = .accepted) :
    ∃ (c : Chain Unit) (o : Fmt.ChainOut),
      (Toy.LinksPublic.read params).bind Toy.linksChain = some c ∧
      readChain c.spec [] file 0 = some (o, file.size) ∧
      (limitsOfX c.spec = [] → file.size + 16 ≤ 2 ^ 32 - 144 →
        CompiledAccepts c.spec.base (c.dec ()) o) := by
  unfold Toy.links at h
  split at h
  · cases h
  · rename_i c hc
    split at h
    · cases h
    · rename_i o j hr
      split at h
      · cases h
      · rename_i hj
        have hj' : j = file.size := by simpa using hj
        subst hj'
        split at h
        · rename_i hd
          rw [viewOf_eq] at hd
          exact ⟨c, o, hc, hr, fun hl hs => whole_compiled c file o _ hr hd hl hs⟩
        · cases h

/-- If the verdict on an entry file under given parameter bytes is "accepted", the reader `readIn`
reads a chain under the description that `entrySpec` gives from some byte offset j of the file (not
shown to be the one that `Entry.check` used). Given `withinX` and a file below about 2^32 bytes, the
compiled verifier accepts what was read there. The first table is the one that the key file names;
the key file's own proofs are not checked by this call. The further table is the one that
`Entry.check` returns. -/
theorem entry_compiled (params key file : ByteArray)
    (h : Shell.entryUnder params key file = .accepted) :
    ∃ (first further : Params.TableName) (p : Params.Link) (block : Blk Unit) (S : Fmt.SpecX)
      (j : ℕ) (r : ChainRead) (s' : Session),
      Shell.firstTable params key = .ok first ∧ Entry.check params first file = .ok further ∧
      Params.Link.read params = some p ∧ entrySpec p first further = some (block, S) ∧
      readIn S file j Session.start = some (r, s') ∧
      (withinX S = true → file.size + 16 ≤ 2 ^ 32 - 144 →
        CompiledAcceptsX S (entryStatement first further) (block.decides (Entry.start p))
          first.root further.root r.out) := by
  unfold Shell.entryUnder at h
  split at h
  · cases h
  · rename_i first hf
    cases hc : Entry.check params first file with
    | error r => rw [hc] at h; cases h
    | ok further =>
      obtain ⟨p, block, S, j, r, s', hp, hS, hrd, himp⟩ :=
        entry_check_compiled params first further file hc
      have hok : S.ok = true := readX_ok Fmt.formatHash S _ file j _ (readIn_read S file j _ s' r hrd).1
      refine ⟨first, further, p, block, S, j, r, s', hf, hc, hp, hS, hrd,
        fun hw hb => himp hw (smallFX_of_withinX S hok hw file hb) ?_⟩
      unfold Shell.firstTable at hf
      split at hf
      · cases hf
      · split at hf
        · cases hf
        · split at hf
          · cases hf
          · rename_i table k ht
            injection hf with hf'
            rw [← hf']
            exact readTable_root _ _ _ _ _ _ ht

/-- A verdict behind a derivation is "accepted" only if the derivation has succeeded. -/
theorem derived_accepted {α : Type} (x : Except String α) (next : α → Verdict)
    (h : Shell.derived x next = .accepted) : ∃ a, x = .ok a ∧ next a = .accepted := by
  unfold Shell.derived at h
  split at h
  · cases h
  · exact ⟨_, rfl, h⟩

/-- What is proved of the call on a proof file of the product test. The derivation of the parameter
bytes from `pub` under the floor `bits` has succeeded. The program's reader has read the whole file
as one chain under the program's description. If that description breaks no limit and the file is
below about 2^32 bytes, the compiled verifier accepts what was read. -/
def ProductTied (bits : ℕ) (pub file : ByteArray) : Prop :=
  ∃ r, Plan.productRun pub bits = .ok r ∧
    ∃ (c : Chain Unit) (o : Fmt.ChainOut),
      (Toy.ProductPublic.read r.params).bind Toy.productChain = some c ∧
      readChain c.spec [] file 0 = some (o, file.size) ∧
      (limitsOfX c.spec = [] → file.size + 16 ≤ 2 ^ 32 - 144 →
        CompiledAccepts c.spec.base (c.dec ()) o)

/-- The same for the call on a proof file of the chain of links. -/
def LinksTied (bits : ℕ) (pub file : ByteArray) : Prop :=
  ∃ r, Plan.linksRun pub bits = .ok r ∧
    ∃ (c : Chain Unit) (o : Fmt.ChainOut),
      (Toy.LinksPublic.read r.params).bind Toy.linksChain = some c ∧
      readChain c.spec [] file 0 = some (o, file.size) ∧
      (limitsOfX c.spec = [] → file.size + 16 ≤ 2 ^ 32 - 144 →
        CompiledAccepts c.spec.base (c.dec ()) o)

/-- What is proved of the call on an entry file. The derivation of the parameter bytes from the two
public files under the floor `bits` has succeeded. The first table is the one that the key file
names, the further table the one that `Entry.check` returns. The reader `readIn` reads a chain under
the description that `entrySpec` gives, from some byte offset j of the file. The statement does not
name j, so j is not shown to be the offset that `Entry.check` used, and it does not say that the
chain ends the file. (`entry_read_spec` says that the chain which `Entry.read` returns is such a
reading; it names no offset and no end either.) If that description is within the limits and the
file is below about 2^32 bytes, the compiled verifier accepts what was read, under the two tables'
roots. -/
def EntryTied (bits : ℕ) (pub1 pub2 key file : ByteArray) : Prop :=
  ∃ c, Plan.toyForCommitters pub1 pub2 bits = .ok c ∧
    ∃ (first further : Params.TableName) (p : Params.Link) (block : Blk Unit) (S : Fmt.SpecX)
      (j : ℕ) (r : ChainRead) (s' : Session),
      Shell.firstTable c.entryLink key = .ok first ∧
      Entry.check c.entryLink first file = .ok further ∧
      Params.Link.read c.entryLink = some p ∧ entrySpec p first further = some (block, S) ∧
      readIn S file j Session.start = some (r, s') ∧
      (withinX S = true → file.size + 16 ≤ 2 ^ 32 - 144 →
        CompiledAcceptsX S (entryStatement first further) (block.decides (Entry.start p))
          first.root further.root r.out)

/-- If the call on a proof file of the product test says "accepted", `ProductTied` holds. -/
theorem shell_product (bits : ℕ) (pub file : ByteArray)
    (h : Shell.product bits pub file = .accepted) : ProductTied bits pub file := by
  obtain ⟨r, hr, ha⟩ := derived_accepted _ _ h
  exact ⟨r, hr, product_compiled r.params file ha⟩

/-- If the call on a proof file of the chain of links says "accepted", `LinksTied` holds. -/
theorem shell_links (bits : ℕ) (pub file : ByteArray)
    (h : Shell.links bits pub file = .accepted) : LinksTied bits pub file := by
  obtain ⟨r, hr, ha⟩ := derived_accepted _ _ h
  exact ⟨r, hr, links_compiled r.params file ha⟩

/-- If the call on an entry file says "accepted", `EntryTied` holds. -/
theorem shell_entry (bits : ℕ) (pub1 pub2 key file : ByteArray)
    (h : Shell.entry bits pub1 pub2 key file = .accepted) : EntryTied bits pub1 pub2 key file := by
  obtain ⟨c, hc, ha⟩ := derived_accepted _ _ h
  exact ⟨c, hc, entry_compiled c.entryLink key file ha⟩

end OnBytes.Tie

#print axioms OnBytes.Tie.shell_product
#print axioms OnBytes.Tie.shell_links
#print axioms OnBytes.Tie.shell_entry
#print axioms OnBytes.Tie.product_compiled
#print axioms OnBytes.Tie.links_compiled
#print axioms OnBytes.Tie.entry_compiled
