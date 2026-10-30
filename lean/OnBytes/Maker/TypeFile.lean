-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/TypeFile.lean: the typing of a whole file from what was read: the tables of
OnBytes/Maker/Tables.lean laid into `toBPrfW` (OnBytes/Maker/TypingW.lean), at the data that
OnBytes/Maker/WholeOf.lean makes of the three chains' plain data.

Main definition. `typeFile`: from the plain data `W` of a file's three chains, the stored table's
depth `a`, the plan's bytes of a salt, the configuration's digest, the plain parts of the three
silent rounds, the salt and the siblings of the leaf in the binding tree, and the three chains as
read: the proof string of the joined protocol. It returns nothing where the chains as read do not
fit the data, an opening fails the parser's tests, a vertex of a path lacks, a sender has no run's
value, one position is opened twice with two columns or two salts, or a plain part does not type.
Main theorem. `typeFile_some`: what a value is made of.

The paths in the openings are whole paths: at each listed position the siblings from the leaf up,
taken from the vertices that the reader has met in that opening (`tabsWFull`, `extWFull`). A tree of
a file can be read at two lists of positions, each opening pruned against its own list, while the
joined protocol's verifier walks all read positions of a tree together: a whole path is the true
sibling at every level, whatever the union is.

What is not said: the head of OnBytes/Maker/TypingW.lean. The salt and the siblings of the leaf in
the binding tree are the caller's: the reading `Proof.TailRead` does not hold them, and nothing here
tests their number or lengths. The tests on the data (`Whole.fits`, `storedFit`, `countsFit`) are
not called here: they are owed by whoever gives `W`. That the whole paths agree with the
vertices that the verifier's walk computes.


-/
import OnBytes.Maker.TypingW
import OnBytes.Maker.Tables
import OnBytes.Maker.WholeOf

set_option autoImplicit false

namespace OnBytes.Maker

open _root_.Run _root_.Run.PQ
open TypedOracleCompiler.Compile.Batch (OneProtocolProof)

section
variable {TF TJ T3 Xi : Type} (C : CK) (a : ℕ) (W : Three.Whole) (tF : TF) (tJ : TJ) (t3 : T3)
  (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)

/-- **The typing of a whole file, from what was read.** salt, path: the salt and the siblings of the
leaf in the binding tree, which `Proof.Place` does not keep: the caller reads them. -/
def typeFile (saltBytes : ℕ) (cfg : ByteArray) (pF : TF) (pJ : TJ) (p3 : T3) (salt : ByteArray)
    (path : List ByteArray) (r : Proof.TailRead) :
    Option (OneProtocolProof 256 (wholeDesc C (WholeD.of a W) tF tJ t3 silent run).batch) :=
  (tabsWFull W saltBytes r).bind fun tabs =>
    (extWFull a cfg W r).bind fun ext =>
      toBPrfW C (WholeD.of a W) tF tJ t3 silent run pF pJ p3 tabs ext salt path r

theorem typeFile_some (saltBytes : ℕ) (cfg : ByteArray) (pF : TF) (pJ : TJ) (p3 : T3)
    (salt : ByteArray) (path : List ByteArray) (r : Proof.TailRead) (π)
    (h : typeFile C a W tF tJ t3 silent run saltBytes cfg pF pJ p3 salt path r = some π) :
    ∃ tabs ext, tabsWFull W saltBytes r = some tabs ∧ extWFull a cfg W r = some ext ∧
      toBPrfW C (WholeD.of a W) tF tJ t3 silent run pF pJ p3 tabs ext salt path r = some π := by
  unfold typeFile at h
  obtain ⟨tabs, ht, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨ext, he, h⟩ := Option.bind_eq_some_iff.1 h
  exact ⟨tabs, ext, ht, he, h⟩

end

end OnBytes.Maker
