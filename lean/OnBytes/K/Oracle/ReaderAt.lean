-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Oracle/ReaderAt.lean: the reader that asks the oracle, at a ground.

 `tyAt` at a digest c: the key file's table by a plain parse (`keyAt`); then THE ASKING HALF
     (`askedE`, `typedER`, OnBytes/Tie/EntryAsked.lean): a twin of the program's reading of an entry
     file, and both tables' seeds, with every hash asked of the oracle; then the typed value that is
     made of what it returns (`valueOf`, a plain function).
 `readerOf` `HomeData.Reader` (OnBytes/K/Oracle/Frame.lean) at these terms: c is the oracle's own
     value at the public string of the three public files; the roots are read off the two files
     without a query (`rtsE`); it asks at most `typedT` strings, one number at every digest, key
     file and entry file (OnBytes/Tie/EntryAskedCost.lean).
 `twin_at_port`   how the twin is tied to the program's reader.
 `tyAt_det`, `tyAt_roots`, `tyAt_asks`, `valueOf_roots`   the steps.

What the asking half is. Its reading of the entry file is A TWIN of the program's reader: the same
text written once more with the hash as an argument (`M.Entry.read`,
OnBytes/ChecksWithHashAsArgument/M/Entry/File.lean), here at the asking monad. Which text the program runs on a
model's entry file follows from what OnBytes/Main.lean calls: `Entry.read`
(OnBytes/Entry/File.lean), of which that is a twin, or that same definition at the identity monad
and the program's own hash. With the program's hash put in, the twin is `Entry.read` on every file
(`twin_at_port`: no condition). At the oracle made from the format's hash, at which the checker runs
in `EntryArmO.zero`, it returns what the program's reader returns for digests and roots of 32 bytes
and files within the format's limits (`readWithR_reader`, OnBytes/Tie); every call at the setting's
lines on which the program says yes is within them (`asked_conv`, OnBytes/K/Oracle/AskedAt.lean).
The parameters' digest too is asked. Of what the format's hash is made of, the definitions of the
asking half, of the whole checker at both sizes and of the event of `EntryArmO.sound` reach nothing:
a program's walk over Lean's environment, no theorem; such a walk cannot see what comes in as data
(the digest c), nor a second writing of the hash under other names. The seeds are then asked once
more by a third text (`seedsBy`: the text of the program's derivation of a record's seeds over a
variable hash). The program calls neither the asking half, nor the checker, nor `seedsBy`; whether
it calls the twin's definition follows from what OnBytes/Main.lean calls.

The reader and the page are fed from the same two tables: the digest c of the three public files and
the parameters' digest in the compiled verifier's page are the oracle's own values at the public
strings (OnBytes/TypedOracleCompiler/Slice/EntryHome.lean), which are what the reader's own questions at these
strings are answered with. For the parameters' digest that is a theorem: under every oracle, the
digest in what the asking half returns is the value that `HomeData.atR` hands to the page
(`asked_pin`, OnBytes/K/Oracle/AskedPd.lean).

What is not claimed. That it asks what the program hashes. That the key file's table has passed the
program's check of the key file: it is parsed, no more. Nothing on a probability. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Oracle.Frame
import OnBytes.TypedOracleCompiler.Slice.EntryVerdict
import OnBytes.TypedOracleCompiler.Slice.EntryTop
import OnBytes.Tie.EntryAskedCost
import OnBytes.Tie.EntryAskedRoots
import OnBytes.ChecksWithHashAsArgument.M.AtPort.Files

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Oracle
open Rom Prob Cb _root_.Compile TypedOracleCompiler.Slice
open OnBytes.Tie (EntryGround linkAtCfg keyAt keyCAt furtherAt AskedE askedAt askedAt_tables typedER
  typedER_det typedT rtsE rtsE_length)
open OnBytes.Slice (Tab)
open OnBytes.Slice.Shapes (Files Size Cfg dgOf dgOf_size pubS₀ pubS₁)
open OnBytes.Slice.Shapes.FileSpec (own₀ own₁)
open scoped ENNReal

/-- **The twin of the program's reading of an entry file, with the program's hash put in, is the
program's reading, on every file.** (`AtPort.entryRead_port`, said once more here so that it stands
in this file's cone.) -/
theorem twin_at_port (p : Params.Link) (first : Params.TableName) (file : ByteArray) :
    OnBytes.TwoPort.M.Entry.read (m := Id) OnBytes.formatHashFastForm p first file =
      OnBytes.Entry.read p first file :=
  OnBytes.TwoPort.M.AtPort.entryRead_port p first file

variable (G : EntryGround)
  (hok : ∀ c : ByteArray, c.size = 32 → TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true)
  (eM : ℕ) (cfg : Cfg)

/-- **The reader at a digest**: the key file's table by a plain parse; THE ASKING HALF
(`askedE`, OnBytes/Tie/EntryAsked.lean): the twin of the program's reading of an entry file and both
tables' seeds, every hash asked of the oracle; then the typed value that is made of what it
returns. -/
def tyAt (c : ByteArray) (hc : c.size = 32) (d : Files) :
    OComp (rom 256) (Option ((homeOf G hok eM).OutC c hc)) :=
  typedER (fun a => valueOf G hok eM a c hc d) (linkAtCfg G.q c)
    (keyAt G.q.link.table c d.key).2.2 d.ent

/-- Its value under an oracle. -/
theorem tyAt_det (c : ByteArray) (hc : c.size = 32) (d : Files) (g : Fam (rom 256)) :
    (tyAt G hok eM c hc d).det g =
      (askedAt (_root_.Run.oB (g ())) (linkAtCfg G.q c) (keyAt G.q.link.table c d.key).2.2
        d.ent).bind fun a => valueOf G hok eM a c hc d :=
  typedER_det _ g _ _ _

/-- What is made of a plain value has that value's two roots. -/
theorem valueOf_roots (a : AskedE) (c : ByteArray) (hc : c.size = 32) (d : Files)
    (o : (homeOf G hok eM).OutC c hc) (h : valueOf G hok eM a c hc d = some o) :
    o.1 = [_root_.Run.bytesToDig a.first.root, _root_.Run.bytesToDig a.further.root] := by
  obtain ⟨π, -, hπ⟩ := Option.map_eq_some_iff.1 h
  exact (congrArg Prod.fst hπ).symm

/-- Under every oracle: what the reader returns has two roots, and they are the roots that are read
off the files without a query. -/
theorem tyAt_roots (c : ByteArray) (hc : c.size = 32) (d : Files) (g : Fam (rom 256))
    (o : (homeOf G hok eM).OutC c hc) (h : (tyAt G hok eM c hc d).det g = some o) :
    o.1.length = 2 ∧ rtsE G.q.link.table c d.key d.ent = o.1 := by
  rw [tyAt_det] at h
  obtain ⟨a, ha, hv⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨h1, h2⟩ := askedAt_tables ha
  have hr := valueOf_roots G hok eM a c hc d o hv
  have h2' : furtherAt G.q.link.table d.ent = some a.further := h2
  refine ⟨?_, ?_⟩
  · rw [hr]
    rfl
  · unfold rtsE keyCAt
    rw [h2', hr, h1]
    rfl

/-- It tosses no coin and asks at most `typedT` strings. -/
theorem tyAt_asks (c : ByteArray) (hc : c.size = 32) (d : Files) :
    (tyAt G hok eM c hc d).NoCoin ∧
      (tyAt G hok eM c hc d).QueryBound (typedT G.q.link.table G.rs) :=
  G.typedER_asks _ c _ d.ent

/-- **THE READER THAT ASKS THE ORACLE, AT A GROUND.** It asks at most `typedT` strings, one number
at every digest, every key file and every entry file. -/
def readerOf : (homeOf G hok eM).Reader cfg (typedT G.q.link.table G.rs) where
  ty := fun T₀ _ d => tyAt G hok eM (dgOf cfg T₀) (dgOf_size cfg T₀) d
  rts := fun T₀ _ d => rtsE G.q.link.table (dgOf cfg T₀) d.key d.ent
  noCoin := fun T₀ _ d => (tyAt_asks G hok eM (dgOf cfg T₀) (dgOf_size cfg T₀) d).1
  queries := fun T₀ _ d => (tyAt_asks G hok eM (dgOf cfg T₀) (dgOf_size cfg T₀) d).2
  roots := fun T₀ _ g d o h => tyAt_roots G hok eM (dgOf cfg T₀) (dgOf_size cfg T₀) d g o h
  few := fun T₀ _ d => le_of_eq (rtsE_length G.q.link.table (dgOf cfg T₀) d.key d.ent)

end OnBytes.K.Oracle
