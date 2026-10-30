-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/EntryAskedRoots.lean: the two roots that are read off the key file and the entry file by
plain readers, and that the tables of what the typing's asking half returns are these readers'.
Over OnBytes/Tie/EntryAsked.lean and LinkPlain.lean.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Tie.EntryAsked
import OnBytes.Tie.LinkPlain

set_option autoImplicit false

namespace OnBytes.Tie

open OnBytes.TwoPort

/-- The roots that are read off the files, at a tables' shape sh and a digest c: the first
table's, off the key file; the copy's, off the entry file. Plain and total; no hash is called. -/
def rtsE (sh : Params.IndexShape) (c key ent : ByteArray) : List (_root_.Iop.Dig 256) :=
  [Run.bytesToDig (keyAt sh c key).2.2.root, Run.bytesToDig (keyCAt sh c ent).2.2.root]

/-- Two roots. -/
theorem rtsE_length (sh : Params.IndexShape) (c key ent : ByteArray) :
    (rtsE sh c key ent).length = 2 := rfl

/-- What the asking half's value holds, at any function O in the place of the hash: the first table
is the one that was handed in, and the copy's is what the plain reader reads off the entry file. -/
theorem askedAt_tables {O : ByteArray → ByteArray} {q : Params.Link} {first : Params.TableName}
    {ent : ByteArray} {a : AskedE} (h : askedAt O q first ent = some a) :
    a.first = first ∧ furtherAt q.link.table ent = some a.further := by
  unfold askedAt at h
  obtain ⟨r, hr, h1⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨l0, -, h2⟩ := Option.bind_eq_some_iff.1 h1
  obtain ⟨l1, -, h3⟩ := Option.map_eq_some_iff.1 h2
  obtain ⟨P, hP, -, -, e3, -⟩ := (readWithR_iff _ _ _ _ _ _).1 hr
  subst h3
  exact ⟨rfl, by rw [e3]; exact entryPlaceR_furtherAt hP⟩

/-- For any plain map behind the asking half whose value's roots are the two tables': the roots
of what the typing returns are among the roots that are read off the files. `first` is the table
that the plain reader reads off the key file. -/
theorem typedER_named {Out : Type} (asm : AskedE → Option Out)
    (roots : Out → List (_root_.Iop.Dig 256))
    (hroots : ∀ a o, asm a = some o →
      roots o = [Run.bytesToDig a.first.root, Run.bytesToDig a.further.root])
    (g : Rom.Fam (Rom.rom 256)) (q : Params.Link) (c key ent : ByteArray) (o : Out)
    (h : (typedER asm q (keyAt q.link.table c key).2.2 ent).det g = some o) :
    ∀ r ∈ roots o, r ∈ rtsE q.link.table c key ent := by
  rw [typedER_det] at h
  obtain ⟨a, ha, ho⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨e1, e2⟩ := askedAt_tables ha
  rw [hroots a o ho, e1]
  unfold rtsE keyCAt
  rw [e2]
  exact fun r hr => hr

end OnBytes.Tie
