-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TieK/HolesOfChains.lean: two of the five named hypotheses of OnBytes/K/TopVC.lean, stated
from the flat records of a file's three chains.

`K.Holes5` names five hypotheses. Two of them speak of a file with three chains: `test` (the key
file) and `session` (the proof file). Each begins at `K.PortYesAt`, which holds the yes of the
program's check of that file as one equation. Here each is stated anew from what that yes
establishes, laid open: `KeyOpened`, `ProofOpened` (OnBytes/TieK/PortChains.lean). The two forms of
`K.Holes5` follow from the new ones.

Main names:
  `TestOfChains V R`: where the key file's three chains were read and judged as `KeyOpened` says,
    the fixed reading gives the program's own table and a typed string, and Test says yes.
  `SessionOfChains V R`: where the entry file gave the further table and the proof file's three
    chains were read and judged as `ProofOpened` says, the request and the reply are read as an
    instance, the fixed reading gives a typed string, and the session says yes.
  `HolesC V R`: the five, with these two in the place of `test` and `session`.
  `holes5_of_chains`: `HolesC V R` gives `K.Holes5 V R`.
Limits: both are hypotheses; nothing here shows that they hold at any shape. Both conclude that the
fixed reading returns a typed string at every file whose chains the program has read and judged. The
program ties two openings of one position by their digests alone, and a typed string has one opening
at a position. So a file that lists one position twice, with two openings of one digest, may be
accepted while a reading that makes typed strings returns nothing: of such a reading these two forms
are not the ones to prove; a form that ends in a second arm on the file is. Each asks more than the
form in `K.Holes5`. Of `K.PortYesAt`, `TestOfChains` keeps `KeyOpened` and `K.IdIs` alone;
`SessionOfChains` keeps `EntryGave`, at any first table, and `ProofOpened` alone. Dropped: the other
files' checks; the size bounds of the entry file and of the five further files (the three public
files, the request, the reply); the stages' accounts; the request's stage. At a shape whose third
protocol were made of the real ends' block alone they would hold within them that this block has the
same rounds as the dry ends'; no theorem states that. At a shape that takes the rounds from the dry
ends' block and the decision from the real ends', as the program does, nothing of the kind is asked.
The hash is fixed in both: `KeyOpened`, `ProofOpened` and `K.PortYesAt` speak of the program's own
readers (`readChain`, OnBytes/Chain/Reader.lean), which take no hash as an argument. None is drawn,
and there is no probability.
Nothing on soundness. The program does not import this file.

-/
import OnBytes.K.TopVC
import OnBytes.TieK.ReadThree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.TieK
open OnBytes.K (Shape Reading5 Holes5 PortYesAt stmOf)
open _root_.Run (bytesToDig)

/-- Test, from the key file's three chains. -/
def TestOfChains (V : Shape) (R : Reading5 V) : Prop :=
  ∀ F o id table r, o.id = some id → o.bits = 128 → V.Served (stmOf F o) →
    V.recOf (stmOf F o) table = some r → K.IdIs (stmOf F o) table → KeyOpened F table →
    ∃ πT, R.key (stmOf F o) F.key = some (table, πT) ∧
      V.vT (stmOf F o) (bytesToDig table.root) r πT = true

/-- The session, from the proof file's three chains. -/
def SessionOfChains (V : Shape) (R : Reading5 V) : Prop :=
  ∀ F o id table further r', o.id = some id → o.bits = 128 → V.Served (stmOf F o) →
    V.recOf (stmOf F o) further = some r' → EntryGave F table further → ProofOpened F further →
    ∃ i πB, V.insOf (stmOf F o) = some i ∧ R.prf (stmOf F o) F.ent F.proof F.entry = some πB ∧
      V.vB (stmOf F o) (bytesToDig further.root) i r' πB = true

/-- Where the program says yes, the entry file has given the further table. -/
theorem port_entry (F : K.Files) (id : String) (table further : Params.TableName)
    (h : PortYesAt F id table further) : EntryGave F table further := by
  obtain ⟨_, p, _, -, -, -, -, -, -, -, -, -, -, hp, -, -, -, he, -⟩ := h
  exact ⟨p, hp, he⟩

/-- The five named hypotheses, two of them from the chains. -/
structure HolesC (V : Shape) (R : Reading5 V) : Prop where
  seed0 : ∀ F o id table further, o.id = some id → o.bits = 128 → PortYesAt F id table further →
    V.Served (stmOf F o) →
    ∃ r, V.recOf (stmOf F o) table = some r ∧
      V.seed0 (stmOf F o) (bytesToDig table.root) r = true
  test : TestOfChains V R
  seed1 : ∀ F o id table further, o.id = some id → o.bits = 128 → PortYesAt F id table further →
    V.Served (stmOf F o) →
    ∃ r', V.recOf (stmOf F o) further = some r' ∧
      V.seed1 (stmOf F o) (bytesToDig further.root) r' = true
  link : ∀ F o id table further r r', o.id = some id → o.bits = 128 →
    PortYesAt F id table further → V.Served (stmOf F o) → V.recOf (stmOf F o) table = some r →
    V.recOf (stmOf F o) further = some r' →
    ∃ πL, R.ent (stmOf F o) F.key F.ent = some (further, πL) ∧
      V.vL (stmOf F o) (bytesToDig table.root) (bytesToDig further.root) r r' πL = true
  session : SessionOfChains V R

/-- **The two hypotheses from the chains give the two of `K.Holes5`.** -/
theorem holes5_of_chains (V : Shape) (R : Reading5 V) (H : HolesC V R) : Holes5 V R where
  seed0 := H.seed0
  test := fun F o id table further r hi hb h hs hr =>
    H.test F o id table r hi hb hs hr (K.idIs_of_port F o id table further hi h)
      (port_key_chains F id table further h)
  seed1 := H.seed1
  link := H.link
  session := fun F o id table further r' hi hb h hs hr =>
    H.session F o id table further r' hi hb hs hr (port_entry F id table further h)
      (port_proof_chains F id table further h)

end OnBytes.TieK

#print axioms OnBytes.TieK.holes5_of_chains
