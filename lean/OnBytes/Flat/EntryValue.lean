-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/EntryValue.lean: what the entry file's link owes to a description of the whole proof
system, at the full-size and at the small files of the setting "record with work": THE LINK'S ITEM
ON KNOWLEDGE SOUNDNESS (`Hiop.LinkKnowR`, Hiop/RecSubs.lean), UNDER THE THEOREM ON CODES, TAKEN AS
GIVEN (`Cb.BCHKS46At`: a hypothesis, which this file does not prove), AND NOTHING ELSE; and that
the link is local, with nothing assumed.

Statements and their proofs, each one application. The term: `entryFull`, `entrySmall`
(OnBytes/Flat/EntryTerm.lean): the link as one reduction whose explicit statement is the pair of
records, made by the maker of OnBytes/Maker/Terminal.lean from the block of the program's link at
the keys written of the two records. The configuration: `DecR.configurationOfStoredTable A R` (OnBytes/Slice/ConfOf.lean).
The term has the type that the item asks over that configuration by unfolding: no cast occurs. The
rule: `link_know_ior` (OnBytes/Join1/LinkHole.lean). Soundness for all pairs of records at once:
`fr_family`, `sr_family` (OnBytes/Slice/LinkFamily.lean).

Main theorems:
  `entryFull_know`, `entrySmall_know`: the item, at the lists of error counts `frErr`, `srErr`.
  `entryFull_local`, `entrySmall_local`: the link is local.
The lists' bound: `frErr_below`, `srErr_below` (OnBytes/Slice/LinkHoleAt.lean).

Letters that stay free: how a decoded table is read as an index (A), and the rest of the
configuration (R).
Not claimed. The theorem on codes. The item speaks of the statements whose first table decodes with
its record to a table that holds an index, and whose copy has no collision at its record's seed
(`ConfigurationWithOutOfDomainSample.onEq`): how often a collision occurs, and where a seed comes from, is not said here. That
the keys written of a pair of records are those that a program makes of a file. The interactive
form: no hash, no bytes. Nothing on an honest prover: none of the items of `Hiop.LinkListR`. No
transcript is shown that the link accepts. Whether the item bites hangs on A: a table holds an index
only where `A.inRange (A.mat u)` (`DecR.configurationOfStoredTable`, OnBytes/Slice/ConfOf.lean), so where `A.inRange`
holds of nothing `ConfigurationWithOutOfDomainSample.onEq` is empty and the item is true for free; and "the same index" is as
fine as `A.mat` is. That `ConfigurationWithOutOfDomainSample.onEq` has a member at this configuration is stated nowhere. One
premise rides inside a letter: the law `mat_cut` of A (OnBytes/Slice/DecoderRec.lean), which whoever
hands in A must prove. The bound on the counts is one round's, with work counted: 32 of the 128 bits
are proof of work at six rounds of the full-size files and at four of the small ones; that work is
worth its bits is not shown; it is no bound on the chance of a false proof. `Cb.BCHKS46At` speaks of
all lengths, degree bounds and radii, not of the link's own codes and radii alone: one false
instance would empty what rests on it (the limits of Cb/Gen/CodeListRSAt.lean). "Knowledge
soundness" is the item's name: nothing is extracted (the comment on `Hiop.LinkKnowR`,
Hiop/RecSubs.lean). All that the heads of the files named above do not claim.

-/
import OnBytes.Flat.EntryTerm
import OnBytes.Slice.LinkHoleAt
import OnBytes.Maker.TerminalLaws

set_option autoImplicit false

namespace OnBytes.Flat
open Iop Prob Cb Cb.Ood Hiop _root_.Run OnBytes.Slice OnBytes.Join1 OnBytes.Maker
open scoped ENNReal

/-! ## The full-size files -/

/-- **THE ENTRY'S LINK AT THE FULL-SIZE FILES HAS THE LINK'S ITEM ON KNOWLEDGE SOUNDNESS, UNDER THE
THEOREM ON CODES ALONE**, over the configuration of a stored table with a record, at the list of
error counts `frErr`. -/
theorem entryFull_know (hA : BCHKS46At GF GE) {X : Type}
    (A : (frS.toDecR frZ 402653181).Claims X) (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) :
    LinkKnowR (C := DecR.configurationOfStoredTable A R) entryFull frErr :=
  link_know_ior (DecR.configurationOfStoredTable A R) entryFull (accFull frD.xs) entryFull_out
    (fun r y => frS.LangE2T frZ 402653181 r y) frErr
    (fun r y hn => fr_family hA frD.xs r y hn) fun r y hon hl => DecR.conf_req A R r y hon hl

/-- It is local. Nothing is assumed. -/
theorem entryFull_local : entryFull.IsLocal := iorX_isLocal ..

/-! ## The small files -/

/-- **THE SAME AT THE SMALL FILES**, at the list `srErr`. -/
theorem entrySmall_know (hA : BCHKS46At GF GE) {X : Type}
    (A : (srS.toDecR srZ 524285).Claims X) (R : (srS.toDecR srZ 524285).RelationsAndEncoding A) :
    LinkKnowR (C := DecR.configurationOfStoredTable A R) entrySmall srErr :=
  link_know_ior (DecR.configurationOfStoredTable A R) entrySmall (accSmall srD.xs) entrySmall_out
    (fun r y => srS.LangE2T srZ 524285 r y) srErr
    (fun r y hn => sr_family hA srD.xs r y hn) fun r y hon hl => DecR.conf_req A R r y hon hl

/-- It is local. Nothing is assumed. -/
theorem entrySmall_local : entrySmall.IsLocal := iorX_isLocal ..

end OnBytes.Flat

#print axioms OnBytes.Flat.entryFull_know
#print axioms OnBytes.Flat.entryFull_local
#print axioms OnBytes.Flat.entrySmall_know
#print axioms OnBytes.Flat.entrySmall_local
