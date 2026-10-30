-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/LinkHoleAt.lean: THE LINK'S ITEM ON KNOWLEDGE SOUNDNESS (`Hiop.LinkKnowR`,
Hiop/RecSubs.lean) OF THE WRITTEN LINK OF AN ENTRY, at the full-size and at the small files of the
setting "record with work", UNDER THE THEOREM ON CODES, TAKEN AS GIVEN (`Cb.BCHKS46At`: a
hypothesis, which this file does not prove), AND NOTHING ELSE.

Statements and their proofs, which put three files together. OnBytes/Slice/LinkFamily.lean: the
written link as one verifier on pairs of records (`accFull`, `accSmall`), sound for all pairs at
once for the language `Sz.LangE2T`, with one list of error counts. OnBytes/Slice/ConfOf.lean: the
configuration of a stored table with a record (`DecR.configurationOfStoredTable`), and that on the statements of which the
item speaks the language gives the link's relaxed relation (`DecR.conf_req`).
OnBytes/Join1/LinkHole.lean: the rule that carries soundness record by record to the item.

Main theorems: `fr_linkKnow`, `sr_linkKnow`: the item. `frErr_below`, `srErr_below`: each count of
its list is at most 2^-128 as a share of its round's written verifier messages, work counted.

Letters that stay free: the openings of stored tables xs; how a decoded table is read as an index
(A) and the rest of the configuration (R); what the reduction declares of blinded oracles and
positions read (bl, er, rd): the item reads none of the last three.
Not claimed. The theorem on codes. The bound on the counts is one round's, with work counted: 32 of
the 128 bits are proof of work at six rounds of the full-size files and at four of the small ones;
that work is worth its bits is not shown; it is no bound on the chance of a false proof. The item
speaks of the statements whose first table decodes with its record to a table that holds an index,
and whose copy has no collision at its record's seed (`ConfigurationWithOutOfDomainSample.onEq`): how often a collision occurs,
and where a seed comes from, is not said. That the keys written of a pair of records are those that
a program makes of a file. Nothing on an honest prover: none of the items of `Hiop.LinkListR`. No
transcript is shown that the link accepts. The item holds at all openings xs. By reading, not by a
theorem: at xs that do not open the stored tables as the link's block asks (the empty list for one)
the view holds no stored column and the block refuses, so there the item is true for free; a
description takes `frD.xs`, `srD.xs` (OnBytes/Slice/FullRecSz.lean, SmallRecSz.lean). Whether the
item bites hangs on A: a table holds an index only where `A.inRange (A.mat u)` (`DecR.configurationOfStoredTable`,
OnBytes/Slice/ConfOf.lean), so where `A.inRange` holds of nothing `ConfigurationWithOutOfDomainSample.onEq` is empty and the item
is true for free; and "the same index" is as fine as `A.mat` is. That `ConfigurationWithOutOfDomainSample.onEq` has a member at
this configuration is stated nowhere. One premise rides inside a letter: the law `mat_cut` of A
(OnBytes/Slice/DecoderRec.lean), which whoever hands in A must prove. `Cb.BCHKS46At` speaks of all
lengths, degree bounds and radii, not of the link's own codes and radii alone: one false instance
would empty what rests on it (the limits of Cb/Gen/CodeListRSAt.lean). "Knowledge soundness" is the
item's name: nothing is extracted (the comment on `Hiop.LinkKnowR`, Hiop/RecSubs.lean). All that the
heads of the three files do not claim.

-/
import OnBytes.Join1.LinkHole
import OnBytes.Slice.ConfOf
import OnBytes.Slice.LinkFamily
import OnBytes.Slice.FullRecNum
import OnBytes.Slice.SmallRecNum

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood Hiop _root_.Run OnBytes.Join1
open scoped ENNReal

/-- **THE LINK'S ITEM ON KNOWLEDGE SOUNDNESS AT THE FULL-SIZE FILES, UNDER THE THEOREM ON CODES
ALONE.** -/
theorem fr_linkKnow (hA : BCHKS46At GF GE) (xs : List PQ.XO) {X : Type}
    (A : (frS.toDecR frZ 402653181).Claims X) (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A)
    (bl : OPos frShape → Bool)
    (er : Rho frShape → Finset (twoExternalStrings (DecR.configurationOfStoredTable A R).n (DecR.configurationOfStoredTable A R).Sg).Pos)
    (rd : Rho frShape → Finset (OPos frShape)) :
    LinkKnowR (C := DecR.configurationOfStoredTable A R) (linkOf frShape bl er rd (accFull xs)) frErr :=
  link_know (DecR.configurationOfStoredTable A R) frShape bl er rd (accFull xs)
    (fun r y => frS.LangE2T frZ 402653181 r y) frErr (fun r y hn => fr_family hA xs r y hn)
    fun r y hon hl => DecR.conf_req A R r y hon hl

/-- **THE SAME AT THE SMALL FILES.** -/
theorem sr_linkKnow (hA : BCHKS46At GF GE) (xs : List PQ.XO) {X : Type}
    (A : (srS.toDecR srZ 524285).Claims X) (R : (srS.toDecR srZ 524285).RelationsAndEncoding A)
    (bl : OPos srShape → Bool)
    (er : Rho srShape → Finset (twoExternalStrings (DecR.configurationOfStoredTable A R).n (DecR.configurationOfStoredTable A R).Sg).Pos)
    (rd : Rho srShape → Finset (OPos srShape)) :
    LinkKnowR (C := DecR.configurationOfStoredTable A R) (linkOf srShape bl er rd (accSmall xs)) srErr :=
  link_know (DecR.configurationOfStoredTable A R) srShape bl er rd (accSmall xs)
    (fun r y => srS.LangE2T srZ 524285 r y) srErr (fun r y hn => sr_family hA xs r y hn)
    fun r y hon hl => DecR.conf_req A R r y hon hl

/-- **The item's list of error counts at the full-size files**: each count is at most 2^-128 as a
share of its round's written verifier messages, work counted: at six rounds 32 of the 128 bits are
proof of work, at the others none (`fr_err_below`, OnBytes/Slice/FullRecNum.lean). -/
theorem frErr_below : Err.Below (s := frShape) frErr ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  fr_err_below [] fun _ => true

/-- **At the small files**: at four rounds 32 of the 128 bits are proof of work, at the others none
(`sr_err_below`, OnBytes/Slice/SmallRecNum.lean). -/
theorem srErr_below : Err.Below (s := srShape) srErr ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  sr_err_below [] fun _ => true

end OnBytes.Slice

#print axioms OnBytes.Slice.fr_linkKnow
#print axioms OnBytes.Slice.sr_linkKnow
#print axioms OnBytes.Slice.frErr_below
#print axioms OnBytes.Slice.srErr_below
