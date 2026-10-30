-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/OkThereB.lean: FOR A FILE OF EVALUATIONS ALONG A WALK: THE Bool OF THE PUBLIC ITEM «K5.okAt» (K5's files', through the
table of joints' door): ON THE CARRIED RECORD ALONE: the open ledger has its sizes; what the attention segment's own rounds handed on is there; and
every slot of which the kind's runs of claims speak is marked "filled" in the open ledger. Which slots these are hangs on the place's shape g and on
what was heard alone: no key point, no run of the kind's road.
  stretchB U a n   the n slots from a on are filled in U · formB U f   every slot that the form f names is · sumB U hh n   of one masked
  sumcheck's record: its start form, its coefficients' stretch, its first n end values · heardSlotsB U g h   a clause a field of Heard, and that
  h.om and h.om'' have g.NP members · sizedB U   the three arrays on slots have the length ns.
  okThereB g s     THE ITEM: at the record's open ledger (S.fork?) and what it holds as heard (S.heard5?); false where either lacks.
g IS A LETTER: whoever fills a segment's row hands in that segment's plan's shape. It imports
texts with code alone: no Mathlib, no root outside the library. What it means: Law/OkThereTie.lean.
-/
import Johnson.Desc.First.State
import Johnson.Desc.First.Att.Geo
import Johnson.Desc.Part.MaskedSum4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Door
open OnBytes OnBytes.Model
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att.P (Geo Heard)

def stretchB (U : Fork) (a n : Nat) : Bool := (List.range n).all fun i => U.gotF.getD (a + i) false

def formB (U : Fork) (f : Aff) : Bool := f.slots.toList.all fun x => U.gotF.getD x.1 false

def sumB (U : Fork) (hh : MaskedSum.Heard) (n : Nat) : Bool :=
  formB U hh.start && stretchB U hh.first (MaskedSum.hidingAt (hh.vars.zip hh.r)).1.length && stretchB U hh.sEnd n

def heardSlotsB (U : Fork) (g : Geo) (h : Heard) : Bool :=
  (h.remainders.toList.all fun j => stretchB U j 3) && (h.scores.toList.all fun o => stretchB U o.1 7) &&
  ((g.scores.toArray.zip h.scores).toList.all fun x => sumB U x.2.2 (2 * x.1.pcs.length)) &&
  stretchB U h.five 5 && stretchB U h.bits g.lt && stretchB U h.two 2 && stretchB U h.values 2 &&
  stretchB U h.maxima g.NP && sumB U h.division (2 * g.NP) && sumB U h.below (2 * g.NP) && sumB U h.on (2 * g.NP) &&
  sumB U h.atIndex (2 * g.NP) && sumB U h.key (g.Lam + g.NP * g.lt) && sumB U h.cells (2 * g.NP) &&
  h.om.size == g.NP && h.om''.size == g.NP

def sizedB (U : Fork) : Bool := U.vp.size == U.ns && U.mf.size == U.ns && U.gotF.size == U.ns

/-- **The item «K5.okAt».** -/
def okThereB (g : Geo) (s : S) : Bool :=
  match s.fork?, s.heard5? with
  | some U, some h => sizedB U && heardSlotsB U g h
  | _, _ => false

end H2K5.Door
