-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/RunsAtBatch.lean: CONDITIONAL.

What is here. A LAW ON WHAT THE VERIFIER's SUB-PROTOCOLS ACCEPT: the honest prover is not in it; it
lies in this folder because `RunAsks` does (Law/RunsName.lean). AT EVERY STATE THAT THE FIRST
CHAIN's RUN REACHES IN FRONT OF THE BATCHING OF A FEED-FORWARD LAYERS' SEGMENT (member number 28 g +
9 of the chain's flat list, counted from 0): WHAT THE STATE HOLDS AS THE RETURN OF THE LAYERS' OWN
ROUNDS (sub-protocol K4) MEETS `RunAsks` AT THE PARAMETERS THAT `LPFK9.k4ParAt` NAMES FOR THE
SEGMENT AND AT THE ARRAY NUMBER 0. `RunAsks` says four things of what was heard: it is a return of
K4's hearing at the plan; the plan's third number of reads is at most the width that the hearing
stored; the forms that the lookup on the calls kept name no entry, and slots alone that are filled
in some ledger (`PadNames`); the third array of reads has the number named. "Reached" is the
library's `Reach` (Johnson/Top/H0/Walk/Reach.lean): along accepting steps of the chain's members,
from any first state. Three statements and their proofs: joinings of the library's:
· `k4_heard_at_front` (Johnson/Desc/First/Link/Law/K4AtFront.lean): the hearing's equation and
  `PadNames` at that border;
· `flat_planOk` (Johnson/P1K2R/SitsDoor.lean) and `sized_upTo`
  (Johnson/Desc/First/Look/K03RowsBare.lean): the two premises of `k4_heard_at_front`, from hS, hR,
  O, hOk and h;
· `k4_hK` (Johnson/Meaning/PlanesTieK8Plan.lean): the width;
· `hear_iU3` (Johnson/Meaning/ReadsK4.lean): the plan names the array that was heard;
· `plansG_at` (OnBytes/Tie/Pv/Lookup/Ends/FoPublic.lean) and `planG_u3`
  (Johnson/Road/K4/Rec/U3Tree.lean): a made plan's third array of reads has the number 0;
· `IM.k4_of` (Johnson/IMR/K4Seat.lean) and `k4ParAt_of_mem` (Johnson/LPFK9R/K4Ties.lean): whose
  parameters these are;
· `Reach.fold` and `reach_raw` (Reach.lean): a reached state is a fold's; what the wrapped
  sub-protocols (`below b`) reach, their own steps reach.

Not shown here. THAT ANY STATE IS REACHED THERE: the statements are met for nothing where none is.
THAT `RunsPre` (Law/RunsName.lean) HOLDS THERE: it asks `RunAsks` at the number that the state's own
record of the smallness test names for its third array of reads; here the number is 0, read off the
plan's record, and that the state's record names 0 is not shown. Nor that the batching runs "front"
or "back" at the very state of this border. That the batching's sub-protocol is the member at that
number: the statements speak of the number alone. THAT THERE IS AN OPENING: hS, hR, O and hOk are
hypotheses: the public files lie in the goals' scope (`VerifierAndGoals.InScope`) and are read, the maker's
description is opened, and it passes its test on the plan. Nothing on what a form or a claim is
worth. THE FULL SIZE ALONE. The description is opened with the format's second hash function
itself (`OnBytes.secondHashFunction`) in the place that its maker keeps for that function: nothing is said where
another function stands there. No example of the hypotheses together has been through Lean.
No property is claimed.
A LAW, NOT A PART: no file that defines a part of the proof file's description may import this one:
its imports reach modules under Johnson/Goal/.

  `runAsks_at_batch`     **at 28 g + 9.**
  `runAsks_at_link`      the same at 14 l + 9, for every g with l = 2 g and g < 12.
  `runAsks_at_wrapped`   **the same where the wrapped sub-protocols reach a layers' segment's
      batching.**
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.RunsName
import Johnson.Desc.First.Link.Law.K4AtFront
import Johnson.Desc.First.Look.K03RowsBare
import Johnson.LPFK9R.K4Ties
import Johnson.Meaning.PlanesTieK8Plan
import Johnson.Meaning.ReadsK4
import Johnson.P1K2R.SitsDoor
import Johnson.Road.K4.Rec.U3Tree

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.PscRun (Sized)
open OnBytes.Desc.First.K4 (Par hearFl)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- CONDITIONAL on hS, hR, O, hOk and h. **IN FRONT OF A LAYERS' SEGMENT's BATCHING what K4's rounds
returned meets `RunAsks`**, at the segment's parameters and the array number 0. -/
theorem runAsks_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {g : ℕ} (hg : g < 12) {Q' : Type} {start : Q' → S} {z : Q'} {s : S}
    (h : Reach 0 c.blocksInOrder start (28 * g + 9) (z, s)) {p4 : Par}
    (e : LPFK9.k4ParAt Z Bs.G₀ (2 * g) = some p4) {o : Own} (ho : s.own? = some o) :
    RunAsks p4 o 0 := by
  have hp := P1K2.flat_planOk O hOk
  obtain ⟨_, R, C, hfold⟩ := h.fold
  have hk : 28 * g + 9 = 14 * (2 * g) + 6 + 2 + 1 := by omega
  rw [hk] at hfold
  obtain ⟨G', hG', hZ'⟩ := VerifiableInference.OnPublicFiles.sized_upTo hS hR O hOk (2 * g) (by omega) 6
    (by omega) hfold
  have hB : ∃ G', s.fork? = some G' ∧ Sized G' := ⟨G', hG', hZ'⟩
  obtain ⟨x, tokv, fo, F₄, o', G, _, t, u, _, xg, xP, xG, hh, _, N, efo, ho', _⟩ :=
    VerifiableInference.Desc.LinkJoin.k4_heard_at_front hS hR O hp hg h hB
  obtain rfl : o' = o := Option.some.inj (ho'.symm.trans ho)
  obtain ⟨_, _, x', _, _, hx', _, el, eg, eP, eG, _, hG⟩ := IM.k4_of hS hR O g hg
  obtain rfl : p4 = LPFK9.parOfMember x' :=
    Option.some.inj (e.symm.trans (LPFK9.k4ParAt_of_mem hx' el))
  have ehp : x'.2.hp = x.2.hp := Option.some.inj (eG.symm.trans xG)
  have ePP : x'.2.P = x.2.P := eP.trans xP.symm
  have egg : x'.2.g = x.2.g := eg.trans xg.symm
  refine ⟨⟨tokv, fo, F₄, G, t, u, ?_⟩, ?_, ⟨F₄, ?_⟩, ?_⟩
  · show hearFl { x'.2.P with tokv := tokv } x'.2.hp x'.2.g fo F₄ t = some (_, G, u)
    rw [ePP, ehp, egg]
    exact hh
  · show x'.2.hp.nU.getD 2 0 ≤ _
    rw [ehp]
    exact _root_.Meaning.Reads.k4_hK hh hG xG
  · rw [efo]
    exact N
  · have u1 := (_root_.Meaning.Reads.hear_iU3 hh).1
    have pl := _root_.Fo.Pub.plansG_at _ _ hG g _ xG
    have u0 : x.2.hp.tl.ix.U.getD 2 none = some 0 := by
      rw [(OnBytes.Road.K4.Rec.planG_u3 _ _ _ _ pl).1]
      rfl
    exact (Option.some.inj (u0.symm.trans u1)).symm

/-- CONDITIONAL on hS, hR, O, hOk and h. **The same at the border 14 l + 9**, for every group g with
l = 2 g and g < 12. -/
theorem runAsks_at_link (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} {Q' : Type} {start : Q' → S} {z : Q'} {s : S}
    (h : Reach 0 c.blocksInOrder start (14 * l + 9) (z, s)) :
    ∀ g p4 o, l = 2 * g → g < 12 → LPFK9.k4ParAt Z Bs.G₀ (2 * g) = some p4 → s.own? = some o →
      RunAsks p4 o 0 := by
  intro g p4 o hl hg e ho
  subst hl
  have e9 : 14 * (2 * g) + 9 = 28 * g + 9 := by omega
  rw [e9] at h
  exact runAsks_at_batch hS hR O hOk hg h e ho

/-- CONDITIONAL on hS, hR, O, hOk and w. **The same at every state that the wrapped sub-protocols
reach, from the description's own first state (`ProofFile.startS Z`) at some request and key, in front of
the batching of a feed-forward layers' segment l** (l = 2 g, g < 12). At every other l, the head's
segment l = 24 among them, where the border is another, nothing is said. -/
theorem runAsks_at_wrapped (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} {s : S}
    (w : ∃ zp : ProofFile.InstPub, Reach 0 (c.blocksInOrder.map VerifiableInference.Desc.Sound.below)
      (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (zp, s)) :
    ∀ g p4 o, l = 2 * g → g < 12 → LPFK9.k4ParAt Z Bs.G₀ (2 * g) = some p4 → s.own? = some o →
      RunAsks p4 o 0 := by
  intro g p4 o hl hg e ho
  subst hl
  obtain ⟨zp, h⟩ := w
  rw [if_neg (by omega : ¬ 2 * g = 24)] at h
  have e9 : 14 * (2 * g) + 9 = 28 * g + 9 := by omega
  rw [e9] at h
  exact runAsks_at_batch hS hR O hOk hg (reach_raw h) e ho

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.runAsks_at_batch
#print axioms ProofFile.Honest.K4.runAsks_at_link
#print axioms ProofFile.Honest.K4.runAsks_at_wrapped
