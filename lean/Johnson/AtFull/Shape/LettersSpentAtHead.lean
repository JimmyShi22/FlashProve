-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/LettersSpentAtHead.lean: UNDER THE HEAD P5J.AtMgA, AT AN OPENING: THE SIX OF
THE TABLE's 20 LETTERS THAT ARE WHAT A READER OF Z OR G RETURNS (nums, hpL, k8, k2n, look, k11;
`lettersOf`, TabLetters.lean) ARE TERMS IN THE READER's STRUCTURE Zp.p.X, IN WRITTEN VALUES, AND IN
ANY GROUND G' THAT HAS THE GROUND's built AND THAT STRUCTURE AS ITS W. A joining of laws; nothing is
evaluated.

What it is for. With `alike_at_head` (LettersAtHead.lean): whoever lays a record L of letters as a
function of the reader's structure X alone may take these six terms at X for L's six fields, and a
ground made of X for G'.

The letter look. The first text of the table makes all fifty sites of the lookups (`lookSites`) and
searches among them. Under the head the search finds a site at each address (`site_found`,
TableSites.lean: by law, from the members' own tests on the plan and one closed fact on the written
places), and a made site's numbers and shape are what the reader's structure gives at the address
(`site_facts`, Johnson/Desc/ProofFile/Honest/K3/Law/MemberSite.lean). So the pair that the cells
spend is a term in X alone, without the list, the search and the table of places. At the calls of a
layers' link the shape is the layout's own record (`shape_layers_at`, LookFree.lean).

Main names.
* `site_is_at`. **`look_at_head`**: for l < 25: look l d = (Look.placeAt Zp.p.X l d).bind fun p =>
  p.shape.map fun hS => (hS, p.first). **`look_layers_at_head`**: for even l < 24: look l false =
  (Look.placeAt Zp.p.X l false).map fun p => (Zp.p.X.y.fo, p.first).
* **`spent_at_head`**: the head, an opening O, Bs.G₀.built = G'.built, Zp.p.X = G'.W ⊢ six
  equations: nums l = (G'.built[l]?).bind (K1.linkNumbers G'); hpL l = P1K2.pureLetters G' l; k8 l =
  (G'.built[l]?).map of k8ParWC at the written messages' numbers; k2n a = K2's preparing at the
  written sizes and Zp.p.X, then numsAt; look as above; k11 = parAtC at the written count and G'.

Limits. IMPLICATIONS. WHAT THE GROUND's built IS, IS NOT SAID HERE: a premise. No ground G' is laid
here. G' 's two other fields (first, cov) are read by none of the terms: seen in the readers'
congruences, which ask nothing of them. AT THE ATTENTION's AND THE HEAD's CALLS AND AT ALL DIGITS
the shape is still what p.shape makes: no law here says what that is. That the head has a member is
shown in scope, where the reader returns and `protocolDataWellFormed` accepts (`head_of_live`,
Johnson/P5J/HeadOfLive.lean); that these three hold together, at two named sets of public files, in
a side library. TWO RIGHT SIDES CARRY THE LIBRARY's SILENT DEFAULTS AT CLOSED TERMS: the written
count is (sentAtC? …).getD 0, and the written messages' numbers fall to the empty list: the
equations hold either way, and no law here says that the fall-back is not taken. Tab.siteAt (a
search) and the lookups' siteAt (a maker) are two things of one name. Closed terms but for X and G';
nothing is evaluated. The full size alone. At the format's second hash function. Nothing on
soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.LettersAtHead
import Johnson.AtFull.Shape.SpentReadersAtHead
import Johnson.AtFull.Shape.TableSites
import Johnson.AtFull.Shape.LookFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain Block FileDescription Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look (placeAt)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.K1 (qFull linkNumbers)
open VerifiableInference.PlanWritten (proofSizedFull)
open Johnson.AtFull.Cut (cutWritten)
open Johnson.AtFull.Desc.Lots (esW)
open Johnson.G (codesFull2)
open ProofFile.Honest.K3 (Site lookSites callerOf)
open ProofFile.Honest.K3.Law (site_facts)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {F : FileDescription ProofFile.Inst} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- Under the head the table's search finds, at each address, a site whose numbers are what the
reader's structure gives at that address, and whose shape is what these numbers give. -/
theorem site_is_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25) (d : Bool) :
    ∃ s, Tab.siteAt Zp l d = some s ∧ s ∈ lookSites Zp ∧ s.link = l ∧ s.digits = d ∧
      placeAt Zp.p.X l d = some s.p ∧ s.p.shape = some s.shape ∧
      s.caller = (callerOf Zp.p.X.p4 Zp.p.X.NGr l).1 := by
  obtain ⟨s, e, hm, e1, e2⟩ := site_found h l hl d
  have hm' := hm
  unfold lookSites at hm'
  obtain ⟨y, -, hy⟩ := List.mem_filterMap.1 hm'
  obtain ⟨f1, f2, f3, f4, -, -, f7, -⟩ := site_facts _ _ y s hy
  rw [← f3, ← f4, e1, e2] at f1
  rw [← f3, e1] at f7
  exact ⟨s, e, hm, e1, e2, f1, f2, f7⟩

/-- **UNDER THE HEAD THE LETTER look IS A TERM IN THE READER's STRUCTURE ALONE**: no list of sites,
no search, no table of places. -/
theorem look_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G : ProofFile.Ground) (l : Nat)
    (hl : l < 25) (d : Bool) :
    (lettersOf Zp G).look l d =
      (placeAt Zp.p.X l d).bind fun p => p.shape.map fun hS => (hS, p.first) := by
  obtain ⟨s, e, -, -, -, f1, f2, -⟩ := site_is_at h l hl d
  show (Tab.siteAt Zp l d).map (fun s => (s.shape, s.p.first)) = _
  rw [e, f1, Option.bind_some, f2]
  rfl

/-- **AT THE CALLS OF A LAYERS' LINK THE SHAPE IS THE LAYOUT's OWN RECORD**: nothing is made. -/
theorem look_layers_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G : ProofFile.Ground) (l : Nat)
    (hl : l < 24) (he : l % 2 = 0) :
    (lettersOf Zp G).look l false =
      (placeAt Zp.p.X l false).map fun p => (Zp.p.X.y.fo, p.first) := by
  obtain ⟨s, e, hm, -, e2, f1, -, f7⟩ := site_is_at h l (by omega) false
  obtain ⟨Bs', base', O'⟩ := h.laid.opened
  obtain ⟨k4, kN, -⟩ := Meaning.scope_plans h.scope h.reads O'.public
  rw [O'.W] at k4 kN
  have hc : s.caller = .layers := by
    rw [f7, k4, kN]
    have h24 : (l == 2 * 12) = false := by simp; omega
    have hev : (l % 2 == 0) = true := by simp [he]
    simp [callerOf, h24, hev]
  show (Tab.siteAt Zp l false).map (fun s => (s.shape, s.p.first)) = _
  rw [e, f1, Option.map_some, Option.map_some, shape_layers_at h s hm e2 hc]

/-- **UNDER THE HEAD, AT AN OPENING: THE SIX LETTERS THAT ARE WHAT A READER RETURNS**, written in
the reader's structure Zp.p.X, in written values, and in any ground G' that has the ground's built
and that structure as its W. look at l < 25; the others at every l, a. -/
theorem spent_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base c A B)
    {G' : ProofFile.Ground} (hB : Bs.G₀.built = G'.built) (hW : Zp.p.X = G'.W) :
    (∀ l, (lettersOf Zp Bs.G₀).nums l = (G'.built[l]?).bind (linkNumbers G')) ∧
    (∀ l, (lettersOf Zp Bs.G₀).hpL l = P1K2.pureLetters G' l) ∧
    (∀ l, (lettersOf Zp Bs.G₀).k8 l =
      (G'.built[l]?).map fun Xl => k8ParWC (k8MsgsC cutWritten esW) G' Xl l) ∧
    (∀ a, (lettersOf Zp Bs.G₀).k2n a =
      (P1K2.prepareAt proofSizedFull Zp.p.X qFull codesFull2 proofSizedFull.request
        proofSizedFull.request.answers).bind fun P => P1K2.numsAt P a) ∧
    (∀ l, l < 25 → ∀ d, (lettersOf Zp Bs.G₀).look l d =
      (placeAt Zp.p.X l d).bind fun p => p.shape.map fun hS => (hS, p.first)) ∧
    (lettersOf Zp Bs.G₀).k11 = parAtC ((sentAtC? cutWritten esW "H.8.call").getD 0) G' := by
  have hW' : Bs.G₀.W = G'.W := O.W.trans hW
  refine ⟨fun l => nums_congr hB hW' l, fun l => pureLetters_congr hB hW' l, fun l => ?_,
    fun a => ?_, fun l hl d => look_at_head h _ l hl d, parOf_at_head h.toAtMg hB hW'⟩
  · show (Bs.G₀.built[l]?).map (fun Xl => ProofFile.k8ParW Zp Bs.G₀ Xl l) = _
    rw [hB, funext fun Xl => k8ParW_at_head h.toAtMg hW' Xl l]
  · show (P1K2.prepOf Zp Bs.G₀).bind (fun P => P1K2.numsAt P a) = _
    rw [prepOf_at_head h.toAtMg O]

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.site_is_at
#print axioms Johnson.AtFull.Shape.look_at_head
#print axioms Johnson.AtFull.Shape.look_layers_at_head
#print axioms Johnson.AtFull.Shape.spent_at_head
