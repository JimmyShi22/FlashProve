-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/LookRoundsAtHead.lean: CONDITIONAL. UNDER THE LIBRARY's
HYPOTHESIS h : `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean), AT EACH GROUP g BELOW 12: THE OWN SCALARS OF
THE DECLARED ROUNDS OF THE FIRST CHAIN's MEMBER NUMBER 28 g + 3 ADD UP TO THE LIBRARY's NUMBER
`Forest.elems` AT THE LAYOUT's SHAPE.

What is here. PUBLIC DATA ALONE: names of rounds and counts. A round's scalars are "own" unless its
name stands in `frameNames` (Honest/BookOf.lean). That member is the lookup on the calls of segment
(link) 2 g: so `lookMember_head` (Law/LookMemberHead.lean). A joining: calls of statements of the
authors of the kind "lookup", of the library and of this file's writers. Statements with their
proofs; no definition.

  `ownOfRounds_entries`: a sub-protocol's own scalars, read off its rounds' entries.
  `lookRounds_own_head`: **THE STATEMENT.**

How. The member stands at the library's address of that lookup and passes its test on the plan
(`lookMember_head`). A site of the kind's authors' list stands there, and a sub-protocol of their
lot (`site_calls_head`, Honest/K3/Law/Thread/SiteThereHead.lean; `lot_at_site`,
Honest/K3/Law/Thread/LotAtSite.lean). The lot's rounds are the plan's entries, and these are, but
for the work bits, the table `entriesV` at the site's face (`site_block`, `site_facts`:
Honest/K3/Law/MemberSite.lean). The member's rounds are the lot's (`IM.k3_of`, `IM.k3Hear_mem`:
Johnson/IMR/K3Seat.lean; `IM.alone_rounds`, `IM.alone_place`: Johnson/IMR/SeatForm.lean; that the
two members are one: `IM.hear_at_flat`, Johnson/IMR/FlatIx.lean; `IM.places_scope`,
Johnson/IMR/PlacesScope.lean; `IM.places_nodup`, Johnson/IMR/BorderW.lean). The table's scalars add
up to `Forest.elems` at the site's shape (`own_work`, `entriesV_elems`: Law/W/LookScalars.lean), and
the site's shape is the layout's (`site_shape_head`, Law/W/SiteShape.lean).

Not shown here. Nothing on what is sent in these rounds. That `Forest.elems` is what the verifier's
ledger moves by. Nothing on the lookup on the digits or on another segment. THE FULL SIZE ALONE, AND
THE FORMAT's EARLIER HASH (`OnBytes.secondHashFunction`) ALONE. Through Law/W/SiteShape.lean it rests on a
statement of a file under Johnson/Goal/, called by name there: `Meaning.scope_plans`; what the
called files of other writers rest on deeper was not traced. Beneath it stand closed facts by
evaluation in Lean's kernel, which no independent checker has replayed (Johnson/IMR/BorderW.lean
holds one; others were not traced). That h can hold: the side library AtFullSide proves, with no
hypothesis, that h has a member at one set of public files (AtFullSide.Top.headMember_zFull,
AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it is worth). IT STANDS OVER FILES
THAT ARE NO PART OF THE SEALED LIBRARY YET: of this file's writers (Honest/Small/OwnOfRounds.lean;
Law/W/LookScalars.lean; Law/W/SiteShape.lean; Law/LookMemberHead.lean and what lies beneath it) and
of other writers (Honest/K3/: Law/Thread/SiteThereHead.lean, Law/Thread/LotAtSite.lean,
Law/MemberSite.lean, Law/SlotsElems.lean, Law/Statements.lean, Lot.lean; Honest/: BookRowKit.lean,
BookCutsLaw.lean, BookOf.lean, BookEntries.lean; and what lies beneath them). Nothing on soundness,
on completeness or on any other property.
No property is claimed.
A LAW, NOT A PART: no file that defines a part of the proof file's description may import this one:
following import lines, its imports reach modules under Johnson/Goal/, under Johnson/Bridge/ and one
whose name begins Cb.Bridge.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.SiteShape
import Johnson.Desc.ProofFile.Honest.K4.Law.W.LookScalars
import Johnson.Desc.ProofFile.Honest.Small.OwnOfRounds
import Johnson.Desc.ProofFile.Honest.K4.Law.LookMemberHead
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.SiteThereHead
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LotAtSite
import Johnson.IMR.K3Seat
import Johnson.IMR.FlatIx
import Johnson.IMR.PlacesScope
import Johnson.IMR.BorderW

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- The default instance `Inst.Model.Scl.ref` (a table of scales) is switched off in this file, so
that no statement picks a table of scales silently. -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.K3 (entriesV)
open ProofFile.Honest.K3 (Site lookSites)

/-- A sub-protocol's own scalars, read off its rounds' entries. -/
theorem ownOfRounds_entries {σ C : Type} (b : Block σ C) :
    ownOfRounds b = ownOfEntries (b.rounds.map (·.entry)) := by
  unfold ownOfRounds ownOfEntries
  rw [List.foldl_map]
  rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL: on h, hg and hb. **THE MEMBER NUMBER 28 g + 3 DECLARES `Forest.elems` OWN SCALARS,
AT THE LAYOUT's SHAPE.** -/
theorem lookRounds_own_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {g : ℕ} (hg : g < 12)
    {blk : Block P5J.TS ProofFile.Cl} (hb : cF.blocksInOrder[28 * g + 3]? = some blk) :
    ownOfRounds blk = Model.Forest.elems (P5J.At.X Zp).y.fo := by
  obtain ⟨blk', e1, e2, e3⟩ := ProofFile.Honest.K4.lookMember_head h hg
  have e0 : blk' = blk := Option.some.inj (e1.symm.trans hb)
  rw [e0] at e2 e3
  have hmem : blk ∈ cF.blocksInOrder := List.mem_of_getElem? hb
  obtain ⟨s, hs, hl, hd, hpl, hps⟩ :=
    ProofFile.Honest.K3.Law.AtThr.site_calls_head h (2 * g) (by omega)
  obtain ⟨lot, hlot, hlp⟩ := ProofFile.Honest.K3.Law.AtThr.lot_at_site h s hs hps
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, hfit, -, hlr, -⟩ := ProofFile.Honest.K3.Law.site_block _ _ _ _ _ _ _ _ _ _ _ O s hs lot blk
    hlot hlp hmem (by rw [e2, hlp, hpl]) e3
  -- the member's rounds are the lot's
  obtain ⟨Lk, b, b', k1, k2, k3, hla⟩ := IM.k3_of h.scope h.reads O (2 * g) (by omega) false
  have hbm : b ∈ cF.blocksInOrder := List.mem_of_getElem? (IM.hear_at_flat k1 k2)
  have hnd : (cF.blocksInOrder.map (·.place)).Nodup := by
    rw [IM.places_scope h.scope h.reads O]
    exact IM.places_nodup
  have eb : b = blk := List.inj_on_of_nodup_map hnd hbm hmem ((IM.alone_place hla).trans e2.symm)
  have hat := IM.k3Hear_mem hlot
  rw [hlp, hpl, ← O.W] at hat
  have el : b' = lot := Option.some.inj (k3.symm.trans hat)
  have hr : blk.rounds = lot.rounds := by
    rw [← eb, ← el]
    exact IM.alone_rounds hla
  -- the site's face
  have hs' := hs
  unfold lookSites at hs'
  obtain ⟨x, -, hsx⟩ := List.mem_filterMap.1 hs'
  obtain ⟨-, -, -, -, -, hface, -, -⟩ := ProofFile.Honest.K3.Law.site_facts _ _ x s hsx
  have hfe : ((s.p.entries.getD []).map fun e => { e with work := 0 }) = entriesV s.at_.face :=
    eq_of_beq hfit
  have hen : (blk.rounds.map (·.entry)) = s.p.entries.getD [] := by
    rw [hr, hlr, List.map_map]
    exact List.map_id _
  rw [ownOfRounds_entries, hen, ← own_work, hfe, hface, entriesV_elems,
    site_shape_head h hg hs hl hd]

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.ownOfRounds_entries
#print axioms ProofFile.Honest.K4.W.lookRounds_own_head
