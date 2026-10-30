-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Close/Law/RowAsksOf.lean (kind K10): SIX OF THE TEN FIELDS OF `RowAsks`
(HRowAtFa.lean, beside this file: what the rows' part of K10's law asks of the statement in front)
PAID FROM THE TABLE's OWN PROMISE AND THE FACTS ON REACHED STATES (`FoldFacts`,
Johnson/Desc/First/FoldFacts.lean). Statements and proofs.

What is said.
  `link_of_stand`: where a segment stands open the link's part of the state is there.
  `held_of_onQ`: the promise at a state without a mark holds `rowsHeld` and `membersHeld` at the
    table's open set of that border.
  `frame_of_link`: where a link is open, the frame that K10's sub-protocol reads off the state (rdK)
    is that link's own.
  `rowAsks_of`: **`RowAsks` at O := the table's open set at border k**: PAID INSIDE: inOrder (the
    facts' "tidy") · grp (the facts' groupIs, at the link that the promise's test on where the chain
    stands shows to be open) · rows · members (the promise) · apart (the facts' "the book fits":
    ApartOfFits.lean) · codes (the facts' codes).
    LEFT AS PREMISES, IN THE FIELDS' VERY FORMS: ties · names · seats · shapes.

PREMISES OF rowAsks_of. On the state: FF (FoldFacts) · hon (the promise) · hr (reached) · hu (no
mark). On the table and the plan, closed: hp, hl (the place at number k is of link m) · hst (there a
segment is to stand open) · hgr (the facts' group of m is the numbers') · hcs (the facts' codes are
cs). The four fields that are left.

Limits. FF, hon, hr, hu are premises: SHOWN OF NO STATE HERE. The closed ones are evaluated by
nobody
here. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.HRowAtFa
import Johnson.Desc.First.Close.Law.ApartOfFits
import Johnson.Desc.First.K8.ForkPromise

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice Cb Johnson.Top.H Johnson.Pack
open VerifiableInference.Desc.Sound
open Johnson.G (memMain)
open OnBytes.Means (tableSize)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (S ModelPart Numbers Item Meaning rowsHeld membersHeld FoldFacts
  FoldData start openSets shapeAt standOf standAt Stand)

/-- Where a segment stands open the link's part of the state is there. -/
theorem link_of_stand (s : S) (sub : ModelPart) (h : standOf s = .link sub) :
    ∃ L, s.link? = some L := by
  unfold standOf at h
  cases hh : s.here with
  | between => rw [hh] at h; cases h
  | lay a => exact ⟨a.L, by simp [S.link?, hh]⟩
  | att a => exact ⟨a.L, by simp [S.link?, hh]⟩
  | head a =>
    rw [hh] at h
    dsimp only at h
    split at h
    · rename_i hi
      have ho : a.opened = true := by
        by_contra c
        simp [S.inLink, S.fork?, hh, c] at hi
      exact ⟨a.L, by simp [S.link?, hh, ho]⟩
    · cases h
  | fin a => rw [hh] at h; cases h
  | mem a => rw [hh] at h; cases h

/-- The promise at a state without a mark holds the two tests on the open rows. -/
theorem held_of_onQ {A P W : Type} {Fr : Frame} (N : Numbers) (Mg : Meaning P W)
    (links : List ModelPart) (ps : List Place) (get : A → P × S) (k : ℕ) (a : A × Fr.E.Str)
    (h : onQ N Mg links ps get k a) (hm : (get a.1).2.failed = none) :
    rowsHeld N ((openSets links ps (start links))[k]?.getD []) (get a.1).2 = true ∧
      membersHeld N ((openSets links ps (start links))[k]?.getD []) (get a.1).2 = true := by
  rcases h.2 with h' | h'
  · exact absurd hm h'
  · have e := h'.1
    simp only [Bool.and_eq_true] at e
    exact ⟨e.1.1.1.1.2, e.1.1.1.2⟩

/-- Where a link is open, the frame that K10's sub-protocol reads is that link's own. -/
theorem frame_of_link (s : S) (L : OnBytes.Model.LinkCtx)
    (h : s.link? = some L) : (rdK s).2.1 = L.check.frame := by
  show s.live.frame = _
  unfold S.live
  rw [h]

variable (cs : OnBytes.Codes) (lo : List (OracleShape × ℕ)) (seat : Fin lo.length → ℕ × ℕ)
  (kb : Fin lo.length → Bool) (R : RowsK (sigOf cs lo)) (N : SlotNames R)

/-- **RowAsks AT THE TABLE's OPEN SET, SIX FIELDS PAID.** -/
theorem rowAsks_of {A P W : Type} {Fr : Frame} (Nu : Numbers) (Mg : Meaning P W)
    (links : List ModelPart) (ps : List Place) (get : A → P × S) (k m : ℕ)
    {Rch : ℕ → A × Fr.E.Str → Prop} {d : FoldData} {reqW : P → Array UInt32}
    (FF : FoldFacts Rch (fun a : A × Fr.E.Str => get a.1) d reqW links ps)
    (no : Fin lo.length → ℕ) (a : A × Fr.E.Str) (hon : onQ Nu Mg links ps get k a)
    (hr : Rch k a) (hu : (get a.1).2.failed = none) (p : Place) (hp : ps[k]? = some p)
    (hl : p.link = some m) (sub : ModelPart) (hst : standAt links p = .link sub)
    (hgr : d.groupAt m = Nu.groupAt m) (hcs : d.sent.codes = cs)
    (ties : ∀ G lay, (rdK (get a.1).2).2.2.groups[(rdK (get a.1).2).2.1.group]? = some G →
      (begun (rdK (get a.1).2).2.2 (rdK (get a.1).2).2.1.group G).layout
        (rdK (get a.1).2).2.1.group = some lay →
      CubeFits R (begun (rdK (get a.1).2).2.2 (rdK (get a.1).2).2.1.group G) lay
          (fun b => no b.1) ∧
        NamesFit R N (begun (rdK (get a.1).2).2.2 (rdK (get a.1).2).2.1.group G) lay
          fun b => no b.1)
    (names : ∀ G, (rdK (get a.1).2).2.2.groups[(rdK (get a.1).2).2.1.group]? = some G → ∀ q x,
      N.orc q < (begun (rdK (get a.1).2).2.2 (rdK (get a.1).2).2.1.group G).oracles.size ∧
        N.idx q x <
          tableSize (begun (rdK (get a.1).2).2.2 (rdK (get a.1).2).2.1.group G) (N.orc q) .main)
    (seats : ∀ i, memMain lo i → seatBy noFirst (get a.1).2.book (no i) = some (seat i))
    (shapes : ∀ Gr, (rdK (get a.1).2).2.2.groups[(rdK (get a.1).2).2.1.group]? = some Gr →
      ShapesAre (rdK (get a.1).2).2.2 Gr lo kb no) :
    RowAsks cs lo seat kb R N Nu m ((openSets links ps (start links))[k]?.getD []) no
      (get a.1).2 := by
  have hsh := VerifiableInference.Desc.First.K8.shapeAt_of_onQ Nu Mg links ps get k a hon hu
  rw [hp] at hsh
  unfold VerifiableInference.Desc.First.shapeAt at hsh
  simp only [Bool.and_eq_true, beq_iff_eq] at hsh
  obtain ⟨L, hL⟩ := link_of_stand (get a.1).2 sub (hsh.1.1.trans hst)
  have hh := held_of_onQ Nu Mg links ps get k a hon hu
  exact
    { inOrder := (OnBytes.Means.tidy4B_iff.1 (FF.tidy k a hr hu)).inOrder
      ties := ties
      names := names
      grp := by
        rw [frame_of_link _ L hL]
        exact (FF.groupIs k a p m L hr hu hp hl hL).2.trans hgr
      rows := hh.1
      members := hh.2
      apart := apart_of_facts FF k a hr hu
      codes := (FF.codes k a hr hu).trans hcs
      seats := seats
      shapes := shapes }

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.link_of_stand
#print axioms VerifiableInference.Desc.First.Close.held_of_onQ
#print axioms VerifiableInference.Desc.First.Close.frame_of_link
#print axioms VerifiableInference.Desc.First.Close.rowAsks_of
