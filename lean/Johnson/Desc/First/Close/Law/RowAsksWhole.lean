-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Close/Law/RowAsksWhole.lean (kind K10): `RowAsks` (HRowAtFa.lean, beside this
file:
what the rows' part of K10's law asks of the statement in front) WHOLE, AT THE WRITTEN LIST's TYPED
GROUP AND ITS NAMES, IN ONE CALL: the six fields that rowAsks_of (RowAsksOf.lean) pays, and "ties"
and
"names" from "shapes" by ties_of_shapes and names_of_shapes (ShapesBegun.lean). A
theorem: an assembly.

What is said. `rowAsks_whole`: RowAsks cs lo seat kb (groupLayK ..) (namesOf .. no) Nu m O no s, at
O := the table's open set at border k and s := the state in front.

PREMISES.
  on the state: FF (the facts on reached states) · hon (the table's promise) · hr (reached) · hu (no
    mark) · **shapes** (ShapesAre at the frame's group: at the constant: AtMg.shapes_at,
    Johnson/P5J/ShapesAtMg.lean) · **seats** (the book places message no i at the plan's seat of
    member i: hs_k10) · hc (at the begun statement's layout the two codes' lengths are
    the stage's).
  closed: hp, hl, hst (the place at number k) · hgr · hcs · hA (LayoutAgrees lo kb: sealed at every
    written list: linksFull_layout) · hinj (no parts the list's members) · hk, hh (the stage's two
    numbers).

Limits. BOOK-KEEPING. NOTHING IS SHOWN OF ANY STATE. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.RowAsksOf
import Johnson.Desc.First.Close.Law.ShapesBegun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice Cb Johnson.Top.H Johnson.Pack
open VerifiableInference.Desc.Sound
open Johnson.G (memMain)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (S ModelPart Numbers Meaning FoldFacts FoldData start openSets
  standAt Stand)

/-- **RowAsks, WHOLE, IN ONE CALL.** -/
theorem rowAsks_whole (cs : OnBytes.Codes) (lo : List (OracleShape × ℕ))
    (seat : Fin lo.length → ℕ × ℕ) (s : Sg) (e : ℕ) (kb : Fin lo.length → Bool)
    (hM : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 → cMain cs (lo.get i).1 = s.C)
    (hZ : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 → cMask cs (lo.get i).1 = s.Z)
    {A P W : Type} {Fr : Frame} (Nu : Numbers) (Mg : Meaning P W)
    (links : List ModelPart) (ps : List Place) (get : A → P × S) (k m : ℕ)
    {Rch : ℕ → A × Fr.E.Str → Prop} {d : FoldData} {reqW : P → Array UInt32}
    (FF : FoldFacts Rch (fun a : A × Fr.E.Str => get a.1) d reqW links ps)
    (no : Fin lo.length → ℕ) (a : A × Fr.E.Str) (hon : onQ Nu Mg links ps get k a)
    (hr : Rch k a) (hu : (get a.1).2.failed = none) (p : Place) (hp : ps[k]? = some p)
    (hl : p.link = some m) (sub : ModelPart) (hst : standAt links p = .link sub)
    (hgr : d.groupAt m = Nu.groupAt m) (hcs : d.sent.codes = cs)
    (hA : LayoutAgrees lo kb)
    (hinj : ∀ i ∈ membersOf lo, ∀ j ∈ membersOf lo, no i = no j → i = j)
    (hk : kLay lo kb = s.h + s.g) (hh : s.h = 0)
    (hc : ∀ G lay, (rdK (get a.1).2).2.2.groups[(rdK (get a.1).2).2.1.group]? = some G →
      (begun (rdK (get a.1).2).2.2 (rdK (get a.1).2).2.1.group G).layout
        (rdK (get a.1).2).2.1.group = some lay →
      2 ^ lay.logEll = s.C.l ∧ 2 ^ lay.logEllZk = s.Z.l)
    (seats : ∀ i, memMain lo i → seatBy noFirst (get a.1).2.book (no i) = some (seat i))
    (shapes : ∀ Gr, (rdK (get a.1).2).2.2.groups[(rdK (get a.1).2).2.1.group]? = some Gr →
      ShapesAre (rdK (get a.1).2).2.2 Gr lo kb no) :
    RowAsks cs lo seat kb (groupLayK cs lo s e kb hM hZ) (namesOf cs lo s e kb hM hZ no) Nu m
      ((openSets links ps (start links))[k]?.getD []) no (get a.1).2 :=
  rowAsks_of cs lo seat kb _ _ Nu Mg links ps get k m FF no a hon hr hu p hp hl sub hst hgr hcs
    (ties_of_shapes _ shapes hA hinj hk hh hc)
    (names_of_shapes _ (OnBytes.Means.tidy4B_iff.1 (FF.tidy k a hr hu)).inOrder shapes hA hc)
    seats shapes

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.rowAsks_whole
