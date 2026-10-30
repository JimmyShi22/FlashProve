-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Riders/ObjAsksOfMeans.lean: THE STRUCTURE OF PREMISES `ObjAsks`
(Riders/ObjectsAtMeans.lean: under which the lookup's own claims, the item formsT m 2 "objects", and
the public test tied to it cross an accept of K4's sub-protocol) OUT OF: the structure of equations
`K4Means` · one line of `K4Reads` · tests and equations on the public parameters · AND THE SEAT's
TIE FOR THE LOOKUP's SUB-PROTOCOL. One statement with its proof: field by field.

  `tied_front`: a public test that is tied to an item which is open in front of K4's sub-protocol
    holds of every unmarked state inside the promise there.
  **`objAsks_of_means`**: Rd, runs: two equations on the letters (premises) · fO, oRun, fG, gRun:
    THE SEAT's TIE: the seated segment states, under the names "objects" and "guests", runs that do
    what the lookup's sub-protocol's do (premises: Riders/SeatsTies.lean has them at a sub-protocol
    behind the driver's guard) · bare: out of the name "K4.rowsBare" (`bare_of_means`) · St: the
    line stMask of `K4Reads` · front: out of the promise (`tied_front`), under hopen: the item is
    open in front of K4's sub-protocol: a test on the table.

Limits. The six premises named stand. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED.
Nothing on soundness.
-/
import Johnson.Road.K4.K4Reads
import Johnson.Road.K4.Riders.ObjectsAtMeans
import Johnson.Road.K4.Riders.MoreFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Riders

open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4.Riders (ObjRun GuestRun)
open VerifiableInference.Desc (Place Wit Claim Link K9.LinkHoles K9.statesOfLink K9.readersOfLink)
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning start openSets pubOfItems pubFit)
open VerifiableInference.Desc.First.FillBare (rowsBareB bareName)
open VerifiableInference.Desc.Sound (Frame onQ MsgT)

variable {Xi P Tok : Type} {rows cols nR kC : ℕ} {X : Verify.Public} {Fr : Frame}
  {Mg : Meaning P (Wit (CellsK rows cols) Tok MsgT)} {D : K4Data Xi P Tok rows cols nR kC X} {Z : P}
  {links : List ModelPart} {ps : List Place} {k m : ℕ} {pl : Place}

/-- A public test tied to an item that is open at the border holds there. -/
theorem tied_front {x : Pub}
    (hx : x ∈ pubOfItems ((openSets links ps (start links))[k]?.getD [])) {a : S × Fr.E.Str}
    (ha : onQ D.N Mg links ps (fun s => (Z, s)) k a) (hu : a.1.failed = none) :
    Mg.pub x (Z, a.1) = true :=
  List.all_eq_true.mp (bools_of_onQ D.N Mg Z ha hu).2.1 x (List.mem_append_right _ hx)

/-- **`ObjAsks`, field by field.** -/
theorem objAsks_of_means (E : K4Means Mg D) {base : ℕ} (R : K4Reads D Z Fr base)
    (H : AtK4 links ps k m pl) (hlinks : D.links = links) (hf : pubFit Mg.more links ps = true)
    (hask : bareName m ∈ (Mg.more.rows links pl).asks)
    (hopen : Item.formsT m 2 "objects" ∈ (openSets links ps (start links))[k]?.getD [])
    {Hh : K9.LinkHoles} {l : Link S Claim} (hRd : D.Rd m = K9.readersOfLink Hh l)
    (hruns : D.runs m 2 "objects" = [(1, "objects"), (1, "guests")]) {nO nG : String}
    {runO runG : ℕ → S → Except String (List Claim × S)}
    (fO : (K9.statesOfLink l 1).find? (fun r => r.1 == "objects") = some (nO, runO))
    (oRun : ObjRun runO)
    (fG : (K9.statesOfLink l 1).find? (fun r => r.1 == "guests") = some (nG, runG))
    (gRun : GuestRun runG) : ObjAsks Fr Mg D Z links ps k m Hh l nO nG runO runG where
  Rd := hRd
  runs := hruns
  fO := fO
  oRun := oRun
  fG := fG
  gRun := gRun
  bare := fun a al g ha hu hal hg => by
    have h := bare_of_means E H hlinks hf hask a ha hu
    unfold rowsBareB at h
    rw [hal] at h
    simp only [hg, Option.any_some] at h
    simpa [Array.all_eq_true_iff_forall_mem, List.all_eq_true] using h
  St := fun s s' h => R.stMask s s' h
  front := fun a ha hu => tied_front (List.mem_flatMap.2 ⟨_, hopen, by simp⟩) ha hu

end OnBytes.Road.K4.Riders

#print axioms OnBytes.Road.K4.Riders.objAsks_of_means
