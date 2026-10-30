-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Total/PlanesAt341MgAll.lean: the kind "lookup" (K3).
Conditional: at the composed meaning of all kinds (Johnson/Desc/Sound/MgAll.lean): from the item
worth 24 3 "planes" in front of the sub-protocol at the output head to the item formsT 24 3 "planes"
behind its acceptance: the library's `planes_mgAll` (Johnson/Desc/Kinds/Law/K6PlanesAtMgAll.lean)
the other way. Theorems.

Terms. Honest/K3/GLOSSARY.md, and the head of Honest/K3/Law/Total/PlanesAt341.lean. In this file: a
is the state in front of the sub-protocol at the output head, b the state behind its acceptance.

What is shown.
  `place_of_caller`: the place of the table's item "left" at link 24 has the caller's shape, packing
    and first slot.
  `planes_back_mgAll`: `planes_mgAll` with its hypothesis on the forms' sentence and its conclusion
    exchanged.
  `planes_field_mgAll`: so the field formsT at 24 3 "planes", where that name stands for the one run
    (2, "planes").
The statements speak of no thread, prover or coin.

Hypotheses that remain. None of them is shown in this file.
  those of `planes_mgAll`, name for name: they are the calling kind's: `h6`, `hd`, `hOn`: b6 is the
    sub-protocol at link 24, the decision of `Sound.below b6` (b6 with the test on the words in
    front) accepts, and `K6On` holds in front; what the link's second sub-protocol that states runs
    states under "planes" (`hSt`); the reader's equation (`hRd`); four
    facts on the state behind (`ha`, `hns`, `hArr`, `hSA`); the width of the reads' array (`hwide`);
    an inequality on the plan's numbers (`hlen`); the shape (`hsh`, `hok`); `hnu`, the two readings
    are one.
  `hruns`: (in `planes_field_mgAll`) the name "planes" at 24 3 stands for the one run (2, "planes").
  `hin`: (new here) the public test formsInT behind.
  `hw`: (new here) the item in front.
  `hRange`: (new here) the witness's cells are in range. The composed meaning says the item in front
    under that condition, as an implication, so it is to be shown beside the item.
  `hL`: (new here) the table's public item "left" in front, which gives the list of rounds.
  `C`, `hlm`: the caller's two equations (`CallerFits`, Johnson/Desc/Kinds/Law/K6WorthAtMgAll.lean);
    the packing is the head's.

Imported. PlanesAt341.lean and K6PlanesAtMgAll.lean.
By a program's count, modules under Johnson/Goal/ (all under Johnson/Goal/Meaning/) stand
in the import closure of the library's file: they come in beneath files of the library that lie
outside that folder. None is imported here; no name of that folder is called here.

How the proof goes. `planes_back_mgAll` is one call of `planes_arm_back_item` (PlanesAt341.lean).
That the place of the item "left" has the caller's shape, packing and first slot is no hypothesis:
`place_of_caller` shows it from the caller's own two equations, by the texts of the library's
`headAt`, `placeAt` and `P.ofPlace`. The library's `placeAt_headAt`
(Johnson/Desc/First/Look/K3HeadStated.lean) says the like, but stands under that file's instance
variables (three: Sizes, Policy, Request), which are not at hand here; so it is not called.

Limits. All statements are implications. No instance of these hypotheses is exhibited in this file.
At the full size (the composed meaning's letters). The head's link alone.
The question of the reading (the head of PlanesAt341.lean) is here that of `hw`: the item in front
is asked at the composed meaning's own reading (`headNu`,
Johnson/Desc/First/Look/K3HeadGoodIn.lean). No statement of this file says that what shows that item
on the honest side reaches that reading.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Total.PlanesAt341
import Johnson.Desc.Kinds.Law.K6PlanesAtMgAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Law.Total
open OnBytes
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head VerifiableInference.Desc.Kinds.Head.Law
open VerifiableInference.Desc.Kinds.Head.Law.AtTable
open VerifiableInference.OnPublicFiles (headLink headNu k3AdrAt k3LeftItemAt)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (S Meaning)
open VerifiableInference.Desc.Sound (MsgT MgData mgAll)

variable {Xi P Tok : Type} {rows cols nR : ℕ} {Wp : OnBytes.Model.Verify.Public}
  {D : MgData Xi P Tok rows cols nR Wp}
  (Mg : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT))

/-- The place of the table's item "left" at link 24 has the caller's shape, packing and first
slot. Conditional on the caller's two equations (`CallerFits`) and on the packing being the
head's. No instance of these hypotheses is exhibited in this file. -/
theorem place_of_caller {x : First.Look.Place} (C : CallerFits (Wp := Wp) x)
    (hlm : x.lm = Wp.hS.lmbH) :
    ∀ p, First.Look.placeAt Wp 24 false = some p →
      p.shape = some x.fs ∧ p.lm = Wp.hS.lmbH ∧ p.first = x.F.next := by
  intro p hp
  have e24 : (if Wp.p4 then 2 else 1) * Wp.NGr = 24 := C.seg
  have hx := C.place
  unfold VerifiableInference.Desc.Kinds.Head.Law.headAt at hx
  obtain ⟨x', h1, hx⟩ := Option.bind_eq_some_iff.1 hx
  obtain ⟨h', hh, rfl⟩ := Option.map_eq_some_iff.1 hx
  unfold First.Look.placeAt at hp
  rw [e24] at h1
  rw [h1] at hp
  obtain rfl := Option.some.inj hp
  exact ⟨hh, hlm, rfl⟩

/-- **From the item worth 24 3 "planes" in front to the forms' sentence behind.** Here a is the
state in front of the sub-protocol at the output head and b the state behind its acceptance.
Conditional on the hypotheses of the library's `planes_mgAll` but for the forms' sentence; the
public test behind; the item in front; the witness's cells in range; the table's public item "left"
in front. No instance of these hypotheses is exhibited in this file. -/
theorem planes_back_mgAll {x : First.Look.Place} (C : CallerFits (Wp := Wp) x)
    (hlm : x.lm = Wp.hS.lmbH)
    (a b : P × S) (y : Strs) (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (b6 : Block S Unit)
    (h6 : blockOf Wp 24 = some b6) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hd : (Sound.below b6).decide a.2 rs gs = .ok b.2) (hOn : K6On Wp a.2)
    (states : Nat → List (K9.RunOf S)) (hSt : PlanesStates (readsOf Wp) Wp.hS.lmbH states 2)
    (hRd : (D.Rd 24).forms 2 "planes" b.2 = k6Silent (p8K6 Wp 24) states 2 "planes" b.2)
    (hin : K9.formsInT (D.Rd 24) (D.N.sent 24 0) 2 "planes" b.2 = true)
    (aK : K9.Part) (ha : K9.segAt? b.2 = some aK) (hns : aK.F.ns = Wp.H.ns) (cU : Nat × String)
    (hArr : aK.L.arrayOf[readsOf Wp]? = some cU) (hSA : StatedAt Wp (p8K6 Wp 24) D.St b.2 cU)
    (hwide : ∀ e F tr, withTables (p8K6 Wp 24) b.2 = some e → e.fork? = some F →
      F.trees[readsOf Wp]? = some tr → Wp.H.nU.getD 2 0 ≤ tr.K)
    (hlen : ∀ gk, b.2.lookHeard? = some gk →
      gk.shape.NC * 2 ^ (gk.shape.kT + 5 - Wp.hS.lmbH) ≤
        (Wp.H.tl.mats.getD (Wp.hS.NHf + 1 + 1) {}).k *
          ((Wp.H.tl.mats.getD (Wp.hS.NHf + 1 + 1) {}).m / 2 ^ Wp.hS.lmbH))
    (hsh : ∀ g, a.2.lookHeard? = some g → g.shape = x.fs) (hok : FoNums.ok x.fs = true)
    (hnu : ∀ pq, nuK6 Wp b.2
        (Sound.dataQ (D.N.sent 24 0) aK (Sound.seatTab D.cs D.arr D.ms w)) pq =
      headNu (k3AdrAt Wp) x Wp.H.tl D.sent D.l3.rad D.l3.oW D.l3.wOf D.l3.nr D.l3.nc
        (fun j => D.l3.seat x.link false j.1) D.l3.arr D.l3.msgW w pq)
    (hRange : VerifiableInference.OnPublicFiles.Flat.InRange w.cells)
    (hw : (mgAll D Mg).worth 24 3 "planes" a y w) (hL : k3LeftItemAt Wp 24 a.2) :
    Sound.formsTQ (D.Rd 24) D.St (D.N.sent 24 0) 2 "planes" b.2
      (Sound.seatTab D.cs D.arr D.ms w) := by
  rw [← C.seg, Sound.mgAll_worth_head_planes D Mg C.place a y w] at hw
  have hw' := hw hRange
  have e : nuK6 Wp b.2 (Sound.dataQ (D.N.sent 24 0) aK (Sound.seatTab D.cs D.arr D.ms w)) =
      headNu (k3AdrAt Wp) x Wp.H.tl D.sent D.l3.rad D.l3.oW D.l3.wOf D.l3.nr D.l3.nc
        (fun j => D.l3.seat x.link false j.1) D.l3.arr D.l3.msgW w := funext hnu
  refine planes_arm_back_item Wp 24 b6 h6 a.2 b.2 rs gs hd hOn (p8K6 Wp 24) 2 states hSt (D.Rd 24)
    D.St (D.N.sent 24 0) (Sound.seatTab D.cs D.arr D.ms w) hRd hin (cellsK6 Wp) (nuK6 Wp) aK ha
    (fun j hj => by
      rw [(hSA _).1 j]
      show _ = if j < Wp.H.ns then _ else 0
      rw [if_pos (hns ▸ hj)])
    cU hArr (fun pos => (hSA _).2 pos) hwide hlen x.fs hsh hok x.F.next hL
    (place_of_caller C hlm)
    (fun g F' hF hg => ?_)
  have k := hw' g F' hF hg
  rw [hlm] at k
  rw [e]
  exact k

/-- **So the field formsT at 24 3 "planes" behind.** Conditional on the same, and on that name
standing for the one run (2, "planes"). No instance of these hypotheses is exhibited in this file.
-/
theorem planes_field_mgAll {x : First.Look.Place} (C : CallerFits (Wp := Wp) x)
    (hlm : x.lm = Wp.hS.lmbH)
    (a b : P × S) (y : Strs) (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (b6 : Block S Unit)
    (h6 : blockOf Wp 24 = some b6) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hd : (Sound.below b6).decide a.2 rs gs = .ok b.2) (hOn : K6On Wp a.2)
    (states : Nat → List (K9.RunOf S)) (hSt : PlanesStates (readsOf Wp) Wp.hS.lmbH states 2)
    (hRd : (D.Rd 24).forms 2 "planes" b.2 = k6Silent (p8K6 Wp 24) states 2 "planes" b.2)
    (hin : K9.formsInT (D.Rd 24) (D.N.sent 24 0) 2 "planes" b.2 = true)
    (aK : K9.Part) (ha : K9.segAt? b.2 = some aK) (hns : aK.F.ns = Wp.H.ns) (cU : Nat × String)
    (hArr : aK.L.arrayOf[readsOf Wp]? = some cU) (hSA : StatedAt Wp (p8K6 Wp 24) D.St b.2 cU)
    (hwide : ∀ e F tr, withTables (p8K6 Wp 24) b.2 = some e → e.fork? = some F →
      F.trees[readsOf Wp]? = some tr → Wp.H.nU.getD 2 0 ≤ tr.K)
    (hlen : ∀ gk, b.2.lookHeard? = some gk →
      gk.shape.NC * 2 ^ (gk.shape.kT + 5 - Wp.hS.lmbH) ≤
        (Wp.H.tl.mats.getD (Wp.hS.NHf + 1 + 1) {}).k *
          ((Wp.H.tl.mats.getD (Wp.hS.NHf + 1 + 1) {}).m / 2 ^ Wp.hS.lmbH))
    (hsh : ∀ g, a.2.lookHeard? = some g → g.shape = x.fs) (hok : FoNums.ok x.fs = true)
    (hnu : ∀ pq, nuK6 Wp b.2
        (Sound.dataQ (D.N.sent 24 0) aK (Sound.seatTab D.cs D.arr D.ms w)) pq =
      headNu (k3AdrAt Wp) x Wp.H.tl D.sent D.l3.rad D.l3.oW D.l3.wOf D.l3.nr D.l3.nc
        (fun j => D.l3.seat x.link false j.1) D.l3.arr D.l3.msgW w pq)
    (hRange : VerifiableInference.OnPublicFiles.Flat.InRange w.cells)
    (hw : (mgAll D Mg).worth 24 3 "planes" a y w) (hL : k3LeftItemAt Wp 24 a.2)
    (hruns : D.runs 24 3 "planes" = [(2, "planes")]) :
    (mgAll D Mg).formsT 24 3 "planes" b y w := by
  rw [Sound.mgAll_formsT]
  refine ⟨fun p hp' => ?_, fun h => absurd h (by decide)⟩
  rw [hruns] at hp'
  obtain rfl := List.mem_singleton.1 hp'
  exact planes_back_mgAll Mg C hlm a b y w b6 h6 rs gs hd hOn states hSt hRd hin aK ha hns cU
    hArr hSA hwide hlen hsh hok hnu hRange hw hL

end ProofFile.Honest.K3.Law.Total

#print axioms ProofFile.Honest.K3.Law.Total.place_of_caller
#print axioms ProofFile.Honest.K3.Law.Total.planes_back_mgAll
#print axioms ProofFile.Honest.K3.Law.Total.planes_field_mgAll
