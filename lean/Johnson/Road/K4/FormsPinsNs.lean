-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/FormsPinsNs.lean: THE PREMISE hns OF forms_pins (Johnson/Road/K4/FormsAtPins.lean)
CONCLUDED: behind an accepting run of K4's sub-protocol, inside the table's promise in front, the
ledger's number of slots is the number that the public parameters' list of rounds gives the group.

  `ns_front`: at an unmarked verifier's state inside the table's promise at border k, in a layers'
    segment, the ledger's number of slots is n. Premises: H (border k is K4's place of segment m:
    the table's; in the caller's hand) · Kf (K4Front at the condition LeftQ n: the first conjunct
    of k4Row_of_means, Johnson/Road/K4/K4RowOfMeans.lean).
  `hns_of_front`: hns of forms_pins, to the letter, at every nV with n ≤ nV. Premises: H · Kf.
  `place_ns`: the place that layAt finds at a layers' segment has the group's number of slots.
    Premises: publicOf's return and three lines on the public parameters (K4RowPlan's fields
    pubOf · notHead · step · plan) · hx (WorthTies.place, Johnson/Road/K4/K4PinsEndFill.lean).
  `forms_pins_ns`: forms_pins at nV := x.ns, hns struck. In its stead: H · Kf at LeftQ par.hp.ns
    · hx · the four of place_ns at hp := par.hp. Its other premises are forms_pins' own, unpaid
    here: E hRd hruns hk hcs · asks · hO hArr hMask hCells hell · hsits hcov · hSt.
No new argument: k4_left_front (Johnson/Road/K4/K4PromiseFront.lean), the library's PadLeft.rest,
LeftQ's second clause (Johnson/Desc/First/Look/K3LeftItem.lean), ns_behind (FormsAtPins.lean),
layAt_plan (Johnson/Road/K4/K4PinsScope.lean). ns_of_leftAt (Johnson/Road/K4/CloseK3.lean) has the
bound at a seat; ns_front says the equation at the segment's own ledger.
Limits. Kf is a premise: it is concluded from K4Means and tests on the public parameters elsewhere.
hell (x.ns ≤ maskEllP A) stays a premise. Met through Lean at no member. AT THE COMPOSED MEANING's
OWN SMALL LIST OF EXTRA PUBLIC TESTS (moreAll, Johnson/Desc/Sound/MoreAll.lean) forms_pins_ns AND
hns_of_front SAY NOTHING: the premise hO (openAllB) rejects there, and Kf hangs on names that have
left: they speak at a wider meaning alone. K04_law, the law of K4's sub-protocol itself, IS NOT
PROVED. Nothing on soundness.


-/
import Johnson.Road.K4.FormsAtPins
import Johnson.Road.K4.K4PromiseFront
import Johnson.Road.K4.K4PinsScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Road.K4

open Iop OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Flat OnBytes.Maker
open OnBytes.Model.Layer (Pub Own Lay HPlan2)
open OnBytes.Desc.First.K4 (Par seatS seatS_fork formsBack)
open OnBytes.Desc.First.K4.Total (KeptAsks)
open OnBytes.Road.K4.InT (InTAsks StatesAt)
open OnBytes.Road.K4.Rec (recPlanOf readsArrayP maskPlanB maskEllP arraysPlanB openAllB)
open _root_.Run (ckP)
open VerifiableInference.Desc (Place Wit Claim Link K9.LinkHoles K9.statesOfLink K9.readersOfLink)
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers)
open VerifiableInference.Desc.First.Look (sigListCalls layAt)
open VerifiableInference.Desc.Sound (Frame Piece onQ meansQ MsgT StatedIs)
open VerifiableInference.Desc.Plain.K04 (FormsT frontRun)
open VerifiableInference.OnPublicFiles (LeftQ)

section
variable {P W Cl : Type} {Fr : Frame} {N : Numbers} {Mg : Meaning P W} {Z : P} {links : List ModelPart}
  {ps : List Place} {k m : ℕ} {pl : Place} {h3 : Forest.Shape} {lm first n : ℕ}

/-- In front of K4's sub-protocol, inside the table's promise, at an unmarked state: the segment's
ledger has n slots. -/
theorem ns_front (H : AtK4 links ps k m pl) (Kf : K4Front Mg Z links ps m h3 lm first (LeftQ n))
    {a : S × Fr.E.Str} (ha : onQ N Mg links ps (fun s => (Z, s)) k a) (hu : a.1.failed = none) :
    ∀ a₀, a.1.here = .lay a₀ → a₀.F.ns = n := by
  intro a₀ h0
  obtain ⟨F, F', _, _, hq, _, K, _, hk⟩ := k4_left_front N Mg Z H Kf ha hu
  obtain rfl : seatS.fork a.1 = F' := Option.some.inj hk
  rw [← seatS_fork h0, K.padLeft.rest.2.1]
  exact hq.2.1

/-- **hns of forms_pins**: behind an accepting run the ledger's number of slots is at most nV. -/
theorem hns_of_front {Tok : Type} {rows cols : ℕ}
    {Mg : Meaning P (Wit (CellsK rows cols) Tok MsgT)} (H : AtK4 links ps k m pl)
    (Kf : K4Front Mg Z links ps m h3 lm first (LeftQ n))
    {q : Piece (ckP .two) Fr S Cl (Wit (CellsK rows cols) Tok MsgT)}
    {par : Par} {nV : ℕ} (hV : n ≤ nV) :
    ∀ a τ fo o G', onQ N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' →
      ∀ G, (behindOf seatS q a τ o G').1.fork? = some G → G.ns ≤ nV :=
  fun _ _ _ _ _ ha hu Y =>
    ns_behind Y fun a₀ h0 => Nat.le_trans (Nat.le_of_eq (ns_front H Kf ha hu a₀ h0)) hV

end

/-- The place that layAt finds at a layers' segment has the group's number of slots. -/
theorem place_ns {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public} {m : ℕ}
    {hp : HPlan2} (h : Verify.publicOf pol KL layout = .ok X)
    (hn : m ≠ (if X.p4 then 2 else 1) * X.NGr) (h0 : m % (if X.p4 then 2 else 1) = 0)
    (hplan : X.G[m / (if X.p4 then 2 else 1)]? = some hp)
    {x : VerifiableInference.Desc.First.Look.Place} (hx : layAt X m = some x) : x.ns = hp.ns := by
  obtain ⟨x', hx', _, _, _, _, en⟩ := layAt_plan h hn h0 hplan
  obtain rfl : x' = x := Option.some.inj (hx'.symm.trans hx)
  exact en

variable [scl : Inst.Model.Scl] {Xi P Tok Cl : Type} {rows cols nR kC : ℕ} {X : Verify.Public}
  {Fr : Frame}
  {Mg : Meaning P (Wit (CellsK rows cols) Tok MsgT)} {D : K4Data Xi P Tok rows cols nR kC X} {Z : P}
  {links : List ModelPart} {ps : List Place} {k m : ℕ} {pl : Place}
  {q : Piece (ckP .two) Fr S Cl (Wit (CellsK rows cols) Tok MsgT)} {par : Par}

/-- **THE LINE "forms" AT THE PINNED VALUE, hns struck**, at nV := the place's number of slots,
under E hRd hruns hk hcs · asks · hO hArr hMask hCells hell · hsits hcov · hSt (forms_pins' own)
and, in the stead of hns: H Kf · hpub hn h0 hplan hx. -/
theorem forms_pins_ns (A : PinPlan (CellsK rows cols))
    (x : VerifiableInference.Desc.First.Look.Place) (y : Lay)
    (nM nRr nC n0 ns nx v7 : ℕ) (hg : par.g < 12) (E : K4Means Mg D) {Hh : K9.LinkHoles}
    {l : Link S Claim} (hRd : D.Rd m = K9.readersOfLink Hh l)
    (hruns : D.runs m 3 "own" = [(2, "front"), (2, "back")]) (hk : par.k3Runs = true)
    (hcs : A.D.codes = D.cs)
    (asks : ∀ a τ fo o G', onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' → ∃ (P₀ : Pub) (o₀ : Own),
        KeptAsks par a.1 (behindOf seatS q a τ o G').1 P₀ o₀ ∧
        InTAsks (D.N.sent m 0) par a.1 (behindOf seatS q a τ o G').1 ∧
        StatesAt (K9.statesOfLink l) 2 par "front" (behindOf seatS q a τ o G').1 ∧
        StatesAt (K9.statesOfLink l) 2 par "back" (behindOf seatS q a τ o G').1)
    (hO : openAllB D.moreL links ps k m = true)
    (hArr : readsArrayP par.hp D.D3.shape D.D3.layout (D.D3.arrayOf.getD m #[]) m (D.sd.trees m) =
      true)
    (hMask : maskPlanB A (D.N.sent m 0) (recPlanOf D D.sd) (D.N.msgsAt ps[k]?) m = true)
    (hCells : arraysPlanB A par.hp.tl (D.N.sent m 0) (recPlanOf D D.sd) (D.N.msgsAt ps[k]?) m =
      true)
    (hell : x.ns ≤ maskEllP A)
    (hsits : SitsIn (sigListCalls A.D A.rad A.link) A.seatT D.ms D.N m)
    (hcov : Covers par.hp.tl nM nRr nC)
    (H : AtK4 links ps k m pl) {h3 : Forest.Shape} {lm first : ℕ}
    (Kf : K4Front Mg Z links ps m h3 lm first (LeftQ par.hp.ns))
    {pol KL : ByteArray} {layout : Option ByteArray}
    (hpub : Verify.publicOf pol KL layout = .ok X)
    (hn : m ≠ (if X.p4 then 2 else 1) * X.NGr) (h0 : m % (if X.p4 then 2 else 1) = 0)
    (hplan : X.G[m / (if X.p4 then 2 else 1)]? = some par.hp) (hx : layAt X m = some x)
    (hSt : ∀ a τ fo o G', onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' →
      StatedIs D.St (uLay par.hp.tl fun _ B => matsOfB A par.hp.tl B)
        (behindOf seatS q a τ o G').1) :
    ∀ b w, keptFrom (tableOn0 D.N Mg Z links ps k) par q b →
      onQ D.N Mg links ps (fun s => (Z, s)) (k + 1) b → b.1.failed = none →
      meansQ (Fr := Fr) D.N Mg (fun s => (Z, s)) (.formsT m 3 "own") b w →
      FormsT seatS
        (((A.seatN x.ns D.N par.hp.tl y nM nRr nC n0 ns nx v7).atRec X par hg).semOf
          (partOf A.D.codes D.arr D.ms D.N m) par.hp.tl) (frontRun par) formsBack b.1 w :=
  forms_pins A x.ns y nM nRr nC n0 ns nx v7 hg E hRd hruns hk hcs asks hO hArr hMask hCells hell
    hsits hcov (hns_of_front H Kf (Nat.le_of_eq (place_ns hpub hn h0 hplan hx).symm)) hSt

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.ns_front
#print axioms OnBytes.Road.K4.hns_of_front
#print axioms OnBytes.Road.K4.place_ns
#print axioms OnBytes.Road.K4.forms_pins_ns
