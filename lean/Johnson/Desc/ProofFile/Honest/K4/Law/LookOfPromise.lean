-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/LookOfPromise.lean: CONDITIONAL.

What is here. WHAT THE LOOKUP HAS HEARD HAS THE PLAN's SHAPE AND SIZES, OUT OF THE PROMISE IN FRONT
OF THE MEMBER OF THE FEED-FORWARD LAYERS' OWN ROUNDS (sub-protocol K4): the public item "behind the
lookup on the calls" (lookOut m 2) is open at that border, and its test (`k3OnOut`,
Johnson/Desc/First/Look/K3Borders.lean) holds the whole shape and the sizes of the lookup's points.
So the sixth fact of the library's `K4Fence` (heard), and five of the eight clauses of `K4LookFacts`
(Law/ReadyOfPromise.lean), are asked of nobody: they come out of the two tests, `K4OnX` and two
comparisons of public numbers. A definition of a hypothesis's form, and statements with their
proofs.

  `out_lay`   of what the item's test holds at a layers' segment: the shape and four sizes, in the
      public parameters' terms.
  `heard_of_tests`   **the sixth fact of `K4Fence`**, from the tests of lookOut m 2 and look m.
  `K4LookRest p fo`   what stays.
  `lookFacts_of_tests`   **K4LookFacts**, from the two tests, the three comparisons and K4LookRest.
  `two_tests`   the two tests are among those of the public items that are open in front, at the
      library's composed meaning and the full size's written lists.
  `k4ReadyS_of_promise`   **K4ReadyS** (Law/HearsShape.lean) with K4LookRest alone asked on what the
      lookup has heard.

Not shown here. THAT THE HYPOTHESES CAN HOLD TOGETHER: this file gives no example (by binder:
`out_lay`: Sx, h · `heard_of_tests`: Sx, ho, hl · `lookFacts_of_tests`: Sx, ho, hl, h1, h2, h3, hR ·
`two_tests`: ePub, eMore, hH, H, Sx, Sd, t0 · `k4ReadyS_of_promise`: ePub, eMore, hH, H, Sx, Sd, hm,
hs, t0, hn, h1, h2, h3, hR, htk). WHAT STAYS IS `K4LookRest`: the calls' points' last coordinates
are read and are the lookup's own; the lookup's weights are as many as its shape's calls: it stands
under h, the hypothesis on the public files (`P5J.AtMgA`), wherever the first chain's thread stands
there, by a statement of the writers of Honest/K3/ (Law/LookJoin.lean, Law/ReadyHead.lean). Three
comparisons of public numbers are asked (la ≤ dT · lt ≤ dT · the shape's calls are as many as the
layout's, at the plan's shape). A LAW, NOT A PART: no file that defines a part of the proof file's
description may import this one: its imports reach Johnson/Goal/. Following import lines, and
stopping unopened at every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/
and at every module whose name begins Cb.Bridge, its imports reach 4 modules under Johnson/Goal/ and
2 under Johnson/Bridge/, and none of the others; what lies behind these is not counted; 29 of the
modules that it reaches have RecCompile in their names, none of them RecCompile's Honest*, Both or
PassH*. An earlier walk, which opened every module that it reached, counted 21 modules under
Johnson/Goal/, 29 whose name holds RecCompile and none under ThirdParty/.

Called. The library's `lastOf_some` (Johnson/Desc/First/K4/Returns/Points.lean): the last k
coordinates of a point of at least k are read, and are k; `place_lay`
(Johnson/Desc/First/Look/K3PlaceLetters.lean): at a layers' segment the place's shape is the public
parameters'; `placeAt_iff` (K3PlaceAt.lean beside it): what `placeAt` returns, unfolded;
`sameShapeAll_eq` (Johnson/Desc/First/Att/Door/ShapeSame.lean); `seatS_look`
(Johnson/Desc/First/K4/SeatS.lean); `k4Means_mgWide` (Johnson/Road/K4/K4MeansAtWide.lean);
`pubWide_hand` (Johnson/Desc/First/PubWide.lean). Ours: `open_at` (Law/PromiseAll.lean),
`k4ReadyS_of_tests` (Law/ReadyOfPromise.lean).

Kin. The converse of `lastOf_some` stands in the library twice, under the name `lastOf_ok`
(Johnson/Road/FormsKeysPoint.lean, OnBytes/Tie/Pv/Lookup/Ends/FoMerged.lean): where the reading
returns, the point has at least k coordinates and what is read is its last k. `look_agrees`
(Johnson/Desc/First/FillK4.lean) is the equation of a segment's two fields that the proofs of
`heard_of_tests` and `lookFacts_of_tests` draw by unfolding the test: not called. The library
carries each of the two tests along its relation `KeptAtS`: `k3OnOutAt_kept`
(Johnson/Road/K4/Riders/KeepsOfMeans.lean), `lookLayB_kept` (Johnson/Road/K4/K4AtMg.lean).
`heard_shape_lay` (Johnson/Desc/First/Look/K3HeardShape.lean) has the end «g.shape = X.y.fo» from
the lookup's own accept, not from the promise's test; the sentence heard is also the third field of
the library's `PubFront` (Johnson/Road/K4/More/MadeEleven.lean).

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.ReadyOfPromise
import Johnson.Desc.First.Look.K3PlaceLetters
import Johnson.Desc.First.Look.K3BoolsAt
import Johnson.Desc.First.Att.Door.ShapeSame

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E)
open OnBytes.Model (Forest.Heard Fork lastOf cutLast Verify.Public)
open OnBytes.Desc.First.K4 (Par seatS)
open OnBytes.Desc.First.K4.Rt (lastOf_some)
open OnBytes.Desc.First.K4.RtPub (zkFits zkSize)
open OnBytes.Road.K4 (K4OnX)
open VerifiableInference.Desc (First.S)
open VerifiableInference.Desc.First.FillK4 (lookLayB)
open VerifiableInference.Desc.First.Look (k3OnOutAt placeAt placeAt_iff place_lay)
open VerifiableInference.Desc.K3 (k3OnOut heardAt)

variable {X : Verify.Public} {pol KL : ByteArray} {layout : Option ByteArray} {m : Nat} {par : Par}

/-- **Of what the test of "behind the lookup on the calls" holds: the shape and four sizes**, at a
layers' segment. -/
theorem out_lay (Sx : K4OnX X pol KL layout m par) {s : First.S}
    (h : k3OnOutAt X m false s = true) :
    ∃ g, s.lookHeard? = some g ∧ g.shape = X.y.fo ∧ X.y.fo.calls.size = X.y.fo.NC ∧
      g.zx.size = X.y.fo.dT ∧ g.zk.size = X.y.fo.NC ∧
      ∀ c, c < X.y.fo.calls.size →
        (g.zk.getD c #[]).size = ((X.y.fo.calls[c]?).map (·.n)).getD 0 := by
  unfold k3OnOutAt at h
  cases e : placeAt X m false with
  | none =>
    rw [e] at h
    cases h
  | some p =>
    rw [e, Option.any_some] at h
    obtain ⟨_, _, esh, _, _, _⟩ := place_lay Sx.pubOf e Sx.notHead Sx.step
    have ed : p.digits = false := by
      obtain ⟨x, _, rfl⟩ := placeAt_iff.1 e
      rfl
    unfold k3OnOut heardAt at h
    rw [esh, ed] at h
    simp only [Bool.false_eq_true, if_false] at h
    cases eg : s.lookHeard? with
    | none =>
      cases eG : s.fork? <;>
      · rw [eg, eG] at h
        cases h
    | some g =>
      cases eG : s.fork? with
      | none =>
        rw [eg, eG] at h
        cases h
      | some G =>
        rw [eg, eG] at h
        simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
        obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, _⟩, a5⟩, a6⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := h
        exact ⟨g, rfl, H2K5.Door.sameShapeAll_eq a1, a2, a3, a5, a6⟩

/-- **THE SIXTH FACT OF `K4Fence`**: what the lookup has heard has the public parameters' shape. -/
theorem heard_of_tests (Sx : K4OnX X pol KL layout m par) {s : First.S}
    (ho : k3OnOutAt X m false s = true) (hl : lookLayB s = true) :
    ∀ al fo', s.here = .lay al → al.fo = some fo' → fo'.shape = X.y.fo := by
  intro al fo' ha hfo
  obtain ⟨g, eg, esh, -⟩ := out_lay Sx ho
  unfold lookLayB at hl
  rw [ha] at hl
  dsimp only at hl
  rw [Bool.and_eq_true, decide_eq_true_eq] at hl
  have e1 : s.lookHeard? = al.lookHeard := by
    unfold VerifiableInference.Desc.First.S.lookHeard?
    rw [ha]
  have e2 : some fo' = some g := by rw [← hfo, hl.2, ← e1, eg]
  rw [Option.some.inj e2]
  exact esh

/-- **What stays of `K4LookFacts`.** This defines a hypothesis; the definition claims nothing. -/
structure K4LookRest (p : Par) (fo : Forest.Heard) : Prop where
  merged : ∀ Z, (lastOf fo.zx p.P.y.h.la).toOption = some Z →
    ∃ ends, (fo.zk.mapM fun zk => (lastOf zk p.P.y.h.la).toOption) = some ends ∧
      ends.all (· == Z) = true
  weights : fo.e.size = fo.shape.NC

/-- **The facts on what the lookup has heard**, from the two tests. -/
theorem lookFacts_of_tests (Sx : K4OnX X pol KL layout m par) {s : First.S}
    (ho : k3OnOutAt X m false s = true) (hl : lookLayB s = true)
    (h1 : par.P.y.h.la ≤ par.P.y.fo.dT) (h2 : par.P.y.h.lt ≤ par.P.y.fo.dT)
    (h3 : par.P.y.fo.calls.size = par.P.y.calls.size)
    (hR : ∀ fo, seatS.look s = some fo → K4LookRest par fo) :
    ∀ fo, seatS.look s = some fo → K4LookFacts par fo := by
  intro fo hlk
  obtain ⟨g, eg, esh, ec, ezx, ezk, ezc⟩ := out_lay Sx ho
  cases ha : s.here with
  | lay al =>
    rw [OnBytes.Desc.First.K4.seatS_look ha] at hlk
    have hsh := heard_of_tests Sx ho hl al fo ha hlk
    have efg : fo = g := by
      unfold lookLayB at hl
      rw [ha] at hl
      dsimp only at hl
      rw [Bool.and_eq_true, decide_eq_true_eq] at hl
      have e1 : s.lookHeard? = al.lookHeard := by
        unfold VerifiableInference.Desc.First.S.lookHeard?
        rw [ha]
      exact Option.some.inj (by rw [← hlk, hl.2, ← e1, eg])
    subst efg
    rw [Sx.shape] at hsh ec ezx ezk ezc
    obtain ⟨Z, z1, -⟩ := lastOf_some (z := fo.zx) (k := par.P.y.h.la) (by rw [ezx]; exact h1)
    obtain ⟨ztF, z2, z3⟩ := lastOf_some (z := fo.zx) (k := par.P.y.h.lt) (by rw [ezx]; exact h2)
    obtain ⟨hm, hw⟩ := hR fo (by rw [OnBytes.Desc.First.K4.seatS_look ha]; exact hlk)
    obtain ⟨ends, m1, m2⟩ := hm Z z1
    refine ⟨hsh, Z, ztF, ends, z1, m1, z2, z3, ?_, by rw [hw, hsh, ← ec, h3], m2⟩
    unfold zkFits
    rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
    refine ⟨ezk, fun q hq => ?_⟩
    rw [beq_iff_eq]
    exact ezc q (by rw [ec]; exact List.mem_range.1 hq)
  | between => simp [seatS, ha] at hlk
  | att _ => simp [seatS, ha] at hlk
  | head _ => simp [seatS, ha] at hlk
  | fin _ => simp [seatS, ha] at hlk
  | mem _ => simp [seatS, ha] at hlk

/-! ## Out of the promise's public test -/

section
open OnBytes.Desc.First.K4.Rt (k4Takes)
open OnBytes.Desc.First.K4.RtPub (tokensFit)
open OnBytes.Road.K4 (CellsK AtK4 K4OnD k4Means_mgWide)
open OnBytes.Road.K4.More (PS)
open VerifiableInference.Desc (Place Wit)
open VerifiableInference.Desc.First (Meaning pubAll shapeAt pubWide_hand pubSets openSets start
  pubHeld classA)
open VerifiableInference.Desc.First.FillK4 (isLay)
open VerifiableInference.OnPublicFiles (headLink)
open VerifiableInference.Desc.Sound (MsgT mgWide MgData WideData mgBase linksFull moreAll)

variable {Xi P Tok : Type} {rows cols nR : ℕ} {Dm : MgData Xi P Tok rows cols nR X}

/-- The closed base, at the witness's type. -/
local notation "Bm" => (mgBase (P := P) (W := Wit (CellsK rows cols) Tok MsgT))

/-- The table's public items (`Pub` alone would name another type in this namespace). -/
local notation "PubI" => VerifiableInference.Desc.First.Pub

/-- **The two tests are among those of the public items that are open in front of the member.**
E₀: any value serves. -/
theorem two_tests (E₀ : WideData P) {Mg : Meaning P (Wit (CellsK rows cols) Tok MsgT)} {k n : ℕ}
    {pl : Place} (ePub : Mg.pub = pubAll Dm.pubD (Bm).pub) (eMore : Mg.more = moreAll)
    (hH : isLay Dm.links (headLink X) = false) (H : AtK4 linksFull PS k m pl)
    (Sx : K4OnX X pol KL layout m par) (Sd : K4OnD Dm m par n) {z : P} {s : First.S}
    (t0 : ∀ q ∈ (pubSets Mg.more linksFull PS)[k]?.getD [], Mg.pub q (z, s) = true) :
    k3OnOutAt X m false s = true ∧ lookLayB s = true := by
  obtain ⟨oQ, -, -, -⟩ := open_at H
  have Em := k4Means_mgWide Dm E₀ Bm hH (fun _ _ _ _ h => h) fun _ _ _ => rfl
  have hand : ∀ (q : PubI), classA q = false → ∀ a,
      (mgWide Dm E₀ Bm).pub q a = Mg.pub q a := fun q hq a => by
    rw [ePub]
    exact pubWide_hand E₀.d12 E₀.dP Dm.pubD (Bm).pub q hq a
  have t : ∀ q ∈ k4OpenQ m, Mg.pub q (z, s) = true := by
    intro q hq
    refine t0 q ?_
    rw [eMore, oQ]
    exact hq
  have hlay : isLay Dm.links m = true := by
    rw [Sd.links]
    unfold isLay
    rw [H.sub]
    rfl
  have t1 := t (.lookOut m 2) (by simp [k4OpenQ])
  rw [← hand _ rfl] at t1
  have e1 := Em.lookOut m false (z, s)
  rw [Sx.pc2] at e1
  rw [e1] at t1
  have t2 := t (.look m) (by simp [k4OpenQ])
  rw [← hand _ rfl, Em.look m _ hlay] at t2
  exact ⟨t1, t2⟩

/-- **THE STATE IN FRONT, OUT OF THE PROMISE's TESTS**, with `K4LookRest` alone asked on what the
lookup has heard. E₀: any value serves. -/
theorem k4ReadyS_of_promise (E₀ : WideData P) {Mg : Meaning P (Wit (CellsK rows cols) Tok MsgT)}
    {k n k' : ℕ} {pl : Place} (ePub : Mg.pub = pubAll Dm.pubD (Bm).pub)
    (eMore : Mg.more = moreAll) (hH : isLay Dm.links (headLink X) = false)
    (H : AtK4 linksFull PS k m pl) (Sx : K4OnX X pol KL layout m par) (Sd : K4OnD Dm m par n)
    {z : P} {s : First.S} (hm : s.failed = none) (hs : shapeAt linksFull (some pl) s = true)
    (t0 : ∀ q ∈ (pubSets Mg.more linksFull PS)[k]?.getD [], Mg.pub q (z, s) = true)
    (hn : n + (k4Takes par.P par.hp par.g + k') ≤ par.hp.ns)
    (h1 : par.P.y.h.la ≤ par.P.y.fo.dT) (h2 : par.P.y.h.lt ≤ par.P.y.fo.dT)
    (h3 : par.P.y.fo.calls.size = par.P.y.calls.size)
    (hR : ∀ fo, seatS.look s = some fo → K4LookRest par fo)
    (htk : tokensFit { par.P with tokv := seatS.tokv s } par.g = true) : K4ReadyS par s := by
  obtain ⟨t1, t2⟩ := two_tests E₀ ePub eMore hH H Sx Sd t0
  exact k4ReadyS_of_tests E₀ ePub eMore hH H Sd hm hs t0 hn
    (lookFacts_of_tests Sx t1 t2 h1 h2 h3 hR) htk

end

end ProofFile.Honest.K4



#print axioms ProofFile.Honest.K4.out_lay
#print axioms ProofFile.Honest.K4.heard_of_tests
#print axioms ProofFile.Honest.K4.K4LookRest
#print axioms ProofFile.Honest.K4.lookFacts_of_tests
#print axioms ProofFile.Honest.K4.two_tests
#print axioms ProofFile.Honest.K4.k4ReadyS_of_promise
