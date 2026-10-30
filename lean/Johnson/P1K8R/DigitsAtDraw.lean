-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/DigitsAtDraw.lean: THE FIELD "digits" OF `K8LeftT` (Johnson/P1K8R/TightAt.lean), TO
THE LETTER, AT EACH OF THE 25 LINKS, FROM THE HEAD `P5J.AtMgA`, ONE CLOSED FACT AND ONE SENTENCE ON
THE STATE BEHIND THE DRAW: `DigAheadOk`. A thin rule: a joining of several files'
theorems. THE WEIGHT STAYS IN `DigAheadOk`.
  `tlAt_of_plan`: in scope's two numbers (four sub-proofs a group; 12 groups): what
    `First.Look.tlAt` returns at link l is the link's own planned value (`P1K8S.PlanAt`).
  `six_behind_draw`: at a reached state in front of link l's draw, and a yes of the draw: the state
    behind holds parameters whose six fields NM, tau, mats, ix.ZZ, mz, off are the built link's:
    five by `P1K8S.k8LaidOwn` and `planAt_built`; tau BY THE DRAW's OWN YES
    (`placeRec_of_decide`: the decision compares the state's number of combinations with the
    place's, which is the built link's by the make); the draw's one writing turns none of the six.
  `k08_digits_of_ahead`: **the field**: by `digitsAt_mgAll`
    (Johnson/Desc/Sound/MgAt/K3DigitsAt.lean) at the constant's letters; its premise hE by
    `digMu_cellsAhead` (Johnson/Desc/First/Look/K3DigitsAhead.lean) from K.
THE PREMISES THAT ARE LEFT. hx: `First.Look.digAt (At.X Zp) l = some (x, tl)`: a closed fact on the
public parameters · K: `DigAheadOk` at the state behind the draw and the witness, under the field's
own four antecedents: SHOWN AT NO STATE (the lookups' own Limits).
Limits. A member of the head `AtMgA` is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction; side library
AtFullSide/Top/). At `OnBytes.secondHashFunction` alone. Nothing on soundness or on hiding.

-/
import Johnson.P1K8R.TightAt
import Johnson.Desc.Sound.MgAt.K3DigitsAt
import Johnson.Desc.First.Look.K3DigitsAhead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T

open Iop
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj Johnson.Pack
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Block Chain Claim Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S flatPlacesOf)
open VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.First.K8.Ready
open Johnson.Desc.First.Walk.Tied (RchAt)
open Desc.K14.Law (secondAt seatZ)
open ProofFile (Cl)
open P5J (AtMgA mgAtAll)

/-- What the lookups' reader of the plan returns is the link's own planned value. -/
theorem tlAt_of_plan {X : Verify.Public} (p4 : X.p4 = true) (ng : X.NGr = 12) {l : ℕ}
    {tl tlP : HTailF2} (h1 : VerifiableInference.Desc.First.Look.tlAt X l = some tl)
    (h2 : P1K8S.PlanAt X l tlP) : tl = tlP := by
  unfold VerifiableInference.Desc.First.Look.tlAt at h1
  simp only [p4, ng, if_true] at h1
  rcases h2 with ⟨rfl, rfl⟩ | ⟨g, hp, hg, rfl, e, rfl⟩ | ⟨g, a, hg, rfl, e, rfl⟩
  · simpa using h1.symm
  · have a1 : (2 * g == 2 * 12) = false := by
      rw [beq_eq_false_iff_ne]
      omega
    have a2 : (2 * g % 2 == 0) = true := by
      rw [beq_iff_eq]
      omega
    have a3 : 2 * g / 2 = g := by omega
    rw [a1, a2, a3, e] at h1
    simpa using h1.symm
  · have a1 : (2 * g + 1 == 2 * 12) = false := by
      rw [beq_eq_false_iff_ne]
      omega
    have a2 : ((2 * g + 1) % 2 == 0) = false := by
      rw [beq_eq_false_iff_ne]
      omega
    have a3 : (2 * g + 1) / 2 = g := by omega
    rw [a1, a2, a3, e] at h1
    simpa using h1.symm

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **The six fields that "the digits are in their tables" reads, behind the draw.** -/
theorem six_behind_draw (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : ℕ} (hl : l ≤ 24) {Xl : LinkH}
    (e3 : G.built[l]? = some Xl) {Str : Type} (a : (ProofFile.InstPub × S) × Str)
    (hr : RchAt (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) (drawAt l) a) {t : S}
    (hy : ∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS (ProofFile.k8ParW Zp G Xl l).toPar).decide a.1.2 rs gs =
      .ok t) :
    ∃ ts, t.tl? = some ts ∧ ts.NM = Xl.tl.NM ∧ ts.tau = Xl.tl.tau ∧ ts.mats = Xl.tl.mats ∧
      ts.ix.ZZ = Xl.tl.ix.ZZ ∧ ts.mz = Xl.tl.mz ∧ ts.off = Xl.tl.off := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  obtain ⟨rs, gs, hy⟩ := hy
  have hx : (l, if l = 24 then 5 else 4) ∈ P1K8S.places :=
    List.mem_map.2 ⟨l, List.mem_range.2 (Nat.lt_succ_of_le hl), rfl⟩
  have hr' : RchAt (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF)
      (14 * l + (if l = 24 then 5 else 4) + 2) a := by
    rw [← drawAt_place l]
    exact hr
  obtain ⟨tlP, hP, h7, -⟩ := P1K8S.k8LaidOwn h.scope h.reads O hx a hr'
  obtain rfl : tlP = Xl.tl := P1K8S.planAt_built h.scope h.reads O e3 hP
  obtain ⟨tl0, mm, f, ht0, rfl⟩ := drawn_of_yes _ _ _ rs gs hy
  have e7 := lay7_of_test h7
  unfold lay7 at e7
  rw [ht0] at e7
  have e7' : seven tl0 = seven Xl.tl := Option.some.inj e7
  simp only [seven, Prod.mk.injEq] at e7'
  obtain ⟨-, b2, b3, b4, b5, -, b7⟩ := e7'
  have hτ : tl0.tau = Xl.tl.tau := (placeRec_of_decide _ tl0 _ _ rs gs ht0 hy).tau
  exact ⟨_, putTl_tl _ tl0 _ ht0, b5, hτ, b7, congrArg (·.ZZ) b2, b3, b4⟩

/-- **THE FIELD "digits", TO THE LETTER, FROM `DigAheadOk` BEHIND THE DRAW.** -/
theorem k08_digits_of_ahead (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {Fr : Frame}
    {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : ℕ} (hl : l ≤ 24)
    {Xl : LinkH} (e3 : G.built[l]? = some Xl)
    {Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop}
    (hRch : ∀ k a, Rch k a → RchAt (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) k a)
    {x : VerifiableInference.Desc.First.Look.Place} {tl : HTailF2}
    (hx : VerifiableInference.Desc.First.Look.digAt (P5J.At.X Zp) l = some (x, tl))
    (K : ∀ (z : ProofFile.InstPub) (a b : S × Fr.E.Str)
      (w : Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT),
      onQ (P5J.At.N Zp cF) (mgAtAll h) linksFull (flatPlacesOf linksFull true)
        (fun s => (z, s)) (drawAt l) a →
      Rch (drawAt l) ((z, a.1), a.2) →
      ¬ a.1.failed ≠ none →
      (∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS (ProofFile.k8ParW Zp G Xl l).toPar).decide a.1 rs gs =
        .ok b.1) →
      VerifiableInference.OnPublicFiles.DigAheadOk x tl h.𝔇.sent h.𝔇.l3.rad
        (fun j => h.𝔇.l3.seat x.link true j.1) h.𝔇.l3.arr h.𝔇.ms h.𝔇.N l b.1 w) :
    ∀ (z : ProofFile.InstPub) (a b : S × Fr.E.Str) w,
      onQ (P5J.At.N Zp cF) (mgAtAll h) linksFull (flatPlacesOf linksFull true)
        (fun s => (z, s)) (drawAt l) a →
      Rch (drawAt l) ((z, a.1), a.2) →
      ¬ a.1.failed ≠ none →
      (∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS (ProofFile.k8ParW Zp G Xl l).toPar).decide a.1 rs gs =
        .ok b.1) →
      (mgAtAll h).constr l .lookDigits (z, b.1) (strsOf Fr b.2) w →
      DigitsAt (cellsAhead (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) l
        (z, b.1)) b.1 w := by
  intro z a b w hq hr hm hy hc
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  have eW : Bs.G₀.W = P5J.At.X Zp := Except.ok.inj (O.public.symm.trans h.pubOne)
  obtain ⟨p4, ng, -⟩ := Meaning.scope_plans h.scope h.reads h.pubOne
  obtain ⟨ts, hts, c1, c2, c3, c4, c5, c6⟩ :=
    six_behind_draw h hG hl e3 ((z, a.1), a.2) (hRch _ _ hr) hy
  -- the lookups' parameters are the built link's
  have hx' : (l, if l = 24 then 5 else 4) ∈ P1K8S.places :=
    List.mem_map.2 ⟨l, List.mem_range.2 (Nat.lt_succ_of_le hl), rfl⟩
  have hr' : RchAt (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF)
      (14 * l + (if l = 24 then 5 else 4) + 2) ((z, a.1), a.2) := by
    rw [← drawAt_place l]
    exact hRch _ _ hr
  obtain ⟨tlP, hP, -, -⟩ := P1K8S.k8LaidOwn h.scope h.reads O hx' _ hr'
  have eP : tlP = Xl.tl := P1K8S.planAt_built h.scope h.reads O e3 hP
  rw [eW] at hP
  have eT : tl = Xl.tl := (tlAt_of_plan p4 ng
    (VerifiableInference.Desc.First.Look.digAt_is
      (VerifiableInference.Desc.First.Look.shapeZAll_of_public h.pubOne) hx) hP).trans eP
  refine VerifiableInference.OnPublicFiles.digitsAt_mgAll h.𝔇 mgBase h.pubOne rfl hx z b.1
    (strsOf Fr b.2) w ⟨ts, hts, fun A => VerifiableInference.OnPublicFiles.digitsOf_six tl ts
      (by rw [c1, eT]) (by rw [c2, eT]) (by rw [c3, eT]) (by rw [c4, eT]) (by rw [c5, eT])
      (by rw [c6, eT]) A⟩
    (VerifiableInference.OnPublicFiles.digMu_cellsAhead x tl h.𝔇.sent h.𝔇.l3.rad _ h.𝔇.l3.arr h.𝔇.ms
      h.𝔇.N l z b.1 w (K z a b w hq hr hm hy)) hc

end P1K8T

#print axioms P1K8T.tlAt_of_plan
#print axioms P1K8T.six_behind_draw
#print axioms P1K8T.k08_digits_of_ahead
