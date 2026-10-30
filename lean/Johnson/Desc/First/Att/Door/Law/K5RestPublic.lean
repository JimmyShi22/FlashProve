-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5RestPublic.lean: kind K5: FIVE FIELDS OF K5Rest (K5AtMgPaid.lean) TAGGED [P] (tests on public data) AND ONE TAGGED [C] (nsOf), AS THEOREMS AT THE COMPOSED MEANING's CLOSED CONSTANT, under the one head h : AtMgA o Z D r Zp Np cF x: lmIs · posG · planesOkAt · colsFit · nsOf WHOLE;
tiePub DOWN TO ITS ONE UNPAID HALF SymsOK.

Why. K5LeftFitsI.lean proves the four from PlanIs · profile 4 · the group's plan · the place · the guard's yes; OwesAtOpen.lean proves tiePub from an opening under SymsOK. Here each is called at the
constant's letters, where these premises are theorems (K5AtConstant.lean · K5RestOpen.lean).

Main names: `lmIs_all` · `ofPlan_all` · `posG_all` · `planesOkAt_all` · `colsFit_all` · `nsOf_all` (the built segment 2 g + 1 has the plan's number of slots: K05_built_of_open with the library's buildLinksH_keeps, after nsOf_plus) · `tiePub_all` (under hSy : SymsOK x₁ a.seam.tl h.𝔇.sent h.𝔇.l3.rad) · `rest_public`: THE CHECK.
Is it empty here? Under the head: A MEMBER OF IT IS PROVED AT `storedPublicFiles` AND `zGap` ALONE (AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/). SymsOK at the constant's radii h.𝔇.l3.rad: unpaid; evaluated at other radii's letter alone.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5RestOpen
import Johnson.Desc.First.Att.Door.Law.K5LeftFitsI
import Johnson.H2K5R.BuiltOfPub
import OnBytes.TieK.LinksEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Door
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (lookAt)
open VerifiableInference.Desc.First.Att.P
open VerifiableInference.Desc.K12.Door (Laid)
open OnBytes.Road.L5 (Zs)
open P5J (AtMgA mgAtAll TS)

section
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA o Z D r Zp Np cF x)
include h

theorem lmIs_all {g : ℕ} {a : Attention.Plan} {x₁ : Look.Place} (ha : (P5J.At.X Zp).A[g]? = some a)
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) : x₁.lm = a.S.cf.lmb := lmIs_plus (P5J.At.X Zp) g a x₁ (scope_all h).1 ha hx

/-- The group's plan is one that the planner returns. -/
theorem ofPlan_all {g : ℕ} {a : Attention.Plan} (ha : (P5J.At.X Zp).A[g]? = some a) : K5Law.OfPlan a := by
  obtain ⟨A0, pf, h0, e⟩ := planIs_all h g a ha
  exact ⟨_, _, _, A0, pf, h0, e⟩

theorem posG_all {g : ℕ} (hg : g < 12) {a : Attention.Plan} (ha : (P5J.At.X Zp).A[g]? = some a) {blk : Block S Claim}
    (hb : k5AtN (P5J.At.X Zp) (2 * g + 1) g (beforeAll Zp g) = some blk) : K5Law.PosG (parCOf a).geo :=
  posG_plus h.𝔇.sent (P5J.At.X Zp) g (beforeAll Zp g) a h.𝔇.l3.rad (planIs_all h) (scope_all h).1 ha (seatedOk_guard_all h hg hb).2
    (planOk_plus (beforeAll Zp g) hb (seatedOk_guard_all h hg hb).1 ha) (claimsOk_plus (beforeAll Zp g) hb (seatedOk_guard_all h hg hb).1 ha)

theorem planesOkAt_all {g : ℕ} {a : Attention.Plan} {x₁ : Look.Place} (ha : (P5J.At.X Zp).A[g]? = some a)
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) : Look.planesOk x₁.fs (parCOf a).geo.lmb = true :=
  planesOkAt_plus (P5J.At.X Zp) g a x₁ (planIs_all h) (scope_all h).1 ha hx

theorem colsFit_all {g : ℕ} {a : Attention.Plan} {x₁ : Look.Place} (ha : (P5J.At.X Zp).A[g]? = some a)
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) :
    x₁.fs.NC * 2 ^ (x₁.fs.kT + 5 - a.S.cf.lmb) ≤
      (a.seam.tl.mats.getD (a.S.cf.NAs + 2) {}).k * ((a.seam.tl.mats.getD (a.S.cf.NAs + 2) {}).m / 2 ^ a.S.cf.lmb) :=
  colsFit_plus a x₁ (ofPlan_all h ha) (place_calls (scope_all h).1 ha hx).2.2.2

/-- **nsOf**: the built segment 2 g + 1 has the attention plan's number of slots. -/
theorem nsOf_all {g : ℕ} (hg : g < 12) {a : Attention.Plan} (ha : (P5J.At.X Zp).A[g]? = some a) : h.𝔇.pubD.nsOf (2 * g + 1) = some a.ns := by
  obtain ⟨Bs, base, O, hW⟩ := open_all h
  obtain ⟨h4, h12, -⟩ := scope_all h
  obtain ⟨-, l₀, -, hB, H⟩ := K05_built_of_open O
  obtain ⟨Y, hY, hns⟩ := H g a (by rw [hW]; exact h4) (by rw [hW, h12]; exact hg) (by rw [hW]; exact ha)
  have hk := OnBytes.TieK.buildLinksH_keeps (fun l : Stages.LinkH => l.ns) (fun _ _ => rfl) hB
  have h2 : (Zp.p.built.links.toList.map fun l : Stages.LinkH => l.ns)[2 * g + 1]? = (l₀.toList.map fun l : Stages.LinkH => l.ns)[2 * g + 1]? := by
    rw [hk]
  rw [List.getElem?_map, List.getElem?_map, Array.getElem?_toList, Array.getElem?_toList, hY] at h2
  show (Zp.p.built.links[2 * g + 1]?).map (fun l : Stages.LinkH => l.ns) = some a.ns
  rw [h2]
  exact congrArg some hns

/-- **tiePub, down to SymsOK.** -/
theorem tiePub_all {g : ℕ} (hg : g < 12) {a : Attention.Plan} (ha : (P5J.At.X Zp).A[g]? = some a) {x₁ : Look.Place}
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) (hSy : SymsOK x₁ a.seam.tl h.𝔇.sent h.𝔇.l3.rad) :
    TiePub h.𝔇.sent x₁ a.seam.tl a.ns h.𝔇.l3.rad := by
  obtain ⟨Bs, base, O, hW⟩ := open_all h
  obtain ⟨h4, h12, -⟩ := scope_all h
  exact tiePub_of_open O h.laid.planOk h.laid.asks (by rw [hW]; exact h4) (g := g) (by rw [hW, h12]; exact hg) (by rw [hW]; exact ha)
    (by rw [hW]; exact hx) h.𝔇.l3.rad hSy

/-- **THE CHECK: the six, laid over a member.** -/
theorem rest_public {Fr : Frame} {Ld : Laid} {Ms : List OracleShape} {bs g : ℕ} {a : Attention.Plan} {x₁ : Look.Place}
    {pl : VerifiableInference.Desc.Place} {O : List Item} {Q : List Pub} {Lk : Link S Claim} {same : S → S → Bool} {blk : Block S Claim}
    {nm : String} {Zof : Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT → Zs} (hg : g < 12) (ha : (P5J.At.X Zp).A[g]? = some a)
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) (hb : k5AtN (P5J.At.X Zp) (2 * g + 1) g (beforeAll Zp g) = some blk)
    (hSy : SymsOK x₁ a.seam.tl h.𝔇.sent h.𝔇.l3.rad)
    (R : K5RestAll (Fr := Fr) h Ld Ms bs g (beforeAll Zp g) a x₁ pl O Q Lk same blk nm Zof) :
    K5RestAll (Fr := Fr) h Ld Ms bs g (beforeAll Zp g) a x₁ pl O Q Lk same blk nm Zof :=
  { R with
    lmIs := lmIs_all h ha hx
    posG := posG_all h hg ha hb
    planesOkAt := planesOkAt_all h ha hx
    colsFit := colsFit_all h ha hx
    nsOf := nsOf_all h hg ha
    tiePub := tiePub_all h hg ha hx hSy }

end

end H2K5.Door

#print axioms H2K5.Door.lmIs_all
#print axioms H2K5.Door.ofPlan_all
#print axioms H2K5.Door.posG_all
#print axioms H2K5.Door.planesOkAt_all
#print axioms H2K5.Door.colsFit_all
#print axioms H2K5.Door.nsOf_all
#print axioms H2K5.Door.tiePub_all
#print axioms H2K5.Door.rest_public
