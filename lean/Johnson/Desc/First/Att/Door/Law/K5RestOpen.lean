-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5RestOpen.lean: kind K5: THE SIX FIELDS "FROM AN OPENING" OF K5Rest (K5AtMgPaid.lean), AS THEOREMS AT THE COMPOSED MEANING's CLOSED CONSTANT, under the one head h : AtMgA o Z D r Zp Np cF x (three of them at the format's own
second hash function secondHashFunction alone), AND WHAT THE HEAD GIVES OF THE PLAN AT A GROUP g < 12.

Why. The head opens (K5AtConstant.lean: open_all); OwesAtOpen.lean proves the fields from an opening at the opening's letters; three ties (open_all's second half · sent_meets · lk_meets) carry them to
the constant's letters. The run "planes" comes from k03_planes_of (Johnson/Desc/First/Look/K03States.lean), joined here.

Main names:
  `scope_all`: profile 4 · twelve groups · each group has a plan (the goals' scope: Meaning.scope_plans at the head's scope · reads · pubOne).
  `planAt_all`, `lookC_all`, `lkAt_all`: at g < 12 there is a plan a, a place x₁ of the lookup argument on the calls, a link Lk (so each may be picked by getD: Desc.K14.Law.eq_some_getD, Johnson/Desc/K14/Law/Tries.lean).
  `readersAt_att`, `planesAt_of_open`: the join to k03_planes_of, at an opening.
  `statesAt_all` · `sameOut_all` · `objIs_gstIs_all` · `planesAt_all`: the fields, at same := ProofFile.sameReply · nm := "planes" · claimC := K3Lot.ofForm, for whichever Lk the constant's lk gives.
  BESIDE THE SIX (fields tagged [P], one call each of the same lemmas): `seated_all` · `seatedOk_guard_all`, at before := beforeAll Zp g.
  `rest_open`: THE CHECK: a member of K5RestAll with these fields laid over it.
Is it empty here? Under the head: A MEMBER OF IT IS PROVED AT `storedPublicFiles` AND `zGap` ALONE (AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/). objIs · gstIs · planesAt: at secondHashFunction, in the goals' scope, g < 12 alone.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5RestMake
import Johnson.H2K5R.OwesAtOpen
import Johnson.Desc.First.Look.K03States
import Johnson.Goal.Meaning.PlanShapes
import Johnson.Desc.First.Att.GuardPlan
import Johnson.Desc.First.Look.K3PlaceAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Door
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (lookAt placeAt)
open VerifiableInference.Desc.First.Att.P
open VerifiableInference.Desc.K12.Door (Laid)
open VerifiableInference.OnPublicFiles (k03_planes_of)
open OnBytes.Road.L5 (Zs)
open P5J (AtMgA mgAtAll TS F0T)

/-- The lot's readers of the planes' matrix at an attention segment are the kind's. -/
theorem readersAt_att {W : Verify.Public} {g : ℕ} {a : Attention.Plan} (h4 : W.p4 = true) (ha : W.A[g]? = some a) :
    K3Lot.readersAt W (2 * g + 1) = some (readersOfO a) := by
  obtain ⟨h1, h2, h3⟩ := odd_facts (W := W) (g := g) h4
  show (if ((2 * g + 1) == (if W.p4 then 2 else 1) * W.NGr) = true then _
    else if ((2 * g + 1) % (if W.p4 then 2 else 1) == 0) = true then none
    else (W.A[(2 * g + 1) / (if W.p4 then 2 else 1)]?).map fun A => readersOfO A) = _
  rw [if_neg (fun e => h1 (beq_iff_eq.1 e)), if_neg (fun e => h2 (beq_iff_eq.1 e)), h3, ha]
  rfl

/-- **planesAt, from an opening.** -/
theorem planesAt_of_open {Pf : VerifierAndGoals.PublicFiles} {pp₀ : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
    {base : List (Block S Claim)} {c : Chain S Claim} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope Pf = true)
    (hR : VerifierAndGoals.readFiles Pf = .ok pp₀) (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    (h4 : Bs.G₀.W.p4 = true) {a : Attention.Plan} (ha : Bs.G₀.W.A[g]? = some a) :
    ∃ Lk : Link S Claim, c.links[2 * g + 1]? = some Lk ∧
      ((K9.statesOfLink Lk 1).find? fun c => c.1 == "planes") =
        some (guardC ProofFile.sameReply ("planes", K3.planesRun (K3.seatCalls K3Lot.ofForm) a.S.cf.lmb (readersOfO a))) := by
  have hix : IM.k3Ix (2 * g + 1) false = 1 := by
    show (if false = true then 6 else 1) + (if 2 * g + 1 = 24 then 1 else 0) = 1
    rw [if_neg (by omega : ¬ 2 * g + 1 = 24)]
    rfl
  obtain ⟨Lk, p, e1, hp, hf⟩ := k03_planes_of hS hR O (2 * g + 1) (by omega) _ (readersAt_att h4 ha)
  obtain ⟨x, hx, rfl⟩ := Look.placeAt_iff.1 hp
  have hlm : x.lm = a.S.cf.lmb := (place_att h4 ha hx).2.1
  rw [hix] at hf
  refine ⟨Lk, e1, ?_⟩
  rw [hf, ← hlm]
  rfl

/-- The list "before" of the seated sub-protocol of group g. -/
def beforeAll (Zp : ProofFile.Pub) (g : ℕ) : List (ℕ × ℕ) := (H2K5.k5Before? Zp ("A" ++ toString g)).getD []

section
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA o Z D r Zp Np cF x)
include h

/-- **The goals' scope at the constant's public parameters.** -/
theorem scope_all : (P5J.At.X Zp).p4 = true ∧ (P5J.At.X Zp).NGr = 12 ∧ ∀ g < 12, ∃ a, (P5J.At.X Zp).A[g]? = some a := by
  obtain ⟨h4, h12, -, hA⟩ := _root_.Meaning.scope_plans h.scope h.reads h.pubOne
  exact ⟨h4, h12, fun g hg => (hA g hg).imp fun _ e => e.1⟩

theorem planAt_all {g : ℕ} (hg : g < 12) : ∃ a, (P5J.At.X Zp).A[g]? = some a := (scope_all h).2.2 g hg

/-- What the opening's joint gives at group g, at the constant's letters. -/
theorem facts_all {g : ℕ} (hg : g < 12) :
    ∃ (blk : Block S Claim) (a : Attention.Plan) (x₁ : Look.Place),
      k5AtN (P5J.At.X Zp) (2 * g + 1) g (beforeAll Zp g) = some blk ∧ blk.planOk = true ∧ k5GuardN (P5J.At.X Zp) (2 * g + 1) g = true ∧
      (P5J.At.X Zp).A[g]? = some a ∧ lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ := by
  obtain ⟨Bs, base, O, hW⟩ := open_all h
  obtain ⟨h4, h12, -⟩ := scope_all h
  obtain ⟨blk, a, x₁, e1, e2, e3, e4, e5, -⟩ := K05_facts_at O h.laid.planOk h.laid.asks (by rw [hW]; exact h4) (g := g) (by rw [hW, h12]; exact hg)
  rw [hW] at e1 e3 e4 e5
  exact ⟨blk, a, x₁, e1, e2, e3, e4, e5⟩

theorem lookC_all {g : ℕ} (hg : g < 12) : ∃ x₁, lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ := by
  obtain ⟨-, -, x₁, -, -, -, -, e⟩ := facts_all h hg
  exact ⟨x₁, e⟩

theorem seated_all {g : ℕ} (hg : g < 12) : ∃ blk, k5AtN (P5J.At.X Zp) (2 * g + 1) g (beforeAll Zp g) = some blk := by
  obtain ⟨blk, -, -, e, -⟩ := facts_all h hg
  exact ⟨blk, e⟩

theorem seatedOk_guard_all {g : ℕ} (hg : g < 12) {blk : Block S Claim} (hb : k5AtN (P5J.At.X Zp) (2 * g + 1) g (beforeAll Zp g) = some blk) :
    blk.planOk = true ∧ k5GuardN (P5J.At.X Zp) (2 * g + 1) g = true := by
  obtain ⟨blk', -, -, e, e2, e3, -⟩ := facts_all h hg
  obtain rfl : blk' = blk := Option.some.inj (e.symm.trans hb)
  exact ⟨e2, e3⟩

/-- **statesAt**, with the link. -/
theorem states_all {g : ℕ} (hg : g < 12) {a : Attention.Plan} (ha : (P5J.At.X Zp).A[g]? = some a) :
    ∃ Lk : Link S Claim, P5J.At.lk Zp (2 * g + 1) = some Lk ∧ K9.statesOfLink Lk 2 = (runsN a).map (guardC ProofFile.sameReply) := by
  obtain ⟨Bs, base, O, hW⟩ := open_all h
  obtain ⟨h4, h12, -⟩ := scope_all h
  obtain ⟨Lk, e, hs⟩ := statesAt_of_open O (by rw [hW]; exact h4) (g := g) (by rw [hW, h12]; exact hg) (by rw [hW]; exact ha)
  exact ⟨Lk, (lk_meets O (2 * g + 1)).trans e, hs⟩

/-- **lkAt**: there is a link. -/
theorem lkAt_all {g : ℕ} (hg : g < 12) : ∃ Lk, P5J.At.lk Zp (2 * g + 1) = some Lk := by
  obtain ⟨a, ha⟩ := planAt_all h hg
  obtain ⟨Lk, e, -⟩ := states_all h hg ha
  exact ⟨Lk, e⟩

/-- **statesAt**, for whichever link the constant's lk gives. -/
theorem statesAt_all {g : ℕ} (hg : g < 12) {a : Attention.Plan} (ha : (P5J.At.X Zp).A[g]? = some a) {Lk : Link S Claim}
    (hLk : P5J.At.lk Zp (2 * g + 1) = some Lk) : K9.statesOfLink Lk 2 = (runsN a).map (guardC ProofFile.sameReply) := by
  obtain ⟨Lk', e, hs⟩ := states_all h hg ha
  obtain rfl : Lk' = Lk := Option.some.inj (e.symm.trans hLk)
  exact hs

end

/-- **sameOut.** -/
theorem sameOut_all : ∀ s t : S, t.out = s.out → ProofFile.sameReply s t = true := sameOut_of_open

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
include h

/-- **objIs AND gstIs.** -/
theorem objIs_gstIs_all {g : ℕ} (hg : g < 12) {Lk : Link S Claim} (hLk : P5J.At.lk Zp (2 * g + 1) = some Lk) :
    (∀ (t : S) (F : Fork) (g₁ : Forest.Heard), t.fork? = some F → t.lookHeard? = some g₁ → (∀ f ∈ g₁.rows.toList, f.ents = #[]) →
        (h.𝔇.pubD.Rd (2 * g + 1)).forms 1 "objects" t = some { forms := g₁.rows.toList, late := [] }) ∧
      ∀ (t : S) (F : Fork), t.fork? = some F → (h.𝔇.pubD.Rd (2 * g + 1)).forms 1 "guests" t = some { forms := [], late := [] } := by
  obtain ⟨Bs, base, O, -⟩ := open_all h
  exact objIs_gstIs_of_open h.scope h.reads O hg ((lk_meets O (2 * g + 1)).symm.trans hLk) h.𝔇.pubD.Rd (P5J.At.lk Zp) (P5J.At.X Zp)
    h.𝔇.pubD.mH (rdIs_all h) hLk

/-- **planesAt.** -/
theorem planesAt_all {g : ℕ} (hg : g < 12) {a : Attention.Plan} (ha : (P5J.At.X Zp).A[g]? = some a) {Lk : Link S Claim}
    (hLk : P5J.At.lk Zp (2 * g + 1) = some Lk) :
    ((K9.statesOfLink Lk 1).find? fun c => c.1 == "planes") =
      some (guardC ProofFile.sameReply ("planes", K3.planesRun (K3.seatCalls K3Lot.ofForm) a.S.cf.lmb (readersOfO a))) := by
  obtain ⟨Bs, base, O, hW⟩ := open_all h
  obtain ⟨Lk', e, hp⟩ := planesAt_of_open h.scope h.reads O hg (by rw [hW]; exact (scope_all h).1) (a := a) (by rw [hW]; exact ha)
  obtain rfl : Lk' = Lk := Option.some.inj (e.symm.trans ((lk_meets O (2 * g + 1)).symm.trans hLk))
  exact hp

/-- **THE CHECK: the six, and three beside (seated · seatedOk · guard), laid over a member.** -/
theorem rest_open {Fr : Frame} {Ld : Laid} {Ms : List OracleShape} {bs g : ℕ} {a : Attention.Plan} {x₁ : Look.Place}
    {pl : VerifiableInference.Desc.Place} {O : List Item} {Q : List Pub} {Lk : Link S Claim} {blk : Block S Claim}
    {Zof : Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT → Zs} (hg : g < 12) (ha : (P5J.At.X Zp).A[g]? = some a)
    (hLk : P5J.At.lk Zp (2 * g + 1) = some Lk)
    (hb : k5AtN (P5J.At.X Zp) (2 * g + 1) g (beforeAll Zp g) = some blk)
    (R : K5RestAll (Fr := Fr) h Ld Ms bs g (beforeAll Zp g) a x₁ pl O Q Lk ProofFile.sameReply blk "planes" Zof) :
    K5RestAll (Fr := Fr) h Ld Ms bs g (beforeAll Zp g) a x₁ pl O Q Lk ProofFile.sameReply blk "planes" Zof :=
  { R with
    objIs := (objIs_gstIs_all h hg hLk).1
    gstIs := (objIs_gstIs_all h hg hLk).2
    lkAt := hLk
    statesAt := statesAt_all h hg ha hLk
    sameOut := sameOut_all
    planesAt := planesAt_all h hg ha hLk
    seated := hb
    seatedOk := (seatedOk_guard_all h hg hb).1
    guard := (seatedOk_guard_all h hg hb).2 }

end

end H2K5.Door

#print axioms H2K5.Door.readersAt_att
#print axioms H2K5.Door.planesAt_of_open
#print axioms H2K5.Door.scope_all
#print axioms H2K5.Door.planAt_all
#print axioms H2K5.Door.facts_all
#print axioms H2K5.Door.lookC_all
#print axioms H2K5.Door.seated_all
#print axioms H2K5.Door.seatedOk_guard_all
#print axioms H2K5.Door.states_all
#print axioms H2K5.Door.lkAt_all
#print axioms H2K5.Door.statesAt_all
#print axioms H2K5.Door.sameOut_all
#print axioms H2K5.Door.objIs_gstIs_all
#print axioms H2K5.Door.planesAt_all
#print axioms H2K5.Door.rest_open
