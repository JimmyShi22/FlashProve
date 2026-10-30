-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/SlotsTiled.lean: CONDITIONAL: THREE PUBLIC FACTS ON THE PLAN OF AN
ATTENTION SEGMENT, under the library's one head on the public input (`P5J.AtMgA`,
Johnson/P5J/MgAtAll.lean), IN THE FORMS IN WHICH THE LAWS ON THE LIVE SLOTS TAKE THEM
(Johnson/Desc/K5/Honest/Law/LiveState.lean): the plan's number of calls is the length of its shape's
list of calls; the place's numbers and the plan's structure of rounds agree (`LiveFits`); and the
window of the slots that the segment's own rounds take, [k, `k5End` x k), has as many slots as the
library counts for these rounds (`slotsOf` of `script`), so that, from k := the scalars of the
lookup on the calls, it ends where the scalars of the lookup on the digits begin. Numbers alone; no
prover, no state, no draw in it.

How. THE LIBRARY HAS THAT THE PLAN's SLOTS ARE TILED: `plan_tiles`
(Johnson/Desc/First/Att/K05PlanTiles.lean): at every return of the planner ns is the scalars of the
lookup on the calls, then `slotsOf` (`script` own), then the scalars of the lookup on the digits;
`planIs_tiles` (K05PlanOfPublic.lean beside it): the same at a stored plan. Both are called. WHAT IS
DONE HERE: `k5End_slots`: the closed number `k5End`, which goes stage by stage over the plan's
numbers (`kB` … `kH`, Johnson/Desc/First/Att/K05Numbers.lean), is k and that count: by the library's
`script_eq`, `slotsOf_append` and `slotsOf_scalars3`, an induction on the units, and the tail's
sixteen stages by unfolding. `nc_of_plan`, `ns_of_plan`: the planner lays the fields so
(OnBytes/Model/AttentionPlan.lean); the library's nearest on the first, `nc_of_hid`
(Johnson/Road/Lane5SameCalls.lean), speaks of the field NC of the lookup's shape, not of the plan's;
the walk through its text is that of `hplan_of_plan` (Johnson/Desc/K5/Honest/Law/PlanShp.lean).
`liveFits_at_head`: two calls: `public_at_head`, `PublicAll.liveFits`. Kin of `k5End_slots`: the
library's `script_slots` (K05PlanTiles.lean) has the same count in the planner's terms;
`filled_behind` (Johnson/Desc/K5/Honest/Law/FilledBehind.lean) and `k5_next` (LiveSecond.lean), read
together, give it at the next slot of a ledger from which the hearing returns, under their own
premises; no theorem joins the two.

Main names:
  `nc_of_plan`, `nc_ofPlan`, `nc_at_head`: **the number of calls.**
  `ns_of_plan`, `ns_ofPlan`, `ns_at_head`: the number of slots is the number of scalars sent.
  `liveFits_at_head`: **`LiveFits` under the head.**
  `unitsNext_slots`, `k5End_slots`: **the window's length.**
  `tiles_at_head`, `k5End_tiles`, `k5End_msgs`: **the three stretches, as numbers, under the head.**

Limits. The head is a hypothesis. That a state's ledger has its next slot at the scalars of the
lookup on the calls when the segment's own rounds begin is not shown here: k is a letter in
`k5End_slots`, and a written number in `k5End_tiles`. Nothing on which slots the two lookups' claims
name. At the function `OnBytes.secondHashFunction`, of which nothing is asked here.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.PublicAtHead
import Johnson.Desc.K5.Honest.Law.PublicImplies
import Johnson.Desc.K5.Honest.Law.PlanShp
import Johnson.Desc.First.Att.K05PlanOfPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att.P (Stage script slotsOf products tailStages script_eq
  slotsOf_append slotsOf_scalars3 unitsNext own3 ownKey kB kE kV kM kVD kX kF kD kH geoOf)

/-- **The number of calls is the length of the shape's list, at what the planner returns.**
Conditional: the planner's return. -/
theorem nc_of_plan {settings : Settings} {j : Attention.In} {cf : Attention.Cfg}
    {A : Attention.Plan} (h : Attention.plan settings j cf = .ok A) : A.NC = A.S.calls.size := by
  unfold Attention.plan at h
  obtain ⟨-, h⟩ := OnBytes.Road.L5.jp_ok h
  obtain ⟨-, h⟩ := OnBytes.Road.L5.jp_ok h
  obtain ⟨-, h⟩ := OnBytes.Road.L5.jp_ok h
  obtain ⟨r, hr, h⟩ := OnBytes.Road.L5.bind_ok h
  obtain ⟨S, fs⟩ := r
  obtain ⟨-, h⟩ := OnBytes.Road.L5.jp_ok h
  obtain ⟨seam0, -, h⟩ := OnBytes.Road.L5.bind_ok h
  obtain ⟨hn, h⟩ := OnBytes.Road.L5.jp_ok h
  obtain ⟨-, h⟩ := OnBytes.Road.L5.jp_ok h
  obtain ⟨seam, h1, h⟩ := OnBytes.Road.L5.bind_ok h
  have e := Except.ok.inj h
  subst e
  rfl

/-- The same at a plan that is the planner's but for the readers' places of shared matrices. -/
theorem nc_ofPlan {A : Attention.Plan} (h : K5Law.OfPlan A) : A.NC = A.S.calls.size := by
  obtain ⟨_, _, _, A0, pf, h0, rfl⟩ := h
  show A0.NC = A0.S.calls.size
  exact nc_of_plan h0

/-- **The number of slots is the number of scalars sent, at what the planner returns.**
Conditional: the planner's return. -/
theorem ns_of_plan {settings : Settings} {j : Attention.In} {cf : Attention.Cfg}
    {A : Attention.Plan} (h : Attention.plan settings j cf = .ok A) : A.ns = A.nMsg := by
  unfold Attention.plan at h
  obtain ⟨-, h⟩ := OnBytes.Road.L5.jp_ok h
  obtain ⟨-, h⟩ := OnBytes.Road.L5.jp_ok h
  obtain ⟨-, h⟩ := OnBytes.Road.L5.jp_ok h
  obtain ⟨r, hr, h⟩ := OnBytes.Road.L5.bind_ok h
  obtain ⟨S, fs⟩ := r
  obtain ⟨-, h⟩ := OnBytes.Road.L5.jp_ok h
  obtain ⟨seam0, -, h⟩ := OnBytes.Road.L5.bind_ok h
  obtain ⟨hn, h⟩ := OnBytes.Road.L5.jp_ok h
  obtain ⟨-, h⟩ := OnBytes.Road.L5.jp_ok h
  obtain ⟨seam, h1, h⟩ := OnBytes.Road.L5.bind_ok h
  have e := Except.ok.inj h
  subst e
  rfl

/-- The same at a plan that is the planner's but for the readers' places of shared matrices. -/
theorem ns_ofPlan {A : Attention.Plan} (h : K5Law.OfPlan A) : A.ns = A.nMsg := by
  obtain ⟨_, _, _, A0, pf, h0, rfl⟩ := h
  show A0.ns = A0.nMsg
  exact ns_of_plan h0

/-- The next slot behind the units is the slot in front and the units' stages' slots. -/
theorem unitsNext_slots : ∀ (us : List (ℕ × ℕ)) (k : ℕ),
    unitsNext us k = k + slotsOf (us.flatMap fun u => [.scalars 7, products u.1 u.2])
  | [], _ => rfl
  | u :: us, k => by
    show unitsNext us (k + 7 + own3 u.1 + 2 * u.2) =
      k + (7 + ((own3 u.1 + 2 * u.2) +
        slotsOf (us.flatMap fun u => [.scalars 7, products u.1 u.2])))
    rw [unitsNext_slots us]
    omega

/-- **THE WINDOW OF THE SEGMENT's OWN ROUNDS HAS AS MANY SLOTS AS THE LIBRARY COUNTS FOR THEM.** No
premise: x: any structure of rounds; k: any number. -/
theorem k5End_slots (x : Params.AttentionRounds) (k : ℕ) :
    k5End x k = k + slotsOf (script x) := by
  rw [script_eq, slotsOf_append, slotsOf_append, slotsOf_scalars3]
  have u : kB x k = k + 3 * x.planeMessages +
      slotsOf (x.score.flatMap fun u => [.scalars 7, products u.1 u.2]) := unitsNext_slots _ _
  have t : slotsOf (tailStages x) = 5 + (x.lt + (2 + ((own3 x.e + 2 * x.pairs) + (0 + (2 +
      ((own3 x.valueM + 2 * x.pairs) + ((own3 x.valueD + 2 * x.pairs) + (0 + (x.pairs + (0 +
      ((own3 x.attained + 2 * x.pairs) + (0 + ((ownKey x + (x.Lam + x.pairs * x.lt)) + (0 +
      ((own3 x.bits + 2 * x.pairs) + 0))))))))))))))) := rfl
  have eE : kE x k = kB x k + 5 + x.lt + 2 := rfl
  have eV : kV x k = kE x k + own3 x.e + 2 * x.pairs := rfl
  have eM : kM x k = kV x k + 2 := rfl
  have eVD : kVD x k = kM x k + own3 x.valueM + 2 * x.pairs := rfl
  have eX : kX x k = kVD x k + own3 x.valueD + 2 * x.pairs := rfl
  have eF : kF x k = kX x k + x.pairs := rfl
  have eD : kD x k = kF x k + own3 x.attained + 2 * x.pairs := rfl
  have eH : kH x k = kD x k + ownKey x + (x.Lam + x.pairs * x.lt) := rfl
  have eZ : k5End x k = kH x k + own3 x.bits + 2 * x.pairs := rfl
  rw [eZ, eH, eD, eF, eX, eVD, eM, eV, eE, u, t]
  clear eZ eH eD eF eX eVD eM eV eE u t
  generalize own3 x.e = s1
  generalize own3 x.valueM = s2
  generalize own3 x.valueD = s3
  generalize own3 x.attained = s4
  generalize own3 x.bits = s5
  generalize ownKey x = s6
  generalize slotsOf (x.score.flatMap fun u => [.scalars 7, products u.1 u.2]) = s7
  generalize x.pairs * x.lt = s8
  omega

end H2K5.Honest

namespace H2K5.Honest
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Att.P (script slotsOf geoOf planIs_tiles)
open P5J (AtMgA TS)
open H2K5.Door

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
include h

/-- **The number of calls, at the plan of each group, under the head.** Conditional: the head; ea:
the group's plan. -/
theorem nc_at_head {g : ℕ} {a : Attention.Plan} (ea : (P5J.At.X Zp).A[g]? = some a) :
    a.NC = a.S.calls.size := nc_ofPlan (ofPlan_all h ea)

/-- The number of slots is the number of scalars sent, under the head. Conditional: the head; ea. -/
theorem ns_at_head {g : ℕ} {a : Attention.Plan} (ea : (P5J.At.X Zp).A[g]? = some a) :
    a.ns = a.nMsg := ns_ofPlan (ofPlan_all h ea)

/-- **The place's numbers and the plan's structure of rounds agree, under the head.** Conditional:
the head; hg; ea. -/
theorem liveFits_at_head {g : ℕ} (hg : g < 12) {a : Attention.Plan}
    (ea : (P5J.At.X Zp).A[g]? = some a) : LiveFits (geoOf a.S) a.own :=
  (public_at_head h hg ea).liveFits

/-- The library's tiling at the plan of each group, under the head. Conditional: the head; ea. -/
theorem tiles_at_head {g : ℕ} {a : Attention.Plan} (ea : (P5J.At.X Zp).A[g]? = some a) :
    a.ns = Forest.elems a.fs + slotsOf (script a.own) + Forest.elems a.seam.tl.f9 :=
  planIs_tiles (planIs_all h) ea

/-- **THE THREE STRETCHES, AS NUMBERS**: from the scalars of the lookup on the calls the window of
the segment's own rounds ends where the scalars of the lookup on the digits begin, and these end at
the plan's number of slots. Conditional: the head; ea. -/
theorem k5End_tiles {g : ℕ} {a : Attention.Plan} (ea : (P5J.At.X Zp).A[g]? = some a) :
    k5End a.own (Forest.elems a.fs) + Forest.elems a.seam.tl.f9 = a.ns := by
  rw [k5End_slots, tiles_at_head h ea]

/-- The same, to the plan's number of scalars sent. Conditional: the head; ea. -/
theorem k5End_msgs {g : ℕ} {a : Attention.Plan} (ea : (P5J.At.X Zp).A[g]? = some a) :
    k5End a.own (Forest.elems a.fs) + Forest.elems a.seam.tl.f9 = a.nMsg :=
  (k5End_tiles h ea).trans (ns_at_head h ea)

end H2K5.Honest

#print axioms H2K5.Honest.nc_of_plan
#print axioms H2K5.Honest.nc_ofPlan
#print axioms H2K5.Honest.ns_of_plan
#print axioms H2K5.Honest.ns_ofPlan
#print axioms H2K5.Honest.unitsNext_slots
#print axioms H2K5.Honest.k5End_slots
#print axioms H2K5.Honest.nc_at_head
#print axioms H2K5.Honest.ns_at_head
#print axioms H2K5.Honest.liveFits_at_head
#print axioms H2K5.Honest.tiles_at_head
#print axioms H2K5.Honest.k5End_tiles
#print axioms H2K5.Honest.k5End_msgs
