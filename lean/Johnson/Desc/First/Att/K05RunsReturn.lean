-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05RunsReturn.lean: kind K5: THE KIND's FOUR RUNS OF CLAIMS RETURN AT THE VERIFIER's STATE AFTER THE KIND's SUB-PROTOCOL (RunsReturn, Att/K05MadeAt.lean): an ASSEMBLY of what lies:
  returns_at_lk (Att/K05ReturnsLk.lean): the gathering returns (Returns, Att/K05GatheredZero.lean) at every hearing that Said speaks of, where the claims' dry run on the plan alone says yes: THE LAW; its premises drawn here as K05_law_one (Att/K05LawOne.lean) and
  billsFormsJ_of_worths (Att/K05BillsWorth.lean) draw them: from K5Public (tests on public data) and the lookup's sharp promise (hK_of_left · hlk_of_left);
  the conversions from Returns' letters to the seat's (inAt_is · inOf_isAt · keysOfO_is), as in readers_hold₀ (Att/K05BehindWorthReaders.lean).
Main names: behindOk₀_at (BehindOk₀ at one state, straight from the promise, what is asked in front and the hearing's return) · runsReturn_of_returns (the conversion) · runsReturn_at · k5Left_runsRet (under the table's promise, "no mark" and the hearing's return).
PREMISES OF runsReturn_at: Pb : K5Public at the planner's plan A0, with a.S = A0.S · a.fs = A0.fs · one number of the two plans' geometry (a: the stored plan: guard_gives, Att/GuardNLaw.lean, hands all of these) · hl: the lookup's sharp promise · Fa : FrontAll · hFl: every slot
  that the lookup's last claim names is filled in the ledger in front · the hearing's return.
IS IT EMPTY HERE? Implications.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05MadeAt
import Johnson.Desc.First.Att.K05LawOne
import Johnson.Desc.First.Att.K05BehindWorthReaders
import Johnson.Desc.First.Att.K05AtTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Params
open VerifiableInference.Desc (Wit Place)
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Item)
open VerifiableInference.Desc.K9 (Readers segAt? atMoment1)
open VerifiableInference.Desc.Sound (Stated Mem msgsOf MsgT Frame strsOf relAt meansQ outsQ
  second)
open VerifiableInference.Desc.First.Look (Sent JAtt attSg sigListCalls bornAt)
open K5Law (funsAt inAt_is firstAt_is secondAt_is readers_at runsN_is)
open VerifiableInference.Desc.K9 (Read lateOf ownRow readerOf RunOf runOfForms)
open VerifiableInference.Desc.First (onAt Pub)
open VerifiableInference.Desc.First.Look (AttOK)
open OnBytes.Tie.Pv.Att (recOf)
open OnBytes.Slice OnBytes.Flat OnBytes.Maker Run Fo.Peel

/-- **BehindOk₀ at one state.** -/
theorem behindOk₀_at {Cl St₀ J₀ : Type} [DecidableEq J₀] (claim : Aff → Cl) {x : VerifiableInference.Desc.First.Look.Place}
    {A : Attention.Plan} {D : Sent} {hs : Forest.Shape} {lm first : ℕ} {ι : Fo.Pl → Option J₀} {Q : Fork → Prop}
    {x0 : TX (St₀ × Cb.Gl.E) Cb.Gl.E (Option J₀)} {gL : Forest.Heard} {s : First.S}
    (hl : K3LeftOutIs (K3.seatCalls claim).fork (K3.seatCalls claim).heard hs lm first ι Q x0 gL s)
    {own : List (ℕ × ℕ)} {ps : List (ℕ × (ℕ × ℕ))} {qs : List (ℕ × OracleShape)} {hi : ℕ} (Fa : FrontAll x A D own ps qs hi gL s)
    {att : First.AttOwn} (e : s.here = .att att) {xr : Params.AttentionRounds} {rs : List Fmt.RoundView} {hd : Heard} {G : Fork}
    (hh : hear xr (att.F, rs, 0) = some (hd, G, [], 0)) : BehindOk₀ A (plannedK A) gL (behind s att hd G) := by
  obtain ⟨Fm, F', pl, _, hd', hf'⟩ := left_parts hl
  have led : seatSO.ledger s = some att.F := by
    show (match s.here with | .att a => some a.F | _ => none) = _
    rw [e]
  obtain rfl : F' = att.F := Option.some.inj (hf'.symm.trans (ledgerO_fork claim led))
  have hlk : att.lookHeard = some gL := by
    have := hd'
    unfold K3.seatCalls First.S.lookHeard? at this
    simp only [e] at this
    exact this
  obtain ⟨g₀, hg, sm⟩ := Fa.reads att e
  obtain ⟨z0, _, T, hT, hK, hW, hR1⟩ := Fa.ledger att.F led
  obtain ⟨_, bl⟩ := hear_below hh z0
  exact ⟨_, g₀, T, rfl, hg, sm, hlk, by show G.trees[A.iU3]? = some T; rw [bl.trees]; exact hT, hK, hR1, hW, by
      show K3.unpaid G gL.owedJoin = true
      rw [unpaid_below bl]
      exact unpaid_of_left pl⟩

/-- **From the law's Returns to the seat's own words.** -/
theorem runsReturn_of_returns (A A0 : Attention.Plan) (eu : A0.iU3 = A.iU3) {Kc : ℕ} {gL : Forest.Heard} {s₀ : First.S} {att : First.AttOwn} {h : Heard}
    {G : Fork} (B : BehindOk₀ A Kc gL (behind s₀ att h G)) {l : Left} {i : Runs.In} {l₁ l₂ : List Aff} {jn : Runs.JoinsP}
    {kf : Array Aff} {xj : Aff × Fork × OnBytes.K.Kc.Tape}
    (Rt : Returns A.S gL.zx gL.zk G h l A0 gL i Kc l₁ l₂ jn (padOfO gL.shape) kf G [] xj A.seam.tl A.nW
      (lookOfO (parCOf A).geo.lmb gL))
    (hc : gL.cEnd.ents = #[]) (hFl : Fo.FilledA att.F gL.cEnd) : RunsReturn A s₀ att h G := by
  obtain ⟨a₀, g₀, T, he, hg, sm, hlk, hT, hK, hR1, hW, hun⟩ := B
  obtain rfl : a₀ = { att with F := G, heard5 := some h } := by
    have : (First.Here.att { att with F := G, heard5 := some h }) = .att a₀ := he
    cases this
    rfl
  have hT' : G.trees[A.iU3]? = some T := hT
  have u3 : i.iU3 = A.iU3 := Rt.u3.trans eu
  have left : LeftIs (geoOf A.S) g₀.zk h G l := by rw [sm.zk]; exact Rt.left
  have zkI : i.zk = g₀.zk := by rw [sm.zk]; exact Rt.zkI
  have points : pointsOf i.g g₀.zk h l = some i.p := by rw [sm.zk]; exact Rt.points
  have tables : tablesP i.g (K5Law.matsOf A.seam.tl.mats) A.nW (lookOfO (parCOf A).geo.lmb g₀) i.p = some i.t := by
    rw [lookOfO_same sm]; exact Rt.tables
  have hin := inAt_is A left Rt.geo zkI u3 points tables hT' hK
  have hk : keysOfO A (behind s₀ att h G) = some kf :=
    keysOfO_is A (s := behind s₀ att h G) rfl hg rfl rfl hin Rt.first (by rw [sm.shape]; exact Rt.keys)
  have hi : inOf (seatCO (parCOf A)) (parCOf A) (behind s₀ att h G) = some (i, Kc) := by
    rw [K5Law.inOf_isAt (a := { att with F := G, heard5 := some h }) rfl]
    show (att.g.bind fun g => (some h).bind fun h => K5Law.inAt (parCOf A) g h G) = _
    have hg' : att.g = some g₀ := hg
    rw [hg']
    exact hin
  exact ⟨i, Kc, l₁, l₂, jn, kf, gL, xj, hi, Rt.first, Rt.second, hk, hlk, hc, hFl, hun, Rt.join⟩

section At
variable (x : VerifiableInference.Desc.First.Look.Place) (D : Sent) (rad : OracleShape → Nat)

/-- **THE FOUR RUNS RETURN.** -/
theorem runsReturn_at (Ex : Iop.ExtSpec) (Wp : Type) {Cl : Type} (claim : Aff → Cl) {set : Params.Setting} {settings : Model.Settings} {i₀ : Attention.In}
    {cf : Attention.Cfg} {a A0 : Attention.Plan} (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)) → Cb.Gl.E) (ns : ℕ)
    {p : Par} {ds : List RDT} {kc nzx : ℕ}
    (Pb : K5Public x a.seam.tl D rad set settings i₀ cf A0 p ds kc a.iU3 a.nW (plannedK a) (padOfO a.fs) nzx)
    (eS : a.S = A0.S) (eF : a.fs = A0.fs) (elm : (parCOf A0).geo.lmb = (parCOf a).geo.lmb)
    {ι : Fo.Pl → Option (JAtt x.ns a.seam.tl)} {Q : Fork → Prop} {x0 : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl))}
    {gL : Forest.Heard} {s : First.S}
    (hl : K3LeftOutIs (K3.seatCalls claim).fork (K3.seatCalls claim).heard x.fs x.lm x.F.next ι Q x0 gL s)
    {own : List (ℕ × ℕ)} {ps : List (ℕ × (ℕ × ℕ))} {qs : List (ℕ × OracleShape)} {hi : ℕ} (Fa : FrontAll x a D own ps qs hi gL s)
    {att : First.AttOwn} (hFl : Fo.FilledA att.F gL.cEnd) (e : s.here = .att att) {rs : List Fmt.RoundView} {hd : Heard} {G : Fork}
    (hh : hear p.own (att.F, rs, 0) = some (hd, G, [], 0)) : RunsReturn a s att hd G := by
  have hid : Attention.shapeHid settings.lidb cf = Except.ok (a.S, x.fs) := by
    rw [eS, Pb.fs]
    exact (OnBytes.Road.L5.plan_shape Pb.plan).1
  have hok : planOkAll cf a.S x.fs = true := by
    rw [eS, Pb.fs]
    exact Pb.planOk
  have B := behindOk₀_at claim hl Fa e hh
  have led : seatSO.ledger s = some att.F := by
    show (match s.here with | .att a => some a.F | _ => none) = _
    rw [e]
  obtain ⟨L, _, sd, zG, _, _⟩ := hear_law_paid hh (Fa.ledger att.F led).1
  have hrec := own_recOf x a.seam.tl D rad Ex Wp α Pb.plan Pb.planOk p Pb.own ns (numsPlan p.own (x.F.next + Forest.elems x.fs))
  rw [hrec, ← eS] at sd
  have hatt : AttOK set x a.S a.seam.tl D rad := eS ▸ Pb.att
  have PA := plan_all hid hok
  obtain ⟨⟨zy, z, H3⟩, hz4, hsh, he⟩ := hK_of_left x a.seam.tl D rad hatt hid PA.law hl
  obtain ⟨hlz, hlp⟩ := hlk_of_left x a.seam.tl (parCOf a).geo.lmb (elm ▸ Pb.planes) hl
  obtain ⟨r1, r2, u1, u2, wl, ix, wh, U⟩ := PA.units
  have Bs := baseIs_att x a.S a.seam.tl D rad
  obtain ⟨_, _, s3, _, _, _, _⟩ := seven_of Bs hid PA.law.fit
  have hshape : gL.shape = a.fs := by
    obtain ⟨_, _, _, _, _, Lf, _, _, _⟩ := hl
    rw [Lf.shape, Pb.fs, eF]
  have hd' : claimsOk ⟨geoOf a.S, a.iU3, a.nW, K5Law.matsOf a.seam.tl.mats⟩ (plannedK a) (padOfO gL.shape) true nzx = true := by
    rw [hshape, eS]
    exact Pb.claims
  obtain ⟨l, i, l₁, l₂, jn, kf, xj, Rt⟩ := returns_at_lk hid PA.law U a.seam.tl (eS ▸ Pb.mats) a.iU3 a.nW hd' H3 hz4
    (fun f hf => by have := s3 f hf; rw [Bs.D] at this; exact this)
    (closedOf (attBase x a.S a.seam.tl D rad) (attLin x a.S a.seam.tl D rad Ex Wp α ns (numsPlan p.own (x.F.next + Forest.elems x.fs))) ns
      (numsPlan p.own (x.F.next + Forest.elems x.fs))) Bs.D Bs.npl A0.own.rows sd zG { a with NC := a.S.calls.size } rfl rfl gL rfl
    hsh he G [] (lookOfO (parCOf a).geo.lmb gL) hlz hlp
  exact runsReturn_of_returns a { a with NC := a.S.calls.size } rfl B Rt Fa.plain hFl

/-- **THE FIELD runsRet**: under the table's promise in front, "no mark" and the hearing's return. -/
theorem k5Left_runsRet (Ex : Iop.ExtSpec) (Wp : Type) {Pp W Cl : Type} {Fr : Frame} (claim : Aff → Cl) {set : Params.Setting}
    {settings : Model.Settings} {i₀ : Attention.In} {cf : Attention.Cfg} {a A0 : Attention.Plan}
    (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)) → Cb.Gl.E) (ns : ℕ) {p : Par} {ds : List RDT} {kc nzx : ℕ}
    (Pb : K5Public x a.seam.tl D rad set settings i₀ cf A0 p ds kc a.iU3 a.nW (plannedK a) (padOfO a.fs) nzx)
    (eS : a.S = A0.S) (eF : a.fs = A0.fs) (elm : (parCOf A0).geo.lmb = (parCOf a).geo.lmb)
    (N : Numbers) (Mg : Meaning Pp W) (links : List ModelPart) (m : ℕ) (pl : Place) (O : List Item) (Q : List Pub)
    {ι : Fo.Pl → Option (JAtt x.ns a.seam.tl)} {Qr : Fork → Prop}
    (x0 : Pp → First.S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)))
    (gOf : Pp → First.S × Fr.E.Str → Forest.Heard)
    (leftIs : ∀ π : Pp, ∀ a' : First.S × Fr.E.Str, Mg.pubP (.left m) (π, a'.1) →
      K3LeftOutIs (K3.seatCalls claim).fork (K3.seatCalls claim).heard x.fs x.lm x.F.next ι Qr ((x0 π) a') ((gOf π) a') a'.1)
    (hleftQ : Pub.left m ∈ Q) {own : List (ℕ × ℕ)} {ps : List (ℕ × (ℕ × ℕ))} {qs : List (ℕ × OracleShape)} {hi : ℕ}
    (hfront : ∀ π a', onT N Mg links π Fr pl O Q a' → FrontAll x a D own ps qs hi ((gOf π) a') a'.1)
    (hFill : ∀ π a' att, onT N Mg links π Fr pl O Q a' → a'.1.here = .att att → Fo.FilledA att.F ((gOf π) a').cEnd) :
    ∀ π : Pp, ∀ (s : First.S) (y : Fr.E.Str) (att : First.AttOwn) (hd : Heard) (G : Fork) (rs : List Fmt.RoundView),
      onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none → s.here = .att att →
      hear p.own (att.F, rs, 0) = some (hd, G, [], 0) → RunsReturn a s att hd G :=
  fun π s y att _ _ _ hon hm e hh =>
    runsReturn_at x D rad Ex Wp claim α ns Pb eS eF elm (leftIs π (s, y) (onAt_pubP hon hm _ hleftQ)) (hfront π (s, y) ⟨hon, hm⟩)
      (hFill π (s, y) att ⟨hon, hm⟩ e) e hh

end At

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.behindOk₀_at
#print axioms VerifiableInference.Desc.First.Att.P.runsReturn_of_returns
#print axioms VerifiableInference.Desc.First.Att.P.runsReturn_at
#print axioms VerifiableInference.Desc.First.Att.P.k5Left_runsRet
