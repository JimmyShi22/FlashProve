-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/JoinValues.lean: CONDITIONAL: the form that the lookup's run "join"
gathers on an attention segment's four key forms is worth 0 at the verifier's state just behind the
lay of the segment's own rounds, with every premise on values but two carried back to the files on
the readings. A joining of lemmas; no algebra is in this file. Statements with their proofs.

THE TWO PREMISES ON VALUES THAT STAY:
  hs (`ScalarsAt`, Johnson/Desc/K5/Honest/Law/KeysSlots.lean): under each named scalar's slot the
    world holds the prover's scalar, read: whoever ties the world's slots to what the prover sent.
  hm (`JoinMeets`, Johnson/Desc/K5/Honest/Law/Join.lean): the lookup's half of the join, at the four
    extensions of the calls' vectors of looked-up values on the prover's cells, read.

Main names:
  `look_of_k3`      the two premises on the lookup's end point and cuts, out of the library's
                    `K3Pts`
  `six_of_public`   what the verifier's function of the points returns has two remainder units'
                    plane claims, two softmax-table units and their two plane claims
  `steps_of_public`   the summands of the two softmax-table units and of "denominator times output",
                    each at challenges of its own, read as the library's steps s6b, s6d, s8
  `rule_of_public`  each of the prover's scalars that the key forms read, read, is its rule value
  `join_of_scalars`   **the gathered form is worth 0**

THE OTHER PREMISES OF `join_of_scalars`. Public: A (`PublicAll`), hid, PL: all three from the
library's head on the public input (`public_at_head`, `law_at_head`,
Johnson/Desc/K5/Honest/Law/PublicAtHead.lean). On the run: hk, hj: the key forms and the lookup's
text return at the state; hg, K3: the open segment holds what the lookup left, and its key points
are cut as the lookup cuts them; c0, c1, cE: the challenges at which the three sums were sent, with
the state's key points, at which the verifier's function of the points returns.
Limits. That any premise is met at a state of an honest run is not shown here. In the proof of
`join_of_scalars` the library's challenges are those made of the prover's at cE; its statement names
of them the point z alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.JoinCore
import Johnson.Desc.K5.Honest.Law.UnitPts

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open VerifiableInference.Desc (First.S First.AttOwn)
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (geoOf RemP ScoreP Pts pointsOf KeyPtsAre K3Pts behind)
open Cb.Pv.Att.End (ReadK)
open K5Law (unitsSix oldOf sixTop PlanLaw LookAll KeyIs)

/-- **The two premises on the lookup's end point and cuts**, out of the library's structure on the
same in the names of what the lookup heard. -/
theorem look_of_k3 {fs : Model.Forest.Shape} {zx zy : Array E} {zk : Array (Array E)}
    {z : ℕ → Cb.Gl.E} (H3 : K3Pts fs zx zy zk z) {p : Inst.Model.AttSeg.Pub Cb.Gl.E}
    (hz : p.z = z) :
    LookAll Reading.gl fs zx zy p ∧ ∀ q : Fin 4, KeyIs fs zx zy (zk.getD q.val #[]) q :=
  ⟨⟨H3.nx, H3.ny, fun t => by rw [hz, H3.z]; rfl⟩, fun q => H3.zk q⟩

section
variable {K : Type} [Field K] {ρ : Reading K} {P : Pub5} {fs : Model.Forest.Shape}
  {zk : Array (Array E)} {h : Att.P.Heard} {L : Att.P.Left} {pts : Pts}

/-- **What the verifier's function of the points returns has these eight.** -/
theorem six_of_public (A : PublicAll P fs) (hp : pointsOf P.g zk h L = some pts) :
    ∃ a1 a2 pM pD kM kD cM cD, h.remainders[0]? = some a1 ∧ h.remainders[1]? = some a2 ∧
      pts.planes[0]? = some pM ∧ pts.planes[1]? = some pD ∧ pts.scores[0]? = some kM ∧
      pts.scores[1]? = some kD ∧ pts.planes[kM.claim]? = some cM ∧
      pts.planes[kD.claim]? = some cD := by
  have Pn := K5Law.planes_are hp
  have PA := K5Law.points_are hp
  obtain ⟨r1, r2, u1, u2, _, _, _, U, _⟩ := A.units
  have hsco : P.g.scores = [u1, u2] := U.sco
  have nH : h.scores.size = 2 := by
    rw [← PA.nH, hsco]
    rfl
  have hlen : (P.g.units .kr [.rm, .rd]).length = 2 := by
    have := congrArg List.length (show Att.P.remainders P.g = [r1, r2] from U.rem)
    unfold Att.P.remainders at this
    rwa [List.length_map] at this
  have nR : h.remainders.size = 2 := by rw [← Pn.nR, hlen]
  have q0 := Pn.rem 0 _ _ (List.getElem?_eq_getElem (by omega : 0 < _))
    (Array.getElem?_eq_getElem (by omega : 0 < h.remainders.size))
  have q1 := Pn.rem 1 _ _ (List.getElem?_eq_getElem (by omega : 1 < _))
    (Array.getElem?_eq_getElem (by omega : 1 < h.remainders.size))
  obtain ⟨kM, s0, _, c0, _⟩ := Pn.unit 0 u1 _ (by rw [hsco]; rfl)
    (Array.getElem?_eq_getElem (by omega : 0 < h.scores.size))
  obtain ⟨kD, s1, _, c1, _⟩ := Pn.unit 1 u2 _ (by rw [hsco]; rfl)
    (Array.getElem?_eq_getElem (by omega : 1 < h.scores.size))
  exact ⟨_, _, _, _, kM, kD, _, _, Array.getElem?_eq_getElem (by omega),
    Array.getElem?_eq_getElem (by omega), q0, q1, s0, s1, c0, c1⟩

variable (w : K5In) {p : Inst.Model.AttSeg.Pub K} {c0 c1 cE : Chal} {Dv : DivIn}

/-- **The three summands whose sums the key forms read, each at challenges of its own, read as the
library's steps.** c0, c1: the challenges of the two softmax-table units' summands; cE: those of
"denominator times output". Conditional: `PublicAll`; at each of the three the verifier's function
of the points returns and the key points, read, are the library's at one z; hth: the th of p is
what the prover reads at cE. -/
theorem steps_of_public (A : PublicAll P fs) (K0 : KeyPtsAre ρ (L5.callsOf fs) p.z c0.zk)
    (K1 : KeyPtsAre ρ (L5.callsOf fs) p.z c1.zk) (KE : KeyPtsAre ρ (L5.callsOf fs) p.z cE.zk)
    {p0 p1 : Pts} (h0 : ptsOf P c0 = some p0) (h1 : ptsOf P c1 = some p1)
    (hE : divIn P cE = some Dv)
    (hth : ρ.val ((heardAt P cE fun _ => none).gam.getD 1 zeroE) = p.th) :
    StepReads ρ (sK P w c0 0) P.D (L5.callsOf fs) p (tOf ρ w) .s6b ∧
      StepReads ρ (sK P w c1 1) P.D (L5.callsOf fs) p (tOf ρ w) .s6d ∧
      StepReads ρ (sSE P w cE) P.D (L5.callsOf fs) p (tOf ρ w) .s8 := by
  obtain ⟨_, _, u1, u2, _, _, _, U, U1, U2, _, _⟩ := A.units
  have hsco : P.g.scores = [u1, u2] := U.sco
  obtain ⟨_, _, pM, pD, kM, kD, _, _, _, _, e0, e1, k0, k1, _, _⟩ :=
    six_of_public A (show pointsOf P.g c0.zk _ _ = some p0 from h0)
  obtain ⟨_, _, pM', pD', kM', kD', _, _, _, _, e0', e1', k0', k1', _, _⟩ :=
    six_of_public A (show pointsOf P.g c1.zk _ _ = some p1 from h1)
  have a0 := lonePairs_of A (show pointsOf P.g c0.zk _ _ = some p0 from h0) e0 e1 k0 k1
  have a1 := lonePairs_of A (show pointsOf P.g c1.zk _ _ = some p1 from h1) e0' e1' k0' k1'
  obtain ⟨ptsE, _, hpE, _, ed, _⟩ := divIn_spec hE
  obtain ⟨_, _, qM, qD, jM, jD, _, _, _, _, f0, f1, j0, j1, _, _⟩ :=
    six_of_public A (show pointsOf P.g cE.zk _ _ = some ptsE from hpE)
  have aE := lonePairs_of A (show pointsOf P.g cE.zk _ _ = some ptsE from hpE) f0 f1 j0 j1
  refine ⟨sKM_reads_of ρ w A.sized (i := 0) (by rw [hsco]; rfl) (by rw [h0]; exact k0) U.below A.vKM
      K0 U1 a0.2.2.1,
    sKD_reads_of ρ w A.sized (i := 1) (by rw [hsco]; rfl) (by rw [h1]; exact k1') U.on A.vKD K1 U2
      A.lookFits.lM a1.2.2.2.1,
    sSE_reads ρ A.sized w A.planned hE (divPts_of ρ A.sized hE KE A.wl hth) ?_⟩
  rw [ed]
  exact aE.2.2.2.2.1

/-- **Each of the prover's scalars that the key forms read, read, is its rule value.** Conditional
as `steps_of_public`, and: the verifier's function of the points returns pts at key points that,
read, are the library's; the six named by number are among what it returns. -/
theorem rule_of_public (A : PublicAll P fs) (hp : pointsOf P.g zk h L = some pts)
    (Kp : KeyPtsAre ρ (L5.callsOf fs) p.z zk) (K0 : KeyPtsAre ρ (L5.callsOf fs) p.z c0.zk)
    (K1 : KeyPtsAre ρ (L5.callsOf fs) p.z c1.zk) (KE : KeyPtsAre ρ (L5.callsOf fs) p.z cE.zk)
    {p0 p1 : Pts} (h0 : ptsOf P c0 = some p0) (h1 : ptsOf P c1 = some p1)
    (hE : divIn P cE = some Dv)
    (hth : ρ.val ((heardAt P cE fun _ => none).gam.getD 1 zeroE) = p.th)
    {pM pD cM cD : RemP} {kM kD : ScoreP} (e0 : pts.planes[0]? = some pM)
    (e1 : pts.planes[1]? = some pD) (k0 : pts.scores[0]? = some kM)
    (k1 : pts.scores[1]? = some kD) (q0 : pts.planes[kM.claim]? = some cM)
    (q1 : pts.planes[kD.claim]? = some cD) :
    ∀ k, ReadK P.D k → scalarOf ρ P.g w pM pD cM cD kM kD pts.d (sK P w c0 0).total
      (sK P w c1 1).total (sSE P w cE).total k =
        Inst.Model.AttSeg.rv P.D (L5.callsOf fs) p (tOf ρ w) k := by
  obtain ⟨RM, RD, RE⟩ := steps_of_public w A K0 K1 KE h0 h1 hE hth
  exact scalar_rule_all A.sized w (loneReads_of_public A hp Kp e0 e1 k0 k1 q0 q1) RM RD RE

end

/-- **The form that the lookup's text returns on the key forms, at the state behind the lay of the
segment's own rounds, is worth 0**, in any world W over the field of the challenges. Conditional;
the premises are listed in the file's head. -/
theorem join_of_scalars {W : World Cb.Gl.E} (Ap : Plan) (A : PublicAll ⟨Ap.S, Ap.own⟩ Ap.fs)
    {lid : ℕ} (hid : shapeHid lid Ap.S.cf = Except.ok (Ap.S, Ap.fs))
    (PL : PlanLaw Ap.S.cf Ap.S Ap.fs) (w : K5In) {s : First.S} {a : First.AttOwn} {h : P.Heard}
    {G : Fork} {kf : Array Aff}
    (hk : P.keysOfK (P.seatCO (P.parCOf Ap)) (P.parCOf Ap) (behind s a h G) = some kf)
    {g : Forest.Heard} (hg : a.g = some g) {z : ℕ → Cb.Gl.E}
    (K3 : K3Pts Ap.fs g.zx g.zy g.zk z) {c0 c1 cE : Chal} (z0 : c0.zk = g.zk) (z1 : c1.zk = g.zk)
    (zE : cE.zk = g.zk) {p0 p1 : Pts} (h0 : ptsOf ⟨Ap.S, Ap.own⟩ c0 = some p0)
    (h1 : ptsOf ⟨Ap.S, Ap.own⟩ c1 = some p1) {Dv : DivIn}
    (hE : divIn ⟨Ap.S, Ap.own⟩ cE = some Dv) (tb : Inst.Model.Tables)
    (hs : ∀ i n, P.inOf (P.seatCO (P.parCOf Ap)) (P.parCOf Ap) (behind s a h G) = some (i, n) →
      ∀ a1 a2 pM pD kM kD cM cD, h.remainders[0]? = some a1 → h.remainders[1]? = some a2 →
        i.p.planes[0]? = some pM → i.p.planes[1]? = some pD → i.p.scores[0]? = some kM →
        i.p.scores[1]? = some kD → i.p.planes[kM.claim]? = some cM →
        i.p.planes[kD.claim]? = some cD →
        ScalarsAt W (L5.dimOf Ap.S) a1 a2 kM kD i.p.d
          (scalarOf Reading.gl (geoOf Ap.S) w pM pD cM cD kM kD i.p.d
            (sK ⟨Ap.S, Ap.own⟩ w c0 0).total (sK ⟨Ap.S, Ap.own⟩ w c1 1).total
            (sSE ⟨Ap.S, Ap.own⟩ w cE).total))
    {gL : Forest.Heard} {y : Aff × Fork × OnBytes.K.Kc.Tape}
    (hj : Look.joinF gL kf G [] = some y)
    (hm : JoinMeets Reading.gl W gL fun c => Blocks.ext ((L5.callsOf Ap.fs).a c)
      (Inst.Model.AttSeg.keyVec (scl := L5.sclOf Ap.S) (L5.dimOf Ap.S) tb (tOf Reading.gl w) c)
      ((L5.callsOf Ap.fs).zC c z)) :
    y.1.value Reading.gl W = 0 := by
  -- the key forms' return, taken apart
  have hk' := hk
  unfold P.keysOfK at hk'
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hk'
  obtain ⟨⟨i, n⟩, hin, _, _, ⟨l₁, j⟩, hf, _⟩ := hk'
  obtain ⟨eg, _, _, g', l, _, hg', _, hp, _⟩ := P.inOf_behind hin
  obtain rfl : g = g' := Option.some.inj (hg.symm.trans hg')
  have Kp : KeyPtsAre Reading.gl (L5.callsOf Ap.fs) z g.zk := keyPts_of_keysFit A.keys K3
  obtain ⟨Lk, hK⟩ := look_of_k3 K3 (p := pubOf Reading.gl ⟨Ap.S, Ap.own⟩ cE z) rfl
  refine join_behind Ap hid PL hin hf hk hg Lk hK tb (t := tOf Reading.gl w) ?_ hj hm
  intro a1 a2 k1 k2 ha1 ha2 hk1 hk2
  obtain ⟨a1', a2', pM, pD, kM, kD, cM, cD, b1, b2, e0, e1, s0, s1, q0, q1⟩ :=
    six_of_public A (show pointsOf (geoOf Ap.S) g.zk h l = some i.p from hp)
  obtain rfl : kM = k1 := Option.some.inj (s0.symm.trans hk1)
  obtain rfl : kD = k2 := Option.some.inj (s1.symm.trans hk2)
  exact ruleAt_of_scalars (hs i n hin a1 a2 pM pD kM kD cM cD ha1 ha2 e0 e1 s0 s1 q0 q1)
    (rule_of_public (P := ⟨Ap.S, Ap.own⟩) w A
      (show pointsOf (geoOf Ap.S) g.zk h l = some i.p from hp)
      (p := pubOf Reading.gl ⟨Ap.S, Ap.own⟩ cE z) Kp (by rw [z0]; exact Kp) (by rw [z1]; exact Kp)
      (by rw [zE]; exact Kp) h0 h1 hE rfl e0 e1 s0 s1 q0 q1)

end H2K5.Honest

#print axioms H2K5.Honest.look_of_k3
#print axioms H2K5.Honest.six_of_public
#print axioms H2K5.Honest.steps_of_public
#print axioms H2K5.Honest.rule_of_public
#print axioms H2K5.Honest.join_of_scalars
