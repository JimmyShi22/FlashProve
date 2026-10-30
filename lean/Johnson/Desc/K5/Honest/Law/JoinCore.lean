-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/JoinCore.lean: CONDITIONAL: the form that the lookup's run "join" gathers
on an attention segment's four key forms is worth 0, at the verifier's state just behind the lay of
the segment's own rounds, from: the planner's return and the plan's law; that the claims' reading,
the run "first", the key forms and the lookup's text return there; that each call's key point is the
lookup's cut of its end point; that under each slot that the key forms read the world holds the
library's rule value (`RuleAt`); and the lookup's half of the join. Beside it two tools for a caller
that pays `RuleAt` out of the prover's scalars (Johnson/Desc/K5/Honest/Law/JoinValues.lean): they
take the public premises in one structure (`PublicAll`). A joining of lemmas; no algebra is in this
file. Statements with their proofs.

Main names:
  `keyPtsAre_of_look`   the key points, read, are the library's, from the lookup's end point and
                    cuts
  `lonePairs_of`    "piece b is pair b" at the seven lists of pieces that the verifier's function of
                    the points returns
  `loneReads_of_public`   the premises of all scalars that are sent by themselves and that the key
                    forms read (`LoneReads`, Johnson/Desc/K5/Honest/Law/RuleAll.lean), with every
                    public premise paid out of `PublicAll`
  `join_zero_law`   the gathered form is worth 0: `kf_at_law'` (KeysSlots.lean) and `join_zero`
                    (Join.lean) in one
  `join_behind`     **the same at the state behind the lay**, the claims' reading taken apart

WHAT IS LEFT AS A PREMISE IN `join_behind`: the planner of shapes' return and the plan's law
(public: `law_at_head`, Johnson/Desc/K5/Honest/Law/PublicAtHead.lean); that the claims' reading, the
run "first", the key forms and the lookup's text return at the state; Lk, hK: the lookup's end point
and cuts; hv: `RuleAt` at whatever the four look-ups return (`ruleAt_of_scalars`); hm: `JoinMeets`,
the lookup's half.
Limits. That any of these is met at a state of an honest run is not shown here. The key points are
read off the field g of the open segment, the join's letters off what the lookup's text is handed:
no statement here ties the two.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.KeysSlots
import Johnson.Desc.K5.Honest.Law.Join
import Johnson.Desc.K5.Honest.Law.PublicImplies

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open VerifiableInference.Desc (First.S First.AttOwn)
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (geoOf RemP ScoreP Pts pointsOf KeyPtsAre behind
  remainders piecesOf)
open VerifiableInference.Desc.First.Att.P.Runs (JoinsP PadIn)
open K5Law (unitsSix oldOf sixTop PlanLaw LookAll KeyIs)

variable {K : Type} [Field K] {ρ : Reading K} {W : World K}

/-- **The key points, read, are the library's**, where the library's z is the lookup's end point,
read, and each call's key point is the lookup's cut of it. -/
theorem keyPtsAre_of_look {S : Attention.Shape} {fs : Model.Forest.Shape} (hF : L5.CallsFit S fs)
    {zx zy : Array E} {p : Inst.Model.AttSeg.Pub K} (Lk : LookAll ρ fs zx zy p)
    {zk : Array (Array E)} (hK : ∀ q : Fin 4, KeyIs fs zx zy (zk.getD q.val #[]) q) :
    KeyPtsAre ρ (L5.callsOf fs) p.z zk :=
  ⟨fun q => (K5Law.keyPt_of hF Lk (hK q)).size,
    fun q i hi => (K5Law.keyPt_of hF Lk (hK q)).read i hi⟩

section
variable {P : Pub5} {fs : Model.Forest.Shape} {zk : Array (Array E)} {h : Att.P.Heard}
  {L : Att.P.Left} {pts : Pts} {pM pD cM cD : RemP} {kM kD : ScoreP}

/-- **"Piece b is pair b" at the seven lists of pieces** that the verifier's function of the points
returns: those of its first two plane claims, of its two units, and of the division's three
lists. -/
theorem lonePairs_of (A : PublicAll P fs) (hp : pointsOf P.g zk h L = some pts)
    (e0 : pts.planes[0]? = some pM) (e1 : pts.planes[1]? = some pD)
    (k0 : pts.scores[0]? = some kM) (k1 : pts.scores[1]? = some kD) :
    PairsAre P.g pM.pw ∧ PairsAre P.g pD.pw ∧ PairsAre P.g kM.pw ∧ PairsAre P.g kD.pw ∧
      PairsAre P.g pts.d.pwW ∧ PairsAre P.g pts.d.pwX ∧ PairsAre P.g pts.d.pwH := by
  have Pn := K5Law.planes_are hp
  have PA := K5Law.points_are hp
  obtain ⟨r1, r2, u1, u2, wl, ix, wh, U, _⟩ := A.units
  obtain ⟨uW, uX, uH, hW, hX, hH, pwW, pwX, pwH⟩ := K5Law.points_pw hp
  have hsco : P.g.scores = [u1, u2] := U.sco
  have nH : h.scores.size = 2 := by
    rw [← PA.nH, hsco]
    rfl
  -- the two remainder units
  have hrem : remainders P.g = [r1, r2] := U.rem
  have hlen : (P.g.units .kr [.rm, .rd]).length = 2 := by
    have := congrArg List.length hrem
    unfold remainders at this
    rwa [List.length_map] at this
  have nR : h.remainders.size = 2 := by rw [← Pn.nR, hlen]
  have rem : ∀ n (hn : n < 2) (q : RemP), pts.planes[n]? = some q → PairsAre P.g q.pw := by
    intro n hn q hq
    have hu : (P.g.units .kr [.rm, .rd])[n]? = some (P.g.units .kr [.rm, .rd])[n] :=
      List.getElem?_eq_getElem (by omega)
    have hs : h.remainders[n]? = some h.remainders[n] := Array.getElem?_eq_getElem (by omega)
    have e := Option.some.inj ((Pn.rem n _ _ hu hs).symm.trans hq)
    rw [← e]
    refine A.pairsRem _ ?_ _
    unfold remainders
    exact List.mem_map.2 ⟨_, List.getElem_mem (by omega), rfl⟩
  have unit : ∀ n (hn : n < 2) (k : ScoreP), pts.scores[n]? = some k → PairsAre P.g k.pw := by
    intro n hn k hk
    have hg : n < P.g.scores.length := by
      rw [hsco]
      exact hn
    have hu : P.g.scores[n]? = some P.g.scores[n] := List.getElem?_eq_getElem hg
    have hs : h.scores[n]? = some h.scores[n] := Array.getElem?_eq_getElem (by omega)
    obtain ⟨k', s1, _, _, _, _, w1, _⟩ := Pn.unit n _ _ hu hs
    obtain rfl : k' = k := Option.some.inj (s1.symm.trans hk)
    rw [w1]
    exact A.pairsScores _ (List.getElem_mem hg) _
  refine ⟨rem 0 (by omega) _ e0, rem 1 (by omega) _ e1, unit 0 (by omega) _ k0,
    unit 1 (by omega) _ k1, ?_, ?_, ?_⟩
  · rw [pwW]
    exact A.pairsWl _ hW _
  · rw [pwX]
    exact A.pairsIx _ hX _
  · rw [pwH]
    exact A.pairsWh _ hH _

/-- **The premises of all scalars that are sent by themselves and that the key forms read**, with
every public premise paid out of `PublicAll`. Left: the verifier's function of the points returns,
with these six among what it returns; the key points, read, are the library's. -/
theorem loneReads_of_public (A : PublicAll P fs) (hp : pointsOf P.g zk h L = some pts)
    {p : Inst.Model.AttSeg.Pub K} (Kp : KeyPtsAre ρ (L5.callsOf fs) p.z zk)
    (e0 : pts.planes[0]? = some pM) (e1 : pts.planes[1]? = some pD)
    (k0 : pts.scores[0]? = some kM) (k1 : pts.scores[1]? = some kD)
    (c0 : pts.planes[kM.claim]? = some cM) (c1 : pts.planes[kD.claim]? = some cD) :
    LoneReads ρ P (L5.callsOf fs) p pM pD cM cD kM kD pts.d := by
  obtain ⟨_, _, _, _, _, _, _, U, _⟩ := A.units
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := lonePairs_of A hp e0 e1 k0 k1
  exact loneReads_of_units ρ A.sized U A.lookFits hp Kp e0 e1 k0 k1 c0 c1 a1 a2 a3 a4 a5 a6 a7

end

section
variable {S : Attention.Shape} {fs : Model.Forest.Shape} {g gL : Forest.Heard} {i : P.Runs.In}
  {n : ℕ} {l₁ : List Aff} {j : JoinsP} {k3 : PadIn} {kf : Array Aff} {zx zy : Array E}
  {hh : P.Heard} {L' : P.Left} {p : Inst.Model.AttSeg.Pub K} {t : Inst.Model.AttSeg.Raw → K}

/-- **The form that the lookup's text returns on the key forms is worth 0.** g: what the claims'
reading takes its key points from; gL: what the lookup's text is handed. Conditional as
`kf_at_law'`, and hj: the text returns; hm: the lookup's half of the join at the four extensions. -/
theorem join_zero_law (A : Plan) {lid : ℕ} {cf : Attention.Cfg}
    (hid : shapeHid lid cf = Except.ok (S, fs)) (PL : PlanLaw cf S fs) (N : Numerals ρ)
    (Lk : LookAll ρ fs zx zy p) (hK : ∀ q : Fin 4, KeyIs fs zx zy (g.zk.getD q.val #[]) q)
    (hg : i.g = geoOf S) (hz : i.zk = g.zk) (hP : P.pointsOf i.g g.zk hh L' = some i.p)
    (h1 : P.Runs.firstRun i n = some (l₁, j)) (hk : P.Runs.keysRun i k3 j = some kf)
    (tb : Inst.Model.Tables)
    (hv : ∀ a1 a2 k1 k2, hh.remainders[0]? = some a1 → hh.remainders[1]? = some a2 →
      i.p.scores[0]? = some k1 → i.p.scores[1]? = some k2 →
      RuleAt W (oldOf S g i) (unitsSix (oldOf S g i) (sixTop S i g.zk a1 a2 k1 k2))
        (L5.dimOf S) (L5.callsOf fs) p t)
    {F : Fork} {tp : OnBytes.K.Kc.Tape} {y : Aff × Fork × OnBytes.K.Kc.Tape}
    (hj : Look.joinF gL kf F tp = some y)
    (hm : JoinMeets ρ W gL fun c => Blocks.ext ((L5.callsOf fs).a c)
      (Inst.Model.AttSeg.keyVec (scl := L5.sclOf S) (L5.dimOf S) tb t c)
      ((L5.callsOf fs).zC c p.z)) :
    y.1.value ρ W = 0 :=
  join_zero N hj (kf_at_law' A hid PL N Lk hK hg hz hP h1 hk tb hv) hm

end

/-- **The same at the state behind the lay of the segment's own rounds**, in any world W over the
field of the challenges. Conditional; what is left as a premise is listed in the file's head. -/
theorem join_behind {W : World Cb.Gl.E} (A : Plan) {lid : ℕ}
    (hid : shapeHid lid A.S.cf = Except.ok (A.S, A.fs)) (PL : PlanLaw A.S.cf A.S A.fs)
    {s : First.S} {a : First.AttOwn} {h : P.Heard} {G : Fork} {i : P.Runs.In} {n : ℕ}
    (hin : P.inOf (P.seatCO (P.parCOf A)) (P.parCOf A) (behind s a h G) = some (i, n))
    {l₁ : List Aff} {j : JoinsP} (h1 : P.Runs.firstRun i n = some (l₁, j)) {kf : Array Aff}
    (hk : P.keysOfK (P.seatCO (P.parCOf A)) (P.parCOf A) (behind s a h G) = some kf)
    {g : Forest.Heard} (hg : a.g = some g) {zx zy : Array E}
    {p : Inst.Model.AttSeg.Pub Cb.Gl.E} (Lk : LookAll Reading.gl A.fs zx zy p)
    (hK : ∀ q : Fin 4, KeyIs A.fs zx zy (g.zk.getD q.val #[]) q) (tb : Inst.Model.Tables)
    {t : Inst.Model.AttSeg.Raw → Cb.Gl.E}
    (hv : ∀ a1 a2 k1 k2, h.remainders[0]? = some a1 → h.remainders[1]? = some a2 →
      i.p.scores[0]? = some k1 → i.p.scores[1]? = some k2 →
      RuleAt W (oldOf A.S g i) (unitsSix (oldOf A.S g i) (sixTop A.S i g.zk a1 a2 k1 k2))
        (L5.dimOf A.S) (L5.callsOf A.fs) p t)
    {gL : Forest.Heard} {y : Aff × Fork × OnBytes.K.Kc.Tape}
    (hj : Look.joinF gL kf G [] = some y)
    (hm : JoinMeets Reading.gl W gL fun c => Blocks.ext ((L5.callsOf A.fs).a c)
      (Inst.Model.AttSeg.keyVec (scl := L5.sclOf A.S) (L5.dimOf A.S) tb t c)
      ((L5.callsOf A.fs).zC c p.z)) :
    y.1.value Reading.gl W = 0 := by
  obtain ⟨eg, _, _, g', l, _, hg', _, hp, _⟩ := P.inOf_behind hin
  obtain rfl : g = g' := Option.some.inj (hg.symm.trans hg')
  have ezk : i.zk = g.zk := by
    have e := (K5Law.inOf_some _ _ _ _ _ hin).2.2.1
    have e' : (a.g.map fun g => g.zk) = some i.zk := e
    rw [hg] at e'
    exact (Option.some.inj e').symm
  obtain ⟨k3, hk3⟩ := P.keys_parts hin h1 hk
  rw [← eg] at hp
  exact join_zero_law A hid PL gl_numerals Lk hK eg ezk hp h1 hk3 tb hv hj hm

end H2K5.Honest

#print axioms H2K5.Honest.keyPtsAre_of_look
#print axioms H2K5.Honest.lonePairs_of
#print axioms H2K5.Honest.loneReads_of_public
#print axioms H2K5.Honest.join_zero_law
#print axioms H2K5.Honest.join_behind
