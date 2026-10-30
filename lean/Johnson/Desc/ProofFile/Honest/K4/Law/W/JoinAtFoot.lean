-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/JoinAtFoot.lean: CONDITIONAL.

What is here. `JoinWorth` (Law/StackStart.lean: what the lookup's join and the second token
sumcheck's claim are worth inside the batched sumcheck's start), the one sentence that
Law/W/FootJoin.lean leaves behind "back", AT A STATE BEHIND THE STEP of the member of the
feed-forward layers' own rounds (sub-protocol K4), in the text of Law/StackAtStand.lean's hypothesis
hJW (`join_stand`). It is one call of `joinWorth_made` (Law/JoinMade.lean). PAID HERE, at the state:
the hearing's return; nine premises of `joinWorth_made`, read off the hypothesis K4Plan; every tie
of the honest side's data to what was heard (Law/W/JoinTies.lean); that the second token sumcheck's
job is made of the same common data; that the slot of its claimed sum holds its cube's total
(Law/TermsTotalAtStand.lean); the inverse that its claim spends; the numbers of the gated products;
that the honest data's list of the calls of the second pass is the verifier's (from hTS); that the
world's entries are the true ones.

  `join_stand`   JoinWorth at a state, at every ledger later than the one that the step leaves.

Not shown here. WHAT IS LEFT, EACH A HYPOTHESIS BY NAME. THE LOOKUP's OWN SENTENCE (hB1): the sum
over the eight calls, at the keys' vectors, is what the lookup's end claim is worth: ALL THE
CONTENT. On what the lookup has heard: the sizes of its two points, its calls' points and weights
(hsx, hsy, hzk, he, hpt, hs0). Public, on the sizes and tables: hc, hN, hfl, Zw, hsL, hlw, h4, hpad,
hnl, hne, hdq, hQK, hTS; the rotary table (R). On the witness: the cells are the matrices' (hC); the
two tensors of the gated products (hts, htu, Ss, Su). The table of scales is the layer sub-proof's
(hscl). K4Stand (Z), that the thread stands (hT), the tie on what the lookup has heard (hLk), K4Plan
(ITS FIELD sw BARS EVERY SHAPE BUT THOSE WITH THE LIBRARY's ELEVEN SWITCHES), hok
(Law/OkAtStand.lean has it). joinWorth_made calls the library's function that builds a public
structure; by the head of Law/JoinMade.lean the premise hfl (a floor under the tables' used lengths)
cannot be met at the small plan: THE FULL SIZE ALONE; that it holds there is not shown here
(Law/W/JoinPubHead.lean has it under the library's hypothesis on the public files). No example is
known of all hypotheses together. AT A THREAD NONE OF WHOSE STEPS ACCEPTS THERE IS NO SUCH STATE. By
a walk of import lines the closure holds seven modules under Johnson/RecCompile/ (Join, Wire, Pass,
CmsGlue, CmsBcs, Cms, Bcs), through Law/SlotsTrue.lean's imports; none under Johnson/Goal/ or
Johnson/D/; under Johnson/RecCompile/ none of the names Honest…, Both…, PassH…. Nothing on
soundness, on completeness or on any other property. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.JoinTies
import Johnson.Desc.ProofFile.Honest.K4.Law.JoinMade
import Johnson.Desc.ProofFile.Honest.K4.Law.TermsTotalAtStand
import Johnson.Road.K4.C.GatedNums

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes (E zeroE ofF)
open OnBytes.Model (Reading Aff Fork Tsc WsShape HTailF2 wsLayOf Forest.Heard)
open OnBytes.Model.Layer (Own Ten callsTS)
open OnBytes.PscRun (Later)
open OnBytes.Road (pt padOf sclOf cellsAt cellsOf Mats RopeFits SizedW LinesAre gl_numerals)
open OnBytes.Road.K4 (entryTrue)
open OnBytes.Road.K4.W (K4Plan)
open OnBytes.Road.K4.C (CellsAre TensorIs gatedNums_of_plan stack_open sides_fields)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim used lut aC keyVec layerR)
open VerifiableInference.Desc (Block Claim First.S)
open VerifiableInference.Desc.Sound (MsgQ)
open ProofFile.Honest.K4.SlotsOwn (worldBehind)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
  {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Q : K4Pub} {p : Par}
  {blk : Block First.S Claim} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}
  {k : Coins Bk} {s s' : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E' : Env}
  {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
  {cols : List VerifiableInference.Desc.OpenedColumn} {A : VerifiableInference.Desc.K9.Part} {o : Own}

/-- **JoinWorth AT A STATE BEHIND THE MEMBER's STEP.** CONDITIONAL: on every hypothesis named; above
all on hB1, the lookup's own sentence. -/
theorem join_stand [scl : Scl]
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E' ds y cols s' A o)
    (hT : Thr T b k s m E') (hLk : K4LookTieAt look Q s m) {h : OnBytes.Model.Layer.Shape}
    {pc : List (List String)} {tl : HTailF2} {D : Dim} (AQ : K4Plan h pc Q.P Q.g tl D)
    (ds' : List Fmt.Drawn) (F : Fork) (hL : Later A.F F) (Mm : Mats Cb.Gl.E)
    (hok : ∀ tT, o.H.tT = some tT → OnBytes.okE tT.p.eps = true)
    {sw : WsShape} {lk : ℕ} {tb : Tables} {s0 : OnBytes.Model.Forest.Shape}
    (hc : D.cap = h.lidb) (hN : LinesAre Q.P.y)
    (hfl : ∀ k : Fin 8, h.nmin - h.ll - h.lt ≤ Nat.clog 2 (used D k))
    (hsx : o.H.fo.zx.size = Q.P.y.fo.dT) (hsy : o.H.fo.zy.size = Q.P.y.fo.rK)
    (hzk : o.H.fo.zk = (Array.range Q.P.y.fo.NC).map fun q =>
      o.H.fo.zy.extract (Q.P.y.fo.rK - Q.P.y.fo.iota.getD q 0) o.H.fo.zy.size ++ o.H.fo.zx)
    (he : o.H.fo.e =
      (Array.range Q.P.y.fo.NC).map (OnBytes.Model.Forest.callWeight Q.P.y.fo o.H.fo.zy))
    (hs0 : OnBytes.Model.Forest.shape Q.P.y.cl Q.P.y.h.lidb = .ok s0)
    (hpt : ((List.range s0.NC).all fun q =>
      (o.H.fo.zk.getD q #[]).size == ((s0.calls[q]?).map (·.n)).getD 0) = true)
    (Zw : SizedW sw D.P) (hsL : sw.L = h.L) (hlw : wsLayOf sw true lk = .ok Q.P.wsLay)
    (h4 : h.p4 = true)
    (R : ∀ (rt : Array E) (lam : ℕ), lam < Q.P.y.Lam →
      RopeFits Reading.gl
        { v := o.v, wsLay := Q.P.wsLay, rope := Q.P.rope, rs := o.K.rs, rt := rt } D tb
        (Q.g * Q.P.y.Lam) lam)
    (hpad : ∀ k : Fin 8,
      Reading.gl.val (ofF ((Q.P.y.cl.getD k.val {}).tauAt (Q.P.y.cl.getD k.val {}).t0)) =
        (((lut tb k).pad : ℤ) : Cb.Gl.E))
    (hscl : scl = sclOf h o.v.sc o.v.g o.v.y.Lam)
    (hC : CellsAre Q (k4Wit Q cells weights tokens (look Q) m.st.input) Mm)
    {ts tu : Ten} (hts : Q.P.y.T_ "s" = some ts) (htu : Q.P.y.T_ "u" = some tu)
    (Ss : TensorIs Q (k4Wit Q cells weights tokens (look Q) m.st.input)
      (cellsOf D (cellsAt o.v.y Mm)) .sl ts)
    (Su : TensorIs Q (k4Wit Q cells weights tokens (look Q) m.st.input)
      (cellsOf D (cellsAt o.v.y Mm)) .up tu)
    (hnl : D.nl ≤ 2 ^ D.lL) (hne : 2 * D.ne ≤ 2 ^ D.lL) (hdq : sw.dq ≤ Q.P.y.dq)
    (hTS : callsTS Q.P = some [0, 1, 2, 5])
    (hQK : D.ChOK ∧ ∀ l, l < D.nl →
      (D.Pl l).kq = (D.Pl l).kk ∨ (16 ≤ (D.Pl l).kq ∧ 16 ≤ (D.Pl l).kk))
    (hB1 : (∑ q : Fin 8, Reading.gl.val (o.H.fo.e.getD q.val zeroE) *
        (Reading.gl.val o.H.fo.alpha - (q.val : Cb.Gl.E) * Reading.gl.val o.H.fo.theta -
          Blocks.ext (aC D q)
            (keyVec D (cellsOf D (cellsAt o.v.y Mm)) tb (o.v.g * o.v.y.Lam)
              (fun l => layerR D.P lk (wmOf (k4Wit Q cells weights tokens (look Q) m.st.input).w)
                (o.v.g * o.v.y.Lam + l)) q)
            (pt Reading.gl (o.v.zk.getD q.val #[])))) +
      Reading.gl.val (padOf o.H) - o.H.fo.cEnd.value Reading.gl
        (worldBehind T own rdOf k y A ds' F (entryTrue tl o Mm)) = 0) :
    ∀ D', stackData Q (k4Wit Q cells weights tokens (look Q) m.st.input)
        (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
          (m.st.heard ++ ds.take (rJ4 Q.P Q.g)))
        (k4SentAt (seenAt m y (rJ4 Q.P Q.g)).rounds (k4TermsEnds Q)) = some D' →
      ∀ (weighed : Array _) (parts : List Aff) (tT' : Tsc),
        o.v.y.calls.mapM o.v.weighedOf = some weighed →
        ((o.v.y.calls.zip weighed).toList.zipIdx.mapM fun x =>
          o.v.joinPart o.H.fo.alpha o.H.fo.theta x.2 x.1.1 x.1.2) = some parts →
        o.H.tT = some tT' →
        JoinWorth o.H tT' parts (worldBehind T own rdOf k y A ds' F (entryTrue tl o Mm)) D' := by
  intro D' hD
  obtain ⟨tv, te, tz, hfo, trt, hpp⟩ := joinAt_ties Z hT hLk hD
  obtain ⟨Fh, hH, hsh⟩ := joinAt_shown Z hT
  obtain ⟨_, _, _, _, _, hyo⟩ := stand_led Z
  have hh := k4_heard_front Z.seat hT
  -- the second token sumcheck's job, of the same common data
  obtain ⟨S, J, hS, hJ, _⟩ := termsJob_at Z hT
  have hS4 := (stack_open hD).1
  have eS : D'.S = S := by
    have h1 := hS4
    rw [sidesOf_fo Q _
      (p' := pts3 Q (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard ds)
      (by
        show (ptsOf Q _ (m.st.heard ++ ds.take (rJ4 Q.P Q.g))).fo =
          (ptsOf Q _ (m.st.heard ++ ds.take (rJ3 Q.P Q.g))).fo
        rw [at_look _ _ ds hh, at_look _ _ ds hh]), hS] at h1
    exact (Option.some.inj h1).symm
  have hJ' : jobTermsOn D'.S = some J := by rw [eS]; exact hJ
  have eTS : D'.S.TS = [0, 1, 2, 5] := by
    obtain ⟨_, _, _, _, _, c, _⟩ := sides_fields hS4
    exact (Option.some.inj (c.symm.trans hTS))
  have evy : D'.S.v.y = o.v.y := by rw [tv]
  exact joinWorth_made (tk := s.tokv) (hH := hH) (hy := AQ.lay) (S := AQ.sw) (hs := AQ.scales)
    (hg := AQ.grp) (hrd := AQ.reads) (hmats := AQ.tails) (hρ := gl_numerals) (Z := AQ.sized)
    (hc := hc) (hN := hN) (hfl := hfl) (hsx := hsx) (hsy := hsy) (hzk := hzk) (he := he)
    (hs0 := hs0) (hpt := hpt) (Zw := Zw) (hsL := hsL) (hlw := hlw) (h4 := h4) (R := R)
    (htm := AQ.mats) (hNM := AQ.NM) (hpad := hpad) (hinv := joinAt_inv Z hok) (h := hD) (hJ := hJ')
    (tv := tv) (te := te) (tz := tz) (hfo := hfo) (hsh := hsh) (trt := trt) (hscl := hscl)
    (W := (worldBehind T own rdOf k y A ds' F (entryTrue tl o Mm))) (Mm := Mm) (hW := rfl)
    (hpp := hpp) (hC := hC) (hts := hts) (htu := htu) (Ss := by rw [evy]; exact Ss)
    (Su := by rw [evy]; exact Su) (N := gatedNums_of_plan AQ) (hnl := hnl) (hne := hne)
    (hdq := by rw [evy, hyo]; exact hdq) (hTS := eTS) (hom := joinAt_om Z hT hD) (hQK := hQK)
    (hB1 := hB1) (hσ := terms_total_stack Z hT ds' F hL _ hD hJ')

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.join_stand
