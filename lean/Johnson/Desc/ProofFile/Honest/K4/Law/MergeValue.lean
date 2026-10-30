-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/MergeValue.lean: CONDITIONAL.

What is here. THE VALUE THAT THE MERGE SHOWS, ON THE HONEST PART's ROUNDS, READS AS THE LIBRARY's
FUNCTION OF THE INPUT's MATRIX OF WEIGHTS AT THE MERGE's POINT, PLUS THE PART's MASK ENTRY TIMES THE
LAST CHALLENGE. The merge's cube binds each claim's two tables; off the corners it reads their
multilinear extensions; these are the verifier's weight on the columns (`wsEpsT`) and the matrix's
rows, each read at the point (`fmAt`, Johnson/Road/FormsKeysMerge.lean). Statements and proofs.

  `col_ext`, `row_ext`, `share_ext`   a claim's two tables, extended to a point
  `merge_summand`   **the cube's summand at the challenges is `fmAt` at the point**
  `merge_rm_size`, `map_headD`, `sent_head`, `merge_letters`   the merge's point and last challenge
     are the part's challenges
  `merge_value`, `merge_value_win`   **the value that the merge shows**

Limits. At the reading `Reading.gl`. Premises of `merge_summand`: each claim names a unit of the
layout, passes the verifier's test on a claim's sizes, and its unit meets the library's condition
`UnitOK`; as many challenges as the matrix has column bits. Of `merge_value` besides: the challenges
have the call's shape and the part's moves answer; the list of claims is made, and there is a power
for each; the flat function returns, from a sized ledger; the part's text `hear` returns on the same
rounds, from the same ledger and at the flat text's claimed form; THE TAPE HOLDS WHAT THE ROUNDS
HOLD (`TapeIs`, FlatCore.lean). `merge_value_win` takes the premise on `hear` away, as
FlatWindow.lean does, and asks three in its stead: a later sized ledger at which the laying of the
sumcheck's own slots returns. NO WORLD AND NO SLOT IS NAMED: nothing is said on what the claimed
form is worth. THE MATRIX IS THE ONE THAT THE PART's INPUT HOLDS, AT ALL ITS ROWS: that a commitment
is to it, and that it reads 0 from some row on, is not said. That the mask entry is the entry of a
message which a witness holds is not said. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SumMergeStart
import Johnson.Desc.ProofFile.Honest.K4.Law.FlatWindow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E F zeroE oneE subE)
open OnBytes.Model (Reading Fork WsLay WsUnit WsClaim WsForkOut wsGamma wsRowPart wsEpsT
  wsClaimShape wsForkStart powers)
open OnBytes.PscRun (Sized)
open OnBytes.K.Kc (Tape flatForkEnd)
open OnBytes.Desc.First.P1 (tapeEps)
open OnBytes.Road (UnitOK fmAt shareAt rowAt eps_multilinear shape_of_claim pt)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.CubeLaw
open VerifiableInference.Desc.Part.MaskedSum
open VerifiableInference.Desc.First.MergeLaw (hear_ended hear_of_flat)
open ProofFile.Honest.SumLaw

variable {V : Type}

/-! ## 1 A claim's two tables, extended to a point -/

/-- The first table's extension is the verifier's weight on the columns at the point. -/
theorem col_ext {lay : WsLay} {c : WsClaim} {u : WsUnit} (hu : lay.U[c.ui]? = some u)
    (hs : wsClaimShape lay c = .ok ()) (U : UnitOK lay.lk u) (z : Array E) (hz : z.size = lay.lk) :
    Reading.gl.val (mle (colTab lay c) z) = Reading.gl.val (wsEpsT lay c z) := by
  rw [mle_read, hz, eps_multilinear Reading.gl hu (shape_of_claim hu hs).1 U z]
  exact Finset.sum_congr rfl fun i hi => by rw [colTab_at lay c i (Finset.mem_range.mp hi)]

/-- The second table's extension: the unit's rows, each read at the point, under the claim's weights
on them. -/
theorem row_ext {lay : WsLay} {c : WsClaim} {u : WsUnit} (w : Nat → Nat → F)
    (hu : lay.U[c.ui]? = some u) (hs : wsClaimShape lay c = .ok ()) (U : UnitOK lay.lk u)
    (z : Array E) (hz : z.size = lay.lk) :
    Reading.gl.val (mle (rowTab lay w c) z) = ∑ y ∈ Finset.range u.rows,
      Reading.gl.val ((wsGamma u (wsRowPart lay c oneE) oneE).getD y zeroE) *
        rowAt Reading.gl lay.lk z (wmOf w) (u.off + y) := by
  rw [mle_read, hz]
  have e : ∀ i ∈ Finset.range (2 ^ lay.lk),
      Blocks.eqN lay.lk 0 (pt Reading.gl z) i * Reading.gl.val ((rowTab lay w c).getD i zeroE) =
        ∑ y ∈ Finset.range u.rows,
          Reading.gl.val ((wsGamma u (wsRowPart lay c oneE) oneE).getD y zeroE) *
            (Blocks.eqN lay.lk 0 (pt Reading.gl z) i * wmOf w (u.off + y) i) := by
    intro i hi
    rw [rowTab_read w hu (gam_size hu hs U) i (Finset.mem_range.mp hi), Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [Finset.sum_congr rfl e, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  unfold rowAt
  rw [Finset.mul_sum]

/-- The product of the two extensions is the claim's share of the library's function. -/
theorem share_ext {lay : WsLay} {c : WsClaim} {u : WsUnit} (w : Nat → Nat → F)
    (hu : lay.U[c.ui]? = some u) (hs : wsClaimShape lay c = .ok ()) (U : UnitOK lay.lk u)
    (z : Array E) (hz : z.size = lay.lk) :
    Reading.gl.val (mle (colTab lay c) z) * Reading.gl.val (mle (rowTab lay w c) z) =
      shareAt Reading.gl lay (wmOf w) z c := by
  rw [col_ext hu hs U z hz, row_ext w hu hs U z hz]
  unfold shareAt
  rw [hu]

/-! ## 2 The cube's summand at the challenges -/

/-- **The summand of the merge's cube at the challenges is the library's function of the matrix at
the point that the challenges make.** -/
theorem merge_summand (lay : WsLay) (w : Nat → Nat → F) (cls : List WsClaim) (rho : Array E)
    (hcl : ∀ c ∈ cls, ∃ u, lay.U[c.ui]? = some u ∧ wsClaimShape lay c = .ok () ∧
      UnitOK lay.lk u) (rs : List E) (hr : rs.length = lay.lk) :
    Reading.gl.val ((mergeJobOf lay w cls rho).cube.summandAt rs) =
      fmAt Reading.gl lay (wmOf w) (cls.zipIdx.map fun x => (x.1, rho.getD x.2 zeroE))
        rs.toArray := by
  have hfit := mergeJob_fits lay w cls rho
  have hp : (mergeJobOf lay w cls rho).cube.pointOf rs = rs.toArray :=
    pointOf_default _ hfit rfl rs hr
  rw [summandAt_read]
  show ((cls.zipIdx.map fun x => (rho.getD x.2 zeroE, 2 * x.2, 2 * x.2 + 1)).map _).sum = _
  unfold fmAt
  rw [List.map_map, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun x hx => ?_)
  obtain ⟨u, hu, hs, U⟩ := hcl x.1 (zipIdx_mem cls 0 x hx)
  have hm := mergeMaps_at lay w cls [] 0 rfl x hx
  have hg : ∀ a, (mergeJobOf lay w cls rho).cube.maps.getD a #[] =
      ([] ++ cls.flatMap fun c => [colTab lay c, rowTab lay w c]).getD a #[] := by
    intro a
    have ht : (mergeJobOf lay w cls rho).cube.maps.toList =
        [] ++ cls.flatMap fun c => [colTab lay c, rowTab lay w c] :=
      mergeMaps_toList lay w cls #[]
    rw [← ht, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]
  show Reading.gl.val (rho.getD x.2 zeroE) *
    (Reading.gl.val (((mergeJobOf lay w cls rho).cube.valuesAt rs).getD (2 * x.2) zeroE) *
      Reading.gl.val (((mergeJobOf lay w cls rho).cube.valuesAt rs).getD (2 * x.2 + 1) zeroE)) =
        Reading.gl.val (rho.getD x.2 zeroE) * _
  rw [valuesAt_mle Reading.gl _ hfit rs hr, valuesAt_mle Reading.gl _ hfit rs hr, hp, hg, hg, hm.1,
    hm.2, share_ext w hu hs U rs.toArray (by simpa using hr)]

/-! ## 3 The value that the merge shows -/

/-- The first member of a list, read. -/
theorem map_headD {α β : Type} (f : α → β) (d : α) : ∀ l : List α,
    (l.map f).headD (f d) = f (l.headD d)
  | [] => rfl
  | _ :: _ => rfl

/-- The one value as sent reads as the job's summand on the masked end values. -/
theorem sent_head (lay : WsLay) (w : Nat → Nat → F) (cls : List WsClaim) (rho : Array E)
    (rs m : List E) (y x : E)
    (h : [x].map Reading.gl.val =
      (maskedEnds ((mergeJobOf lay w cls rho).ends rs) m y).map Reading.gl.val) :
    Reading.gl.val x = Reading.gl.val ((mergeJobOf lay w cls rho).atEnds rs
      (maskedEnds ((mergeJobOf lay w cls rho).ends rs) m y)) := by
  have b5 := congrArg (fun l => l.headD (Reading.gl.val zeroE)) h
  show _ = Reading.gl.val (List.headD _ zeroE)
  rw [← map_headD Reading.gl.val zeroE]
  exact b5

/-- The merge's point and its last challenge are what `hear` has read. -/
theorem merge_letters {lay : WsLay} {cl : Array WsClaim} {sv : Array Nat} {F G : Fork}
    {t u : Tape} {wo : WsForkOut} (hF : flatForkEnd lay cl sv F t = some (wo, G, u)) {h : Heard}
    (hL : SameLetters wo.p h) :
    wo.rm = (h.r.take lay.lk).toArray ∧ wo.beta = h.r.getD lay.lk zeroE := by
  obtain ⟨x, mu, c, beta, v, T, r1, rY, rV, qs, hn, _, _, _, hE, hrm, hb, _⟩ :=
    hear_ended (hear_of_flat hF)
  have hr : h.r = qs.map (·.2.2) ++ [beta] := by
    rw [← hL.r, hE.r, List.map_map]
    rfl
  have hl : (qs.map (·.2.2)).length = lay.lk := by rw [List.length_map, hn]
  refine ⟨?_, ?_⟩
  · apply Array.toList_inj.mp
    rw [hrm, hr, ← hl, List.take_left]
  · rw [hb, hr, ← hl, List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _),
      Nat.sub_self]
    rfl

/-- The merge's point has a coordinate for each column bit. -/
theorem merge_rm_size {lay : WsLay} {cl : Array WsClaim} {sv : Array Nat} {F G : Fork}
    {t u : Tape} {wo : WsForkOut} (hF : flatForkEnd lay cl sv F t = some (wo, G, u)) :
    wo.rm.size = lay.lk := by
  obtain ⟨x, mu, c, beta, v, T, r1, rY, rV, qs, hn, _, _, _, _, hrm, _⟩ :=
    hear_ended (hear_of_flat hF)
  rw [← Array.length_toList, hrm, List.length_map, hn]

/-- **The value that the merge shows**, where both texts of the verifier return. cls: the honest
parts' list of claims. -/
theorem merge_value (name endName : String) (Q : K4Pub)
    (c : SumCoins name endName (mergeSum Q)) (st : State K4In Unit) (seen : Seen)
    (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (F G : Fork) (h : Heard)
    {cl : Array WsClaim} {sv : Array Nat} {tp u : Tape} {G2 : Fork} {wo : WsForkOut}
    (hd : drawsOk ((mergeSum Q).callAt st.input (frontOf st seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName (mergeSum Q)) c st seen ds = some rounds)
    (hh : hear (wsForkStart sv (powers (tapeEps tp) sv.size))
      ((mergeSum Q).callAt st.input (frontOf st seen)) F rounds = some (h, G))
    (cls : List WsClaim) (hc : mergeClaimsAt Q st.input (ptsOf Q st.input st.heard) = some cls)
    (hcl : ∀ c ∈ cls, ∃ u, Q.P.wsLay.U[c.ui]? = some u ∧ wsClaimShape Q.P.wsLay c = .ok () ∧
      UnitOK Q.P.wsLay.lk u)
    (hlen : cls.length ≤ (ptsOf Q st.input st.heard).rhoW.size)
    (hF : flatForkEnd Q.P.wsLay cl sv F tp = some (wo, G2, u)) (hS : Sized F)
    (hT : TapeIs (tp.drop 1) rounds) :
    Reading.gl.val wo.fvp =
      fmAt Reading.gl Q.P.wsLay (wmOf st.input.w)
          (cls.zip (ptsOf Q st.input st.heard).rhoW.toList) wo.rm +
        Reading.gl.val ((endRun c).getD 0 zeroE) * Reading.gl.val wo.beta := by
  obtain ⟨rho, hrho⟩ : ∃ rho, (ptsOf Q st.input st.heard).rhoW = rho := ⟨_, rfl⟩
  rw [hrho] at hlen ⊢
  obtain ⟨hSL, rv, a1, a2⟩ := merge_sameLetters hF hS _
    (merge_weights Q st.input (frontOf st seen)) hh hT
  obtain ⟨erm, ebeta⟩ := merge_letters hF hSL
  have hr : h.r = varsOf ((mergeSum Q).callAt st.input (frontOf st seen)) ds :=
    (sumClaim V K4In Unit name endName (mergeSum Q) c st seen ds rounds _ F G h hd ha hh).2.1
  have hj : (fun (w : K4In) (fr : Front Unit) => jobMerge Q w (ptsOf Q w fr.heard)) st.input
      (frontOf st seen) =
      some (mergeJobOf Q.P.wsLay st.input.w cls rho) := by
    show (mergeClaimsAt Q st.input (ptsOf Q st.input st.heard)).map _ = _
    rw [hc, ← hrho]
    rfl
  obtain ⟨r, s, b1, b2, b3, b4⟩ := k4_sent (V := V) name endName (k4PlainShape Q.P.wsLay.lk 1 1)
    (fun w fr => jobMerge Q w (ptsOf Q w fr.heard)) c st seen ds rounds
    (mergeJobOf Q.P.wsLay st.input.w cls rho) ⟨1, 1⟩ hd ha hj
    (jobFits_parts (mergeJob_jobFits _ _ _ _)) rfl rfl
  have e1 : rv = r := Option.some.inj (a1.symm.trans b1)
  rw [e1] at a2
  have e2 : s = [wo.fvp] := Option.some.inj (b2.symm.trans a2)
  rw [e2, ← hr] at b4
  have hrl : (h.r.take Q.P.wsLay.lk).length = Q.P.wsLay.lk := by
    have := heard_r_length (V := V) hd ha hh
    rw [List.length_take]
    have e : ((mergeSum Q).callAt st.input (frontOf st seen)).all.length = Q.P.wsLay.lk + 1 := by
      show (withPoints (List.replicate Q.P.wsLay.lk (Var.plain 3)) _ ++ [_]).length = _
      rw [List.length_append, wp_replicate_plain, List.length_replicate]
      rfl
    omega
  have hm : (endRun c).length = 1 := endRun_length c ⟨1, 1⟩ rfl
  have b6 := sent_head Q.P.wsLay st.input.w cls rho _ _ _ _ b4
  have ez : (cls.zipIdx.map fun x => (x.1, rho.getD x.2 zeroE)) = cls.zip rho.toList := by
    have hz := zipIdx_zip rho.toList cls 0 (by simpa using hlen)
    rw [List.drop_zero] at hz
    rw [← hz]
    refine List.map_congr_left fun x _ => ?_
    rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]
  have hn : (mergeJobOf Q.P.wsLay st.input.w cls rho).cube.n = Q.P.wsLay.lk := rfl
  rw [hn] at b6
  rw [b6, mergeJob_end _ _ _ _ _ _ hm, merge_summand _ _ _ _ hcl _ hrl, ez, ← erm, ← ebeta]
  ring

/-- **The value that the merge shows**, without a premise on the part's text of the verifier. Fz: a
later ledger at which the verifier lays the sumcheck's own slots. -/
theorem merge_value_win (name endName : String) (Q : K4Pub)
    (c : SumCoins name endName (mergeSum Q)) (st : State K4In Unit) (seen : Seen)
    (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (F : Fork)
    {cl : Array WsClaim} {sv : Array Nat} {tp u : Tape} {G2 : Fork} {wo : WsForkOut}
    (hd : drawsOk ((mergeSum Q).callAt st.input (frontOf st seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName (mergeSum Q)) c st seen ds = some rounds)
    (cls : List WsClaim) (hc : mergeClaimsAt Q st.input (ptsOf Q st.input st.heard) = some cls)
    (hcl : ∀ c ∈ cls, ∃ u, Q.P.wsLay.U[c.ui]? = some u ∧ wsClaimShape Q.P.wsLay c = .ok () ∧
      UnitOK Q.P.wsLay.lk u)
    (hlen : cls.length ≤ (ptsOf Q st.input st.heard).rhoW.size)
    (hF : flatForkEnd Q.P.wsLay cl sv F tp = some (wo, G2, u)) (hS : Sized F)
    (hT : TapeIs (tp.drop 1) rounds) (Fz F1 : Fork) (hL : Fo.Later G2 Fz) (hSz : Sized Fz)
    (hW : Fz.hideRun wo.p.first (Array.replicate wo.p.walk.1.length zeroE) (subE zeroE oneE) =
      some F1) :
    Reading.gl.val wo.fvp =
      fmAt Reading.gl Q.P.wsLay (wmOf st.input.w)
          (cls.zip (ptsOf Q st.input st.heard).rhoW.toList) wo.rm +
        Reading.gl.val ((endRun c).getD 0 zeroE) * Reading.gl.val wo.beta := by
  obtain ⟨h, G, hh, _⟩ := k4_hears (V := V) name endName (mergeSum Q) c st seen ds rounds
    (wsForkStart sv (powers (tapeEps tp) sv.size)) F
    (shapeOk_plain _ (Nat.le_refl 1) (Nat.le_refl 1)) hd ha
    (merge_ready hF hS _ (merge_weights Q st.input (frontOf st seen)) hL hSz hW)
  exact merge_value (V := V) name endName Q c st seen ds rounds F G h hd ha hh cls hc hcl hlen hF hS
    hT

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.col_ext
#print axioms ProofFile.Honest.K4.row_ext
#print axioms ProofFile.Honest.K4.share_ext
#print axioms ProofFile.Honest.K4.merge_summand
#print axioms ProofFile.Honest.K4.map_headD
#print axioms ProofFile.Honest.K4.sent_head
#print axioms ProofFile.Honest.K4.merge_letters
#print axioms ProofFile.Honest.K4.merge_rm_size
#print axioms ProofFile.Honest.K4.merge_value
#print axioms ProofFile.Honest.K4.merge_value_win
