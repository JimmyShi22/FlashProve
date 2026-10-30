-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/OwnAtFoot.lean: CONDITIONAL.

What is here. The own claims of four masked sumchecks of K4 are worth 0 at a state behind the
member's step: `OwnFront` (Johnson/Road/K4/W/Join.lean), in the world that `RightFoot.own` names
(Law/W/ItemRightOf.lean). One call of `ownFront_stand` (Law/OwnAtStand.lean), whose three premises
on the sumchecks' starts are paid by `start_squares`, `start_gated1`, `start_gated2`
(Law/W/StartsAt.lean). What these ask: the slots' worths by `own_h1`, `own_h2`
(Law/W/RightStack.lean) and by the left half with `right_norms` (Law/SlotsTrue.lean,
Law/W/RightNorms.lean); the honest side's returns by Law/W/MakersReturn.lean and `tabs_at`
(Law/W/ItemRightOf.lean); that the sampled values are the verifier's by the laws of Law/PtsAt.lean
on the library's LedG; sizes by Law/W/SizesOfLed.lean, Law/W/StandHear.lean and LedG's own fields;
public numbers by Johnson/Road/K4/C/, among them that the plan of the hashed rounds has room for the
first gated product's coordinates (`lam_room`, C/LamRoom.lean).

  `own_at`   OwnFront at a state behind the member's step.

Not shown here. K4Stand, Thr, K4LookTieAt, K4Plan (ITS FIELD sw BARS EVERY SHAPE BUT THOSE WITH THE
LIBRARY's ELEVEN SWITCHES), K4Ground, CellsAre, drawsFit at the step's rounds (hd); that "front"
returns and what the ledger shows under the row products' end values (hf, hsh): hypotheses. That
they can hold together: no example is known. K4Seated's field fits (the public test k4Fits) is
spent. THE OWN CLAIMS BEHIND "back" ARE NOT REACHED HERE. By a walk of import lines the closure
holds seven modules under Johnson/RecCompile/ (Join, Wire, Pass, CmsGlue, CmsBcs, Cms, Bcs), through
Law/SlotsTrue.lean's imports; none under Johnson/Goal/ or Johnson/D/; under Johnson/RecCompile/ none
of the names Honest…, Both…, PassH…. Nothing on soundness, on completeness or on any other property.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.StartsAt
import Johnson.Desc.ProofFile.Honest.K4.Law.W.ItemRightOf
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MakersAt
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MakersReturn
import Johnson.Desc.ProofFile.Honest.K4.Law.W.StandHear
import Johnson.Desc.ProofFile.Honest.K4.Law.W.SizesOfLed
import Johnson.Desc.ProofFile.Honest.K4.Law.OwnAtStand
import Johnson.Desc.ProofFile.Honest.K4.Law.ClaimsAre
import Johnson.Road.K4.C.RowFieldsPub
import Johnson.Road.K4.C.PlanLens
import Johnson.Road.K4.C.LamRoom

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.PscRun (Later)
open OnBytes.Road (sclOf cellsOf cellsAt gl_numerals admitted_of_layout)
open OnBytes.Road.K4 (entryTrue nNu_tie)
open OnBytes.Road.K4.W (K4Plan K4Ground OwnFront ground holds_item)
open OnBytes.Road.K4.C (CellsAre gated_tensors gatedNums_of_plan normsPlan_of_plan gatedIn_of_plan
  rowFields_pub planLens_of_plan lam_room)
open OnBytes.Desc.First.K4 (Par formsFrontWith formsFrontWith_later)
open OnBytes.Desc.First.K4.Honest
open Inst.Model.FFSeg (Dim lF lFe)
open VerifiableInference.Desc (Block Claim First.S)
open VerifiableInference.Desc.Sound (MsgQ dataQ)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}

/-- **OwnFront AT A STATE BEHIND THE MEMBER's STEP.** CONDITIONAL: on every hypothesis named. -/
theorem own_at {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    {b : Nat} {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Q : K4Pub} {p : Par}
    {blk : Block First.S Claim} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}
    {k : Coins Bk} {s s' : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn} {A : VerifiableInference.Desc.K9.Part} {o : Own}
    {h : Layer.Shape} {pc : List (List String)} {tl : HTailF2} {D : Dim}
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (hT : Thr T b k s m E) (hd : drawsFit blk.rounds ds = true) (hLk : K4LookTieAt look Q s m)
    (AQ : K4Plan h pc Q.P Q.g tl D)
    {r : List Layer.TableAt × List (Layer.TableAsk × List (ℕ × ℕ)) × ℕ}
    {pts : List (String × Array OnBytes.E)}
    (Gr : K4Ground h pc o.v Q.P.rd r tl o.H o.hd o.hd2 pts o.funs D) {Mm : Road.Mats Cb.Gl.E}
    (C : CellsAre Q (k4Wit Q cells weights tokens (look Q) m.st.input) Mm) (ds' : List Fmt.Drawn)
    {rows : Bool} {P' : Layer.Pub} {g' : ℕ} {fs₁ : Array Aff} {F₁ : Fork}
    (hf : formsFrontWith rows P' g' o A.F = some (fs₁, F₁)) (sh : Array OnBytes.E)
    (hsh : ((Array.range (4 * Q.P.y.NI)).mapM fun i => A.F.shown (o.H.tV.sEnd + i)) = some sh) :
    OwnFront Reading.gl
      (F₁.worldOf Reading.gl (dataQ own A (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))).mask
        (entryTrue tl o Mm)) Q.P o sh := by
  letI : Inst.Model.Scl := sclOf h o.v.sc o.v.g o.v.y.Lam
  obtain ⟨hd2, tT, ⟨F, G, t, u, H1, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5, L, hD⟩, hr, eg,
    ey⟩ := stand_led Z
  obtain ⟨e0, _, _, _, e4, e5, _⟩ := k4StartAt_eq Q
  obtain ⟨hll, hPf, elt, _, hN, hdd⟩ := planLens_of_plan AQ
  have N := gatedNums_of_plan AQ
  have Np := normsPlan_of_plan AQ
  have l1 : k4StartAt Q 1 ≤ ds.length := by
    simp only [k4StartAt] at hr ⊢
    omega
  have l2 : k4StartAt Q 2 ≤ ds.length := by
    simp only [k4StartAt] at hr ⊢
    omega
  have l3 : k4StartAt Q 3 ≤ ds.length := by
    simp only [k4StartAt] at hr ⊢
    omega
  have l4 : k4StartAt Q 4 ≤ ds.length := by
    simp only [k4StartAt] at hr ⊢
    omega
  have l5 : k4StartAt Q 5 ≤ ds.length := by
    simp only [k4StartAt] at hr ⊢
    omega
  have l0 : k4StartAt Q 0 ≤ ds.length := by
    simp only [k4StartAt] at hr ⊢
    omega
  have Ad := admitted_of_layout Gr.lay Gr.sw.p3
  have Sw : OnBytes.Road.Switches o.v.y.h := by rw [Ad.shape]; exact Gr.sw
  obtain ⟨_, _, _, _, Ft, _⟩ := ground Gr gl_numerals Mm
    (holds_item Gr Mm F₁ (dataQ own A (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))).mask)
  obtain ⟨ts, tu, hts, htu, Ss, Su⟩ :=
    gated_tensors Ft ey.symm Ad.laid Sw C Np.mats (gatedIn_of_plan AQ)
  have OL := opened_left Z ds' F₁ (formsFrontWith_later hf) (entryTrue tl o Mm)
  obtain ⟨SD, e4', data, ends, _⟩ :=
    stackJob_at Z hT (k4SentAt (m.seen ++ roundsOf (y.1.take (rJ4 Q.P Q.g))) (k4TermsEnds Q))
  have SA := stackAt_at (seen := m.shown.plus (roundsOf (y.1.take (rJ4 Q.P Q.g))))
    Z hT hLk data ends
  have hlam : D.lL + lF D ≤ Q.hp.lamS := lam_room data ends N
  have rsz := rs_size L hD l4
  have h1 := own_h1 OL SA hts htu Ss Su N ((ztF_size L).trans elt) (by rw [rsz]; exact hlam)
  have h2 := own_h2 OL SA hts htu Ss Su N
    (by rw [rsz]; have := N.ffe; omega) (fun tT' hq => (rt_size L hD l3 tT' hq).trans elt)
  have hh := k4_heard_front Z.seat hT
  have hzx := stand_zx Z hLk
  obtain ⟨Fh, hH⟩ := stand_hear Z
  have hzk : (look Q m.st.heard).zk = o.H.fo.zk := by
    obtain ⟨g, _, q2, _, hz, _⟩ := hLk
    have el := stand_look Z
    rw [q2] at el
    obtain rfl := Option.some.inj el
    exact hz
  have hmats : matsOf Q = Road.matsR o.v.y o.v.g := by rw [ey, eg]; exact AQ.tails
  have RN := right_norms (ptsAre_at Z hT _)
    (makersNorms_at Z hT hd ((PV_size L hD l1).trans elt) elt) Ft ey.symm C Np
    (rowFields_pub Gr (env_is hH _ (by rw [at_look _ _ ds hh]; exact hzk)) hmats rfl C Np.NI
      ((rtV_size L hD l2).trans elt))
  have HN := halvesNums_of_plan AQ ey eg
  obtain ⟨tb1, tb2, t1, t2, f1, _⟩ := tabs_at Z hT hd
  have hnl : Q.P.y.xb.nl = 5 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, T0, _⟩ := Ft.stream
    rw [← ey]
    exact T0.1
  refine ownFront_stand Z hT hLk ds' hf F₁ (Later.refl _) (entryTrue tl o Mm)
    (by rw [Np.NI, nNu_tie AQ.sized]; exact Nat.mul_pos (by decide) (Nat.two_pow_pos _)) sh hsh
    ?_ ?_ ?_
  · intro j hj
    refine start_squares Ft ey.symm C Np (fun ν hν q hq => ?_) _
      (at_PV _ _ L ds hD l1 hh _ (by rw [← e0]; simp only [k4StartAt]; omega))
      ((at_gp _ _ L ds hD l1 hh _ (by rw [← e0]; simp only [k4StartAt]; omega)).trans
        (L.kGp.trans L.gp))
      HN.NS hnl
      (by rw [at_rhoI _ _ ds hD l0 hh _ (by rw [e0]), List.size_toArray]; exact L.lI)
      ((PV_size L hD l1).trans elt) hN hdd hj
    rw [Nat.add_assoc, OL.sums (9 * ν + q) (by rw [HN.NS, HN.NI]; omega)]
    exact RN.sums ν hν q hq
  · intro tb htb
    obtain rfl : tb1 = tb := Option.some.inj (t1.symm.trans htb)
    exact start_gated1 h1 hts htu Ss Su N hll hPf _
      (at_rs _ _ L ds hD l4 hh _ (by rw [← e4]; simp only [k4StartAt]; omega))
      (at_zt _ _ L ds hh hzx _) htb f1
  · intro tb htb
    exact start_gated2 (fun lm hlm => h2 _ L.kTT lm (by rw [ey]; exact hlm)) hts htu Ss Su N _
      (at_rs _ _ L ds hD l4 hh _ (by rw [← e5]; simp only [k4StartAt]; omega))
      (at_rt _ _ L ds hD l3 hh _ (by rw [← e5]; simp only [k4StartAt]; omega))
      (by rw [rsz]; have := N.ffe; omega)
      (by
        rw [at_rhoM _ _ ds hD l5 hh _ (by rw [e5]), List.size_toArray, L.lM, hll])
      ((rt_size L hD l3 _ L.kTT).trans elt) htb

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.own_at
