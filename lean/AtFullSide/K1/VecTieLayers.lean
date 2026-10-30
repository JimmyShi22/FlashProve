-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/VecTieLayers.lean: THE POINTS THAT THE HONEST SIDE LISTS AT A LAYERS' READS ARE THE VERIFIER's,
ONCE ALL THE SUB-PROTOCOL's ROUNDS ARE HEARD: what the vector of reads needs of the tables.
Statements and proofs.

  `ZE_else`       outside the first group the verifier's embedding point is empty
  `named_whole`   at a point that has coordinates, the honest list finds what the verifier's finds
  `funs_honest`   so `funsOf` returns at the honest list what it returns at the verifier's

Limits. LedG, DrawnIs, that all the rounds are heard, the lookup's ties (hzx, hB) and the sizes (hla,
hlt, hE) are premises: no run is read here. Nothing on any property.
-/
import Johnson.Road.K4.C.ReadsAgree
import Johnson.Desc.ProofFile.Honest.K4.Law.PtsFront
import Johnson.Desc.First.K4.Returns.Points
import Johnson.Road.FormsKeysPoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.VT
open OnBytes (E)
open OnBytes.Model (Fork Level Tsc lastOf)
open OnBytes.Model.Layer (Own TableAsk phiOf pointsOf funsOf)
open OnBytes.K.Kc (Tape)
open OnBytes.Road.K4 (LedG)
open OnBytes.Road.K4.C (lastSeg fullSeg namedPts_eq)
open ProofFile.Honest.K4 (k4StartAt DrawnIs at_look at_zt at_r6 at_PV at_rtV at_r12 at_rt at_r14 led_fo led_ztF led_rt led_rtV at_ZE at_ZE_else norms_vals drawnE_take_length)
open OnBytes.Desc.First.K4.Honest (K4Pub K4In ptsOf namedPts ztOf)
open OnBytes.Desc.First.K4.Rt (lastOf_size)

theorem lastSeg_some {la : ℕ} {n : String} {z x : Array E} (hla : la ≠ 0)
    (h : (lastOf z la).toOption = some x) : lastSeg la n z = [(n, x)] := by
  have hs : x.size = la := lastOf_size h
  have hz : z.isEmpty = false := by
    by_cases e : z.isEmpty = true
    · have : z = #[] := by simpa using e
      subst this
      unfold lastOf OnBytes.Model.cutLast at h
      rw [if_pos (by simp; omega)] at h
      cases h
    · simpa using e
  unfold lastSeg
  rw [h]
  simp [hz]

theorem fullSeg_some {k : ℕ} {n : String} {z : Array E} (hk : k ≠ 0) (h : z.size = k) :
    fullSeg n k z = [(n, z)] := by
  unfold fullSeg
  simp [h, hk]

theorem fullSeg_none {k : ℕ} {n : String} {z : Array E} (h : z.size ≠ k) : fullSeg n k z = [] := by
  unfold fullSeg
  simp [h]

variable {Q : K4Pub} {tk : Array Nat} {t : Tape} {fo : OnBytes.Model.Forest.Heard} {o : Own} {F G : Fork}
  {u : Tape} {H1 : OnBytes.Model.Layer.Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape} {w : K4In} {h ds : List Fmt.Drawn}

/-- A search passes a member of another name. -/
theorem find_erase {n : String} {x : String × Array E} (hx : x.1 ≠ n) :
    ∀ l₁ l₂ : List (String × Array E), ((l₁ ++ x :: l₂).find? fun y => y.1 == n) =
      (l₁ ++ l₂).find? fun y => y.1 == n
  | [], l₂ => by
    rw [List.nil_append, List.nil_append, List.find?_cons_of_neg (by simpa using hx)]
  | y :: l, l₂ => by
    rw [List.cons_append, List.cons_append, List.find?_cons, List.find?_cons, find_erase hx l l₂]

/-- Outside the first group the verifier's embedding point is empty. -/
theorem ZE_else
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (hg : (Q.g == 0) = false) : o.H.ZE = #[] := by
  obtain ⟨u1, hN, hT⟩ := L.nt
  obtain ⟨_, _, k3, _, _⟩ := OnBytes.Desc.First.K4.hearTerms_keeps hT
  obtain ⟨F1, F2, F3, F4', F5, F6, F7', F8', F9, t1, t2, t3, t4, t5, t6, t7, t8, t9, c1, c2, _⟩ :=
    OnBytes.Desc.First.K4.hearNorms_calls hN
  rw [if_neg (by simp [hg])] at c2
  have e : (#[] : Array E) = H1.ZE := (Prod.mk.inj (Option.some.inj c2)).1
  rw [k3, ← e]

/-- **Once all the rounds are heard, the honest list finds what the verifier's finds, at a point
that has coordinates.** -/
theorem named_whole {pts : List (String × Array E)}
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (hD : DrawnIs t ds) (hl : k4StartAt Q 6 ≤ ds.length) (hh : h.length = Q.r0)
    (hzx : (w.look h).zx = fo.zx) (hla : Q.P.y.h.la ≠ 0) (hlt : Q.P.y.h.lt ≠ 0)
    (hE : (Q.g == 0) = true → o.H.ZE.size = Q.P.y.h.la)
    (hpts : pointsOf Q.P.y o.H o.hd (some hd2) = some pts) {n : String} {q : String × Array E}
    (hq : (pts.find? fun x => x.1 == n) = some q) (hs : q.2.size ≠ 0) :
    ((namedPts Q (ptsOf Q w (h ++ ds))).find? fun x => x.1 == n) = some q := by
  have l1 : k4StartAt Q 1 ≤ ds.length := by
    simp only [k4StartAt] at hl ⊢
    omega
  have l2 : k4StartAt Q 2 ≤ ds.length := by
    simp only [k4StartAt] at hl ⊢
    omega
  have l3 : k4StartAt Q 3 ≤ ds.length := by
    simp only [k4StartAt] at hl ⊢
    omega
  have l5 : k4StartAt Q 5 ≤ ds.length := by
    simp only [k4StartAt] at hl ⊢
    omega
  have e0 : h ++ ds = h ++ ds.take ds.length := by rw [List.take_length]
  obtain ⟨Z, zv, za, routed, hZ, hzv, hza, hr, rfl⟩ := OnBytes.Road.K4.C.points_open hpts
  obtain ⟨zb, hzb, rfl⟩ := Option.map_eq_some_iff.1 hr
  have fz : o.H.fo = fo := led_fo L
  rw [e0, namedPts_eq]
  have pz : (ptsOf Q w (h ++ ds.take ds.length)).fo.zx = o.H.fo.zx := by
    rw [at_look w h ds hh, hzx, fz]
  have pt : ztOf Q (ptsOf Q w (h ++ ds.take ds.length)) = o.H.ztF := at_zt w h L ds hh hzx _
  have p6 := at_r6 w h L ds hD l1 hh ds.length (by simp only [k4StartAt] at hl ⊢; omega)
  have pV := at_PV w h L ds hD l1 hh ds.length (by simp only [k4StartAt] at hl ⊢; omega)
  have pT := at_rtV w h L ds hD l2 hh ds.length (by simp only [k4StartAt] at hl ⊢; omega)
  have p12 := at_r12 w h L ds hD l5 hh ds.length (by simp only [k4StartAt] at hl ⊢; omega)
  have prt := at_rt w h L ds hD l3 hh ds.length (by simp only [k4StartAt] at hl ⊢; omega)
  have p14 := at_r14 w h L ds hD hl hh ds.length (by simp only [k4StartAt] at hl ⊢; omega)
  have sZt : o.H.ztF.size = Q.P.y.h.lt := lastOf_size (led_ztF L)
  have sPV : o.H.PV.size = Q.P.y.h.lt := by
    obtain ⟨u1, hN, _⟩ := L.nt
    obtain ⟨_, _, _, a4, _⟩ := norms_vals hN ds hD l1
    rw [L.kPV]
    exact a4
  have sTV : o.H.tV.r.size = Q.P.y.h.lt := by
    rw [led_rtV L ds hD l2, List.size_toArray]
    refine drawnE_take_length ds _ _ ?_
    simp only [k4StartAt] at l2 ⊢
    omega
  have sRt : tT.r.size = Q.P.y.h.lt := by
    rw [led_rt L ds hD l3, List.size_toArray]
    refine drawnE_take_length ds _ _ ?_
    simp only [k4StartAt] at hl ⊢
    omega
  have l0 : 3 ≤ ds.length := by
    simp only [k4StartAt] at hl
    omega
  have hq1 := hq
  rw [L.kTT] at hq1
  rw [pz, pt, p6, pV, pT, p12, prt, p14, lastSeg_some hla hZ, fullSeg_some hlt sZt,
    lastSeg_some hla hzv, fullSeg_some hlt sPV, fullSeg_some hlt sTV, lastSeg_some hla hza,
    lastSeg_some hla hzb]
  by_cases hg : (Q.g == 0) = true
  · rw [at_ZE w h L ds hD l0 hg hh ds.length (by omega), fullSeg_some hla (hE hg)]
    simpa [sRt, List.append_assoc] using hq1
  · have hg' : (Q.g == 0) = false := by simpa using hg
    have hz0 : o.H.ZE = #[] := ZE_else L hg'
    rw [at_ZE_else w hg', fullSeg_none (by simpa using Ne.symm hla)]
    rw [hz0] at hq1
    by_cases hn : n = "Z_E"
    · subst hn
      simp at hq1
      subst hq1
      simp at hs
    · have e := find_erase (n := n) (x := ("Z_E", #[])) (fun e => hn e.symm)
        [("Z", Z), ("zt", o.H.ztF), ("Z_V", zv), ("P_V", o.H.PV)]
        ([("r_tV", o.H.tV.r), ("Z_a", za), ("Y", OnBytes.Model.longPoint (Z.extract 0 Q.P.y.ls) tT.r),
          ("rt", tT.r), ("Z_b", zb)])
      simp only [List.append_assoc, List.cons_append, List.nil_append] at hq1 e ⊢
      simpa [sRt] using e.symm.trans hq1

theorem mapM_congr_mem {α β : Type} {f g : α → Option β} : ∀ (l : List α),
    (∀ a ∈ l, f a = g a) → l.mapM f = l.mapM g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.mapM_cons, List.mapM_cons, h a List.mem_cons_self,
      mapM_congr_mem l fun b hb => h b (List.mem_cons_of_mem _ hb)]

/-- **The tables at the honest list are the verifier's.** hB: the lookup's reader and the hearing's
lookup give one weights of the bits. -/
theorem funs_honest {pts : List (String × Array E)}
    {laid : List (OnBytes.Model.Layer.TableAsk × List (ℕ × ℕ))} {funs : Array OnBytes.Model.HFun}
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (hD : DrawnIs t ds) (hl : k4StartAt Q 6 ≤ ds.length) (hh : h.length = Q.r0)
    (hzx : (w.look h).zx = fo.zx) (hla : Q.P.y.h.la ≠ 0) (hlt : Q.P.y.h.lt ≠ 0)
    (hE : (Q.g == 0) = true → o.H.ZE.size = Q.P.y.h.la)
    (hB : ∀ lm e, OnBytes.Model.Forest.phiB (w.look h) lm e = OnBytes.Model.Forest.phiB fo lm e)
    (hpts : pointsOf Q.P.y o.H o.hd (some hd2) = some pts)
    (hf : funsOf Q.P.y fo pts laid = some funs) :
    funsOf Q.P.y (ptsOf Q w (h ++ ds)).fo (namedPts Q (ptsOf Q w (h ++ ds))) laid = some funs := by
  have hfo : (ptsOf Q w (h ++ ds)).fo = w.look h := by
    have e := at_look w h ds hh ds.length
    rwa [List.take_length] at e
  have key : ∀ q ∈ laid, phiOf Q.P.y (ptsOf Q w (h ++ ds)).fo
      (namedPts Q (ptsOf Q w (h ++ ds))) q.1 = phiOf Q.P.y fo pts q.1 := by
    intro q hq
    obtain ⟨phi, hphi, -⟩ := OnBytes.Road.funsOf_mem hf hq
    rw [hphi]
    rw [hfo]
    unfold phiOf at hphi ⊢
    by_cases b0 : (q.1.name == "b-bits-0") = true
    · rw [if_pos b0] at hphi ⊢
      rw [hB, hphi]
    · rw [if_neg b0] at hphi ⊢
      by_cases b1 : (q.1.name == "b-bits-1") = true
      · rw [if_pos b1] at hphi ⊢
        rw [hB, hphi]
      · rw [if_neg b1] at hphi ⊢
        by_cases b2 : (q.1.name == "b-pin") = true
        · rw [if_pos b2] at hphi ⊢
          exact hphi
        · rw [if_neg b2] at hphi ⊢
          cases hp : pts.find? (fun p => p.1 == q.1.point) with
          | none =>
            rw [hp] at hphi
            cases hphi
          | some p =>
            rw [hp] at hphi
            have hs : p.2.size ≠ 0 := by
              by_cases c : (p.2.size != (if q.1.lng then Q.P.y.h.la else Q.P.y.h.lt)) = true
              · simp only [c, if_true] at hphi
                cases hphi
              · have e : p.2.size = (if q.1.lng then Q.P.y.h.la else Q.P.y.h.lt) := by
                  simpa using c
                rw [e]
                split
                · exact hla
                · exact hlt
            rw [named_whole L hD hl hh hzx hla hlt hE hpts hp hs]
            exact hphi
  unfold funsOf at hf ⊢
  rw [mapM_congr_mem laid fun q hq => by rw [key q hq]]
  exact hf

end ProofFile.Honest.K4.VT

#print axioms ProofFile.Honest.K4.VT.named_whole
#print axioms ProofFile.Honest.K4.VT.funs_honest
#print axioms ProofFile.Honest.K4.VT.ZE_else
