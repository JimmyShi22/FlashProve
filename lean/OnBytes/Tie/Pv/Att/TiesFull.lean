-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Att/TiesFull.lean: the ties of attention's two kinds of sumcheck, with what the
routines leave in the state; and the claim on an end value.

`scd_tie` (OnBytes/Tie/Pv/Att/ScdTop.lean) and `sc3_tie` (OnBytes/Tie/Pv/Att/Sc3Top.lean) say
nothing of the state that the routines leave. This file states both again, with two more clauses in
front of the premise on beta, on the same scalars, rounds and end values: how the end values were
put under their slots, and how the coefficients of the hiding polynomial were. From these, by
`Filled.world` and `Filled.masks` (OnBytes/Tie/Pv/Psc/Run/PscHide.lean, PscSeam.lean), follows what
the end values' slots are worth in the world of the state F2, and what the coefficients' slots are
worth in the world of the state that is left.

Main names:
  `scd_tie_full`, `sc3_tie_full`: the two ties, with the state F2 between the receipt of the
    messages and the making of the row, and: the end values v lie under the slots from sEnd on with
    the factor beta (`Filled` from the state before, with the slots taken, to F2); zeros lie under
    the slots of the hiding polynomial's coefficients, from the record's first slot on, with the
    factor -1 (`Filled` from F2 to the state that is left).
  `plain_end`: on the transcript that is made from what the port has heard, the typed claim on end
    value a (`PscPar.EHolds`) says: the map a at the output's point is the end value less the map's
    own mask entry times the reading of beta.
  `plain_end_slot`: so, in a world in which the slot of that end value is worth the end value less
    the reading of beta times that mask entry, the typed claim holds exactly if the map at the point
    is what the slot is worth.

Limits: those of the two files. What the row form is worth follows by `plain_row`
(OnBytes/Tie/Pv/Att/RowTie.lean), under (D1) and (D2). No world and no entries with (D1) and (D2)
are built here, and the places of the mask entries stay parameters. That a later state keeps these
slots is not said here.
-/
import OnBytes.Tie.Pv.Att.Sc3Top

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Att
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Attention
open Johnson.L5.Layers Cb.Pv.Att
open OnBytes.Psc (Weight hearMany)

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K)

theorem scd_tie_full (S : Attention.Shape) (scF : Sc3) (o : Attention.Scd) (F G : Fork) (c c' : Ctx)
    (h : keyAtIndexIn S scF F c = .ok ((o, G), c')) (hz : Sized F)
    (hsz : S.cf.lt + S.cf.lgk ≤ scF.r.size) (T : Cb.Pv.Att.Scd K (ofShape S)) (st : T.St) :
    ∃ (om4 : Array E) (c1 : Ctx) (F2 : Fork) (τ mu : E) (rs : List (List E × E)) (sentY : List E)
      (beta : E) (v : List E) (s0 : E),
      coinsOm S.NP F c = .ok ((om4, F), c1) ∧
      F.publicPart (weightedSum S.NP om4 (sc3B scF)) = some τ ∧
      Parts c1 c1 c' [] mu o.p.eps (S.scdDegrees.map fun d => Weight.plain (d + 1)) rs
        (S.cf.lt + 1) sentY beta v ∧
      v.length = S.Lam + S.NP * S.cf.lt ∧ o.r.toList = rs.map (·.2) ∧
      o.p.start = weightedSum S.NP om4 (sc3B scF) ∧ o.p.target = τ ∧ o.p.first = F.next ∧
      o.sEnd = F.next + (1 + S.scdDegrees.sum) + (S.cf.lt + 1) ∧
      o.rowU = o.p.rowForm s0 {} ∧
      PscAt o.p (plainWs (List.ofFn T.plain.deg) T.plain.DY) (rs ++ [(sentY, beta)]) mu ∧
      Filled (taken F (1 + S.scdDegrees.sum + (S.cf.lt + 1 + (S.Lam + S.NP * S.cf.lt)))) F2 o.sEnd v
        beta ∧
      Filled F2 G o.p.first (List.replicate o.p.walk.1.length zeroE) (subE zeroE oneE) ∧
      ∀ hβ : ρ.val beta ≠ 0,
        ReadsAs ρ (rs ++ [(sentY, beta)]) T.plain.our.par.fmt [pRoundV K T.plain.our.par.A]
          (plainTr ρ T.plain rs sentY beta hβ (scdVals ρ (ofShape S) v)) ∧
        (plainOut ρ T.plain st τ mu o.p.eps rs sentY beta hβ (scdVals ρ (ofShape S) v)).eps =
          ρ.val o.p.eps ∧
        (plainOut ρ T.plain st τ mu o.p.eps rs sentY beta hβ (scdVals ρ (ofShape S) v)).fin =
          ρ.val o.p.claim ∧
        (∀ i : Fin (ofShape S).k, ldPartIni (ofShape S).k (ofShape S).deg (pDummy K (S.cf.lt + 1))
          (plainOut ρ T.plain st τ mu o.p.eps rs sentY beta hβ (scdVals ρ (ofShape S) v)).pt i =
            ρ.val (o.r.getD i.1 zeroE)) ∧
        ldPartLast (ofShape S).k (ofShape S).deg (pDummy K (S.cf.lt + 1))
          (plainOut ρ T.plain st τ mu o.p.eps rs sentY beta hβ (scdVals ρ (ofShape S) v)).pt =
            ρ.val beta ∧
        (plainOut ρ T.plain st τ mu o.p.eps rs sentY beta hβ (scdVals ρ (ofShape S) v)).vals =
          scdVals ρ (ofShape S) v ∧
        ((∀ a : Fin S.cf.lt, T.ri st a = ρ.val (scF.r.getD a.1 zeroE)) →
          (∀ a : Fin S.cf.lgk, T.rg st a = ρ.val (scF.r.getD (S.cf.lt + a.1) zeroE)) →
          (∀ b : Fin (ofShape S).pairs, T.om st b = ρ.val (om4.getD b.1 zeroE)) →
          T.plain.S st
            (ldPartIni (ofShape S).k (ofShape S).deg (pDummy K (S.cf.lt + 1))
              (plainOut ρ T.plain st τ mu o.p.eps rs sentY beta hβ (scdVals ρ (ofShape S) v)).pt)
            (plainOut ρ T.plain st τ mu o.p.eps rs sentY beta hβ (scdVals ρ (ofShape S) v)).vals =
          ρ.val s0) := by
  obtain ⟨om4, F1, c1, o1, F2, c2, h1, h2, h3⟩ := keyAtIndexIn_flat S scF o F G c c' h
  have hF1 : F1 = F := ((liftY_ok (trBatch S.NP) F F1 c c1 om4).1 h1).2
  rw [hF1] at h1 h2
  obtain ⟨τ, mu, rs, sentY, beta, v, a1, a2, a3, a4, a5, a6, a7, _, _, _, a11, a12⟩ :=
    scdIn_seam _ _ _ _ o1 F F2 c1 c2 h2 hz
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := scdRow_ok o1 o _ F2 G c2 c' h3 a12.sized
  have hε : o.p.eps = o1.p.eps := by rw [b3]
  have hcl : o.p.claim = o1.p.claim := by rw [b3]
  have hdeg : List.ofFn T.plain.deg = S.scdDegrees := scd_degrees_shape S
  have hl : rs.map (·.1.length) = List.ofFn T.plain.deg := by rw [hdeg]; exact a5
  have hat := ended_pscAt a3
  have hws : plainWs (List.ofFn T.plain.deg) T.plain.DY =
      (S.scdDegrees.map fun d => Weight.plain (d + 1)) ++ [Weight.atZero (S.cf.lt + 1 + 1)] := by
    unfold plainWs
    rw [hdeg]
    rfl
  have hsh : ∀ a : (ofShape S).A,
      shownAt F2 o1.sEnd (scdNum (ofShape S) a) = v.getD (scdNum (ofShape S) a) zeroE := fun a => by
    have hlt : scdNum (ofShape S) a < v.length := by rw [a7]; exact scdNum_lt (ofShape S) a
    unfold shownAt
    rw [a12.shown _ hlt]
    rfl
  refine ⟨om4, c1, F2, τ, mu, rs, sentY, beta, v,
    keyFlat S.cf.lt S.Lam S.HA S.NP (scF.r.extract 0 S.cf.lt)
      (scF.r.extract S.cf.lt (S.cf.lt + S.cf.lgk)) (o1.r.extract 0 S.cf.lt)
      (o1.r.extract S.cf.lt (S.cf.lt + S.cf.lgk))
      (o1.r.extract (S.cf.lt + S.cf.lgk) (2 * S.cf.lt + S.cf.lgk)) om4 (shownAt F2 o1.sEnd),
    h1, a1, ?_, a7, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hε, b1]
    exact a2
  · rw [b4]
    exact a4
  · rw [b3]
    exact a3.start
  · rw [b3]
    exact a3.target
  · rw [b3]
    exact a3.first
  · rw [b5]
    exact a11
  · rw [b2, b3]
    rfl
  · rw [hws, b3]
    exact ⟨hat.vars, hat.r, hat.claim⟩
  · rw [b5]
    exact a12
  · rw [b3]
    exact b6
  · intro hβ
    refine ⟨plain_reads ρ T.plain rs sentY beta hβ _ hl a6, rfl, ?_, ?_,
      plain_last ρ T.plain st _ _ _ rs sentY beta hβ _,
      plain_vals ρ T.plain st _ _ _ rs sentY beta hβ _, ?_⟩
    · rw [plain_fin ρ T.plain st _ _ _ rs sentY beta hβ _ (scd_ok T).one hl a6, hws, hcl, a3.claim,
        hε]
    · intro i
      rw [b4, toList_getD o1.r _ a4, snd_getD]
      exact plain_ini ρ T.plain st _ _ _ rs sentY beta hβ _ i
    · intro hri hrg hom
      rw [plain_vals, scd_summand ρ S T st scF.r om4 o1.r rs _ hsz hri hrg hom a4 _
        (fun i => plain_ini ρ T.plain st _ _ _ rs sentY beta hβ _ i)]
      congr 1
      funext a
      show ρ.val _ = ρ.val _
      rw [hsh a]


theorem sc3_tie_full (T : Cb.Pv.Att.Sc3 K) (C : Aff) (W : Array E) (o1 o : Attention.Sc3)
    (F F2 G : Fork) (c c2 c' : Ctx) (h1 : sc3In T.nv T.nb C F c = .ok ((o1, F2), c2))
    (h2 : sc3Row o1 W F2 c2 = .ok ((o, G), c')) (hz : Sized F) (st : T.St) :
    ∃ (τ mu : E) (rs : List (List E × E)) (sentY : List E) (beta : E) (v : List E) (s0 : E),
      F.publicPart C = some τ ∧
      Parts c c c' [] mu o.p.eps (List.replicate T.nv (Weight.plain 4)) rs 2 sentY beta v ∧
      v.length = 2 * T.nb ∧ W.size = T.nb ∧ o.r.toList = rs.map (·.2) ∧
      o.p.start = C ∧ o.p.target = τ ∧ o.p.first = F.next ∧
      o.sEnd = F.next + (1 + 3 * T.nv) + 2 ∧
      o.rowU = o.p.rowForm s0 {} ∧
      PscAt o.p (plainWs (List.ofFn T.plain.deg) T.plain.DY) (rs ++ [(sentY, beta)]) mu ∧
      rs.map (·.1.length) = List.ofFn T.plain.deg ∧ sentY.length = T.plain.DY ∧
      Filled (taken F (1 + 3 * T.nv + (2 + 2 * T.nb))) F2 o.sEnd v beta ∧
      Filled F2 G o.p.first (List.replicate o.p.walk.1.length zeroE) (subE zeroE oneE) ∧
      ∀ hβ : ρ.val beta ≠ 0,
        ReadsAs ρ (rs ++ [(sentY, beta)]) T.plain.our.par.fmt [pRoundV K T.plain.our.par.A]
          (plainTr ρ T.plain rs sentY beta hβ (sc3Vals ρ T.nb v)) ∧
        (plainOut ρ T.plain st τ mu o.p.eps rs sentY beta hβ (sc3Vals ρ T.nb v)).eps =
          ρ.val o.p.eps ∧
        (plainOut ρ T.plain st τ mu o.p.eps rs sentY beta hβ (sc3Vals ρ T.nb v)).fin =
          ρ.val o.p.claim ∧
        (∀ i : Fin T.nv, ldPartIni T.nv (fun _ => 3) (pDummy K 2)
          (plainOut ρ T.plain st τ mu o.p.eps rs sentY beta hβ (sc3Vals ρ T.nb v)).pt i =
            ρ.val (o.r.getD i.1 zeroE)) ∧
        ldPartLast T.nv (fun _ => 3) (pDummy K 2)
          (plainOut ρ T.plain st τ mu o.p.eps rs sentY beta hβ (sc3Vals ρ T.nb v)).pt =
            ρ.val beta ∧
        (plainOut ρ T.plain st τ mu o.p.eps rs sentY beta hβ (sc3Vals ρ T.nb v)).vals =
          sc3Vals ρ T.nb v ∧
        ((∀ b : Fin T.nb, T.W st b
            (ldPartIni T.nv (fun _ => 3) (pDummy K 2)
              (plainOut ρ T.plain st τ mu o.p.eps rs sentY beta hβ (sc3Vals ρ T.nb v)).pt) =
            ρ.val (W.getD b.1 zeroE)) →
          T.plain.S st
            (ldPartIni T.nv (fun _ => 3) (pDummy K 2)
              (plainOut ρ T.plain st τ mu o.p.eps rs sentY beta hβ (sc3Vals ρ T.nb v)).pt)
            (plainOut ρ T.plain st τ mu o.p.eps rs sentY beta hβ (sc3Vals ρ T.nb v)).vals =
          ρ.val s0) := by
  obtain ⟨τ, mu, rs, sentY, beta, v, a1, a2, a3, a4, a5, a6, a7, _, a9, a11, a12⟩ :=
    sc3In_seam _ _ _ o1 F F2 c c2 h1 hz
  obtain ⟨b1, b0, b2, b3, b4, b5, _, b6⟩ := sc3Row_ok o1 o W F2 G c2 c' h2 a12.sized
  have hε : o.p.eps = o1.p.eps := by rw [b3]
  have hcl : o.p.claim = o1.p.claim := by rw [b3]
  have hdeg : List.ofFn T.plain.deg = List.replicate T.nv 3 := List.ofFn_const _ _
  have hl : rs.map (·.1.length) = List.ofFn T.plain.deg := by rw [hdeg]; exact a5
  have hat := ended_pscAt a3
  have hws : plainWs (List.ofFn T.plain.deg) T.plain.DY =
      List.replicate T.nv (Weight.plain 4) ++ [Weight.atZero (2 + 1)] := by
    unfold plainWs
    rw [hdeg, List.map_replicate]
    rfl
  have hsh : ∀ j, j < 2 * T.nb → shownAt F2 o1.sEnd j = v.getD j zeroE := fun j hj => by
    unfold shownAt
    rw [a12.shown _ (by rw [a7]; exact hj)]
    rfl
  refine ⟨τ, mu, rs, sentY, beta, v, sc3Flat W (shownAt F2 o1.sEnd) o1.nb 0 zeroE, a1, ?_, a7,
    by rw [b0, a9], ?_, ?_, ?_, ?_, ?_, ?_, ?_, hl, a6, ?_, ?_, ?_⟩
  · rw [hε, b1]
    exact a2
  · rw [b4]
    exact a4
  · rw [b3]
    exact a3.start
  · rw [b3]
    exact a3.target
  · rw [b3]
    exact a3.first
  · rw [b5]
    exact a11
  · rw [b2, b3]
    rfl
  · rw [hws, b3]
    exact ⟨hat.vars, hat.r, hat.claim⟩
  · rw [b5]
    exact a12
  · rw [b3]
    exact b6
  · intro hβ
    refine ⟨plain_reads ρ T.plain rs sentY beta hβ _ hl a6, rfl, ?_, ?_,
      plain_last ρ T.plain st _ _ _ rs sentY beta hβ _,
      plain_vals ρ T.plain st _ _ _ rs sentY beta hβ _, ?_⟩
    · rw [plain_fin ρ T.plain st _ _ _ rs sentY beta hβ _ (sc3_ok T).one hl a6, hws, hcl, a3.claim,
        hε]
    · intro i
      rw [b4, toList_getD o1.r _ a4, snd_getD]
      exact plain_ini ρ T.plain st _ _ _ rs sentY beta hβ _ i
    · intro hW
      rw [plain_vals, a9, sc3Flat_read]
      show ∑ b : Fin T.nb, T.W st b _ * sc3Vals ρ T.nb v (b, false) * sc3Vals ρ T.nb v (b, true) = _
      refine Finset.sum_congr rfl fun b _ => ?_
      have hb := b.2
      rw [hW b, hsh (2 * b.1) (by omega), hsh (2 * b.1 + 1) (by omega)]
      rfl


section Ends
variable (T : PlainSc K) (st : T.St) (target mu eps : E) (rs : List (List E × E)) (sentY : List E)
  (beta : E) (hβ : ρ.val beta ≠ 0) (vals : T.A → K)

theorem plain_end (m : T.J → K) (a : T.A) :
    T.our.par.EHolds (plainOut ρ T st target mu eps rs sentY beta hβ vals) m a ↔
      T.map st m a (ldPartIni T.nv T.deg (pDummy K T.DY)
          (plainOut ρ T st target mu eps rs sentY beta hβ vals).pt) =
        vals a - m (T.cAt a) * ρ.val beta := by
  rw [psc_our_val K T.our (plainOut ρ T st target mu eps rs sentY beta hβ vals) m a]
  have h1 := ldPartVars_ini K T.nv T.deg T.dat (pDummy K T.DY) (pDummyD K T.DY)
    (plainOut ρ T st target mu eps rs sentY beta hβ vals).pt
  have h2 := ldPartVars_last K T.nv T.deg T.dat (pDummy K T.DY) (pDummyD K T.DY)
    (plainOut ρ T st target mu eps rs sentY beta hβ vals).pt
  have h3 := plain_last ρ T st target mu eps rs sentY beta hβ vals
  have h4 := plain_vals ρ T st target mu eps rs sentY beta hβ vals
  refine (Iff.of_eq (congrArg₂
    (fun p q => T.map st m a p + m (T.cAt a) * q =
      (plainOut ρ T st target mu eps rs sentY beta hβ vals).vals a) h1 (h2.trans h3))).trans ?_
  rw [h4]
  exact eq_sub_iff_add_eq.symm

theorem plain_end_slot (m : T.J → K) (a : T.A) (w : K)
    (hw : w = vals a - ρ.val beta * m (T.cAt a)) :
    T.our.par.EHolds (plainOut ρ T st target mu eps rs sentY beta hβ vals) m a ↔
      T.map st m a (ldPartIni T.nv T.deg (pDummy K T.DY)
          (plainOut ρ T st target mu eps rs sentY beta hβ vals).pt) = w := by
  rw [plain_end, hw, mul_comm]

end Ends

end OnBytes.Tie.Pv.Att

#print axioms OnBytes.Tie.Pv.Att.scd_tie_full
#print axioms OnBytes.Tie.Pv.Att.sc3_tie_full
#print axioms OnBytes.Tie.Pv.Att.plain_end
#print axioms OnBytes.Tie.Pv.Att.plain_end_slot
