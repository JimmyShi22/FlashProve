-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05GuestHid.lean: an attention segment's identity at3 and its key forms where
the three free linear claims of the own rounds are the library's own (LMat, LDat, LEat in
Cb/Pv/Att/End/Hid.lean): what the first joint says there, and the lookup's out-claim on the keys,
drawn at the joint between the lookup and the own rounds.

Definitions, statements and proofs. No protocol of its own. It stands on `att_seam`, `hid_rule`,
`KF_congr` (Cb/Pv/Att/End/Seam.lean), `att_seam_keys` (Cb/Pv/Att/End/SeamKeys.lean) and
`ruleFill_rule` (Cb/Pv/Att/End/ClFill.lean).
Main names:
  `HidLet P Q`: the three letters of P are LMat, LDat and LEat at the join's letters Q: the three
    equivalences that `att_seam` asks.
  `zcRead_hid`: `HidLet` gives `ZCRead` (Johnson/Desc/First/Att/K05Guest.lean), the premise of
    `guest_link` (Johnson/Desc/First/Att/K05GuestLink.lean).
  `fillM`, `fillD`, `fillE`, `ruleAt_update`: further scalars whose hidden values are the rule
    values: `ruleFill`, with the four scalars that have no name (ss M, ss D, zo, acc) laid at their
    sums.
  `todo_iff_hid`: at these letters and two plane messages, Todo holds exactly if `denOut` = 0, the
    identities at2 and at1 vanish on their cubes, and the join holds at the rule values. The
    direction from Todo is `att_seam` with the two families of `ownAt_todo`.
  `forRest c`, `KeysHold c x m`, `forOut_split`: the lookup's out-joint `forOut` is `forRest` (what
    rides through the lookup, the lookup's rows, and `more`) and its claim on the keys.
  `JoinGives c P Q tb`: the premise on the caller's L and the join's letters: where the join holds
    at the four extensions of `keyVec` of the cells, the lookup's out-claim on the keys holds.
  `keys_mid`: the lookup alone, from (`forIn` and `Three`) to (`forRest`, Dn and Todo).
  `keys_link`: the lookup, then the own rounds, from (`forIn` and `Three`) to (`forRest` at the
    first statement inside the last, and the chain's `Last`), at the errors of `guest_link`.
Premises of `keys_link`: `FoNums.ok c.h`; `AttFits`; P.zOf is the lookup's pt; P.D.lT ≤ 2 ^ P.kap;
two plane messages; `HidLet`; `JoinGives`; the three premises of `kfExt`, at the scales of Q (the
same for `KF` and `keyVec`).
`stepIn_ok_own` (Johnson/Top/H/LinkAttAtEnd.lean) takes the whole tie between Todo
and the lookup's claim at its end as one premise (hOut); `keys_mid` draws the first of that claim's
three clauses from `att_seam_keys` under `JoinGives`, and leaves the other two in the base joint.
Used beside these: typed reductions and joints and theorems on them; no routine in a
context: `forOut`, `forA`, `cj`, `ShiftQ.ride`, `RowsHold`, `zext`, `joinVal`, `hidV`, `RuleAt`,
`ownAt_todo`, `denOut_split`, `knowAt_mono`, `knowAt_seq`, `ownAt_knowAt`, `guest_mid`.
Limits: those of Johnson/Desc/First/Att/K05GuestLink.lean. Q and tb are free letters. `JoinGives` is
shown for no caller. `forIn` says "each call's keys lie in that call's table" of the caller's own
keys: that these are `keyVec` of the cells is not shown in this file or in what it imports.
`todo_iff_hid` says what Todo is: that its four clauses hold together at some statement and message
is not shown here. Which scalar is which in LMat, LDat and LEat follows a reading of the verifier on
bytes (the limit of Cb/Pv/Att/End/Hid.lean). Nothing on an honest prover or on hiding.

-/
import Cb.Pv.Att.End.SeamKeys
import Cb.Pv.Att.End.ClFill
import Johnson.Desc.First.Att.K05GuestLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.Rider Cb.LdLkp Cb.LdLkp.Kn Cb.Pv.Att Cb.Pv.Att.End Inst.Model
  Inst.Model.AttSeg
open VerifiableInference.OnPublicFiles (LookupCCaller)

section Letters
variable {K M X : Type} [Field K] [Fintype K] (P : OwnPar K M X) (Q : JoinLay P)

/-- The three free linear claims of P are the library's, at the join's letters Q. -/
structure HidLet : Prop where
  lm : ∀ x r m, P.LM x r m ↔ LMat P x r m
  ld : ∀ x r m, P.LD x r m ↔ LDat P x r m
  le : ∀ x r m, P.LE x r m ↔ LEat P Q x r m

variable {P Q}

/-- **At the library's letters ZCRead is a lemma.** -/
theorem zcRead_hid (H : HidLet P Q) : ZCRead P := fun s r m h =>
  ((H.le s r m).1 h).1 P.iZC .zc (by simp [nameE, OwnPar.iZC])

variable (P)

/-- Further scalars of the unit below the diagonal whose hidden values are the rule values; the
score at its sum. -/
noncomputable def fillM (x : X) (m : M) : Fin (3 * P.npl + 7) → K :=
  Function.update (ruleFill P.D P.C nameM P.kM (P.pub0 (x, [])) (P.tOf m) (P.msg m)) (Fin.last _)
    (sumPhi P.D P.C (P.pub0 (x, [])) (P.tOf m) .s6b + P.msg m (P.kM (Fin.last _)))

/-- The same for the unit on the diagonal. (pub0 reads the first statement alone: so (x, []) serves
at all three.) -/
noncomputable def fillD (x : X) (m : M) : Fin 7 → K :=
  Function.update (ruleFill P.D P.C nameD P.kD (P.pub0 (x, [])) (P.tOf m) (P.msg m)) (Fin.last _)
    (sumPhi P.D P.C (P.pub0 (x, [])) (P.tOf m) .s6d + P.msg m (P.kD (Fin.last _)))

/-- The same for the denominator times the output: ZO at its sum, ACC at its rule value. -/
noncomputable def fillE (x : X) (m : M) : Fin (5 + P.D.lT + 2) → K :=
  Function.update (Function.update (ruleFill P.D P.C (nameE P.D) P.kE (P.pub0 (x, [])) (P.tOf m) (P.msg m))
    P.iZO (sumPhi P.D P.C (P.pub0 (x, [])) (P.tOf m) .s8 + P.msg m (P.kE P.iZO)))
    P.iACC (rv P.D P.C (pubOfZ K (P.zOf x)) (P.tOf m) .acc + P.msg m (P.kE P.iACC))

omit [Fintype K] in
/-- A linear claim does not see a scalar that has no name. -/
theorem ruleAt_update {J : Type} (D : Dim) (C : Calls) (name : ℕ → Option KSc) {n : ℕ} (r : Fin n → K)
    (kk : Fin n → J) (p : Pub K) (t : Raw → K) (μ : J → K) (j0 : Fin n) (a : K) (h0 : name j0.val = none)
    (h : RuleAt D C name r kk p t μ) : RuleAt D C name (Function.update r j0 a) kk p t μ := by
  intro j k hk
  have hne : j ≠ j0 := fun e => by rw [e, h0] at hk; cases hk
  rw [Function.update_of_ne hne]
  exact h j k hk

variable {P}

/-- **What the first joint says at the library's letters, exactly.** -/
theorem todo_iff_hid (H : HidLet P Q) (hn : P.npl = 2) (hK : P.D.lT ≤ 2 ^ P.kap) (x : X) (m : M) :
    (P.own (theMeans K P.D P.C P.kap)).ch.Todo x m ↔
      denOut P.D P.C (P.zOf x) (P.tOf m) = 0 ∧
      (∀ i : Fin P.D.nb, ∀ Y < 2 ^ P.g1, scoreIdnG P.D (P.tOf m) i Y = 0) ∧
      (∀ i : Fin P.D.nb, ∀ Y < 2 ^ P.g2, bitIdnT P.D (P.tOf m) i Y = 0) ∧
      joinVal (Q.q x) (KF (scl := Q.scl) P.D P.C (pubOfZ K (P.zOf x))
        (rv P.D P.C (pubOfZ K (P.zOf x)) (P.tOf m))) ((Q.ce x).val (P.msg m)) = 0 := by
  constructor
  · intro h
    obtain ⟨_, hj, hd⟩ := att_seam Q hn hK H.lm H.ld H.le x m h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h1, h2⟩ := (ownAt_todo P x m).1 h
    exact ⟨hd, h1, h2, hj⟩
  · rintro ⟨h0, h1, h2, hj⟩
    have nACC : P.iACC ≠ P.iZO := fun e => by
      have := congrArg Fin.val e
      simp [OwnPar.iACC, OwnPar.iZO] at this
    have aM : LMat P (x, []) (fillM P x m) m :=
      ruleAt_update _ _ _ _ _ _ _ _ _ _ (by simp [Fin.val_last, hn, nameM, nameU]) (ruleFill_rule _ _ _ _ _ _ _)
    have aD : LDat P (x, [List.ofFn (fillM P x m)]) (fillD P x m) m :=
      ruleAt_update _ _ _ _ _ _ _ _ _ _ (by simp [nameD, nameU]) (ruleFill_rule _ _ _ _ _ _ _)
    have aE : RuleAt P.D P.C (nameE P.D) (fillE P x m) P.kE
        (P.pub0 (x, [List.ofFn (fillM P x m), List.ofFn (fillD P x m)])) (P.tOf m) (P.msg m) :=
      ruleAt_update _ _ _ _ _ _ _ _ _ _ (by simp [nameE, OwnPar.iACC])
        (ruleAt_update _ _ _ _ _ _ _ _ _ _ (by simp [nameE, OwnPar.iZO]) (ruleFill_rule _ _ _ _ _ _ _))
    have sM : sumPhi P.D P.C (P.pub0 (x, [])) (P.tOf m) .s6b =
        fillM P x m (Fin.last _) - P.msg m (P.kM (Fin.last _)) := by
      unfold fillM
      rw [Function.update_self]
      exact (add_sub_cancel_right _ _).symm
    have sD : sumPhi P.D P.C (P.pub0 (x, [List.ofFn (fillM P x m)])) (P.tOf m) .s6d =
        fillD P x m (Fin.last _) - P.msg m (P.kD (Fin.last _)) := by
      unfold fillD
      rw [Function.update_self]
      exact (add_sub_cancel_right _ _).symm
    have sE : sumPhi P.D P.C (P.pub0 (x, [List.ofFn (fillM P x m), List.ofFn (fillD P x m)])) (P.tOf m) .s8 =
        fillE P x m P.iZO - P.msg m (P.kE P.iZO) := by
      unfold fillE
      rw [Function.update_of_ne nACC.symm, Function.update_self]
      exact (add_sub_cancel_right _ _).symm
    have sA : rv P.D P.C (pubOfZ K (P.zOf x)) (P.tOf m) .acc =
        fillE P x m P.iACC - P.msg m (P.kE P.iACC) := by
      unfold fillE
      rw [Function.update_self]
      exact (add_sub_cancel_right _ _).symm
    have hr := hid_rule hn x m _ _ _ aM aD aE sM sD sE sA
    have e : KF (scl := Q.scl) P.D P.C (pubOfZ K (P.zOf x)) (rv P.D P.C (pubOfZ K (P.zOf x)) (P.tOf m)) =
        KF (scl := Q.scl) P.D P.C (P.pub0 (x, [List.ofFn (fillM P x m), List.ofFn (fillD P x m)]))
          (hidV P (x, [List.ofFn (fillM P x m), List.ofFn (fillD P x m)]) (fillE P x m) m) :=
      funext fun q => (KF_congr (scl := Q.scl) P.D P.C _ hr q).symm
    rw [e] at hj
    rw [ownAt_todo]
    refine ⟨_, (H.lm _ _ _).2 aM, sM, (out_nonempty _ (P.uM.cl (x, []) fun _ => 0).2).some, _,
      (H.ld _ _ _).2 aD, sD, (out_nonempty _ (P.uD.cl (x, []) fun _ => 0).2).some, _,
      (H.le _ _ _).2 ⟨aE, hj⟩, sE, (out_nonempty _ (P.sE.cl (x, []) fun _ => 0).2).some, ⟨sA, ?_⟩, h1, h2⟩
    rw [aE P.iZC .zc (by simp [nameE, OwnPar.iZC])]
    rw [denOut_split, sub_eq_zero] at h0
    exact h0.symm

end Letters

section KeysLink
variable (c : LookupCCaller)
  (P : OwnPar Cb.Gl.E c.Sg.Msg (TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀)))

/-- The lookup's out-joint less its claim on the keys. -/
def forRest : Rels c.Kc (TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀)) c.Ex (c.Sg.Msg × c.Wp) :=
  cj (ShiftQ.ride c.R0) (fun m => zext (c.msg₀ m)) Prod.fst
    (fun x μ => RowsHold x.2.2 μ ∧ (forA Cb.Gl.E c.h c.L).lk.more x.1 μ)
    (fun x μ => RowsHold x.2.2 μ ∧ (forA Cb.Gl.E c.h c.L).lk.more x.1 μ)

/-- The lookup's out-claim on the keys. -/
def KeysHold (x : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀)) (m : c.Sg.Msg) : Prop :=
  x.2.1.Holds (forA Cb.Gl.E c.h c.L).lk.v ((forA Cb.Gl.E c.h c.L).lk.key x.1 (zext (c.msg₀ m)))
    (zext (c.msg₀ m))

theorem forOut_split (a : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) × c.Ex.Str) (w : c.Sg.Msg × c.Wp) :
    (forOut Cb.Gl.E c.h c.L c.R0 c.msg₀).relR a w ↔ (forRest c).relR a w ∧ KeysHold c a.1 w.1 :=
  ⟨fun h => ⟨⟨h.1, h.2.2.1, h.2.2.2⟩, h.2.1⟩, fun h => ⟨h.1.1, h.2, h.1.2.1, h.1.2.2⟩⟩

variable (Q : JoinLay P) (tb : Tables)

/-- **The one named premise on the caller's L and the join's letters**: the join at the calls'
vectors of looked-up values gives the lookup's out-claim on the keys. -/
def JoinGives : Prop :=
  ∀ (x : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀)) (m : c.Sg.Msg),
    joinVal (Q.q x) (fun q => Blocks.ext (P.C.a q) (keyVec (scl := Q.scl) P.D tb (P.tOf m) q)
      (P.C.zC q (P.zOf x))) ((Q.ce x).val (P.msg m)) = 0 → KeysHold c x m

/-- **The lookup alone, with its out-claim on the keys drawn from the first joint of the own
rounds.** -/
theorem keys_mid (ok : FoNums.ok c.h = true) (F : AttFits c.h P.D P.C) (hz : ∀ b, P.zOf b = b.2.1.pt)
    (hk : P.D.lT ≤ 2 ^ P.kap) (hn : P.npl = 2) (H : HidLet P Q) (hJ : JoinGives c P Q tb)
    (hC : Calls.OK (scl := Q.scl) P.C P.D) (hdeep : ∀ u : AttSeg.Fam, u.l P.D ≤ P.C.Dk)
    (hs : P.C.a 0 = P.C.a 1) (Dn : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) → c.Sg.Msg → Prop) :
    KnowAt (forB Cb.Gl.E c.h c.L V₀ V₀C (Ex := c.Ex)).R
      (withRider (forIn Cb.Gl.E c.h c.L c.R0 c.msg₀) fun m _ => Three P m)
      (jt (forRest c) id fun x m => Dn x m ∧ (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).ch.Todo x m)
      (fun _ _ _ wp => wp) (forB Cb.Gl.E c.h c.L V₀ V₀C (Ex := c.Ex)).e :=
  knowAt_mono (guest_mid c P ok F hz (zcRead_hid H) hk Dn) (fun _ h => h) (fun _ _ _ h => h)
    (fun b w _ h => ⟨(forOut_split c _ w).2 ⟨h.1, hJ b.1 w.1
      (att_seam_keys Q tb hn hk hC hdeep hs H.lm H.ld H.le b.1 w.1 h.2.2).2.1⟩, h.2⟩) (fun _ h => h)

/-- **The lookup, then the own rounds: the base that rides is the lookup's out-joint less its claim
on the keys.** -/
theorem keys_link (ok : FoNums.ok c.h = true) (F : AttFits c.h P.D P.C) (hz : ∀ b, P.zOf b = b.2.1.pt)
    (hk : P.D.lT ≤ 2 ^ P.kap) (hn : P.npl = 2) (H : HidLet P Q) (hJ : JoinGives c P Q tb)
    (hC : Calls.OK (scl := Q.scl) P.C P.D) (hdeep : ∀ u : AttSeg.Fam, u.l P.D ≤ P.C.Dk)
    (hs : P.C.a 0 = P.C.a 1) (Dn : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) → c.Sg.Msg → Prop) :
    KnowAt ((forB Cb.Gl.E c.h c.L V₀ V₀C (Ex := c.Ex)).R.seq
        ((P.own (theMeans Cb.Gl.E P.D P.C P.kap)).ch.R c.Ex))
      (withRider (forIn Cb.Gl.E c.h c.L c.R0 c.msg₀) fun m _ => Three P m)
      (jt (forRest c) (fun e => id ((P.own (theMeans Cb.Gl.E P.D P.C P.kap)).ch.back e))
        ((P.own (theMeans Cb.Gl.E P.D P.C P.kap)).ch.Last Dn))
      (fun _ _ _ wp => wp)
      (Err.app (forB Cb.Gl.E c.h c.L V₀ V₀C (Ex := c.Ex)).e
        ((P.own (theMeans Cb.Gl.E P.D P.C P.kap)).ch.eps c.Ex)) :=
  knowAt_seq (keys_mid c P Q tb ok F hz hk hn H hJ hC hdeep hs Dn) (ownAt_knowAt P c.Ex (forRest c) id Dn)

end KeysLink

end VerifiableInference.Desc.First.Att.P
