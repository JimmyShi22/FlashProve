-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HeadPlanesNu.lean: THE LOOKUP'S PLACES AT THE OUTPUT HEAD (the entries of the
mask row; the cells of the planes' matrix), READ OFF THE DATA OF THE RUNS' FORMS: one term; and that
it is the reading of the same places by the caller of the proved lookup sub-protocol off the witness
(Johnson/Desc/First/Look/K3HeadGoodIn.lean: headNu).

Why. The stated reads of the planes (Law/K6StatedPlanes.lean: statedAll) take a
letter nu: the lookup's places off the verifier's state and the data. The table's item "worth 24 3
planes" speaks at headNu ... w. Law/StatedHeadArm.lean names nu (nuK6); this file ties the two.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law).
  (nuK6 itself: Law/StatedHeadArm.lean.)
  colsB Wp: the planes' matrix's columns.
  Came.nu_cell_meets: the cells: nuK6 at the data dataQ own aK (seatTab ... w) is headNu ... w.
  Came.nu_mask_meets: the mask entries.

Every letter under "there is": none.
What it does not say. The premises: the test laidThere; at the planes' matrix: one tenant
bears its message's number (pB), MatsSeated (five facts on the verifier's state) and CallsSeated
(eight on public letters); at the mask row: the like facts of both readers: NONE IS SHOWN HERE.
Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.HeadCellsAtCaller
import Johnson.Desc.Kinds.Law.DataSeatedOfLaid
import Johnson.Desc.Kinds.Law.StatedHeadArm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes OnBytes.Params
open OnBytes.Model.Verify (borderOf)
open VerifiableInference.OnPublicFiles (layMs headNu)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.First.Look (Sent sigListCalls matsOfE msgLay)
open VerifiableInference.Desc.Sound (Mem MsgT namedOnce)
open VerifiableInference.Desc.K9L (Bound)

/-- The planes' matrix's columns. -/
def colsB (Wp : OnBytes.Model.Verify.Public) : Nat → Nat → Prop := fun a _ => a = Wp.hS.NHf + 2

namespace Came

/-- **The cells of the planes' matrix.** -/
theorem nu_cell_meets {rows cols : Nat} {Tok : Type} (cs : OnBytes.Codes) (arr : Nat → Nat → Nat)
    (msR : List Mem) (N : Numbers) (Wp : OnBytes.Model.Verify.Public) (lay : ReqLayout)
    (num : Nat → Nat → Nat) (x : First.Look.Place) (D : Sent) (rad : OracleShape → Nat)
    (oW : Cb.OMsg Cb.Gl.E) (wOf : oW.Msg → Nat → Nat → Cb.Gl.E) (nr nc : Nat)
    (seatT : Fin (sigListCalls D rad x.link).length → Nat × Nat)
    (msgW : Wit (Fin rows → Fin cols → GE) Tok MsgT → oW.Msg)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (own : List (Nat × Nat)) (aK : K9.Part) (s : S)
    (T : Meaning.laidThere Wp (Meaning.sizesOf Wp) lay = true) (hlay : D.layout = lay)
    (hcs : D.codes = cs) (hlayA : aK.L.check.rows.layout = lay)
    (pB : ∀ (μ : Fin (Meaning.sizesOf Wp 24).NM) (r c : Nat),
      r < Alg.symRows ((Meaning.sizesOf Wp 24).m μ) → c < (Meaning.sizesOf Wp 24).k μ →
      colsB Wp μ.val c → namedOnce arr N 24 (seatLay Wp lay num 24 μ r c).1 = true)
    (hC : CallsSeated (colsB Wp) arr msR N Wp lay num D rad x.link seatT)
    (hM : MatsSeated (colsB Wp) arr N Wp own aK num lay) (r c : Nat) :
    nuK6 Wp s (Sound.dataQ own aK (Sound.seatTab cs arr msR w)) (.cell r c) =
      headNu (adrOf Wp.hS Wp.HLy (borderOf Wp.y)) x Wp.H.tl D rad oW wOf nr nc seatT arr msgW w
        (.cell r c) := by
  have e := tlAt_head Wp
  rw [← e]
  show ((Meaning.ownOf (Meaning.sizesOf Wp) (symD Wp (Meaning.sizesOf Wp)
      (Sound.dataQ own aK (Sound.seatTab cs arr msR w))) 24 (Wp.hS.NHf + 2) r c : Int) : Cb.Gl.E) =
    matsOfE (msgLay x (Meaning.tlAt Wp 24) D rad oW wOf nr nc (layMs x D rad oW seatT arr msgW w))
      (Wp.hS.NHf + 2) r c
  unfold matsOfE First.Look.lyCell First.Look.cellJ Meaning.ownOf OnBytes.Road.Rows.Norms.mzTot
  by_cases h1 : Wp.hS.NHf + 2 < (Meaning.sizesOf Wp 24).NM
  · by_cases h2 : c < (Meaning.sizesOf Wp 24).k (Wp.hS.NHf + 2)
    · by_cases h3 : r < (Meaning.sizesOf Wp 24).m (Wp.hS.NHf + 2)
      · rw [dif_pos h1, dif_pos h2, dif_pos h3, dif_pos ⟨h1, h2, h3⟩]
        refine congrArg (fun z : Int => (z : Cb.Gl.E)) (congrFun (Cb.Pv.Tail.cellsOf_congr
          (Λ := Cb.Pv.Tail.symL Cb.Gl.E (Meaning.sizesOf Wp 24))
          (msg := symD Wp (Meaning.sizesOf Wp) (Sound.dataQ own aK (Sound.seatTab cs arr msR w)) 24)
          (msg' := First.Look.symAt D.codes (sigListCalls D rad x.link)
            (First.Look.seatCalls D x.link) (Meaning.tlAt Wp 24)
            (First.Look.ownPart (layMs x D rad oW seatT arr msgW w)))
          (μ := ⟨Wp.hS.NHf + 2, h1⟩) (c := ⟨c, h2⟩) fun i' => ?_) ⟨r, h3⟩)
        have hs := syms_meet (colsB Wp) cs arr msR N Wp lay num D rad x.link seatT w T hlay hcs pB
            hC
          ⟨Wp.hS.NHf + 2, h1⟩ ⟨c, h2⟩ rfl i'
        obtain ⟨A, rp, hA, _, _, hl, _⟩ := Meaning.seat_of_laidThere T num (k := 24) (by decide)
          (⟨Wp.hS.NHf + 2, h1⟩ : Fin (Meaning.sizesOf Wp 24).NM) i'.isLt h2
        obtain ⟨o, xt, m3, m4, m5, m6, m7⟩ := hM ⟨Wp.hS.NHf + 2, h1⟩ c h2 rfl A hA
        have h8 := pB ⟨Wp.hS.NHf + 2, h1⟩ i'.val c i'.isLt h2 rfl
        subst hlayA
        have hd := sym_of_data cs arr msR N own aK w num (Meaning.labAt Wp 24 (Wp.hS.NHf + 2))
            i'.val
          c A rp o xt hA hl m3 m4 m5 m6 m7 (by
            have e8 : (seatLay Wp aK.L.check.rows.layout num 24 ⟨Wp.hS.NHf + 2, h1⟩ i'.val c).1 =
                num (Meaning.ownerK (Meaning.labAt Wp 24 (Wp.hS.NHf + 2))) A.message := by
              obtain ⟨A', rp', hA', _, _, _, hs'⟩ := Meaning.seat_of_laidThere T num (k := 24)
                (by decide) (⟨Wp.hS.NHf + 2, h1⟩ : Fin (Meaning.sizesOf Wp 24).NM) i'.isLt h2
              have eA : A' = A := Option.some.inj (hA'.symm.trans hA)
              subst eA
              show (Meaning.seatBy (Meaning.fLay aK.L.check.rows.layout num) Wp (Meaning.sizesOf Wp)
                24 ⟨Wp.hS.NHf + 2, h1⟩ i'.val c).1 = _
              rw [hs']
            rw [e8] at h8
            exact h8)
        exact hd.symm.trans hs.symm
      · rw [dif_pos h1, dif_pos h2, dif_neg h3, dif_neg (fun h => h3 h.2.2)]
        simp [First.Look.msgLay]
    · rw [dif_pos h1, dif_neg h2, dif_neg (fun h => h2 h.2.1)]
      simp [First.Look.msgLay]
  · rw [dif_neg h1, dif_neg (fun h => h1 h.1)]
    simp [First.Look.msgLay]

/-- **The entries of the mask row.** -/
theorem nu_mask_meets {rows cols : Nat} {Tok : Type} (cs : OnBytes.Codes) (arr : Nat → Nat → Nat)
    (msR : List Mem) (N : Numbers) (sz : Nat → Cb.Pv.Tail.Size)
    (seat : ∀ k, Fin (sz k).NM → Nat → Nat → Nat × Nat × Nat) (Wp : OnBytes.Model.Verify.Public)
    (n : Nat) (adr : HeadAdr) (x : First.Look.Place) (tl : OnBytes.Model.HTailF2) (D : Sent)
    (rad : OracleShape → Nat) (oW : Cb.OMsg Cb.Gl.E) (wOf : oW.Msg → Nat → Nat → Cb.Gl.E)
    (nr nc : Nat) (seatT : Fin (sigListCalls D rad x.link).length → Nat × Nat)
    (msgW : Wit (Fin rows → Fin cols → GE) Tok MsgT → oW.Msg)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (own : List (Nat × Nat)) (aK : K9.Part) (s : S)
    (o : Nat) (xo : Nat × Nat) (ho : K9L.maskOracle aK.L.check.frame = some o)
    (hx : K9.seatAt own aK.d.book o = some xo) (hgo : xo ∈ N.group 24) (hno : arr xo.1 xo.2 = n)
    (hrb : aK.d.st.rowBits o .mask = 0)
    (hmeets : ∀ j, rd ((compCut cs arr msR N sz seat Wp (plAt n 0) w).2 j) =
      headNu adr x tl D rad oW wOf nr nc seatT arr msgW w (.mask j))
    (g1 : namedOnce arr N 24 n = true) (j : Nat) :
    nuK6 Wp s (Sound.dataQ own aK (Sound.seatTab cs arr msR w)) (.mask j) =
      headNu adr x tl D rad oW wOf nr nc seatT arr msgW w (.mask j) := by
  rw [← hmeets j]
  show (if j < Wp.H.ns then (Sound.dataQ own aK (Sound.seatTab cs arr msR w)).mask j else 0) = _
  by_cases hj : j < Wp.H.ns
  · rw [if_pos hj, mask_of_data cs arr msR N sz seat Wp own aK w o n xo ho hx hgo hno g1 j hj, hrb]
  · rw [if_neg hj]
    have e2 : (compCut cs arr msR N sz seat Wp (plAt n 0) w).2 =
        maskQ cs arr msR N 24 Wp.H.ns (plAt n 0) w := rfl
    rw [e2]
    unfold maskQ
    rw [if_neg hj]
    exact OnBytes.Slice.readE_zero.symm

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.nu_cell_meets
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.nu_mask_meets
