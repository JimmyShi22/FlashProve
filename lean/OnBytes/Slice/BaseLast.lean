-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BaseLast.lean: the last case of the program's proximity test, from the claim on the
last group to the library's decision.

The program (the Lean verifier in OnBytes/) holds the claim after the last code switch as a row on a
group (`GroupRow`). A group of the program has at least one row variable, even a group of one main
row: its second row is a row of zeros that nobody sent. So entry (row 0, place j) of the main table
has the index 2 j. The last case of `ioppStagesVerify` (OnBytes/Iop/Prox.lean) fixes that variable
at 0 (`ioppLastRows`), which picks the first row, and runs the base case on the single rows. The
stage of OnBytes/Slice/Stage.lean has no row variable there. This file is the joint between the two.

Main definitions: `FixLaw` (what is asked of the program's fixing of a form's low variables).
Main theorems.
 `fix_zero`          under `FixLaw`, a form with its lowest variable fixed at 0 has the entries of
                     even index.
 `ioppLastRows_inv`  what the single rows of the last stage are.
 `ioppLast_frame`    if no named test has failed after the last case, none had failed before it; the
                     case takes the two rounds alone.
 `ioppLast_sem`      if the last case runs through and no named test fails, the library's decision
                     holds at the values of the two written rounds, for a claim that reads the
                     program's row at the indices 2 j.
A named test (`Blk.check`) does not stop the run; the first that fails is noted in the context's
field `failed`.
Not claimed. That `FixLaw` and the named hypotheses of OnBytes/Slice/BaseYields.lean hold.
-/
import OnBytes.Slice.BaseYields
import OnBytes.Slice.BlkTop

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb _root_.Run
open Params (IoppStage)

/-- What is asked of the program's fixing of low variables: entry p of the form f with its low
variables fixed at g is the sum, over the numbers b of the rows, of the weight of b at g times the
entry (b, p) of f. -/
def FixLaw (f : Form) (g : List E) : Prop :=
  ∀ p, readE ((f.fixLow g).entry p) =
    (∑ b ∈ Finset.range (2 ^ g.length),
      eqW g.length (readL g) b * readE (f.entry (b + 2 ^ g.length * p))) * readE oneE

/-- Under `FixLaw`, a form with its lowest variable fixed at 0 has the entries of even index. -/
theorem fix_zero (f : Form) (h : FixLaw f [zeroE]) (p : ℕ) :
    readE ((f.fixLow [zeroE]).entry p) = readE (f.entry (2 * p)) := by
  have z0 : readL [zeroE] 0 = 0 := readE_zero
  have w0 : eqW 1 (readL [zeroE]) 0 = 1 := by
    rw [eqW_succ, eqW_zero, z0]
    simp
  have w1 : eqW 1 (readL [zeroE]) 1 = 0 := by
    rw [eqW_succ, eqW_zero, z0]
    simp
  rw [h p]
  show (∑ b ∈ Finset.range 2, eqW 1 (readL [zeroE]) b * readE (f.entry (b + 2 * p))) *
    readE oneE = _
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, w0, w1,
    readE_one, zero_add, zero_mul, add_zero, one_mul, mul_one, Nat.zero_add]

/-- What the single rows of the last stage are. -/
theorem ioppLastRows_inv (st : IoppStage) (L : GroupLayout) (row : GroupRow) (R : SingleRows)
    (h : ioppLastRows st L row = some R) :
    R = { code := st.code, maskCode := st.maskCode, masks := 1, c := row.c.fixLow [zeroE],
          d := #[row.d], target := row.target, layout := { L with k := 0 } } := by
  unfold ioppLastRows at h
  split at h
  · exact (Option.some.inj h).symm
  · cases h

/-- What a run of the last case says of the run before it, and what it leaves: if no named test has
failed at its end, none had failed at its start; and it takes the two written rounds and no more. -/
theorem ioppLast_frame (answers : ℕ) (ride : Bool) (cur : IoppStage) (row : GroupRow)
    (L : GroupLayout) (star : ℕ) (dL dB : PQ.RD) (mL : (wRound dL).Msg) (cL : (wRound dL).Chal)
    (mB : (wRound dB).Msg) (cB : (wRound dB).Chal) (rest : List Fmt.RoundView) (c c' : Ctx)
    (hd : c.ch.dry = false)
    (hp : c.ch.pending = PQ.rvSL (ckP .two) [dL, dB] (mL, cL, mB, cB, ()) ++ rest)
    (h : (ioppStagesVerify answers ride cur [] row L (some star)).Yields c () c')
    (hf : c'.failed = none) : c.failed = none ∧ c'.ch.pending = rest := by
  obtain ⟨R, hR, hrun⟩ := ioppStages_last_inv answers ride cur row L (some star) c c' h
  have eR := ioppLastRows_inv cur L row R hR
  subst eR
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, h1, h2, _⟩ := baseVerify_run _ star 0 dL dB mL cL mB cB rest c c' hd hp rfl rfl hrun hf
  exact ⟨h1, h2⟩

/-- If the last case of the program's proximity test runs through and no named test fails, the
library's decision holds at the values of the two written rounds. The claim x reads the program's
row on the last group: its main table at the indices 2 j, its mask table at the indices j. Also
asked: `FixLaw` for the row's form, and the hypotheses of `baseVerify_sem` on codes, sizes and
symbols (`htie`). -/
theorem ioppLast_sem (s : Sg) (h0 : s.h = 0) (g0 : s.g = 0) (ha : s.C.a ≤ 32) (hz : s.Z.a ≤ 32)
    (answers : ℕ) (ride : Bool) (cur : IoppStage) (row : GroupRow) (L : GroupLayout) (star : ℕ)
    (dL dB : PQ.RD) (mL : (wRound dL).Msg) (cL : (wRound dL).Chal) (mB : (wRound dB).Msg)
    (cB : (wRound dB).Chal) (rest : List Fmt.RoundView) (c c' : Ctx) (hd : c.ch.dry = false)
    (hp : c.ch.pending = PQ.rvSL (ckP .two) [dL, dB] (mL, cL, mB, cB, ()) ++ rest)
    (h : (ioppStagesVerify answers ride cur [] row L (some star)).Yields c () c')
    (hf : c'.failed = none) {nB : ℕ} (hB : SendsDraws dB nB 0 s.t s.C.a) (cd : Code)
    (hcd : c.st.codes.base[cur.code]? = some cd) (hC : codeOf cd = s.C)
    (hZ : codeOf (c.st.codes.mask.getD cur.maskCode default) = s.Z)
    (x : GE × (s.cIn.J → GE)) (f g : s.cIn.Word) (hx1 : x.1 = readE row.target)
    (hxc : ∀ j : Fin s.C.l, x.2 (.inl (fun _ => false, j)) = readE (row.c.entry (2 * j.val)))
    (hxd : ∀ j : Fin s.Z.l, x.2 (.inr (fun _ => false, j)) = readV row.d j.val)
    (hfix : FixLaw row.c [zeroE])
    (htie : ∀ R c1 a opened y stars, ioppLastRows cur L row = some R →
      (Blk.readOpened ((singleRowsOracles R).push star)
        (Positions.ofDraws cd.logN (rvOf dB mB cB).poss)).Yields a opened c' →
      a.ch.dry = false → a.ch.opened = c.ch.opened → a.book = c.book →
      a.ch.firstTree = c.ch.firstTree → (Blk.spendAsMask star).Yields c () c1 → a.st = c1.st →
      singleRowsSymbols R opened
        (Positions.ofDraws cd.logN (rvOf dB mB cB).poss).all.size = some y →
      opened.back? = some stars →
      BaseTie s f g (Positions.ofDraws cd.logN (rvOf dB mB cB).poss) y stars) :
    LdwAccept (ldCw s.cIn) (ldForm (Slf.idf (E := GE) (J := s.cIn.J)) x) x.1 (s.cIn.T f)
      (s.cIn.T g) (lst (sentW dL mL) 0) (gOne _ (valsOf dL cL)) (shownW s (sentW dB mB))
      (gPos s.C.a s.t _ (valsOf dB cB)) := by
  obtain ⟨R, hR, hrun⟩ := ioppStages_last_inv answers ride cur row L (some star) c c' h
  have eR := ioppLastRows_inv cur L row R hR
  have tie := htie R
  subst eR
  exact baseVerify_sem s h0 g0 ha hz _ star 0 dL dB mL cL mB cB rest c c' hd hp rfl rfl hrun
    hf hB cd hcd hC hZ x f g hx1 (fun j => (hxc j).trans (fix_zero row.c hfix j.val).symm) hxd
    fun c1 a opened y stars => tie c1 a opened y stars hR

end OnBytes.Slice

#print axioms OnBytes.Slice.fix_zero
#print axioms OnBytes.Slice.ioppLast_frame
#print axioms OnBytes.Slice.ioppLast_sem
#print axioms OnBytes.Slice.ioppLastRows_inv
