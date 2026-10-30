-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Coin.LawY
import Johnson.Desc.K12.Coin.Vals
import Johnson.Desc.K12.Law.TupleVals
/-
Johnson/Desc/K12/Law/BatValsPay.lean: THE PAYER OF THE COUNT THAT THE LAW OF THE PROXIMITY TEST IN THE PLAIN FORM LEAVES OPEN: BatVals (Johnson/Desc/K12/Coin/Vals.lean), AND WITH IT BatAtN AND BatAtY, AT THE LETTER N := «one tuple for all rows». NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  NTuple        what is concluded, as the sheet's letter N: there are row₀ and hok with TupleAt (Johnson/Desc/K12/Law/TupleAt.lean: tuple_or_few's first arm) at the record behind the batching's beginning, at the written oracles W0 F no D.book x.2 and the radius rad (sgOf a)
  PayK          WHAT THE PAYER ASKS OF A RECORD, at whatever the record fixes: StageJ at the radius (the facts on codes) · combineAt at the statement behind the beginning (a test with code) · the layout's four numbers · lstJ (radius) * (rows − 1) ≤ v₀
  batVals_pay   PayK · "BAT"'s round draws one element and nothing else ⇒ BatVals F π no rad rd dB v₀ (NTuple …) x
  batAtN_pay    … · logN ≤ 64 ⇒ BatAtN at e₀ := v₀ * w (by the sheet's batAtN_of_vals)
  batAtY_pay    … ⇒ BatAtY at that e₀ (by the sheet's batAtY_of_N)
WHAT STANDS AGAINST IT: (1) PayK IS A PREMISE: NO MEMBER IS SHOWN IN LEAN: each clause is a test that has run true at the four proximity tests of both stored proofs, or a gift of one (a run's word) · (2) Ly.k and Ly.h a yes of the piece gives (the sheet's yes_fits): here they are asked outright: a payer of BatAtY alone could spare them · (3) NTuple IS NOT NearAll: «all the batched rows hold of the witness's own words, and its parts are candidates at each sampled member», not «every row, carried to the group's tables, holds at the witness»: the bridge row by row is untyped · (4) which arm holds no program can choose · (5) the number v₀ is evaluated nowhere here.


(Where this and lean/THEOREM.md differ,
the page holds.)
No sorry, no axiom of ours; each theorem has its premises;
what each rests on is printed at the file's end.

-/
set_option autoImplicit false
namespace H2K.Pin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker OnBytes.Flat
open OnBytes.Means
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Coin
open H2K.JointK (yOf)
open H2K.Pub (sgOf)
open H2K.First (gpL Plain good_of_ok)

/-- What is concluded: one tuple for all rows. -/
def NTuple (F : Frame) (π : P12) (no : ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) : ConclK F :=
  fun x a _ G0 Ly D =>
    ∃ (row₀ : GroupRow) (hok : H2K.First.ok (gpL π a row₀ D) = true),
      TupleAt (good_of_ok π a row₀ D hok)
        { x.1 with st := begun x.1.st x.1.g G0, pass := .claim row₀ Ly } Ly x.1.st G0 rd
        (fun i => (W0 F no D.book x.2 (D.mems.get i).t).1) (W0 F no D.book x.2 D.fresh.t).1
        (fun i => (W0 F no D.book x.2 (D.mems.get i).t).2) (rad (sgOf a))

/-- What the payer asks of a record in front of the block, at whatever the record fixes. -/
def PayK (π : P12) (rad : Sg → ℕ) (v₀ : ℕ) (t : T12) : Prop :=
  ∀ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain),
    Fixes π t a rest G0 Ly D →
    (sgOf a).StageJ (rad (sgOf a)) ∧
    combineAt (begun t.st t.g G0) t.g ⟨Ly, runRows t.st G0⟩ = true ∧
    Ly.k = (sgOf a).h + (sgOf a).g ∧ Ly.h = (sgOf a).h ∧
    2 ^ Ly.logEll = (sgOf a).C.l ∧ 2 ^ Ly.logEllZk = (sgOf a).Z.l ∧
    (sgOf a).lstJ (rad (sgOf a)) * ((runRows t.st G0).size - 1) ≤ v₀


theorem batVals_pay (F : Frame) (π : P12) (no : ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (dB : RDT)
    (v₀ : ℕ) (x : T12 × F.E.Str) (hP : PayK π rad v₀ x.1)
    (h1 : Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0]) :
    BatVals F π no rad rd dB v₀ (NTuple F π no rad rd) x := by
  intro a rest G0 Ly D row₀ hok hf m
  obtain ⟨hJ, ht, hk, hh, hl, hz, hv⟩ := hP a rest G0 Ly D hf
  rcases bat_vals_yOf π x.1 a G0 Ly D row₀ hok hf.2.1 hf.2.2.1 (hf.2.2.2 row₀) rd
    (W0 F no D.book x.2) (rad (sgOf a)) hJ ht hk hh hl hz dB.entry dB.kind h1 with hT | hC
  · rw [cnt_false]
    · exact Nat.zero_le _
    · rintro v ⟨_, _, _, _, hn⟩
      exact hn ⟨row₀, hok, hT⟩
  · refine le_trans (cnt_mono ?_)
      ((hC (PQ.PlainOf.gots dB.items (GPlain.old (b := dB.entry.work) m.2))).trans hv)
    rintro v ⟨row, w, hb, hr, _⟩
    exact ⟨row, w, hb, hr⟩

theorem batAtN_pay (F : Frame) (π : P12) (no : ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (dB : RDT)
    (v₀ : ℕ) (x : T12 × F.E.Str) (hP : PayK π rad v₀ x.1)
    (h1 : Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0]) (hlog : dB.entry.logN ≤ 64) :
    BatAtN F π no rad rd dB (v₀ * (bsRound .two dB.entry dB.kind).w) (NTuple F π no rad rd) x :=
  batAtN_of_vals F π no rad rd dB v₀ _ x hlog (batVals_pay F π no rad rd dB v₀ x hP h1)

theorem batAtY_pay (F : Frame) (W : Type) (π : P12) (no : ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ)
    (base : ℕ) (dB : RDT) (dt : List RDT) (v₀ : ℕ) (εt : Err (uLT (ckP .two) dt))
    (x : T12 × F.E.Str) (hP : PayK π rad v₀ x.1)
    (h1 : Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0]) (hlog : dB.entry.logN ≤ 64) :
    BatAtY F W π no rad rd base dB dt (v₀ * (bsRound .two dB.entry dB.kind).w) εt
      (NTuple F π no rad rd) x :=
  batAtY_of_N F W π no rad rd base dB dt _ εt _ x
    (batAtN_pay F π no rad rd dB v₀ x hP h1 hlog)

end H2K.Pin

#print axioms H2K.Pin.batVals_pay
#print axioms H2K.Pin.batAtN_pay
#print axioms H2K.Pin.batAtY_pay
