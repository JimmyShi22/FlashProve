-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5LeftFits.lean: kind K5: THE FIELDS OF K5Left
(Johnson/Desc/First/Att/Door/Law/K5AtEqsPlus.lean: what is left of K5AtMg at a filling that meets
the equations) PAID, ONE SMALL THEOREM A FIELD, BY K5's FILES' OWN THEOREMS, CALLED AT THE COMMON
LETTERS. TWO THEOREMS A FIELD: ‹field›_plus: the payer at the common letters, its premises given
directly · left_‹field›_fits: takes a given structure and returns it with that field laid anew: it
proves nothing new of the structure (the given one holds the field already); LEAN WOULD REFUSE IT IF
THE PAYER's CONCLUSION WERE NOT THE FIELD's TYPE. The fits build no K5Left: the last assembly is a
structure instance over the ‹field›_plus.

IS IT EMPTY HERE? Checks of fit. NO MEMBER IS SHOWN.

Main names:
  `behind_plus`: **the field behind**, at the filled pin and the table's relation behind the
    sub-protocol: k5AtMg_behind_row (Johnson/Desc/First/Att/K05AtMgRow.lean) with hfT := hfT_plus
    (K5GainsPlus.lean), hdoor := hdoor_plus (K5DoorAtPlus.lean), the pin's equation off MgIs, the
    runs and the readers off three fields of K5Left.
  `left_behind_fits`, `left_pinOk_fits`: the checks.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5DoorAtPlus
import Johnson.Desc.First.Att.Door.Law.K5GainsPlus
import Johnson.Desc.First.Att.K05AtMgRow
import Johnson.Desc.First.Att.K05AtMgPin

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Door
open Cb Cb.Fo Cb.LdLkp OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Maker Johnson.Pack
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (Sent attSg JAtt enMask lookAt sigListCalls keptAt)
open VerifiableInference.Desc.K9 (RunOf)
open VerifiableInference.Desc.K13.Law (DataK13)
open VerifiableInference.Desc.First.Att.P
open VerifiableInference.Desc.K12.Door (Laid)

section
variable {Pp Xi Cells Tok Cl : Type} {nR : ℕ} {Fr : Frame}
  (Mg Mg0 : Meaning Pp (Wit Cells Tok MsgT)) (D : PubData) (Dn : Sent) (G0 : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf Dn.codes s.l).om i).Smp) (ms : List Mem)
  (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells) (in0 : Pp × S → Bool) (c5 : Pp → Bool)
  (Ld : Laid) (Ms : List OracleShape) (D13 : DataK13 Pp (Wit Cells Tok MsgT) nR)
  (E : MgIs Mg Mg0 D Dn.codes G0 arr smp ms decT in0 c5 Ld Ms D13)
  (bs : ℕ) (claim : Aff → Cl) (Wv : Verify.Public) (g : ℕ) (before : List (ℕ × ℕ)) (a : Attention.Plan) (x : Look.Place)
  (links : List ModelPart) (T : DataIs D Wv links (2 * g + 1)) (Sn : DataSent D Dn.codes Dn)
  (hP : PlanIs Wv) (h4 : Wv.p4 = true) (ha : Wv.A[g]? = some a) (hx : lookAt Wv (2 * g + 1) false = some x)
  {pl pl' : VerifiableInference.Desc.Place} (Ix : K5Place links (2 * g + 1) pl pl')
  (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
  (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)) → Cb.Gl.E) (plJ : ℕ → ℕ → JAtt x.ns a.seam.tl)
  (O : List Item) (Q : List Pub) (states : ℕ → List (RunOf S))
  (uL uH : ℕ → UFn) (wt : ℕ → Pp × S → Strs → Wit Cells Tok MsgT → Prop)
  (seatT : Fin (sigListCalls Dn rad x.link).length → ℕ × ℕ) (arrL : ℕ → ℕ → ℕ)
  (G : MgGains Mg Dn.codes arr ms D.Rd D.runs (Stated.of (uBySort uL (uArm Wv) uH)) D.N wt (2 * g + 1) x a.S a.seam.tl Dn rad seatT arrL)
  (pls : List VerifiableInference.Desc.Place) (k : ℕ) (hk : pls[k]? = some pl)
  (seat : Fin (sigListCalls Dn rad x.link).length → ℕ × ℕ)
  (smpR : Array OnBytes.Oracle × OnBytes.TreeBook → (i : Fin (sigListCalls Dn rad x.link).length) →
    Option ((sigOf Dn.codes (sigListCalls Dn rad x.link)).om i).Smp)
  (hlow : ∀ i, (seat i).1 < bs)

include E T Sn hP h4 ha hx Ix G hk in
/-- **The field behind.** -/
theorem behind_plus (hmH : (2 * g + 1 == D.mH) = false) (hn : D.nsOf (2 * g + 1) = some a.ns) (Oq : OpenQ (2 * g + 1) Q)
    (hruns3 : D.runs (2 * g + 1) 3 "own" = [(2, "first"), (2, "keys"), (2, "second")])
    (hrunsJ : D.runs (2 * g + 1) 2 "join" = [(2, "join")])
    (hrds : ∀ (name : String) (s : S) (R : K9.Read), (name == "K8.equations") = false →
      K9.readerOf states 2 name s = some R → (D.Rd (2 * g + 1)).forms 2 name s = some R)
    (hst : states 2 = runsN a)
    (hpub : TiePub Dn x a.seam.tl a.ns rad)
    (hm : ∀ (fs : List Aff) (j : Fin (sigListCalls Dn rad x.link).length),
      ReadMsg (ReadAddr a.seam.tl fs) Dn x.link j.val → MemAt ms (sigListCalls Dn rad x.link) seat j)
    (hPs : seatsPlanB D.dS (2 * g + 1) (keptAt Dn x.link).length Ld
      (psOf (sigListCalls Dn rad x.link) seat (readMsgs Dn x a.seam.tl)) (D.N.sent x.link 0) (D.N.msgsAt (some pl)) = true)
    (hPq : shapesPlanB D.dS (2 * g + 1) (keptAt Dn x.link).length Ms
      (qsOf (sigListCalls Dn rad x.link) (readMsgs Dn x a.seam.tl)) (D.N.msgsAt (some pl)) = true)
    (hsome : ∀ i, ∃ y ∈ ms, Alike y (⟨⟨sigListCalls Dn rad x.link, seat⟩, i⟩ : Mem)) (hSB : SmpBySeat Dn.codes smp)
    (hsent : ∀ i, seat i ∈ D.N.sent (2 * g + 1) 0)
    (hsm : ∀ (π : Pp) (s : S) i, smpR (s.st.oracles, s.book) i = smp (π, s) ⟨sigListCalls Dn rad x.link, seat⟩ i) :
    ∀ x0 gOf, LeftIsP Mg claim Wv g before a x plJ x0 gOf → ∀ π : Pp,
      K5Behind x a.seam.tl Dn rad Ex Wp α a (parO Wv (2 * g + 1) a before) a.ns bs a.nW (plannedK a) (padOfO a.fs) [] (gOf π)
        (onT D.N Mg links π Fr pl O Q) (k5Pin (Cells := Cells) (Tok := Tok) G0 x Dn rad seat smpR arr Fr bs hlow)
        (relAt (meansQ (Fr := Fr) D.N Mg fun s => (π, s)) (outsQ links pls k)) := by
  intro x0 gOf hL
  obtain ⟨_, _, hxl, hfs⟩ := place_calls h4 ha hx
  have hOf : K5Law.OfPlan a := by
    obtain ⟨A0, pf, h0, e⟩ := hP g a ha
    exact ⟨_, _, _, A0, pf, h0, e⟩
  have hA : Wv.A[x.link / 2]? = some a := by
    rw [hxl, show (2 * g + 1) / 2 = g by omega]
    exact ha
  exact k5AtMg_behind_row bs claim Wv (2 * g + 1) before a x Dn rad Ex Wp α a.ns x0 gOf plJ D.N Mg links pl O Q hL hfs Oq.q6 Ix hxl
    G0 D.Rd D.runs uL uH pls k arr seat ms a.ns smpR hlow
    (fun π j name b w h => hfT_plus G x.link j name (π, b.1) (strsOf Fr b.2) w h) hpub
    (by rw [hxl, hruns3]; simp) (by rw [hxl, hruns3]; simp) (by rw [hxl, hrunsJ]; simp)
    (by rw [hxl]; exact hrds) hst hm hA hOf
    (hdoor_plus Mg Mg0 D Dn.codes G0 arr smp ms decT in0 c5 Ld Ms D13 E claim Wv g before a x links T Dn Sn Ix hxl hmH hn O Q Oq plJ
      x0 gOf hL _ _ hPs hPq)
    smp E.pin hsome hSB hsent hsm hk

include E T Sn hP h4 ha hx Ix G hk in
/-- Lean's check: behind_plus' conclusion is the field's type. -/
theorem left_behind_fits (hmH : (2 * g + 1 == D.mH) = false) (Oq : OpenQ (2 * g + 1) Q)
    (hpub : TiePub Dn x a.seam.tl a.ns rad)
    (hm : ∀ (fs : List Aff) (j : Fin (sigListCalls Dn rad x.link).length),
      ReadMsg (ReadAddr a.seam.tl fs) Dn x.link j.val → MemAt ms (sigListCalls Dn rad x.link) seat j)
    (hPs : seatsPlanB D.dS (2 * g + 1) (keptAt Dn x.link).length Ld
      (psOf (sigListCalls Dn rad x.link) seat (readMsgs Dn x a.seam.tl)) (D.N.sent x.link 0) (D.N.msgsAt (some pl)) = true)
    (hPq : shapesPlanB D.dS (2 * g + 1) (keptAt Dn x.link).length Ms
      (qsOf (sigListCalls Dn rad x.link) (readMsgs Dn x a.seam.tl)) (D.N.msgsAt (some pl)) = true)
    (hsome : ∀ i, ∃ y ∈ ms, Alike y (⟨⟨sigListCalls Dn rad x.link, seat⟩, i⟩ : Mem)) (hSB : SmpBySeat Dn.codes smp)
    (hsent : ∀ i, seat i ∈ D.N.sent (2 * g + 1) 0)
    (hsm : ∀ (π : Pp) (s : S) i, smpR (s.st.oracles, s.book) i = smp (π, s) ⟨sigListCalls Dn rad x.link, seat⟩ i)
    (L : K5Left Mg Mg0 D Dn.codes smp decT in0 D13 bs claim Wv g before a x Dn rad Ex Wp α plJ
      (k5Pin (Cells := Cells) (Tok := Tok) G0 x Dn rad seat smpR arr Fr bs hlow)
      (fun π => relAt (meansQ (Fr := Fr) D.N Mg fun s => (π, s)) (outsQ links pls k)) links pl O Q states) :
    K5Left Mg Mg0 D Dn.codes smp decT in0 D13 bs claim Wv g before a x Dn rad Ex Wp α plJ
      (k5Pin (Cells := Cells) (Tok := Tok) G0 x Dn rad seat smpR arr Fr bs hlow)
      (fun π => relAt (meansQ (Fr := Fr) D.N Mg fun s => (π, s)) (outsQ links pls k)) links pl O Q states :=
  { L with
    behind := behind_plus Mg Mg0 D Dn G0 arr smp ms decT in0 c5 Ld Ms D13 E bs claim Wv g before a x links T Sn hP h4 ha hx Ix rad Ex Wp α
      plJ O Q states uL uH wt seatT arrL G pls k hk seat smpR hlow hmH L.nsOf Oq L.runs3 L.runsJ L.rds L.st2 hpub hm hPs hPq hsome hSB hsent
      hsm }

/-- Lean's check: the filled pin's own side condition is the field's type. No premise. -/
theorem left_pinOk_fits
    (L : K5Left Mg Mg0 D Dn.codes smp decT in0 D13 bs claim Wv g before a x Dn rad Ex Wp α plJ
      (k5Pin (Cells := Cells) (Tok := Tok) G0 x Dn rad seat smpR arr Fr bs hlow)
      (fun π => relAt (meansQ (Fr := Fr) D.N Mg fun s => (π, s)) (outsQ links pls k)) links pl O Q states) :
    K5Left Mg Mg0 D Dn.codes smp decT in0 D13 bs claim Wv g before a x Dn rad Ex Wp α plJ
      (k5Pin (Cells := Cells) (Tok := Tok) G0 x Dn rad seat smpR arr Fr bs hlow)
      (fun π => relAt (meansQ (Fr := Fr) D.N Mg fun s => (π, s)) (outsQ links pls k)) links pl O Q states :=
  { L with pinOk := pinOk_at_pin G0 x Dn rad seat smpR arr Fr bs hlow D.N Mg links pl O Q }

end

end H2K5.Door

#print axioms H2K5.Door.behind_plus
#print axioms H2K5.Door.left_behind_fits
#print axioms H2K5.Door.left_pinOk_fits
