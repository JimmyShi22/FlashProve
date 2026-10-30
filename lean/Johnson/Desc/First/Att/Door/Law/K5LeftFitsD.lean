-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Door/Law/K5LeftFitsD.lean: kind K5: SEVEN MORE FIELDS OF K5Left (Door/Law/K5AtEqsPlus.lean): runs3 · runsJ · okAll · st2 · rds · objR · objLate: each as a theorem concluding the field's own text (‹field›_plus), and Lean's own check that the conclusion is the field's
type (left_‹field›_fits: { L with ‹field› := … }: nothing new).
THE PAYERS: runsAt_own | runsAt_join (Door/Law/K5LeftFitsB.lean: the table's own map of names) · guard_gives_written (Att/GuardNLaw.lean) · hRds_seated (Att/K05ReadersGuarded.lean) · the two sentences on the readers' answers at (1, "objects") and (1, "guests") (hObj | hGst, as
k5FillRel_objects takes them: Att/K05ObjectsBack.lean).
st2 AND rds FIX A LETTER: K5Left's letter "states" is laid := fun _ => runsN a: their checks stand at that K5Left.
THREE FACTS ARE PREMISES HERE, NOT SHOWN IN THIS FILE: hL | hsame (what the seated link's block 2 states; the guard's test) and hObj | hGst at the seated link.
objR | objLate: the premise hbare is fenced by the promise and "no mark" (onT).
IS IT EMPTY HERE? Implications: no member of K5Left is shown. objLate holds for want of any late slot.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5LeftFitsB

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Door
open Cb Cb.Fo Cb.LdLkp OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Maker Johnson.Pack
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (Sent attSg JAtt enMask lookAt placeAt k3SortAt)
open VerifiableInference.Desc.First.FillK4 (isLay)
open VerifiableInference.Desc.K9 (RunOf readerOf)
open VerifiableInference.Desc.K13.Law (DataK13 fillK13)
open VerifiableInference.OnPublicFiles (k3LeftItemAt k3LeftOnItemAt)
open VerifiableInference.Desc.First.Att.P
open VerifiableInference.Desc.K12.Door (Laid)
open VerifiableInference.Desc.K9 (Readers statesOfLink readersOfLink LinkHoles)

section
variable {Pp Cells Tok Cl : Type} {nR : ℕ} {Fr : Frame}
  (Mg Mg0 : Meaning Pp (Wit Cells Tok MsgT)) (D : PubData)
  (cs : OnBytes.Codes)
  (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells) (in0 : Pp × S → Bool)
  (D13 : DataK13 Pp (Wit Cells Tok MsgT) nR)
  (bs : ℕ) (claim : Aff → Cl) (Wv : Verify.Public) (g : ℕ) (before : List (ℕ × ℕ)) (a : Attention.Plan) (x : Look.Place)
  (Dn : Sent) (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
  (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)) → Cb.Gl.E) (plJ : ℕ → ℕ → JAtt x.ns a.seam.tl)
  (I : PinItemP Fr seatSO bs (Wit Cells Tok MsgT) (attSg x Dn rad).Msg)
  (R' : Pp → S × Fr.E.Str → Wit Cells Tok MsgT → Prop)
  (links : List ModelPart) (pl : VerifiableInference.Desc.Place) (O : List Item) (Q : List Pub) (states : ℕ → List (RunOf S))

/-! ## runs3 · runsJ -/

theorem runs3_plus (hR : D.runs = runsAt links) (hs : links[2 * g + 1]? = some .attention) :
    D.runs (2 * g + 1) 3 "own" = [(2, "first"), (2, "keys"), (2, "second")] := by
  rw [hR]
  exact runsAt_own hs

theorem runsJ_plus (hR : D.runs = runsAt links) (hs : links[2 * g + 1]? = some .attention) :
    D.runs (2 * g + 1) 2 "join" = [(2, "join")] := by
  rw [hR]
  exact runsAt_join hs

theorem runsO_plus (hR : D.runs = runsAt links) (hs : links[2 * g + 1]? = some .attention) :
    D.runs (2 * g + 1) 2 "objects" = [(1, "objects"), (1, "guests")] := by
  rw [hR]
  exact runsAt_objects hs

/-! ## okAll -/

include Dn rad in
theorem okAll_plus (hP : PlanIs Wv) (h4 : Wv.p4 = true) (ha : Wv.A[g]? = some a)
    (hG : k5GuardN Wv (2 * g + 1) g = true) (hb : planOk (parO Wv (2 * g + 1) a before) = true) (hc : claimsOkAtO a = true) :
    planOkAll a.S.cf a.S a.fs = true := by
  obtain ⟨_, A0, _, ⟨pf, e⟩, Pb⟩ := guard_gives_written hP h4 g before Dn rad ha hG hb hc
  have eS : a.S = A0.S := by rw [e]
  have eF : a.fs = A0.fs := by rw [e]
  have h := Pb.planOk
  rw [← eS, ← eF] at h
  exact h

/-! ## st2 · rds -/

theorem st2_plus : (fun _ : ℕ => runsN a) 2 = runsN a := rfl

theorem rds_plus (H : LinkHoles) (L : Link S Claim) (hRd : D.Rd (2 * g + 1) = readersOfLink H L) (same : S → S → Bool)
    (hL : statesOfLink L 2 = (runsN a).map (guardC same)) (hsame : ∀ s t : S, t.out = s.out → same s t = true) :
    ∀ (name : String) (s : S) (R : K9.Read), (name == "K8.equations") = false →
      readerOf (fun _ => runsN a) 2 name s = some R → (D.Rd (2 * g + 1)).forms 2 name s = some R := by
  rw [hRd]
  exact hRds_seated H L a same hL hsame

/-! ## objR · objLate -/

theorem objR_plus (x0 : Pp → S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl))) (gOf : Pp → S × Fr.E.Str → Forest.Heard)
    (hLI : LeftIsP Mg claim Wv g before a x plJ x0 gOf) (hleftQ : Pub.left (2 * g + 1) ∈ Q)
    (hObj : ∀ (t : S) (F : Fork) (g₁ : Forest.Heard), t.fork? = some F → t.lookHeard? = some g₁ →
      (∀ f ∈ g₁.rows.toList, f.ents = #[]) → (D.Rd (2 * g + 1)).forms 1 "objects" t = some { forms := g₁.rows.toList, late := [] })
    (hGst : ∀ (t : S) (F : Fork), t.fork? = some F → (D.Rd (2 * g + 1)).forms 1 "guests" t = some { forms := [], late := [] })
    (hbare : ∀ (π : Pp) (a' : S × Fr.E.Str), onT D.N Mg links π Fr pl O Q a' → ∀ f ∈ ((gOf π) a').rows.toList, f.ents = #[])
    (hrO : D.runs (2 * g + 1) 2 "objects" = [(1, "objects"), (1, "guests")]) :
    ∀ π : Pp, ∀ (s : S) (y : Fr.E.Str) (att : AttOwn) (hd : Heard) (G : Fork) (rs : List Fmt.RoundView),
      onAt D.N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none → s.here = .att att →
      hear (parO Wv (2 * g + 1) a before).own (att.F, rs, 0) = some (hd, G, [], 0) → ∀ p ∈ D.runs (2 * g + 1) 2 "objects",
        (D.Rd (2 * g + 1)).forms p.1 p.2 (behind s att hd G) = (D.Rd (2 * g + 1)).forms p.1 p.2 s := by
  intro π s y att hd G rs hon hm e _ p hp
  have hPl := onAt_pubP hon hm _ hleftQ
  obtain ⟨_, _, _, _, _, _, e1, _, _⟩ := hLI π (s, y) hPl
  have e1' : s.lookHeard? = some ((gOf π) (s, y)) := e1
  have hlk : (behind s att hd G).lookHeard? = some ((gOf π) (s, y)) := by
    unfold S.lookHeard? at e1' ⊢
    rw [e] at e1'
    exact e1'
  have hbr := hbare π (s, y) ⟨hon, hm⟩
  rw [hrO] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact (hObj _ G _ rfl hlk hbr).trans (hObj s att.F _ (fork_front e) e1' hbr).symm
  · exact (hGst _ G rfl).trans (hGst s att.F (fork_front e)).symm

theorem objLate_plus (x0 : Pp → S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl))) (gOf : Pp → S × Fr.E.Str → Forest.Heard)
    (hLI : LeftIsP Mg claim Wv g before a x plJ x0 gOf) (hleftQ : Pub.left (2 * g + 1) ∈ Q)
    (hObj : ∀ (t : S) (F : Fork) (g₁ : Forest.Heard), t.fork? = some F → t.lookHeard? = some g₁ →
      (∀ f ∈ g₁.rows.toList, f.ents = #[]) → (D.Rd (2 * g + 1)).forms 1 "objects" t = some { forms := g₁.rows.toList, late := [] })
    (hGst : ∀ (t : S) (F : Fork), t.fork? = some F → (D.Rd (2 * g + 1)).forms 1 "guests" t = some { forms := [], late := [] })
    (hbare : ∀ (π : Pp) (a' : S × Fr.E.Str), onT D.N Mg links π Fr pl O Q a' → ∀ f ∈ ((gOf π) a').rows.toList, f.ents = #[])
    (hrO : D.runs (2 * g + 1) 2 "objects" = [(1, "objects"), (1, "guests")]) :
    ∀ π : Pp, ∀ (s : S) (y : Fr.E.Str) (att : AttOwn), onAt D.N Mg links (some pl) O Q (π, s) (strsOf Fr y) →
      s.failed = none → s.here = .att att → ∀ p ∈ D.runs (2 * g + 1) 2 "objects", ∀ R,
        (D.Rd (2 * g + 1)).forms p.1 p.2 s = some R → ∀ t ∈ R.late, t.1 < att.F.next := by
  intro π s y att hon hm e p hp R hR t ht
  have hPl := onAt_pubP hon hm _ hleftQ
  obtain ⟨_, _, _, _, _, _, e1, _, _⟩ := hLI π (s, y) hPl
  have e1' : s.lookHeard? = some ((gOf π) (s, y)) := e1
  have hbr := hbare π (s, y) ⟨hon, hm⟩
  rw [hrO] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · obtain rfl := Option.some.inj ((hObj s att.F _ (fork_front e) e1' hbr).symm.trans hR)
    cases ht
  · obtain rfl := Option.some.inj ((hGst s att.F (fork_front e)).symm.trans hR)
    cases ht

/-! ## Lean's own checks of the fields' types -/

theorem left_runs3_fits (hR : D.runs = runsAt links) (hs : links[2 * g + 1]? = some .attention)
    (L : K5Left Mg Mg0 D cs smp decT in0 D13 bs claim Wv g before a x Dn rad Ex Wp α plJ I R' links pl O Q states) : K5Left Mg Mg0 D cs smp decT in0 D13 bs claim Wv g before a x Dn rad Ex Wp α plJ I R' links pl O Q states :=
  { L with runs3 := runs3_plus D g links hR hs }

theorem left_runsJ_fits (hR : D.runs = runsAt links) (hs : links[2 * g + 1]? = some .attention)
    (L : K5Left Mg Mg0 D cs smp decT in0 D13 bs claim Wv g before a x Dn rad Ex Wp α plJ I R' links pl O Q states) : K5Left Mg Mg0 D cs smp decT in0 D13 bs claim Wv g before a x Dn rad Ex Wp α plJ I R' links pl O Q states :=
  { L with runsJ := runsJ_plus D g links hR hs }

theorem left_okAll_fits (hP : PlanIs Wv) (h4 : Wv.p4 = true) (ha : Wv.A[g]? = some a)
    (hG : k5GuardN Wv (2 * g + 1) g = true) (hb : planOk (parO Wv (2 * g + 1) a before) = true) (hc : claimsOkAtO a = true)
    (L : K5Left Mg Mg0 D cs smp decT in0 D13 bs claim Wv g before a x Dn rad Ex Wp α plJ I R' links pl O Q states) : K5Left Mg Mg0 D cs smp decT in0 D13 bs claim Wv g before a x Dn rad Ex Wp α plJ I R' links pl O Q states :=
  { L with okAll := okAll_plus Wv g before a Dn rad hP h4 ha hG hb hc }

theorem left_st2_fits (L : K5Left Mg Mg0 D cs smp decT in0 D13 bs claim Wv g before a x Dn rad Ex Wp α plJ I R' links pl O Q (fun _ => runsN a)) : K5Left Mg Mg0 D cs smp decT in0 D13 bs claim Wv g before a x Dn rad Ex Wp α plJ I R' links pl O Q (fun _ => runsN a) :=
  { L with st2 := st2_plus a }

theorem left_rds_fits (H : LinkHoles) (Lk : Link S Claim) (hRd : D.Rd (2 * g + 1) = readersOfLink H Lk) (same : S → S → Bool)
    (hL : statesOfLink Lk 2 = (runsN a).map (guardC same)) (hsame : ∀ s t : S, t.out = s.out → same s t = true)
    (L : K5Left Mg Mg0 D cs smp decT in0 D13 bs claim Wv g before a x Dn rad Ex Wp α plJ I R' links pl O Q (fun _ => runsN a)) : K5Left Mg Mg0 D cs smp decT in0 D13 bs claim Wv g before a x Dn rad Ex Wp α plJ I R' links pl O Q (fun _ => runsN a) :=
  { L with rds := rds_plus D g a H Lk hRd same hL hsame }

theorem left_objR_fits (x0 : Pp → S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl))) (gOf : Pp → S × Fr.E.Str → Forest.Heard)
    (hLI : LeftIsP Mg claim Wv g before a x plJ x0 gOf) (hleftQ : Pub.left (2 * g + 1) ∈ Q)
    (hObj : ∀ (t : S) (F : Fork) (g₁ : Forest.Heard), t.fork? = some F → t.lookHeard? = some g₁ →
      (∀ f ∈ g₁.rows.toList, f.ents = #[]) → (D.Rd (2 * g + 1)).forms 1 "objects" t = some { forms := g₁.rows.toList, late := [] })
    (hGst : ∀ (t : S) (F : Fork), t.fork? = some F → (D.Rd (2 * g + 1)).forms 1 "guests" t = some { forms := [], late := [] })
    (hbare : ∀ (π : Pp) (a' : S × Fr.E.Str), onT D.N Mg links π Fr pl O Q a' → ∀ f ∈ ((gOf π) a').rows.toList, f.ents = #[])
    (hrO : D.runs (2 * g + 1) 2 "objects" = [(1, "objects"), (1, "guests")])
    (L : K5Left Mg Mg0 D cs smp decT in0 D13 bs claim Wv g before a x Dn rad Ex Wp α plJ I R' links pl O Q states) : K5Left Mg Mg0 D cs smp decT in0 D13 bs claim Wv g before a x Dn rad Ex Wp α plJ I R' links pl O Q states :=
  { L with objR := (objR_plus Mg D claim Wv g before a x plJ links pl O Q x0 gOf hLI hleftQ hObj hGst hbare hrO) }

theorem left_objLate_fits (x0 : Pp → S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl))) (gOf : Pp → S × Fr.E.Str → Forest.Heard)
    (hLI : LeftIsP Mg claim Wv g before a x plJ x0 gOf) (hleftQ : Pub.left (2 * g + 1) ∈ Q)
    (hObj : ∀ (t : S) (F : Fork) (g₁ : Forest.Heard), t.fork? = some F → t.lookHeard? = some g₁ →
      (∀ f ∈ g₁.rows.toList, f.ents = #[]) → (D.Rd (2 * g + 1)).forms 1 "objects" t = some { forms := g₁.rows.toList, late := [] })
    (hGst : ∀ (t : S) (F : Fork), t.fork? = some F → (D.Rd (2 * g + 1)).forms 1 "guests" t = some { forms := [], late := [] })
    (hbare : ∀ (π : Pp) (a' : S × Fr.E.Str), onT D.N Mg links π Fr pl O Q a' → ∀ f ∈ ((gOf π) a').rows.toList, f.ents = #[])
    (hrO : D.runs (2 * g + 1) 2 "objects" = [(1, "objects"), (1, "guests")])
    (L : K5Left Mg Mg0 D cs smp decT in0 D13 bs claim Wv g before a x Dn rad Ex Wp α plJ I R' links pl O Q states) : K5Left Mg Mg0 D cs smp decT in0 D13 bs claim Wv g before a x Dn rad Ex Wp α plJ I R' links pl O Q states :=
  { L with objLate := (objLate_plus Mg D claim Wv g before a x plJ links pl O Q x0 gOf hLI hleftQ hObj hGst hbare hrO) }

end

end H2K5.Door

#print axioms H2K5.Door.runs3_plus
#print axioms H2K5.Door.runsJ_plus
#print axioms H2K5.Door.runsO_plus
#print axioms H2K5.Door.okAll_plus
#print axioms H2K5.Door.st2_plus
#print axioms H2K5.Door.rds_plus
#print axioms H2K5.Door.objR_plus
#print axioms H2K5.Door.objLate_plus
#print axioms H2K5.Door.left_runs3_fits
#print axioms H2K5.Door.left_runsJ_fits
#print axioms H2K5.Door.left_okAll_fits
#print axioms H2K5.Door.left_st2_fits
#print axioms H2K5.Door.left_rds_fits
#print axioms H2K5.Door.left_objR_fits
#print axioms H2K5.Door.left_objLate_fits
