-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Door/Law/K5LeftFitsF.lean: kind K5: THE FIELD planesIn OF K5Left (Door/Law/K5AtEqsPlus.lean: the public test tied to the lookup argument's run "planes" holds at the verifier's state after the kind's sub-protocol) AS A THEOREM AT THE STRUCTURE's OWN LETTERS, with Lean's own
check of the field's type.
THE OTHER FILES' SHARE IS CALLED, NOT ASSUMED: ONE premise on the verifier's state, under the table's promise in front: hleft: the test leftAtB (Johnson/Desc/First/FillBare.lean) says yes at what the
lookup argument has left and the ledger in front (a public test of the wider filling is to pay it). hU3 is not asked either: it is drawn from the door's yes (u3There_of_sheet, Door/Law/ReadsThereTie.lean).
THE JOIN: formsInT_planes_left (Att/K05PlanesLeft.lean) · leftAtB_later (Door/Law/K5FillPlus.lean: the test rides over the kind's hearing) · readers_ret_plan (Att/K05ReadersRet.lean) · pubAll_formsInT.
IS IT EMPTY HERE? An implication: no member of K5Left is shown.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5LeftFitsB
import Johnson.Desc.First.Att.Door.Law.ReadsThereTie
import Johnson.Desc.First.Att.Door.Law.K5FillPlus
import Johnson.Desc.First.Att.K05PlanesLeft
import Johnson.Desc.First.Att.K05ReadersRet
import Johnson.Desc.First.PubAllAt

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
open VerifiableInference.Desc.First.Look (bornAt keptAt)
open VerifiableInference.Desc.K9 (statesOfLink readersOfLink LinkHoles)

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

/-- What the lookup argument's sub-protocol leaves has the planes' claims not yet made. FROM PadLeft ALONE: left_unpaid (Johnson/Top/H/Keep/K3LeftWindow.lean) says the like of all three debts from its K3Left; the sentence that the law's premise LeftIsP
hands out is K3LeftIs, another structure with the same field padLeft: so this stays. -/
theorem unpaid_planes_of_left {h : Forest.Shape} {F F' : Fork} {g₁ : Forest.Heard} (L : _root_.Fo.PadLeft h F F' g₁) :
    K3.unpaid F' g₁.owedPlanes = true := by
  unfold K3.unpaid
  rw [L.owed, L.owedAt.2.1]
  simp [Array.getElem_push]

theorem planesIn_plus {base : Pub → Pp × S → Bool} (hpub : Mg.pub = pubAll D base) (hxl : x.link = 2 * g + 1)
    (hrP : D.runs (2 * g + 1) 2 "planes" = [(1, "planes")])
    (H : LinkHoles) (Lk : Link S Claim) (hRd : D.Rd (2 * g + 1) = readersOfLink H Lk) {same : S → S → Bool} (claimC : Aff → Claim)
    (hcl : ∀ f, (claimC f).form = f ∧ (claimC f).runs.isEmpty = true ∧ (claimC f).eqFirst.isNone = true) (lm : ℕ) {nm : String}
    (hL : ((statesOfLink Lk 1).find? fun c => c.1 == "planes") = some (guardC same
      (nm, K3.planesRun (K3.seatCalls claimC) lm (readersOfO a))))
    (hsame : ∀ s t : S, t.out = s.out → same s t = true)
    (hRet : ∀ (π : Pp) (s : S) (y : Fr.E.Str) (att : AttOwn) (hd : Heard) (G : Fork) (rs : List Fmt.RoundView),
      onAt D.N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none → s.here = .att att →
      hear (parO Wv (2 * g + 1) a before).own (att.F, rs, 0) = some (hd, G, [], 0) → RunsReturn a s att hd G)
    (x0 : Pp → S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl))) (gOf : Pp → S × Fr.E.Str → Forest.Heard)
    (hLI : LeftIsP Mg claim Wv g before a x plJ x0 gOf) (hleftQ : Pub.left (2 * g + 1) ∈ Q)
    (hA : Wv.A[x.link / 2]? = some a) (hOP : K5Law.OfPlan a) {ps : List (ℕ × (ℕ × ℕ))}
    {qs : List (ℕ × OracleShape)} {hi : ℕ}
    (hdoor : ∀ (π : Pp) (a' : S × Fr.E.Str), onT D.N Mg links π Fr pl O Q a' →
      DoorYes Wv x Dn (bornAt Dn x.link) (keptAt Dn x.link).length (D.N.sent x.link 0) ps qs hi ((gOf π) a') a'.1)
    (hPl : Look.planesOk x.fs (parCOf a).geo.lmb = true) (hPos : K5Law.PosG (geoOf a.S))
    (hn : x.fs.NC * 2 ^ (x.fs.kT + 5 - (parCOf a).geo.lmb) ≤
      (a.seam.tl.mats.getD (a.S.cf.NAs + 2) {}).k * ((a.seam.tl.mats.getD (a.S.cf.NAs + 2) {}).m / 2 ^ a.S.cf.lmb))
    (hlm : lm = (parCOf a).geo.lmb)
    (hleft : ∀ (π : Pp) (a' : S × Fr.E.Str), onT D.N Mg links π Fr pl O Q a' → ∀ att, a'.1.here = .att att →
      FillBare.leftAtB ((gOf π) a') att.F = true) :
    ∀ π : Pp, ∀ (s : S) (y : Fr.E.Str) (att : AttOwn) (hd : Heard) (G : Fork) (rs : List Fmt.RoundView),
      onAt D.N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none → s.here = .att att →
      hear (parO Wv (2 * g + 1) a before).own (att.F, rs, 0) = some (hd, G, [], 0) →
      Mg.pub (.formsInT (2 * g + 1) 2 "planes") (π, behind s att hd G) = true := by
  intro π s y att hd G rs hon hm e hh
  have Y := hdoor π (s, y) ⟨hon, hm⟩
  have Fa := frontAll_of_door hA hOP Y
  have led : seatSO.ledger s = some att.F := by
    show (match s.here with | .att a => some a.F | _ => none) = _
    rw [e]
  have hz : Sized att.F := (Fa.ledger att.F led).1
  obtain ⟨i, K, _, _, _, _, _, _, hin, _⟩ := hRet π s y att hd G rs hon hm e hh
  have hLf := hLI π (s, y) (onAt_pubP hon hm _ hleftQ)
  obtain ⟨_, F', _, _, _, Lf, e1, e2, _⟩ := hLf
  have hshape : ((gOf π) (s, y)).shape = x.fs := Lf.shape
  obtain rfl : F' = att.F := Option.some.inj ((show s.fork? = some F' from e2).symm.trans (fork_front e))
  have hlk : att.lookHeard = some ((gOf π) (s, y)) := by
    have e1' : s.lookHeard? = some ((gOf π) (s, y)) := e1
    rw [lookHeard_front e] at e1'
    exact e1'
  have U : U3There (D.N.sent (2 * g + 1) 0) s att (parCOf a) := by
    obtain ⟨L₀, hL₀, hl₀, _⟩ := Y.link
    obtain rfl : att.L = L₀ := Option.some.inj ((link_front e).symm.trans hL₀)
    rw [← hxl]
    exact u3There_of_sheet Wv _ s att e a (by rw [hl₀]; exact hA) Y.reads
  obtain ⟨eg, _, hK, _, _, lk, _, _, _, ht⟩ := inOf_behind hin
  obtain ⟨_, bl⟩ := hear_below hh hz
  have lt : _root_.Fo.Later att.F G := by
    obtain ⟨_, _, _, _, _, _, st⟩ := hear_said hh hz
    exact ⟨bl.1, bl.ns, fun j hj => by
      obtain ⟨a₁, b₁, d₁⟩ := st j _ _ ⟨hj, rfl, rfl⟩
      exact ⟨a₁, b₁, d₁⟩⟩
  have hW : (parCOf a).nW ≤ K := by
    obtain ⟨T, hT, _, hw⟩ := U.tree
    rw [bl.trees, hT] at hK
    obtain rfl : T.K = K := Option.some.inj hK
    exact hw
  rw [← eg] at ht
  rw [hpub, pubAll_formsInT, hrP]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [hRd]
  refine formsInT_planes_left H Lk _ claimC hcl a lm hh hz hin U hlk hL hsame (by rw [unpaid_below bl]; exact unpaid_planes_of_left Lf.padLeft)
    (leftAtB_later lt bl (hleft π (s, y) ⟨hon, hm⟩ att e)) (by rw [hshape, hlm]; exact hPl) (fun r hr => ?_)
  have R := readers_ret_plan (n := x.fs.NC * 2 ^ (x.fs.kT + 5 - (parCOf a).geo.lmb)) hin hr (K5Law.len_in ht) hW (S := a.S) (tl := a.seam.tl) eg ht (eg ▸ hPos) hn
  rw [hshape, hlm]
  exact R

theorem left_planesIn_fits {base : Pub → Pp × S → Bool} (hpub : Mg.pub = pubAll D base) (hxl : x.link = 2 * g + 1)
    (hrP : D.runs (2 * g + 1) 2 "planes" = [(1, "planes")])
    (H : LinkHoles) (Lk : Link S Claim) (hRd : D.Rd (2 * g + 1) = readersOfLink H Lk) {same : S → S → Bool} (claimC : Aff → Claim)
    (hcl : ∀ f, (claimC f).form = f ∧ (claimC f).runs.isEmpty = true ∧ (claimC f).eqFirst.isNone = true) (lm : ℕ) {nm : String}
    (hL : ((statesOfLink Lk 1).find? fun c => c.1 == "planes") = some (guardC same
      (nm, K3.planesRun (K3.seatCalls claimC) lm (readersOfO a))))
    (hsame : ∀ s t : S, t.out = s.out → same s t = true)
    (hRet : ∀ (π : Pp) (s : S) (y : Fr.E.Str) (att : AttOwn) (hd : Heard) (G : Fork) (rs : List Fmt.RoundView),
      onAt D.N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none → s.here = .att att →
      hear (parO Wv (2 * g + 1) a before).own (att.F, rs, 0) = some (hd, G, [], 0) → RunsReturn a s att hd G)
    (x0 : Pp → S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl))) (gOf : Pp → S × Fr.E.Str → Forest.Heard)
    (hLI : LeftIsP Mg claim Wv g before a x plJ x0 gOf) (hleftQ : Pub.left (2 * g + 1) ∈ Q)
    (hA : Wv.A[x.link / 2]? = some a) (hOP : K5Law.OfPlan a) {ps : List (ℕ × (ℕ × ℕ))}
    {qs : List (ℕ × OracleShape)} {hi : ℕ}
    (hdoor : ∀ (π : Pp) (a' : S × Fr.E.Str), onT D.N Mg links π Fr pl O Q a' →
      DoorYes Wv x Dn (bornAt Dn x.link) (keptAt Dn x.link).length (D.N.sent x.link 0) ps qs hi ((gOf π) a') a'.1)
    (hPl : Look.planesOk x.fs (parCOf a).geo.lmb = true) (hPos : K5Law.PosG (geoOf a.S))
    (hn : x.fs.NC * 2 ^ (x.fs.kT + 5 - (parCOf a).geo.lmb) ≤
      (a.seam.tl.mats.getD (a.S.cf.NAs + 2) {}).k * ((a.seam.tl.mats.getD (a.S.cf.NAs + 2) {}).m / 2 ^ a.S.cf.lmb))
    (hlm : lm = (parCOf a).geo.lmb)
    (hleft : ∀ (π : Pp) (a' : S × Fr.E.Str), onT D.N Mg links π Fr pl O Q a' → ∀ att, a'.1.here = .att att →
      FillBare.leftAtB ((gOf π) a') att.F = true)
    (L : K5Left Mg Mg0 D cs smp decT in0 D13 bs claim Wv g before a x Dn rad Ex Wp α plJ I R' links pl O Q states) : K5Left Mg Mg0 D cs smp decT in0 D13 bs claim Wv g before a x Dn rad Ex Wp α plJ I R' links pl O Q states :=
  { L with
    planesIn := (planesIn_plus Mg D claim Wv g before a x Dn plJ links pl O Q hpub hxl hrP H Lk hRd claimC hcl lm hL hsame hRet x0 gOf hLI hleftQ
      hA hOP hdoor hPl hPos hn hlm hleft) }

end

end H2K5.Door

#print axioms H2K5.Door.unpaid_planes_of_left
#print axioms H2K5.Door.planesIn_plus
#print axioms H2K5.Door.left_planesIn_fits
