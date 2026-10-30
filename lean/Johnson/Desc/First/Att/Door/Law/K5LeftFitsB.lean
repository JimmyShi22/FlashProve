-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Door/Law/K5LeftFitsB.lean: kind K5: FIVE FIELDS OF K5Left (Door/Law/K5AtEqsPlus.lean: what is left of K5AtMg at the composed meaning): runsRet · objects · small · constr · ins: EACH AS A THEOREM AT THE STRUCTURE's OWN LETTERS, and Lean's own check that the
theorem's conclusion is the field's type.
For each field two theorems: ‹field›_plus: the payer, called at the common letters, concluding the field's text, its premises given directly · left_‹field›_fits (L : K5Left …) : K5Left … := { L with ‹field› := ‹field›_plus … }: it proves nothing new: Lean refuses it unless the types fit.
And small joins: runsAt_own | runsAt_join | runsAt_objects | runsAt_planes (the table's own map of names at an attention segment, by its text) · r123_of_runs (the three memberships r1 · r2 · r3 of the road of "behind") · fill_of_door: every slot that the lookup argument's last claim names is filled in the ledger in front: from the door's yes.
THE PAYERS: k5Left_runsRet (Att/K05RunsReturn.lean) with guard_gives_written (Att/GuardNLaw.lean) and frontAll_of_door (Att/K05FrontOfDoor.lean) · k5FillRel_objects (Att/K05ObjectsBack.lean) · k5FillRel_small | k5FillRel_constr (Att/K05ConstrBack.lean) · k5FillIns_idn
(Att/K05IdnClause.lean) · k5FillIns_rider (Att/K05RiderAt.lean) · k5FillIns_keys_paid (Att/K05KeysPaid.lean).
EVERY PREMISE THAT A THEOREM HERE STILL TAKES IS A DEBT WITH AN OWNER: they are listed, one by one, in the note that goes with this file.



IS IT EMPTY HERE? Implications: no member of K5Left is shown.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5AtEqsPlus
import Johnson.Desc.First.Att.Door.Law.FillK5Tie
import Johnson.Desc.First.Att.K05RunsReturn
import Johnson.Desc.First.Att.K05ObjectsBack
import Johnson.Desc.First.Att.K05ConstrBack
import Johnson.Desc.First.Att.K05IdnClause
import Johnson.Desc.First.Att.K05RiderAt
import Johnson.Desc.First.Att.K05KeysPaid
import Johnson.Desc.First.Att.K05FrontOfDoor
import Johnson.Desc.First.Att.GuardNLaw

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
open VerifiableInference.Desc.First.Look (AttOK bornAt keptAt attCells CellsAre attLay sigListCalls)
open VerifiableInference.OnPublicFiles (K3WorthKeys K3WorthRider attMs attMu attNu)
open VerifiableInference.Desc.K9 (Readers formsInT)
open OnBytes.Road.L5 (dimOf callsOf Zs cellsA)

/-! ## The table's runs at an attention segment -/

/-- The table's own map of names, at an attention segment: the item "own". -/
theorem runsAt_own {links : List ModelPart} {m : ℕ} (h : links[m]? = some .attention) :
    runsAt links m 3 "own" = [(2, "first"), (2, "keys"), (2, "second")] := by
  unfold runsAt
  rw [h]
  rfl

/-- The item "join". -/
theorem runsAt_join {links : List ModelPart} {m : ℕ} (h : links[m]? = some .attention) : runsAt links m 2 "join" = [(2, "join")] := by
  unfold runsAt
  rw [h]
  rfl

/-- The item "objects". -/
theorem runsAt_objects {links : List ModelPart} {m : ℕ} (h : links[m]? = some .attention) :
    runsAt links m 2 "objects" = [(1, "objects"), (1, "guests")] := by
  unfold runsAt
  rw [h]
  rfl

/-- The item "planes". -/
theorem runsAt_planes {links : List ModelPart} {m : ℕ} (h : links[m]? = some .attention) : runsAt links m 2 "planes" = [(1, "planes")] := by
  unfold runsAt
  rw [h]
  rfl

/-- **The three memberships that the road of "behind" spends**, from the two equations on the letter runs (K5Left's runs3 | runsJ). -/
theorem r123_of_runs {runs : ℕ → ℕ → String → List (ℕ × String)} {m : ℕ}
    (h3 : runs m 3 "own" = [(2, "first"), (2, "keys"), (2, "second")]) (hJ : runs m 2 "join" = [(2, "join")]) :
    (2, "first") ∈ runs m 3 "own" ∧ (2, "second") ∈ runs m 3 "own" ∧ (2, "join") ∈ runs m 2 "join" := by
  rw [h3, hJ]
  simp

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

/-! ## The small join -/

/-- **Every slot that the lookup argument's last claim names is filled in front**: from the door's yes: its fields look and heard hold all that is spent. -/
theorem fill_of_door {own : List (ℕ × ℕ)} {ps : List (ℕ × (ℕ × ℕ))} {qs : List (ℕ × OracleShape)} {hi kept : ℕ} {born : Array (ℕ × ℕ)}
    {gL : Forest.Heard} {s : S} (Y : DoorYes Wv x Dn born kept own ps qs hi gL s) {att : AttOwn} (e : s.here = .att att) :
    _root_.Fo.FilledA att.F gL.cEnd := by
  obtain ⟨a₁, _, gL', e₁, _, hl₁, _, _, hF⟩ := lookAtt_gives Y.look
  obtain rfl : att = a₁ := by
    have : Here.att att = Here.att a₁ := e.symm.trans e₁
    cases this
    rfl
  have hl₂ : att.lookHeard = some gL := by
    have := Y.heard
    unfold S.lookHeard? at this
    simp only [e] at this
    exact this
  obtain rfl : gL' = gL := Option.some.inj (hl₁.symm.trans hl₂)
  exact hF

/-! ## runsRet -/

include rad Ex Wp α in
theorem runsRet_plus (hP : PlanIs Wv) (h4 : Wv.p4 = true) (ha : Wv.A[g]? = some a) (hx : lookAt Wv (2 * g + 1) false = some x)
    (hG : k5GuardN Wv (2 * g + 1) g = true) (hb : planOk (parO Wv (2 * g + 1) a before) = true) (hc : claimsOkAtO a = true)
    (x0 : Pp → S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl))) (gOf : Pp → S × Fr.E.Str → Forest.Heard)
    (hLI : LeftIsP Mg claim Wv g before a x plJ x0 gOf) (hleftQ : Pub.left (2 * g + 1) ∈ Q)
    (hA : Wv.A[x.link / 2]? = some a) (hOP : K5Law.OfPlan a) {own : List (ℕ × ℕ)} {ps : List (ℕ × (ℕ × ℕ))}
    {qs : List (ℕ × OracleShape)} {hi : ℕ}
    (hdoor : ∀ (π : Pp) (a' : S × Fr.E.Str), onT D.N Mg links π Fr pl O Q a' →
      DoorYes Wv x Dn (bornAt Dn x.link) (keptAt Dn x.link).length own ps qs hi ((gOf π) a') a'.1) :
    ∀ π : Pp, ∀ (s : S) (y : Fr.E.Str) (att : AttOwn) (hd : Heard) (G : Fork) (rs : List Fmt.RoundView),
      onAt D.N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none → s.here = .att att →
      hear (parO Wv (2 * g + 1) a before).own (att.F, rs, 0) = some (hd, G, [], 0) → RunsReturn a s att hd G := by
  obtain ⟨x', A0, hx', ⟨pf, e⟩, Pb⟩ := guard_gives_written hP h4 g before Dn rad ha hG hb hc
  obtain rfl : x' = x := Option.some.inj (hx'.symm.trans hx)
  have eS : a.S = A0.S := by rw [e]
  have eF : a.fs = A0.fs := by rw [e]
  have elm : (parCOf A0).geo.lmb = (parCOf a).geo.lmb := by rw [e]; rfl
  exact k5Left_runsRet x' Dn rad Ex Wp claim α a.ns Pb eS eF elm D.N Mg links (2 * g + 1) pl O Q x0 gOf hLI hleftQ
    (fun π a' hon => frontAll_of_door hA hOP (hdoor π a' hon))
    (fun π a' _ hon e' => fill_of_door Wv x' Dn (hdoor π a' hon) e')

/-! ## objects -/

theorem objects_plus (x0 : Pp → S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl))) (gOf : Pp → S × Fr.E.Str → Forest.Heard)
    (hLI : LeftIsP Mg claim Wv g before a x plJ x0 gOf) (hleftQ : Pub.left (2 * g + 1) ∈ Q) (Rd : Readers) (St : Stated)
    (ownL : List (ℕ × ℕ)) (rdOf : Wit Cells Tok MsgT → ℕ × ℕ → MsgQ)
    (hObj : ∀ (t : S) (F : Fork) (g₁ : Forest.Heard), t.fork? = some F → t.lookHeard? = some g₁ →
      (∀ f ∈ g₁.rows.toList, f.ents = #[]) → Rd.forms 1 "objects" t = some { forms := g₁.rows.toList, late := [] })
    (hbare : ∀ (π : Pp) (a' : S × Fr.E.Str), onT D.N Mg links π Fr pl O Q a' → ∀ f ∈ ((gOf π) a').rows.toList, f.ents = #[])
    (hIn : ∀ (π : Pp) s y, onAt D.N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
      formsInT Rd ownL 1 "objects" s = true)
    (hMask : ∀ t Dt, (St.at1 t Dt).mask = Dt.mask)
    (hTo : ∀ (π : Pp) t y w, Mg.formsT (2 * g + 1) 2 "objects" (π, t) y w → formsTQ Rd St ownL 1 "objects" t (rdOf w))
    (hGst : ∀ (t : S) (F : Fork), t.fork? = some F → Rd.forms 1 "guests" t = some { forms := [], late := [] })
    (hFrom : ∀ (π : Pp) t y w, formsTQ Rd St ownL 1 "objects" t (rdOf w) → formsTQ Rd St ownL 1 "guests" t (rdOf w) →
      Mg.formsT (2 * g + 1) 2 "objects" (π, t) y w) :
    ∀ π : Pp, ∀ s att hd G rs y y' w, onAt D.N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none → s.here = .att att →
      hear (parO Wv (2 * g + 1) a before).own (att.F, rs, 0) = some (hd, G, [], 0) → SameBelow Fr bs y y' →
      Mg.formsT (2 * g + 1) 2 "objects" (π, behind s att hd G) (strsOf Fr y') w →
      Mg.formsT (2 * g + 1) 2 "objects" (π, s) (strsOf Fr y) w :=
  fun π => k5FillRel_objects claim Mg D.N links π bs (2 * g + 1) pl O Q (parO Wv (2 * g + 1) a before).own x.fs x.lm x.F.next _ _ (x0 π)
    (gOf π) (hLI π) hleftQ Rd St ownL rdOf hObj (hbare π) (hIn π) hMask (hTo π) hGst (hFrom π)

/-! ## small · constr -/

section Constr
variable {Ix : Type} (Hd : Cells → Ix → Prop) (bsW : ℕ → Wit Cells Tok MsgT → Prop)
  (dP : ℕ → Pp × S → Strs → Wit Cells Tok MsgT → Prop) (body : ℕ → First.Part → Ix → Pp × S → Strs → Wit Cells Tok MsgT → Prop)
  (hC : ∀ n p a₁ y w, Mg.constr n p a₁ y w ↔
    if p = .lookDigits then dP n a₁ y w
    else (p = .small → bsW n w) ∧ ∀ M i, decT y.cell a₁ = some M → Hd M i → body n p i a₁ y w)
  (hdecT : ∀ π c s a₁ h G, s.here = .att a₁ → decT c (π, behind s a₁ h G) = decT c (π, s))
include hC hdecT

theorem small_plus (hBs : ∀ i a₁ a₂ y y' w, body (2 * g + 1) .small i a₁ y w → body (2 * g + 1) .small i a₂ y' w) :
    ∀ π : Pp, ∀ s att hd G rs y y' w, onAt D.N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none → s.here = .att att →
      hear (parO Wv (2 * g + 1) a before).own (att.F, rs, 0) = some (hd, G, [], 0) → SameBelow Fr bs y y' →
      Mg.constr (2 * g + 1) .small (π, behind s att hd G) (strsOf Fr y') w → Mg.constr (2 * g + 1) .small (π, s) (strsOf Fr y) w :=
  fun π => k5FillRel_small Mg π bs decT (hdecT π) Hd bsW dP body hC D.N links (2 * g + 1) pl O Q (parO Wv (2 * g + 1) a before).own hBs

theorem constr_plus
    (hD : ∀ (π : Pp) n, n ≠ 2 * g + 1 → ∀ s att hd G rs (y y' : Fr.E.Str) w, onAt D.N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none → s.here = .att att →
      hear (parO Wv (2 * g + 1) a before).own (att.F, rs, 0) = some (hd, G, [], 0) → SameBelow Fr bs y y' →
      dP n (π, behind s att hd G) (strsOf Fr y') w → dP n (π, s) (strsOf Fr y) w)
    (hB : ∀ (π : Pp) n p, n ≠ 2 * g + 1 → ∀ i s att hd G rs (y y' : Fr.E.Str) w, onAt D.N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none → s.here = .att att →
      hear (parO Wv (2 * g + 1) a before).own (att.F, rs, 0) = some (hd, G, [], 0) → SameBelow Fr bs y y' →
      body n p i (π, behind s att hd G) (strsOf Fr y') w → body n p i (π, s) (strsOf Fr y) w) :
    ∀ π : Pp, ∀ n p, n ≠ 2 * g + 1 → ∀ s att hd G rs y y' w, onAt D.N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none → s.here = .att att →
      hear (parO Wv (2 * g + 1) a before).own (att.F, rs, 0) = some (hd, G, [], 0) → SameBelow Fr bs y y' →
      Mg.constr n p (π, behind s att hd G) (strsOf Fr y') w → Mg.constr n p (π, s) (strsOf Fr y) w :=
  fun π => k5FillRel_constr Mg π bs decT (hdecT π) Hd bsW dP body hC D.N links (2 * g + 1) pl O Q (parO Wv (2 * g + 1) a before).own
    (hD π) (hB π)

theorem left_small_fits (hBs : ∀ i a₁ a₂ y y' w, body (2 * g + 1) .small i a₁ y w → body (2 * g + 1) .small i a₂ y' w)
    (L : K5Left Mg Mg0 D cs smp decT in0 D13 bs claim Wv g before a x Dn rad Ex Wp α plJ I R' links pl O Q states) : K5Left Mg Mg0 D cs smp decT in0 D13 bs claim Wv g before a x Dn rad Ex Wp α plJ I R' links pl O Q states :=
  { L with small := small_plus Mg D decT bs Wv g before a links pl O Q Hd bsW dP body hC hdecT hBs }

theorem left_constr_fits
    (hD : ∀ (π : Pp) n, n ≠ 2 * g + 1 → ∀ s att hd G rs (y y' : Fr.E.Str) w, onAt D.N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none → s.here = .att att →
      hear (parO Wv (2 * g + 1) a before).own (att.F, rs, 0) = some (hd, G, [], 0) → SameBelow Fr bs y y' →
      dP n (π, behind s att hd G) (strsOf Fr y') w → dP n (π, s) (strsOf Fr y) w)
    (hB : ∀ (π : Pp) n p, n ≠ 2 * g + 1 → ∀ i s att hd G rs (y y' : Fr.E.Str) w, onAt D.N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none → s.here = .att att →
      hear (parO Wv (2 * g + 1) a before).own (att.F, rs, 0) = some (hd, G, [], 0) → SameBelow Fr bs y y' →
      body n p i (π, behind s att hd G) (strsOf Fr y') w → body n p i (π, s) (strsOf Fr y) w)
    (L : K5Left Mg Mg0 D cs smp decT in0 D13 bs claim Wv g before a x Dn rad Ex Wp α plJ I R' links pl O Q states) : K5Left Mg Mg0 D cs smp decT in0 D13 bs claim Wv g before a x Dn rad Ex Wp α plJ I R' links pl O Q states :=
  { L with constr := constr_plus Mg D decT bs Wv g before a links pl O Q Hd bsW dP body hC hdecT hD hB }

end Constr

/-! ## ins -/

section Ins
variable {Ix : Type} (Hd : Cells → Ix → Prop) (bsW : ℕ → Wit Cells Tok MsgT → Prop)
  (dP : ℕ → Pp × S → Strs → Wit Cells Tok MsgT → Prop) (body : ℕ → First.Part → Ix → Pp × S → Strs → Wit Cells Tok MsgT → Prop)
  (hC : ∀ n p a₁ y w, Mg.constr n p a₁ y w ↔
    if p = .lookDigits then dP n a₁ y w
    else (p = .small → bsW n w) ∧ ∀ M i, decT y.cell a₁ = some M → Hd M i → body n p i a₁ y w)

include hC in
theorem ins_plus (Ex' : Iop.ExtSpec) (Wp' : Type) {set : Params.Setting} (H : AttOK set x a.S a.seam.tl Dn rad) (hF : OnBytes.Road.L5.CallsFit a.S x.fs)
    (hleftQ : Pub.left (2 * g + 1) ∈ Q) (Zof : Wit Cells Tok MsgT → Zs)
    (hCells : ∀ w, bsW (2 * g + 1) w → CellsAre x a.S a.seam.tl Dn rad (I.part w) (Zof w))
    (hBody : ∀ i a₁ y w,
      ((∀ k b g' n, (Inst.Model.AttSeg.Idn.at1 k b g' n).Valid (dimOf a.S) →
          Inst.Model.AttSeg.idnVal (dimOf a.S) (Inst.Model.AttSeg.castT (cellsA a.S (Zof w)) : Inst.Model.AttSeg.Raw → Cb.Gl.F) (.at1 k b g' n) = 0) ∧
        ∀ b g' n, (Inst.Model.AttSeg.Idn.at2 b g' n).Valid (dimOf a.S) →
          Inst.Model.AttSeg.idnVal (dimOf a.S) (Inst.Model.AttSeg.castT (cellsA a.S (Zof w)) : Inst.Model.AttSeg.Raw → Cb.Gl.F) (.at2 b g' n) = 0) →
      body (2 * g + 1) .idn i a₁ y w)
    (seatT : Fin (sigListCalls Dn rad x.link).length → ℕ × ℕ) (arrL : ℕ → ℕ → ℕ)
    (hms : ∀ w, attMs x Dn rad seatT arrL w = I.part w)
    (hWr : ∀ (π : Pp) (s : S) y w,
      K3WorthRider (K3.seatCalls claim).fork (K3.seatCalls claim).heard (VerifiableInference.Desc.First.Look.attRider x a.S a.seam.tl Dn rad Ex' Wp')
        x.lm x.F.next (fun _ => ()) (attMs x Dn rad seatT arrL) s w → Mg.worth (2 * g + 1) 2 "rider" (π, s) y w)
    (hWk : ∀ (π : Pp) (s : S) y w,
      K3WorthKeys (K3.seatCalls claim).fork (K3.seatCalls claim).heard x.fs x.lm x.F.next (attNu x a.S a.seam.tl Dn rad seatT arrL)
        (fun w => forK Cb.Gl.E (attLay a.S x.fs x.lm x.F.next x.ns a.seam.tl) () (zext (attMu x a.seam.tl Dn rad seatT arrL w))) s w →
      Mg.worth (2 * g + 1) 2 "keys" (π, s) y w)
    (hPl : ∀ π : Pp, ∀ s att hd G rs y y' w, onAt D.N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none → s.here = .att att →
      hear (parO Wv (2 * g + 1) a before).own (att.F, rs, 0) = some (hd, G, [], 0) → SameBelow Fr bs y y' →
      (∀ i ∈ [Item.formsT (2 * g + 1) 3 "own", .formsT (2 * g + 1) 2 "planes", .formsT (2 * g + 1) 2 "join", .pin (2 * g + 1) 0, .pinW,
          .constr (2 * g + 1) .small], i.holds D.N Mg (π, behind s att hd G) (strsOf Fr y') w) →
      Mg.worth (2 * g + 1) 2 "planes" (π, s) (strsOf Fr y) w) :
    ∀ x0 gOf, LeftIsP Mg claim Wv g before a x plJ x0 gOf → ∀ π : Pp,
      K5FillIns Mg D.N links π Fr bs (2 * g + 1) pl O Q (parO Wv (2 * g + 1) a before).own x a.S a.seam.tl Dn rad Ex Wp α a.ns
        (numsPlan (parO Wv (2 * g + 1) a before).own (x.F.next + Forest.elems x.fs)) (x0 π) I.part :=
  fun x0 gOf hLI π =>
    { idn := k5FillIns_idn Mg π decT Hd bsW dP body hC D.N links (2 * g + 1) pl O Q x a.S a.seam.tl Dn rad I.part Zof hCells hBody
      rider := k5FillIns_rider claim Mg D.N links π (2 * g + 1) pl O Q x a.S a.seam.tl Dn rad H Ex' Wp' (x0 π) (gOf π) _ _ I.part
        (attMs x Dn rad seatT arrL) hms (hLI π) hleftQ (hWr π)
      keys := k5FillIns_keys_paid x a.S a.seam.tl Dn rad Ex Wp α a.ns
        (numsPlan (parO Wv (2 * g + 1) a before).own (x.F.next + Forest.elems x.fs)) claim Mg D.N links π (2 * g + 1) pl O Q H hF (x0 π) (gOf π)
        _ (fun _ => rfl) _ seatT arrL I.part hms (hLI π) hleftQ (hWk π)
      planes := hPl π }

include hC in
theorem left_ins_fits (Ex' : Iop.ExtSpec) (Wp' : Type) {set : Params.Setting} (H : AttOK set x a.S a.seam.tl Dn rad) (hF : OnBytes.Road.L5.CallsFit a.S x.fs)
    (hleftQ : Pub.left (2 * g + 1) ∈ Q) (Zof : Wit Cells Tok MsgT → Zs)
    (hCells : ∀ w, bsW (2 * g + 1) w → CellsAre x a.S a.seam.tl Dn rad (I.part w) (Zof w))
    (hBody : ∀ i a₁ y w,
      ((∀ k b g' n, (Inst.Model.AttSeg.Idn.at1 k b g' n).Valid (dimOf a.S) →
          Inst.Model.AttSeg.idnVal (dimOf a.S) (Inst.Model.AttSeg.castT (cellsA a.S (Zof w)) : Inst.Model.AttSeg.Raw → Cb.Gl.F) (.at1 k b g' n) = 0) ∧
        ∀ b g' n, (Inst.Model.AttSeg.Idn.at2 b g' n).Valid (dimOf a.S) →
          Inst.Model.AttSeg.idnVal (dimOf a.S) (Inst.Model.AttSeg.castT (cellsA a.S (Zof w)) : Inst.Model.AttSeg.Raw → Cb.Gl.F) (.at2 b g' n) = 0) →
      body (2 * g + 1) .idn i a₁ y w)
    (seatT : Fin (sigListCalls Dn rad x.link).length → ℕ × ℕ) (arrL : ℕ → ℕ → ℕ)
    (hms : ∀ w, attMs x Dn rad seatT arrL w = I.part w)
    (hWr : ∀ (π : Pp) (s : S) y w,
      K3WorthRider (K3.seatCalls claim).fork (K3.seatCalls claim).heard (VerifiableInference.Desc.First.Look.attRider x a.S a.seam.tl Dn rad Ex' Wp')
        x.lm x.F.next (fun _ => ()) (attMs x Dn rad seatT arrL) s w → Mg.worth (2 * g + 1) 2 "rider" (π, s) y w)
    (hWk : ∀ (π : Pp) (s : S) y w,
      K3WorthKeys (K3.seatCalls claim).fork (K3.seatCalls claim).heard x.fs x.lm x.F.next (attNu x a.S a.seam.tl Dn rad seatT arrL)
        (fun w => forK Cb.Gl.E (attLay a.S x.fs x.lm x.F.next x.ns a.seam.tl) () (zext (attMu x a.seam.tl Dn rad seatT arrL w))) s w →
      Mg.worth (2 * g + 1) 2 "keys" (π, s) y w)
    (hPl : ∀ π : Pp, ∀ s att hd G rs y y' w, onAt D.N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none → s.here = .att att →
      hear (parO Wv (2 * g + 1) a before).own (att.F, rs, 0) = some (hd, G, [], 0) → SameBelow Fr bs y y' →
      (∀ i ∈ [Item.formsT (2 * g + 1) 3 "own", .formsT (2 * g + 1) 2 "planes", .formsT (2 * g + 1) 2 "join", .pin (2 * g + 1) 0, .pinW,
          .constr (2 * g + 1) .small], i.holds D.N Mg (π, behind s att hd G) (strsOf Fr y') w) →
      Mg.worth (2 * g + 1) 2 "planes" (π, s) (strsOf Fr y) w)
    (L : K5Left Mg Mg0 D cs smp decT in0 D13 bs claim Wv g before a x Dn rad Ex Wp α plJ I R' links pl O Q states) : K5Left Mg Mg0 D cs smp decT in0 D13 bs claim Wv g before a x Dn rad Ex Wp α plJ I R' links pl O Q states :=
  { L with
    ins := (ins_plus Mg D decT bs claim Wv g before a x Dn rad Ex Wp α plJ I links pl O Q Hd bsW dP body hC Ex' Wp' H hF hleftQ Zof hCells hBody seatT
      arrL hms hWr hWk hPl) }

end Ins

/-! ## Lean's own checks of the fields' types -/

theorem left_runsRet_fits (hP : PlanIs Wv) (h4 : Wv.p4 = true) (ha : Wv.A[g]? = some a) (hx : lookAt Wv (2 * g + 1) false = some x)
    (hG : k5GuardN Wv (2 * g + 1) g = true) (hb : planOk (parO Wv (2 * g + 1) a before) = true) (hc : claimsOkAtO a = true)
    (x0 : Pp → S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl))) (gOf : Pp → S × Fr.E.Str → Forest.Heard)
    (hLI : LeftIsP Mg claim Wv g before a x plJ x0 gOf) (hleftQ : Pub.left (2 * g + 1) ∈ Q)
    (hA : Wv.A[x.link / 2]? = some a) (hOP : K5Law.OfPlan a) {own : List (ℕ × ℕ)} {ps : List (ℕ × (ℕ × ℕ))}
    {qs : List (ℕ × OracleShape)} {hi : ℕ}
    (hdoor : ∀ (π : Pp) (a' : S × Fr.E.Str), onT D.N Mg links π Fr pl O Q a' →
      DoorYes Wv x Dn (bornAt Dn x.link) (keptAt Dn x.link).length own ps qs hi ((gOf π) a') a'.1)
    (L : K5Left Mg Mg0 D cs smp decT in0 D13 bs claim Wv g before a x Dn rad Ex Wp α plJ I R' links pl O Q states) : K5Left Mg Mg0 D cs smp decT in0 D13 bs claim Wv g before a x Dn rad Ex Wp α plJ I R' links pl O Q states :=
  { L with
    runsRet := (runsRet_plus Mg D claim Wv g before a x Dn rad Ex Wp α plJ links pl O Q hP h4 ha hx hG hb hc x0 gOf hLI hleftQ
      hA hOP hdoor) }

theorem left_objects_fits (x0 : Pp → S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl))) (gOf : Pp → S × Fr.E.Str → Forest.Heard)
    (hLI : LeftIsP Mg claim Wv g before a x plJ x0 gOf) (hleftQ : Pub.left (2 * g + 1) ∈ Q) (Rd : Readers) (St : Stated)
    (ownL : List (ℕ × ℕ)) (rdOf : Wit Cells Tok MsgT → ℕ × ℕ → MsgQ)
    (hObj : ∀ (t : S) (F : Fork) (g₁ : Forest.Heard), t.fork? = some F → t.lookHeard? = some g₁ →
      (∀ f ∈ g₁.rows.toList, f.ents = #[]) → Rd.forms 1 "objects" t = some { forms := g₁.rows.toList, late := [] })
    (hbare : ∀ (π : Pp) (a' : S × Fr.E.Str), onT D.N Mg links π Fr pl O Q a' → ∀ f ∈ ((gOf π) a').rows.toList, f.ents = #[])
    (hIn : ∀ (π : Pp) s y, onAt D.N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
      formsInT Rd ownL 1 "objects" s = true)
    (hMask : ∀ t Dt, (St.at1 t Dt).mask = Dt.mask)
    (hTo : ∀ (π : Pp) t y w, Mg.formsT (2 * g + 1) 2 "objects" (π, t) y w → formsTQ Rd St ownL 1 "objects" t (rdOf w))
    (hGst : ∀ (t : S) (F : Fork), t.fork? = some F → Rd.forms 1 "guests" t = some { forms := [], late := [] })
    (hFrom : ∀ (π : Pp) t y w, formsTQ Rd St ownL 1 "objects" t (rdOf w) → formsTQ Rd St ownL 1 "guests" t (rdOf w) →
      Mg.formsT (2 * g + 1) 2 "objects" (π, t) y w)
    (L : K5Left Mg Mg0 D cs smp decT in0 D13 bs claim Wv g before a x Dn rad Ex Wp α plJ I R' links pl O Q states) : K5Left Mg Mg0 D cs smp decT in0 D13 bs claim Wv g before a x Dn rad Ex Wp α plJ I R' links pl O Q states :=
  { L with
    objects := (objects_plus Mg D bs claim Wv g before a x plJ links pl O Q x0 gOf hLI hleftQ Rd St ownL rdOf hObj hbare hIn hMask hTo hGst
      hFrom) }

end

end H2K5.Door

#print axioms H2K5.Door.runsAt_own
#print axioms H2K5.Door.r123_of_runs
#print axioms H2K5.Door.fill_of_door
#print axioms H2K5.Door.runsRet_plus
#print axioms H2K5.Door.objects_plus
#print axioms H2K5.Door.small_plus
#print axioms H2K5.Door.constr_plus
#print axioms H2K5.Door.ins_plus
#print axioms H2K5.Door.left_runsRet_fits
#print axioms H2K5.Door.left_objects_fits
#print axioms H2K5.Door.left_small_fits
#print axioms H2K5.Door.left_constr_fits
#print axioms H2K5.Door.left_ins_fits
