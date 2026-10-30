-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05KeysPaid.lean: kind K5: THE CLAUSE "keys" OF K5FillIns (Att/K05Closes.lean) WITH ITS TWO INNER PREMISES PAID, at the lookups' own letters (Johnson/Desc/First/Look/K3AttGoodIn.lean: attMs · attMu · attNu):
  hKF (each call's key vector at its point is the typed key form at the rule values): hKF_at (Att/K05KeysKF.lean) · hν (the lookup's reading of the places at the masks is the kind's mask row): mask_is_nu (Att/K05PlacesNu.lean).
Main names: keys_of_todo_paid (its conclusion is the lookups' attWorthKeys, letter for letter) · k5FillIns_keys_paid (the clause's text) · keys_paid_fits (Lean's own check that the conclusion is the field's type: it calls the theorem itself and lays what
it returns as the field of a given structure; it proves nothing new).
PREMISES OF k5FillIns_keys_paid, ALL: H : AttOK · hF : Road.L5.CallsFit S x.fs (public data) · leftIs (K5AtMg's own field) · hleftQ · hι (the promise's places at the masks) · hms (the pin's part is the lookups' tuple of messages) · hW (K3WorthKeys … gives
the meaning's worth m 2 "keys": an implication at values).
IS IT EMPTY HERE? Implications.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05KeysClause
import Johnson.Desc.First.Att.K05KeysKF
import Johnson.Desc.First.Att.K05PlacesNu

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road
open OnBytes.Road.L5 (dimOf callsOf)
open VerifiableInference.Desc.First.Look (Sent attCaller attSg JAtt AttOK enMask attCells attLay sigListCalls att_ok)
open VerifiableInference.Desc.Sound (Frame strsOf MsgT)
open VerifiableInference.Desc (Place Wit)
open VerifiableInference.Desc.First (Item Pub Meaning Numbers ModelPart)
open VerifiableInference.OnPublicFiles (K3WorthKeys keysAt attMs attMu attNu)

section
variable {Cells Tok : Type} (x : VerifiableInference.Desc.First.Look.Place) (S : Attention.Shape) (tl : HTailF2) (D : Sent)
  (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
  (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)) → Cb.Gl.E) (ns : ℕ) (N : Nums)

/-- **The lookup's item worth "keys" at the lookups' own letters, from the kind's relation in front.** -/
theorem keys_of_todo_paid {S₀ : Type} {set : Params.Setting} (H : AttOK set x S tl D rad) (hF : OnBytes.Road.L5.CallsFit S x.fs)
    {fork : S₀ → Option Fork} {heard : S₀ → Option Forest.Heard} {ι : Fo.Pl → Option (JAtt x.ns tl)}
    (hι : ∀ j, ι (.mask j) = some (enMask x.ns tl j)) {Q : Fork → Prop}
    {x0 : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl))} {g₀ : Forest.Heard} {s : S₀}
    (hl : K3LeftOutIs fork heard x.fs x.lm x.F.next ι Q x0 g₀ s)
    (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ) (w : Wit Cells Tok MsgT)
    (hT : TodoJoin x S tl D rad Ex Wp α ns N x0 (attMs x D rad seatT arr w)) :
    K3WorthKeys fork heard x.fs x.lm x.F.next (attNu x S tl D rad seatT arr)
      (fun w => forK Cb.Gl.E (attLay S x.fs x.lm x.F.next x.ns tl) () (zext (attMu x tl D rad seatT arr w))) s w := by
  have hl' := hl
  obtain ⟨F, F₁, rs₀, _, hn, L, _, _, T⟩ := hl'
  have hI₀ := L.heardIs
  rw [hn] at hI₀ T
  exact keys_of_todo x S tl D rad Ex Wp α ns N H hι hl (attNu x S tl D rad seatT arr) _ (attMs x D rad seatT arr) w
    (fun j hj => (mask_is_nu (x := x) (A := S) (tl := tl) (D := D) (rad := rad) (seatT := seatT) (arr := arr) Ex Wp α ns N w j hj).symm)
    (hKF_at x S tl D rad Ex Wp α ns N (att_ok Ex Wp H (attCaller x S tl D rad Ex Wp) (List.mem_singleton.2 rfl)) H.four hF T hI₀
      seatT arr w) hT

/-- **The clause "keys" of K5FillIns, its inner premises paid.** -/
theorem k5FillIns_keys_paid {Pp Cl : Type} {Fr : Frame} {set : Params.Setting} (claim : Aff → Cl)
    (Mg : Meaning Pp (Wit Cells Tok MsgT)) (Nm : Numbers) (links : List ModelPart) (π : Pp) (m : ℕ) (pl : Place) (O : List Item)
    (Q : List Pub) (H : AttOK set x S tl D rad) (hF : OnBytes.Road.L5.CallsFit S x.fs)
    (x0 : First.S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl))) (gOf : First.S × Fr.E.Str → Forest.Heard)
    (ι : Fo.Pl → Option (JAtt x.ns tl)) (hι : ∀ j, ι (.mask j) = some (enMask x.ns tl j)) (Qr : Fork → Prop)
    (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
    (part : Wit Cells Tok MsgT → (attSg x D rad).Msg) (hms : ∀ w, attMs x D rad seatT arr w = part w)
    (leftIs : ∀ a' : First.S × Fr.E.Str, Mg.pubP (.left m) (π, a'.1) →
      K3LeftOutIs (VerifiableInference.Desc.K3.seatCalls claim).fork (VerifiableInference.Desc.K3.seatCalls claim).heard
        x.fs x.lm x.F.next ι Qr (x0 a') (gOf a') a'.1)
    (hleftQ : Pub.left m ∈ Q)
    (hW : ∀ (s : First.S) y w,
      K3WorthKeys (VerifiableInference.Desc.K3.seatCalls claim).fork (VerifiableInference.Desc.K3.seatCalls claim).heard
        x.fs x.lm x.F.next (attNu x S tl D rad seatT arr)
        (fun w => forK Cb.Gl.E (attLay S x.fs x.lm x.F.next x.ns tl) () (zext (attMu x tl D rad seatT arr w))) s w →
      Mg.worth m 2 "keys" (π, s) y w) :
    ∀ a' w, onT Nm Mg links π Fr pl O Q a' → TodoJoin x S tl D rad Ex Wp α ns N (x0 a') (part w) →
      Mg.worth m 2 "keys" (π, a'.1) (strsOf Fr a'.2) w := fun a' w hon hT =>
  hW a'.1 _ w (keys_of_todo_paid x S tl D rad Ex Wp α ns N H hF hι (leftIs a' (onAt_pubP hon.1 hon.2 _ hleftQ)) seatT arr w
    (by rw [hms]; exact hT))

theorem keys_paid_fits {Pp Cl : Type} {Fr : Frame} {set : Params.Setting} (claim : Aff → Cl)
    (Mg : Meaning Pp (Wit Cells Tok MsgT)) (Nm : Numbers) (links : List ModelPart) (π : Pp) (m : ℕ) (pl : Place) (O : List Item)
    (Q : List Pub) (H : AttOK set x S tl D rad) (hF : OnBytes.Road.L5.CallsFit S x.fs)
    (x0 : First.S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl))) (gOf : First.S × Fr.E.Str → Forest.Heard)
    (ι : Fo.Pl → Option (JAtt x.ns tl)) (hι : ∀ j, ι (.mask j) = some (enMask x.ns tl j)) (Qr : Fork → Prop)
    (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
    (part : Wit Cells Tok MsgT → (attSg x D rad).Msg) (hms : ∀ w, attMs x D rad seatT arr w = part w)
    (leftIs : ∀ a' : First.S × Fr.E.Str, Mg.pubP (.left m) (π, a'.1) →
      K3LeftOutIs (VerifiableInference.Desc.K3.seatCalls claim).fork (VerifiableInference.Desc.K3.seatCalls claim).heard
        x.fs x.lm x.F.next ι Qr (x0 a') (gOf a') a'.1)
    (hleftQ : Pub.left m ∈ Q)
    (hW : ∀ (s : First.S) y w,
      K3WorthKeys (VerifiableInference.Desc.K3.seatCalls claim).fork (VerifiableInference.Desc.K3.seatCalls claim).heard
        x.fs x.lm x.F.next (attNu x S tl D rad seatT arr)
        (fun w => forK Cb.Gl.E (attLay S x.fs x.lm x.F.next x.ns tl) () (zext (attMu x tl D rad seatT arr w))) s w →
      Mg.worth m 2 "keys" (π, s) y w)
    (base : ℕ) (own : Params.AttentionRounds)
    (I : K5FillIns Mg Nm links π Fr base m pl O Q own x S tl D rad Ex Wp α ns N x0 part) :
    K5FillIns Mg Nm links π Fr base m pl O Q own x S tl D rad Ex Wp α ns N x0 part :=
  { I with keys := (k5FillIns_keys_paid x S tl D rad Ex Wp α ns N claim Mg Nm links π m pl O Q H hF x0 gOf ι hι Qr seatT arr part hms
      leftIs hleftQ hW) }

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.keys_of_todo_paid
#print axioms VerifiableInference.Desc.First.Att.P.k5FillIns_keys_paid
#print axioms VerifiableInference.Desc.First.Att.P.keys_paid_fits
