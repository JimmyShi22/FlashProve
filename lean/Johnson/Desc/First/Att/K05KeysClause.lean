-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05KeysClause.lean: kind K5: WHAT THE KIND's RELATION IN FRONT SAYS OF THE JOIN (TodoJoin, Att/K05Closes.lean) GIVES THE LOOKUP's ITEM worth "keys" (Johnson/Top/H/K3Worth.lean: K3WorthKeys): the clause "keys" of K5FillIns.

The chain, at all rounds rs for which what the verifier has received from the lookup argument stands:
  claimJoin h lm first rs ν (keysAt h lm first Kv rs)
    = joinVal (joinPubOf h lm first rs) (the key vectors at their points) (AffK.val (cEndF, cEndC) ν)     [the lookups' claimJoin_joinVal, Johnson/Top/H/K3JoinVal.lean]
    = joinVal (Q.q x0) (the key vectors at their points) ((Q.ce x0).val msg)                               [join_typed, Att/K05KeysAt.lean]
    = joinVal (Q.q x0) (the typed key forms at the rule values) ((Q.ce x0).val msg)                        [hKF: A PREMISE HERE]
    = 0                                                                                                     [TodoJoin].
Main names: kfTodo (TodoJoin's own four values, by name) · keys_of_todo · k5FillIns_keys (the clause's text).
PREMISES: H : AttOK · the lookup's sharp promise (leftIs) · hι (the promise's places at the masks) · hν (ν reads the kind's mask row) · hKF : each call's key vector at its point is the typed key form at the rule values: the library's kfExt
  (Inst/Model/Att/KeyFormsExt/All.lean) with the lookups' attLay_K is its road: NOT PAID HERE · for the clause: hleftQ · hW (K3WorthKeys … gives the meaning's worth m 2 "keys": an implication at values) · hms.
THE LETTERS UNDER "FOR ALL": hKF: a', w free under the promise; rs fenced by HeardIs; c a call's number · hν: w, j: a law of two makes · hW, hms: laws of a make.
IS IT EMPTY HERE? Implications.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3Worth
import Johnson.Desc.First.Att.K05KeysAt
import Johnson.Desc.First.Att.K05Closes
import Johnson.Desc.First.Att.K05LeftSeats

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road
open OnBytes.Road.L5 (dimOf callsOf)
open VerifiableInference.Desc.First.Look (Sent attCaller attSg JAtt AttOK enMask attCells)
open VerifiableInference.Desc.Sound (Frame strsOf)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (Item Pub Meaning Numbers ModelPart)
open VerifiableInference.OnPublicFiles (K3WorthKeys K3OutKeys K3Keys keysAt)

section
variable (x : VerifiableInference.Desc.First.Look.Place) (S : Attention.Shape) (tl : HTailF2) (D : Sent)
  (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
  (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)) → Cb.Gl.E) (ns : ℕ) (N : Nums)

/-- TodoJoin's own four values: the typed key forms at the rule values. -/
noncomputable def kfTodo (x0 : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl))) (m : (attSg x D rad).Msg) : Fin 4 → Cb.Gl.E :=
  KF (scl := (meantQ (attBase x S tl D rad) (attLin0 x S tl D rad) ns N (attQ0 x S tl D rad Ex Wp α ns N)).scl)
    (dimOf S) (callsOf x.fs) (pubOfZ Cb.Gl.E x0.2.1.pt)
    (rv (dimOf S) (callsOf x.fs) (pubOfZ Cb.Gl.E x0.2.1.pt) (attCells x S tl D rad m))

/-- **The lookup's item worth "keys", from the kind's relation in front.** -/
theorem keys_of_todo {S₀ W : Type} {set : Params.Setting} (H : AttOK set x S tl D rad) {fork : S₀ → Option Fork}
    {heard : S₀ → Option Forest.Heard} {ι : Fo.Pl → Option (JAtt x.ns tl)} (hι : ∀ j, ι (.mask j) = some (enMask x.ns tl j))
    {Q : Fork → Prop} {x0 : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl))} {g₀ : Forest.Heard} {s : S₀}
    (hl : K3LeftOutIs fork heard x.fs x.lm x.F.next ι Q x0 g₀ s) (nu : W → Fo.Pl → Cb.Gl.E) (Kv : W → ℕ → ℕ → Cb.Gl.E)
    (ms : W → (attSg x D rad).Msg) (w : W)
    (hν : ∀ j, j < x.ns → nu w (.mask j) = (attLin x S tl D rad Ex Wp α ns N).maskOf (ms w) j)
    (hKF : ∀ (rs : TwV.Rounds Cb.Gl.E) (F' : Fork), Fo.HeardIs Reading.gl g₀ F' (Fo.endsOf x.fs x.lm x.F.next rs) →
      ∀ c : Fin 4, keysAt x.fs x.lm x.F.next (Kv w) rs c.val = kfTodo x S tl D rad Ex Wp α ns N x0 (ms w) c)
    (hT : TodoJoin x S tl D rad Ex Wp α ns N x0 (ms w)) :
    K3WorthKeys fork heard x.fs x.lm x.F.next nu Kv s w := by
  obtain ⟨F, F₁, rs₀, _, hn, L, e1, e2, T⟩ := hl
  intro g F' hf hh rs hI
  obtain rfl : g₀ = g := Option.some.inj (e1.symm.trans hh)
  obtain rfl : F₁ = F' := Option.some.inj (e2.symm.trans hf)
  have hI₀ := L.heardIs
  rw [hn] at hI₀ T
  show Fo.claimJoin x.fs x.lm x.F.next rs (nu w) (keysAt x.fs x.lm x.F.next (Kv w) rs) = 0
  rw [Fo.claimJoin_joinVal x.fs x.lm x.F.next rs (nu w) _ H.four,
    join_typed x S tl D rad Ex Wp α ns N H rs rs₀ ι hι hI hI₀ L.shape (ms w) T (nu w) hν,
    show (fun c : Fin 4 => keysAt x.fs x.lm x.F.next (Kv w) rs c.val) = kfTodo x S tl D rad Ex Wp α ns N x0 (ms w) from
      funext (hKF rs F₁ hI)]
  exact hT

/-- **The clause "keys" of K5FillIns.** -/
theorem k5FillIns_keys {Pp W Cl : Type} {Fr : Frame} {set : Params.Setting} (claim : Aff → Cl) (Mg : Meaning Pp W) (Nm : Numbers)
    (links : List ModelPart) (π : Pp) (m : ℕ) (pl : Place) (O : List Item) (Q : List Pub) (H : AttOK set x S tl D rad)
    (x0 : First.S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl))) (gOf : First.S × Fr.E.Str → Forest.Heard)
    (ι : Fo.Pl → Option (JAtt x.ns tl)) (hι : ∀ j, ι (.mask j) = some (enMask x.ns tl j)) (Qr : Fork → Prop)
    (part ms : W → (attSg x D rad).Msg) (hms : ∀ w, ms w = part w) (nu : W → Fo.Pl → Cb.Gl.E) (Kv : W → ℕ → ℕ → Cb.Gl.E)
    (leftIs : ∀ a' : First.S × Fr.E.Str, Mg.pubP (.left m) (π, a'.1) →
      K3LeftOutIs (VerifiableInference.Desc.K3.seatCalls claim).fork (VerifiableInference.Desc.K3.seatCalls claim).heard
        x.fs x.lm x.F.next ι Qr (x0 a') (gOf a') a'.1)
    (hleftQ : Pub.left m ∈ Q)
    (hν : ∀ w j, j < x.ns → nu w (.mask j) = (attLin x S tl D rad Ex Wp α ns N).maskOf (ms w) j)
    (hKF : ∀ (a' : First.S × Fr.E.Str) (w : W), onT Nm Mg links π Fr pl O Q a' → ∀ (rs : TwV.Rounds Cb.Gl.E) (F' : Fork),
      Fo.HeardIs Reading.gl (gOf a') F' (Fo.endsOf x.fs x.lm x.F.next rs) →
      ∀ c : Fin 4, keysAt x.fs x.lm x.F.next (Kv w) rs c.val = kfTodo x S tl D rad Ex Wp α ns N (x0 a') (ms w) c)
    (hW : ∀ (s : First.S) y w,
      K3WorthKeys (VerifiableInference.Desc.K3.seatCalls claim).fork (VerifiableInference.Desc.K3.seatCalls claim).heard
        x.fs x.lm x.F.next nu Kv s w → Mg.worth m 2 "keys" (π, s) y w) :
    ∀ a' w, onT Nm Mg links π Fr pl O Q a' → TodoJoin x S tl D rad Ex Wp α ns N (x0 a') (part w) →
      Mg.worth m 2 "keys" (π, a'.1) (strsOf Fr a'.2) w := fun a' w hon hT =>
  hW a'.1 _ w (keys_of_todo x S tl D rad Ex Wp α ns N H hι (leftIs a' (onAt_pubP hon.1 hon.2 _ hleftQ)) nu Kv ms w (hν w)
    (hKF a' w hon) (by rw [hms]; exact hT))

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.keys_of_todo
#print axioms VerifiableInference.Desc.First.Att.P.k5FillIns_keys
