-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Door/Law/K5LeftFitsH.lean: kind K5: THE TWO PREMISES ON THE VERIFIER's STATE THAT planes_plus (Door/Law/K5LeftFitsG.lean) STILL TOOK, AS THEOREMS UNDER THE TABLE's PROMISE IN FRONT OF THE KIND's SUB-PROTOCOL: each concludes the premise's own text.
  hBare_plus: the start form of the leaves' sumcheck is bare: THE SECOND CONJUNCT OF THE ITEM left m's OWN SENTENCE (LeavesBare, Johnson/Desc/First/Look/K3LeftItem.lean), by the filling's equation at that item (MgIs.pubPl).
  hH5_plus: nothing of the kind's own was received yet: the first clause of the public item callerIn m (callerIn3B, Att/Door/DoorBools.lean), by the filling's equation (MgIs.pub; pubAll_callerIn_att, Johnson/Desc/First/PubAllAt.lean): it wants that item among those that are open in front.
IS IT EMPTY HERE? Implications.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5LeftFitsG
import Johnson.Desc.First.Att.Door.Law.DoorTie
import Johnson.Desc.First.Att.K05BehindLay3
import Johnson.Desc.First.Look.K3LeftItem
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
open VerifiableInference.Desc.First.Look (bornAt keptAt sigListCalls)
open VerifiableInference.Desc.K9 (statesOfLink readersOfLink LinkHoles)
open VerifiableInference.OnPublicFiles (k3LeftItemAt)

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

theorem hBare_plus {X : Verify.Public} (hPl : ∀ m (a₁ : Pp × S), Mg.pubP (.left m) a₁ = k3LeftItemAt X m a₁.2)
    (x0 : Pp → S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl))) (gOf : Pp → S × Fr.E.Str → Forest.Heard)
    (hLI : LeftIsP Mg claim Wv g before a x plJ x0 gOf) (hleftQ : Pub.left (2 * g + 1) ∈ Q) :
    ∀ (π : Pp) (s : S) (y : Fr.E.Str) (att : AttOwn), onAt D.N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
      s.here = .att att → OnBytes.Road.Rows.Bare ((gOf π) (s, y)).leaves.start := by
  intro π s y att hon hm _
  have hP := onAt_pubP hon hm _ hleftQ
  obtain ⟨_, _, _, _, _, _, e1, _, _⟩ := hLI π (s, y) hP
  have e1' : s.lookHeard? = some ((gOf π) (s, y)) := e1
  rw [hPl] at hP
  obtain ⟨_, _, _, hb⟩ := hP
  have he := hb _ e1'
  intro Qr z hz
  rw [he] at hz
  cases hz

theorem hH5_plus {base : Pub → Pp × S → Bool} (hpub : Mg.pub = pubAll D base) (hlay : FillK4.isLay D.links (2 * g + 1) = false)
    (hatt : D.d5.isAtt (2 * g + 1) = true) (hcQ : Pub.callerIn (2 * g + 1) ∈ Q) :
    ∀ (π : Pp) (s : S) (y : Fr.E.Str) (att : AttOwn), onAt D.N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
      s.here = .att att → att.heard5 = none := by
  intro π s y att hon hm e
  have h := onAt_pub hon hm _ hcQ
  rw [hpub, pubAll_callerIn_att D base (2 * g + 1) hlay hatt] at h
  cases hf : D.d5.first? (2 * g + 1) with
  | none => rw [hf] at h; cases h
  | some n =>
    rw [hf] at h
    exact (callerIn3_at e (first := n) h).1

end

end H2K5.Door

#print axioms H2K5.Door.hBare_plus
#print axioms H2K5.Door.hH5_plus
