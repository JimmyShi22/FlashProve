-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/JoinMeetsAtHead.lean: CONDITIONAL, under the library's one head on the
public input (`P5J.AtMgA`): the lookup's half of the join (`JoinMeets`,
Johnson/Desc/K5/Honest/Law/Join.lean) in the world of the table's sentence at the state behind the
lay of an attention segment's own rounds, from the table's item on the worth of the keys in front,
at the same witness. It is `joinMeets_behind` (Johnson/Desc/K5/Honest/Law/JoinMeetsBehind.lean) at
the head's letters; its premises on public data, on what stands in front of the block and on what
the lookup leaves are paid as in `planes_at_head` (Johnson/Desc/K5/Honest/Law/PlanesAtHead.lean),
whose lines this file follows. A joining; calls alone.

Main names:
  `joinMeets_at_head`   **`JoinMeets` in the sentence's world behind the lay**, with the item in the
                    library's letters
  `joinMeets_item_at_head`   the same with the item in the closed filling's own letters

THE PREMISES, beside the head: hL, hg, ea, hx: the layout is laid; the group, its plan and the
lookup's place. Mg, hpub, hpubP, O, Q, Oq, hcQ, hr, hu, hon: the promise in front of the block, at a
state that the first chain reaches. e, hh: an attention segment is open; the hearing of its own
rounds returns. hW: THE ITEM ON THE KEYS' WORTH HOLDS IN FRONT, at the witness w. hg0, K3: the open
segment holds what the lookup left for the claims' reading, with its key points cut as the lookup
cuts them. hlk: the open segment's other field on the lookup holds gL, off which the join's letters
are read. hKv: THE ITEM'S KEY VECTORS ARE kvec. kvec is a free letter; what is meant are the
library's key vectors of the honest cells, and there hKv is a tie on the witness:
Johnson/Desc/K5/Honest/Law/KvOfCells.lean draws it, under the library's head, from a tie of the
cells to the witness's data, which is shown nowhere.
Limits. That the promise in front holds of an honest run, that the item holds of the honest witness,
and hKv are not shown here. At the function `OnBytes.secondHashFunction`, of which nothing is asked here; at the
library's full size alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.PlanesAtHead
import Johnson.Desc.K5.Honest.Law.JoinMeetsBehind
import Johnson.Desc.K5.Honest.Law.PublicAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace H2K5.Honest
open Cb Cb.LdLkp OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (lookAt)
open VerifiableInference.Desc.First.Att.P (behind hear Heard K3Pts)
open VerifiableInference.Desc.K12.Door (Laid)
open VerifiableInference.OnPublicFiles (K3WorthKeys attNu)
open Johnson.Desc.First.Walk.Tied (Reach)
open P5J (AtMgA mgAtAll TS)
open H2K5.Door

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- **The lookup's half of the join, in the sentence's world behind the lay, at the head's
letters.** Conditional; the premises are listed in the file's head. -/
theorem joinMeets_at_head {L : Laid} (hL : P5J.At.laid? Zp = some L) {g : ℕ} (hg : g < 12)
    {a : Attention.Plan} {x₁ : Look.Place} (ea : (P5J.At.X Zp).A[g]? = some a)
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {W' : Type}
    (Mg : Meaning ProofFile.InstPub W') (hpub : Mg.pub = (mgAtAll h).pub)
    (hpubP : Mg.pubP = (mgAtAll h).pubP) (O : List Item) (Q : List Pub)
    (Oq : Open8 (2 * g + 1) Q) (hcQ : Pub.callerIn (2 * g + 1) ∈ Q) {π : ProofFile.InstPub} {s : S}
    {y : Strs} (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * (2 * g + 1) + 4) (π, s))
    (hu : s.failed = none)
    (hon : onAt (P5J.At.N Zp cF) Mg P5J.At.links (some (plK5 g)) O Q (π, s) y)
    {att : AttOwn} (e : s.here = .att att) {rs : List Fmt.RoundView} {hd : Heard} {G : Fork}
    (hh : hear a.own (att.F, rs, 0) = some (hd, G, [], 0)) {Cells Tok : Type}
    {w : Wit Cells Tok MsgT} (Kv : Wit Cells Tok MsgT → ℕ → ℕ → Cb.Gl.E)
    (hW : K3WorthKeys (K3.seatCalls K3Lot.ofForm).fork (K3.seatCalls K3Lot.ofForm).heard x₁.fs
      x₁.lm x₁.F.next
      (attNu x₁ a.S a.seam.tl h.𝔇.sent h.𝔇.l3.rad (seatAll h x₁) h.𝔇.arr) Kv s w)
    {g0 : Forest.Heard} (hg0 : att.g = some g0) {z : ℕ → Cb.Gl.E}
    (K3 : K3Pts a.fs g0.zx g0.zy g0.zk z) {kvec : Fin 4 → ℕ → Cb.Gl.E}
    (hKv : ∀ c : Fin 4, ∀ X < 2 ^ (OnBytes.Road.L5.callsOf a.fs).a c, Kv w c.val X = kvec c X)
    {gL : Forest.Heard} (hlk : att.lookHeard = some gL) :
    JoinMeets Reading.gl
      (worldBehind h.𝔇.St (h.𝔇.pubD.N.sent (2 * g + 1) 0) s att hd G
        (seatTab h.𝔇.sent.codes h.𝔇.arr h.𝔇.ms w)) gL
      fun c => Blocks.ext ((OnBytes.Road.L5.callsOf a.fs).a c) (kvec c)
        ((OnBytes.Road.L5.callsOf a.fs).zC c z) := by
  obtain ⟨h4, _, _⟩ := scope_all h
  have hP := planIs_all h
  obtain ⟨_, hxns, hxl, hfs⟩ := Att.P.place_calls h4 ea hx
  obtain ⟨blk, hat⟩ := seated_all h hg
  obtain ⟨hok, hG⟩ := seatedOk_guard_all h hg hat
  have pOk := planOk_plus (beforeAll Zp g) hat hok ea
  have cOk := claimsOk_plus (beforeAll Zp g) hat hok ea
  have hA : (P5J.At.X Zp).A[x₁.link / 2]? = some a := by
    rw [hxl, show (2 * g + 1) / 2 = g by omega]
    exact ea
  have T := dataIs_all h (2 * g + 1)
  have hatt : h.𝔇.pubD.d5.isAtt (2 * g + 1) = true :=
    isAtt_of h.𝔇.pubD.d5 (by rw [T.d5links]; exact sub_full hg)
  have hlay : FillK4.isLay h.𝔇.pubD.links (2 * g + 1) = false :=
    att_not_lay (by rw [T.links]; exact sub_full hg)
  have hf : h.𝔇.pubD.d5.first? (2 * g + 1) = some (Forest.elems a.fs) :=
    first_at h.𝔇.pubD.d5 (by rw [T.d5W]; exact hP) (by rw [T.d5W]; exact h4)
      (by rw [T.d5W]; exact ea) (by rw [T.d5W]; exact hx)
  have h5 : att.heard5 = none := by
    have hc := Att.P.onAt_pub hon hu _ hcQ
    rw [hpub, hpubPlus_all h, pubAll_callerIn_att h.𝔇.pubD _ (2 * g + 1) hlay hatt, hf] at hc
    exact (Att.P.callerIn3_at e hc).1
  obtain ⟨_, gL', Y, hLf⟩ := door_at_head h hL hg ea hx Mg hpub hpubP O Q Oq hr hu hon
    K3Lot.ofForm (fun _ => (none : Option Unit))
  obtain rfl : gL' = gL := by
    have := Y.heard
    rw [Att.P.lookHeard_front e, hlk] at this
    exact (Option.some.inj this).symm
  obtain ⟨i, K, _, _, _, _, gL'', _, hin, _, _, _, hlk'', _, hFil, _⟩ :=
    runs_at_head h hL hg ea hx Mg hpub hpubP O Q Oq hr hu hon e hh
  obtain rfl : gL'' = gL' := Option.some.inj (hlk''.symm.trans hlk)
  have AO := attOK_plus (beforeAll Zp g) h.𝔇.sent h.𝔇.l3.rad hP h4 ea hx hG pOk cOk
  have FA := Att.P.frontAll_of_door hA (ofPlan_all h ea) Y
  obtain ⟨g1, hg1, Sr⟩ := FA.reads att e
  obtain rfl : g1 = g0 := Option.some.inj (hg1.symm.trans hg0)
  have Kp : Att.P.KeyPtsAre Reading.gl (OnBytes.Road.L5.callsOf a.fs) z gL''.zk := by
    rw [← Sr.zk]
    exact keyPts_of_keysFit (public_at_head h hg ea).keys K3
  have C := k5CondAt_at_head h hL
  have Tc := C.each g hg a x₁ ea hx
  have R := joinMeets_behind x₁ a h.𝔇.sent h.𝔇.l3.rad ⟨Unit, Unit, Unit, fun _ _ => ()⟩ Unit
    (fun _ => 0) K3Lot.ofForm e hu h5 hh hin hFil a.ns
    (Att.P.numsPlan a.own (x₁.F.next + Forest.elems x₁.fs)) h.𝔇.St h.𝔇.pubD.N h.𝔇.arr
    (seatAll h x₁) h.𝔇.ms a.ns FA (tiePubCells_all h hg ea hx Tc.cells)
    (Nat.le_of_eq hxns.symm) hLf Kv hW (VerifiableInference.OnPublicFiles.foOk_of_shape AO.shape) AO.four
    (fun _ j _ => memAt_field C.head.oneShape _ _ Tc.tests.someMem j)
    (fun s' a₀ h' hl => Att.P.hSt_of_arm hA h.𝔇.uL h.𝔇.uH s' a₀ h' hl) Kp hKv
  rw [hxl] at R
  exact R

/-- **The same with the item in the closed filling's own letters**: worth "keys" in front gives the
lookup's half of the join behind. y₁: the item's strings, which the sentence does not read. The
item's key vectors are written out: they are the layout's, at the cells that are unpacked from the
witness's messages. Conditional as `joinMeets_at_head`. -/
theorem joinMeets_item_at_head {L : Laid} (hL : P5J.At.laid? Zp = some L) {g : ℕ} (hg : g < 12)
    {a : Attention.Plan} {x₁ : Look.Place} (ea : (P5J.At.X Zp).A[g]? = some a)
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {W' : Type}
    (Mg : Meaning ProofFile.InstPub W') (hpub : Mg.pub = (mgAtAll h).pub)
    (hpubP : Mg.pubP = (mgAtAll h).pubP) (O : List Item) (Q : List Pub)
    (Oq : Open8 (2 * g + 1) Q) (hcQ : Pub.callerIn (2 * g + 1) ∈ Q) {π : ProofFile.InstPub} {s : S}
    {y : Strs} (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * (2 * g + 1) + 4) (π, s))
    (hu : s.failed = none)
    (hon : onAt (P5J.At.N Zp cF) Mg P5J.At.links (some (plK5 g)) O Q (π, s) y)
    {att : AttOwn} (e : s.here = .att att) {rs : List Fmt.RoundView} {hd : Heard} {G : Fork}
    (hh : hear a.own (att.F, rs, 0) = some (hd, G, [], 0)) (y₁ : Strs)
    {w : Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
    (hW : (mgAtAll h).worth (2 * g + 1) 2 "keys" (π, s) y₁ w)
    {g0 : Forest.Heard} (hg0 : att.g = some g0) {z : ℕ → Cb.Gl.E}
    (K3 : K3Pts a.fs g0.zx g0.zy g0.zk z) {kvec : Fin 4 → ℕ → Cb.Gl.E}
    (hKv : ∀ c : Fin 4, ∀ X < 2 ^ (OnBytes.Road.L5.callsOf a.fs).a c,
      Cb.Fo.forK Cb.Gl.E (Look.attLay a.S x₁.fs x₁.lm x₁.F.next x₁.ns a.seam.tl) ()
        (Cb.Fo.zext (VerifiableInference.OnPublicFiles.attMu x₁ a.seam.tl h.𝔇.sent h.𝔇.l3.rad
          (seatAll h x₁) h.𝔇.arr w)) c.val X = kvec c X)
    {gL : Forest.Heard} (hlk : att.lookHeard = some gL) :
    JoinMeets Reading.gl
      (worldBehind h.𝔇.St (h.𝔇.pubD.N.sent (2 * g + 1) 0) s att hd G
        (seatTab h.𝔇.sent.codes h.𝔇.arr h.𝔇.ms w)) gL
      fun c => Blocks.ext ((OnBytes.Road.L5.callsOf a.fs).a c) (kvec c)
        ((OnBytes.Road.L5.callsOf a.fs).zC c z) := by
  have Gn := mgGains_all h (scope_all h).1 ea hx
  rw [Gn.keys] at hW
  exact joinMeets_at_head h hL hg ea hx Mg hpub hpubP O Q Oq hcQ hr hu hon e hh
    (fun w => Cb.Fo.forK Cb.Gl.E (Look.attLay a.S x₁.fs x₁.lm x₁.F.next x₁.ns a.seam.tl) ()
      (Cb.Fo.zext (VerifiableInference.OnPublicFiles.attMu x₁ a.seam.tl h.𝔇.sent h.𝔇.l3.rad
        (seatAll h x₁) h.𝔇.arr w))) hW hg0 K3 hKv hlk

end

end H2K5.Honest

#print axioms H2K5.Honest.joinMeets_at_head
#print axioms H2K5.Honest.joinMeets_item_at_head
