-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6PlanesAtMgAll.lean: THE THIRD ITEM "worth 24 3" THAT THE SUB-PROTOCOL AT
THE OUTPUT HEAD CLOSES, AT THE COMPOSED MEANING OF ALL KINDS (Johnson/Desc/Sound/MgAll.lean):
"planes": from the item on the planes' forms behind that sub-protocol.

A joining. That meaning says the item in the lookup library's words, at the reading headNu of the
lookup's places off the witness (Johnson/Desc/Sound/MgAllAt.lean: mgAll_worth_head_planes). Another
of K6's files has the road from the forms' sentence behind the sub-protocol to these words, at
a letter for the places off the data (Law/PlanesArm.lean: planes_arm). Law/HeadPlanesNu.lean ties
K6's files' term for that letter (nuK6) to headNu.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable).
  nu_mg: nuK6 at the data dataQ (N.sent 24 0) aK (seatTab ... w) IS headNu ... w, at every place, at
      the composed meaning's own letters.
  planes_mgAll: the item.

Every letter under "there is": none.
What it does not say. THE PREMISES, EACH NAMED IN THE STATEMENTS. Of nu_mg: CallerMeets; the
test laidThere; at the planes' matrix: one tenant bears its message's number, CallsSeated,
MatsSeated; at the mask row: five facts on the verifier's state. Of planes_mgAll: what the link's
second run-stating sub-protocol states under "planes" (PlanesStates); the reader's equation; the
forms' sentence; four facts on the verifier's state behind (its open segment, its ledger's number of
slots, the name of the array of the reads, StatedAt); the width of that array; an inequality on the
plan's numbers; what the lookup heard has the plan's shape. Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.K6WorthAtMgAll
import Johnson.Desc.Kinds.Law.HeadPlanesNu
import Johnson.Desc.Kinds.Law.PlanesArm
import Johnson.Desc.Kinds.Law.K6OpenedCut

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open OnBytes.Model.Verify (borderOf)
open VerifiableInference.OnPublicFiles (headLink layMs headNu k3AdrAt)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (S Meaning)
open VerifiableInference.Desc.Sound (MsgT MgData mgAll)

variable {Xi P Tok : Type} {rows cols nR : ℕ} {Wp : OnBytes.Model.Verify.Public}
  {D : MgData Xi P Tok rows cols nR Wp}
  (Mg : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT))

/-- **The lookup's places off the data are the caller's off the witness.** -/
theorem nu_mg {lay6 : OnBytes.Params.ReqLayout} {num : ℕ → ℕ → ℕ} {n : ℕ}
    {x : First.Look.Place} (M : CallerMeets D lay6 num n x)
    (T : Meaning.laidThere Wp (Meaning.sizesOf Wp) lay6 = true)
    (pB : ∀ (μ : Fin (Meaning.sizesOf Wp 24).NM) (r c : Nat),
      r < Alg.symRows ((Meaning.sizesOf Wp 24).m μ) → c < (Meaning.sizesOf Wp 24).k μ →
      colsB Wp μ.val c → Sound.namedOnce D.arr D.N 24 (seatLay Wp lay6 num 24 μ r c).1 = true)
    (hC : CallsSeated (colsB Wp) D.arr D.ms D.N Wp lay6 num D.sent D.l3.rad x.link
      fun j => D.l3.seat x.link false j.1)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (aK : K9.Part) (s : S)
    (hlayA : aK.L.check.rows.layout = lay6)
    (hM : MatsSeated (colsB Wp) D.arr D.N Wp (D.N.sent 24 0) aK num lay6)
    (hmk : ∃ (o : Nat) (xo : Nat × Nat), K9L.maskOracle aK.L.check.frame = some o ∧
      K9.seatAt (D.N.sent 24 0) aK.d.book o = some xo ∧ xo ∈ D.N.group 24 ∧
      D.arr xo.1 xo.2 = n ∧ aK.d.st.rowBits o .mask = 0) (pq : _root_.Fo.Pl) :
    nuK6 Wp s (Sound.dataQ (D.N.sent 24 0) aK (Sound.seatTab D.cs D.arr D.ms w)) pq =
      headNu (k3AdrAt Wp) x Wp.H.tl D.sent D.l3.rad D.l3.oW D.l3.wOf D.l3.nr D.l3.nc
        (fun j => D.l3.seat x.link false j.1) D.l3.arr D.l3.msgW w pq := by
  cases pq with
  | mask j =>
    obtain ⟨o, xo, m1, m2, m3, m4, m5⟩ := hmk
    obtain ⟨_, _, _, _, _, _, _, _, _, g1, _⟩ := M.mask
    exact Came.nu_mask_meets D.cs D.arr D.ms D.N (Meaning.sizesOf Wp) (seatLay Wp lay6 num) Wp n
        (k3AdrAt Wp) x Wp.H.tl
      D.sent D.l3.rad D.l3.oW D.l3.wOf D.l3.nr D.l3.nc (fun j => D.l3.seat x.link false j.1)
      D.l3.msgW w (D.N.sent 24 0) aK s o xo m1 m2 m3 m4 m5 (mask_mg M w) g1 j
  | cell r c =>
    exact Came.nu_cell_meets D.cs D.arr D.ms D.N Wp lay6 num x D.sent D.l3.rad D.l3.oW D.l3.wOf
      D.l3.nr D.l3.nc (fun j => D.l3.seat x.link false j.1) D.l3.msgW w (D.N.sent 24 0) aK s T M.lay
      rfl hlayA pB hC hM r c
  | key a b => rfl
  | zero => rfl

/-- **The item "worth 24 3 planes".** -/
theorem planes_mgAll {x : First.Look.Place} (C : CallerFits (Wp := Wp) x) (hlm : x.lm = Wp.hS.lmbH)
    (a b : P × S) (y : Strs) (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (b6 : Block S Unit)
    (h6 : blockOf Wp 24 = some b6) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hd : (Sound.below b6).decide a.2 rs gs = .ok b.2) (hOn : K6On Wp a.2)
    (states : Nat → List (K9.RunOf S)) (hSt : PlanesStates (readsOf Wp) Wp.hS.lmbH states 2)
    (hRd : (D.Rd 24).forms 2 "planes" b.2 = k6Silent (p8K6 Wp 24) states 2 "planes" b.2)
    (hf : Sound.formsTQ (D.Rd 24) D.St (D.N.sent 24 0) 2 "planes" b.2
      (Sound.seatTab D.cs D.arr D.ms w))
    (aK : K9.Part) (ha : K9.segAt? b.2 = some aK) (hns : aK.F.ns = Wp.H.ns) (cU : Nat × String)
    (hArr : aK.L.arrayOf[readsOf Wp]? = some cU) (hSA : StatedAt Wp (p8K6 Wp 24) D.St b.2 cU)
    (hwide : ∀ e F tr, withTables (p8K6 Wp 24) b.2 = some e → e.fork? = some F →
      F.trees[readsOf Wp]? = some tr → Wp.H.nU.getD 2 0 ≤ tr.K)
    (hlen : ∀ gk, b.2.lookHeard? = some gk →
      gk.shape.NC * 2 ^ (gk.shape.kT + 5 - Wp.hS.lmbH) ≤
        (Wp.H.tl.mats.getD (Wp.hS.NHf + 1 + 1) {}).k *
          ((Wp.H.tl.mats.getD (Wp.hS.NHf + 1 + 1) {}).m / 2 ^ Wp.hS.lmbH))
    (hsh : ∀ g, a.2.lookHeard? = some g → g.shape = x.fs) (hok : FoNums.ok x.fs = true)
    (hnu : ∀ pq, nuK6 Wp b.2
        (Sound.dataQ (D.N.sent 24 0) aK (Sound.seatTab D.cs D.arr D.ms w)) pq =
      headNu (k3AdrAt Wp) x Wp.H.tl D.sent D.l3.rad D.l3.oW D.l3.wOf D.l3.nr D.l3.nc
        (fun j => D.l3.seat x.link false j.1) D.l3.arr D.l3.msgW w pq) :
    (mgAll D Mg).worth 24 3 "planes" a y w := by
  rw [← C.seg, Sound.mgAll_worth_head_planes D Mg C.place a y w]
  intro _ g F' hF hg
  have arm := planes_arm Wp 24 b6 h6 a.2 b.2 rs gs hd hOn (p8K6 Wp 24) 2 states hSt (D.Rd 24) D.St
    (D.N.sent 24 0) (Sound.seatTab D.cs D.arr D.ms w) hRd hf (cellsK6 Wp) (nuK6 Wp) aK ha
    (fun j hj => by
      rw [(hSA _).1 j]
      show _ = if j < Wp.H.ns then _ else 0
      rw [if_pos (hns ▸ hj)])
    cU hArr (fun pos => (hSA _).2 pos) hwide hlen x.fs hsh hok x.F.next g F' hF hg
  have e : nuK6 Wp b.2 (Sound.dataQ (D.N.sent 24 0) aK (Sound.seatTab D.cs D.arr D.ms w)) =
      headNu (k3AdrAt Wp) x Wp.H.tl D.sent D.l3.rad D.l3.oW D.l3.wOf D.l3.nr D.l3.nc
        (fun j => D.l3.seat x.link false j.1) D.l3.arr D.l3.msgW w := funext hnu
  rw [e] at arm
  rw [hlm]
  exact arm

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.nu_mg
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.planes_mgAll
