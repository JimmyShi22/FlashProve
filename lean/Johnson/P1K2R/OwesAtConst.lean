-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/OwesAtConst.lean: WHAT THE CODE SWITCH's FIFTH TIE OWES (`K2Owes`,
    Johnson/Top/H0/K2Ties/T5.lean) AT THE COMPOSED MEANING's CLOSED CONSTANT, AT EVERY PLACE OF THE
        KIND: OF ITS FOURTEEN FIELDS EIGHT ARE CALLS, TWO ARE THE PREMISES ON THE PLACE, FOUR STAY
        PREMISES. Three theorems. A law file: no sub-protocol imports
    it.

Why. `K2Owes` is one field (O) of what is owed at a place. Its fields have found payers one by one,
    at several hands. Here Lean holds that they meet in one member, at one place, one piece and one
    list of listed places.

What is said.
  `links_lt_full`, `k2_link_lt`: BY LEAN's KERNEL at the written full list: a place of the kind K2
      bears a segment's number of at most 25, or none. `links_lt_can_fail`: a negative test: with 24
      for 25 the test rejects.
  `k2Owes_at_const`: at D := `dC Hd`, the closed base, the constant's lists, "reached, at a typed
      instance's public part, and no mark", the place pl at number k, the segment mOf k + 1, the
      shapes of the first chain's oracle messages and the listed places L. THE CALLS: place, kind:
      the premises on the place · riders, fromM: `riders_at` (Johnson/P1K2R/TableAtConst.lean) ·
      decBlind, reqBlind, hidBears: `decBlind_at`, `reqBlind_at`, `hidBears_at`
      (Johnson/Top/H0/K2Ties/AtConstant.lean) · indexOff: `indexOff_at` (IndexOffAt.lean) · fence:
      `fence_at` with `pinOpen_at` and `hP_at` (IndexPlace.lean) · smp: `smp_of_fence`
      (SmpOfFence.lean) over that fence, with `hidx_at`.
  THE PREMISES THAT STAY. On the piece: left (an accept leaves what `Left` names) · base (the index
      masks' tree was sent in front). On the output head's part of the meaning: headBack ·
      headBears. Named tests and ties: the test `offC` · `AtWritten` · `AtTold` · "the first chain's
      sendings are the written ones" · "the listed places are the constant's tenants". The head with
      the facts on reached states (`P5J.AtMgR`) at that "reached".

Limits. NO MEMBER IS SHOWN: the premises are not shown to hold together. No soundness is claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K2R.ThirdAtConst
import Johnson.Top.H0.K2Ties.IndexOffAt
import Johnson.Top.H0.K2Ties.IndexPlace
import Johnson.Top.H0.K2Ties.SmpOfFence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc (Chain KindName Strs)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Door (Laid)
open VerifiableInference.Desc.First (flatPlacesOf laysPads)
open VerifiableInference.Desc.First.K2Ties (Wq K2Owes Left HeadBears AtWritten AtTold smp_named
    decBlind_at reqBlind_at hidBears_at fence_at indexOff_at hP_at smp_of_fence riders_of_B)
open P1K2 (mOf riders_at pinOpen_at hidx_at)
open ProofFile (Cl)
open _root_.Run (ckP)

theorem links_lt_full : (flatPlacesOf linksFull true).all (fun a => !(a.kind == KindName.K2) ||
    decide (a.link.getD 25 - 1 < 25)) = true := by decide +kernel

/-- A negative test: the bound one lower. -/
theorem links_lt_can_fail : (flatPlacesOf linksFull true).all (fun a => !(a.kind == KindName.K2) ||
    decide (a.link.getD 25 - 1 < 24)) = false := by decide +kernel

theorem k2_link_lt {k : ℕ} {pl : VerifiableInference.Desc.Place} (ha : P5J.At.ps[k]? = some pl) (hk
    : pl.kind = KindName.K2)
    : pl.link.getD P5J.At.links.length - 1 < 25 := by
  have h := List.all_eq_true.1 links_lt_full pl (List.mem_of_getElem? ha)
  rw [hk] at h
  have h' : decide (pl.link.getD 25 - 1 < 25) = true := by simpa using h
  exact of_decide_eq_true h'

variable {Z : VerifierAndGoals.PublicFiles} {Dw : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF
                  : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

set_option maxHeartbeats 2000000 in
/-- **What the fifth tie owes, at the constant: eight fields of fourteen are calls.** -/
theorem k2Owes_at_const (Hd : P5J.AtMgA OnBytes.secondHashFunction Z Dw r₀ Zp Np cF x) {k : ℕ} {pl :
                VerifiableInference.Desc.Place} (ha
                : P5J.At.ps[k]? = some pl) (hk : pl.kind = KindName.K2) (z : ProofFile.InstPub) (p : Piece (ckP .two)
                      (frC Dw) First.S Cl (Wq numsFull.rows (P5J.colsAt numsFull) P5J.At.Tok)) (A : AtWritten Zp cF)
    (T : AtTold Zp cF) (hs : Zp.made.proof.1 = Johnson.G.proofSends0) {L :
    Laid} (hR : P5J.AtMgR OnBytes.secondHashFunction Z Dw r₀ Zp Np cF Hd.rchU Prod.fst L) (hPl : L.places =
                P5J.At.seats Zp) (hC : Hd.toAtMg.offC = true) (hleft : ∀ (a : First.S × (frC Dw).E.Str) τ b,
                p.ior.red.out a τ = some b → Left a.1 b.1) (hbase : (dC Hd).N.index.1 < p.base) (hHB : ∀ q i (s
                s' : First.S) (y y' : Strs) w, Left s s' → y'.cell = y.cell → (dC Hd).headPart q i (z, s') y' w
                → (dC Hd).headPart q i (z, s) y w) (hHe : HeadBears (dC Hd).headPart (laysPads (dC Hd).N
                P5J.fullLinks pl)) :
    K2Owes (dC Hd) mgBase P5J.fullLinks P5J.At.ps k z p (rchAtZ Hd.rchU z k) pl (mOf k + 1)
        (VerifiableInference.Desc.K12.Door.msgsOfChain Zp.made.proof.1) L :=
  have hF := fence_at Hd hR k z (pinOpen_at ha hk) (hP_at A T hs hR.listed)
  have hD : (dC Hd).smp = smpNamed (dC Hd).cs L.places := hPl ▸ smp_named Zp
  { place := ha
    kind := hk
    riders := (riders_of_B _ _ _ _ (riders_at ha hk)).1
    fromM := (riders_of_B _ _ _ _ (riders_at ha hk)).2
    left := hleft
    decBlind := decBlind_at Hd
    reqBlind := fun s s' _ => reqBlind_at Hd z s s'
    headBack := hHB
    headBears := hHe
    hidBears := hidBears_at Hd hC _ _
    base := hbase
    indexOff := indexOff_at A pl hk (k2_link_lt ha hk)
    smp := smp_of_fence (dC Hd) mgBase P5J.fullLinks P5J.At.ps k z (rchAtZ Hd.rchU z k) hD (hidx_at
        _ ha hk) hF
    fence := hF }

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.links_lt_full
#print axioms VerifiableInference.Desc.First.K2Caller.links_lt_can_fail
#print axioms VerifiableInference.Desc.First.K2Caller.k2_link_lt
#print axioms VerifiableInference.Desc.First.K2Caller.k2Owes_at_const
