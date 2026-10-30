-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/FenceDecodesFit.lean: TWO SENTENCES ON THE MERGE OF THE CLAIMS ON THE
COMMITTED TABLE (kind K11) LAID INTO THE THEOREMS THAT ASK THEM: so that "to the letter" is Lean's
word and nobody's reading. Nothing new is proved.

  merge_hcb_low       `merge_hcb` (CtxBack.lean) at m := 24 with its premise hF paid by
                      `fence_at_merge` (FenceAtMerge.lean): what is left of hF is "every sampled tenant
                      whose pin is open at border 346 sits in a tree below base"
  seatLaws_with_hD    `merge_seatLaws` (TieLaws.lean) at Mg := mgAll 𝔇 Mg₀ with its premise
                      hD paid by `merge_hD` (DecodesAtMerge.lean): every other premise is handed
                      through, with the type that `merge_seatLaws` itself gives it

Limits. Joins. All that the two theorems ask beside stays asked. No soundness statement.

-/
import Johnson.Top.H0.MergeLaw.FenceAtMerge
import Johnson.Top.H0.MergeLaw.DecodesAtMerge
import Johnson.Top.H0.MergeLaw.CtxBack
import Johnson.Top.H0.MergeLaw.TieLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.MergeLaw
open Iop
open OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj
open _root_.Run (ckP)
open VerifiableInference.Desc (FileDescription Wit Claim)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S HeadOwn Item Meaning Numbers sampledIn openSets start
  flatPlacesOf)
open Johnson.Pack (sigOf)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide)

/-- **`merge_hcb` with the fence paid.** -/
theorem merge_hcb_low (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) {Pp Cells Tok : Type}
    (arr : ℕ → ℕ → ℕ)
    (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells) {Fr : Frame} (ms : List Mem)
    (Nn : Numbers) (Mg : Meaning Pp (Wit Cells Tok MsgT)) (P : HeadMergeP) (base : ℕ)
    (ds : List RDT)
    (hpin : ∀ j t a y w, Mg.pin j t a y w ↔ pinJT cs G arr smp ms j t a y w)
    (hpinW : ∀ a y w, Mg.pinW a y w ↔ pinWOf decT a y w)
    (low : ∀ x ∈ sampledIn Nn
      ((openSets linksFull (flatPlacesOf linksFull true) (start linksFull))[346]?.getD []),
      x.1 < base)
    (hsmp : ∀ z (s : S) (a' : HeadOwn),
      smp (z, { s with rowsOwed := none, here := .head a' }) = smp (z, s))
    (hdec : ∀ z c (s : S) (a' : HeadOwn),
      decT c (z, { s with rowsOwed := none, here := .head a' }) = decT c (z, s))
    (z : Pp) (a b : S × Fr.E.Str) (w : Wit Cells Tok MsgT)
    (hy : ∃ rs, headMergeDecide P a.1 rs = .ok b.1)
    (hb : ∃ τ : Iop.Tr (uLT (ckP .two) ds), b.2 = behind (ckP .two) Fr base ds a.2 τ) :
    ∀ i ∈ [Item.pinW, .pin 24 0, .pinI], meansQ Nn Mg (fun s => (z, s)) i b w →
      meansQ Nn Mg (fun s => (z, s)) i a w :=
  merge_hcb cs G arr smp decT ms Nn Mg 24 P base ds hpin hpinW (fence_at_merge Nn base low ms) hsmp
    hdec z a b w hy hb

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) (Mg₀ : Meaning P (Wit (CellsQ rows cols) Tok MsgT))
  {Xi' : Type} {Pl : K11Caller.Place} {Fr : Frame}

/-- **`merge_seatLaws` at the composed meaning with "decodes rides" paid**: Lean's check of hD's
letters. The binders without a type get theirs from `merge_seatLaws`. -/
def seatLaws_with_hD (hk : DecKeeps 𝔇.decT) (G : FileDescription Xi') (N : K11Caller.Nums Pl)
    (q : Piece (ckP .two) Fr (P × S) Claim (Wit (CellsQ rows cols) Tok MsgT)) (Pm : HeadMergeP) :=
  fun cs arr smp rc decT claims lin xM xI posM posI links ps k Nn hlay h1 hk0 hnum hunit hinM hinI
      hsmp hdec he hkd hback herr hF t1 t2 t3 t4 t5 =>
    merge_seatLaws cs G arr smp rc decT N claims lin xM xI posM posI links ps k q Nn (mgAll 𝔇 Mg₀)
      Pm hlay h1 hk0 hnum hunit hinM hinI hsmp hdec he hkd hback herr hF t1 t2 t3 t4 t5
      (merge_hD 𝔇 Mg₀ Pm q.base q.ds hk)

end

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.merge_hcb_low
#print axioms VerifiableInference.Desc.First.MergeLaw.seatLaws_with_hD
