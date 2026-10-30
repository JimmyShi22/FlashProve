-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/KeepsDecide.lean: WHAT A YES OF THE LOT's OWN BATCHING BLOCK LEAVES, AT WHATEVER
ROUNDS AND COLUMNS: for whoever has the decision of `K9.batch K9.atS p g` in hand and no step of a thread. Statements
and proofs ON THE VERIFIER's TEXT; no prover is in this file, and no goal is stated.
  `beside_headOf`   `headOf` (Honest/K9/KeepsPaid.lean) does not see what K9's blocks and the closing write: the
      library's `K9.Beside` (Johnson/Desc/First/Batch/Law/Keeps.lean)
  `beside_ownK9`   the like for `S.own?`, out of the library's `LinkJoin.putLink_own`, `putFork_own` (the same
      sentence as `beside_own`, Johnson/Desc/K10/Honest/KeepsStep.lean, which this file does not import)
  `rests_out`   `S.out` rests under the library's four writings (`FieldRests`)
  **`batch_any`**   for f with `K9.Beside f` that each run of the order keeps: (K9.batch K9.atS p (claimsInBy each bs
      order)).decide s rs gs = .ok s' → f s' = f s: the library's `K9.batch_keeps` over its
      `TailClaims.Law.claimsInBy_keeps` ("the gatherer keeps what each of its runs keeps",
      Johnson/Desc/First/TailClaims/K8SitsFront.lean)
  **`batch_any_lay`**, **`batch_any_att`**, **`batch_any_head`**   so under the library's head, at a link that sits at
      a segment (the premises of Honest/K9/KeepsAtHead.lean): s'.out = s.out at all three sorts; s'.own? = s.own? at a
      feed-forward segment; the riders' form on the head's x · t · wo at the head's
FOR K9's TWO OTHER MEMBERS AND K10's ONE THE LIBRARY HAS THE LAW OUTRIGHT, with no premise but `K9.Beside f`:
`K9.oneEquation_keeps`, `K9.shut_keeps`, `K9.closing_keeps`, `K9.closeOf_keeps` (the same file): call them at
`beside_ownK9`, `beside_headOf`, the library's `beside_out`. The letter u : HTailF2 is read by nothing in the
conclusions. On a member: as in Honest/K9/KeepsAtHead.lean. The last three are called by Honest/K9/DecideTied.lean.
WHAT IS NOT CLAIMED. That the block says yes at any state. The step from a block of the description that seats the
lot's block to the lot's block itself (the library's `IM.LaidAlone`). The four seating facts at any link (under the
head they come off K9's seat: Honest/K9/SeatTied.lean; so laid: DecideTied.lean). Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K9.KeepsAtHead
import Johnson.Desc.First.Batch.Law.Keeps
import Johnson.Desc.First.TailClaims.K8SitsFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin VerifiableInference.Desc.K9L VerifiableInference.Desc.PhiAll

theorem beside_headOf : Desc.K9.Beside headOf :=
  ⟨putLink_headOf, rests_headOf.fork, fun _ _ _ => rfl, fun _ _ => rfl⟩

theorem beside_ownK9 : Desc.K9.Beside S.own? :=
  ⟨LinkJoin.putLink_own, LinkJoin.putFork_own, fun _ _ _ => rfl, fun _ _ => rfl⟩

/-- **A yes of the lot's batching block, at whatever rounds and columns.** -/
theorem batch_any {γ : Type} {f : S → γ} (hf : Desc.K9.Beside f) (p : Desc.K9.Where)
    (each : ℕ × String → List Claim → S → Except String Unit) (bs : List (Block S Claim))
    (order : List (ℕ × String))
    (hrun : ∀ o ∈ order, ∀ run, claimsRunOf bs o = some run → ∀ n e c e₁, run n e = .ok (c, e₁) → f e₁ = f e)
    {s s' : S} {rs gs}
    (h : (Desc.K9.batch Desc.K9.atS p (claimsInBy each bs order)).decide s rs gs = .ok s') : f s' = f s :=
  Desc.K9.batch_keeps hf p _ (fun t y hy => TailClaims.Law.claimsInBy_keeps f order t y hrun hy) h

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} {F : FileDescription ProofFile.Inst} {Bs : ProofFile.PureBase}
  {base : List (Block S ProofFile.Cl)} {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}

/-- `S.out` rests under the four writings. -/
theorem rests_out : FieldRests (·.out) where
  tl := S.out_putTl
  fork := S.out_putFork
  wrote _ _ _ _ hw := by obtain ⟨_, rfl⟩ := hw; rfl
  head _ _ _ _ := rfl

/-- **At a feed-forward segment of the description.** -/
theorem batch_any_lay (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) (m : ℕ) (hm : m < 25)
    (hs : IM.subAt m = .layers) (L : Link S ProofFile.Cl) (p : Desc.K9.Where) (hlk : h.𝔇.lk m = some L)
    (seg : SegAt m (IM.subAt m) L)
    (drawB : DrawMoves Desc.K9.atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (kp : IM.k9At Zp m = some p) (u : HTailF2) {s s' : S} {rs gs}
    (hd : (Desc.K9.batch Desc.K9.atS p (claimsInBy L.each L.hear L.order)).decide s rs gs = .ok s') :
    s'.out = s.out ∧ s'.own? = s.own? :=
  ⟨batch_any Desc.K9.beside_out p L.each L.hear L.order
      (fun o ho run hr => fieldRun_lay_at h O m hm hs L p hlk seg drawB kp u rests_out o ho run hr) hd,
    batch_any beside_ownK9 p L.each L.hear L.order
      (fun o ho run hr => fieldRun_lay_at h O m hm hs L p hlk seg drawB kp u rests_own o ho run hr) hd⟩

/-- **At an attention segment of the description.** -/
theorem batch_any_att (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) {g : ℕ} (hg : g < 12)
    (hs : IM.subAt (2 * g + 1) = .attention) (L : Link S ProofFile.Cl) (p : Desc.K9.Where)
    (hlk : h.𝔇.lk (2 * g + 1) = some L) (seg : SegAt (2 * g + 1) (IM.subAt (2 * g + 1)) L)
    (drawB : DrawMoves Desc.K9.atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (kp : IM.k9At Zp (2 * g + 1) = some p) (u : HTailF2) {s s' : S} {rs gs}
    (hd : (Desc.K9.batch Desc.K9.atS p (claimsInBy L.each L.hear L.order)).decide s rs gs = .ok s') :
    s'.out = s.out :=
  batch_any Desc.K9.beside_out p L.each L.hear L.order
    (fun o ho run hr => fieldRun_att_at h O hg hs L p hlk seg drawB kp u rests_out o ho run hr) hd

/-- **At the head's segment of the description.** -/
theorem batch_any_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) (hs : IM.subAt 24 = .head)
    (L : Link S ProofFile.Cl) (p : Desc.K9.Where) (hlk : h.𝔇.lk 24 = some L) (seg : SegAt 24 (IM.subAt 24) L)
    (drawB : DrawMoves Desc.K9.atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (kp : IM.k9At Zp 24 = some p) (u : HTailF2) {s s' : S} {rs gs}
    (hd : (Desc.K9.batch Desc.K9.atS p (claimsInBy L.each L.hear L.order)).decide s rs gs = .ok s') :
    s'.out = s.out ∧
      ∀ a, s.here = .head a → ∃ a', s'.here = .head a' ∧ a'.x = a.x ∧ a'.t = a.t ∧ a'.wo = a.wo :=
  ⟨batch_any Desc.K9.beside_out p L.each L.hear L.order
      (fun o ho run hr => fieldRun_head_at h O hs L p hlk seg drawB kp u rests_out o ho run hr) hd,
    head_form (batch_any beside_headOf p L.each L.hear L.order
      (fun o ho run hr => fieldRun_head_at h O hs L p hlk seg drawB kp u rests_headOf o ho run hr) hd)⟩

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.beside_headOf
#print axioms ProofFile.Honest.K9.beside_ownK9
#print axioms ProofFile.Honest.K9.batch_any
#print axioms ProofFile.Honest.K9.rests_out
#print axioms ProofFile.Honest.K9.batch_any_lay
#print axioms ProofFile.Honest.K9.batch_any_att
#print axioms ProofFile.Honest.K9.batch_any_head
