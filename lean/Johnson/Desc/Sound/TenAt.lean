-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/TenAt.lean: **THE LEDGER's CLAUSE AT THE SHARED CHAIN's BLOCK 10 (THE PROXIMITY TEST ON G_omega), AT THE PIECE THAT A DESCRIPTION HOLDS: THE KIND's LAW, THE PIN's AND THE PROMISE's RIDERS PAID; WHAT IS
LEFT IS NAMED.** Statements and proofs. The sister of NineAt.lean, at the same terms (smpSt · shiftBook N.lo · besideP (promSigS …) sharedX · e₀H).
  smp_ten      the test on G_omega leaves smp₂ at every member of ms.
  law_ten      K12's law, second arm (GameHeldBook.lean; leads_alike), at the piece, from inside the ledger's promise, towards QN π (NTuple …).
  **ten_paid** THE CLAUSE. PAID HERE: the law's promise (by X) · o_omega's pin rides back · the promise at 11: "no collision" of o_omega · X 11. Nothing rides past this block beside (rides_ten).
LEFT, NAMED, EACH A PREMISE: seam (it is handed the piece's yes too) · hrow | hcong (Say's filling; asked inside the promise at 10; hcong under agreement at o_sp AND o_omega) · htab · hshape (10 → 11) · ON
THE PLAN: K12's law's own premises, second arm · SentBefore at o_omega · apartAt · hsit · hN · oNo on ms · the two sendings' counts.
Limits. NO MEMBER. It closes no row. NO SOUNDNESS IS CLAIMED.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.NineAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law.Fence
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker Desc.Plain
open Iop Prob _root_.Run
open VerifiableInference.Desc (Block FileDescription Strs Wit smpHeld)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts Seat.onGomega Seat.leave)
open VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open H2K.Pin (NTuple)
open H2K.Pub (PayPub)

section
variable (cs : Codes) {Xi P₁ Cl Cells Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ) (ms : List Mem)
  (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells) (c₀ : Cells) (N : NumbersS)
  (Mg : MeaningS St P₁ (Wit Cells Tok MsgT)) (Pm₀ : PromMeaning St) (Oc : P₁ → Strs → Prop)
  {Fr : Frame} (oNo : Mem → ℕ) (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay)
  (f : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
  (l : List (Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)))
  (π : P12) (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
  (hb : Alike (held (P := P₁) (Seat.onGomega (proximityTestKind guardedProximityTestParts π : Block T12 Unit))) x.b)
  (he : π.early = true) (ha1 : π.answers = 1) (hsU : sentU.size = 2)
  (hsO : (withOmega P.S).size = 2)
  (hms : ∀ z ∈ ms, oNo z = 0 ∨ oNo z = sentU.size ∨ oNo z = sentU.size + 1)
include hb he ha1 hsU hsO hms

/-- **The test on G_omega leaves smp₂ at every member.** -/
theorem smp_ten (a b : (P₁ × St) × Fr.E.Str) (τ : Iop.Tr (uLT (ckP .two) x.ds))
    (ha : onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l 10 a)
    (hout : x.ior.red.out a τ = some b) :
    ∀ z ∈ ms, smpSt cs oNo stSh b.1.2 z.1 z.2 = smpSt cs oNo stSh a.1.2 z.1 z.2 := by
  intro z hz
  have hX := x_of_on cs G ms N Pm₀ Oc oNo P sentU layU layO f l 10 a ha
  obtain ⟨rs, gs, hd, _⟩ := held_decides _ x hb a b τ hout
  exact smpSt_onGomega cs oNo π he ha1 _ _ rs gs hd z
    (x_numbers P sentU layU layO 10 (.inr rfl) _ hX hsU hsO _ (hms z hz))

variable (t₁ t₂ c : ℕ) (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (dB : RDT)
  (dt : List RDT) (e v₀ : ℕ) (εt : Err (uLT (ckP .two) dt))
  (ε : Err (uLT (ckP .two) x.ds)) (h0 : x.back = []) (hds : x.ds = dB :: dt)
  (herr : HEq ε ((e, εt) : Err (uLT (ckP .two) (dB :: dt))))
  (hA : AtPlaceOwn Fr π (VerifiableInference.Desc.numAt t₁ t₂ c) L mC mS mW rad x.base dB dt εt)
  (hPay : PayPub π rad dB.entry.rows v₀) (h1 : Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0])
  (hlog : dB.entry.logN ≤ 64) (hle : v₀ * (bsRound .two dB.entry dB.kind).w ≤ e)
  (ho : π.nums.ownMask = true) (hP : ownLabelsB π = true)
  (n2 : ∀ n, n < π.nums.free → VerifiableInference.Desc.numAt t₁ t₂ c (.own n) < x.base)
  (n3 : ∀ c' n, (c' + 1, n) ∈ π.before →
    VerifiableInference.Desc.numAt t₁ t₂ c (.taken c' n) < x.base)
  (hft : π.nums.firstTree = P.par.toGPar.firstTree)

omit he ha1 hsU hsO hms in
include h0 hds herr hA hPay h1 hlog hle ho hP n2 n3 hft in
/-- **K12's law, second arm, at the piece, from inside the ledger's promise.** -/
theorem law_ten :
    x.ior.red.Leads (onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l 10)
      (fun a _ => ∃ t, inGomega a.1.2 = .ok t ∧
        QN π (NTuple Fr π (noAt t₁ t₂ c) rad rd) (t, a.2)) ε := by
  have k := k12_held_onGomega_book P₁ Fr (Wit Cells Tok MsgT) π t₁ t₂ c L mC mS mW rad rd x.base dB dt e
    v₀ εt ⟨held (P := P₁) (Seat.onGomega (proximityTestKind guardedProximityTestParts π : Block T12 Unit)), x.base, x.ds, x.back,
      fun _ _ w => w, ε⟩ rfl h0 rfl hds herr hA hPay h1 hlog hle ho hP n2 n3
  have k' := leads_alike
    (⟨held (P := P₁) (Seat.onGomega (proximityTestKind guardedProximityTestParts π : Block T12 Unit)), x.base, x.ds, x.back,
      fun _ _ w => w, ε⟩ : Piece (ckP .two) Fr (P₁ × St) Unit (Wit Cells Tok MsgT))
    ({ x with err := ε } : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) hb rfl rfl rfl
    HEq.rfl _ _ k
  refine Reduction.Leads.conseq (K := x.ior.red) k' (fun a ha => ?_) fun a _ _ _ _ hq => ?_
  · exact sharedX_gives_ten P sentU layU layO π hft _
      (x_of_on cs G ms N Pm₀ Oc oNo P sentU layU layO f l 10 a ha)
  · obtain ⟨⟨t, _, ht, _, hQ⟩, _⟩ := hq
    exact ⟨t, ht, hQ⟩

variable (Say : St → RowS → Tup cs → Prop)

include h0 hds herr hA hPay h1 hlog hle ho hP n2 n3 hft in
/-- **THE CLAUSE AT BLOCK 10.** -/
theorem ten_paid
    (seam : ∀ a τ b t, onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l 10 a →
      x.ior.red.out a τ = some b →
      inGomega a.1.2 = .ok t → QN π (NTuple Fr π (noAt t₁ t₂ c) rad rd) (t, a.2) →
      TestSays N f l Say (candT cs G (smpSt cs oNo stSh) ms N) 10 .oSp [.oOmega]
        [.sample .oOmega, .sample .oSp, .foldOmega] a)
    (hsit : ∃ y ∈ ms, SitsAt y (N.tenant .oSp).1 (N.tenant .oSp).2)
    (hN : ((mineS N ms true 10).map (numOf arr)).Nodup)
    (hapO : apartAt N arr true 10 (.msg .oOmega) = true)
    (sb : SentBefore N f l 10 x .oOmega)
    (hrow : ∀ q ∈ [RowS.sample .oOmega, .sample .oSp, .foldOmega], ∀ a, onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l 10 a → ∀ w,
      Say a.1.2 q (rgT cs arr w) → Mg.row q a.1.2 w)
    (hcong : ∀ q ∈ [RowS.sample .oOmega, .sample .oSp, .foldOmega], ∀ a, onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l 10 a → ∀ m m',
      (∀ μ, μ = Msg2.oSp ∨ μ ∈ [Msg2.oOmega] → sameT cs ms N μ m m') → Say a.1.2 q m → Say a.1.2 q m')
    (htab : ∀ a τ b, onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l 10 a →
      x.ior.red.out a τ = some b → Pm₀.tablePromise b.1.2 (strsOfAct Fr ((actQ N f l 11).2 b)))
    (hshape : ∀ a τ b, onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l 10 a →
      x.ior.red.out a τ = some b → Pm₀.shape 11 b.1.2 = true) :
    ClauseAt N (meaningSigS cs G arr (smpSt cs oNo stSh) ms decT₂ Mg)
      (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l
      (e₀H cs G arr (smpSt cs oNo stSh) ms decT₂ c₀ N true Fr) 10 x ε := by
  have hsm := smp_ten cs G ms N Pm₀ Oc oNo P sentU layU layO f l π x hb he ha1 hsU hsO hms
  refine ten_sig cs G arr (smpSt cs oNo stSh) ms decT₂ c₀ stSh
    (fun s : St => shiftBook N.lo s.book) N Mg (besideP Pm₀ (sharedX P sentU layU layO)) Oc Say f l x
    ε hsit hN hapO ?_ ?_ hrow hcong ?_
  · exact Reduction.Leads.conseq (K := x.ior.red)
      (law_ten cs G ms N Pm₀ Oc oNo P sentU layU layO f l π x hb t₁ t₂ c L mC mS mW rad rd dB dt e v₀
        εt ε h0 hds herr hA hPay h1 hlog hle ho hP n2 n3 hft) (fun _ ha => ha)
      fun a τ b ha hb hq => by
        obtain ⟨t, ht, hQ⟩ := hq
        exact seam a τ b t ha hb ht hQ
  · intro a τ b w ha hout h
    exact pin_rides cs G arr (smpSt cs oNo stSh) ms decT₂ N Mg f l 10 x .oOmega sb a b τ
      hout (fun z hz => (hsm a b τ ha hout z hz).symm) w h
  · intro a τ b ha hout q hq
    have e11 : promsAt true 11 = [.tablePromise, .shape 11, .noColl .oOmega] :=
      promsAt_tests.2.2.1
    rw [e11] at hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    obtain ⟨rs, gs, hd, _⟩ := held_decides _ x hb a b τ hout
    have hX := x_of_on cs G ms N Pm₀ Oc oNo P sentU layU layO f l 10 a ha
    rcases hq with rfl | rfl | rfl
    · exact htab a τ b ha hout
    · exact Bool.and_eq_true_iff.2 ⟨hshape a τ b ha hout,
        sharedX_onGomega P sentU layU layO π hft he ha1 _ _ rs gs hd hX⟩
    · exact noColl_rides cs G (smpSt cs oNo stSh) ms stSh (fun s : St => shiftBook N.lo s.book) N _ f l
        10 x .oOmega sb a b τ hout (hsm a b τ ha hout)
        (ha.1 (.noColl .oOmega) (by decide))

end

end Desc.K14.Law.Fence

#print axioms Desc.K14.Law.Fence.smp_ten
#print axioms Desc.K14.Law.Fence.law_ten
#print axioms Desc.K14.Law.Fence.ten_paid
