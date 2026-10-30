-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/FourFactsOfWorth.lean: THE SMALLNESS TEST, THE HONEST PROVER's SIDE: AT EVERY
STATE REACHED IN FRONT OF EACH OF THE 25 BATCHINGS: THE LIBRARY's TWO SENTENCES "worth" ON THE
DIGITS' LOOKUP (`WorthTwo`, Johnson/Desc/First/Link/Law/WorthAtFront.lean) AND FIVE NAMED PREMISES
GIVE THE BUNDLE `FourFactsAt` (FourFactsAt.lean) AT WHAT IS FIXED BEFORE THE DRAW: IN THE GOALS'
SCOPE, THE FILES READ, UNDER AN OPENING OF THE DESCRIPTION AND ITS TEST ON ITS PLAN. THAT ANY SUCH
STATE IS REACHED IS NOT SHOWN. An assembly; none of the library's goals.

  `leftOnFull_at_all` `leftOnFull_at_batch` and `leftOnFull_at_head_seg` (LeftOnFull.lean) in one
                   sentence, at the wrapped blocks' reach at the batching of any l < 25
  **`fourFactsAt_of_worth`** the four · l < 25 · the built segment Xl · the wrapped blocks' reach at
                   the batching (z, s) · Look.digAt Bs.G₀.W l = some (xx, tlD) · DigOK set xx tlD D
                   rad pp · K9.atS.get? s = some a · WorthTwo S.fork? heardDig xx tlD D rad seatT
                   arr s w · THE FIVE ⊢ FourFactsAt pi8 (fixed9 (phiAll tlD ψ) s) (dataQ own a rd),
                   at every ψ
THE FIVE NAMED PREMISES, NONE SHOWN HERE OF ANY STATE OR WITNESS: two `OneReader` at rd (the
witness's messages are what rd reads) · maskB … = true (on public data) · `CellOkR` and `MaskOkR` at
the part a.
WHO PAYS WHICH CLAUSE: the four claims' slots: `fourSlots_at_all` · tl.f9 = g.shape, FoNums.ok,
HeardIs at one list of rounds: `leftOnFull_at_all`, carried to the state's own ledger by
OnPublicFiles.heardIsLater (Johnson/Top/H/K3LeftLater.lean) · the sizes of g.zk: `K3Left`'s zkLen with
`staticFacts_at_all`'s calls' numbers · the eight other static facts: `staticFacts_at_all` · the
three ties: `ties_of_rest`; its clause on the slots by LinkJoin.slots_of
(Johnson/Desc/First/Link/Law/LeftLight.lean) from the first fact and: THE WINDOW OF THE SUMCHECK
OVER THE LEAVES LIES BELOW THE LEDGER's NUMBER OF SLOTS: by the library's left_len, left_within,
left_room (Johnson/Top/H/Keep/K3LeftWindow.lean), each from `K3Left` alone · K3Planes and K3Keys:
`WorthTwo`, by unfolding, from tlD to the state's data by `sameDig_at_all` and SameDig.lay · THE
LETTERS: jLK := xx.F.next · F' := the state's own ledger · J₀ := Option xx.arrays.J · en := enOf ·
mk := mkOf · μ₀ := digMu.
KIN IN THE LIBRARY, NOT CALLED: `DigitsRest` (WorthAtFront.lean) is the exchange's own bundle on the
verifier's side: same, shape, five, points, small, pieces, apart, sameZ, coef, inside, cellsB,
cellsZ, masks: this bundle's facts nearly one for one; there worth_at_front goes FROM the four
values' being zero TO `WorthTwo`: here the way back is prepared. `LeftAsks` and left_three
(Johnson/Desc/First/Link/Law/LeftThree.lean): see TiesOfRest.lean.
THE PROMISE Ok OF A SORT OF SEGMENT IS NOT AMONG THE PREMISES.
ONE DEVICE STANDS IN IT: `attribute [-instance] Inst.Model.Scl.ref`. TACTICS THAT SEARCH: `omega` on
one line.
Limits. NOTHING SAYS THAT ANY STATE IS REACHED, NOR THAT THE FIVE AND `WorthTwo` CAN HOLD TOGETHER
AT ONE: where they cannot, all is idle: NO MEMBER. IN SCOPE ALONE: the full size; the first chain;
at OnBytes.secondHashFunction. At Bs.G₀.W. Which of the files beneath it are rows of the library is for the
library's own list to say: it is not said here. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.K8.Honest.LeftOnFull
import Johnson.Desc.K8.Honest.StaticFactsAtAll
import Johnson.Desc.K8.Honest.FourSlotsAtAll
import Johnson.Desc.K8.Honest.TiesOfRest
import Johnson.Desc.K8.Honest.FourFactsAt
import Johnson.Desc.First.Link.Law.WorthAtFront
import Johnson.Desc.First.Link.Law.LeftLight
import Johnson.Top.H.K3LeftLater
import Johnson.Top.H.Keep.K3LeftWindow

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 OnBytes.Params OnBytes.DgP Cb.Fo
open _root_.Fo
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.OnPublicFiles (K3Left SameDig CellOkR MaskOkR cellAddr maskAddr digMu)
open VerifiableInference.Desc.Sound (MsgT MsgQ dataQ msgsOf)
open VerifiableInference.Desc.First.Att.P (OneReader ReadMsgOf)
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.K9L (Pub9 pubOf fixed9 four8)
open VerifiableInference.Desc.K4Values (winOf)
open VerifiableInference.Desc.PhiAll (phiAll)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)

section
variable {P : VerifierAndGoals.PublicFiles} {pp₀ : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Desc.Claim)} {c : Chain S Desc.Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- What the lookup on the digits has left, whole, at all 25 segments in one sentence. -/
theorem leftOnFull_at_all (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z)
      (14 * l + (if l = 24 then 11 else 9)) (z, s)) {tl : HTailF2} {G : Fork}
    (ht : s.tl? = some tl) (hG : s.fork? = some G) :
    heldFields tl = heldFields Xl.tl ∧ ∃ (P' : First.Look.P) (g : Forest.Heard) (F₀ F' : Fork)
      (rs : TwV.Rounds Cb.Gl.E), placeAt Bs.G₀.W l true = some P' ∧ tl.heard = some g ∧
      FoNums.ok tl.f9 = true ∧ F₀.next = P'.first ∧ K3Left Reading.gl tl.f9 5 F₀ F' g rs ∧
      _root_.Fo.Later F' G := by
  by_cases h24 : l = 24
  · subst h24
    exact leftOnFull_at_head_seg hS hR O hOk e3 h ht hG
  · have r := reach_raw h
    rw [if_neg h24] at r
    exact leftOnFull_at_batch hS hR O hOk (by omega) e3 r ht hG

/-- **AT EVERY STATE REACHED IN FRONT OF EACH OF THE 25 BATCHINGS: THE TWO SENTENCES "worth" AND
FIVE NAMED PREMISES GIVE THE BUNDLE AT THE ONE FIXED DATA.** -/
theorem fourFactsAt_of_worth {Cells Tok β : Type} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z)
      (14 * l + (if l = 24 then 11 else 9)) (z, s))
    {xx : First.Look.Place} {tlD : HTailF2} (hd : Look.digAt Bs.G₀.W l = some (xx, tlD))
    {set : Params.Setting} {pp : ℕ} {D : Sent} {rad : OracleShape → ℕ}
    (HD : DigOK set xx tlD D rad pp) (seatT : Fin (digList xx D rad).length → ℕ × ℕ)
    (arr : ℕ → ℕ → ℕ) (own : List (ℕ × ℕ)) (rd : ℕ × ℕ → MsgQ) (w : Wit Cells Tok MsgT)
    (hc : OneReader (ReadMsgOf (cellAddr tlD) (seatOf D xx.link)) D.codes (digList xx D rad)
      seatT (msgsOf D.codes (digList xx D rad) seatT arr w) rd)
    (hm : OneReader (ReadMsgOf (maskAddr xx.arrays.ns) (seatOf D xx.link)) D.codes
      (digList xx D rad) seatT (msgsOf D.codes (digList xx D rad) seatT arr w) rd)
    (hB : maskB D (digList xx D rad) xx.link xx.arrays.ns = true)
    {a : Desc.K9.Part} (ha : Desc.K9.atS.get? s = some a)
    (C : CellOkR xx tlD D rad seatT own a) (M : MaskOkR xx D rad seatT own a)
    (hW : LinkJoin.WorthTwo S.fork? LinkJoin.heardDig xx tlD D rad seatT arr s w)
    (ψ : S → β) :
    FourFactsAt LinkJoin.pi8 (fixed9 (phiAll tlD ψ) s) (dataQ own a rd) := by
  intro tlb v g h1 h2 hg
  have hG : s.fork? = some a.F := Desc.K9.get_fork s a ha
  have hv : v = pubOf a := by
    have e : (Desc.K9.atS.get? s).map pubOf = some v := h2
    rw [ha] at e
    exact (Option.some.inj e).symm
  subst hv
  have h1' : s.tl?.map (TailClaims.Law.blank tlD) = some tlb := h1
  obtain ⟨tl, ht, rfl⟩ := Option.map_eq_some_iff.1 h1'
  have hg' : tl.heard = some g := hg
  have hr := reach_raw h
  obtain ⟨Sd, hfirst⟩ := sameDig_at_all hS hR O hl e3 hr ht hd
  have Sb : SameDig tlD (TailClaims.Law.blank tlD tl) :=
    ⟨Sd.f9, Sd.ix, Sd.mz, Sd.tau, Sd.z1, Sd.z2⟩
  obtain ⟨-, P', g₁, F₀, F', rs, hP, hg₁, hok, hn, K, hL⟩ :=
    leftOnFull_at_all hS hR O hOk hl e3 h ht hG
  obtain rfl : g₁ = g := Option.some.inj (hg₁.symm.trans hg')
  obtain ⟨b4, b5, b6, b7, b8, b9, b10, b11, b12⟩ :=
    staticFacts_at_all hS hR O hl e3 hr ht hG tlD
  obtain ⟨hz, b1⟩ := fourSlots_at_all hS hR O hOk hl h LinkJoin.pi8 (phiAll tlD ψ) tlD
    (fun _ => rfl) (pubOf a) _ g₁ h2 h1 hg
  have e9 : g₁.shape = tl.f9 := K.shape
  have es : g₁.shape = tlD.f9 := e9.trans Sd.f9
  have hWin : (winOf g₁.leaves).1 + (winOf g₁.leaves).2 ≤ a.F.ns := by
    show g₁.leaves.first + g₁.leaves.walk.1.length ≤ a.F.ns
    rw [OnPublicFiles.left_len K, hL.ns]
    exact le_trans (OnPublicFiles.left_within K) (OnPublicFiles.left_room K)
  have hns := LinkJoin.slots_of (pa := a) (g := g₁)
    (c := four8 (TailClaims.Law.blank tlD tl) g₁) hz (fun k hk => b1 k hk) hWin
  obtain ⟨t1, t2, t3⟩ := ties_of_rest seatT arr own HD rd w hc hm a C M hB
    (fixed9 (phiAll tlD ψ) s) h2 Sb g₁ (fun k hk => hns k hk)
  have hI : HeardIs Reading.gl g₁ a.F (endsOf tlD.f9 5 xx.F.next rs) := by
    have k := OnPublicFiles.heardIsLater Cb.Gl.E Reading.gl g₁ F' a.F _ hL K.heardIs
    rw [hn, hfirst P' hP, Sd.f9] at k
    exact k
  have hgd : LinkJoin.heardDig s = some g₁ := by
    show s.tl?.bind (·.heard) = some g₁
    rw [ht]
    exact hg'
  have p1 := hW.1 g₁ a.F hG hgd rs hI
  have p2 := hW.2 g₁ a.F hG hgd rs hI
  refine ⟨b1, e9.symm, ?_, b4, ?_, ?_, fun c hc' => (K.zkLen c (b7 c hc').1).trans (b7 c hc').2,
    b8, b9, b10, b11, b12, xx.F.next, a.F, Option xx.arrays.J, enOf xx.arrays, mkOf xx.arrays,
    digMu xx D rad seatT arr w, rs, ⟨le_refl _, rfl, fun _ hx => ⟨hx, rfl, rfl⟩⟩, t1, t2, t3,
    ?_, ?_, ?_⟩
  · rw [e9]
    exact hok
  · rw [e9]
    exact b5
  · rw [e9]
    exact b6
  · rw [es]
    exact hI
  · rw [es, Sb.lay.pl]
    exact p1
  · rw [es, Sb.lay.pl, Sb.lay.lay]
    exact p2

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.leftOnFull_at_all
#print axioms VerifiableInference.Desc.First.K8.Honest.fourFactsAt_of_worth
