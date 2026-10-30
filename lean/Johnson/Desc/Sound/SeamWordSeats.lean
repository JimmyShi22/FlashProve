-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SeamWordSeats.lean: **MemberFacts' SEVENTH CLAUSE (THE WORD) AT THE SHARED CHAIN's TWO PROXIMITY TESTS, WITH TWO OF word_at's PREMISES PAID FROM THE PROMISE AND THE ONE X.** Statements; each proof is calls of what lies.
  cf_of_on        inside the promise at a border k that holds "no collision" of a message μ: at every member of the list that sits at μ's tenant: the record holds its sample, every leaf of its word is shown, no collision (CfAt): the promise's own clause, unfolded.
  **word_seat**   at such a border, for a member x that sits at μ's tenant and a seat m of the kind's data with seatAt t₁ t₂ m = μ's tenant and SeatToldAt (SeatIsAtLaw.lean): s1 TO THE LETTER. ShownAt: FROM THE PROMISE (cf_of_on; carried to the whole strings by
                  shownAt_col). SeatIs: FROM SeatToldAt. The window: SentBefore's first two fields.
LEFT AS PREMISES: SeatFits (a test on the plan and the description) · the depth's premise (depth_at_desc, at a description's frame) · SentBefore (numbers) · the member's entry.
Limits. It closes no row. NO SOUNDNESS.

-/
import Johnson.Desc.Sound.SeamWordAt
import Johnson.Desc.Sound.NineAt
import Johnson.Desc.K12.Coin.SeatIsAtLaw
import Johnson.Desc.K12.Coin.MemberSits

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law.Fence
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker Desc.Plain Johnson.Pack Cb
open Iop Prob _root_.Run
open VerifiableInference.Desc (Block FileDescription Strs Wit)
open VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open H2K.Pin (strOf layOf)
open H2K.First (Seat1)

variable (cs : Codes) {Xi P₁ Cl Cells Tok : Type} (G : FileDescription Xi) (ms : List Mem) (N : NumbersS)
  (Pm₀ : PromMeaning St) (Oc : P₁ → Strs → Prop) {Fr : Frame} (oNo : Mem → ℕ) (P : P14)
  (sentU : Array OracleNotice) (layU layO : TreeLay)
  (f : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
  (l : List (Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)))

/-- The promise's clause "no collision", unfolded at a member. -/
theorem cf_of_on (k : ℕ) (μ : Msg2) (hμ : PromS.noColl μ ∈ promsAt true k)
    (a : (P₁ × St) × Fr.E.Str)
    (ha : onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l k a) (x : Mem) (hx : x ∈ ms)
    (hs : SitsAt x (N.tenant μ).1 (N.tenant μ).2) :
    CfAt G cs x.1.l x.1.seat (fun z => smpSt cs oNo stSh z x.1) x.2 ((actQ N f l k).2 a).1
      (strsOfAct Fr ((actQ N f l k).2 a)) := by
  have hnc : noCollJT cs G (smpSt cs oNo stSh) ms (N.tenant μ).1 (N.tenant μ).2
      ((actQ N f l k).2 a).1 (strsOfAct Fr ((actQ N f l k).2 a)) := by
    first
      | exact (ha.1 (.noColl μ) hμ).2.2
      | exact (ha.1 (.noColl μ) hμ).2
      | exact ha.1 (.noColl μ) hμ
  exact hnc x hx hs

/-- **s1 at a seat.** -/
theorem word_seat (k : ℕ) (μ : Msg2) (hμ : PromS.noColl μ ∈ promsAt true k)
    (a : (P₁ × St) × Fr.E.Str)
    (ha : onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l k a) (x : Mem) (hx : x ∈ ms)
    (hs : SitsAt x (N.tenant μ).1 (N.tenant μ).2)
    (y : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (hB : SentBefore N f l k y μ)
    (t₁ t₂ : ℕ) (book : TreeBook) (m : Seat1) (hseat : seatAt t₁ t₂ m = N.tenant μ)
    (sent : Array OracleNotice) (gs : List (List ℕ)) (lay : TreeLay) (i : ℕ)
    (hT : SeatToldAt G t₁ t₂ book m sent gs lay i) (hpart : lay.part.getD i 0 = m.part)
    (hF : SeatFits G cs x.1.l x.1.seat)
    (hd : ∀ o, G.oracleAt (x.1.seat x.2).1 = some o →
      ∀ e ∈ Fr.all, e.no = (x.1.seat x.2).1 → e.a ≤ o.logLength)
    (sh : OracleShape) (e0 : ℕ) (he : x.1.l.get x.2 = (sh, e0)) :
    HEq (strOf cs sh e0 (layOf m) (W0 Fr (noAt t₁ t₂ 1) book a.2 m.t).1
        (W0 Fr (noAt t₁ t₂ 1) book a.2 m.t).2)
      (wordsOf G cs x.1.l x.1.seat (strsOfAct Fr ((actQ N f l k).2 a)) x.2) := by
  have e : x.1.seat x.2 = ((N.tenant μ).1, (N.tenant μ).2) := hs
  have e1 : (x.1.seat x.2).1 = noAt t₁ t₂ 1 m.t := by rw [e, ← hseat]
  have e2 : (x.1.seat x.2).2 = m.part := by rw [e, ← hseat]
  have hlo : N.lo ≤ (x.1.seat x.2).1 := by rw [e]; exact hB.lo
  have hhi : (x.1.seat x.2).1 < hiAt k f l := by rw [e]; exact hB.front
  obtain ⟨_, _, hsh, _⟩ := cf_of_on cs G ms N Pm₀ Oc oNo P sentU layU layO f l k μ hμ a ha x hx hs
  have hS : ShownAt G cs x.1.l x.1.seat (strsOf Fr a.2) x.2 :=
    shownAt_col G cs x.1.l x.1.seat _ _ x.2
      (fun z => (col_act N f l k a _ hlo hhi z).symm) hsh
  obtain ⟨o, ho, hI, _⟩ := hT
  refine word_at N f l cs G k a x m (noAt t₁ t₂ 1) book hlo hhi hF hS (fun o' ho' => ?_) hd sh e0 he
  rw [e1] at ho'
  obtain rfl : o = o' := Option.some.inj (ho.symm.trans ho')
  rw [e1, e2, ← hpart]
  exact hI

end Desc.K14.Law.Fence

#print axioms Desc.K14.Law.Fence.cf_of_on
#print axioms Desc.K14.Law.Fence.word_seat
