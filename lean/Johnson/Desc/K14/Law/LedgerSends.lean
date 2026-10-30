-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerSends.lean: THE TWO SENDINGS OF A PROOF FILE's SHARED CHAIN ("send o_u",
"send o_omega": blocks 2 and 5) AT THE LEDGER, AT THE ONE FILLING OF
Johnson/Desc/K14/Law/LedgerOne.lean, at blocks that decide as the kind's own, in the wrap in which a
description's pieces hold them; at the promise with ANY test XX laid beside the book-keeping
(besideP, Johnson/Desc/Sound/LedgerBeside.lean).

  sendU_step, sendO_step   what a yes of the second | the fifth block does to the small record; the
                  step is onward.
  isSend_as, on_down   a block that decides as a sending does is one; inside the promise with XX the
                  promise without it holds.
  two_core, five_core   **the two clauses from ONE premise with a price each** (hD): inside the
                  promise in front, but for ε, at a yes the new messages have the table's own
                  promise (PromS.noColl m).holds behind.
  two_at, five_at hD from K1's law of a sending (send_goodIn_entry, Johnson/Desc/K1/Law/) and hnew:
                  "sealed" gives the new message's promise.
  cf_gives        what SendGivesCf, a law of a sending, gives at a seat, at the acting part's value.
  two_cf, five_cf hD from that law of a sending BY NAME (SendGivesCf,
                  Johnson/Desc/Sound/SendLaw.lean).
PAID IN THE CORES: the stored table's promise rides (the key stays) · the book-keeping is earned
(shapeK 2 to 3, 5 to 6) · the riders at both sendings (at 2: omU, nearU, recRow, by the reader uR;
at 5: omU, o_u's pin and promise, the rows of o_u's sample, of "(rec_gamma)" and of "LOC": these are
said at a later statement, RowsUL).
WHAT STAYS, AND WHOSE. hD (above) · hX: XX is handed on (whoever lays it) · hkeep5: over o_omega's
sending the record holds, at the members at o_u's seat, the sample that it held (paid at smpSt
(Johnson/Desc/Sound/SmpShared.lean) in Johnson/Desc/K14/Law/LedgerPays.lean) · hB5 (numbers) · huR,
huN (the reader uR: paid at uRK, LedgerOne.lean) · hsr (the sample rows' letter).
What is not claimed. NO MEMBER IS SHOWN. No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.LedgerOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Cb Johnson.Pack Desc.Plain
open Iop Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words)
open VerifiableInference.Desc (Block Strs Wit FileDescription Grows)
open VerifiableInference.Desc.Ground
open VerifiableInference.Desc.K1 (IsSend sendPiece Sealed sampledAt shapeAt shapesOf condPort
  errPort seedEntry seedMaps send_goodIn_entry ins_two ins_five isSend_two_held isSend_five_held)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared

/-- **A yes of "send o_u"**: onward; of the small record it turns what is noted of o_u and of the
first mask, and nothing else. -/
theorem sendU_step (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) (d d' : St) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) (h : b2.decide d rs gs = .ok d') :
    Onward d d' ∧ ∃ mask, d'.loc = { d.loc with
      oU := ⟨d.st.oracles.size, vectorLay d.st.codes Q.par.S.fold.u Q.par.S.fold.rowsHigh⟩,
      firstMask := mask } := by
  obtain ⟨⟨sentU, hU, hs2⟩, _⟩ := send_of_blocks Q b1 b2 b3 b4 b5 b6 b7 b8 hbl
  obtain ⟨ft, ids, c1, c2, rU, cU, cUl, k2⟩ := hs2 d rs gs d' h
  obtain ⟨o1, l1⟩ := onward_recvP ft d c1 _ ids rU
  obtain ⟨s2, o, mask, ho, l2⟩ := behindU_inv Q.par c2 d' ids k2
  obtain ⟨nU, sU0, _⟩ := withU_first Q.S sentU hU
  obtain ⟨eo, _⟩ := recvP_first ft d c1 sentU ids rU nU sU0 o ho
  have hc : c2.st.codes = d.st.codes := (o1.trans cU).grows.1
  exact ⟨(o1.trans cU).trans (Onward.of_st s2), mask, by rw [l2, cUl, l1, eo, hc]⟩

/-- **A yes of "send o_omega"**: onward; of the small record it turns what is noted of o_omega and
of o_sp, and nothing else. -/
theorem sendO_step (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) (d d' : St) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) (h : b5.decide d rs gs = .ok d') :
    Onward d d' ∧ ∃ o sp, d'.loc = { d.loc with oOmega := o, oSp := sp } := by
  obtain ⟨_, hs5⟩ := send_of_blocks Q b1 b2 b3 b4 b5 b6 b7 b8 hbl
  obtain ⟨ft, ids, c1, c2, rO, cO, cOl, k5⟩ := hs5 d rs gs d' h
  obtain ⟨o1, l1⟩ := onward_recvP ft d c1 _ ids rO
  obtain ⟨s2, o, sp, _, l2⟩ := behindOmega_inv Q.par c2 d' ids k5
  exact ⟨(o1.trans cO).trans (Onward.of_st s2), o, sp, by rw [l2, cOl, l1]⟩

variable {P₁ Cl Xi Cells Tok : Type} {Fr : Frame} (cs : OnBytes.Codes) (G : FileDescription Xi)
  (arr : ℕ → ℕ → ℕ)
  (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem) (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells) (c₀ : Cells)
  (bkR : TreeBook → TreeBook)
  (N : NumbersS) (Mg₀ : MeaningS St P₁ (Wit Cells Tok MsgT)) (Pm₀ : PromMeaning St)
  (Oc : P₁ → Strs → Prop)
  (mem : ℕ → Option Mem) (rd : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg → Part → ℕ → GE)
  (uR : St → St) (omW : Wit Cells Tok MsgT → ℕ → GE) (e' n nU nO : ℕ) (num : Msg2 → ℕ)
  (p : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
  (l : List (Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)))
  (Q : P14) (XX : ℕ → St → Bool)


/-- A block that decides as a sending does, in the wrap, is a sending. -/
theorem isSend_as {U Cl' : Type} (K : VerifiableInference.Desc.K1.Par) (c : Block St Cl)
    (b : Block St Cl') (h : DecidesAs c b)
    (hs : IsSend K (fun t : U × St => t.2.st) (heldW (U := U) b)) :
    IsSend K (fun t : U × St => t.2.st) (heldW (U := U) c) := fun s s' r₁ r₂ gs hy =>
  hs s s' r₁ r₂ gs ((heldW_decide c b h s [r₁, r₂] gs).symm.trans hy)

/-- Inside the promise with XX beside, the promise without it holds. -/
theorem on_down (k : ℕ) (a : (P₁ × St) × Fr.E.Str) (ha : onQ₂ N (besideP (promSigS cs G smp₂ ms (fun
    s : St => s.st) (fun s : St => bkR s.book) (pmI decT₂ Pm₀ (P14.par Q) n nU nO)) XX) Oc true p l
    k a) :
    onQ₂ N (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR s.book) (pmI decT₂ Pm₀
        (P14.par Q) n nU nO)) Oc true p l k a := ⟨((promQ_beside N (promSigS cs G smp₂ ms (fun s :
        St => s.st) (fun s : St => bkR s.book) (pmI decT₂ Pm₀ (P14.par Q) n nU nO)) true p l XX k
        _).1 ha.1).1, ha.2⟩

variable (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
  (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) (hS : Q.S.sharedSplitNeeded = true)
  (hdk : ∀ c (s s' : St), s'.loc.key = s.loc.key → decT₂ c s' = decT₂ c s)
  (huR : ∀ s, seatedUB Q.par s = true → uR s = s)
include hbl hdk huR

/-- **"send o_u": the core**: the clause at block 2 from ONE premise with a price: but for ε, at a
    yes
the new message o_u has its promise behind (hD). -/
theorem two_core (c2 : Block St Cl) (h2c : DecidesAs c2 b2) (sentU : Array OracleNotice)
    (hU : withU Q.S = some sentU) (hnO : nO = nU + sentU.size) (base : ℕ) (d₁ d₂ : RDT)
    (ext₀ : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d₁, d₂]) → (Wit Cells Tok MsgT) → (Wit
        Cells Tok MsgT))
    (err₀ ε : Err (uLT (ckP .two) [d₁, d₂]))
    (hD : ∀ a, onQ₂ N (besideP (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR
        s.book) (pmI decT₂ Pm₀ (P14.par Q) n nU nO)) XX) Oc true p l 2 a → Doomed (uLT (ckP .two)
        [d₁, d₂]) ε fun τ =>
      ∀ y, (⟨heldW c2, base, [d₁, d₂], [], ext₀, err₀⟩ : Piece (ckP .two) Fr (P₁ × St) Cl
          (Wit Cells Tok MsgT)).ior.red.out a τ = some y →
        (PromS.noColl .oU).holds N (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR
            s.book) (pmI decT₂ Pm₀ (P14.par Q) n nU nO)) y.1.2 (strsOfAct Fr ((actQ N p l 3).2 y)))
    (hX : ∀ a τ y, onQ₂ N (besideP (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR
        s.book) (pmI decT₂ Pm₀ (P14.par Q) n nU nO)) XX) Oc true p l 2 a →
      (⟨heldW c2, base, [d₁, d₂], [], ext₀, err₀⟩ : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok
          MsgT)).ior.red.out
          a τ = some y → XX 3 y.1.2 = true)
    (huN : ∀ s, shapeP Q.par nU s = true → uR s = withNext Q.par s) :
    ClauseAt N (meaningSigS cs G arr smp₂ ms decT₂ (mgI cs arr Mg₀ mem rd (P14.par Q) uR omW e' n))
        (besideP (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR s.book) (pmI decT₂
        Pm₀ (P14.par Q) n nU nO)) XX) Oc true p l (fun k v w => extS cs G arr smp₂ ms decT₂ c₀ N
        true k v.1 (strsOfAct Fr v) w) 2 (⟨heldW c2, base, [d₁, d₂], [], ext₀, err₀⟩ : Piece (ckP
        .two)
        Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) ε := by
  have yes : ∀ a τ y, onQ₂ N (besideP (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR
      s.book) (pmI decT₂ Pm₀ (P14.par Q) n nU nO)) XX) Oc true p l 2 a →
      (⟨heldW c2, base, [d₁, d₂], [], ext₀, err₀⟩ : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok
          MsgT)).ior.red.out
          a τ = some y →
      shapeP Q.par nU a.1.2 = true ∧ ∃ rs gs, b2.decide a.1.2 rs gs = .ok y.1.2 := by
    intro a τ y ha hout
    obtain ⟨rs, gs, hd⟩ := held_yes (⟨heldW c2, base, [d₁, d₂], [], ext₀, err₀⟩ : Piece (ckP .two)
        Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) c2 rfl a τ y hout
    rw [h2c] at hd
    have h2 : ((promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR s.book) (pmI decT₂ Pm₀
        (P14.par Q) n nU nO))).shape 2 a.1.2 = true :=
      (on_down cs G smp₂ ms decT₂ bkR N Pm₀ Oc n nU nO p l Q XX 2 a ha).1 (.shape 2)
        (by simp [promsAt])
    rw [pmI_shape cs G smp₂ ms decT₂ bkR Pm₀ n nU nO Q 2 (by decide)] at h2
    exact ⟨h2, rs, gs, hd⟩
  have p3 : promsAt true 3 = [.tablePromise, .shape 3, .noColl .oU] := by decide
  refine clause_of_own N (meaningSigS cs G arr smp₂ ms decT₂ (mgI cs arr Mg₀ mem rd (P14.par Q) uR
      omW e' n)) (besideP (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR s.book)
      (pmI decT₂ Pm₀ (P14.par Q) n nU nO)) XX) Oc true p l (fun k v w => extS cs G arr smp₂ ms decT₂
      c₀ N true k v.1 (strsOfAct Fr v) w) 2 (⟨heldW c2, base, [d₁, d₂], [], ext₀, err₀⟩ : Piece
      (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) ε ?_ ?_
  · intro a ha
    refine Doomed.mono _ _ (fun τ hτ y hy => ?_) (hD a ha)
    refine ⟨?_, fun _ _ i hi => absurd hi (ins_two true i)⟩
    obtain ⟨h2, rs, gs, hd⟩ := yes a τ y ha hy
    obtain ⟨_, mask, lo⟩ := sendU_step Q b1 b2 b3 b4 b5 b6 b7 b8 hbl _ _ rs gs hd
    refine (promQ_beside N (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR s.book)
        (pmI decT₂ Pm₀ (P14.par Q) n nU nO)) true p l XX 3 _).2 ⟨fun c hc => ?_, hX a τ y ha hy⟩
    rw [p3] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact tab_rides decT₂ N p l hdk 2 (⟨heldW c2, base, [d₁, d₂], [], ext₀, err₀⟩ : Piece (ckP
        .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) a y τ hy (by rw [lo])
        ((on_down cs G smp₂ ms decT₂ bkR N Pm₀ Oc n nU nO p l Q XX 2 a ha).1 .tablePromise
          (by simp [promsAt]))
    · show ((promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR s.book) (pmI decT₂ Pm₀
        (P14.par Q) n nU nO))).shape 3 y.1.2 = true
      rw [pmI_shape cs G smp₂ ms decT₂ bkR Pm₀ n nU nO Q 3 (by decide)]
      obtain ⟨s1, s2⟩ := shapes_at_b2 Q b1 b2 b3 b4 b5 b6 b7 b8 hbl sentU hU nU _ _ rs gs hd h2
      rw [← hnO] at s2
      exact (shapeM_iff Q.par nU nO 0 y.1.2).2 ⟨s1, s2⟩
    · exact hτ y hy
  · intro a τ y w i ha hout _ ho _ hm
    show muQ N (meaningSigS cs G arr smp₂ ms decT₂ (mgI cs arr Mg₀ mem rd (P14.par Q) uR omW e' n))
        p l i 2 ((actQ N p l 2).2 a) (extS cs G arr smp₂ ms decT₂ c₀ N true 2 _ _ w)
    rw [extS_id cs G arr smp₂ ms decT₂ c₀ N true 2 rfl]
    obtain ⟨h2, rs, gs, hd⟩ := yes a τ y ha hout
    obtain ⟨_, mask, lo⟩ := sendU_step Q b1 b2 b3 b4 b5 b6 b7 b8 hbl _ _ rs gs hd
    obtain ⟨s1, _⟩ := shapes_at_b2 Q b1 b2 b3 b4 b5 b6 b7 b8 hbl sentU hU nU _ _ rs gs hd h2
    have eA : uR a.1.2 = withNext Q.par a.1.2 := huN _ h2
    have eY : uR y.1.2 = y.1.2 := huR _ ((shapeU_iff Q.par nU 0 y.1.2).1 s1).2.1
    have hp : y.1.2.loc.psiSh = (withNext Q.par a.1.2).loc.psiSh := by rw [lo]; rfl
    have hu : y.1.2.loc.oU = (withNext Q.par a.1.2).loc.oU := by rw [lo]; rfl
    have hk : y.1.2.loc.key = (withNext Q.par a.1.2).loc.key := by rw [lo]; rfl
    have h2l : ∀ j ∈ openL (insLSh true) (outsLSh true) startLSh 2,
        j = ItemS.omU ∨ j = .nearU ∨ j = .recRow := by decide
    rcases h2l i ((openSh_iff true 2 i).1 ho) with rfl | rfl | rfl
    · have hm' : OmU Q.par uR (rgOf cs arr mem rd) omW y.1.2 w := hm
      show OmU Q.par uR (rgOf cs arr mem rd) omW a.1.2 w
      exact omU_of_same Q.par uR _ omW a.1.2 y.1.2 w (by rw [lo]) (by rw [eY, eA]; exact hu) hm'
    · have hm' : NearAt OnBytes.Model.Reading.gl Q.par (uR y.1.2) (rgOf cs arr mem rd w)
          (colsOf (strsOfAct Fr ((actQ N p l 3).2 y)).cell) e' := hm
      show NearAt OnBytes.Model.Reading.gl Q.par (uR a.1.2) (rgOf cs arr mem rd w)
        (colsOf (strsOfAct Fr ((actQ N p l 2).2 a)).cell) e'
      rw [eY] at hm'
      rw [eA, cells_stay N p l 2 (⟨heldW c2, base, [d₁, d₂], [], ext₀, err₀⟩ : Piece (ckP .two) Fr
          (P₁ × St) Cl (Wit Cells Tok MsgT)) a y τ hout]
      exact NearAt.of_same _ hp hu hm'
    · have hm' : RecAll OnBytes.Model.Reading.gl Q.par (uR y.1.2) (rgOf cs arr mem rd w) := hm
      show RecAll OnBytes.Model.Reading.gl Q.par (uR a.1.2) (rgOf cs arr mem rd w)
      rw [eY] at hm'
      rw [eA]
      exact RecAll.of_same _ hp hu hk hm'

/-- **"send o_u": the clause at block 2, from K1's law of a sending.** hnew: "sealed" gives the new
message's promise. -/
theorem two_at (c2 : Block St Cl) (h2c : DecidesAs c2 b2) (sentU : Array OracleNotice)
    (hU : withU Q.S = some sentU)
    (hnO : nO = nU + sentU.size) (rad : ℕ → ℕ)
    (hC : condPort (parK1 Q 2 "o_u and the first mask" sentU) rad = true) (base : ℕ)
    (d₁ d₂ : RDT) (he₁ : d₁.entry = seedEntry (parK1 Q 2 "o_u and the first mask" sentU))
    (hk₁ : d₁.kind = .seeds) (e : ℕ)
    (he : errPort (parK1 Q 2 "o_u and the first mask" sentU) rad ≤ e)
    (fOf : Fr.E.Str → ∀ j, (portOmZ (parK1 Q 2 "o_u and the first mask" sentU).codes
      (shapeAt (parK1 Q 2 "o_u and the first mask" sentU) j) (rad j.val)).Str)
    (fIn : Fr.E.Str → (wT d₁).Msg → ∀ j, (portOmZ (parK1 Q 2 "o_u and the first mask" sentU).codes
      (shapeAt (parK1 Q 2 "o_u and the first mask" sentU) j) (rad j.val)).Str)
    (hf : ∀ y τ, fOf ((sendPiece (W := (Wit Cells Tok MsgT)) (F := Fr) (heldW (U := P₁) c2) base d₁
        d₂ (parK1 Q 2
        "o_u and the first mask" sentU).coordinates e).ior.imp y τ) = fIn y τ.1)
    (ext₀ : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d₁, d₂]) → (Wit Cells Tok MsgT) → (Wit
        Cells Tok MsgT))
    (err₀ : Err (uLT (ckP .two) [d₁, d₂]))
    (hX : ∀ a τ y, onQ₂ N (besideP (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR
        s.book) (pmI decT₂ Pm₀ (P14.par Q) n nU nO)) XX) Oc true p l 2 a →
      (⟨heldW c2, base, [d₁, d₂], [], ext₀, err₀⟩ : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok
          MsgT)).ior.red.out
          a τ = some y → XX 3 y.1.2 = true)
    (hnew : ∀ a τ y, onQ₂ N (besideP (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR
        s.book) (pmI decT₂ Pm₀ (P14.par Q) n nU nO)) XX) Oc true p l 2 a →
      (⟨heldW c2, base, [d₁, d₂], [], ext₀, err₀⟩ : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok
          MsgT)).ior.red.out
          a τ = some y →
      (∀ j, sampledAt (parK1 Q 2 "o_u and the first mask" sentU) j →
        Sealed (parK1 Q 2 "o_u and the first mask" sentU).codes
          (shapeAt (parK1 Q 2 "o_u and the first mask" sentU) j) (rad j.val) (fOf y.2 j) y.1.2.st
          (y.1.2.st.oracles.size -
            (shapesOf (parK1 Q 2 "o_u and the first mask" sentU)).length + j.val)) →
      (PromS.noColl .oU).holds N (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR
          s.book) (pmI decT₂ Pm₀ (P14.par Q) n nU nO)) y.1.2 (strsOfAct Fr ((actQ N p l 3).2 y)))
    (huN : ∀ s, shapeP Q.par nU s = true → uR s = withNext Q.par s) :
    ClauseAt N (meaningSigS cs G arr smp₂ ms decT₂ (mgI cs arr Mg₀ mem rd (P14.par Q) uR omW e' n))
        (besideP (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR s.book) (pmI decT₂
        Pm₀ (P14.par Q) n nU nO)) XX) Oc true p l (fun k v w => extS cs G arr smp₂ ms decT₂ c₀ N
        true k v.1 (strsOfAct Fr v) w) 2 (⟨heldW c2, base, [d₁, d₂], [], ext₀, err₀⟩ : Piece (ckP
        .two)
        Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
      ((seedMaps d₁ d₂ (parK1 Q 2 "o_u and the first mask" sentU).coordinates).err
        ((e, ()) : ℕ × Unit)) := by
  refine two_core cs G arr smp₂ ms decT₂ c₀ bkR N Mg₀ Pm₀ Oc mem rd uR omW e' n nU nO p l Q XX b1 b2
    b3 b4 b5 b6 b7 b8 hbl hdk huR c2 h2c sentU hU hnO base d₁ d₂ ext₀ err₀ _ ?_ hX huN
  have g := send_goodIn_entry (W := (Wit Cells Tok MsgT)) (F := Fr) (parK1 Q 2
      "o_u and the first mask" sentU) rad hC
    (heldW c2) (fun t => t.2.st)
    (isSend_as _ c2 b2 h2c (isSend_two_held P₁ Q b1 b2 b3 b4 b5 b6 b7 b8 hbl sentU hU)) base
    d₁ d₂ he₁ hk₁ e he fOf fIn hf (onQ₂ N (besideP (promSigS cs G smp₂ ms (fun s : St => s.st) (fun
        s : St => bkR s.book) (pmI decT₂ Pm₀ (P14.par Q) n nU nO)) XX) Oc true p l 2) (fun _ =>
        True) (fun _ _ => True)
    (fun _ _ => True) (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ => trivial)
  intro a ha
  exact Doomed.mono _ _ (fun τ hτ y hy => hnew a τ y ha hy (hτ y hy).1.2) (g a ha)

include hS in
/-- **"send o_omega": the core**: the clause at block 5 from ONE premise with a price: but for ε, at
    a
yes the new messages o_omega and o_sp have their promises behind (hD). -/
theorem five_core (c5 : Block St Cl) (h5c : DecidesAs c5 b5) (hne : nO ≠ nU) (base : ℕ)
    (d₁ d₂ : RDT)
    (ext₀ : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d₁, d₂]) → (Wit Cells Tok MsgT) → (Wit
        Cells Tok MsgT))
    (err₀ ε : Err (uLT (ckP .two) [d₁, d₂]))
    (hsr : SampleRides Mg₀ num) (hnum : num .oU = nU)
    (hB5 : SentBefore N p l 5 (⟨heldW c5, base, [d₁, d₂], [], ext₀, err₀⟩ : Piece (ckP .two) Fr (P₁
        × St) Cl (Wit Cells Tok MsgT)) .oU)
    (hD : ∀ a, onQ₂ N (besideP (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR
        s.book) (pmI decT₂ Pm₀ (P14.par Q) n nU nO)) XX) Oc true p l 5 a → Doomed (uLT (ckP .two)
        [d₁, d₂]) ε fun τ =>
      ∀ y, (⟨heldW c5, base, [d₁, d₂], [], ext₀, err₀⟩ : Piece (ckP .two) Fr (P₁ × St) Cl
          (Wit Cells Tok MsgT)).ior.red.out a τ = some y → ∀ m, m = Msg2.oOmega ∨ m = .oSp →
        (PromS.noColl m).holds N (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR
            s.book) (pmI decT₂ Pm₀ (P14.par Q) n nU nO)) y.1.2 (strsOfAct Fr ((actQ N p l 6).2 y)))
    (hX : ∀ a τ y, onQ₂ N (besideP (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR
        s.book) (pmI decT₂ Pm₀ (P14.par Q) n nU nO)) XX) Oc true p l 5 a →
      (⟨heldW c5, base, [d₁, d₂], [], ext₀, err₀⟩ : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok
          MsgT)).ior.red.out
          a τ = some y → XX 6 y.1.2 = true)
    (hkeep5 : ∀ a τ y, onQ₂ N (besideP (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St =>
        bkR s.book) (pmI decT₂ Pm₀ (P14.par Q) n nU nO)) XX) Oc true p l 5 a →
      (⟨heldW c5, base, [d₁, d₂], [], ext₀, err₀⟩ : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok
          MsgT)).ior.red.out
          a τ = some y →
      ∀ z ∈ ms, SitsAt z (N.tenant .oU).1 (N.tenant .oU).2 →
        smp₂ y.1.2 z.1 z.2 = smp₂ a.1.2 z.1 z.2) :
    ClauseAt N (meaningSigS cs G arr smp₂ ms decT₂ (mgI cs arr Mg₀ mem rd (P14.par Q) uR omW e' n))
        (besideP (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR s.book) (pmI decT₂
        Pm₀ (P14.par Q) n nU nO)) XX) Oc true p l (fun k v w => extS cs G arr smp₂ ms decT₂ c₀ N
        true k v.1 (strsOfAct Fr v) w) 5 (⟨heldW c5, base, [d₁, d₂], [], ext₀, err₀⟩ : Piece (ckP
        .two)
        Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) ε := by
  have yes : ∀ a τ y, onQ₂ N (besideP (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR
      s.book) (pmI decT₂ Pm₀ (P14.par Q) n nU nO)) XX) Oc true p l 5 a →
      (⟨heldW c5, base, [d₁, d₂], [], ext₀, err₀⟩ : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok
          MsgT)).ior.red.out
          a τ = some y →
      shapeM Q.par nU nO (Q.par.S.fold.index.answers + n) a.1.2 = true ∧
        ∃ rs gs, b5.decide a.1.2 rs gs = .ok y.1.2 := by
    intro a τ y ha hout
    obtain ⟨rs, gs, hd⟩ := held_yes (⟨heldW c5, base, [d₁, d₂], [], ext₀, err₀⟩ : Piece (ckP .two)
        Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) c5 rfl a τ y hout
    rw [h5c] at hd
    have h5 : ((promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR s.book) (pmI decT₂ Pm₀
        (P14.par Q) n nU nO))).shape 5 a.1.2 = true :=
      (on_down cs G smp₂ ms decT₂ bkR N Pm₀ Oc n nU nO p l Q XX 5 a ha).1 (.shape 5)
        (by simp [promsAt])
    rw [pmI_shape cs G smp₂ ms decT₂ bkR Pm₀ n nU nO Q 5 (by decide)] at h5
    exact ⟨h5, rs, gs, hd⟩
  have p6 : promsAt true 6 =
      [.tablePromise, .shape 6, .noColl .oU, .noColl .oOmega, .noColl .oSp] := by decide
  refine clause_of_own N (meaningSigS cs G arr smp₂ ms decT₂ (mgI cs arr Mg₀ mem rd (P14.par Q) uR
      omW e' n)) (besideP (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR s.book)
      (pmI decT₂ Pm₀ (P14.par Q) n nU nO)) XX) Oc true p l (fun k v w => extS cs G arr smp₂ ms decT₂
      c₀ N true k v.1 (strsOfAct Fr v) w) 5 (⟨heldW c5, base, [d₁, d₂], [], ext₀, err₀⟩ : Piece
      (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) ε ?_ ?_
  · intro a ha
    refine Doomed.mono _ _ (fun τ hτ y hy => ?_) (hD a ha)
    refine ⟨?_, fun _ _ i hi => absurd hi (ins_five true i)⟩
    obtain ⟨h5, rs, gs, hd⟩ := yes a τ y ha hy
    obtain ⟨_, o, sp, lo⟩ := sendO_step Q b1 b2 b3 b4 b5 b6 b7 b8 hbl _ _ rs gs hd
    have ha0 := on_down cs G smp₂ ms decT₂ bkR N Pm₀ Oc n nU nO p l Q XX 5 a ha
    refine (promQ_beside N (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR s.book)
        (pmI decT₂ Pm₀ (P14.par Q) n nU nO)) true p l XX 6 _).2 ⟨fun c hc => ?_, hX a τ y ha hy⟩
    rw [p6] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · exact tab_rides decT₂ N p l hdk 5 (⟨heldW c5, base, [d₁, d₂], [], ext₀, err₀⟩ : Piece (ckP
        .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) a y τ hy (by rw [lo])
        (ha0.1 .tablePromise (by simp [promsAt]))
    · show ((promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR s.book) (pmI decT₂ Pm₀
        (P14.par Q) n nU nO))).shape 6 y.1.2 = true
      rw [pmI_shape cs G smp₂ ms decT₂ bkR Pm₀ n nU nO Q 6 (by decide)]
      obtain ⟨s1, s2⟩ := (shapeM_iff Q.par nU nO _ a.1.2).1 h5
      exact shapes_at_b5 Q b1 b2 b3 b4 b5 b6 b7 b8 hbl hS nU nO _ hne _ _ rs gs hd s1 s2
    · exact noColl_ridesAt cs G smp₂ ms _ _ N _ p l 5 (⟨heldW c5, base, [d₁, d₂], [], ext₀, err₀⟩ :
        Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) .oU hB5 a y τ hy
        (hkeep5 a τ y ha hy) (ha0.1 (.noColl .oU) (by decide))
    · exact hτ y hy .oOmega (Or.inl rfl)
    · exact hτ y hy .oSp (Or.inr rfl)
  · intro a τ y w i ha hout _ ho _ hm
    show muQ N (meaningSigS cs G arr smp₂ ms decT₂ (mgI cs arr Mg₀ mem rd (P14.par Q) uR omW e' n))
        p l i 5 ((actQ N p l 5).2 a) (extS cs G arr smp₂ ms decT₂ c₀ N true 5 _ _ w)
    rw [extS_id cs G arr smp₂ ms decT₂ c₀ N true 5 rfl]
    obtain ⟨h5, rs, gs, hd⟩ := yes a τ y ha hout
    obtain ⟨on, o, sp, lo⟩ := sendO_step Q b1 b2 b3 b4 b5 b6 b7 b8 hbl _ _ rs gs hd
    obtain ⟨_, sA, eN, hc⟩ :=
      (shapeU_iff Q.par nU _ a.1.2).1 ((shapeM_iff Q.par nU nO _ a.1.2).1 h5).1
    have sY : seatedUB Q.par y.1.2 = true :=
      seatedUB_grows Q.par a.1.2 y.1.2 on.grows (by rw [lo]) sA
    have h5l : ∀ j ∈ openL (insLSh true) (outsLSh true) startLSh 5, j = ItemS.omU ∨ j = .pin .oU ∨
        j = .row (.sample .oU) ∨ j = .row .recG ∨ j = .row .loc := by decide
    rcases h5l i ((openSh_iff true 5 i).1 ho) with rfl | rfl | rfl | rfl | rfl
    · have hm' : OmU Q.par uR (rgOf cs arr mem rd) omW y.1.2 w := hm
      show OmU Q.par uR (rgOf cs arr mem rd) omW a.1.2 w
      exact omU_of_same Q.par uR _ omW a.1.2 y.1.2 w (by rw [lo])
        (by rw [huR _ sY, huR _ sA, lo]) hm'
    · exact pin_ridesAt cs G arr smp₂ ms decT₂ N _ p l 5 (⟨heldW c5, base, [d₁, d₂], [], ext₀, err₀⟩
        : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) .oU hB5 a y τ hout
        (fun z hz hs => (hkeep5 a τ y ha hout z hz hs).symm) w hm
    · refine hsr .oU a.1.2 y.1.2 w on.grows ?_ hm
      rw [hnum, elder_at_sends Q b1 b2 b3 b4 b5 b6 b7 b8 hbl b5 (Or.inr rfl) _ rs gs _ hd nU
        (by rw [← eN]; exact noted_of_seatedUB Q.par a.1.2 sA)]
    · exact rowsUL_back OnBytes.Model.Reading.gl 0 Q.par.S.fold.index.answers a.1.2 y.1.2 _ on
        (by rw [lo]) (by rw [hc]; omega) hm
    · exact rowsUL_back OnBytes.Model.Reading.gl Q.par.S.fold.index.answers n a.1.2 y.1.2 _ on
        (by rw [lo]) (by rw [hc]) hm

include hS in
/-- **"send o_omega": the clause at block 5, from K1's law of a sending.** -/
theorem five_at (c5 : Block St Cl) (h5c : DecidesAs c5 b5) (hne : nO ≠ nU) (rad : ℕ → ℕ)
    (hC : condPort (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S)) rad = true) (base : ℕ)
    (d₁ d₂ : RDT) (he₁ : d₁.entry = seedEntry (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S)))
    (hk₁ : d₁.kind = .seeds) (e : ℕ)
    (he : errPort (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S)) rad ≤ e)
    (fOf : Fr.E.Str → ∀ j, (portOmZ (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S)).codes
      (shapeAt (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S)) j) (rad j.val)).Str)
    (fIn : Fr.E.Str → (wT d₁).Msg → ∀ j,
      (portOmZ (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S)).codes
        (shapeAt (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S)) j) (rad j.val)).Str)
    (hf : ∀ y τ, fOf ((sendPiece (W := (Wit Cells Tok MsgT)) (F := Fr) (heldW (U := P₁) c5) base d₁
        d₂ (parK1 Q 5
        "o_omega and o_sp" (withOmega Q.S)).coordinates e).ior.imp y τ) = fIn y τ.1)
    (ext₀ : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d₁, d₂]) → (Wit Cells Tok MsgT) → (Wit
        Cells Tok MsgT))
    (err₀ : Err (uLT (ckP .two) [d₁, d₂]))
    (hsr : SampleRides Mg₀ num) (hnum : num .oU = nU)
    (hB5 : SentBefore N p l 5 (⟨heldW c5, base, [d₁, d₂], [], ext₀, err₀⟩ : Piece (ckP .two) Fr (P₁
        × St) Cl (Wit Cells Tok MsgT)) .oU)
    (hX : ∀ a τ y, onQ₂ N (besideP (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR
        s.book) (pmI decT₂ Pm₀ (P14.par Q) n nU nO)) XX) Oc true p l 5 a →
      (⟨heldW c5, base, [d₁, d₂], [], ext₀, err₀⟩ : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok
          MsgT)).ior.red.out
          a τ = some y → XX 6 y.1.2 = true)
    (hkeep5 : ∀ a τ y, onQ₂ N (besideP (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St =>
        bkR s.book) (pmI decT₂ Pm₀ (P14.par Q) n nU nO)) XX) Oc true p l 5 a →
      (⟨heldW c5, base, [d₁, d₂], [], ext₀, err₀⟩ : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok
          MsgT)).ior.red.out
          a τ = some y →
      ∀ z ∈ ms, SitsAt z (N.tenant .oU).1 (N.tenant .oU).2 →
        smp₂ y.1.2 z.1 z.2 = smp₂ a.1.2 z.1 z.2)
    (hnew : ∀ a τ y, onQ₂ N (besideP (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR
        s.book) (pmI decT₂ Pm₀ (P14.par Q) n nU nO)) XX) Oc true p l 5 a →
      (⟨heldW c5, base, [d₁, d₂], [], ext₀, err₀⟩ : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok
          MsgT)).ior.red.out
          a τ = some y →
      (∀ j, sampledAt (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S)) j →
        Sealed (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S)).codes
          (shapeAt (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S)) j) (rad j.val) (fOf y.2 j)
          y.1.2.st (y.1.2.st.oracles.size -
            (shapesOf (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S))).length + j.val)) →
      ∀ m, m = Msg2.oOmega ∨ m = .oSp →
        (PromS.noColl m).holds N (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR
            s.book) (pmI decT₂ Pm₀ (P14.par Q) n nU nO)) y.1.2 (strsOfAct Fr ((actQ N p l 6).2 y)))
            :
    ClauseAt N (meaningSigS cs G arr smp₂ ms decT₂ (mgI cs arr Mg₀ mem rd (P14.par Q) uR omW e' n))
        (besideP (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR s.book) (pmI decT₂
        Pm₀ (P14.par Q) n nU nO)) XX) Oc true p l (fun k v w => extS cs G arr smp₂ ms decT₂ c₀ N
        true k v.1 (strsOfAct Fr v) w) 5 (⟨heldW c5, base, [d₁, d₂], [], ext₀, err₀⟩ : Piece (ckP
        .two)
        Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
      ((seedMaps d₁ d₂ (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S)).coordinates).err
        ((e, ()) : ℕ × Unit)) := by
  refine five_core cs G arr smp₂ ms decT₂ c₀ bkR N Mg₀ Pm₀ Oc mem rd uR omW e' n nU nO num p l Q XX
      b1
    b2 b3 b4 b5 b6 b7 b8 hbl hS hdk huR c5 h5c hne base d₁ d₂ ext₀ err₀ _ hsr hnum hB5 ?_ hX hkeep5
  have g := send_goodIn_entry (W := (Wit Cells Tok MsgT)) (F := Fr) (parK1 Q 5 "o_omega and o_sp"
      (withOmega Q.S)) rad
      hC
    (heldW c5) (fun t => t.2.st)
    (isSend_as _ c5 b5 h5c (isSend_five_held P₁ Q b1 b2 b3 b4 b5 b6 b7 b8 hbl)) base
    d₁ d₂ he₁ hk₁ e he fOf fIn hf (onQ₂ N (besideP (promSigS cs G smp₂ ms (fun s : St => s.st) (fun
        s : St => bkR s.book) (pmI decT₂ Pm₀ (P14.par Q) n nU nO)) XX) Oc true p l 5) (fun _ =>
        True) (fun _ _ => True)
    (fun _ _ => True) (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ => trivial)
  intro a ha
  exact Doomed.mono _ _ (fun τ hτ y hy => hnew a τ y ha hy (hτ y hy).1.2) (g a ha)

omit hbl hdk huR in
/-- **What a law of a sending gives at a seat** (SendGivesCf's conclusion,
Johnson/Desc/Sound/SendLaw.lean): every leaf is shown, and no two members of the list answer the
    sample
alike, AT THE ACTING PART's VALUE behind the block. -/
theorem cf_gives (k : ℕ) (m : Msg2) (new : List Mem) (y : (P₁ × St) × Fr.E.Str)
    (hcf : ∀ x ∈ new, CfAt G cs x.1.l x.1.seat (fun z : P₁ × St => smp₂ z.2 x.1) x.2 y.1
      (strsOf Fr y.2))
    (hnew : ∀ x ∈ ms, SitsAt x (N.tenant m).1 (N.tenant m).2 → x ∈ new)
    (hmem : ∃ x ∈ ms, SitsAt x (N.tenant m).1 (N.tenant m).2) (h1 : N.lo ≤ (N.tenant m).1)
    (h2 : (N.tenant m).1 < hiAt k p l) :
    shownJT cs G ms (N.tenant m).1 (N.tenant m).2 (strsOfAct Fr ((actQ N p l k).2 y)) ∧
      noCollJT cs G smp₂ ms (N.tenant m).1 (N.tenant m).2 y.1.2
        (strsOfAct Fr ((actQ N p l k).2 y)) := by
  have key : ∀ x ∈ ms, SitsAt x (N.tenant m).1 (N.tenant m).2 →
      CfAt G cs x.1.l x.1.seat (fun z : St => smp₂ z x.1) x.2 y.1.2
        (strsOfAct Fr ((actQ N p l k).2 y)) := by
    intro x hx hs
    have e : (x.1.seat x.2).1 = (N.tenant m).1 := congrArg Prod.fst hs
    obtain ⟨z, hz, hsh, hc⟩ := cfAt_col G cs x.1.l x.1.seat (fun z : P₁ × St => smp₂ z.2 x.1)
      (strsOf Fr y.2) (strsOfAct Fr ((actQ N p l k).2 y)) x.2 y.1
      (fun q => by rw [e]; exact actCol_eq N p l k y _ q h1 h2) (hcf x (hnew x hx hs))
    exact ⟨z, hz, hsh, hc⟩
  exact ⟨⟨hmem, fun x hx hs => (key x hx hs).choose_spec.2.1⟩, key⟩

/-- **"send o_u": the clause at block 2, from a law of a sending BY NAME** (SendGivesCf at
    the
piece). -/
theorem two_cf (c2 : Block St Cl) (h2c : DecidesAs c2 b2) (sentU : Array OracleNotice)
    (hU : withU Q.S = some sentU) (hnO : nO = nU + sentU.size) (base : ℕ) (d₁ d₂ : RDT) (cc e : ℕ)
    (ext₀ : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d₁, d₂]) → (Wit Cells Tok MsgT) → (Wit
        Cells Tok MsgT))
    (err₀ : Err (uLT (ckP .two) [d₁, d₂])) (new : List Mem)
    (hcf : SendGivesCf cs G (fun t : P₁ × St => smp₂ t.2)
      (sendPiece (W := (Wit Cells Tok MsgT)) (F := Fr) (heldW (U := P₁) c2) base d₁ d₂ cc e) new
      (onQ₂ N (besideP (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR s.book) (pmI
          decT₂ Pm₀ (P14.par Q) n nU nO)) XX) Oc true p l 2) fun _ => True)
    (hnew : ∀ x ∈ ms, SitsAt x (N.tenant .oU).1 (N.tenant .oU).2 → x ∈ new)
    (hmem : ∃ x ∈ ms, SitsAt x (N.tenant .oU).1 (N.tenant .oU).2)
    (h1 : N.lo ≤ (N.tenant .oU).1) (h2 : (N.tenant .oU).1 < hiAt 3 p l)
    (hX : ∀ a τ y, onQ₂ N (besideP (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR
        s.book) (pmI decT₂ Pm₀ (P14.par Q) n nU nO)) XX) Oc true p l 2 a → (⟨heldW c2, base, [d₁,
        d₂], [], ext₀, err₀⟩ : Piece
        (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)).ior.red.out a τ = some y →
      XX 3 y.1.2 = true)
    (huN : ∀ s, shapeP Q.par nU s = true → uR s = withNext Q.par s) :
    ClauseAt N (meaningSigS cs G arr smp₂ ms decT₂ (mgI cs arr Mg₀ mem rd (P14.par Q) uR omW e' n))
        (besideP (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR s.book) (pmI decT₂
        Pm₀ (P14.par Q) n nU nO)) XX) Oc true p l (fun k v w => extS cs G arr smp₂ ms decT₂ c₀ N
        true k v.1 (strsOfAct Fr v) w) 2 (⟨heldW c2, base, [d₁, d₂], [], ext₀, err₀⟩ : Piece (ckP
        .two)
        Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
      ((seedMaps d₁ d₂ cc).err ((e, ()) : ℕ × Unit)) := by
  refine two_core cs G arr smp₂ ms decT₂ c₀ bkR N Mg₀ Pm₀ Oc mem rd uR omW e' n nU nO p l Q XX b1 b2
    b3 b4 b5 b6 b7 b8 hbl hdk huR c2 h2c sentU hU hnO base d₁ d₂ ext₀ err₀ _ ?_ hX huN
  intro a ha
  refine Doomed.mono _ _ (fun τ hτ y hy => ?_) (hcf a ha)
  have g := cf_gives cs G smp₂ ms N p l 3 .oU new y (hτ y hy).2 hnew hmem h1 h2
  exact g

include hS in
/-- **"send o_omega": the clause at block 5, from the law of a sending SendGivesCf BY NAME.** -/
theorem five_cf (c5 : Block St Cl) (h5c : DecidesAs c5 b5) (hne : nO ≠ nU) (base : ℕ)
    (d₁ d₂ : RDT) (cc e : ℕ)
    (ext₀ : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d₁, d₂]) → (Wit Cells Tok MsgT) → (Wit
        Cells Tok MsgT))
    (err₀ : Err (uLT (ckP .two) [d₁, d₂]))
    (hsr : SampleRides Mg₀ num) (hnum : num .oU = nU)
    (hB5 : SentBefore N p l 5 (⟨heldW c5, base, [d₁, d₂], [], ext₀, err₀⟩ : Piece (ckP .two) Fr (P₁
        × St) Cl (Wit Cells Tok MsgT)) .oU) (new : List Mem)
    (hcf : SendGivesCf cs G (fun t : P₁ × St => smp₂ t.2)
      (sendPiece (W := (Wit Cells Tok MsgT)) (F := Fr) (heldW (U := P₁) c5) base d₁ d₂ cc e) new
      (onQ₂ N (besideP (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR s.book) (pmI
          decT₂ Pm₀ (P14.par Q) n nU nO)) XX) Oc true p l 5) fun _ => True)
    (hnew : ∀ m, m = Msg2.oOmega ∨ m = .oSp →
      (∀ x ∈ ms, SitsAt x (N.tenant m).1 (N.tenant m).2 → x ∈ new) ∧
        (∃ x ∈ ms, SitsAt x (N.tenant m).1 (N.tenant m).2) ∧ N.lo ≤ (N.tenant m).1 ∧
          (N.tenant m).1 < hiAt 6 p l)
    (hX : ∀ a τ y, onQ₂ N (besideP (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR
        s.book) (pmI decT₂ Pm₀ (P14.par Q) n nU nO)) XX) Oc true p l 5 a → (⟨heldW c5, base, [d₁,
        d₂], [], ext₀, err₀⟩ : Piece
        (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)).ior.red.out a τ = some y →
      XX 6 y.1.2 = true)
    (hkeep5 : ∀ a τ y, onQ₂ N (besideP (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St =>
        bkR s.book) (pmI decT₂ Pm₀ (P14.par Q) n nU nO)) XX) Oc true p l 5 a → (⟨heldW c5, base,
        [d₁, d₂], [], ext₀, err₀⟩ :
        Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)).ior.red.out a τ = some y →
      ∀ z ∈ ms, SitsAt z (N.tenant .oU).1 (N.tenant .oU).2 →
        smp₂ y.1.2 z.1 z.2 = smp₂ a.1.2 z.1 z.2) :
    ClauseAt N (meaningSigS cs G arr smp₂ ms decT₂ (mgI cs arr Mg₀ mem rd (P14.par Q) uR omW e' n))
        (besideP (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR s.book) (pmI decT₂
        Pm₀ (P14.par Q) n nU nO)) XX) Oc true p l (fun k v w => extS cs G arr smp₂ ms decT₂ c₀ N
        true k v.1 (strsOfAct Fr v) w) 5 (⟨heldW c5, base, [d₁, d₂], [], ext₀, err₀⟩ : Piece (ckP
        .two)
        Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
      ((seedMaps d₁ d₂ cc).err ((e, ()) : ℕ × Unit)) := by
  refine five_core cs G arr smp₂ ms decT₂ c₀ bkR N Mg₀ Pm₀ Oc mem rd uR omW e' n nU nO num p l Q XX
      b1
    b2 b3 b4 b5 b6 b7 b8 hbl hS hdk huR c5 h5c hne base d₁ d₂ ext₀ err₀ _ hsr hnum hB5 ?_ hX hkeep5
  intro a ha
  refine Doomed.mono _ _ (fun τ hτ y hy m hm => ?_) (hcf a ha)
  obtain ⟨n1, n2, n3, n4⟩ := hnew m hm
  have g := cf_gives cs G smp₂ ms N p l 6 m new y (hτ y hy).2 n1 n2 n3 n4
  exact g

end Desc.K14.Law
