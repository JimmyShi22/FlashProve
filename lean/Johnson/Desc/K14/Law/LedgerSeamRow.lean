-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/LedgerSeamRow.lean: THE ONE TERM (share_filled,
Johnson/Desc/K14/Law/LedgerFilled.lean) WITH THE CHANCE AT THE TWO SENDINGS PAID: hD2 | hD5 by K1's
law of a sending through the seam (send_cf, Johnson/Desc/K14/Law/LedgerSeam.lean), with
the new messages' numbers by number_two | number_five (Johnson/Desc/K14/Law/LedgerPays.lean). The
codes' letter is the plan's: cs := Q.codes. General in the test X beside shapeK (HandsAt).

  d2_seamed, d5_seamed   hD2 | hD5, in share_row's own form, at any row and any test beside shapeK.
  share_seamed    **the one term**: at our eight blocks (2 … 8, 11) no premise with a price is left;
                  h9 | h10, the two proximity tests' clauses, are premises of it still.
  once_seamed     **the call** at it: charged once, at every number of slots.
WHAT STAYS. AT THE SENDINGS, ALL ON THE PLAN AND THE DATA (twice): hC, he₁, hk₁, he (K1's law's own)
· entry · all · hno (at sampled messages) · htree · hSh · hnew (LedgerSeam.lean's head says each).
THEY FORCE: ms holds JUST ONE member at each of the three seats: so the sendings of ms are K1's
sendings, not the groups' lists, and o_sp has one radius. WHICH: at o_u's seat memK2 0 (by hoU); at
o_omega's | o_sp's seat memK5 k for SOME sampled k: that k is 0 | 1 is forced by nothing here (it
wants the like of hoU at these two seats: ent_at_omega, Johnson/Desc/K14/Law/LedgerLast.lean). h9 |
h10. hX (whoever lays X). The letters decT₂ · Mg₀ (the sample rows; dot) · Pm₀.shape 10 | 11 | 12 ·
oNo · ms · the numbers and the rounds' data: as in LedgerRow.lean's and LedgerFilled.lean's heads.
WHERE THE COUNTS' LETTERS ARE PINNED. e2, e4, e5, e7 are bounded FROM BELOW alone here (he2, he4,
he5, he7): a larger count is a weaker law. They are laid WITH EQUALITY, and the errors shown below
2⁻¹ ^ 128, at the typed plan and the written lists of both files, in other files (EachOwnBelow
128 at ownK: K14OwnAt.lean); the like at "LIN point" in leadsBN_at_cap (K14PointCap.lean); at
9 | 10 in a theorem own_nine_ten, which is not in this library. Nothing of that is in this file.
What is not claimed. NO MEMBER IS SHOWN. It closes no row. No soundness of a verifier; no level.

-/
import Johnson.Desc.K14.Law.LedgerSeam
import Johnson.Desc.K14.Law.LedgerFilled

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Cb Johnson.Pack Desc.Plain
open Iop Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words)
open VerifiableInference.Desc (Block Strs Wit FileDescription Grows)
open VerifiableInference.Desc.ChainEnd (untestedL Exact)
open VerifiableInference.Desc.K1 (sendPiece sampledAt shapeAt shapesOf condPort errPort seedEntry
  seedMaps isSend_two_held isSend_five_held)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared

variable {P₁ Cl Xi Cells Tok : Type} {Fr : Frame} (G : FileDescription Xi) (oNo : Mem → ℕ) (ms : List Mem)
  (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells) (bkR : TreeBook → TreeBook)
  (N : NumbersS) (Q : P14) (Pm₀ : PromMeaning St) (Oc : P₁ → Strs → Prop) (n nU nO : ℕ)
  (p : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (l : List (Piece (ckP .two) Fr (P₁ ×
      St) Cl (Wit Cells Tok MsgT))) (XX : ℕ → St → Bool) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
  (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8])
include hbl

/-- **hD2**, in share_row's own form. -/
theorem d2_seamed (c2 : Block St Cl) (h2c : DecidesAs c2 b2) (sentU : Array OracleNotice)
    (hU : withU Q.S = some sentU) (rad : ℕ → ℕ) (hC : condPort (parU Q sentU) rad = true)
    (base : ℕ) (d₁ d₂ : RDT) (he₁ : d₁.entry = seedEntry (parU Q sentU)) (hk₁ : d₁.kind = .seeds)
    (e : ℕ) (he : errPort (parU Q sentU) rad ≤ e)
    (ext₀ : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d₁, d₂]) → Wit Cells Tok MsgT → Wit Cells
        Tok MsgT)
    (err₀ : Err (uLT (ckP .two) [d₁, d₂]))
    (memK : Fin (shapesOf (parU Q sentU)).length → Mem) (new : List Mem)
    (entry : ∀ k, (memK k).1.l.get (memK k).2 = (shapeAt (parU Q sentU) k, rad k.val))
    (all : ∀ x ∈ new, ∃ k, sampledAt (parU Q sentU) k ∧ memK k = x)
    (hno : ∀ k, sampledAt (parU Q sentU) k → oNo (memK k) = nU + k.val)
    (htree : ∀ k, ∃ j, ((memK k).1.seat (memK k).2).1 = base + j ∧ j < d₁.trees.length)
    (hSh : ∀ x ∈ new, (sendPiece (W := Wit Cells Tok MsgT) (F := Fr) (heldW (U := P₁) c2) base d₁ d₂
      (parU Q sentU).coordinates e).ShownAll G Q.codes x.1.l x.1.seat)
    (hnew : ∀ x ∈ ms, SitsAt x (N.tenant .oU).1 (N.tenant .oU).2 → x ∈ new)
    (hmem : ∃ x ∈ ms, SitsAt x (N.tenant .oU).1 (N.tenant .oU).2)
    (h1 : N.lo ≤ (N.tenant .oU).1) (h2 : (N.tenant .oU).1 < hiAt 3 p l) :
    ∀ a, onQ₂ N (besideP (pm0 Q.codes G (smpSt Q.codes oNo stSh) ms decT₂ bkR Pm₀ n nU nO Q) XX) Oc
        true p l 2 a →
      Doomed (uLT (ckP .two) [d₁, d₂])
        ((seedMaps d₁ d₂ (parU Q sentU).coordinates).err ((e, ()) : ℕ × Unit)) fun τ =>
        ∀ y, (pc2 c2 base d₁ d₂ ext₀ err₀).ior.red.out a τ = some y →
          (PromS.noColl .oU).holds N (pm0 Q.codes G (smpSt Q.codes oNo stSh) ms decT₂ bkR Pm₀ n nU
              nO Q) y.1.2
            (strsOfAct Fr ((actQ N p l 3).2 y)) := by
  intro a ha
  refine Doomed.mono _ _ (fun τ hτ y hy => ?_)
    (send_cf (W := Wit Cells Tok MsgT) G (parU Q sentU) rad hC (heldW c2)
      (isSend_as _ c2 b2 h2c (isSend_two_held P₁ Q b1 b2 b3 b4 b5 b6 b7 b8 hbl sentU hU)) base d₁ d₂
      he₁ hk₁ e he oNo memK new _ entry all
      (fun a τ x ha hx k hk => by
        rw [hno k hk]
        exact (number_two Q.codes G (smpSt Q.codes oNo stSh) ms decT₂ bkR N Pm₀ Oc n nU nO p l Q XX
            b1
          b2 b3 b4 b5 b6 b7 b8 hbl sentU hU c2 h2c _ rfl a τ x ha hx k.val).symm)
      htree hSh a ha)
  exact cf_gives Q.codes G (smpSt Q.codes oNo stSh) ms N p l 3 .oU new y (hτ y hy).2 hnew hmem h1 h2

/-- **hD5**, in share_row's own form. -/
theorem d5_seamed (c5 : Block St Cl) (h5c : DecidesAs c5 b5) (sentU : Array OracleNotice)
    (hU : withU Q.S = some sentU) (rad : ℕ → ℕ) (hC : condPort (parO Q) rad = true)
    (base : ℕ) (d₁ d₂ : RDT) (he₁ : d₁.entry = seedEntry (parO Q)) (hk₁ : d₁.kind = .seeds)
    (e : ℕ) (he : errPort (parO Q) rad ≤ e)
    (ext₀ : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d₁, d₂]) → Wit Cells Tok MsgT → Wit Cells
        Tok MsgT)
    (err₀ : Err (uLT (ckP .two) [d₁, d₂]))
    (memK : Fin (shapesOf (parO Q)).length → Mem) (new : List Mem)
    (entry : ∀ k, (memK k).1.l.get (memK k).2 = (shapeAt (parO Q) k, rad k.val))
    (all : ∀ x ∈ new, ∃ k, sampledAt (parO Q) k ∧ memK k = x)
    (hno : ∀ k, sampledAt (parO Q) k → oNo (memK k) = nO + k.val)
    (htree : ∀ k, ∃ j, ((memK k).1.seat (memK k).2).1 = base + j ∧ j < d₁.trees.length)
    (hSh : ∀ x ∈ new, (sendPiece (W := Wit Cells Tok MsgT) (F := Fr) (heldW (U := P₁) c5) base d₁ d₂
      (parO Q).coordinates e).ShownAll G Q.codes x.1.l x.1.seat)
    (hnew : ∀ m, m = Msg2.oOmega ∨ m = .oSp →
      (∀ x ∈ ms, SitsAt x (N.tenant m).1 (N.tenant m).2 → x ∈ new) ∧
        (∃ x ∈ ms, SitsAt x (N.tenant m).1 (N.tenant m).2) ∧ N.lo ≤ (N.tenant m).1 ∧
          (N.tenant m).1 < hiAt 6 p l) :
    ∀ a, onQ₂ N (besideP (pm0 Q.codes G (smpSt Q.codes oNo stSh) ms decT₂ bkR Pm₀ n nU nO Q) XX) Oc
        true p l 5 a →
      Doomed (uLT (ckP .two) [d₁, d₂])
        ((seedMaps d₁ d₂ (parO Q).coordinates).err ((e, ()) : ℕ × Unit)) fun τ =>
        ∀ y, (pc2 c5 base d₁ d₂ ext₀ err₀).ior.red.out a τ = some y →
          ∀ m, m = Msg2.oOmega ∨ m = .oSp →
            (PromS.noColl m).holds N (pm0 Q.codes G (smpSt Q.codes oNo stSh) ms decT₂ bkR Pm₀ n nU
                nO Q) y.1.2
              (strsOfAct Fr ((actQ N p l 6).2 y)) := by
  intro a ha
  refine Doomed.mono _ _ (fun τ hτ y hy m hm => ?_)
    (send_cf (W := Wit Cells Tok MsgT) G (parO Q) rad hC (heldW c5)
      (isSend_as _ c5 b5 h5c (isSend_five_held P₁ Q b1 b2 b3 b4 b5 b6 b7 b8 hbl)) base d₁ d₂
      he₁ hk₁ e he oNo memK new _ entry all
      (fun a τ x ha hx k hk => by
        rw [hno k hk]
        exact (number_five Q.codes G (smpSt Q.codes oNo stSh) ms decT₂ bkR N Pm₀ Oc n nU nO p l Q XX
            b1
          b2 b3 b4 b5 b6 b7 b8 hbl sentU hU c5 h5c _ rfl a τ x ha hx k.val).symm)
      htree hSh a ha)
  obtain ⟨n1, n2, n3, n4⟩ := hnew m hm
  exact cf_gives Q.codes G (smpSt Q.codes oNo stSh) ms N p l 6 m new y (hτ y hy).2 n1 n2 n3 n4

omit hbl

variable (arr : ℕ → ℕ → ℕ) (c₀ : Cells) (Mg₀ : MeaningS St P₁ (Wit Cells Tok MsgT))
  (mem : ℕ → Option Mem) (rd : (x : Mem) → ((sigOf Q.codes x.1.l).om x.2).Msg → Part → ℕ → GE)
  (e' : ℕ) (num : Msg2 → ℕ) (sentU : Array OracleNotice) (X : ℕ → St → Bool)
  (c2 c3 c4 c5 c6 c7 c8 c11 : Block St Cl)
  (f pt x3 x6 x8 x9 x10 x11 : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
  (base2 : ℕ) (d21 d22 : RDT)
  (ex2 : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d21, d22]) → Wit Cells Tok MsgT → Wit Cells
      Tok MsgT)
  (er2 : Err (uLT (ckP .two) [d21, d22]))
  (base4 : ℕ) (d4 : RDT) (ex4 : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d4]) → Wit Cells Tok
      MsgT → Wit Cells Tok MsgT)
  (er4 : Err (uLT (ckP .two) [d4]))
  (base5 : ℕ) (d51 d52 : RDT)
  (ex5 : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d51, d52]) → Wit Cells Tok MsgT → Wit Cells
      Tok MsgT)
  (er5 : Err (uLT (ckP .two) [d51, d52]))
  (base7 : ℕ) (d7 : RDT) (ex7 : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d7]) → Wit Cells Tok
      MsgT → Wit Cells Tok MsgT)
  (er7 : Err (uLT (ckP .two) [d7]))
  (ht : Tiled (pc2 c2 base2 d21 d22 ex2 er2) [x3, (pc1 c4 base4 d4 ex4 er4), (pc2 c5 base5 d51 d52
      ex5 er5), x6, (pc1 c7 base7 d7 ex7 er7), x8, x9, x10, x11])
  (hlo : ∀ m, N.lo ≤ (N.tenant m).1) (tU : (N.tenant .oU).1 < x3.base)
  (tO : (N.tenant .oOmega).1 < x6.base) (tS : (N.tenant .oSp).1 < x6.base)
  (hS : Q.S.sharedSplitNeeded = true)
  (hdk : ∀ c (s s' : St), s'.loc.key = s.loc.key → decT₂ c s' = decT₂ c s)
  (hsr : SampleRides Mg₀ num) (hnum : num .oU = nU)
  (h2c : DecidesAs c2 b2) (h3c : DecidesAs c3 b3) (h4c : DecidesAs c4 b4) (h5c : DecidesAs c5 b5)
  (h6c : DecidesAs c6 b6) (h7c : DecidesAs c7 b7) (h8c : DecidesAs c8 b8) (h2r : c2.rounds =
      b2.rounds) (h3r : c3.rounds = b3.rounds) (h4r : c4.rounds = b4.rounds) (h5r : c5.rounds =
      b5.rounds) (h6r : c6.rounds = b6.rounds) (h8r : c8.rounds = b8.rounds)
  (hx3 : x3.b = heldW c3) (hx6 : x6.b = heldW c6) (hx8 : x8.b = heldW c8)
  (hx11 : x11.b = heldW c11) (he11 : Exact (fun d : St => untestedL d.st) c11)
  (xU xO : Mem) (hU : mem nU = some xU) (hO : mem nO = some xO) (mU : xU ∈ ms) (mO : xO ∈ ms)
  (sU : SitsAt xU (N.tenant .oU).1 (N.tenant .oU).2)
  (sO : SitsAt xO (N.tenant .oOmega).1 (N.tenant .oOmega).2)
  (hUw : withU Q.S = some sentU) (hn0 : nU = 0) (hnO : nO = nU + sentU.size)
  (hX : HandsAt (Cl := Cl) (Cells := Cells) (Tok := Tok) (onQ₂ N (pmK Q.codes G (smpSt Q.codes oNo
      stSh) ms decT₂ (shiftBook N.lo) Pm₀ n nU nO Q X) Oc true f (pt :: [(pc2 c2 base2 d21 d22 ex2
      er2), x3, (pc1 c4 base4 d4 ex4 er4), (pc2 c5 base5 d51 d52 ex5 er5), x6, (pc1 c7 base7 d7 ex7
      er7), x8, x9, x10, x11])) [b1, b2, b3, b4, b5, b6, b7, b8] X)
  (hoU : ∀ z ∈ ms, SitsAt z (N.tenant .oU).1 (N.tenant .oU).2 → oNo z = nU)
  -- "send o_u": the plan's and the data's
  (rad2 : ℕ → ℕ) (hC2 : condPort (parU Q sentU) rad2 = true)
  (he12 : d21.entry = seedEntry (parU Q sentU)) (hk12 : d21.kind = .seeds) (e2 : ℕ)
  (he2 : errPort (parU Q sentU) rad2 ≤ e2)
  (memK2 : Fin (shapesOf (parU Q sentU)).length → Mem) (new2 : List Mem)
  (entry2 : ∀ k, (memK2 k).1.l.get (memK2 k).2 = (shapeAt (parU Q sentU) k, rad2 k.val))
  (all2 : ∀ x ∈ new2, ∃ k, sampledAt (parU Q sentU) k ∧ memK2 k = x)
  (hno2 : ∀ k, sampledAt (parU Q sentU) k → oNo (memK2 k) = nU + k.val)
  (htree2 : ∀ k, ∃ j, ((memK2 k).1.seat (memK2 k).2).1 = base2 + j ∧ j < d21.trees.length)
  (hSh2 : ∀ x ∈ new2, (sendPiece (W := Wit Cells Tok MsgT) (F := Fr) (heldW (U := P₁) c2) base2 d21
      d22
    (parU Q sentU).coordinates e2).ShownAll G Q.codes x.1.l x.1.seat)
  (hnew2 : ∀ x ∈ ms, SitsAt x (N.tenant .oU).1 (N.tenant .oU).2 → x ∈ new2)
  -- "LOC"
  {ns4 : ℕ} (hd4 : SendsDraws (toRD d4) ns4 0 n Q.par.S.fold.index.code.logN)
  (ho4 : d4.opens = []) (e4 : ℕ) (he4 : (2 ^ Q.par.S.fold.index.code.logN - e' - 1) ^ n ≤ e4)
  -- "send o_omega": the plan's and the data's
  (rad5 : ℕ → ℕ) (hC5 : condPort (parO Q) rad5 = true)
  (he15 : d51.entry = seedEntry (parO Q)) (hk15 : d51.kind = .seeds) (e5 : ℕ)
  (he5 : errPort (parO Q) rad5 ≤ e5)
  (memK5 : Fin (shapesOf (parO Q)).length → Mem) (new5 : List Mem)
  (entry5 : ∀ k, (memK5 k).1.l.get (memK5 k).2 = (shapeAt (parO Q) k, rad5 k.val))
  (all5 : ∀ x ∈ new5, ∃ k, sampledAt (parO Q) k ∧ memK5 k = x)
  (hno5 : ∀ k, sampledAt (parO Q) k → oNo (memK5 k) = nO + k.val)
  (htree5 : ∀ k, ∃ j, ((memK5 k).1.seat (memK5 k).2).1 = base5 + j ∧ j < d51.trees.length)
  (hSh5 : ∀ x ∈ new5, (sendPiece (W := Wit Cells Tok MsgT) (F := Fr) (heldW (U := P₁) c5) base5 d51
      d52
    (parO Q).coordinates e5).ShownAll G Q.codes x.1.l x.1.seat)
  (hnew5 : ∀ m, m = Msg2.oOmega ∨ m = .oSp →
    ∀ x ∈ ms, SitsAt x (N.tenant m).1 (N.tenant m).2 → x ∈ new5)
  (xS : Mem) (mS : xS ∈ ms) (sS : SitsAt xS (N.tenant .oSp).1 (N.tenant .oSp).2)
  -- "LIN zeta"
  {ns7 a7 : ℕ} (hd7 : SendsDraws (toRD d7) ns7 Q.par.S.kRow 0 a7) (e7 : ℕ)
  (he7 : Q.par.S.kRow * Fintype.card GE ^ (Q.par.S.kRow - 1) ≤ e7)
  (hS12 : ∀ s, Pm₀.shape 11 s = true → Pm₀.shape 12 s = true)
  (own : OwnErrs (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
  (ho2' : own 2 (pc2 c2 base2 d21 d22 ex2 er2) = ((seedMaps d21 d22 (parU Q sentU).coordinates).err
      ((e2, ()) : ℕ × Unit)))
  (ho4' : own 4 (pc1 c4 base4 d4 ex4 er4) = (posMaps d4 Q.par.S.fold.index.code.logN n).err ((e4,
      ()) : ℕ × Unit))
  (ho5' : own 5 (pc2 c5 base5 d51 d52 ex5 er5) = ((seedMaps d51 d52 (parO Q).coordinates).err ((e5,
      ()) : ℕ × Unit)))
  (ho7' : own 7 (pc1 c7 base7 d7 ex7 er7) = (vecMaps d7 Q.par.S.kRow).err ((e7, ()) : ℕ × Unit))
  (h9 : ClauseAt N (mgK Q.codes G arr (smpSt Q.codes oNo stSh) ms decT₂ Mg₀ mem rd e' n nO Q) (pmK
      Q.codes G (smpSt Q.codes oNo stSh) ms decT₂ (shiftBook N.lo) Pm₀ n nU nO Q X) Oc true f (pt ::
          [(pc2 c2 base2 d21 d22 ex2 er2), x3, (pc1 c4 base4 d4 ex4 er4),
      (pc2 c5 base5 d51 d52 ex5 er5), x6, (pc1 c7 base7 d7 ex7 er7), x8, x9, x10, x11]) (exK Q.codes
      G arr (smpSt Q.codes oNo stSh) ms decT₂ c₀ N Fr) 9 x9 (own 9 x9))
  (h10 : ClauseAt N (mgK Q.codes G arr (smpSt Q.codes oNo stSh) ms decT₂ Mg₀ mem rd e' n nO Q) (pmK
      Q.codes G (smpSt Q.codes oNo stSh) ms decT₂ (shiftBook N.lo) Pm₀ n nU nO Q X) Oc true f (pt ::
          [(pc2 c2 base2 d21 d22 ex2 er2), x3, (pc1 c4 base4 d4 ex4 er4),
      (pc2 c5 base5 d51 d52 ex5 er5), x6, (pc1 c7 base7 d7 ex7 er7), x8, x9, x10, x11]) (exK Q.codes
      G arr (smpSt Q.codes oNo stSh) ms decT₂ c₀ N Fr) 10 x10 (own 10 x10))
include hbl ht hlo tU tO tS hS hdk hsr hnum h2c h3c h4c h5c h6c h7c h8c h2r h3r h4r h5r h6r h8r hx3
    hx6 hx8 hx11 he11 hU hO
    mU
  mO sU sO hUw hn0 hnO hX hoU hC2 he12 hk12 he2 entry2 all2 hno2 htree2 hSh2 hnew2 hd4 ho4
      he4
  hC5 he15 hk15 he5 entry5 all5 hno5 htree5 hSh5 hnew5 mS sS hd7 he7 hS12 ho2' ho4' ho5' ho7' h9 h10

/-- **THE ONE TERM, with the chance at the two sendings paid.** -/
theorem share_seamed : EachPlainShOwn N (mgK Q.codes G arr (smpSt Q.codes oNo stSh) ms decT₂ Mg₀ mem
    rd e' n nO Q) (pmK Q.codes G (smpSt Q.codes oNo stSh) ms decT₂ (shiftBook N.lo) Pm₀ n nU nO Q
    X) Oc true f (pt :: [(pc2 c2 base2 d21 d22 ex2 er2), x3, (pc1 c4 base4
    d4 ex4 er4), (pc2 c5 base5 d51 d52 ex5 er5), x6, (pc1 c7 base7 d7 ex7 er7), x8, x9, x10, x11])
    (exK Q.codes G arr (smpSt Q.codes oNo stSh) ms decT₂ c₀ N Fr) own 2 [(pc2 c2 base2 d21 d22 ex2
    er2), x3, (pc1 c4 base4 d4 ex4 er4), (pc2 c5 base5 d51 d52 ex5 er5), x6, (pc1 c7 base7 d7 ex7
    er7), x8, x9, x10, x11] :=
  share_filled Q.codes G arr oNo ms decT₂ c₀ N Mg₀ Pm₀ Oc mem rd e' n nU nO num Q sentU X b1
      b2 b3 b4 b5 b6 b7 b8 c2 c3 c4 c5 c6 c7 c8 c11 f pt x3 x6 x8 x9 x10 x11 base2 d21 d22 ex2 er2
      base4 d4 ex4 er4 base5 d51 d52 ex5 er5 base7 d7 ex7 er7 ht hlo tU tO tS hbl hS hdk hsr hnum
      h2c h3c h4c h5c h6c h7c h8c h2r h3r h4r h5r h6r h8r hx3 hx6 hx8 hx11 he11 xU xO hU hO mU mO sU
          sO hUw hn0 hnO hX hoU
    ((seedMaps d21 d22 (parU Q sentU).coordinates).err ((e2, ()) : ℕ × Unit))
    (d2_seamed G oNo ms decT₂ (shiftBook N.lo) N Q Pm₀ Oc n nU nO f (pt :: [(pc2 c2 base2 d21 d22
        ex2 er2), x3, (pc1 c4 base4 d4 ex4 er4), (pc2 c5 base5 d51 d52 ex5 er5), x6, (pc1 c7 base7
        d7 ex7 er7), x8, x9, x10, x11]) (besX Q X) b1 b2 b3 b4 b5 b6 b7 b8
        hbl c2 h2c sentU hUw rad2 hC2 base2 d21 d22 he12 hk12 e2 he2 ex2 er2 memK2 new2 entry2 all2
        hno2 htree2 hSh2 hnew2 ⟨xU, mU, sU⟩ (hlo .oU) tU)
    hd4 ho4 e4 he4
    ((seedMaps d51 d52 (parO Q).coordinates).err ((e5, ()) : ℕ × Unit))
    (d5_seamed G oNo ms decT₂ (shiftBook N.lo) N Q Pm₀ Oc n nU nO f (pt :: [(pc2 c2 base2 d21 d22
        ex2 er2), x3, (pc1 c4 base4 d4 ex4 er4), (pc2 c5 base5 d51 d52 ex5 er5), x6, (pc1 c7 base7
        d7 ex7 er7), x8, x9, x10, x11]) (besX Q X) b1 b2 b3 b4 b5 b6 b7 b8
        hbl c5 h5c sentU hUw rad5 hC5 base5 d51 d52 he15 hk15 e5 he5 ex5 er5 memK5 new5 entry5 all5
        hno5 htree5 hSh5
      (fun m hm' => by
        rcases hm' with rfl | rfl
        · exact ⟨hnew5 _ (Or.inl rfl), ⟨xO, mO, sO⟩, hlo _, tO⟩
        · exact ⟨hnew5 _ (Or.inr rfl), ⟨xS, mS, sS⟩, hlo _, tS⟩))
    hd7 e7 he7 hS12 own ho2' ho4' ho5' ho7' h9 h10

/-- **THE CALL: charged once.** -/
theorem once_seamed (slots : ℕ) (hh : EachHands (actQ N f (pt :: [(pc2 c2 base2 d21 d22 ex2 er2),
    x3, (pc1 c4 base4 d4 ex4 er4), (pc2 c5 base5 d51 d52 ex5 er5), x6, (pc1 c7 base7 d7 ex7 er7),
    x8, x9, x10, x11])) 2 [(pc2 c2 base2 d21 d22 ex2 er2), x3, (pc1 c4 base4 d4 ex4 er4), (pc2 c5
    base5 d51 d52 ex5 er5), x6, (pc1 c7 base7 d7 ex7 er7), x8, x9, x10, x11])
    (hr : EachRides N (mgK Q.codes G arr (smpSt Q.codes oNo stSh) ms decT₂ Mg₀ mem rd e' n nO Q)
        (pmK Q.codes G (smpSt Q.codes oNo stSh) ms decT₂ (shiftBook N.lo) Pm₀ n nU nO Q X) Oc true f
            (pt :: [(pc2 c2 base2 d21 d22 ex2 er2), x3, (pc1 c4 base4 d4 ex4
        er4), (pc2 c5 base5 d51 d52 ex5 er5), x6, (pc1 c7 base7 d7 ex7 er7), x8, x9, x10, x11]) (exK
        Q.codes G arr (smpSt Q.codes oNo stSh) ms decT₂ c₀ N Fr) 2 [(pc2 c2 base2 d21 d22 ex2 er2),
        x3, (pc1 c4 base4 d4 ex4 er4), (pc2 c5 base5 d51 d52 ex5 er5), x6, (pc1 c7 base7 d7 ex7
        er7), x8, x9, x10, x11]) :
    EachLawsBNOwn (keyE N f (pt :: [(pc2 c2 base2 d21 d22 ex2 er2), x3, (pc1 c4 base4 d4 ex4 er4),
        (pc2 c5 base5 d51 d52 ex5 er5), x6, (pc1 c7 base7 d7 ex7 er7), x8, x9, x10, x11])) (onQ₂ N
        (pmK Q.codes G (smpSt Q.codes oNo stSh) ms decT₂ (shiftBook N.lo) Pm₀ n nU nO Q X) Oc true f
            (pt :: [(pc2 c2 base2 d21 d22 ex2 er2), x3, (pc1 c4 base4 d4 ex4
        er4), (pc2 c5 base5 d51 d52 ex5 er5), x6, (pc1 c7 base7 d7 ex7 er7), x8, x9, x10, x11]))
      (stepE N (mgK Q.codes G arr (smpSt Q.codes oNo stSh) ms decT₂ Mg₀ mem rd e' n nO Q) (pmK
          Q.codes G (smpSt Q.codes oNo stSh) ms decT₂ (shiftBook N.lo) Pm₀ n nU nO Q X) Oc true f
              (pt :: [(pc2 c2 base2 d21 d22 ex2 er2), x3, (pc1 c4 base4 d4
          ex4 er4), (pc2 c5 base5 d51 d52 ex5 er5), x6, (pc1 c7 base7 d7 ex7 er7), x8, x9, x10,
          x11]) fun k a _ w => (exK Q.codes G arr (smpSt Q.codes oNo stSh) ms decT₂ c₀ N Fr) k
          ((actQ N f (pt :: [(pc2 c2 base2 d21 d22 ex2 er2), x3, (pc1 c4 base4 d4 ex4 er4), (pc2 c5
          base5 d51 d52 ex5 er5), x6, (pc1 c7 base7 d7 ex7 er7), x8, x9, x10, x11]) k).2 a) w) slots
          own 2 [(pc2 c2 base2 d21 d22 ex2 er2), x3, (pc1 c4 base4 d4 ex4 er4), (pc2 c5 base5 d51
          d52 ex5 er5), x6, (pc1 c7 base7 d7 ex7 er7), x8, x9, x10, x11] :=
  eachLawsBNOwn_plain N (mgK Q.codes G arr (smpSt Q.codes oNo stSh) ms decT₂ Mg₀ mem rd e' n nO Q)
      (pmK Q.codes G (smpSt Q.codes oNo stSh) ms decT₂ (shiftBook N.lo) Pm₀ n nU nO Q X) Oc true f
          (pt :: [(pc2 c2 base2 d21 d22 ex2 er2), x3, (pc1 c4 base4 d4 ex4
      er4), (pc2 c5 base5 d51 d52 ex5 er5), x6, (pc1 c7 base7 d7 ex7 er7), x8, x9, x10, x11]) (exK
      Q.codes G arr (smpSt Q.codes oNo stSh) ms decT₂ c₀ N Fr) slots own [(pc2 c2 base2 d21 d22 ex2
      er2), x3, (pc1 c4 base4 d4 ex4 er4), (pc2 c5 base5 d51 d52 ex5 er5), x6, (pc1 c7 base7 d7 ex7
      er7), x8, x9, x10, x11] 2 (Nat.le_refl 2) hh
    (share_seamed G oNo ms decT₂ N Q Pm₀ Oc n nU nO b1 b2 b3 b4 b5 b6 b7 b8 hbl arr c₀ Mg₀ mem rd e'
        num sentU X c2 c3 c4 c5 c6 c7 c8 c11 f pt x3 x6 x8 x9 x10 x11 base2 d21 d22 ex2 er2
        base4 d4 ex4 er4 base5 d51 d52 ex5 er5 base7 d7 ex7 er7 ht hlo tU tO tS hS hdk hsr hnum h2c
        h3c h4c h5c h6c h7c h8c h2r h3r h4r h5r h6r h8r hx3 hx6 hx8 hx11 he11 xU xO hU hO mU mO sU
            sO hUw hn0 hnO hX hoU
            rad2 hC2 he12 hk12 e2 he2 memK2 new2 entry2 all2 hno2 htree2 hSh2 hnew2 hd4 ho4 e4 he4
        rad5 hC5 he15 hk15 e5 he5 memK5 new5 entry5 all5 hno5 htree5 hSh5 hnew5 xS mS sS hd7 e7 he7
        hS12 own ho2' ho4' ho5' ho7' h9 h10) hr

end Desc.K14.Law

#print axioms Desc.K14.Law.d2_seamed
#print axioms Desc.K14.Law.d5_seamed
#print axioms Desc.K14.Law.share_seamed
#print axioms Desc.K14.Law.once_seamed
