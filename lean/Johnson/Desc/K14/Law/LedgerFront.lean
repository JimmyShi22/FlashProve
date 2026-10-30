-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerFront.lean: AT THE SHARED CHAIN's FRONT BLOCK, WHAT A SLOT HAS OF ITS OWN
RIDES, AT THE LEDGER's ONE FILLING. One binder of ledger_at_cap
(Johnson/Desc/K14/Law/LedgerAtCap.lean: hFR : FrontRides …) is had from nine others.

  front_rides_tied   FrontRides (Johnson/Desc/Sound/SharedJointCountLedger.lean) at the numbers
                     tiedNumbers N₁ Ns, the items' meaning mgK at tiedMeaning get Mg₁ MgS, and the
                     slot's own condition ocWith (ocEnd get N₁ Mg₁ links ps) R; the first table's
                     meaning Mg₁, R, the promise's meaning, the samples' reader, MgS and the pieces
                     behind the front are letters.
  front_rides_at_K   the same with N, Oc, Mg₀ as letters under the user's equations eN, eO, eM₀, and
                     the front block's base tied to "LIN point"'s (hfb).
HOW. The slot's own condition goes on by ocRides (Johnson/Desc/Sound/OcRides.lean): the first
chain's last promise reads the stored table and the trees below lo alone (ocEndReadsBelow, from
hread), and R reads no oracle (ocWith_readsBelow, Johnson/Desc/Sound/PointReached.lean). The four
own items that are open at border 0: W's and the index masks' pins read their own tree alone
(pin₁_col_eq, Johnson/Desc/Sound/ReadsBelowEq.lean, from hpin), and a piece leaves the columns of
the trees below its base (colStays); "no mark" reads no oracle; THAT THE FIRST TABLE's SENTENCE ON
THE PENDING ROWS READS NONE IS A PREMISE (hpo).
frontRides_of_below (SharedJointCountLedger.lean) is NOT called: it asks Ns.lo ≤ the front block's
base, which is no premise of the user; here the letter lo and W's and the masks' trees are held
against the base instead (hlo, hw, hi).
What is not claimed. That a front block keeps the state (hf1). No instance. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.LedgerSeamRow
import Johnson.Desc.Sound.PointAtOcEnd
import Johnson.Desc.Sound.PointReached
import Johnson.Desc.Sound.ReadsBelowEq
import Johnson.Desc.Sound.SamplesAtK14
import Johnson.Desc.Sound.SharedJointCountLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open VerifiableInference.Desc.Sound (LettersReadBelow ocEndReadsBelow pinJT)
open VerifiableInference.Desc.K13.Law (WRow evalLaidB wSitsB wSeatB wSitsItem)
open OnBytes.Means (wordsOn)
open VerifiableInference.Desc (Strs)
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Run OnBytes.Maker OnBytes.Flat
open Johnson.Pack
open VerifiableInference.Desc (Block Strs Wit FileDescription First.S)
open VerifiableInference.Desc.First (Meaning Numbers ModelPart openSets start)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.K13 (Where)

/-- **What a slot has of its own rides past the front block**, at the tied letters. -/
theorem front_rides_tied {P₀ P₁ Cl Xi Cells Tok : Type} {Fr : Frame} (cs : OnBytes.Codes)
    (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
    (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells)
    (mem : ℕ → Option Mem) (rd : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg → Part → ℕ → GE)
    (e' n nO : ℕ) (Q : P14) (get : P₁ → P₀ × First.S)
    (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) →
      Option ((sigOf cs s.l).om i).Smp)
    (ms₁ : List Mem)
    (stOf₁ : P₀ × First.S → Statement) (tabP₁ : P₀ × First.S → Wit Cells Tok MsgT → Nat → MsgT)
    (Pw : Where) (wSeat : ℕ × ℕ) (matC : Cells → Nat → Nat → GE)
    (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT)) (MgS : MeaningS St P₁ (Wit Cells Tok MsgT))
    (N₁ : Numbers) (Ns : NumbersS) (links : List ModelPart)
    (ps : List VerifiableInference.Desc.Place) (lo : ℕ) (R : P₁ → Prop) (Pm : PromMeaning St)
      (split : Bool)
    (f : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
    (l : List (Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)))
    (hpin : Mg₁.pin = fun j t a y w => pinJT cs G arr smp₁ ms₁ j t a y w)
    (hpo : ∀ a (y y' : Strs) (w : Wit Cells Tok MsgT), Mg₁.pileOne a y w → Mg₁.pileOne a y' w)
    (hread : LettersReadBelow lo N₁ Mg₁ ((openSets links ps (start links))[ps.length]?.getD []))
    (hlo : lo ≤ f.base) (hw : N₁.w.1 < f.base) (hi : N₁.index.1 < f.base)
    (hf1 : ∀ a τ b, f.ior.red.out a τ = some b → b.1 = a.1) :
    FrontRides (tiedNumbers N₁ Ns)
      (mgK cs G arr smp₂ ms decT₂
        (tiedMeaning get Mg₁ MgS)
        mem rd e' n nO Q) Pm
      (ocWith (ocEnd get N₁ Mg₁ links
        ps) R)
      split f l := by
  intro a τ b ha hb
  refine ⟨?_, fun w hw' i hi' => ?_⟩
  · exact ocRides _ _ _ _ _ Fr Prod.fst lo _ f
      (ocWith_readsBelow lo _ R (ocEndReadsBelow P₁ P₀ _ get lo N₁ Mg₁ links ps hread)) hlo (fun a
        τ b h => congrArg Prod.fst (hf1 a τ b h)) a τ b
        ha.2 hb
  · have h1 := hw' i hi'
    rw [hf1 a τ b hb, out_behind f a b τ hb] at h1
    rw [show ownAt 0 = [ItemS.unmarked1, .pinI, .pinV, .claimM] from rfl] at hi'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
    rcases hi' with rfl | rfl | rfl | rfl
    · exact h1
    · refine VerifiableInference.Desc.Sound.pin₁_col_eq cs G arr smp₁ ms₁ Mg₁ hpin get MgS
        _ _ _ _ _ w ?_ h1
      exact fun x => (colStays _ Fr f.base f.ds a.2 τ _ x hi).symm
    · refine VerifiableInference.Desc.Sound.pin₁_col_eq cs G arr smp₁ ms₁ Mg₁ hpin get MgS
        _ _ _ _ _ w ?_ h1
      exact fun x => (colStays _ Fr f.base f.ds a.2 τ _ x hw).symm
    · exact hpo _ _ _ _ h1

/-- **hFR**, at the user's own letters. -/
theorem front_rides_at_K {P₀ P₁ Cl Xi Cells Tok : Type} {Fr : Frame} (G : FileDescription Xi)
    (oNo : Mem → ℕ) (ms : List Mem)
    (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells) (N : NumbersS) (Q : P14)
    (Pm₀ : PromMeaning St) (Oc : P₁ → Strs → Prop) (nU nO : ℕ) (b1 : Block St Unit)
    (arr : ℕ → ℕ → ℕ) (Mg₀ : MeaningS St P₁ (Wit Cells Tok MsgT)) (mem : ℕ → Option Mem)
    (rd : (x : Mem) → ((sigOf Q.codes x.1.l).om x.2).Msg → Part → ℕ → GE) (X : ℕ → St → Bool)
    (get : P₁ → P₀ × First.S)
    (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) →
      Option ((sigOf Q.codes s.l).om i).Smp)
    (ms₁ : List Mem) (xW : Mem)
    (stOf₁ : P₀ × First.S → Statement) (tabP₁ : P₀ × First.S → Wit Cells Tok MsgT → Nat → MsgT)
    (base : Nat) (d : RDT)
    (ext : (P₁ × St) × Fr.E.Str → Tr (uLT (ckP .two) [d]) → Wit Cells Tok MsgT →
      Wit Cells Tok MsgT)
    (err : Err (uLT (ckP .two) [d])) (N₁ : Numbers) (Ns : NumbersS) (links : List ModelPart)
    (ps : List VerifiableInference.Desc.Place) (gOf : P₁ → Nat → GE) (lo : Nat) (R : P₁ → Prop)
      (err₂ eM : Nat)
    (rank : ((Fin Q.par.S.fold.index.v → Bool) →
      Fin (Q.par.S.fold.index.code.r + Q.par.S.fold.index.code.ell) → GE) → Nat)
    (held : ((ixOf2 Q.par.S.fold err₂ eM rank).Row × Fin Q.par.S.fold.index.code.ell → GE) →
      Option Cells)
    (Pw : Where) (matC : Cells → Nat → Nat → GE) (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT))
    (MgZ : MeaningS St P₁ (Wit Cells Tok MsgT))
    (hpin : Mg₁.pin = fun j t a y w => pinJT Q.codes G arr smp₁ ms₁ j t a y w)
    (hpo : ∀ a (y y' : Strs) (w : Wit Cells Tok MsgT), Mg₁.pileOne a y w → Mg₁.pileOne a y' w)
    (hread : LettersReadBelow lo N₁ Mg₁ ((openSets links ps (start links))[ps.length]?.getD []))
    (hloB : lo ≤ base) (hw : N₁.w.1 < base) (hi : N₁.index.1 < base)
    (c2 c4 c5 c7 : Block St Cl)
    (f x3 x6 x8 x9 x10 x11 : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
    (base2 : ℕ) (d21 d22 : RDT)
    (ex2 : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d21, d22]) → Wit Cells Tok MsgT →
      Wit Cells Tok MsgT)
    (er2 : Err (uLT (ckP .two) [d21, d22])) (base4 : ℕ) (d4 : RDT)
    (ex4 : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d4]) → Wit Cells Tok MsgT →
      Wit Cells Tok MsgT)
    (er4 : Err (uLT (ckP .two) [d4])) (base5 : ℕ) (d51 d52 : RDT)
    (ex5 : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d51, d52]) → Wit Cells Tok MsgT →
      Wit Cells Tok MsgT)
    (er5 : Err (uLT (ckP .two) [d51, d52])) (base7 : ℕ) (d7 : RDT)
    (ex7 : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d7]) → Wit Cells Tok MsgT →
      Wit Cells Tok MsgT)
    (er7 : Err (uLT (ckP .two) [d7]))
    (eN : N = tiedNumbers N₁ Ns)
    (eO : Oc = ocWith (ocEnd get N₁
      Mg₁ links ps) R)
    (eM₀ : Mg₀ = tiedMeaning get
      Mg₁
      (mgJoint Q.codes G arr get smp₁ ms₁ xW (smpSt Q.codes oNo stSh) ms (linLayW Q.codes Pw.lin)
        (fun q => stOf₁ (get q)) (fun q => tabP₁ (get q)) (rgOf Q.codes arr mem rd)
        (omWK Q.codes arr mem rd nO Q) Q.par 2852142980 gOf err₂ eM rank held Pw matC MgZ))
    (hf1 : ∀ a τ b, f.ior.red.out a τ = some b → b.1 = a.1)
    (hfb : (seatedPiece (W := Wit Cells Tok MsgT) (Cl' := Cl) (F := Fr) (P₁ := P₁) b1 base d ext
      err).base = f.base) :
    FrontRides N
      (mgK Q.codes G arr (smpSt Q.codes oNo stSh) ms decT₂ Mg₀ mem rd 2852142980
        Q.S.fold.columns nO Q)
      (pmK Q.codes G (smpSt Q.codes oNo stSh) ms decT₂ (shiftBook N.lo) Pm₀ Q.S.fold.columns nU
        nO Q X) Oc true f
      ((seatedPiece (W := Wit Cells Tok MsgT) (Cl' := Cl) (F := Fr) (P₁ := P₁) b1 base d ext
        err) :: [pc2 c2 base2 d21 d22 ex2 er2, x3, pc1 c4 base4 d4 ex4 er4,
        pc2 c5 base5 d51 d52 ex5 er5, x6, pc1 c7 base7 d7 ex7 er7, x8, x9, x10, x11]) := by
  subst eN eO eM₀
  exact front_rides_tied Q.codes G arr _ ms decT₂ mem rd _ _ nO Q get smp₁ ms₁ stOf₁ tabP₁
    Pw N₁.w matC Mg₁ _ N₁ Ns links ps lo R _ true f _ hpin hpo hread (hloB.trans_eq hfb)
      (hw.trans_eq hfb)
    (hi.trans_eq hfb) hf1

end Desc.K14.Law

#print axioms Desc.K14.Law.front_rides_tied
#print axioms Desc.K14.Law.front_rides_at_K
