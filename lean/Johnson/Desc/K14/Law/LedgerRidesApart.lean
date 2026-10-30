-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerRidesApart.lean: FOUR OF THE FIVE DEBTS OF each_rides_at_K
(Johnson/Desc/K14/Law/LedgerRidesOwn.lean), CUT DOWN: p9, p10 are paid at the forms that nine_at_K
and ten_at_K (Johnson/Desc/K14/Law/LedgerNineTen.lean) ask of the two pieces; k9, k10 fall to three
tests on the plan's numbers each and ONE SENTENCE ON (Eval), named.

  psi_nine, psi_ten   PsiStays at a piece that holds the test on G_u | G_omega (onGu_leaves |
                      onGomega_leaves, Johnson/Desc/K12/Coin/SamplesThrough.lean).
  EvKept … k          INSIDE THE PROMISE at border k, at a witness at which the five own items hold:
                      (Eval) holds at what block k's extractor makes of the witness.
  ownKept_apart       OwnKept … k at the tied letters, from: the block lays none of W's, the index
                      masks' and o_omega's components · apartAt (the shared table's test,
                      Johnson/Desc/Sound/BordersSharedFill.lean) at these three · W's member sits at
                      W's seat, o_omega's at o_omega's tenant · EvKept … k.
  each_rides_at_K_apart   hRd at the user's own letters, from all this.
HOW. The old part is kept (extSSame, Johnson/Desc/Sound/BordersSharedFillProofs.lean). The two pins
by pin_congr. (Dot) reads of the witness Omega (omWK: o_omega's member's messages) and W's member's
table: both by msgs_same (Johnson/Desc/Sound/HrowsNine.lean). "No mark" reads no witness.
WHAT IS LEFT OF hRd's DEBTS: hb2 : base ≤ base2 · six tests apartAt (two of them, at o_omega's
component, are binders of nine_at_K | ten_at_K) · EvKept … 9 | 10. EvKept IS NOT HAD FROM THE
USER's BINDERS: (Eval)'s row reads W's words AND entries of the masks' message; the witness's words
come through the letter tabP₁, known only at a number that the handed state's book places (hbook);
that the masks' message's number is placed at a seat apart from o_u's and o_sp's no binder says.
What is not claimed. What is left. No instance. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.LedgerRidesOwn
import Johnson.Desc.Sound.HrowsNine
import Johnson.Desc.Sound.BordersSharedFillProofs
import Johnson.Desc.K12.Coin.SamplesThrough

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open VerifiableInference.Desc.Sound (LettersReadBelow ocEndReadsBelow pinJT)
open VerifiableInference.Desc.K13.Law (WRow evalLaidB wSitsB wSeatB wSitsItem)
open OnBytes.Means (wordsOn)
open VerifiableInference.Desc (Strs)
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words wordsOn)
open Johnson.Pack
open _root_.Run.PQ (CK)
open Cb Cb.Ood Blocks Cb.Pv Cb.Pv.Lin Cb.Bridge
open VerifiableInference.Desc (Block Strs Wit FileDescription First.S Grows)
open VerifiableInference.Desc.ChainEnd (untestedL Exact)
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Pub pubSets openSets start)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts Seat.onGu Seat.onGomega)
open VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Law (vecAt)
open Desc.K14.Law.Fence (msgs_same held_decides)

/-- **p9**, at the form that nine_at_K asks of the piece. -/
theorem psi_nine {P₁ Cl W : Type} {Fr : Frame} (π : P12)
    (x : Piece (ckP .two) Fr (P₁ × St) Cl W)
    (hb : Alike (held (P := P₁) (Seat.onGu (proximityTestKind guardedProximityTestParts π : Block T12 Unit))) x.b)
    (he : π.early = true) (ha1 : π.answers = 1) : PsiStays x := fun a τ b h => by
  obtain ⟨rs, gs, hd, _⟩ := held_decides _ x hb a b τ h
  rw [(onGu_leaves π he ha1 _ _ rs gs hd).2.2.2.1]

/-- **p10**, at the form that ten_at_K asks of the piece. -/
theorem psi_ten {P₁ Cl W : Type} {Fr : Frame} (π : P12)
    (x : Piece (ckP .two) Fr (P₁ × St) Cl W)
    (hb : Alike (held (P := P₁) (Seat.onGomega (proximityTestKind guardedProximityTestParts π : Block T12 Unit))) x.b)
    (he : π.early = true) (ha1 : π.answers = 1) : PsiStays x := fun a τ b h => by
  obtain ⟨rs, gs, hd, _⟩ := held_decides _ x hb a b τ h
  rw [(onGomega_leaves π he ha1 _ _ rs gs hd).2.2.2.1]

/-- **Inside the promise at border k, (Eval) is kept by block k's extractor.** -/
def EvKept {P₁ S₂ Cl Wt : Type} {C : CK} {Fr : Frame} (N : NumbersS) (Mg : MeaningS S₂ P₁ Wt)
    (Pm : PromMeaning S₂) (Oc : P₁ → Strs → Prop) (split : Bool)
    (p : Piece C Fr (P₁ × S₂) Cl Wt) (l : List (Piece C Fr (P₁ × S₂) Cl Wt))
    (e₀ : ℕ → ActV S₂ Fr → Wt → Wt) (k : ℕ) : Prop :=
  ∀ a w, onQ₂ N Pm Oc split p l k a → relOwn N Mg 2 a w →
    Mg.ev a.1.1 (strsOf Fr a.2) (e₀ k ((actQ N p l k).2 a) w)

/-- **k9 | k10, cut down.** -/
theorem ownKept_apart {P₀ P₁ Cl Xi Cells Tok : Type} {Fr : Frame} (cs : OnBytes.Codes)
    (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
    (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells) (c₀ : Cells)
    (mem : ℕ → Option Mem) (rd : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg → Part → ℕ → GE)
    (e' n nO : ℕ) (Q : P14) (get : P₁ → P₀ × First.S)
    (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) →
      Option ((sigOf cs s.l).om i).Smp)
    (ms₁ : List Mem) (xW : Mem)
    (stOf₁ : P₀ × First.S → Statement) (tabP₁ : P₀ × First.S → Wit Cells Tok MsgT → Nat → MsgT)
    (Pw : Where) (wSeat : ℕ × ℕ) (matC : Cells → Nat → Nat → GE)
    (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT))
    (hpin : Mg₁.pin = fun j t a y w => pinJT cs G arr smp₁ ms₁ j t a y w)
    (smp₃ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₃ : List Mem) (lay₀ : VectorLay) (stOf : P₁ → Statement)
    (tabP : P₁ → Wit Cells Tok MsgT → Nat → MsgT) (rg : Wit Cells Tok MsgT → Words GE)
    (pr : Par) (e'' : ℕ) (gOf : P₁ → Nat → GE) (err₂ eM : Nat)
    (rank : ((Fin pr.S.fold.index.v → Bool) →
      Fin (pr.S.fold.index.code.r + pr.S.fold.index.code.ell) → GE) → Nat)
    (held : ((ixOf2 pr.S.fold err₂ eM rank).Row × Fin pr.S.fold.index.code.ell → GE) →
      Option Cells)
    (MgZ : MeaningS St P₁ (Wit Cells Tok MsgT))
    (N₁ : Numbers) (Ns : NumbersS) (Pm : PromMeaning St) (Oc : P₁ → Strs → Prop)
    (f : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
    (l : List (Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))) (k : ℕ)
    (nW : Comp.w ∉ laysAtS true k) (nI : Comp.index ∉ laysAtS true k)
    (nOm : Comp.msg .oOmega ∉ laysAtS true k)
    (aW : apartAt (tiedNumbers N₁ Ns) arr true k .w = true)
    (aI : apartAt (tiedNumbers N₁ Ns) arr true k .index = true)
    (aO : apartAt (tiedNumbers N₁ Ns) arr true k (.msg .oOmega) = true)
    (hsW : SitsAt xW N₁.w.1 N₁.w.2) (xO : Mem) (hO : mem nO = some xO)
    (sO : SitsAt xO ((tiedNumbers N₁ Ns).tenant .oOmega).1 ((tiedNumbers N₁ Ns).tenant .oOmega).2)
    (hev : EvKept (tiedNumbers N₁ Ns)
      (mgK cs G arr smp₂ ms decT₂
        (tiedMeaning get Mg₁
          (mgJoint cs G arr get smp₁ ms₁ xW smp₃ ms₃ lay₀ stOf tabP rg
            (omWK cs arr mem rd nO Q) pr e'' gOf err₂ eM rank held Pw matC MgZ))
        mem rd e' n nO Q) Pm Oc true f l
      (exK cs G arr smp₂ ms decT₂ c₀ (tiedNumbers N₁ Ns) Fr) k) :
    OwnKept (tiedNumbers N₁ Ns)
      (mgK cs G arr smp₂ ms decT₂
        (tiedMeaning get Mg₁
          (mgJoint cs G arr get smp₁ ms₁ xW smp₃ ms₃ lay₀ stOf tabP rg
            (omWK cs arr mem rd nO Q) pr e'' gOf err₂ eM rank held Pw matC MgZ))
        mem rd e' n nO Q) Pm Oc true f l
      (exK cs G arr smp₂ ms decT₂ c₀ (tiedNumbers N₁ Ns) Fr) k := by
  intro a w ha hw i hi
  have same := fun c hc hap => extSSame cs Xi St Cells Tok G arr smp₂ ms decT₂ c₀
    (tiedNumbers N₁ Ns) true k c hc hap ((actQ (tiedNumbers N₁ Ns) f l k).2 a).1
    (strsOfAct Fr ((actQ (tiedNumbers N₁ Ns) f l k).2 a)) w
  have sW := same .w nW aW
  have sI := same .index nI aI
  have sOm := same (.msg .oOmega) nOm aO
  have hi' : i ∈ [ItemS.unmarked1, .pinI, .pinV, .ev, .dot] := hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
  rcases hi' with rfl | rfl | rfl | rfl | rfl
  · exact hw .unmarked1 hi
  · have h : pinJT cs G arr smp₁ ms₁ N₁.index.1 N₁.index.2 (get a.1.1) (strsOf Fr a.2) w := by
      have h0 : Mg₁.pin N₁.index.1 N₁.index.2 (get a.1.1) (strsOf Fr a.2) w := hw .pinI hi
      rwa [hpin] at h0
    show Mg₁.pin N₁.index.1 N₁.index.2 (get a.1.1) (strsOf Fr a.2) _
    rw [hpin]
    refine (⟨h.1, fun x hx hs => ?_⟩ : pinJT cs G arr smp₁ ms₁ N₁.index.1 N₁.index.2 (get a.1.1)
      (strsOf Fr a.2) _)
    have e : x.1.seat x.2 = (N₁.index.1, N₁.index.2) := hs
    refine pin_congr cs G arr smp₁ x.1 x.2 _ _ w _ ?_ ?_ (h.2 x hx hs)
    · rw [e]
      exact sI.1
    · rw [e]
      exact sI.2
  · have h : pinJT cs G arr smp₁ ms₁ N₁.w.1 N₁.w.2 (get a.1.1) (strsOf Fr a.2) w := by
      have h0 : Mg₁.pin N₁.w.1 N₁.w.2 (get a.1.1) (strsOf Fr a.2) w := hw .pinV hi
      rwa [hpin] at h0
    show Mg₁.pin N₁.w.1 N₁.w.2 (get a.1.1) (strsOf Fr a.2) _
    rw [hpin]
    refine (⟨h.1, fun x hx hs => ?_⟩ : pinJT cs G arr smp₁ ms₁ N₁.w.1 N₁.w.2 (get a.1.1)
      (strsOf Fr a.2) _)
    have e : x.1.seat x.2 = (N₁.w.1, N₁.w.2) := hs
    refine pin_congr cs G arr smp₁ x.1 x.2 _ _ w _ ?_ ?_ (h.2 x hx hs)
    · rw [e]
      exact sW.1
    · rw [e]
      exact sW.2
  · exact hev a w ha hw
  · have h : DotEq pr.S.matrixRows pr.S.kCol (gOf a.1.1) (omWK cs arr mem rd nO Q w)
        (a.1.2.loc.psiSh.map OnBytes.Model.Reading.gl.val)
        (vecAt lay₀ (xW.1.l.get xW.2).1 (wTab cs arr xW w)) := hw .dot hi
    have eW : xW.1.seat xW.2 = (N₁.w.1, N₁.w.2) := hsW
    have eO : xO.1.seat xO.2 = (((tiedNumbers N₁ Ns).tenant .oOmega).1,
      ((tiedNumbers N₁ Ns).tenant .oOmega).2) := sO
    have m1 := msgs_same cs arr xW w (exK cs G arr smp₂ ms decT₂ c₀ (tiedNumbers N₁ Ns) Fr k
      ((actQ (tiedNumbers N₁ Ns) f l k).2 a) w) (by rw [eW]; exact sW.1) (by rw [eW]; exact sW.2)
    have m2 := msgs_same cs arr xO w (exK cs G arr smp₂ ms decT₂ c₀ (tiedNumbers N₁ Ns) Fr k
      ((actQ (tiedNumbers N₁ Ns) f l k).2 a) w) (by rw [eO]; exact sOm.1)
      (by rw [eO]; exact sOm.2)
    show DotEq pr.S.matrixRows pr.S.kCol (gOf a.1.1) (omWK cs arr mem rd nO Q _)
        (a.1.2.loc.psiSh.map OnBytes.Model.Reading.gl.val)
        (vecAt lay₀ (xW.1.l.get xW.2).1 (wTab cs arr xW _))
    have t1 : wTab cs arr xW (exK cs G arr smp₂ ms decT₂ c₀ (tiedNumbers N₁ Ns) Fr k
        ((actQ (tiedNumbers N₁ Ns) f l k).2 a) w) = wTab cs arr xW w := by
      unfold wTab
      exact congrArg _ m1
    have t2 : omWK cs arr mem rd nO Q (exK cs G arr smp₂ ms decT₂ c₀ (tiedNumbers N₁ Ns) Fr k
        ((actQ (tiedNumbers N₁ Ns) f l k).2 a) w) = omWK cs arr mem rd nO Q w := by
      funext y
      unfold omWK rgOf
      simp only [hO]
      exact congrArg (fun z => rd xO z .main _) m2
    rw [t1, t2]
    exact h

/-- **hRd**, at the user's own letters, with four of the five debts cut down: what is left is hb2,
six tests on the plan's numbers, and (Eval) past the two extractors (ev9, ev10). hsW, hO, sO are the
user's binders; hb9 … ha10 are nine_at_K's and ten_at_K's. -/
theorem each_rides_at_K_apart {P₀ P₁ Cl Xi Cells Tok : Type} {Fr : Frame} (G : FileDescription Xi)
    (oNo : Mem → ℕ) (ms : List Mem)
    (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells) (N : NumbersS) (Q : P14)
    (Pm₀ : PromMeaning St) (Oc : P₁ → Strs → Prop) (nU nO : ℕ)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (arr : ℕ → ℕ → ℕ) (c₀ : Cells) (Mg₀ : MeaningS St P₁ (Wit Cells Tok MsgT))
    (mem : ℕ → Option Mem)
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
    (hwrow : Mg₁.wrow = fun a _ w => WRow Pw a.2 (wordsOn (stOf₁ a) (tabP₁ a w)))
    (hread : LettersReadBelow lo N₁ Mg₁ ((openSets links ps (start links))[ps.length]?.getD []))
    (hloB : lo ≤ base) (hw : N₁.w.1 < base) (hi : N₁.index.1 < base)
    (c2 c3 c4 c5 c6 c7 c8 c11 : Block St Cl)
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
    (ht : Tiled (pc2 c2 base2 d21 d22 ex2 er2) [x3, (pc1 c4 base4 d4 ex4 er4), (pc2 c5 base5 d51
      d52 ex5 er5), x6, (pc1 c7 base7 d7 ex7 er7), x8, x9, x10, x11])
    (hS : Q.S.sharedSplitNeeded = true)
    (h2c : DecidesAs c2 b2) (h3c : DecidesAs c3 b3) (h4c : DecidesAs c4 b4)
    (h5c : DecidesAs c5 b5) (h6c : DecidesAs c6 b6) (h7c : DecidesAs c7 b7)
    (h8c : DecidesAs c8 b8)
    (hx3 : x3.b = heldW c3) (hx6 : x6.b = heldW c6) (hx8 : x8.b = heldW c8)
    (hx11 : x11.b = heldW c11) (he11 : Exact (fun d : St => untestedL d.st) c11)
    (eN : N = tiedNumbers N₁ Ns)
    (eO : Oc = ocWith (ocEnd get N₁
      Mg₁ links ps) R)
    (eM₀ : Mg₀ = tiedMeaning get
      Mg₁
      (mgJoint Q.codes G arr get smp₁ ms₁ xW (smpSt Q.codes oNo stSh) ms (linLayW Q.codes Pw.lin)
        (fun q => stOf₁ (get q)) (fun q => tabP₁ (get q)) (rgOf Q.codes arr mem rd)
        (omWK Q.codes arr mem rd nO Q) Q.par 2852142980 gOf err₂ eM rank held Pw matC MgZ))
    (hx9 : ∃ b₀ : Block St Cl, x9.b = b₀.lift Prod.snd fun t s => (t.1, s))
    (hx10 : ∃ b₀ : Block St Cl, x10.b = b₀.lift Prod.snd fun t s => (t.1, s))
    (hb2 : base ≤ base2)
    (hsW : SitsAt xW N₁.w.1 N₁.w.2) (xO : Mem) (hO : mem nO = some xO)
    (sO : SitsAt xO (N.tenant .oOmega).1 (N.tenant .oOmega).2)
    (π9 π10 : P12)
    (hb9 : Alike (VerifiableInference.Desc.Sound.held (P := P₁)
      (Seat.onGu (proximityTestKind guardedProximityTestParts π9 : Block T12 Unit))) x9.b)
    (he9 : π9.early = true) (ha9 : π9.answers = 1)
    (hb10 : Alike (VerifiableInference.Desc.Sound.held (P := P₁)
      (Seat.onGomega (proximityTestKind guardedProximityTestParts π10 : Block T12 Unit))) x10.b)
    (he10 : π10.early = true) (ha10 : π10.answers = 1)
    (aW9 : apartAt N arr true 9 .w = true) (aI9 : apartAt N arr true 9 .index = true)
    (aO9 : apartAt N arr true 9 (.msg .oOmega) = true)
    (aW10 : apartAt N arr true 10 .w = true) (aI10 : apartAt N arr true 10 .index = true)
    (aO10 : apartAt N arr true 10 (.msg .oOmega) = true)
    (ev9 : EvKept N
      (mgK Q.codes G arr (smpSt Q.codes oNo stSh) ms decT₂ Mg₀ mem rd 2852142980
        Q.S.fold.columns nO Q)
      (pmK Q.codes G (smpSt Q.codes oNo stSh) ms decT₂ (shiftBook N.lo) Pm₀ Q.S.fold.columns nU
        nO Q X) Oc true f
      ((seatedPiece (W := Wit Cells Tok MsgT) (Cl' := Cl) (F := Fr) (P₁ := P₁) b1 base d ext
        err) :: [pc2 c2 base2 d21 d22 ex2 er2, x3, pc1 c4 base4 d4 ex4 er4,
        pc2 c5 base5 d51 d52 ex5 er5, x6, pc1 c7 base7 d7 ex7 er7, x8, x9, x10, x11])
      (exK Q.codes G arr (smpSt Q.codes oNo stSh) ms decT₂ c₀ N Fr) 9)
    (ev10 : EvKept N
      (mgK Q.codes G arr (smpSt Q.codes oNo stSh) ms decT₂ Mg₀ mem rd 2852142980
        Q.S.fold.columns nO Q)
      (pmK Q.codes G (smpSt Q.codes oNo stSh) ms decT₂ (shiftBook N.lo) Pm₀ Q.S.fold.columns nU
        nO Q X) Oc true f
      ((seatedPiece (W := Wit Cells Tok MsgT) (Cl' := Cl) (F := Fr) (P₁ := P₁) b1 base d ext
        err) :: [pc2 c2 base2 d21 d22 ex2 er2, x3, pc1 c4 base4 d4 ex4 er4,
        pc2 c5 base5 d51 d52 ex5 er5, x6, pc1 c7 base7 d7 ex7 er7, x8, x9, x10, x11])
      (exK Q.codes G arr (smpSt Q.codes oNo stSh) ms decT₂ c₀ N Fr) 10) :
    EachRides N
      (mgK Q.codes G arr (smpSt Q.codes oNo stSh) ms decT₂ Mg₀ mem rd 2852142980
        Q.S.fold.columns nO Q)
      (pmK Q.codes G (smpSt Q.codes oNo stSh) ms decT₂ (shiftBook N.lo) Pm₀ Q.S.fold.columns nU
        nO Q X) Oc true f
      ((seatedPiece (W := Wit Cells Tok MsgT) (Cl' := Cl) (F := Fr) (P₁ := P₁) b1 base d ext
        err) :: [pc2 c2 base2 d21 d22 ex2 er2, x3, pc1 c4 base4 d4 ex4 er4,
        pc2 c5 base5 d51 d52 ex5 er5, x6, pc1 c7 base7 d7 ex7 er7, x8, x9, x10, x11])
      (exK Q.codes G arr (smpSt Q.codes oNo stSh) ms decT₂ c₀ N Fr) 2
      [pc2 c2 base2 d21 d22 ex2 er2, x3, pc1 c4 base4 d4 ex4 er4,
        pc2 c5 base5 d51 d52 ex5 er5, x6, pc1 c7 base7 d7 ex7 er7, x8, x9, x10, x11] := by
  subst eN eO eM₀
  exact each_rides_at_K G oNo ms decT₂ _ Q Pm₀ _ nU nO b1 b2 b3 b4 b5 b6 b7 b8 hbl arr c₀ _ mem rd
    X get smp₁ ms₁ xW stOf₁ tabP₁ base d ext err N₁ Ns links ps gOf lo R err₂ eM rank held Pw
    matC Mg₁ MgZ hpin hwrow hread hloB hw hi c2 c3 c4 c5 c6 c7 c8 c11 f x3 x6 x8 x9 x10 x11 base2
      d21 d22
    ex2 er2 base4 d4 ex4 er4 base5 d51 d52 ex5 er5 base7 d7 ex7 er7 ht hS h2c h3c h4c h5c h6c h7c
    h8c hx3 hx6 hx8 hx11 he11 rfl rfl rfl hx9 hx10 hb2 (psi_nine π9 x9 hb9 he9 ha9)
    (psi_ten π10 x10 hb10 he10 ha10)
    (ownKept_apart Q.codes G arr _ ms decT₂ c₀ mem rd _ _ nO Q get smp₁ ms₁ xW stOf₁ tabP₁
      Pw N₁.w matC Mg₁ hpin _ _ _ _ _ _ _ _ gOf err₂ eM rank held MgZ N₁ Ns _ _ f _ 9 (by decide)
      (by decide) (by decide) aW9 aI9 aO9 hsW xO hO sO ev9)
    (ownKept_apart Q.codes G arr _ ms decT₂ c₀ mem rd _ _ nO Q get smp₁ ms₁ xW stOf₁ tabP₁
      Pw N₁.w matC Mg₁ hpin _ _ _ _ _ _ _ _ gOf err₂ eM rank held MgZ N₁ Ns _ _ f _ 10 (by decide)
      (by decide) (by decide) aW10 aI10 aO10 hsW xO hO sO ev10)

end Desc.K14.Law

#print axioms Desc.K14.Law.psi_nine
#print axioms Desc.K14.Law.psi_ten
#print axioms Desc.K14.Law.ownKept_apart
#print axioms Desc.K14.Law.each_rides_at_K_apart
