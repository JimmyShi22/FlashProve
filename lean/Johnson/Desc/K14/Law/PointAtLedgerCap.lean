-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/PointAtLedgerCap.lean: BLOCK 1's CLAUSE OF THE SHARED CHAIN's ROW, AT THE
LEDGER's OWN FILLING, AT THE CAP 128, FOR UP TO 64 SLOTS, WITH THE RADIUS WRITTEN: NO FREE e'. One
theorem: ONE TERM that applies point_at_ledgerN (Johnson/Desc/K14/Law/PointAtLedger.lean) to
point_leadsBN_cap_reader (Johnson/Desc/Sound/PointReader.lean). A JOINING OF FILES:
no chance is counted here.

  point_ledger_at_cap   at any row f :: l of pieces that holds the shared chain's own blocks as a
                        description lays them (hps): l is seatedPiece b1 … :: r, and that piece has
                        LeadsBN at: key := keyAt Prod.snd N.lo f l 1 · the condition onQ₂ at pmK ·
                        the step stepAt at mgK, pmK and extOf … exK · n slots, n ≤ 64 · the one
                        list Err.cap 128 of its one written round.
THE RADIUS. 2852142980 STANDS, AS A WRITTEN NUMBER, IN THE LAW's KEY's COUNT AND IN mgK: so "near"
at the ledger's borders 2 to 4, and with it the ledger's count at "LOC", speak of that radius. It is
OnBytes.Params.recordRadius (by rfl: radius_is).
Limits. ALL OF THAT LAW's PREMISES STAND HERE, to the letter (cut by program), the letter R beside
the first chain's last promise among them (see Johnson/Desc/K14/Law/PointAtLedgerS5.lean's head),
and PointCap P.par.S Wr: THAT P.par.S IS THE RELEASE's SHAPE AT THE SEATED DESCRIPTION is another
file's (k14_at_seat, WrittenAtZ.lean, under Written Z x): not joined here. THAT THE PLANNER PRICES
"LIN point" AND "LOC" AT THAT RADIUS is a closed statement at the written plans in other files: not
joined here. eM, err₂, rank stay letters (2852142980 ≤ eM is asked). And hS, hsz, hX, as in
Johnson/Desc/K14/Law/PointAtLedgerS5.lean. The full size alone. NO MEMBER. No soundness of a
verifier.

-/
import Johnson.Desc.K14.Law.PointAtLedgerS5
import Johnson.Desc.Sound.PointAtCap

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open VerifiableInference.Desc.Sound (LettersReadBelow ocEndReadsBelow pinJT)
open VerifiableInference.Desc.K13.Law (WRow evalLaidB wSitsB wSeatB wSitsItem)
open OnBytes.Means (wordsOn)
open VerifiableInference.Desc (Strs)
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words wordsOn)
open Johnson.Pack (sigOf)
open _root_.Run.PQ (CK)
open Cb Cb.Ood Blocks Cb.Pv Cb.Pv.Lin Cb.Bridge
open VerifiableInference.Desc (Block Chain Strs Wit FileDescription First.S)
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Pub pubSets openSets start)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared (NumbersS MeaningS PromMeaning)
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Law (EvalAt laidOf wSitsItem wSitsMore)

/-- The written radius is the constant recordRadius (the OOD sample's radius). -/
theorem radius_is : OnBytes.Params.recordRadius = 2852142980 := rfl

variable {P₁ P₀ Xi Cells Tok Cl' : Type} {F : Frame}

/-- **Block 1's clause at the ledger's filling, at the cap, with the radius written.** -/
theorem point_ledger_at_cap
    (cs : OnBytes.Codes)
    (G : FileDescription Xi)
    (arr : Nat → Nat → Nat)
    (get : P₁ → P₀ × First.S)
    (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om
      i).Smp)
    (ms₁ : List Mem)
    (xW : Mem)
    (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₂ : List Mem)
    (c₀ : Cells)
    (stOf₁ : P₀ × First.S → Statement)
    (tabP₁ : P₀ × First.S → Wit Cells Tok MsgT → Nat → MsgT)
    (P : P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (d : RDT)
    {ns a0 : Nat}
    (hd : SendsDraws (toRD d) ns P.par.S.kCol 0 a0)
    (N₁ : Numbers)
    (Ns : NumbersS)
    (links : List ModelPart)
    (ps : List VerifiableInference.Desc.Place)
    (lo : Nat)
    (f : Piece (ckP .two) F (P₁ × St) Cl' (Wit Cells Tok MsgT))
    (l : List (Piece (ckP .two) F (P₁ × St) Cl' (Wit Cells Tok MsgT)))
    (c : Model.Verify.Chains)
    (tests : List (Block St Unit))
    (last : List (Block St Unit) → Block St Unit)
    (hps : (f :: l).map (·.b) = (((chainOf c P tests last).retype (Cl' := Cl')).blocksInOrder.map
      below).map (Block.lift Prod.snd fun t s => (t.1, s)))
    (hdat : ∀ q, (f :: l)[1]? = some q → q.ds = [d] ∧ q.back = [] ∧ lo ≤ q.base ∧ N₁.w.1 < q.base
      ∧ N₁.index.1 < q.base)
    (gOf : P₁ → Nat → GE)
    (err₂ eM : Nat)
    (rank : ((Fin P.par.S.fold.index.v → Bool) → Fin (P.par.S.fold.index.code.r +
      P.par.S.fold.index.code.ell) → GE) → Nat)
    (held : ((ixOf2 P.par.S.fold err₂ eM rank).Row × Fin P.par.S.fold.index.code.ell → GE) →
      Option Cells)
    (Pw : Where)
    (hlin : Pw.lin = P.par.S)
    (matC : Cells → Nat → Nat → GE)
    (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT))
    (Mg₀ : MeaningS St P₁ (Wit Cells Tok MsgT))
    (Pm₀ : PromMeaning St)
    (ha : P.par.S.fold.index.code.logN ≤ 32)
    (hix : P.par.S.fold.index.ok = true)
    (hroom : P.par.S.matrixRows * 2 ^ P.par.S.kLo ≤ P.par.S.fold.index.plain)
    (hk : 0 < (codeOf P.par.S.fold.index.code).r + (codeOf P.par.S.fold.index.code).l - 1)
    (hr : (codeOf P.par.S.fold.index.code).r + (codeOf P.par.S.fold.index.code).l ≤ 2 ^ (codeOf
      P.par.S.fold.index.code).a)
    (hle : 2852142980 ≤ eM)
    (hM : eM < 2 ^ (codeOf P.par.S.fold.index.code).a - ((codeOf P.par.S.fold.index.code).r +
      (codeOf P.par.S.fold.index.code).l) + 1)
    (hJ : InJohnson (2 ^ (codeOf P.par.S.fold.index.code).a) (2 ^ (codeOf
      P.par.S.fold.index.code).a - ((codeOf P.par.S.fold.index.code).r + (codeOf
      P.par.S.fold.index.code).l) + 1) 2852142980)
    (hpin : Mg₁.pin = fun j t a y w => pinJT cs G arr smp₁ ms₁ j t a y w)
    (hwrow : Mg₁.wrow = fun a _ w => WRow Pw a.2 (wordsOn (stOf₁ a) (tabP₁ a w)))
    (hevalLaid : ∀ a, Mg₁.pub .evalLaid a = evalLaidB Pw a.2)
    (hwSits : ∀ a, Mg₁.pub wSitsItem a = (wSitsB cs Pw a.2 && wSeatB N₁.w a.2))
    (h2 : Pub.evalLaid ∈ (pubSets Mg₁.more links ps)[ps.length]?.getD [])
    (h3 : wSitsItem ∈ (pubSets Mg₁.more links ps)[ps.length]?.getD [])
    (hread : LettersReadBelow lo N₁ Mg₁ ((openSets links ps (start links))[ps.length]?.getD []))
    (hxW : xW ∈ ms₁)
    (hsW : SitsAt xW N₁.w.1 N₁.w.2)
    (hst : ∀ a, stOf₁ a = a.2.st)
    (R : P₁ → Prop)
    (hbook : ∀ p y, ocEnd get N₁ Mg₁
      links ps p y → R p → (get p).2.failed = none → (get p).2.st.codes = cs → ∀ (w : Wit Cells Tok
      MsgT) n j t sh, (get p).2.book.place[n]? = some (j, t) → ((get p).2.st.oracles[n]?).map
      (·.shape) = some sh → tabP₁ (get p) w n = w.tab cs sh (arr j t) j t)
    (htab : ∀ a (w w' : Wit Cells Tok MsgT), (∀ n, w'.msg n = w.msg n) → (∀ j t, w'.pad j t =
      w.pad j t) → tabP₁ a w' = tabP₁ a w)
    (hsh : Pw.lin.w = (xW.1.l.get xW.2).1)
    (hg : ∀ p y' D, ocEnd get N₁ Mg₁
      links ps p y' → (get p).2.failed = none → laidOf Pw (get p).2 = some D → ∀ y <
      P.par.S.matrixRows, gOf p y = (D.row.g.map fun t => OnBytes.Model.Reading.gl.val (t.entry
      y)).sum)
    (hH : HeldTie P.par err₂ eM rank held matC)
    (hpile : ∀ p y (w : Wit Cells Tok MsgT), ocEnd get N₁ Mg₁ links ps p y → R p → (get
      p).2.failed = none → pileStep stOf₁ tabP₁ Pw matC (get p) w → Mg₁.pileOne (get p) y w)
    (Wr : Rounds)
    (hPC : PointCap P.par.S Wr)
    (hdW : atW Wr 0 = some (d.entry, d.kind))
    (n : ℕ)
    (hn : n ≤ 64)
    (mem : ℕ → Option Mem) (rd : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg → Part → ℕ → GE)
    (nL nO : ℕ) (bkR : TreeBook → TreeBook) (X : ℕ → St → Bool)
    (hS : P.par.S.sharedSplitNeeded = true)
    (hsz : ∀ s, X 1 s = true → s.st.oracles.size = 0)
    (hX : ∀ (x : Piece (ckP .two) F (P₁ × St) Cl' (Wit Cells Tok MsgT)), x.b = heldW b1.retype →
      ∀ a τ y, x.ior.red.out a τ = some y → X 1 a.1.2 = true → X 2 y.1.2 = true) :
    ∃ (base : Nat)
      (ext : (P₁ × St) × F.E.Str → Tr (uLT (ckP .two) [d]) → Wit Cells Tok MsgT →
        Wit Cells Tok MsgT)
      (err : Err (uLT (ckP .two) [d]))
      (r : List (Piece (ckP .two) F (P₁ × St) Cl' (Wit Cells Tok MsgT))),
      l = seatedPiece b1 base d ext err :: r ∧
      (seatedPiece (Cl' := Cl') (F := F) (P₁ := P₁) b1 base d ext err).ior.red.LeadsBN
        (keyAt Prod.snd (tiedNumbers N₁ Ns).lo f l 1)
        (onQ₂ (tiedNumbers N₁ Ns)
          (pmK cs G smp₂ ms₂ (decK P.par err₂ eM rank held) bkR
            (pmPoint cs G smp₂ ms₂ P.par err₂ eM rank held (fun s : St => s.st)
              (fun s : St => bkR s.book) Pm₀) nL 0 nO P X)
          (ocWith (ocEnd get N₁ Mg₁
            links ps) R)
          true f l 1)
        (stepAt (tiedNumbers N₁ Ns)
          (mgK cs G arr smp₂ ms₂ (decK P.par err₂ eM rank held)
            (tiedMeaning get Mg₁
              (mgJoint cs G arr get smp₁ ms₁ xW smp₂ ms₂ (linLayW cs Pw.lin)
                (fun q => stOf₁ (get q)) (fun q => tabP₁ (get q)) (rgOf cs arr mem rd)
                (omWK cs arr mem rd nO P) P.par 2852142980 gOf err₂ eM rank held Pw matC Mg₀))
            mem rd 2852142980 nL nO P)
          (pmK cs G smp₂ ms₂ (decK P.par err₂ eM rank held) bkR
            (pmPoint cs G smp₂ ms₂ P.par err₂ eM rank held (fun s : St => s.st)
              (fun s : St => bkR s.book) Pm₀) nL 0 nO P X)
          (ocWith (ocEnd get N₁ Mg₁
            links ps) R)
          true f l
          (extOf (tiedNumbers N₁ Ns) f l
            (exK cs G arr smp₂ ms₂ (decK P.par err₂ eM rank held) c₀ (tiedNumbers N₁ Ns) F)) 1)
        n (Err.cap 128 (uLT (ckP .two) [d])) := by
  obtain ⟨base, ext, err, r, hl, h⟩ := point_leadsBN_cap_reader (Cl' := Cl') (F := F)
    cs G arr get smp₁ ms₁ xW smp₂ ms₂ c₀ stOf₁ tabP₁ (rgOf cs arr mem rd) (omWK cs arr mem
    rd nO P) P b1 b2 b3 b4 b5 b6 b7 b8 hbl d hd N₁ Ns links ps true lo f l c tests last hps hdat
    gOf err₂ eM rank held Pw hlin matC
    Mg₁ Mg₀ Pm₀
    (fun s : St => s.st) (fun s : St => bkR s.book) ha hix hroom hk hr hle hM hJ
    hpin hwrow hevalLaid hwSits h2 h3
    hread hxW hsW hst R hbook htab hsh
      hg
    hH hpile Wr hPC hdW n hn
  refine ⟨base, ext, err, r, hl, ?_⟩
  exact point_at_ledgerN cs G arr smp₂ ms₂ (decK P.par err₂ eM rank held) bkR (tiedNumbers N₁ Ns)
    _ _ _ mem rd 2852142980 nL nO P X true (uAt P.par notedU) f l
    ⟨rfl, rfl, rfl, fun _ h => (Bool.and_eq_true_iff.1 h).1⟩
    ⟨rfl, fun _ _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩
    (uAt_next P.par) b1 b2 b3 b4 b5 b6 b7 b8 hbl hS _ rfl hsz (hX _ rfl) _ _ n _ h

end Desc.K14.Law

#print axioms Desc.K14.Law.point_ledger_at_cap
