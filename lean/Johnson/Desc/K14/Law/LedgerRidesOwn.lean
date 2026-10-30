-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerRidesOwn.lean: BEHIND "LIN point", WHAT A SLOT HAS OF ITS OWN RIDES PAST
EACH OF THE SHARED CHAIN's TEN BLOCKS, AT THE LEDGER's ONE FILLING. One binder of ledger_at_cap
(Johnson/Desc/K14/Law/LedgerAtCap.lean: hRd : EachRides …) is had from others of its binders AND
FIVE NAMED DEBTS that none of its binders pays.

  lift_decide       a yes of a lifted block: a yes of the block; what was handed stays.
  tiled_base_le     along a tiling the bases do not fall.
  PsiStays x        the piece x leaves the point psi_sh in the chain's own state.
  psi_blocks        the kind's own blocks 2 to 8 leave it; psi_held, psi_exact: so their pieces do,
                    and the piece of a last block that hands the state on as it is.
  OwnKept … k       INSIDE THE PROMISE at border k, the five own items at a witness hold at what
                    block k's extractor makes of it. ownKept_id: so where the table lays nothing.
  each_rides_tied   EachRides over any list of pieces, at the tied letters.
  each_rides_at_K   hRd, at the user's own letters.
HOW. Back past a block at the SAME witness by ridesAt (Johnson/Desc/Sound/RidesMake.lean) at the
identity: (K) lift_decide · (Oc) ocEndReadsBelow from hread, with ocWith_readsBelow · (P)
pin₁_col_eq from hpin · (V) (Eval) reads no oracle, by hwrow (the first table's meaning Mg₁ is a
letter) · (D1) (Dot) at mgPoint reads no oracle, and the state through psi_sh alone · (D2)
PsiStays. Then along the extractor by OwnKept.
THE FIVE DEBTS of each_rides_at_K: hb2 : base ≤ base2 (nothing among the user's binders ties the
pieces behind the point to the point's base) · p9, p10 : PsiStays x9 | x10 (of these two pieces the
user says only that their blocks are lifted) · k9, k10 : OwnKept … 9 | 10 (the two blocks whose
extractor lays a message: o_u's, o_sp's).
WHY OwnKept IS ASKED INSIDE THE PROMISE, and not as RidesAt's four clauses (E), which speak of every
handed state: (Eval) reads the witness through the letter tabP₁, of which the user says what it
gives at a number that the handed state's book places (hbook); at a handed state whose book
places a number at o_u's seat the bare clause can fail.
What is not claimed. The five debts. No instance. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.LedgerSeamRow
import Johnson.Desc.Sound.PointAtOcEnd
import Johnson.Desc.Sound.PointReached
import Johnson.Desc.Sound.ReadsBelowEq
import Johnson.Desc.Sound.SamplesAtK14
import Johnson.Desc.Sound.SharedJointCountLedger
import Johnson.Desc.Sound.RidesMake

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
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Law (vecAt)

/-- A yes of a lifted block: a yes of the block itself; what was handed stays. -/
theorem lift_decide {U σ Cl : Type} (b₀ : Block σ Cl) (x x' : U × σ) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64)))
    (h : (b₀.lift Prod.snd fun t s => (t.1, s)).decide x rs gs = .ok x') :
    b₀.decide x.2 rs gs = .ok x'.2 ∧ x'.1 = x.1 := by
  have hd : (b₀.decide x.2 rs gs).map (fun s => (x.1, s)) = .ok x' := h
  cases hB : b₀.decide x.2 rs gs with
  | error e => rw [hB] at hd; cases hd
  | ok s => rw [hB] at hd; cases hd; exact ⟨rfl, rfl⟩

/-- So at a piece that holds a lifted block. -/
theorem lift_keeps {U σ Cl W : Type} {C : CK} {Fr : Frame} (x : Piece C Fr (U × σ) Cl W)
    (hb : ∃ b₀ : Block σ Cl, x.b = b₀.lift Prod.snd fun t s => (t.1, s))
    (a : (U × σ) × Fr.E.Str) (τ : Iop.Tr (uLT C x.ds)) (b : (U × σ) × Fr.E.Str)
    (h : x.ior.red.out a τ = some b) : b.1.1 = a.1.1 := by
  obtain ⟨b₀, hb⟩ := hb
  obtain ⟨_, gs, hd⟩ := piece_yes x a τ b h
  rw [hb] at hd
  exact (lift_decide b₀ a.1 b.1 _ gs hd).2

/-- Along a tiling the bases do not fall. -/
theorem tiled_base_le {S Cl W : Type} {C : CK} {Fr : Frame} :
    ∀ (l : List (Piece C Fr S Cl W)) (p : Piece C Fr S Cl W), Tiled p l →
      ∀ x ∈ p :: l, p.base ≤ x.base
  | [], p, _, x, hx => by
    obtain rfl := List.mem_singleton.1 hx
    exact Nat.le_refl _
  | q :: l, p, h, x, hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Nat.le_refl _
    · refine Nat.le_trans ?_ (tiled_base_le l q h.2.2.2.2 x hx)
      rw [h.2.2.2.1]
      exact Nat.le_add_right _ _

/-- The piece leaves the point psi_sh in the chain's own state. -/
def PsiStays {U Cl W : Type} {C : CK} {Fr : Frame} (x : Piece C Fr (U × St) Cl W) : Prop :=
  ∀ a τ b, x.ior.red.out a τ = some b → b.1.2.loc.psiSh = a.1.2.loc.psiSh

/-- **The kind's own blocks 2 to 8 leave psi_sh.** -/
theorem psi_blocks (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hS : Q.S.sharedSplitNeeded = true) :
    ∀ b ∈ [b2, b3, b4, b5, b6, b7, b8], ∀ d rs gs d', b.decide d rs gs = .ok d' →
      d'.loc.psiSh = d.loc.psiSh := by
  have q := quiet_at Q b1 b2 b3 b4 b5 b6 b7 b8 hbl hS
  intro b hb d rs gs d' h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨_, mask, lo⟩ := sendU_step Q b1 _ b3 b4 b5 b6 b7 b8 hbl d d' rs gs h
    rw [lo]
  · rw [(q _ (by simp) d rs gs d' h).loc]
  · rw [(q _ (by simp) d rs gs d' h).loc]
  · obtain ⟨_, o, sp, lo⟩ := sendO_step Q b1 b2 b3 b4 _ b6 b7 b8 hbl d d' rs gs h
    rw [lo]
  · rw [(q _ (by simp) d rs gs d' h).loc]
  · have hz := zeta_of_blocks Q b1 b2 b3 b4 b5 b6 _ b8 hbl d rs gs d' h
    rcases rs with _ | ⟨r, _ | ⟨r', t⟩⟩
    · simp [linZeta] at hz
    · obtain rfl := Option.some.inj hz
      rfl
    · simp [linZeta] at hz
  · rw [(q _ (by simp) d rs gs d' h).loc]

/-- So the piece that holds, in the wrap, a block that decides as one of them. -/
theorem psi_held {U Cl W : Type} {Fr : Frame} (x : Piece (ckP .two) Fr (U × St) Cl W)
    (c : Block St Cl) (hx : x.b = heldW c) (b' : Block St Unit) (hc : DecidesAs c b')
    (hb' : ∀ d rs gs d', b'.decide d rs gs = .ok d' → d'.loc.psiSh = d.loc.psiSh) :
    PsiStays x := fun a τ b h => by
  obtain ⟨rs, gs, hd⟩ := held_yes x c hx a τ b h
  rw [hc] at hd
  exact hb' _ _ _ _ hd

/-- And the piece of a last block that hands the state on as it is. -/
theorem psi_exact {U Cl W : Type} {Fr : Frame} (x : Piece (ckP .two) Fr (U × St) Cl W)
    (c : Block St Cl) (hx : x.b = heldW c) (ask : St → VerifiableInference.Desc.Ground.Clauses)
    (he : Exact ask c) : PsiStays x := fun a τ b h => by
  obtain ⟨rs, gs, hd⟩ := held_yes x c hx a τ b h
  rw [((he _ _ _ _).1 hd).1]

/-- **Inside the promise at border k, the five own items are kept by block k's extractor.** -/
def OwnKept {P₁ S₂ Cl Wt : Type} {C : CK} {Fr : Frame} (N : NumbersS) (Mg : MeaningS S₂ P₁ Wt)
    (Pm : PromMeaning S₂) (Oc : P₁ → Strs → Prop) (split : Bool)
    (p : Piece C Fr (P₁ × S₂) Cl Wt) (l : List (Piece C Fr (P₁ × S₂) Cl Wt))
    (e₀ : ℕ → ActV S₂ Fr → Wt → Wt) (k : ℕ) : Prop :=
  ∀ a w, onQ₂ N Pm Oc split p l k a → relOwn N Mg 2 a w →
    relOwn N Mg 2 a (e₀ k ((actQ N p l k).2 a) w)

/-- Where the table lays nothing the extractor is the identity: nothing is owed. -/
theorem ownKept_id {P₁ Cl Xi Cells Tok : Type} {Fr : Frame} (cs : OnBytes.Codes)
    (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
    (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells) (c₀ : Cells)
    (N : NumbersS) (Mg : MeaningS St P₁ (Wit Cells Tok MsgT)) (Pm : PromMeaning St)
    (Oc : P₁ → Strs → Prop) (p : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
    (l : List (Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))) (k : ℕ)
    (h : laysAtS true k = []) :
    OwnKept N Mg Pm Oc true p l (exK cs G arr smp₂ ms decT₂ c₀ N Fr) k := by
  intro a w _ hw
  show relOwn N Mg 2 a (extS cs G arr smp₂ ms decT₂ c₀ N true k _ _ w)
  rw [extS_id cs G arr smp₂ ms decT₂ c₀ N true k h]
  exact hw

/-- **What each slot has of its own rides past every piece of a list**, at the tied letters. -/
theorem each_rides_tied {P₀ P₁ Cl Xi Cells Tok : Type} {Fr : Frame} (cs : OnBytes.Codes)
    (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
    (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells)
    (mem : ℕ → Option Mem) (rd : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg → Part → ℕ → GE)
    (e' n nO : ℕ) (Q : P14) (get : P₁ → P₀ × First.S)
    (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) →
      Option ((sigOf cs s.l).om i).Smp)
    (ms₁ : List Mem) (xW : Mem)
    (stOf₁ : P₀ × First.S → Statement) (tabP₁ : P₀ × First.S → Wit Cells Tok MsgT → Nat → MsgT)
    (Pw : Where) (wSeat : ℕ × ℕ) (matC : Cells → Nat → Nat → GE)
    (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT))
    (smp₃ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₃ : List Mem) (lay₀ : VectorLay) (stOf : P₁ → Statement)
    (tabP : P₁ → Wit Cells Tok MsgT → Nat → MsgT) (rg : Wit Cells Tok MsgT → Words GE)
    (omW : Wit Cells Tok MsgT → Nat → GE) (pr : Par) (e'' : ℕ) (gOf : P₁ → Nat → GE)
    (err₂ eM : Nat)
    (rank : ((Fin pr.S.fold.index.v → Bool) →
      Fin (pr.S.fold.index.code.r + pr.S.fold.index.code.ell) → GE) → Nat)
    (held : ((ixOf2 pr.S.fold err₂ eM rank).Row × Fin pr.S.fold.index.code.ell → GE) →
      Option Cells)
    (MgZ : MeaningS St P₁ (Wit Cells Tok MsgT))
    (N₁ : Numbers) (Ns : NumbersS) (links : List ModelPart)
    (ps : List VerifiableInference.Desc.Place) (lo : ℕ) (R : P₁ → Prop) (Pm : PromMeaning St)
      (split : Bool)
    (f : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
    (l : List (Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)))
    (e₀ : ℕ → ActV St Fr → Wit Cells Tok MsgT → Wit Cells Tok MsgT)
    (hpin : Mg₁.pin = fun j t a y w => pinJT cs G arr smp₁ ms₁ j t a y w)
    (hwrow : Mg₁.wrow = fun a _ w => WRow Pw a.2 (wordsOn (stOf₁ a) (tabP₁ a w)))
    (hread : LettersReadBelow lo N₁ Mg₁ ((openSets links ps (start links))[ps.length]?.getD [])) :
    ∀ (m : List (Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))) (k : ℕ),
      (∀ x ∈ m, (∃ b₀ : Block St Cl, x.b = b₀.lift Prod.snd fun t s => (t.1, s)) ∧
        lo ≤ x.base ∧ N₁.w.1 < x.base ∧ N₁.index.1 < x.base ∧ PsiStays x) →
      (∀ j < m.length, OwnKept (tiedNumbers N₁ Ns)
        (mgK cs G arr smp₂ ms decT₂
          (tiedMeaning get Mg₁
            (mgJoint cs G arr get smp₁ ms₁ xW smp₃ ms₃ lay₀ stOf tabP rg omW pr e'' gOf err₂ eM
              rank held Pw matC MgZ)) mem rd e' n nO Q) Pm
        (ocWith (ocEnd get N₁ Mg₁
          links ps) R)
        split f l e₀ (k + j)) →
      EachRides (tiedNumbers N₁ Ns)
        (mgK cs G arr smp₂ ms decT₂
          (tiedMeaning get Mg₁
            (mgJoint cs G arr get smp₁ ms₁ xW smp₃ ms₃ lay₀ stOf tabP rg omW pr e'' gOf err₂ eM
              rank held Pw matC MgZ)) mem rd e' n nO Q) Pm
        (ocWith (ocEnd get N₁ Mg₁
          links ps) R)
        split f l e₀ k m
  | [], _, _, _ => trivial
  | x :: m, k, hx, hk => by
    obtain ⟨hb, hlo, hw, hi, hp⟩ := hx x (List.mem_cons_self ..)
    refine ⟨fun a τ b ha hout => ?_, each_rides_tied cs G arr smp₂ ms decT₂ mem rd e' n nO Q get
      smp₁ ms₁ xW stOf₁ tabP₁ Pw wSeat matC Mg₁ smp₃ ms₃ lay₀ stOf tabP rg omW pr e'' gOf
      err₂ eM rank held MgZ N₁ Ns links ps lo R Pm split f l e₀ hpin hwrow hread m (k + 1)
      (fun y hy => hx y (List.mem_cons_of_mem _ hy)) fun j hj => ?_⟩
    · obtain ⟨hoc, hback⟩ := ridesAt P₁ St Cl (Wit Cells Tok MsgT) _ (ckP .two) Fr
        (tiedNumbers N₁ Ns)
        (mgK cs G arr smp₂ ms decT₂
          (tiedMeaning get Mg₁
            (mgJoint cs G arr get smp₁ ms₁ xW smp₃ ms₃ lay₀ stOf tabP rg omW pr e'' gOf err₂ eM
              rank held Pw matC MgZ)) mem rd e' n nO Q)
        Pm _ split lo k f l x (fun _ w => w) (fun s : St => s.loc.psiSh)
        (lift_keeps x hb)
        (ocWith_readsBelow lo _ R (ocEndReadsBelow P₁ P₀ _ get lo N₁ Mg₁ links ps hread)) hlo
        (fun j t q y y' w h hp' => VerifiableInference.Desc.Sound.pin₁_col_eq cs G arr smp₁ ms₁
          Mg₁ hpin get
          (mgJoint cs G arr get smp₁ ms₁ xW smp₃ ms₃ lay₀ stOf tabP rg omW pr e'' gOf err₂ eM
            rank held Pw matC MgZ) j t q y y' w h hp') hw hi
        (fun q y y' w h => by
          have h' : Mg₁.wrow (get q) y w := h
          show Mg₁.wrow (get q) y' w
          rw [hwrow] at h' ⊢
          exact h')
        (fun q s s' y y' w hs h => by
          have hs' : s'.loc.psiSh = s.loc.psiSh := hs
          have h' : DotEq pr.S.matrixRows pr.S.kCol (gOf q) (omW w)
              (s.loc.psiSh.map OnBytes.Model.Reading.gl.val)
              (vecAt lay₀ (xW.1.l.get xW.2).1 (wTab cs arr xW w)) := h
          show DotEq pr.S.matrixRows pr.S.kCol (gOf q) (omW w)
              (s'.loc.psiSh.map OnBytes.Model.Reading.gl.val)
              (vecAt lay₀ (xW.1.l.get xW.2).1 (wTab cs arr xW w))
          rw [hs']
          exact h')
        (fun a τ b h => (hp a τ b h).symm) (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
        (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h) a τ b ha hout
      exact ⟨hoc, fun w hw' => by
        have := hk 0 (Nat.succ_pos _) a w ha (hback w hw')
        exact this⟩
    · have := hk (j + 1) (Nat.succ_lt_succ hj)
      rwa [show k + (j + 1) = k + 1 + j by omega] at this

/-- **hRd**, at the user's own letters, from its binders and five named debts (hb2, p9, p10, k9,
k10). -/
theorem each_rides_at_K {P₀ P₁ Cl Xi Cells Tok : Type} {Fr : Frame} (G : FileDescription Xi)
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
    (hb2 : base ≤ base2) (p9 : PsiStays x9) (p10 : PsiStays x10)
    (k9 : OwnKept N
      (mgK Q.codes G arr (smpSt Q.codes oNo stSh) ms decT₂ Mg₀ mem rd 2852142980
        Q.S.fold.columns nO Q)
      (pmK Q.codes G (smpSt Q.codes oNo stSh) ms decT₂ (shiftBook N.lo) Pm₀ Q.S.fold.columns nU
        nO Q X) Oc true f
      ((seatedPiece (W := Wit Cells Tok MsgT) (Cl' := Cl) (F := Fr) (P₁ := P₁) b1 base d ext
        err) :: [pc2 c2 base2 d21 d22 ex2 er2, x3, pc1 c4 base4 d4 ex4 er4,
        pc2 c5 base5 d51 d52 ex5 er5, x6, pc1 c7 base7 d7 ex7 er7, x8, x9, x10, x11])
      (exK Q.codes G arr (smpSt Q.codes oNo stSh) ms decT₂ c₀ N Fr) 9)
    (k10 : OwnKept N
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
  have pb := psi_blocks Q b1 b2 b3 b4 b5 b6 b7 b8 hbl hS
  have hbase := tiled_base_le _ _ ht
  refine each_rides_tied Q.codes G arr _ ms decT₂ mem rd _ _ nO Q get smp₁ ms₁ xW stOf₁
    tabP₁ Pw N₁.w matC Mg₁ _ _ _ _ _ _ _ _ _ gOf err₂ eM rank held MgZ N₁ Ns links ps lo R _ true f
    _ _ hpin hwrow hread _ 2 (fun x hx => ?_) (fun j hj => ?_)
  · have hB : base2 ≤ x.base := hbase x hx
    have two : (∃ b₀ : Block St Cl, x.b = b₀.lift Prod.snd fun t s => (t.1, s)) ∧
        PsiStays x := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨⟨below c2, rfl⟩, psi_held _ c2 rfl b2 h2c (pb b2 (by simp))⟩
      · exact ⟨⟨below c3, hx3⟩, psi_held _ c3 hx3 b3 h3c (pb b3 (by simp))⟩
      · exact ⟨⟨below c4, rfl⟩, psi_held _ c4 rfl b4 h4c (pb b4 (by simp))⟩
      · exact ⟨⟨below c5, rfl⟩, psi_held _ c5 rfl b5 h5c (pb b5 (by simp))⟩
      · exact ⟨⟨below c6, hx6⟩, psi_held _ c6 hx6 b6 h6c (pb b6 (by simp))⟩
      · exact ⟨⟨below c7, rfl⟩, psi_held _ c7 rfl b7 h7c (pb b7 (by simp))⟩
      · exact ⟨⟨below c8, hx8⟩, psi_held _ c8 hx8 b8 h8c (pb b8 (by simp))⟩
      · exact ⟨hx9, p9⟩
      · exact ⟨hx10, p10⟩
      · exact ⟨⟨below c11, hx11⟩, psi_exact _ c11 hx11 _ he11⟩
    exact ⟨two.1, by omega, by omega, by omega, two.2⟩
  · have hj' : j < 10 := hj
    interval_cases j
    · exact ownKept_id _ G arr _ ms decT₂ c₀ _ _ _ _ f _ _ rfl
    · exact ownKept_id _ G arr _ ms decT₂ c₀ _ _ _ _ f _ _ rfl
    · exact ownKept_id _ G arr _ ms decT₂ c₀ _ _ _ _ f _ _ rfl
    · exact ownKept_id _ G arr _ ms decT₂ c₀ _ _ _ _ f _ _ rfl
    · exact ownKept_id _ G arr _ ms decT₂ c₀ _ _ _ _ f _ _ rfl
    · exact ownKept_id _ G arr _ ms decT₂ c₀ _ _ _ _ f _ _ rfl
    · exact ownKept_id _ G arr _ ms decT₂ c₀ _ _ _ _ f _ _ rfl
    · exact k9
    · exact k10
    · exact ownKept_id _ G arr _ ms decT₂ c₀ _ _ _ _ f _ _ rfl

end Desc.K14.Law

#print axioms Desc.K14.Law.lift_keeps
#print axioms Desc.K14.Law.tiled_base_le
#print axioms Desc.K14.Law.psi_blocks
#print axioms Desc.K14.Law.psi_exact
#print axioms Desc.K14.Law.ownKept_id
#print axioms Desc.K14.Law.each_rides_tied
#print axioms Desc.K14.Law.each_rides_at_K
