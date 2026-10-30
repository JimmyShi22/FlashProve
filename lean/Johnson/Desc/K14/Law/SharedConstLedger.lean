-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstLedger.lean: FROM THE LEDGER's END TO THE SHARED TABLE's CONSTANT.
The ledger's top ends in EachLawsBN at the promise pmK … XK, the three shapes written as K1 reads
them off the two sendings. The constant's promise Sh.pm (Johnson/Desc/K14/Law/SharedConst.lean) has
the parameters' own shapes and, beside XK, the tests for the last chain's door (XD). HERE the step
between the two, so that the top need not be typed again.

  Sh.pmXK, Sh.pmXK_is   the promise at XK in the constant's letters; it IS the top's own term (the
                  shapes are the parameters': Sh.shapes_are).
  Sh.pm_is        Sh.pm is Sh.pmXK with XD laid beside: as terms (pmW_is).
  Sh.ledger_at_const   **the ledger's end at Sh.pmXK gives the ledger's end at Sh.pm**, at the same
                  keys, errors and extractor, where each piece's accepting step hands XD on
                  (eachLawsBN_beside).
  Sh.Law, Sh.law_of_ledger   **the law's own name at the constant** (what is counted as K14's law on
                  the shared chain), and the same step ending in it.
  Sh.xd_row       hXD, paid at the row's twelve pieces from the pieces' forms.
WHAT STAYS. hXD: at each of the row's pieces, inside the constant's promise, an accepting step hands
XD on: away from the last border XD is "the book fits" (fitsX_front | fitsX_k14 |
fitsX_onGu | fitsX_onGomega); at the last piece it is door_of_record (LedgerDoor).
What is not claimed. No law of its own. No soundness; no level.

-/
import Johnson.Desc.K14.Law.SharedConstWalk
import Johnson.Desc.Sound.LedgerBesideAll
import Johnson.Desc.K14.Law.LedgerSmpK

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words wordsOn)
open Johnson.Pack
open _root_.Run.PQ (CK)
open Cb Cb.Ood Blocks Cb.Pv Cb.Pv.Lin Cb.Bridge
open VerifiableInference.Desc (Block Strs Wit FileDescription First.S Grows)
open VerifiableInference.Desc.ChainEnd (untestedL Exact)
open VerifiableInference.Desc.K1 (sendPiece sampledAt shapeAt shapesOf condPort errPort seedEntry
  seedMaps)
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Pub pubSets openSets start)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts Seat.onGu Seat.onGomega)
open VerifiableInference.Desc.K12.Coin
open Desc.K14.Law.Fence
open H2K.Pin (NTuple)
open H2K.Pub (johOk batV0 PayPub)
open H2K.First (batOneOk)
open VerifiableInference.Desc.K13.Law (EvalAt laidOf wSitsItem wSitsMore)
open VerifiableInference.Desc.Third (P₁₄)

namespace Sh

variable {Xi P₀ P₁ Cl Cells Tok : Type} {Fr : Frame} (A : ShPlan Xi)
  (O : ShOpen P₀ P₁ Cells Tok A.Q)

/-- The promise at XK, in the constant's letters. -/
def pmXK : PromMeaning St := (pmK A.Q.codes A.G (smp₂ A) (ms A) (decT₂ A O) (shiftBook (nums A
    O).lo) (pm₀ A O) A.Q.S.fold.columns 0 (sentU A).size A.Q (XK A.Q (sentU A) (layU A) (layO A)
    (A.Q.S.fold.u, A.Q.S.omega, A.Q.S.sharedSplit, Y A) (sentU A).size))

/-- **It is the ledger's top's own term.** -/
theorem pmXK_is (hUw : withU A.Q.S = some (sentU A)) (hS : A.Q.S.sharedSplitNeeded = true) :
    (pmK A.Q.codes A.G (smp₂ A) (ms A) (decT₂ A O) (shiftBook (nums A O).lo) (pm₀ A O)
        A.Q.S.fold.columns 0 (sentU A).size A.Q (XK A.Q (sentU A) (layU A) (layO A) (shapeAt (parU
        A.Q (sentU A)) ⟨0, (places A.Q (sentU A)).1 hUw⟩, shapeAt (parO A.Q) ⟨0, (places A.Q (sentU
        A)).2.1⟩, shapeAt (parO A.Q) ⟨1, (places A.Q (sentU A)).2.2 hS⟩, smpK A.Q.codes (shapeAt
        (parU A.Q (sentU A)) ⟨0, (places A.Q (sentU A)).1 hUw⟩) (shapeAt (parO A.Q) ⟨0, (places A.Q
        (sentU A)).2.1⟩) (shapeAt (parO A.Q) ⟨1, (places A.Q (sentU A)).2.2 hS⟩) (sentU A).size)
        (sentU A).size)) = pmXK A O := by
  obtain ⟨e1, e2, e3⟩ := shapes_are A hUw hS
  rw [e1, e2, e3]
  rfl

/-- **Sh.pm is Sh.pmXK with XD laid beside.** -/
theorem pm_is : pm A O = besideP (pmXK A O) (XD A.p) :=
  pmW_is A.Q (sentU A) (layU A) (layO A) (A.Q.S.fold.u, A.Q.S.omega, A.Q.S.sharedSplit, Y A)
    (sentU A).size A.p (decT₂ A O) (pm₀ A O) A.Q.S.fold.columns 0 A.Q.codes A.G (ms A) (nums A O)
    (oNo A)

/-- **FROM THE LEDGER's END TO THE CONSTANT.** -/
theorem ledger_at_const {κ : Type} (key : ℕ → (P₁ × St) × Fr.E.Str → κ)
    (f : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (l : List (Piece (ckP .two) Fr (P₁ ×
        St) Cl (Wit Cells Tok MsgT)))
    (ext : ℕ → (P₁ × St) × Fr.E.Str → Wit Cells Tok MsgT → Wit Cells Tok MsgT) (n : ℕ)
    (hXD : ∀ i x, (f :: l)[i]? = some x → ∀ a τ b,
      onQ₂ (nums A O) (pm A O) (own A O) true f l i a → x.ior.red.out a τ = some b →
      XD A.p (i + 1) b.1.2 = true)
    (L : EachLawsBN key (onQ₂ (nums A O) (pmXK A O) (own A O) true f l)
      (stepAt (nums A O) (mg A O) (pmXK A O) (own A O) true f l ext) n 0 (f :: l)) :
    EachLawsBN key (onQ₂ (nums A O) (pm A O) (own A O) true f l)
      (stepAt (nums A O) (mg A O) (pm A O) (own A O) true f l ext) n 0 (f :: l) := by
  rw [pm_is] at hXD ⊢
  exact eachLawsBN_beside (nums A O) (mg A O) (pmXK A O) (own A O) true f l (XD A.p) key ext n
    (f :: l) 0 (fun i x hx a τ b ha hb => by
      rw [Nat.zero_add] at ha ⊢
      exact hXD i x hx a τ b ha hb) L

/-- Y from border 11 to border 12, at one state. -/
theorem smpK_last (s : St) (h : Y A 11 s = true) : Y A 12 s = true := by
  obtain ⟨h1, h2, h3⟩ := smpK_parts _ _ _ A.Q.codes (sentU A).size 11 s h
  unfold Y smpK
  rw [smpY_last _ _ _ _ (by omega) s h1, smpY_last _ _ _ _ (by omega) s h2,
    smpY_last _ _ _ _ (by omega) s h3]
  rfl

/-! ## The law's own name -/

/-- **K14's LAW ON THE SHARED CHAIN, AT THE CONSTANT**: each of the row's pieces has its law for a
batch of `slots` slots, at its own list of error bounds, between the constant's promise in front
and behind, with the constant's extractor. f: the front's piece; l: the other eleven. -/
def Law (f : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (l : List (Piece (ckP .two) Fr
    (P₁ × St) Cl (Wit Cells Tok MsgT))) (slots : ℕ) : Prop :=
  EachLawsBN (keyAt Prod.snd (nums A O).lo f l) (onQ₂ (nums A O) (pm A O) (own A O) true f l)
    (stepAt (nums A O) (mg A O) (pm A O) (own A O) true f l
      (extOf (nums A O) f l (ex A O Fr))) slots 0 (f :: l)

/-- **From the ledger's end, at the promise without the door, to the law.** -/
theorem law_of_ledger (f : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (l : List (Piece
    (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))) (slots : ℕ)
    (hXD : ∀ i x, (f :: l)[i]? = some x → ∀ a τ b,
      onQ₂ (nums A O) (pm A O) (own A O) true f l i a → x.ior.red.out a τ = some b →
      XD A.p (i + 1) b.1.2 = true)
    (L : EachLawsBN (keyAt Prod.snd (nums A O).lo f l)
      (onQ₂ (nums A O) (pmXK A O) (own A O) true f l)
      (stepAt (nums A O) (mg A O) (pmXK A O) (own A O) true f l
        (extOf (nums A O) f l (ex A O Fr))) slots 0 (f :: l)) : Law A O f l slots :=
  ledger_at_const A O _ f l _ slots hXD L

/-! ## hXD, paid at the row's twelve pieces -/

/-- Inside the constant's promise: XD, and XK. -/
theorem XD_of_on (f : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (l : List (Piece (ckP
    .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))) (k : ℕ) (a : (P₁ × St) × Fr.E.Str)
    (ha : onQ₂ (nums A O) (pm A O) (own A O) true f l k a) : XD A.p k a.1.2 = true := by
  rw [pm_is] at ha
  exact ((on_beside (nums A O) (pmXK A O) (own A O) true f l (XD A.p) k a).1 ha).2

theorem XK_of_on (f : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (l : List (Piece (ckP
    .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))) (k : ℕ) (a : (P₁ × St) × Fr.E.Str)
    (ha : onQ₂ (nums A O) (pm A O) (own A O) true f l k a) : (XK A.Q (sentU A) (layU A) (layO A)
        (A.Q.S.fold.u, A.Q.S.omega, A.Q.S.sharedSplit, Y A) (sentU A).size) k a.1.2 = true := by
  rw [pm_is] at ha
  have h1 := ((on_beside (nums A O) (pmXK A O) (own A O) true f l (XD A.p) k a).1 ha).1
  unfold pmXK smp₂ at h1
  rw [pmK_is] at h1
  have h2 := beside_of_on _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ f l k a h1
  unfold XK
  exact Bool.and_eq_true_iff.2 ⟨h2.1, h2.2.2.1⟩

/-- One of the kind's eight sub-protocols, at a piece that holds it in the wrap: "the book fits" is
handed on. -/
theorem fits_k14 (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks A.Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) (b : Block St Unit)
    (hb : b ∈ [b1, b2, b3, b4, b5, b6, b7, b8]) (c : Block St Cl) (hc : DecidesAs c b)
    (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (hx : x.b = heldW c) (j k : ℕ) (a :
        (P₁ × St) × Fr.E.Str)
    (τ : Iop.Tr (uLT (ckP .two) x.ds)) (y : (P₁ × St) × Fr.E.Str)
    (hout : x.ior.red.out a τ = some y) (h : fitsX j a.1.2 = true) : fitsX k y.1.2 = true := by
  obtain ⟨rs, gs, hd⟩ := held_yes x c hx a τ y hout
  rw [hc] at hd
  exact fitsX_k14 A.Q b1 b2 b3 b4 b5 b6 b7 b8 hbl b hb j k _ _ rs gs hd h

variable (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
  (hbl : blocks A.Q = some [b1, b2, b3, b4, b5, b6, b7, b8])
  (c1 c2 c3 c4 c5 c6 c7 c8 : Block St Cl)
  (h1c : DecidesAs c1 b1) (h2c : DecidesAs c2 b2) (h3c : DecidesAs c3 b3) (h4c : DecidesAs c4 b4)
  (h5c : DecidesAs c5 b5) (h6c : DecidesAs c6 b6) (h7c : DecidesAs c7 b7) (h8c : DecidesAs c8 b8)
  (f pt x3 x6 x8 x9 x10 x11 : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
  (base2 base4 base5 base7 : ℕ) (d21 d22 d4 d51 d52 d7 : RDT)
  (ex2 : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d21, d22]) → Wit Cells Tok MsgT → Wit Cells
      Tok MsgT)
  (er2 : Err (uLT (ckP .two) [d21, d22]))
  (ex4 : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d4]) → Wit Cells Tok MsgT → Wit Cells Tok
      MsgT)
  (er4 : Err (uLT (ckP .two) [d4]))
  (ex5 : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d51, d52]) → Wit Cells Tok MsgT → Wit Cells
      Tok MsgT)
  (er5 : Err (uLT (ckP .two) [d51, d52]))
  (ex7 : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d7]) → Wit Cells Tok MsgT → Wit Cells Tok
      MsgT)
  (er7 : Err (uLT (ckP .two) [d7]))
  (hxp : pt.b = heldW c1) (hx3 : x3.b = heldW c3) (hx6 : x6.b = heldW c6) (hx8 : x8.b = heldW c8)

include hbl h1c h2c h3c h4c h5c h6c h7c h8c hxp hx3 hx6 hx8 in
/-- **hXD at the row.** -/
theorem xd_row
    (hfd : ∀ a τ b, f.ior.red.out a τ = some b →
      ∃ (c : Model.Verify.Chains) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
        (frontBlock c).decide a.1.2 rs gs = .ok b.1.2)
    (πA πB : P12)
    (hbA : Alike (held (P := P₁) (Seat.onGu (proximityTestKind guardedProximityTestParts πA : Block T12 Unit))) x9.b)
    (heA : πA.early = true) (ha1A : πA.answers = 1)
    (hbB : Alike (held (P := P₁) (Seat.onGomega (proximityTestKind guardedProximityTestParts πB : Block T12 Unit))) x10.b)
    (heB : πB.early = true) (ha1B : πB.answers = 1)
    (hend : ∀ a τ b, x11.ior.red.out a τ = some b → b.1.2 = a.1.2)
    (hpS : A.p.S.omega = A.Q.S.omega) (h1a : A.Q.S.omega.answers = 1)
    (hlO : layTrees A.Q.codes (withOmega A.Q.S) = some (layO A))
    (hO : 0 < (withOmega A.Q.S).size) :
    ∀ i x, (f :: [pt, pc2 c2 base2 d21 d22 ex2 er2, x3, pc1 c4 base4 d4 ex4 er4, pc2 c5 base5 d51
        d52 ex5 er5, x6, pc1 c7 base7 d7 ex7 er7, x8, x9, x10, x11])[i]? = some x → ∀ a τ b,
      onQ₂ (nums A O) (pm A O) (own A O) true f [pt, pc2 c2 base2 d21 d22 ex2 er2, x3, pc1 c4 base4
          d4 ex4 er4, pc2 c5 base5 d51 d52 ex5 er5, x6, pc1 c7 base7 d7 ex7 er7, x8, x9, x10, x11] i
          a → x.ior.red.out a τ = some b →
      XD A.p (i + 1) b.1.2 = true := by
  intro i x hx a τ b ha hout
  have hF : fitsX i a.1.2 = true := ((XD_iff A.p i _).1 (XD_of_on A O f _ i a ha)).1
  have K := fits_k14 (Cl := Cl) (Fr := Fr) (P₁ := P₁) (Cells := Cells) (Tok := Tok) A b1 b2 b3 b4 b5
      b6
    b7 b8 hbl
  match i, hx with
  | 0, hx =>
    obtain rfl : f = x := Option.some.inj hx
    obtain ⟨c, rs, gs, hd⟩ := hfd a τ b hout
    exact XD_off A.p 1 (by omega) _ (fitsX_front c _ _ rs gs hd hF)
  | 1, hx =>
    obtain rfl : pt = x := Option.some.inj hx
    exact XD_off A.p 2 (by omega) _ (K b1 (by simp) c1 h1c pt hxp 1 2 a τ b hout hF)
  | 2, hx =>
    obtain rfl := Option.some.inj hx
    exact XD_off A.p 3 (by omega) _ (K b2 (by simp) c2 h2c (pc2 c2 base2 d21 d22 ex2 er2) rfl 2 3 a
        τ b hout hF)
  | 3, hx =>
    obtain rfl : x3 = x := Option.some.inj hx
    exact XD_off A.p 4 (by omega) _ (K b3 (by simp) c3 h3c x3 hx3 3 4 a τ b hout hF)
  | 4, hx =>
    obtain rfl := Option.some.inj hx
    exact XD_off A.p 5 (by omega) _ (K b4 (by simp) c4 h4c (pc1 c4 base4 d4 ex4 er4) rfl 4 5 a τ b
        hout hF)
  | 5, hx =>
    obtain rfl := Option.some.inj hx
    exact XD_off A.p 6 (by omega) _ (K b5 (by simp) c5 h5c (pc2 c5 base5 d51 d52 ex5 er5) rfl 5 6 a
        τ b hout hF)
  | 6, hx =>
    obtain rfl : x6 = x := Option.some.inj hx
    exact XD_off A.p 7 (by omega) _ (K b6 (by simp) c6 h6c x6 hx6 6 7 a τ b hout hF)
  | 7, hx =>
    obtain rfl := Option.some.inj hx
    exact XD_off A.p 8 (by omega) _ (K b7 (by simp) c7 h7c (pc1 c7 base7 d7 ex7 er7) rfl 7 8 a τ b
        hout hF)
  | 8, hx =>
    obtain rfl : x8 = x := Option.some.inj hx
    exact XD_off A.p 9 (by omega) _ (K b8 (by simp) c8 h8c x8 hx8 8 9 a τ b hout hF)
  | 9, hx =>
    obtain rfl : x9 = x := Option.some.inj hx
    obtain ⟨rs, gs, hd, _⟩ := held_decides _ _ hbA a b τ hout
    exact XD_off A.p 10 (by omega) _ (fitsX_onGu πA heA ha1A 9 10 _ _ rs gs hd hF)
  | 10, hx =>
    obtain rfl : x10 = x := Option.some.inj hx
    obtain ⟨rs, gs, hd, _⟩ := held_decides _ _ hbB a b τ hout
    exact XD_off A.p 11 (by omega) _ (fitsX_onGomega πB heB ha1B 10 11 _ _ rs gs hd hF)
  | 11, hx =>
    obtain rfl : x11 = x := Option.some.inj hx
    rw [hend a τ b hout]
    have hK := XK_last A.Q (sentU A) (layU A) (layO A) _ _
      (fun s h => smpK_last A s h) a.1.2 (XK_of_on A O f _ 11 a ha)
    exact (XD_iff A.p 12 _).2 ⟨hF, Or.inr (door_of_record A.Q (sentU A) (layU A) (layO A) _ _ A.p
        hpS
      h1a rfl hlO hO a.1.2 hK hF)⟩
  | n + 12, hx => exact absurd hx (by simp)

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.pmXK_is
#print axioms Desc.K14.Law.Sh.pm_is
#print axioms Desc.K14.Law.Sh.ledger_at_const
#print axioms Desc.K14.Law.Sh.law_of_ledger
#print axioms Desc.K14.Law.Sh.XK_of_on
#print axioms Desc.K14.Law.Sh.xd_row
