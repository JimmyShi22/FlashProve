-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3DigitsMade.lean: the lookup on the digits of a segment's approximate range
proof: THE PUBLIC TESTS OF THE COMPOSED MEANING (pubAll D base, Johnson/Desc/First/PubAll.lean:
another house's) THAT AN ACCEPT OF THE WHOLE SEATED SUB-PROTOCOL MAKES OR KEEPS, A LEMMA A SORT OF
ITEM, AS FACTS ON TWO STATES OF THE VERIFIER: at the sub-protocol's own decide, whatever the rounds'
words. For the debt «what is asked behind my place and does not ride by the footprints' rule». NO
SOUNDNESS IS CLAIMED.

Main names. Each: an .ok of decide from s to s₂, and what it spends of the tests in front, give the
test behind.
  digits_makes_lookOut: lookOut i (the digits' piece): NEW BEHIND THE PLACE: spends lookIn i (that
    piece) at s.
  digits_keeps_lookOut: lookOut i (the calls' piece): spends the same item at s.
  digits_makes_leftOn: leftOn i: the test is «true».
  digits_keeps_liveReq: the name "K5.liveReq" at an attention segment: spends the same item at s (it
    reads the open segment's link context alone).
NOT HERE, BY NAME: ledger, freeAbove (another house's hands take the items that read the ledger, for
all kinds: they call digLeft_ledgerB, digLeft_freeAboveB, K3KeeperRides.lean, under
k3_digits_step_leaves) · hasRow · formsIn of other sub-protocols' runs and of this one's · the names
"K5.readsThere", "K5.okAt", "K5.plain" (each reads the ledger beside what attention's own rounds
heard) · tokenSmall. NO FACT ALONG THE FOLD IS SPENT BY ANY LEMMA OF THIS FILE.
OBJECT. Desc.K3.theStated's value at the digits' address; pubAll D base.
USER. Nobody yet.
LETTERS. D, base; claim, readers, codes, shape, a, B, i; z, s, s₂, rs, gs.
IS IT EMPTY? The premises are an .ok of decide and tests in front.
Limits. The public parameters are D.d3.X. Nothing where decide rejects.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3DigitsStep
import Johnson.Desc.First.Look.K3Fill
import Johnson.Desc.First.PubAllAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Pub PubData pubAll pubAll_lookIn pubAll_lookOut pubAll_leftOn
  pubAll_more_liveReq)

section
variable {P Cl : Type} (D : PubData) (base : Pub → P × Desc.First.S → Bool)

/-- **lookOut at the digits' piece: made.** -/
theorem digits_makes_lookOut (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers D.d3.X codes shape a = some B) (hOk : B.planOk = true)
    (i : ℕ) (hi : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt D.d3.X i true)
    (z : P) (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok s₂)
    (hin : pubAll D base (.lookIn i a.piece) (z, s) = true) :
    pubAll D base (.lookOut i a.piece) (z, s₂) = true := by
  rw [hpc, pubAll_lookIn D base i _ true (sort_at D.d3.X i true)] at hin
  rw [hpc, pubAll_lookOut D base i _ true (sort_at D.d3.X i true)]
  unfold lookInC at hin
  unfold lookOutC
  unfold placeAt at hin ⊢
  cases hlook : lookAt D.d3.X i true with
  | none =>
    rw [hlook] at hin
    cases hin
  | some x =>
    rw [hlook] at hin
    have h1 : (Desc.K3.k3OnIn (Desc.First.Look.P.ofPlace (Params.settingOf D.d3.X.P.frame) true x)
        s && s.link?.any fun C =>
          C.link == (Desc.First.Look.P.ofPlace (Params.settingOf D.d3.X.P.frame) true x).link &&
            C.arrayOf == D.d3.arrayOf.getD i #[]) = true := hin
    have hIn := (Eq.mp (Bool.and_eq_true _ _) h1).1
    cases hsh : (Desc.First.Look.P.ofPlace (Params.settingOf D.d3.X.P.frame) true x).shape with
    | none =>
      unfold Desc.K3.k3OnIn at hIn
      rw [hsh] at hIn
      cases hIn
    | some hs =>
      exact (k3_digits_step_turns claim readers D.d3.X codes shape a B h hOk i hi hpc hlook hsh s s₂
        rs gs hd).2 hIn

/-- **lookOut at the calls' piece: kept.** -/
theorem digits_keeps_lookOut (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers D.d3.X codes shape a = some B) (hOk : B.planOk = true)
    (i : ℕ) (hi : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt D.d3.X i true)
    (z : P) (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok s₂)
    (hin : pubAll D base (.lookOut i (Desc.K3.pieceAt D.d3.X i false)) (z, s) = true) :
    pubAll D base (.lookOut i (Desc.K3.pieceAt D.d3.X i false)) (z, s₂) = true := by
  rw [pubAll_lookOut D base i _ false (sort_at D.d3.X i false)] at hin ⊢
  unfold lookOutC at hin ⊢
  obtain ⟨-, -, -, -, -, -, hO⟩ :=
    k3_digits_step_leaves claim readers D.d3.X codes shape a B h hOk i hi hpc s s₂ rs gs hd
  unfold placeAt at hin ⊢
  cases hlook : lookAt D.d3.X i false with
  | none =>
    rw [hlook] at hin
    cases hin
  | some x =>
    rw [hlook] at hin
    exact hO _ rfl hin

/-- **leftOn: the test is «true».** -/
theorem digits_makes_leftOn (i : ℕ) (a : P × Desc.First.S) :
    pubAll D base (.leftOn i) a = true := pubAll_leftOn D base i a

/-- **"K5.liveReq": kept.** -/
theorem digits_keeps_liveReq (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers D.d3.X codes shape a = some B) (hOk : B.planOk = true)
    (i : ℕ) (hi : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt D.d3.X i true)
    (z : P) (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok s₂)
    {x : Desc.First.Look.Place} (hlook : lookAt D.d3.X i true = some x) {hs : Forest.Shape}
    (hsh : (Desc.First.Look.P.ofPlace (Params.settingOf D.d3.X.P.frame) true x).shape = some hs)
    (m : ℕ) (hm : D.d5.isAtt m = true)
    (hin : pubAll D base (.more (some m) "K5.liveReq") (z, s) = true) :
    pubAll D base (.more (some m) "K5.liveReq") (z, s₂) = true := by
  have T := (k3_digits_step_turns claim readers D.d3.X codes shape a B h hOk i hi hpc hlook hsh s s₂
    rs gs hd).1
  rw [pubAll_more_liveReq D base m hm] at hin ⊢
  unfold Desc.First.Att.P.liveReqB at hin ⊢
  rw [T.link]
  exact hin

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.digits_makes_lookOut
#print axioms VerifiableInference.OnPublicFiles.digits_keeps_lookOut
#print axioms VerifiableInference.OnPublicFiles.digits_keeps_liveReq
