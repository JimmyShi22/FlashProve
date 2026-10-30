-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3DigitsMadeTrees.lean: the lookup on the digits of a segment's approximate
range proof: AN ACCEPT OF THE WHOLE SEATED SUB-PROTOCOL LEAVES THE LEDGER's LIST OF ARRAYS; and so
the composed meaning's public tests (pubAll D base) at attention's names "K5.plain" and
"K5.readsThere" are kept (the other sorts: K3DigitsMade.lean, K3DigitsMadeMore.lean). At the
sub-protocol's own decide, whatever the rounds' words. NO SOUNDNESS IS CLAIMED.

Main names.
  k3_digits_trees: at K3.block's .ok at the digits' seat, from a ledger F with its sizes: the ledger
    behind has F's list of arrays (by decide_left_some, Johnson/Top/H/Keep/K3LeftAnyWords.lean:
    PadLeft's field rest). k3_digits_step_trees: at the whole seated sub-protocol (the step without
    a round turns planClaimsF alone: quietAt_ledger).
  digits_keeps_plain, digits_keeps_readsThere: each spends the same item at s and the promise in
    front k3OnIn p s (for the ledger's sizes).
NO FACT ALONG THE FOLD IS SPENT BY ANY LEMMA OF THIS FILE.
OBJECT. Desc.K3.theStated's value at the digits' address; pubAll D base.
USER. Johnson/Desc/Sound/MgAt/K3DigitsOthers.lean calls digits_keeps_plain; no file calls
digits_keeps_readsThere.
LETTERS. Those of K3DigitsMadeMore.lean.
IS IT EMPTY? The premises are an .ok of decide, the place and tests in front.



Compiled with the whole library.
Limits. One way each.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3DigitsOwnStays
import Johnson.Desc.First.Look.K3DigitsTies
import Johnson.Desc.First.PubAllAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Pub PubData pubAll pubAll_more_plain pubAll_more_readsThere)

/-- **K3.block's .ok at the digits' seat leaves the ledger's list of arrays.** -/
theorem k3_digits_trees {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) {h : Forest.Shape}
    (hs : p.shape = some h) (s s' : Desc.First.S) (rs : List Fmt.RoundView)
    (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block (Desc.K3.seatDigits claim) piece laid before p guests).decide s rs cols =
      .ok s') {F : Fork} (hF : s.fork? = some F) (hS : OnBytes.PscRun.Sized F) :
    ∃ G, s'.fork? = some G ∧ G.trees = F.trees := by
  obtain ⟨F0, x, hF0, hn0, e0, hL⟩ :=
    decide_left_some (Desc.K3.seatDigits claim) piece laid before p guests
      (Desc.K3.seatDigits_reads claim) h hs Reading.gl p.lm s s' rs cols hd
  obtain rfl : F = F0 := Option.some.inj (hF.symm.trans hF0)
  have hsome : ((Desc.K3.seatDigits claim).fork s).isSome = true := by
    rw [hF0]
    rfl
  obtain ⟨rs', L⟩ := hL hS
  refine ⟨x.2, ?_, L.padLeft.rest.1⟩
  rw [e0]
  exact seatDigits_keeps claim _ _ _ hsome hn0

section
variable {Cl : Type}

/-- **So does the whole seated sub-protocol.** -/
theorem k3_digits_step_trees (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (i : ℕ) (hi : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i true)
    {x : Desc.First.Look.Place} (hlook : lookAt X i true = some x) {hs : Forest.Shape}
    (hsh : (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x).shape = some hs)
    (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok s₂) {F : Fork} (hF : s.fork? = some F)
    (hS : OnBytes.PscRun.Sized F) :
    ∃ G, s₂.fork? = some G ∧ G.trees = F.trees := by
  obtain ⟨P', sent, laid, n, gs', s', hP, hyes, hstep⟩ :=
    theStated_yes_digits claim readers X codes shape a B h hOk i hi hpc s s₂ rs gs hd
  have eP : P' = (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x) := by
    unfold placeAt at hP
    rw [hlook] at hP
    exact (Option.some.inj hP).symm
  subst eP
  obtain ⟨G, hG, hT⟩ := k3_digits_trees claim a.piece laid sent _ [] hsh s s' _ gs' hyes hF hS
  rcases hstep with e | ⟨f, hf, hfs⟩
  · rw [e]
    exact ⟨G, hG, hT⟩
  · obtain ⟨F₂, c, hF₂, hG₂, -⟩ := quietAt_ledger X i f hf s' s₂ hfs
    obtain rfl : G = F₂ := Option.some.inj (hG.symm.trans hF₂)
    exact ⟨_, hG₂, hT⟩

end

section
variable {P Cl : Type} (D : PubData) (base : Pub → P × Desc.First.S → Bool)

/-- **"K5.plain": kept.** -/
theorem digits_keeps_plain (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers D.d3.X codes shape a = some B) (hOk : B.planOk = true)
    (i : ℕ) (hi : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt D.d3.X i true)
    (z : P) (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok s₂)
    {x : Desc.First.Look.Place} (hlook : lookAt D.d3.X i true = some x) {hs : Forest.Shape}
    (hsh : (Desc.First.Look.P.ofPlace (Params.settingOf D.d3.X.P.frame) true x).shape = some hs)
    (hIn : Desc.K3.k3OnIn
      (Desc.First.Look.P.ofPlace (Params.settingOf D.d3.X.P.frame) true x) s = true)
    (m : ℕ) (hm : D.d5.isAtt m = true)
    (hin : pubAll D base (.more (some m) "K5.plain") (z, s) = true) :
    pubAll D base (.more (some m) "K5.plain") (z, s₂) = true := by
  obtain ⟨F, hF, hS, -⟩ := k3OnIn_ledger hIn
  obtain ⟨G, hG, hT⟩ := k3_digits_step_trees claim readers D.d3.X codes shape a B h hOk i hi hpc
    hlook hsh s s₂ rs gs hd hF hS
  have e5 := digits_step_heard5 claim readers D.d3.X codes shape a B h hOk i hi hpc hlook hsh s s₂
    rs gs hd
  rw [pubAll_more_plain D base m hm] at hin ⊢
  have e : ∀ q : Attention.Plan, H2K5.Door.plainThereB q.iU3 q.nW s₂ =
      H2K5.Door.plainThereB q.iU3 q.nW s := by
    intro q
    unfold H2K5.Door.plainThereB
    rw [hG, hF, e5]
    cases s.heard5? with
    | none => rfl
    | some e0 =>
      show (H2K5.Door.heardPlainB e0 && H2K5.Door.wideB G q.iU3 q.nW) =
        (H2K5.Door.heardPlainB e0 && H2K5.Door.wideB F q.iU3 q.nW)
      unfold H2K5.Door.wideB
      rw [hT]
  show ((D.d5.W.A[m / 2]?).any fun q => H2K5.Door.plainThereB q.iU3 q.nW s₂) = true
  simp only [e]
  exact hin

/-- **"K5.readsThere": kept.** -/
theorem digits_keeps_readsThere (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers D.d3.X codes shape a = some B) (hOk : B.planOk = true)
    (i : ℕ) (hi : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt D.d3.X i true)
    (z : P) (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok s₂)
    {x : Desc.First.Look.Place} (hlook : lookAt D.d3.X i true = some x) {hs : Forest.Shape}
    (hsh : (Desc.First.Look.P.ofPlace (Params.settingOf D.d3.X.P.frame) true x).shape = some hs)
    (hIn : Desc.K3.k3OnIn
      (Desc.First.Look.P.ofPlace (Params.settingOf D.d3.X.P.frame) true x) s = true)
    (m : ℕ) (hm : D.d5.isAtt m = true)
    (hin : pubAll D base (.more (some m) "K5.readsThere") (z, s) = true) :
    pubAll D base (.more (some m) "K5.readsThere") (z, s₂) = true := by
  obtain ⟨F, hF, hS, -⟩ := k3OnIn_ledger hIn
  obtain ⟨G, hG, hT⟩ := k3_digits_step_trees claim readers D.d3.X codes shape a B h hOk i hi hpc
    hlook hsh s s₂ rs gs hd hF hS
  have T := (k3_digits_step_turns claim readers D.d3.X codes shape a B h hOk i hi hpc hlook hsh s s₂
    rs gs hd).1
  have A := k3_digits_step_attStays claim readers D.d3.X codes shape a B h hOk i hi hpc s s₂ rs gs
    hd
  rw [pubAll_more_readsThere D base m hm] at hin ⊢
  have h0 : H2K5.Door.readsThereB D.d5.W (D.d5.ownOf m) s = true := hin
  show H2K5.Door.readsThereB D.d5.W (D.d5.ownOf m) s₂ = true
  unfold H2K5.Door.readsThereB at h0 ⊢
  cases hh : s.here with
  | att u =>
    rw [hh] at h0
    obtain ⟨w, hw, k⟩ := A u hh
    have eL : w.L = u.L := congrArg (·.L) (k u.tl u.F)
    have eF : u.F = F := by simpa [Desc.First.S.fork?, hh] using hF
    have eG : w.F = G := by simpa [Desc.First.S.fork?, hw] using hG
    rw [hw]
    show ((D.d5.W.A[w.L.link / 2]?).any fun q =>
      H2K5.Door.readsAtB (D.d5.ownOf m) q.iU3 q.nW w.L w.F s₂.book) = true
    have h1 : ((D.d5.W.A[u.L.link / 2]?).any fun q =>
      H2K5.Door.readsAtB (D.d5.ownOf m) q.iU3 q.nW u.L u.F s.book) = true := h0
    rw [eL, eG, T.book]
    rw [eF] at h1
    have e3 : ∀ q : Attention.Plan,
        H2K5.Door.readsAtB (D.d5.ownOf m) q.iU3 q.nW u.L G s.book =
          H2K5.Door.readsAtB (D.d5.ownOf m) q.iU3 q.nW u.L F s.book := by
      intro q
      unfold H2K5.Door.readsAtB
      rw [hT]
    simp only [e3]
    exact h1
  | between => rw [hh] at h0; cases h0
  | fin _ => rw [hh] at h0; cases h0
  | mem _ => rw [hh] at h0; cases h0
  | lay _ => rw [hh] at h0; cases h0
  | head _ => rw [hh] at h0; cases h0

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3_digits_trees
#print axioms VerifiableInference.OnPublicFiles.k3_digits_step_trees
#print axioms VerifiableInference.OnPublicFiles.digits_keeps_plain
#print axioms VerifiableInference.OnPublicFiles.digits_keeps_readsThere
