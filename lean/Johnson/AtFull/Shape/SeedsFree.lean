-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/SeedsFree.lean: AT THE 52 MEMBERS OF THE PROOF FILE's OWN FIRST CHAIN THAT HOLD
A SENDING OF THE KIND K1, THE NAMED TEST ON VALUES "NO SEED's FACTOR IS 0" (seedsV, FrameForm.lean)
IS PAID BY THE MEMBER's OWN TEST ON THE ROUNDS' FORM: SO THE FRAME's TWO PREMISES STAND THERE
WITHOUT IT. Under the head P5J.AtMgA. Nothing is evaluated.

Why it can be had. seedsV asks of each seed's factor that isZeroE says no, and isZeroE
(OnBytes/Field/Ext.lean) says yes just where all three WORDS are 0. The test on the rounds' form
(roundsFit, Johnson/Desc/Block.lean) asks the same of each drawn element that the format marks as
never 0. The library's factors_of_fit (Johnson/Prover/Send/Form.lean) ties the two at K1's declared
rounds. "Returns" (Johnson/Desc/ProofFile/Honest/Thread/Shape.lean) hands in rounds that fit.

  1 **`seedsV_of_fit`**: roundsFit (K1.rounds P) rs = true: then seedsV P (rs.map noDigest) = true.
  2 `returns_strike`: at a member whose declared rounds are K1.rounds P: "Returns" under the tests
    seedsV P rs && V s rs gs gives "Returns" under V alone. `returns_strike_all`: under seedsV
    alone: "Returns" under whatever tests.
  3 **`opening_frame_free`** (member 2), **`digits_frame_free`** (25 members),
    **`sendW_frame_free`** (member 356), **`reads_layers_frame_free`** (12 members): the statements
    of opening_frame, digits_frame, sendW_frame and reads_layers_frame WITHOUT THEIR PREMISE ON
    vals: for every vals.
    **`reads_att_frame_free`** (12 members), **`reads_head_frame_free`** (member 342): those of
    reads_att_frame and reads_head_frame with vals the one further test (midV …) alone.

Limits. "Not 0" is said of words, as K1's text says it. The further tests at the thirteen reads'
members of the attention links and the head's link stay. No state is shown at which a step on shapes
returns. That the head has a member is shown in scope, where the reader returns and `protocolDataWellFormed`
accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold together, at two named
sets of public files, in a side library. At the format's second hash function. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.OpeningFrame
import Johnson.AtFull.Shape.SendWFrame
import Johnson.AtFull.Shape.ReadsFrames
import Johnson.Prover.Send.Form

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link Place KindName roundsFit noDigest)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open Johnson.Desc.First.Walk
open Johnson.Desc.First.Walk.Shape
open Johnson.Desc.First.Walk.Seat (fvsOf pubOf)
open H2K5.Honest (valsTS)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)
open ProofFile.Honest (Shape Carries Returns)

/-! ## 1 Rounds that fit pay the test -/

/-- **On rounds that fit K1's declared rounds the named test on the seeds' factors accepts.** -/
theorem seedsV_of_fit (P : VerifiableInference.Desc.K1.Par) {rs : List Fmt.RoundView}
    (h : roundsFit (VerifiableInference.Desc.K1.rounds P) rs = true) :
    seedsV P (rs.map noDigest) = true := by
  obtain ⟨r₁, r₂, rfl, -, -⟩ := k1_fit h
  show ((VerifiableInference.Desc.K1.seedsOf P (noDigest r₁)).all fun y => !isZeroE y.2) = true
  rw [List.all_eq_true]
  intro y hy
  rw [Bool.not_eq_true']
  exact Johnson.Prover.Send.factors_of_fit P r₁ r₂ h y hy

/-! ## 2 The test is struck -/

variable {Cl : Type} {bs : List (Block S Cl)} {ft n : Nat} {b : Block S Cl}
  {P : VerifiableInference.Desc.K1.Par} {g : Nat → ShA → Except String ShA}
  {vals₀ vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool}

/-- "Returns" under seedsV and a further test gives "Returns" under the further test alone. -/
theorem returns_strike (q : bs[n]? = some b)
    (hrd : b.rounds = VerifiableInference.Desc.K1.rounds P)
    (V : S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
    (h0 : ∀ s rs gs, vals₀ n s rs gs = (seedsV P rs && V s rs gs))
    (h1 : ∀ s rs gs, vals n s rs gs = V s rs gs) (hR : Returns bs ft (firstZA g vals₀) n) :
    Returns bs ft (firstZA g vals) n := by
  intro blk hb s rs cols t hg hF hv
  obtain rfl : b = blk := Option.some.inj (q.symm.trans hb)
  refine hR b hb s rs cols t hg hF ?_
  show vals₀ n s (rs.map noDigest) (b.shown ft rs cols) = true
  have hv' : vals n s (rs.map noDigest) (b.shown ft rs cols) = true := hv
  rw [h0, seedsV_of_fit P (hrd ▸ hF.1), ← h1, hv']
  rfl

/-- "Returns" under seedsV alone gives "Returns" under whatever tests. -/
theorem returns_strike_all (q : bs[n]? = some b)
    (hrd : b.rounds = VerifiableInference.Desc.K1.rounds P)
    (h0 : ∀ s rs gs, vals₀ n s rs gs = seedsV P rs) (hR : Returns bs ft (firstZA g vals₀) n) :
    Returns bs ft (firstZA g vals) n := by
  intro blk hb s rs cols t hg hF _
  obtain rfl : b = blk := Option.some.inj (q.symm.trans hb)
  refine hR b hb s rs cols t hg hF ?_
  show vals₀ n s (rs.map noDigest) (b.shown ft rs cols) = true
  rw [h0]
  exact seedsV_of_fit P (hrd ▸ hF.1)

/-! ## 3 The six frames without the test -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Member 2** (the first segment's opening): for every vals. -/
theorem opening_frame_free (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ (Bs : ProofFile.PureBase), ∃ X hp P,
      (cF.blocksInOrder[2]?).isSome = true ∧
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      Zp.p.built.links[0]? = some X ∧ Zp.p.X.G[X.g]? = some hp ∧
      P = ⟨pubOf X, 0, Zp.p.X.layers.y.h.p4, X.g, hp.Tp, hp.Fp, hp.ns, hp.tl⟩ ∧
      ∀ (ft : Nat) g vals,
        g 2 = openingA (VerifiableInference.Desc.K1.firstPar Bs.G₀.first
          (VerifiableInference.Desc.K1.gpOf Zp))
          (openZeroG P (fvsOf Zp.p.built.links) Zp.first.lin.kCol) →
        Carries cF.blocksInOrder ft (firstZA g vals) 2 ∧ Returns cF.blocksInOrder ft (firstZA g vals) 2 := by
  obtain ⟨Bs, X, hp, P, i, e1, x1, x3, x4, F⟩ := opening_frame h
  obtain ⟨Bs₁, b, e1', q, hrd, -⟩ := opening_more_at h
  obtain rfl : Bs = Bs₁ := Except.ok.inj (e1.symm.trans e1')
  refine ⟨Bs, X, hp, P, i, e1, x1, x3, x4, fun ft g vals hg => ?_⟩
  obtain ⟨c, w⟩ := F ft g (fun _ _ rs _ => seedsV (VerifiableInference.Desc.K1.firstPar Bs.G₀.first
    (VerifiableInference.Desc.K1.gpOf Zp)) rs) hg (fun _ _ _ => rfl)
  exact ⟨c, returns_strike_all q hrd (fun _ _ _ => rfl) w⟩

/-- **The digits' commitment, at all 25 links**: for every vals. -/
theorem digits_frame_free (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25) :
    ∃ (Bs : ProofFile.PureBase) (Xl : Stages.LinkH) (pr : Nat) (reads digits : Option (List Nat)),
      (cF.blocksInOrder[14 * l + IM.k1Ix l true + 2]?).isSome = true ∧
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      Bs.G₀.built[l]? = some Xl ∧
      VerifiableInference.Desc.K1.linkNumbers Bs.G₀ Xl =
        some (pr, IM.k1Ix l true + 1, reads, digits) ∧
      ∀ (ft : Nat) g vals,
        g (14 * l + IM.k1Ix l true + 2) = digitsA (VerifiableInference.Desc.K1.parLater
          Bs.G₀.first (VerifiableInference.Desc.K1.gpOf Zp) l (IM.k1Ix l true + 1) 2) l digits →
        Carries cF.blocksInOrder ft (firstZA g vals) (14 * l + IM.k1Ix l true + 2) ∧
          Returns cF.blocksInOrder ft (firstZA g vals) (14 * l + IM.k1Ix l true + 2) := by
  obtain ⟨Bs, Xl, pr, reads, digits, i, e1, e2, e3, F⟩ := digits_frame h l hl
  obtain ⟨Bs₁, b, e1', q, hrd, -⟩ := digits_forms_at h l hl
  obtain rfl : Bs = Bs₁ := Except.ok.inj (e1.symm.trans e1')
  refine ⟨Bs, Xl, pr, reads, digits, i, e1, e2, e3, fun ft g vals hg => ?_⟩
  obtain ⟨c, w⟩ := F ft g (fun _ _ rs _ => seedsV (VerifiableInference.Desc.K1.parLater Bs.G₀.first
    (VerifiableInference.Desc.K1.gpOf Zp) l (IM.k1Ix l true + 1) 2) rs) hg (fun _ _ _ => rfl)
  exact ⟨c, returns_strike_all q hrd (fun _ _ _ => rfl) w⟩

/-- **Member 356** (W's sending and the rows behind it): for every vals. -/
theorem sendW_frame_free (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ msg : Array OracleNotice,
      (cF.blocksInOrder[356]?).isSome = true ∧ linMessageW Zp.first.lin = some msg ∧
      ∀ (ft : Nat) g vals,
        g 356 = sendWA (wPar Zp msg) (VerifiableInference.Desc.K13.whereOf Zp) →
        Carries cF.blocksInOrder ft (firstZA g vals) 356 ∧ Returns cF.blocksInOrder ft (firstZA g vals) 356 := by
  obtain ⟨msg, i, hm, F⟩ := sendW_frame h
  obtain ⟨b, msg₁, hm₁, q, hrd⟩ := sendW_rounds_at h
  obtain rfl : msg = msg₁ := Option.some.inj (hm.symm.trans hm₁)
  refine ⟨msg, i, hm, fun ft g vals hg => ?_⟩
  obtain ⟨c, w⟩ := F ft g (fun _ _ rs _ => seedsV (wPar Zp msg) rs) hg (fun _ _ _ => rfl)
  exact ⟨c, returns_strike_all q hrd (fun _ _ _ => rfl) w⟩

/-- **The reads' member of the twelve layers' links**: for every vals. -/
theorem reads_layers_frame_free (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (k : Nat)
    (hk : k < 12) :
    ∃ (Bs : ProofFile.PureBase) (Xl : Stages.LinkH) (pd : Nat) (reads digits : Option (List Nat))
      (hp : Layer.HPlan2),
      (cF.blocksInOrder[14 * (2 * k) + 3 + 2]?).isSome = true ∧
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      Bs.G₀.built[2 * k]? = some Xl ∧
      VerifiableInference.Desc.K1.linkNumbers Bs.G₀ Xl = some (4, pd, reads, digits) ∧
      Bs.G₀.W.G[k]? = some hp ∧
      ∀ (ft : Nat) g vals,
        g (14 * (2 * k) + 3 + 2) = readsA (readsGS (VerifiableInference.Desc.K1.parLater Bs.G₀.first
          (VerifiableInference.Desc.K1.gpOf Zp) (2 * k) 4 1) (2 * k) reads (tailSh hp.tl))
          (VerifiableInference.Desc.K1.parLater Bs.G₀.first
            (VerifiableInference.Desc.K1.gpOf Zp) (2 * k) 4 1) →
        Carries cF.blocksInOrder ft (firstZA g vals) (14 * (2 * k) + 3 + 2) ∧
          Returns cF.blocksInOrder ft (firstZA g vals) (14 * (2 * k) + 3 + 2) := by
  obtain ⟨Bs, Xl, pd, reads, digits, hp, b, e1, e2, e3, e4, q, hrd, hf, hc, hr⟩ :=
    reads_layers_at h k hk
  refine ⟨Bs, Xl, pd, reads, digits, hp, by rw [q]; rfl, e1, e2, e3, e4, fun ft g vals hg => ?_⟩
  obtain ⟨c, w⟩ := reads_frame_of q hrd hf hc (fun _ _ _ => true)
    (fun s r₁ r₂ gs u hu hz hn _ => hr s r₁ r₂ gs u hu hz hn) ft g
    (fun _ _ rs _ => seedsV (VerifiableInference.Desc.K1.parLater Bs.G₀.first
      (VerifiableInference.Desc.K1.gpOf Zp) (2 * k) 4 1) rs && true) hg (fun _ _ _ => rfl)
  exact ⟨c, returns_strike_all q hrd (fun _ _ _ => Bool.and_true _) w⟩

/-- **The reads' member of the twelve attention links**: vals: the one further test alone. -/
theorem reads_att_frame_free (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (k : Nat) (hk : k < 12) :
    ∃ (Bs : ProofFile.PureBase) (Xl : Stages.LinkH) (pd : Nat) (reads digits : Option (List Nat))
      (A : Attention.Plan),
      (cF.blocksInOrder[14 * (2 * k + 1) + 3 + 2]?).isSome = true ∧
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      Bs.G₀.built[2 * k + 1]? = some Xl ∧
      VerifiableInference.Desc.K1.linkNumbers Bs.G₀ Xl = some (4, pd, reads, digits) ∧
      Bs.G₀.W.A[k]? = some A ∧
      ∀ (ft : Nat) g vals,
        g (14 * (2 * k + 1) + 3 + 2) = readsA (readsAttGS (VerifiableInference.Desc.K1.parLater
          Bs.G₀.first (VerifiableInference.Desc.K1.gpOf Zp) (2 * k + 1) 4 1) (2 * k + 1) reads A)
          (VerifiableInference.Desc.K1.parLater Bs.G₀.first
            (VerifiableInference.Desc.K1.gpOf Zp) (2 * k + 1) 4 1) →
        (∀ s rs gs, vals (14 * (2 * k + 1) + 3 + 2) s rs gs =
           midV (VerifiableInference.Desc.K1.parLater Bs.G₀.first
            (VerifiableInference.Desc.K1.gpOf Zp) (2 * k + 1) 4 1) (2 * k + 1) reads (valsTS A)
            s rs gs) →
        Carries cF.blocksInOrder ft (firstZA g vals) (14 * (2 * k + 1) + 3 + 2) ∧
          Returns cF.blocksInOrder ft (firstZA g vals) (14 * (2 * k + 1) + 3 + 2) := by
  obtain ⟨Bs, Xl, pd, reads, digits, A, i, e1, e2, e3, e4, F⟩ := reads_att_frame h k hk
  obtain ⟨Bs₁, Xl₁, pd₁, reads₁, digits₁, A₁, b, e1', -, -, -, q, hrd, -⟩ := reads_att_at h k hk
  obtain rfl : Bs = Bs₁ := Except.ok.inj (e1.symm.trans e1')
  refine ⟨Bs, Xl, pd, reads, digits, A, i, e1, e2, e3, e4, fun ft g vals hg hv => ?_⟩
  obtain ⟨c, w⟩ := F ft g (fun _ s rs gs =>
    seedsV (VerifiableInference.Desc.K1.parLater Bs.G₀.first
      (VerifiableInference.Desc.K1.gpOf Zp) (2 * k + 1) 4 1) rs &&
    midV (VerifiableInference.Desc.K1.parLater Bs.G₀.first
      (VerifiableInference.Desc.K1.gpOf Zp) (2 * k + 1) 4 1) (2 * k + 1) reads (valsTS A) s rs gs)
    hg (fun _ _ _ => rfl)
  exact ⟨c, returns_strike q hrd _ (fun _ _ _ => rfl) hv w⟩

/-- **The reads' member of the head's link**: vals: the one further test alone. -/
theorem reads_head_frame_free (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ (Bs : ProofFile.PureBase) (Xl : Stages.LinkH) (pd : Nat) (reads digits : Option (List Nat)),
      (cF.blocksInOrder[342]?).isSome = true ∧
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      Bs.G₀.built[24]? = some Xl ∧
      VerifiableInference.Desc.K1.linkNumbers Bs.G₀ Xl = some (5, pd, reads, digits) ∧
      ∀ (ft : Nat) g vals,
        g 342 = readsA (readsHeadGS (VerifiableInference.Desc.K1.parLater Bs.G₀.first
          (VerifiableInference.Desc.K1.gpOf Zp) 24 5 1) reads
          ⟨⟨1, some 24, 5, .K1⟩, Bs.G₀.W.hS, Bs.G₀.W.HLy, Bs.G₀.W.H⟩)
          (VerifiableInference.Desc.K1.parLater Bs.G₀.first
            (VerifiableInference.Desc.K1.gpOf Zp) 24 5 1) →
        (∀ s rs gs, vals 342 s rs gs =
           midV (VerifiableInference.Desc.K1.parLater Bs.G₀.first
            (VerifiableInference.Desc.K1.gpOf Zp) 24 5 1) 24 reads
            (fun m => (m.covered Bs.G₀.W.hS.T Bs.G₀.W.hS.V).toOption.isSome) s rs gs) →
        Carries cF.blocksInOrder ft (firstZA g vals) 342 ∧ Returns cF.blocksInOrder ft (firstZA g vals) 342 := by
  obtain ⟨Bs, Xl, pd, reads, digits, i, e1, e2, e3, F⟩ := reads_head_frame h
  obtain ⟨Bs₁, Xl₁, pd₁, reads₁, digits₁, b, e1', -, -, q, hrd, -⟩ := reads_head_at h
  obtain rfl : Bs = Bs₁ := Except.ok.inj (e1.symm.trans e1')
  refine ⟨Bs, Xl, pd, reads, digits, i, e1, e2, e3, fun ft g vals hg hv => ?_⟩
  obtain ⟨c, w⟩ := F ft g (fun _ s rs gs =>
    seedsV (VerifiableInference.Desc.K1.parLater Bs.G₀.first
      (VerifiableInference.Desc.K1.gpOf Zp) 24 5 1) rs &&
    midV (VerifiableInference.Desc.K1.parLater Bs.G₀.first
      (VerifiableInference.Desc.K1.gpOf Zp) 24 5 1) 24 reads
      (fun m => (m.covered Bs.G₀.W.hS.T Bs.G₀.W.hS.V).toOption.isSome) s rs gs)
    hg (fun _ _ _ => rfl)
  exact ⟨c, returns_strike q hrd _ (fun _ _ _ => rfl) hv w⟩

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.seedsV_of_fit
#print axioms Johnson.AtFull.Shape.returns_strike
#print axioms Johnson.AtFull.Shape.returns_strike_all
#print axioms Johnson.AtFull.Shape.opening_frame_free
#print axioms Johnson.AtFull.Shape.digits_frame_free
#print axioms Johnson.AtFull.Shape.sendW_frame_free
#print axioms Johnson.AtFull.Shape.reads_layers_frame_free
#print axioms Johnson.AtFull.Shape.reads_att_frame_free
#print axioms Johnson.AtFull.Shape.reads_head_frame_free
