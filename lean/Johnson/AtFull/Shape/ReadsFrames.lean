-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/ReadsFrames.lean: THE 25 MEMBERS «K1's COMMITMENT TO THE READS WITH THE QUIET
STEP BEHIND IT» OF THE PROOF FILE's OWN FIRST CHAIN IN THE FORM THAT THE THREAD's FRAME ASKS
(ProofFile.Honest.Carries | Returns at firstZA g vals, Johnson/AtFull/Shape/FrameForm.lean). Under the
head P5J.AtMgA; a joining of laws; nothing is evaluated.
  `readsA G P`: a reads' member's step on the whole: G on the chain's shape; the makes of the rows
    that the commitment lays (sendForms P). `midV P link arrays v`: a test at the state behind the
    commitment, as a test with code on the state in front, the rounds and what is shown: it runs the
    commitment's own decision.
  **`reads_frame_of`**: from a reads' seat's four clauses (the declared rounds; the makes behind a
    yes on two rounds; carries; returns under a further test V) to Carries and Returns, at g n =
    readsA G P and vals n s rs gs = (seedsV P rs && V s rs gs).
  **`reads_layers_frame`** (k < 12; number 14 (2 k) + 5; V: none) · **`reads_att_frame`** (k < 12;
    number 14 (2 k + 1) + 5; V := midV … (valsTS A), another house's test on values) ·
    **`reads_head_frame`** (number 342; V := midV … «the covered positions can be said»). Each names
    its parameters by the same equations as its seat.
By reads_layers_at | reads_att_at | reads_head_at (their files), carries_of_seat | returns_of_seat |
seedsV (FrameForm.lean), k1_fit (FormsAtHead.lean).
Limits. The steps g and the tests vals are letters with an equation at one number each: no table of
all 358 is built here. "Carries" is under the step's own return. seedsV IS A TEST ON VALUES IN A
ROUND (no seed's factor is 0); midV RUNS THE COMMITMENT's DECISION ON THE STATE: it reads the state
beyond its shape, AND IT SAYS NO WHERE THAT DECISION REFUSES. The seat's own premise reads "at every
m that the commitment returns …" and asks nothing at a refusal. So at the attention links' members
and at 342, where midV stands, the test on values asks more than the seat does: whoever pays the
values there owes the commitment's yes. At the attention links tabsGC is enough, not shown to be
needed. UNDER THE HEAD: that it has a member is shown in scope, where the reader returns and
`protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold together, at
two named sets of public files (`VerifierAndGoals.storedPublicFiles` and `VerifierAndGoals.zGap`), in a side library
(AtFullSide/Top/HeadMemberAtFull.lean, HeadMemberAtGap.lean). No state is shown by a theorem at
which a step returns. At the earlier hash OnBytes.secondHashFunction. Nothing on soundness, completeness or
hiding.
Terms: lean/GLOSSARY.md.
-/
import Johnson.AtFull.Shape.FrameOpt
import Johnson.AtFull.Shape.ReadsLayersAtHead
import Johnson.AtFull.Shape.ReadsAttAtHead
import Johnson.AtFull.Shape.ReadsHeadAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link KindName roundsFit noDigest K1.commitAtS)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open H2K5.Honest (valsTS)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)
open ProofFile.Honest (Shape Carries Returns carries_seat returns_seat)

/-- A reads' member's step on the whole: G on the chain's shape; the makes of the rows that the
commitment lays (sendForms, Johnson/Desc/First/Shape/SendForms.lean). -/
def readsA (G : ChainSh → Option ChainSh) (P : VerifiableInference.Desc.K1.Par) (x : ShA) :
    Except String ShA :=
  match G x.1 with
  | some u => .ok (u, sendForms P x.1.core.st.oracles.length x.2)
  | none => .error "the reads' member refuses on shapes"

/-- A test at the state behind the commitment, as a test with code on the state in front, the rounds
and what is shown. WHERE THE COMMITMENT's DECISION REFUSES IT SAYS NO. The 1 is the reads' moment,
typed into this text. -/
def midV (P : VerifiableInference.Desc.K1.Par) (link : Nat) (arrays : Option (List Nat))
    (v : S → Bool) (s : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) : Bool :=
  match (K1.commitAtS (Cl := Unit) P link 1 arrays).decide s rs
      (gs.take (K1.commitAtS (Cl := Unit) P link 1 arrays).openings) with
  | .ok m => v m
  | .error _ => false

variable {Cl : Type} {bs : List (Block S Cl)} {n : Nat} {b : Block S Cl}
  {P : VerifiableInference.Desc.K1.Par} {G : ChainSh → Option ChainSh}

/-- **From a reads' seat's four clauses to the frame's two premises.** V: the further test on values
(at the layers' links: none). -/
theorem reads_frame_of (q : bs[n]? = some b)
    (hrd : b.rounds = VerifiableInference.Desc.K1.rounds P)
    (hf : ∀ s r₁ r₂ gs t, b.decide s [r₁, r₂] gs = .ok t →
      formsOf t.st = sendForms P (chainSh s).core.st.oracles.length (formsOf s.st))
    (hc : ∀ s rs gs t u, b.decide s rs gs = .ok t → G (chainSh s) = some u → u = chainSh t)
    (V : S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
    (hr : ∀ s r₁ r₂ gs u, G (chainSh s) = some u →
      (∀ y ∈ VerifiableInference.Desc.K1.seedsOf P r₁, isZeroE y.2 = false) →
      (VerifiableInference.Desc.K1.answersIn r₂).length = P.answers →
      V s [r₁, r₂] gs = true → ∃ t, b.decide s [r₁, r₂] gs = .ok t)
    (ft : Nat) (g : Nat → ShA → Except String ShA)
    (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
    (hg : g n = readsA G P) (hv : ∀ s rs gs, vals n s rs gs = (seedsV P rs && V s rs gs)) :
    Carries bs ft (firstZA g vals) n ∧ Returns bs ft (firstZA g vals) n := by
  refine ⟨?_, ?_⟩
  · refine carries_of_seat q fun s rs gs t u hfit hd hu => ?_
    rw [hg] at hu
    rw [hrd] at hfit
    obtain ⟨r₁, r₂, rfl, -, -⟩ := k1_fit hfit
    unfold readsA at hu
    split at hu
    · rename_i w hw
      cases hu
      have := hc s _ gs t w hd hw
      subst this
      show (chainSh t, _) = (chainSh t, formsOf t.st)
      rw [hf s (noDigest r₁) (noDigest r₂) gs t hd]
      rfl
    · cases hu
  · refine returns_of_seat q fun s rs gs u hfit hu hvv => ?_
    rw [hg] at hu
    rw [hv, Bool.and_eq_true] at hvv
    rw [hrd] at hfit
    obtain ⟨r₁, r₂, rfl, -, han⟩ := k1_fit hfit
    unfold readsA at hu
    split at hu
    · rename_i w hw
      refine hr s (noDigest r₁) (noDigest r₂) gs w hw ?_ han hvv.2
      intro y hy
      have := List.all_eq_true.1 hvv.1 y hy
      simpa using this
    · cases hu

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The frame's two premises at the reads' member of the twelve layers' links.** -/
theorem reads_layers_frame (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (k : Nat) (hk : k < 12) :
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
        (∀ s rs gs, vals (14 * (2 * k) + 3 + 2) s rs gs =
          (seedsV (VerifiableInference.Desc.K1.parLater Bs.G₀.first
            (VerifiableInference.Desc.K1.gpOf Zp) (2 * k) 4 1) rs && true)) →
        Carries cF.blocksInOrder ft (firstZA g vals) (14 * (2 * k) + 3 + 2) ∧
          Returns cF.blocksInOrder ft (firstZA g vals) (14 * (2 * k) + 3 + 2) := by
  obtain ⟨Bs, Xl, pd, reads, digits, hp, b, e1, e2, e3, e4, q, hrd, hf, hc, hr⟩ :=
    reads_layers_at h k hk
  refine ⟨Bs, Xl, pd, reads, digits, hp, by rw [q]; rfl, e1, e2, e3, e4, fun ft g vals hg hv => ?_⟩
  exact reads_frame_of q hrd hf hc (fun _ _ _ => true)
    (fun s r₁ r₂ gs u hu hz hn _ => hr s r₁ r₂ gs u hu hz hn) ft g vals hg hv

/-- **The frame's two premises at the reads' member of the twelve attention links.** -/
theorem reads_att_frame (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (k : Nat) (hk : k < 12) :
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
          (seedsV (VerifiableInference.Desc.K1.parLater Bs.G₀.first
            (VerifiableInference.Desc.K1.gpOf Zp) (2 * k + 1) 4 1) rs &&
           midV (VerifiableInference.Desc.K1.parLater Bs.G₀.first
            (VerifiableInference.Desc.K1.gpOf Zp) (2 * k + 1) 4 1) (2 * k + 1) reads (valsTS A)
            s rs gs)) →
        Carries cF.blocksInOrder ft (firstZA g vals) (14 * (2 * k + 1) + 3 + 2) ∧
          Returns cF.blocksInOrder ft (firstZA g vals) (14 * (2 * k + 1) + 3 + 2) := by
  obtain ⟨Bs, Xl, pd, reads, digits, A, b, e1, e2, e3, e4, q, hrd, hf, hc, hr⟩ :=
    reads_att_at h k hk
  refine ⟨Bs, Xl, pd, reads, digits, A, by rw [q]; rfl, e1, e2, e3, e4, fun ft g vals hg hv => ?_⟩
  refine reads_frame_of q hrd hf hc _ (fun s r₁ r₂ gs u hu hz hn hV => ?_) ft g vals hg hv
  refine hr s r₁ r₂ gs u hu hz hn fun m hm => ?_
  unfold midV at hV
  rw [hm] at hV
  exact hV

/-- **The frame's two premises at the reads' member of the head's link.** -/
theorem reads_head_frame (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
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
          (seedsV (VerifiableInference.Desc.K1.parLater Bs.G₀.first
            (VerifiableInference.Desc.K1.gpOf Zp) 24 5 1) rs &&
           midV (VerifiableInference.Desc.K1.parLater Bs.G₀.first
            (VerifiableInference.Desc.K1.gpOf Zp) 24 5 1) 24 reads
            (fun m => (m.covered Bs.G₀.W.hS.T Bs.G₀.W.hS.V).toOption.isSome) s rs gs)) →
        Carries cF.blocksInOrder ft (firstZA g vals) 342 ∧ Returns cF.blocksInOrder ft (firstZA g vals) 342 := by
  obtain ⟨Bs, Xl, pd, reads, digits, b, e1, e2, e3, q, hrd, hf, hc, hr⟩ := reads_head_at h
  refine ⟨Bs, Xl, pd, reads, digits, by rw [q]; rfl, e1, e2, e3, fun ft g vals hg hv => ?_⟩
  refine reads_frame_of q hrd hf hc _ (fun s r₁ r₂ gs u hu hz hn hV => ?_) ft g vals hg hv
  refine hr s r₁ r₂ gs u hu hz hn fun m hm => ?_
  unfold midV at hV
  rw [hm] at hV
  exact hV

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.reads_frame_of
#print axioms Johnson.AtFull.Shape.reads_layers_frame
#print axioms Johnson.AtFull.Shape.reads_att_frame
#print axioms Johnson.AtFull.Shape.reads_head_frame
#print axioms Johnson.AtFull.Shape.readsA
#print axioms Johnson.AtFull.Shape.midV
