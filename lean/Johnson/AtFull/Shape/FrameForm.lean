-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/FrameForm.lean: OUR SEATS IN THE FRAME's OWN FORM: from a seat's two laws (on
the member's decision, under the head P5J.AtMgA) to the two premises that the rule for acceptance
asks at a member: Carries and Returns (another house's
Johnson/Desc/ProofFile/Honest/Thread/Shape.lean). THE PATTERN, AND ITS FIRST USE: K1's digits'
commitment at all 25 links. Nothing is evaluated.

  1 `ShA` := ChainF: the chain's shape and the rows' makes: the whole of what the digits' step
    reads and turns; that it is enough for every other member's step is not shown. (The arrays'
    marks are no third part: the ledger's shape sees them.) `shA`: its reader (a state's "whole
    shape" is the pair of the two). `firstZA g vals`: the frame's letters at that reader; the steps
    g and the named tests on values vals stay letters.
  2 **`carries_of_seat`**, **`returns_of_seat`**: from a law on blk.decide s (rs.map noDigest) gs
    AT ROUNDS THAT FIT (roundsFit blk.rounds rs = true) AND AT EVERY gs to Carries | Returns at the
    member (by that house's carries_seat | returns_seat). A member that tests its columns' form
    takes that house's two laws outright.
  3 `digitsA` (the step on ShA: commitGS on the shape, sendForms on the makes),
    `seedsV` (the one named test on values: no seed's factor is 0), **`digits_frame`**: the plan's
    letters tied as in digits_at; then for every ft, g and vals with g ‹the member's number› =
    digitsA … and vals ‹that number› = seedsV …: Carries cF.blocksInOrder ft (firstZA g vals) ‹number› ∧
    Returns cF.blocksInOrder ft (firstZA g vals) ‹number›. That a member stands at that number is its first
    clause.

Limits. TWO PREMISES OF THE RULE AT 25 OF 358 MEMBERS (accepted_of_shape, which asks Carries at
every member): the rule asks them at every member, and more (that the run on shapes returns; the
values; the fits; the first state's shape). g and vals are letters: no table of steps is laid here.
digits_frame's PREMISE ON vals CANNOT BE MET AT THE TABLE THAT TableOfSteps.lean LAYS. That table
has no test at the digits' cell (noVals, true at every list of rounds; seedsV is false at the empty
one). It is served by SeedsFree.lean's digits_frame_free, which calls this law and pays the test by
the rounds' fit. So this law is the pattern, not the table's law. No state is shown at which digitsA
returns. At the format's second hash function. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.FormsAtHead
import Johnson.Desc.ProofFile.Honest.Thread.ShapeJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link KindName roundsFit noDigest)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)
open ProofFile.Honest (Shape Carries Returns carries_seat returns_seat)

/-! ## 1 The letters -/

/-- The chain's shape and the rows' makes. -/
abbrev ShA : Type := ChainF

/-- A state's whole shape. -/
def shA (s : S) : ShA := chainF s

/-- The frame's letters at that reader; the steps and the tests on values are letters. -/
def firstZA (g : Nat → ShA → Except String ShA)
    (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool) : Shape S :=
  ⟨ShA, shA, g, vals⟩

/-! ## 2 From a seat's two laws to the frame's two -/

variable {Cl : Type} {bs : List (Block S Cl)} {ft b : Nat} {blk : Block S Cl}
  {g : Nat → ShA → Except String ShA}
  {vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool}

/-- "Carries", from a law on the member's decision at rounds that fit. -/
theorem carries_of_seat (hb : bs[b]? = some blk)
    (h : ∀ s rs gs t u, roundsFit blk.rounds rs = true →
      blk.decide s (rs.map noDigest) gs = .ok t → g b (shA s) = .ok u → u = shA t) :
    Carries bs ft (firstZA g vals) b :=
  carries_seat hb fun rs _ hF s s' t hd hg => h s rs _ s' t hF.1 hd hg

/-- "Returns", likewise. -/
theorem returns_of_seat (hb : bs[b]? = some blk)
    (h : ∀ s rs gs u, roundsFit blk.rounds rs = true → g b (shA s) = .ok u →
      vals b s (rs.map noDigest) gs = true → ∃ t, blk.decide s (rs.map noDigest) gs = .ok t) :
    Returns bs ft (firstZA g vals) b :=
  returns_seat hb fun rs _ hF s t hg hv => h s rs _ t hF.1 hg hv

/-! ## 3 The digits' commitment, at all 25 links, in the frame's form -/

/-- The step. -/
def digitsA (P : VerifiableInference.Desc.K1.Par) (l : Nat) (digits : Option (List Nat))
    (x : ShA) : Except String ShA :=
  match commitGS P l 2 digits x.1 with
  | some u => .ok (u, sendForms P x.1.core.st.oracles.length x.2)
  | none => .error "the digits' commitment refuses on shapes"

/-- The one named test on values: no seed's factor is 0. -/
def seedsV (P : VerifiableInference.Desc.K1.Par) (rs : List Fmt.RoundView) : Bool :=
  match rs with
  | r₁ :: _ => (VerifiableInference.Desc.K1.seedsOf P r₁).all fun y => !isZeroE y.2
  | [] => false

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The frame's two premises at the digits' commitment, at all 25 links.** -/
theorem digits_frame (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25) :
    ∃ (Bs : ProofFile.PureBase) (Xl : Stages.LinkH) (pr : Nat) (reads digits : Option (List Nat)),
      (cF.blocksInOrder[14 * l + IM.k1Ix l true + 2]?).isSome = true ∧
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      Bs.G₀.built[l]? = some Xl ∧
      VerifiableInference.Desc.K1.linkNumbers Bs.G₀ Xl =
        some (pr, IM.k1Ix l true + 1, reads, digits) ∧
      ∀ (ft : Nat) g vals,
        g (14 * l + IM.k1Ix l true + 2) = digitsA (VerifiableInference.Desc.K1.parLater
          Bs.G₀.first (VerifiableInference.Desc.K1.gpOf Zp) l (IM.k1Ix l true + 1) 2) l digits →
        (∀ s rs gs, vals (14 * l + IM.k1Ix l true + 2) s rs gs =
          seedsV (VerifiableInference.Desc.K1.parLater Bs.G₀.first
            (VerifiableInference.Desc.K1.gpOf Zp) l (IM.k1Ix l true + 1) 2) rs) →
        Carries cF.blocksInOrder ft (firstZA g vals) (14 * l + IM.k1Ix l true + 2) ∧
          Returns cF.blocksInOrder ft (firstZA g vals) (14 * l + IM.k1Ix l true + 2) := by
  obtain ⟨Bs, Xl, pr, reads, digits, b, e1, e2, e3, e4, hc, hr⟩ := digits_at h l hl
  obtain ⟨Bs', b', e1', e4', hrd, hf⟩ := digits_forms_at h l hl
  have eB : Bs' = Bs := by
    rw [e1] at e1'
    exact (Except.ok.inj e1').symm
  subst eB
  have eb : b' = b := by
    rw [e4] at e4'
    exact (Option.some.inj e4').symm
  subst eb
  refine ⟨Bs', Xl, pr, reads, digits, by rw [e4]; rfl, e1, e2, e3,
    fun ft g vals hg hv => ⟨?_, ?_⟩⟩
  · refine carries_of_seat e4 fun s rs gs t u hfit hd hu => ?_
    rw [hg] at hu
    unfold digitsA at hu
    split at hu
    · rename_i w hw
      cases hu
      have := hc s _ gs t w hd hw
      subst this
      show (chainSh t, _) = (chainSh t, formsOf t.st)
      rw [hf s rs gs t hfit hd]
      rfl
    · cases hu
  · refine returns_of_seat e4 fun s rs gs u hfit hu hvv => ?_
    rw [hg] at hu
    rw [hv] at hvv
    rw [hrd] at hfit
    obtain ⟨r₁, r₂, rfl, -, han⟩ := k1_fit hfit
    unfold digitsA at hu
    split at hu
    · rename_i w hw
      refine hr s (noDigest r₁) (noDigest r₂) gs w hw ?_ ?_
      · intro y hy
        have := List.all_eq_true.1 hvv y hy
        simpa using this
      · exact han
    · cases hu

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.carries_of_seat
#print axioms Johnson.AtFull.Shape.returns_of_seat
#print axioms Johnson.AtFull.Shape.digits_frame
#print axioms Johnson.AtFull.Shape.ShA
#print axioms Johnson.AtFull.Shape.shA
#print axioms Johnson.AtFull.Shape.firstZA
#print axioms Johnson.AtFull.Shape.digitsA
#print axioms Johnson.AtFull.Shape.seedsV
