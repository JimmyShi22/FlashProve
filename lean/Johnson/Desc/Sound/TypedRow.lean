-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/TypedRow.lean: FROM A ROW OF PROVED TYPED BLOCKS TO THE PREMISE OF THE RULE OF
COMPOSITION: what has to be shown of a block of the description so that a proved typed block's
soundness is the block's own.

The setting. The rule of composition (Johnson/Desc/Sound/ChainRule.lean) asks of every block of a
chain that it be good between the conditions and relations at its two boundaries (`EachGood`); these
are parameters. The library has typed blocks between typed joints (`KObj.BK`, `KObj.JK`,
Johnson/E/KObj/Blocks.lean) that are proved good. Here the conditions and relations at the chain's
boundaries are WRITTEN as the typed joints', read along a reading of the statements and of the
witnesses; and what is left to be shown of a block speaks of the two verifiers, of the extractor's
bookkeeping and of the counts alone.

What is said.
  `PieceTie p k rdA rdB wA wB`: the tie of a block with its stretch p to a typed block k. There is a
    reading G of the block's rounds as k's rounds such that: (fits) the block's errors bear k's
    along G; (yes) at every statement whose reading has the typed condition and AT EVERY TRANSCRIPT:
    where the block says yes, the transcript has an image, THE TYPED VERIFIER PUTS OUT AT THAT
    IMAGE, AND WHAT IT PUTS OUT IS THE READING OF THE STATEMENT BEHIND THE BLOCK (an equation, not
    only a yes); and the block's extractor does at the witness what k's extractor does.
  `goodOfTie`: a tied block is good between the typed joints' conditions and relations, read.
  `EachTie`, `eachGoodOfTies`: the same along a row, for a family of joints and typed blocks.
  `PieceTieW`, `tieOfTieW`: THE FORM IN WHICH A KIND'S LAW IS MEANT: the tie asked only where every
    word shown is below the prime; it is the tie of the piece that holds `below b`.
Trials. `tie_trial_yes`: a block that says yes at a statement and a transcript where the typed
  verifier refuses every transcript has no tie. `tie_trial_other`: nor has a block that says yes and
  leaves another statement than the typed verifier's. A block that refuses all has a tie wherever a
  reading with `fits` exists (`tie_trial_no`): a verifier that never accepts is sound.

Limits. A rule. No block of the protocol is tied here. The witness's type W, its readings and the
pieces' extractors are parameters: whoever fills the chain lays them (a product over the boundaries,
each extractor writing its own coordinate, meets the clause on extractors). Nothing on acceptance.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.ChainRuleProofs
import Johnson.Desc.Sound.FoldBelowProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString)
open _root_.Iop.Reduction (orOff)

variable {S Cl W : Type} {C : CK} {F : Frame}

/-- **The tie of a block of the description, with its stretch, to a typed block.** rdA, rdB: how the
statements in front of and behind the block are read as the typed block's; wA, wB: how the chain's
witness is read as a witness at the two typed joints. -/
def PieceTie (p : Piece C F S Cl W) {A B : JK} (k : BK A B)
    (rdA : S × F.E.Str → A.X × A.E.Str) (rdB : S × F.E.Str → B.X × B.E.Str)
    (wA : W → A.W) (wB : W → B.W) : Prop :=
  ∃ G : S × F.E.Str → CarryS (uLT C p.ds) k.R.red.shape,
    (∀ a, (G a).Fits k.err p.err) ∧
    ∀ a τ a', A.on (rdA a) → p.ior.red.out a τ = some a' →
      ∃ τ', (G a).tr τ = some τ' ∧ k.R.red.out (rdA a) τ' = some (rdB a') ∧
        ∀ w, wA (p.ext a τ w) = k.ext (rdA a) τ' (wB w)

/-- **A tied block is good** between the typed joints' conditions and relations, read along the
readings. -/
theorem goodOfTie (p : Piece C F S Cl W) {A B : JK} (k : BK A B)
    (rdA : S × F.E.Str → A.X × A.E.Str) (rdB : S × F.E.Str → B.X × B.E.Str)
    (wA : W → A.W) (wB : W → B.W) (hk : k.Good) (ht : PieceTie p k rdA rdB wA wB) :
    (p.bk (fun a => A.on (rdA a)) (fun a => B.on (rdB a)) (fun a w => A.relR (rdA a) (wA w))
      (fun a w => B.relR (rdB a) (wB w))).Good := by
  obtain ⟨G, hfit, hyes⟩ := ht
  refine ⟨⟨pointsT C p.ds⟩, stageIOR_isLocal C p.stage p.run, ?_⟩
  exact pieceOfProved S Cl W C F p (A.X × A.E.Str) (B.X × B.E.Str) A.W B.W k.R.red G k.err rdA
    (fun a => A.on (rdA a)) A.on (fun a w => A.relR (rdA a) (wA w))
    (orOff (fun a => B.on (rdB a)) (fun a w => B.relR (rdB a) (wB w))) A.relR
    (orOff B.on B.relR) k.ext hfit (fun _ h => h)
    (fun a τ a' w ha ho hw => by
      obtain ⟨τ', h1, h2, h3⟩ := hyes a τ a' ha ho
      refine ⟨τ', rdB a', wB w, h1, h2, hw, fun h => ?_⟩
      show A.relR (rdA a) (wA (p.ext a τ w))
      rw [h3 w]
      exact h)
    hk.know

/-- The tie along a row: boundary i has the typed joint J i; the i-th block is tied to k i. -/
def EachTie (J : ℕ → JK) (k : ∀ i, BK (J i) (J (i + 1)))
    (rd : ∀ i, S × F.E.Str → (J i).X × (J i).E.Str) (wr : ∀ i, W → (J i).W) :
    ℕ → List (Piece C F S Cl W) → Prop
  | _, [] => True
  | i, p :: l =>
    PieceTie p (k i) (rd i) (rd (i + 1)) (wr i) (wr (i + 1)) ∧ EachTie J k rd wr (i + 1) l

/-- **A row of tied blocks meets the premise of the rule of composition**, at the typed joints'
conditions and relations, read. -/
theorem eachGoodOfTies (J : ℕ → JK) (k : ∀ i, BK (J i) (J (i + 1)))
    (rd : ∀ i, S × F.E.Str → (J i).X × (J i).E.Str) (wr : ∀ i, W → (J i).W)
    (hk : ∀ i, (k i).Good) : ∀ (l : List (Piece C F S Cl W)) (i : ℕ), EachTie J k rd wr i l →
    EachGood (fun i a => (J i).on (rd i a)) (fun i a w => (J i).relR (rd i a) (wr i w)) i l
  | [], _, _ => trivial
  | p :: l, i, h =>
    ⟨goodOfTie p (k i) (rd i) (rd (i + 1)) (wr i) (wr (i + 1)) (hk i) h.1,
      eachGoodOfTies J k rd wr hk l (i + 1) h.2⟩

/-! ## The test that every word is below the prime -/

/-- The piece that holds the block `below b` (Johnson/Desc/Sound/ChainRule.lean: b behind the test
that every word which is shown as part of a field's element is below the prime) in b's place: the
same stretch, extractor and errors. By `FoldBelow` the fold of such blocks is the decision that
runs: the test on all that is shown, once, then the fold. -/
def Piece.below (p : Piece C F S Cl W) : Piece C F S Cl W :=
  ⟨Sound.below p.b, p.base, p.ds, p.back, p.ext, p.err⟩

/-- What it decides: the test, then b's decision. -/
theorem Piece.below_run (p : Piece C F S Cl W) (hb : viewWordsBelowPrime ⟨p.back, []⟩ = true) :
    p.below.run = fun s v => if viewWordsBelowPrime v then p.run s v else none :=
  foldBelow S Cl F p.b.name [p.b] p.back hb

/-- Where it says yes, the words shown are below the prime and b says the same yes. -/
theorem Piece.below_out (p : Piece C F S Cl W) (hb : viewWordsBelowPrime ⟨p.back, []⟩ = true)
    (a a' : S × F.E.Str) (τ : Iop.Tr (uLT C p.ds)) (h : p.below.ior.red.out a τ = some a') :
    viewWordsBelowPrime (sView C p.stage a.2 τ) = true ∧ p.ior.red.out a τ = some a' := by
  have h' : ((if sTests C p.stage a.2 τ then p.below.run a.1 (sView C p.stage a.2 τ) else none).map
      fun xo => (xo, p.ior.imp a.2 τ)) = some a' := h
  rw [p.below_run hb] at h'
  by_cases h1 : viewWordsBelowPrime (sView C p.stage a.2 τ) = true
  · refine ⟨h1, ?_⟩
    simp only [h1, if_true] at h'
    exact h'
  · by_cases h2 : sTests C p.stage a.2 τ = true
    · simp [h1, h2] at h'
    · simp [h2] at h'

/-- **The tie, asked only where every word shown is below the prime.** As `PieceTie`, with that
hypothesis on what the verifier is shown of the stretch. -/
def PieceTieW (p : Piece C F S Cl W) {A B : JK} (k : BK A B)
    (rdA : S × F.E.Str → A.X × A.E.Str) (rdB : S × F.E.Str → B.X × B.E.Str)
    (wA : W → A.W) (wB : W → B.W) : Prop :=
  ∃ G : S × F.E.Str → CarryS (uLT C p.ds) k.R.red.shape,
    (∀ a, (G a).Fits k.err p.err) ∧
    ∀ a τ a', A.on (rdA a) → viewWordsBelowPrime (sView C p.stage a.2 τ) = true →
      p.ior.red.out a τ = some a' →
      ∃ τ', (G a).tr τ = some τ' ∧ k.R.red.out (rdA a) τ' = some (rdB a') ∧
        ∀ w, wA (p.ext a τ w) = k.ext (rdA a) τ' (wB w)

/-- It is the tie of the piece that holds `below b`. -/
theorem tieOfTieW (p : Piece C F S Cl W) {A B : JK} (k : BK A B)
    (rdA : S × F.E.Str → A.X × A.E.Str) (rdB : S × F.E.Str → B.X × B.E.Str)
    (wA : W → A.W) (wB : W → B.W) (hb : viewWordsBelowPrime ⟨p.back, []⟩ = true)
    (h : PieceTieW p k rdA rdB wA wB) : PieceTie p.below k rdA rdB wA wB := by
  obtain ⟨G, hfit, hyes⟩ := h
  refine ⟨G, hfit, fun a τ a' ha ho => ?_⟩
  obtain ⟨h1, h2⟩ := p.below_out hb a a' τ ho
  exact hyes a τ a' ha h1 h2

/-! ## Trials -/

/-- A CHECK. A block that says yes where the typed verifier refuses every transcript has no tie. -/
theorem tie_trial_yes (p : Piece C F S Cl W) {A B : JK} (k : BK A B)
    (rdA : S × F.E.Str → A.X × A.E.Str) (rdB : S × F.E.Str → B.X × B.E.Str)
    (wA : W → A.W) (wB : W → B.W) (a a' : S × F.E.Str) (τ : Iop.Tr (uLT C p.ds))
    (ha : A.on (rdA a)) (hyes : p.ior.red.out a τ = some a')
    (hno : ∀ τ', k.R.red.out (rdA a) τ' = none) : ¬ PieceTie p k rdA rdB wA wB := by
  rintro ⟨G, -, h⟩
  obtain ⟨τ', -, h2, -⟩ := h a τ a' ha hyes
  rw [hno τ'] at h2
  cases h2

/-- A CHECK. Nor has a block that says yes and leaves a statement whose reading the typed verifier
puts out at no transcript. -/
theorem tie_trial_other (p : Piece C F S Cl W) {A B : JK} (k : BK A B)
    (rdA : S × F.E.Str → A.X × A.E.Str) (rdB : S × F.E.Str → B.X × B.E.Str)
    (wA : W → A.W) (wB : W → B.W) (a a' : S × F.E.Str) (τ : Iop.Tr (uLT C p.ds))
    (ha : A.on (rdA a)) (hyes : p.ior.red.out a τ = some a')
    (hother : ∀ τ', k.R.red.out (rdA a) τ' ≠ some (rdB a')) : ¬ PieceTie p k rdA rdB wA wB := by
  rintro ⟨G, -, h⟩
  obtain ⟨τ', -, h2, -⟩ := h a τ a' ha hyes
  exact hother τ' h2

/-- A CHECK. A block that refuses all has a tie wherever a reading of its rounds exists along which
its errors bear the typed block's. -/
theorem tie_trial_no (p : Piece C F S Cl W) {A B : JK} (k : BK A B)
    (rdA : S × F.E.Str → A.X × A.E.Str) (rdB : S × F.E.Str → B.X × B.E.Str)
    (wA : W → A.W) (wB : W → B.W) (G : S × F.E.Str → CarryS (uLT C p.ds) k.R.red.shape)
    (hfit : ∀ a, (G a).Fits k.err p.err) (hno : ∀ a τ, p.ior.red.out a τ = none) :
    PieceTie p k rdA rdB wA wB :=
  ⟨G, hfit, fun a τ a' _ h => by
    rw [hno a τ] at h
    cases h⟩

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.goodOfTie
#print axioms VerifiableInference.Desc.Sound.eachGoodOfTies
#print axioms VerifiableInference.Desc.Sound.tieOfTieW
#print axioms VerifiableInference.Desc.Sound.tie_trial_yes
#print axioms VerifiableInference.Desc.Sound.tie_trial_other
#print axioms VerifiableInference.Desc.Sound.tie_trial_no
