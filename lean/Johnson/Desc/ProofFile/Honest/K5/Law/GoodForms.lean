-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/GoodForms.lean: the texts of two fields of Good
(Honest/Side.lean), exact and fresh, AT ONE MEMBER OF A ROW; and three sentences on the frame's own
parts beside their simulators, in the form in which the row of an attention segment's own rounds
(kind K5) would call them. Definitions of propositions, and one statement with its proof.

  ExactU, FreshU   the two fields' texts at one member u: FreshU with all the field's premises;
                 ExactU without the field's premise on the opened columns, so it is asked at every
                 value of them: each an equation of two distributions on these files' own
                 definitions
  DrawnLike      declared rounds agree with entries in what the frame's test on challenges reads
  OwnsNothing    no entry of the book names the part at an address as owner
  fresh_u        CONDITIONAL: FreshU at every member that owns nothing: by the frame's own lemmas
  MSForm bud      ExactU at the masked sumcheck's part (sumPart,
                 Honest/Sum.lean) beside sumSim: general in the job; under a lift onto Unit; at
                 On := True and the letter bud. No more is asked than a caller at that letter
                 spends; the form at every letter is: for all bud, MSForm bud
  LoneForm bud    the like at scalarsPart beside scalarsSim (Honest/ForKinds.lean)
  QuietForm bud   the like at quietPart beside quietSim

THE THREE ARE PREMISES IN Honest/K5/Law/Good.lean. NONE IS SHOWN IN THIS FILE:
Honest/K5/Law/GoodPaid.lean has each, at every bud, from a theorem on that part. Whoever states and
shows the like of these parts: that form rules, not these.

Limits. No property is claimed by a definition.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Side
import Johnson.Desc.ProofFile.Honest.ForKinds
import Johnson.Desc.ProofFile.Honest.SumLaw.Fits
import Johnson.Desc.ProofFile.Honest.Law.ToyLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes (E)
open VerifiableInference.Desc (Place Oracle)
open VerifiableInference.Desc.Part.MaskedSum (entries shapeOk)
open ProofFile.Honest.SumLaw (StatedBy)

/-! ## 1 The forms: the fields' texts at ONE member -/

section
variable {S Cl V W X Pb : Type}

/-- **Good.exact's text at one member u** (Honest/Side.lean), WITHOUT ITS PREMISE ON THE OPENED
COLUMNS (m.opened = front.opened (readsBefore pre front)); its other premises are kept. So it asks
the same equation at more states than the field does. -/
def ExactU (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (chain firstTree : Nat)
    (On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) (u : Member V W X Pb) : Prop :=
  ∀ ca m front ds asks, On u ca m front → m.seen = front.seen →
    drawsFit (u.rounds.map (·.1)) ds = true → bud u.number ds asks →
    front.holds chain firstTree (u.rounds.map (·.1)) ds = true →
    u.part.stopAt (φ.sees m.st.input) m.loc ds ≠ some .hid →
    (Prob.unif (Cs u.part.takes × CsAll u.part.spends)).map
        (fun c => σ.shows φ u (c.1, c.2, ca) m ds asks) =
      (Prob.unif (Cs u.sim.takes)).map fun c => u.tells φ c m.st.input front ds asks

/-- **Good.fresh's own text at one member u.** -/
def FreshU (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (Bk : ProverCoinCounts) (ord : List Place)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) (u : Member V W X Pb) : Prop :=
  ∀ (p : Addr) sp ca m ds asks,
    drawsFit (u.rounds.map (·.1)) ds = true → bud u.number ds asks →
    u.part.stopAt (φ.sees m.st.input) m.loc ds ≠ some .hid →
    (Prob.unif (Cs u.part.takes)).map (fun c =>
        (cutAll c (Bk.spentBy ⟨σ.block.place, u.number⟩ p), σ.shows φ u (c, sp, ca) m ds asks,
          cutAll c (Bk.knownBy ord ⟨σ.block.place, u.number⟩ p))) =
      (Prob.unif (CsAll ((Bk.spentBy ⟨σ.block.place, u.number⟩ p).map Ahead.named) ×
          Cs u.part.takes)).map fun a =>
        (some a.1, σ.shows φ u (a.2, sp, ca) m ds asks,
          cutAll a.2 (Bk.knownBy ord ⟨σ.block.place, u.number⟩ p))

/-- The declared rounds agree with entries in what the frame's test on challenges reads. The range
of positions (logN) is left out: that test reads it of drawn positions alone, and the entries that
are laid here draw none. -/
def DrawnLike (es : List Fmt.Entry) (rs : List (Fmt.DeclaredRound × List Oracle)) : Prop :=
  rs.map (fun r => (r.1.entry.name, r.1.entry.drawE, r.1.entry.drawNZ, r.1.entry.poss,
      r.1.entry.trits)) =
    es.map fun e => (e.name, e.drawE, e.drawNZ, e.poss, e.trits)

/-- No entry of the book names the part at a as owner. -/
def OwnsNothing (Bk : ProverCoinCounts) (a : Addr) : Prop := ∀ e ∈ Bk.ahead, e.owner ≠ a

/-- **Good.fresh's text holds at every member that owns nothing**: by the frame's own two lemmas
(spentBy_nil, fresh_of_nil, Honest/Law/ToyLaw.lean): where the list of spent runs is empty the two
laws are one law. General in the side, the member and the letter bud. CONDITIONAL on OwnsNothing. -/
theorem fresh_u (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (Bk : ProverCoinCounts) (ord : List Place)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) (u : Member V W X Pb)
    (h : OwnsNothing Bk ⟨σ.block.place, u.number⟩) : FreshU φ σ Bk ord bud u :=
  fun p sp ca m ds asks _ _ _ =>
    fresh_of_nil (Bk.spentBy ⟨σ.block.place, u.number⟩ p)
      (spentBy_nil Bk _ p fun e he _ ho => absurd ho (h e he))
      (fun c => σ.shows φ u (c, sp, ca) m ds asks)
      fun c => cutAll c (Bk.knownBy ord ⟨σ.block.place, u.number⟩ p)

end

/-! ## 2 Three general sentences, in the form in which K5's row would call them: premises -/

/-- The masked sumcheck's part beside its simulator: general in the job, under a lift onto Unit; at
On := True and at the letter bud that is handed in. It is general in the variables' sorts; K5's
calls have no variable that is summed at a point but the last. A FORM: A PREMISE IN
Honest/K5/Law/Good.lean; NOT SHOWN IN THIS FILE (msForm_paid, Honest/K5/Law/GoodPaid.lean). -/
def MSForm (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) : Prop :=
  ∀ (S Cl V W X Pb V' W' : Type) (φ : Face V W Pb) (σ : Side S Cl V W X Pb)
    (chain firstTree : Nat) (see : V → V') (wit : W → W')
    (name endName : String) (J : SumJob W' Unit) (j : Nat)
    (rs : List (Fmt.DeclaredRound × List Oracle)), shapeOk J.shape = true →
    StatedBy (scalarsOf J.shape) rs → DrawnLike (entries J.shape) rs →
    ExactU φ σ chain firstTree (fun _ _ _ _ => True) bud ⟨j, rs,
        (sumPart (V := V') name endName J).lift see wit (fun _ => ()) fun x _ => x,
        sumSim ⟨σ.block.place, j⟩ J.shape⟩

/-- One round that sends n scalars, each as its value plus a mask entry. A FORM: A PREMISE IN
Honest/K5/Law/Good.lean; NOT SHOWN IN THIS FILE (loneForm_paid, Honest/K5/Law/GoodPaid.lean). -/
def LoneForm (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) : Prop :=
  ∀ (S Cl V W X Pb V' W' : Type) (φ : Face V W Pb) (σ : Side S Cl V W X Pb)
    (chain firstTree : Nat) (see : V → V') (wit : W → W')
    (name : String) (n : Nat) (vals : W' → Front Unit → List E) (j : Nat)
    (rs : List (Fmt.DeclaredRound × List Oracle)), StatedBy [n] rs →
    ExactU φ σ chain firstTree (fun _ _ _ _ => True) bud ⟨j, rs,
        (scalarsPart (V := V') name n vals).lift see wit (fun _ => ()) fun x _ => x,
        scalarsSim ⟨σ.block.place, j⟩ n⟩

/-- The round that sends nothing. A FORM: A PREMISE IN Honest/K5/Law/Good.lean; NOT SHOWN IN THIS
FILE (quietForm_paid, Honest/K5/Law/GoodPaid.lean). -/
def QuietForm (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) : Prop :=
  ∀ (S Cl V W X Pb V' W' : Type) (φ : Face V W Pb) (σ : Side S Cl V W X Pb)
    (chain firstTree : Nat) (see : V → V') (wit : W → W')
    (j : Nat) (rs : List (Fmt.DeclaredRound × List Oracle)), StatedBy [0] rs →
    ExactU φ σ chain firstTree (fun _ _ _ _ => True) bud ⟨j, rs,
        (quietPart (V := V') (W := W') (X := Unit)).lift see wit (fun _ => ()) fun x _ => x,
        quietSim ⟨σ.block.place, j⟩⟩

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.fresh_u
