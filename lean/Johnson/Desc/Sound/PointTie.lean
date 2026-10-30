-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/PointTie.lean: "LIN point", THE ONE BLOCK OF THE SHARED CHAIN AT WHICH A SLOT's OWN ENTERS: ITS DEBT IN THE PLAIN FORM FOR A BATCH (LeadsBN, Johnson/Desc/Plain/Both.lean), AT THE TABLE's OWN TERMS, BROUGHT DOWN
TO NAMED STEPS, EACH WITH ITS PAYER. Definitions, three small lemmas on the table, one of plain logic, three statements written as def … : Prop, and their proofs. ((S4)'s binder takes "no mark behind the block": a premise's premise: each statement says more for it.) (PointYes: the step at one yes in the shape in which K14's files hold their law: two sorts
of lost points apart.)

In front of the block (border 1) are open: own: no mark, the index masks' pin, W's pin, THE CLAIM ON M; shared: the cells' pin. Behind it (border 2): own: no mark, the two pins, (Eval), (Dot); shared: omU, nearU, recRow.
  stepPt E a b: THE RELATION THAT IS OWED (the row shared_joint_count's stepAt … 1, unfolded): the table's promise at border 2 holds of b, and for every witness w: all that is open at border 2 holds of (b, w) gives: all that is
    open at border 1 holds of (a, E a w). E: the table's extractor at this block: it lays the cells.
  PointStep: THE STEP WITHOUT CHANCE, AT ONE YES (a, b): from
    (S0) the promise behind;
    (S23) AT THIS YES's CHALLENGE, WHICH IS NOT BAD: nearU, recRow, omU, (Dot) and W's pin give WIs ("W's message is the row weights applied to what the table decodes to"): a letter that stands under "for all", opened and
          closed inside this block: no item of the table. [K14's files: (Dot) with omU is their DotU, without chance; then their law of a yes off the two bad sets];
    (S4) WITHOUT CHANCE: NO MARK (the own item behind the block: it may be spent here), (Eval), WIs and the index masks' pin give the claim on M and the cells' pin AT THE WITNESS THAT E LAYS [K13's files' step back from (Eval), under "(Eval) is laid", which rides in the slot's own condition;
          the cells' pin: by the make of E under the promise on the table];
    (S5) no mark and the two pins ride back [frames: they read trees below the chain's first, and no cell].
  PointLeadsBN: THE DEBT ITSELF, from two games: lostK, a function of THE KEY (the acting part: the chain's own record with the key, the stored table), lost at εK AT EVERY KEY; lostO, which may read the slot's whole statement, lost at εO
    inside the promise; the block's own errors bear εK + n · εO; and the four steps where both games are lost.
  PointYes: (S23) UNFOLDED INTO WHAT K14's FILES HOLD AT A YES WHOSE WRITTEN ROUND READS AS THE POINT psi: letters: Vec (the other vector's type), Pt (the points), VI a V ("V is the row weights applied to the matrix": g and the matrix read
    off the statement in front), DotT a V psi ((Dot)'s equation with the matrix itself at psi), VOf a (THE OTHER VECTOR AS THE STATEMENT IN FRONT FIXES IT: what W's word decodes to with W's sample), wv w (the witness's), DotU b w.
    THE SLOT's SORT OF LOST POINTS IS ¬ VI a (VOf a) ∧ DotT a (VOf a) psi: A FUNCTION OF THE STATEMENT IN FRONT AND THE POINT: IT READS NO WITNESS. From: psi is of neither sort · K14's files' law of a yes (off the key's sort: nearU, recRow and
    DotU give DotT at the witness's own vector) · (Dot) with omU is DotU · W's pin fixes the vector (wv w = VOf a) · (S0), (S4) at WIs w := VI a (wv w), (S5).
WHOEVER HOLDS TWO COUNTS OF TYPED VALUES (a bad set by the key, one by the statement) calls the rule "a plain law for a batch, for one written round, from two counts" with PointStep as its last premise: the two roads meet in stepPt.

Limits. Rules under letters. No step is shown of the protocol's block. At lostK := lostO := "false" with errors as large as the number of challenges all holds and says nothing. n stands in one premise alone.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.GlueSecondProofs
import Johnson.Desc.Plain.Both

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape Doomed)
open VerifiableInference.Desc.Shared

section
variable {P₁ S₂ Cl Wt : Type} {C : CK} {Fr : Frame} (N : NumbersS) (Mg : MeaningS S₂ P₁ Wt)
  (Pm : PromMeaning S₂) (Oc : P₁ → Strs → Prop) (split : Bool)
  (p : Piece C Fr (P₁ × S₂) Cl Wt) (l : List (Piece C Fr (P₁ × S₂) Cl Wt))

/-- A shared item, read at border k of the chain p :: l. -/
def shIt (i : ItemS) (k : ℕ) (a : (P₁ × S₂) × Fr.E.Str) (w : Wt) : Prop :=
  muQ N Mg p l i k ((actQ N p l k).2 a) w

/-- An own item. -/
def ownItem (i : ItemS) (a : (P₁ × S₂) × Fr.E.Str) (w : Wt) : Prop :=
  i.holdsOwn N Mg a.1.1 a.1.2 (strsOf Fr a.2) w

/-- **The relation that is owed at "LIN point".** -/
def stepPt (E : (P₁ × S₂) × Fr.E.Str → Wt → Wt) (a b : (P₁ × S₂) × Fr.E.Str) : Prop :=
  onQ₂ N Pm Oc split p l 2 b ∧ ∀ w, relQ₂ N Mg split p l 2 b w → relQ₂ N Mg split p l 1 a (E a w)

end

/-- What is open, of the shared items, at border k: by the computed list. -/
theorem openShL_iff (split : Bool) (k : ℕ) (i : ItemS) :
    openAfter (insSh split) (outsSh split) startSh k i ↔
      i ∈ openL (insLSh split) (outsLSh split) startLSh k := by
  rw [insSh_eq, outsSh_eq, startSh_eq, openIsList ItemS (insLSh split) (outsLSh split) startLSh]

theorem openSh_one (split : Bool) (i : ItemS)
    (h : openAfter (insSh split) (outsSh split) startSh 1 i) : i = .pinT := by
  have h' := (openShL_iff split 1 i).1 h
  cases split
  · have e : (openL (insLSh false) (outsLSh false) startLSh 1).dedup = [.pinT] := by decide
    rw [← List.mem_dedup, e, List.mem_singleton] at h'
    exact h'
  · have e : (openL (insLSh true) (outsLSh true) startLSh 1).dedup = [.pinT] := by decide
    rw [← List.mem_dedup, e, List.mem_singleton] at h'
    exact h'

theorem openSh_two (split : Bool) (i : ItemS) (h : i ∈ [ItemS.omU, .nearU, .recRow]) :
    openAfter (insSh split) (outsSh split) startSh 2 i := by
  refine (openShL_iff split 2 i).2 ?_
  cases split
  · have e : ∀ j ∈ [ItemS.omU, .nearU, .recRow], j ∈ openL (insLSh false) (outsLSh false) startLSh 2 := by
      decide
    exact e i h
  · have e : ∀ j ∈ [ItemS.omU, .nearU, .recRow], j ∈ openL (insLSh true) (outsLSh true) startLSh 2 := by
      decide
    exact e i h

/-- **The step without chance, at one yes.** -/
def PointStep : Prop :=
  ∀ (P₁ S₂ Cl Wt : Type) (C : CK) (Fr : Frame) (N : NumbersS) (Mg : MeaningS S₂ P₁ Wt)
    (Pm : PromMeaning S₂) (Oc : P₁ → Strs → Prop) (split : Bool)
    (f : Piece C Fr (P₁ × S₂) Cl Wt) (r : List (Piece C Fr (P₁ × S₂) Cl Wt))
    (E : (P₁ × S₂) × Fr.E.Str → Wt → Wt) (a b : (P₁ × S₂) × Fr.E.Str) (WIs : Wt → Prop),
    onQ₂ N Pm Oc split f r 2 b →
    (∀ w, shIt N Mg f r .nearU 2 b w → shIt N Mg f r .recRow 2 b w → shIt N Mg f r .omU 2 b w →
      ownItem N Mg .dot b w → ownItem N Mg .pinV b w → WIs w) →
    (∀ w, ownItem N Mg .unmarked1 b w → ownItem N Mg .ev b w → WIs w → ownItem N Mg .pinI b w →
      ownItem N Mg .claimM a (E a w) ∧ shIt N Mg f r .pinT 1 a (E a w)) →
    (∀ w i, i ∈ [ItemS.unmarked1, .pinI, .pinV] → ownItem N Mg i b w → ownItem N Mg i a (E a w)) →
    stepPt N Mg Pm Oc split f r E a b

/-- Plain logic: off the slot's sort of lost points, (Dot)'s equation with the matrix at the fixed vector gives the claim. -/
theorem vi_of_notBad {Vec Pt : Type} (VI : Vec → Prop) (DotT : Vec → Pt → Prop) (V V' : Vec) (psi : Pt)
    (hO : ¬ (¬ VI V ∧ DotT V psi)) (hv : V' = V) (hd : DotT V' psi) : VI V' := by
  subst hv
  by_contra hn
  exact hO ⟨hn, hd⟩

/-- **The step at one yes, from the two sorts of lost points apart.** -/
def PointYes : Prop :=
  ∀ (P₁ S₂ Cl Wt Vec Pt : Type) (C : CK) (Fr : Frame) (N : NumbersS) (Mg : MeaningS S₂ P₁ Wt)
    (Pm : PromMeaning S₂) (Oc : P₁ → Strs → Prop) (split : Bool)
    (f : Piece C Fr (P₁ × S₂) Cl Wt) (r : List (Piece C Fr (P₁ × S₂) Cl Wt))
    (E : (P₁ × S₂) × Fr.E.Str → Wt → Wt) (a b : (P₁ × S₂) × Fr.E.Str)
    (VI : Vec → Prop) (DotT : Vec → Pt → Prop) (V : Vec) (wv : Wt → Vec) (DotU : Wt → Prop)
    (badK : Pt → Prop) (psi : Pt),
    onQ₂ N Pm Oc split f r 2 b →
    ¬ badK psi → ¬ (¬ VI V ∧ DotT V psi) →
    (∀ w, ¬ badK psi → shIt N Mg f r .nearU 2 b w → shIt N Mg f r .recRow 2 b w → DotU w →
      DotT (wv w) psi) →
    (∀ w, ownItem N Mg .dot b w → shIt N Mg f r .omU 2 b w → DotU w) →
    (∀ w, ownItem N Mg .pinV b w → wv w = V) →
    (∀ w, ownItem N Mg .unmarked1 b w → ownItem N Mg .ev b w → VI (wv w) → ownItem N Mg .pinI b w →
      ownItem N Mg .claimM a (E a w) ∧ shIt N Mg f r .pinT 1 a (E a w)) →
    (∀ w i, i ∈ [ItemS.unmarked1, .pinI, .pinV] → ownItem N Mg i b w → ownItem N Mg i a (E a w)) →
    stepPt N Mg Pm Oc split f r E a b

/-- **The debt at "LIN point", in the plain form for a batch, from two games and the four steps.** -/
def PointLeadsBN : Prop :=
  ∀ (P₁ S₂ Cl Wt : Type) (C : CK) (Fr : Frame) (N : NumbersS) (Mg : MeaningS S₂ P₁ Wt)
    (Pm : PromMeaning S₂) (Oc : P₁ → Strs → Prop) (split : Bool) (n : ℕ)
    (f pt : Piece C Fr (P₁ × S₂) Cl Wt) (r : List (Piece C Fr (P₁ × S₂) Cl Wt))
    (E : (P₁ × S₂) × Fr.E.Str → Wt → Wt) (εK εO : Err (uLT C pt.ds))
    (lostK : (actQ N f (pt :: r) 1).1 → Iop.Tr (uLT C pt.ds) → Prop)
    (lostO : (P₁ × S₂) × Fr.E.Str → Iop.Tr (uLT C pt.ds) → Prop)
    (WIs : (P₁ × S₂) × Fr.E.Str → Wt → Prop),
    Err.le (Err.add εK (Err.times n εO)) pt.err →
    (∀ k, Doomed (uLT C pt.ds) εK (lostK k)) →
    (∀ a, onQ₂ N Pm Oc split f (pt :: r) 1 a → Doomed (uLT C pt.ds) εO (lostO a)) →
    (∀ a τ b, onQ₂ N Pm Oc split f (pt :: r) 1 a → pt.ior.red.out a τ = some b →
      onQ₂ N Pm Oc split f (pt :: r) 2 b) →
    (∀ a τ b w, onQ₂ N Pm Oc split f (pt :: r) 1 a → lostK ((actQ N f (pt :: r) 1).2 a) τ →
      lostO a τ → pt.ior.red.out a τ = some b → shIt N Mg f (pt :: r) .nearU 2 b w →
      shIt N Mg f (pt :: r) .recRow 2 b w → shIt N Mg f (pt :: r) .omU 2 b w →
      ownItem N Mg .dot b w → ownItem N Mg .pinV b w → WIs b w) →
    (∀ a τ b w, onQ₂ N Pm Oc split f (pt :: r) 1 a → pt.ior.red.out a τ = some b →
      ownItem N Mg .unmarked1 b w → ownItem N Mg .ev b w → WIs b w → ownItem N Mg .pinI b w →
      ownItem N Mg .claimM a (E a w) ∧ shIt N Mg f (pt :: r) .pinT 1 a (E a w)) →
    (∀ a τ b w i, i ∈ [ItemS.unmarked1, .pinI, .pinV] → onQ₂ N Pm Oc split f (pt :: r) 1 a →
      pt.ior.red.out a τ = some b → ownItem N Mg i b w → ownItem N Mg i a (E a w)) →
    pt.ior.red.LeadsBN (actQ N f (pt :: r) 1).2 (onQ₂ N Pm Oc split f (pt :: r) 1)
      (stepPt N Mg Pm Oc split f (pt :: r) E) n pt.err

theorem pointStep : PointStep := by
  intro P₁ S₂ Cl Wt C Fr N Mg Pm Oc split f r E a b WIs s0 s23 s4 s5
  refine ⟨s0, fun w hw => ?_⟩
  obtain ⟨hs, hown⟩ := hw
  have own2 : ∀ i ∈ [ItemS.unmarked1, .pinI, .pinV, .ev, .dot], ownItem N Mg i b w := fun i hi =>
    hown i hi
  have hW := s23 w (hs .nearU (openSh_two split _ (by decide)))
    (hs .recRow (openSh_two split _ (by decide))) (hs .omU (openSh_two split _ (by decide)))
    (own2 .dot (by decide)) (own2 .pinV (by decide))
  obtain ⟨hc, hp⟩ := s4 w (own2 .unmarked1 (by decide)) (own2 .ev (by decide)) hW (own2 .pinI (by decide))
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · obtain rfl := openSh_one split i hi
    exact hp
  · have hi' : i ∈ [ItemS.unmarked1, .pinI, .pinV, .claimM] := hi
    rcases List.mem_cons.1 hi' with rfl | hi'
    · exact s5 w _ (by decide) (own2 _ (by decide))
    rcases List.mem_cons.1 hi' with rfl | hi'
    · exact s5 w _ (by decide) (own2 _ (by decide))
    rcases List.mem_cons.1 hi' with rfl | hi'
    · exact s5 w _ (by decide) (own2 _ (by decide))
    · obtain rfl := List.mem_singleton.1 hi'
      exact hc

theorem pointYes : PointYes := by
  intro P₁ S₂ Cl Wt Vec Pt C Fr N Mg Pm Oc split f r E a b VI DotT V wv DotU badK psi s0 hK hO hyes hU hV
    s4 s5
  exact pointStep P₁ S₂ Cl Wt C Fr N Mg Pm Oc split f r E a b (fun w => VI (wv w)) s0
    (fun w hn hr ho hd hp => vi_of_notBad VI DotT V (wv w) psi hO (hV w hp)
      (hyes w hK hn hr (hU w hd ho))) s4 s5

theorem pointLeadsBN : PointLeadsBN := by
  intro P₁ S₂ Cl Wt C Fr N Mg Pm Oc split n f pt r E εK εO lostK lostO WIs hle hK hO s0 s23 s4 s5
  refine ⟨εK, εO, hle, lostK, lostO, hK, hO, fun a τ b ha hk ho hb => ?_⟩
  exact pointStep P₁ S₂ Cl Wt C Fr N Mg Pm Oc split f (pt :: r) E a b (WIs b) (s0 a τ b ha hb)
    (fun w h1 h2 h3 h4 h5 => s23 a τ b w ha hk ho hb h1 h2 h3 h4 h5)
    (fun w h0 h1 h2 h3 => s4 a τ b w ha hb h0 h1 h2 h3) (fun w i hi h => s5 a τ b w i hi ha hb h)

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.pointStep
#print axioms VerifiableInference.Desc.Sound.pointYes
#print axioms VerifiableInference.Desc.Sound.pointLeadsBN
