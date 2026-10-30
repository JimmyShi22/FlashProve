-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/SharesChain.lean: the stops of one chain's prover's sides, as
gates (Honest/Law/SharesHeld.lean). `chainStopAt` (Honest/Rule.lean) asks the parts' stops one after
the other, each at the challenges heard before the part's own and at its own rounds' challenges. So
each part is a gate at its own stretch of the chain's rounds, and a sub-protocol without a prover's
side is a gate that never fires. The main lemma, `chain_stops_le`: the probability of the typed
verifier's messages at which the chain's prover's sides stop is at most the sum of the parts'
numbers. Its hypothesis, `ChainHeld`: each part's gate fires, over its own rounds' messages, with
probability at most the part's number, at every list of such challenges.

What this is. Definitions, and conditional lemmas about a function of Honest/Rule.lean and the
library's own probability. No run and no coin occurs in this file. None of the library's goals.
Probabilities are over the verifier's messages, drawn uniformly (`Iop.prRho`), at a fixed private
input and instance.

Trivially met. At numbers that add up to 1 or more the bound says nothing. A part whose gate never
fires meets the hypothesis with the number 0.

  1  `total`, `spoken_append`, `gatesHeld_all`, `prRho_ds`   on gates
  2  `rowGates`, `row_total`, `row_ds`, `row_spoken`   a list's parts as gates
  3  `memberGates`, `chainGates`, `HalvesFit`, `member_gates`, `chain_ds`, `chain_spoken`   a
     chain's
  4  `ChainHeld`, `chain_stops_le`   the main lemma

Limits.
  * `sp` says which results of `Part.stopAt` count: a parameter, with two hypotheses (`hor`, `hno`).
  * The hypothesis `ChainHeld` is stated gate by gate: which stretch of the chain's data a part's
    gate has is read from `chainGates`.
  * `ChainHeld` asks every list of such challenges, of any length and content. That is more than
    `gates_le` needs: a stop that reads such challenges may meet it with the number 1 alone.
    `GatesHeld` at `chainGates` is the weaker hypothesis: it is asked at fewer lists of such
    challenges.
  * The kit C of verifier's messages is a parameter. How a probability over its typed challenges
    follows from a count of what they show depends on the kit, and is not treated here.
  * `val` (a part's number), `v` (what the second stops may read) and `ds` (the rounds' data,
    compared with the rounds by their number alone) are parameters.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.SharesHeld
import Johnson.Desc.ProofFile.Honest.Rule

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob
open scoped ENNReal
open VerifiableInference.Desc (Block)
open OnBytes.Maker (RDT uLT drawnT)
open _root_.Run.PQ (CK)

variable {S Cl V W Y : Type}

/-! ## 1 On gates -/

/-- How many rounds a list of gates has. -/
def total (gs : List Gate) : Nat := (gs.map (·.ds.length)).sum

theorem spoken_append (B : List Gate) : ∀ (A : List Gate) (fr dr : List Fmt.Drawn),
    spoken (A ++ B) fr dr =
      (spoken A fr (dr.take (total A)) ||
        spoken B (fr ++ dr.take (total A)) (dr.drop (total A)))
  | [], fr, dr => by
    show spoken B fr dr = (false || spoken B (fr ++ dr.take 0) (dr.drop 0))
    rw [List.take_zero, List.append_nil, List.drop_zero, Bool.false_or]
  | g :: A, fr, dr => by
    have ht : total (g :: A) = g.ds.length + total A := by
      unfold total
      rw [List.map_cons, List.sum_cons]
    show (g.test fr (dr.take g.ds.length) ||
        spoken (A ++ B) (fr ++ dr.take g.ds.length) (dr.drop g.ds.length)) =
      ((g.test fr ((dr.take (total (g :: A))).take g.ds.length) ||
        spoken A (fr ++ (dr.take (total (g :: A))).take g.ds.length)
          ((dr.take (total (g :: A))).drop g.ds.length)) ||
        spoken B (fr ++ dr.take (total (g :: A))) (dr.drop (total (g :: A))))
    rw [spoken_append B A, ht, List.take_take, Nat.min_eq_left (Nat.le_add_right _ _),
      List.drop_take, Nat.add_sub_cancel_left, List.drop_drop, List.take_add, Bool.or_assoc,
      List.append_assoc]

theorem gatesHeld_all (C : CK) : ∀ (gs : List Gate),
    (∀ g ∈ gs, ∀ fr, Iop.prRho {ρ : Iop.Rho (uLT C g.ds) |
      g.test fr (drawnT C g.ds ρ) = true} ≤ g.p) → ∀ fr, GatesHeld C gs fr
  | [], _, _ => trivial
  | g :: gs, h, fr =>
    ⟨h g List.mem_cons_self fr, fun _ _ =>
      gatesHeld_all C gs (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')) _⟩

theorem prRho_ds (C : CK) {l l' : List RDT} (e : l = l') (P : List Fmt.Drawn → Prop) :
    Iop.prRho {ρ : Iop.Rho (uLT C l) | P (drawnT C l ρ)} =
      Iop.prRho {ρ : Iop.Rho (uLT C l') | P (drawnT C l' ρ)} := by
  subst e
  rfl

/-! ## 2 A list's parts as gates -/

section
variable (sp : Option Why → Bool) (v : Option V) (val : Part V W Y → ℝ≥0∞)

/-- A list's parts, each at its stretch of the list's rounds. -/
def rowGates : List (Part V W Y) → List RDT → List Gate
  | [], _ => []
  | p :: ps, ds =>
    ⟨ds.take p.moves.length, fun fr own => sp (p.stopAt v fr own), val p⟩ ::
      rowGates ps (ds.drop p.moves.length)

theorem row_total : ∀ (ps : List (Part V W Y)) (ds : List RDT),
    ds.length = (ps.map (·.moves.length)).sum → total (rowGates sp v val ps ds) = ds.length
  | [], ds, h => h.symm
  | p :: ps, ds, h => by
    rw [List.map_cons, List.sum_cons] at h
    have ih := row_total ps (ds.drop p.moves.length) (by rw [List.length_drop]; omega)
    show ((ds.take p.moves.length).length :: (rowGates sp v val ps
      (ds.drop p.moves.length)).map (·.ds.length)).sum = ds.length
    rw [List.sum_cons]
    have ih' : ((rowGates sp v val ps (ds.drop p.moves.length)).map (·.ds.length)).sum =
        (ds.drop p.moves.length).length := ih
    rw [ih', List.length_take, List.length_drop]
    omega

theorem row_ds : ∀ (ps : List (Part V W Y)) (ds : List RDT),
    ds.length = (ps.map (·.moves.length)).sum → (rowGates sp v val ps ds).flatMap (·.ds) = ds
  | [], ds, h => (List.eq_nil_of_length_eq_zero h).symm
  | p :: ps, ds, h => by
    rw [List.map_cons, List.sum_cons] at h
    show ds.take p.moves.length ++
      (rowGates sp v val ps (ds.drop p.moves.length)).flatMap (·.ds) = ds
    rw [row_ds ps (ds.drop p.moves.length) (by rw [List.length_drop]; omega),
      List.take_append_drop]

variable (hor : ∀ a b : Option Why, sp (a.or b) = true → sp a = true ∨ sp b = true)
  (hno : sp none = false)
include hor hno

theorem row_spoken : ∀ (ps : List (Part V W Y)) (ds : List RDT) (loc dr : List Fmt.Drawn),
    ds.length = (ps.map (·.moves.length)).sum → sp (rowStopAt v ps loc dr) = true →
    spoken (rowGates sp v val ps ds) loc dr = true
  | [], _, _, _, _, h => by
    have h' : sp none = true := h
    rw [hno] at h'
    cases h'
  | p :: ps, ds, loc, dr, hl, h => by
    rw [List.map_cons, List.sum_cons] at hl
    have hm : (ds.take p.moves.length).length = p.moves.length := by
      rw [List.length_take]
      omega
    have h' : sp ((p.stopAt v loc (dr.take p.moves.length)).or
        (rowStopAt v ps (loc ++ dr.take p.moves.length) (dr.drop p.moves.length))) = true := h
    show (sp (p.stopAt v loc (dr.take (ds.take p.moves.length).length)) ||
      spoken (rowGates sp v val ps (ds.drop p.moves.length))
        (loc ++ dr.take (ds.take p.moves.length).length)
        (dr.drop (ds.take p.moves.length).length)) = true
    rw [hm, Bool.or_eq_true]
    rcases hor _ _ h' with g | g
    · exact Or.inl g
    · exact Or.inr (row_spoken ps _ _ _ (by rw [List.length_drop]; omega) g)

end

/-! ## 3 A chain's prover's sides as gates -/

section
variable (sp : Option Why → Bool) (v : Option V) (val : Part V W Y → ℝ≥0∞)
  (hs : List (Placed V W Y))

/-- One sub-protocol: the parts of the prover's side at its place; where there is none, a gate that
never fires. `ds`: the data of the sub-protocol's own rounds. -/
def memberGates (b : Block S Cl) (ds : List RDT) : List Gate :=
  match hs.find? fun h => h.place == b.place with
  | none => [⟨ds, fun _ _ => false, 0⟩]
  | some h => rowGates sp v val h.parts ds

/-- A chain's sub-protocols, one after the other. -/
def chainGates : List (Block S Cl) → List RDT → List Gate
  | [], _ => []
  | b :: bs, ds =>
    memberGates sp v val hs b (ds.take b.rounds.length) ++
      chainGates bs (ds.drop b.rounds.length)

/-- Each prover's side has exactly as many moves as its sub-protocol has rounds. -/
def HalvesFit (bs : List (Block S Cl)) : Prop :=
  ∀ b ∈ bs, ∀ h, (hs.find? fun h => h.place == b.place) = some h →
    (h.parts.map (·.moves.length)).sum = b.rounds.length

theorem member_gates (b : Block S Cl) (ds : List RDT) (hm : ds.length = b.rounds.length)
    (hf : ∀ h, (hs.find? fun h => h.place == b.place) = some h →
      (h.parts.map (·.moves.length)).sum = b.rounds.length) :
    total (memberGates sp v val hs b ds) = b.rounds.length ∧
      (memberGates sp v val hs b ds).flatMap (·.ds) = ds := by
  unfold memberGates
  cases hfd : hs.find? fun h => h.place == b.place with
  | none =>
    refine ⟨?_, ?_⟩
    · show (ds.length :: []).sum = _
      rw [List.sum_cons, List.sum_nil, hm, Nat.add_zero]
    · show ds ++ [] = _
      rw [List.append_nil]
  | some h =>
    have e := hf h hfd
    exact ⟨by
      show total (rowGates sp v val h.parts ds) = _
      rw [row_total sp v val h.parts _ (by rw [hm, e]), hm],
      row_ds sp v val h.parts _ (by rw [hm, e])⟩

theorem chain_ds : ∀ (bs : List (Block S Cl)) (ds : List RDT),
    ds.length = (bs.flatMap (·.rounds)).length → HalvesFit hs bs →
    (chainGates sp v val hs bs ds).flatMap (·.ds) = ds
  | [], ds, h, _ => (List.eq_nil_of_length_eq_zero h).symm
  | b :: bs, ds, h, hf => by
    rw [List.flatMap_cons, List.length_append] at h
    obtain ⟨-, e2⟩ := member_gates sp v val hs b (ds.take b.rounds.length)
      (by rw [List.length_take]; omega) (hf b List.mem_cons_self)
    unfold chainGates
    rw [List.flatMap_append, e2, chain_ds bs (ds.drop b.rounds.length)
      (by rw [List.length_drop]; omega) (fun c hc => hf c (List.mem_cons_of_mem _ hc)),
      List.take_append_drop]

variable (hor : ∀ a b : Option Why, sp (a.or b) = true → sp a = true ∨ sp b = true)
  (hno : sp none = false)
include hor hno

theorem chain_spoken : ∀ (bs : List (Block S Cl)) (ds : List RDT) (loc dr : List Fmt.Drawn),
    ds.length = (bs.flatMap (·.rounds)).length → HalvesFit hs bs →
    sp (chainStopAt v bs hs loc dr) = true → spoken (chainGates sp v val hs bs ds) loc dr = true
  | [], _, _, _, _, _, h => by
    have h' : sp none = true := h
    rw [hno] at h'
    cases h'
  | b :: bs, ds, loc, dr, hl, hf, h => by
    rw [List.flatMap_cons, List.length_append] at hl
    have hm : (ds.take b.rounds.length).length = b.rounds.length := by
      rw [List.length_take]
      omega
    obtain ⟨e1, -⟩ := member_gates sp v val hs b (ds.take b.rounds.length) hm
      (hf b List.mem_cons_self)
    have h' : sp (((hs.find? fun g => g.place == b.place).bind fun g =>
        rowStopAt v g.parts loc (dr.take b.rounds.length)).or
          (chainStopAt v bs hs (loc ++ dr.take b.rounds.length)
            (dr.drop b.rounds.length))) = true := h
    unfold chainGates
    rw [spoken_append, e1, Bool.or_eq_true]
    rcases hor _ _ h' with g | g
    · left
      unfold memberGates
      cases hfd : hs.find? fun h => h.place == b.place with
      | none =>
        rw [hfd] at g
        have g' : sp none = true := g
        rw [hno] at g'
        cases g'
      | some q =>
        rw [hfd] at g
        exact row_spoken sp v val hor hno q.parts _ _ _
          (by rw [hm, hf b List.mem_cons_self q hfd]) g
    · exact Or.inr (chain_spoken bs _ _ _ (by rw [List.length_drop]; omega)
        (fun c hc => hf c (List.mem_cons_of_mem _ hc)) g)

/-! ## 4 The main lemma -/

omit hor hno in
/-- **Each gate of the chain fires, over its own rounds' messages, with probability at most its
number, at every list of challenges heard before the part's own.** A definition, meant as a
hypothesis. -/
def ChainHeld (C : CK) (bs : List (Block S Cl)) (ds : List RDT) : Prop :=
  ∀ g ∈ chainGates sp v val hs bs ds, ∀ fr,
    Iop.prRho {ρ : Iop.Rho (uLT C g.ds) | g.test fr (drawnT C g.ds ρ) = true} ≤ g.p

/-- **The probability of the messages at which a chain's prover's sides stop is at most the sum of
the gates' numbers.** -/
theorem chain_stops_le (C : CK) (bs : List (Block S Cl)) (ds : List RDT)
    (hl : ds.length = (bs.flatMap (·.rounds)).length) (hf : HalvesFit hs bs)
    (hh : ChainHeld sp v val hs C bs ds) (loc : List Fmt.Drawn) :
    Iop.prRho {ρ : Iop.Rho (uLT C ds) | sp (chainStopAt v bs hs loc (drawnT C ds ρ)) = true} ≤
      ((chainGates sp v val hs bs ds).map (·.p)).sum := by
  have key := gates_le C (chainGates sp v val hs bs ds) loc (gatesHeld_all C _ hh loc)
  rw [prRho_ds C (chain_ds sp v val hs bs ds hl hf)
    (fun dr => spoken (chainGates sp v val hs bs ds) loc dr = true)] at key
  refine le_trans (pr_mono _ ?_) key
  intro ρ hρ
  exact chain_spoken sp v val hs hor hno bs ds loc _ hl hf hρ

end

end ProofFile.Honest

#print axioms ProofFile.Honest.spoken_append
#print axioms ProofFile.Honest.gatesHeld_all
#print axioms ProofFile.Honest.prRho_ds
#print axioms ProofFile.Honest.row_total
#print axioms ProofFile.Honest.row_ds
#print axioms ProofFile.Honest.row_spoken
#print axioms ProofFile.Honest.member_gates
#print axioms ProofFile.Honest.chain_ds
#print axioms ProofFile.Honest.chain_spoken
#print axioms ProofFile.Honest.chain_stops_le
