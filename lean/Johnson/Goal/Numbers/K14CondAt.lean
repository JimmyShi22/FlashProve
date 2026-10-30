-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Numbers/K14CondAt.lean: the public conditions of the kind K14 (the linear claim's
shared part) at the
release's numbers, by Lean's kernel: at the typed sizes of a proof file's test on the table over the
file's own codes (Johnson/Desc/K1/Law/CondReal.lean: `realSized`), and at the library's typed sizes
of a key of
full
size (`keyFull`), and so at the planner's sizes of the key at every three public files in the scope
of the goals.

The law of the kind's eight blocks (K14/Law/FencedRow.lean: row1to8_decoded) has premises on public
numbers, on written rounds, and on letters. Here the premises on public numbers are gathered in one
record, under that law's own names, with one test with code.
  pub P: of the eight blocks: each one's name, its test on the plan, the entries of its rounds
  pub_free: these do not hang on the statement's item, nor on which messages are fixed before the
      point, if there are some (another form of the kind's text refuses a plan that names none)
  K14Cond f P W: cond: the kind's public condition (K14/Law/Condition.lean: the shape's conditions
      with the codes, and two codes) · ha: the index's code has at most 2 ^ 32 positions · hi: the
      index's shape is lawful · hroom: the matrix fits the index's plain part · blocks: there are
      eight blocks, each one's test on the plan says yes, and the entries of their rounds, in a row,
      are the first eight entries of the written list W · sendU, sendO: K14's two places for K1 have
      the codes and messages of the records (f, 1, 0) and (f, 1, 1), the kind K1's one Boolean holds
      there at the records' radii, and each draws one seed
  k14B, k14B_sound: the part that is not K1's, as a test with code
  real_test14, key_test14: the test says yes: evaluations in Lean's kernel (decide +kernel)
  k14_real: there are sizes x with `realSized = some (x, codesFull2)` such that K14Cond holds at
      ⟨recordSet, .shared, codesFull2, x.shape, item, before⟩, before not empty, and the proof
      file's second written
      list
  k14_real_seat: so it holds at the parameters that the shared chain's maker takes off the planner's
      chains (Desc.K14.p14Of c before), wherever the planner's sizes of the proof have that setting,
      these codes and that shape, and are no one-time test's
  k14_key, k14_key_at_scope: the like at the key file's second written list

What is not claimed. That the planner's sizes of a proof at the release's files are x: no theorem.
The premises of row1to8_decoded on written rounds beyond their entries, on pieces, on trees' numbers
and on letters; hbad (the count of the index's bad points); the numbers e1 … e7. With which scope,
item and messages a description of a key file calls the kind: the scope is taken as .once. What the
heads of Johnson/Desc/K1/Law/CondReal.lean and K01KeyAt.lean do not claim. Nothing on soundness, on
an honest prover
or on hiding.

-/
import Johnson.Goal.Numbers.K01KeyAt
import Johnson.Desc.K14.Law.Condition

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Params.Prices OnBytes.Plan Johnson.G
open VerifiableInference.Desc.K1 (PlaceOk realSized k01_real placeOk_key keySent sharedSent)
open Lk6.AtPlan (keyFull key_eq_at_scope)

/-- Of the eight blocks: the name, the test on the plan, the entries of the rounds. -/
def pub (P : P14) : Option (List (String × Bool × List Fmt.Entry)) :=
  (blocks P).map (·.map fun b => (b.name, b.planOk, b.rounds.map (·.entry)))

/-- They do not hang on the item, nor on which messages are fixed before the point, if there are
some. -/
theorem pub_free (set : Setting) (scope : Scope) (codes : Codes) (S : LinShape) (item : Nat)
    (bp : List (Nat × Nat)) (hbp : bp ≠ []) :
    pub ⟨set, scope, codes, S, item, bp⟩ = pub ⟨set, scope, codes, S, 0, [(1, 0)]⟩ := by
  cases bp with
  | nil => exact absurd rfl hbp
  | cons x l =>
    unfold pub blocks
    dsimp only
    cases withU S <;> rfl

/-- K14's two places for K1. -/
abbrev pU (P : P14) (sent : Array OracleNotice) : VerifiableInference.Desc.K1.Par :=
  parK1 P 2 "o_u and the first mask" sent
abbrev pO (P : P14) : VerifiableInference.Desc.K1.Par :=
  parK1 P 5 "o_omega and o_sp" (withOmega P.S)

/-- **The kind's public conditions.** f: the file's number in the written lists; W: the written list
of the file's second chain. -/
structure K14Cond (f : Nat) (P : P14) (W : Rounds) : Prop where
  cond : Condition P.codes P.S
  ha : P.par.S.fold.index.code.logN ≤ 32
  hi : P.par.S.fold.index.ok = true
  hroom : P.par.S.matrixRows * 2 ^ P.par.S.kLo ≤ P.par.S.fold.index.plain
  blocks : ∃ bs, blocks P = some bs ∧ bs.length = 8 ∧ (∀ b ∈ bs, b.planOk = true) ∧
    bs.flatMap (·.rounds.map (·.entry)) = (W.take 8).map (·.1.entry)
  sendU : ∃ sent, withU P.S = some sent ∧ PlaceOk f 1 0 (pU P sent) ∧ (pU P sent).seeds = 1
  sendO : PlaceOk f 1 1 (pO P) ∧ (pO P).seeds = 1

/-- The part that is not K1's, as a test with code. -/
def k14B (P : P14) (W : Rounds) : Bool :=
  conditionB P.codes P.S && decide (P.par.S.fold.index.code.logN ≤ 32) &&
    P.par.S.fold.index.ok &&
    decide (P.par.S.matrixRows * 2 ^ P.par.S.kLo ≤ P.par.S.fold.index.plain) &&
    (pub P).any (fun l => decide (l.length = 8) && l.all (·.2.1) &&
      decide (l.flatMap (·.2.2) = (W.take 8).map (·.1.entry))) &&
    (withU P.S).any (fun u => decide ((pU P u).seeds = 1)) && decide ((pO P).seeds = 1)

/-- What the test's yes gives, with K1's two places handed in. -/
theorem k14B_sound {f : Nat} {set : Setting} {scope : Scope} {codes : Codes} {S : LinShape}
    {W : Rounds} (h : k14B ⟨set, scope, codes, S, 0, [(1, 0)]⟩ W = true) (item : Nat)
    (bp : List (Nat × Nat)) (hbp : bp ≠ [])
    (hU : ∀ sent, withU S = some sent → PlaceOk f 1 0 (pU ⟨set, scope, codes, S, item, bp⟩ sent))
    (hO : PlaceOk f 1 1 (pO ⟨set, scope, codes, S, item, bp⟩)) :
    K14Cond f ⟨set, scope, codes, S, item, bp⟩ W := by
  unfold k14B at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  rw [← pub_free set scope codes S item bp hbp] at h5
  refine ⟨(condition_iff _ _).2 h1, h2, h3, h4, ?_, ?_, ⟨hO, h7⟩⟩
  · unfold pub at h5
    cases hb : blocks ⟨set, scope, codes, S, item, bp⟩ with
    | none =>
      rw [hb] at h5
      cases h5
    | some bs =>
    rw [hb] at h5
    simp only [Option.map_some, Option.any_some, Bool.and_eq_true, decide_eq_true_eq,
      List.length_map, List.all_map, List.all_eq_true, List.flatMap_map] at h5
    exact ⟨bs, rfl, h5.1.1, fun b hb' => h5.1.2 b hb', h5.2⟩
  · cases hu : withU S with
    | none =>
      have h6' : (Option.any
          (fun u => decide ((pU ⟨set, scope, codes, S, 0, [(1, 0)]⟩ u).seeds = 1))
          (withU S)) = true := h6
      rw [hu] at h6'
      cases h6'
    | some u =>
      have h6' : (Option.any
          (fun u => decide ((pU ⟨set, scope, codes, S, 0, [(1, 0)]⟩ u).seeds = 1))
          (withU S)) = true := h6
      rw [hu] at h6'
      exact ⟨u, rfl, hU u hu, of_decide_eq_true h6'⟩

/-! ## A proof file -/

theorem real_test14 : (realSized.any fun p =>
    k14B ⟨recordSet, .shared, p.2, p.1.shape, 0, [(1, 0)]⟩ dryProofFull.2.1) = true := by
  decide +kernel

/-- **The kind's public conditions at the typed sizes over a proof file's own codes.** -/
theorem k14_real : ∃ x : LinSized, realSized = some (x, codesFull2) ∧ AtRecord x ∧
    ∀ (item : Nat) (bp : List (Nat × Nat)), bp ≠ [] →
      K14Cond 2 ⟨recordSet, .shared, codesFull2, x.shape, item, bp⟩ dryProofFull.2.1 := by
  obtain ⟨x, -, -, a1, a2, -, -, -, -, -, -, a9, -, -⟩ := k01_real
  refine ⟨x, a1, a2, fun item bp hbp => ?_⟩
  have h := real_test14
  rw [a1] at h
  obtain ⟨⟨u, hu, hp⟩, hO⟩ := a9 ⟨recordSet, .shared, codesFull2, x.shape, item, bp⟩ rfl rfl
  refine k14B_sound h item bp hbp (fun sent hs => ?_) hO
  obtain rfl : u = sent := Option.some.inj (hu.symm.trans hs)
  exact hp

/-- **At the parameters that the shared chain's maker takes off the planner's chains.** -/
theorem k14_real_seat : ∃ x : LinSized, realSized = some (x, codesFull2) ∧ AtRecord x ∧
    ∀ (c : Model.Verify.Chains) (bp : List (Nat × Nat)), bp ≠ [] →
      c.made.sized.proof.set = recordSet → c.made.sized.proof.codes = codesFull2 →
      c.made.sized.proof.batch.shape = x.shape →
      c.made.sized.proof.batch.lines.oneTime = false →
        K14Cond 2 (p14Of c bp) dryProofFull.2.1 := by
  obtain ⟨x, a1, a2, a3⟩ := k14_real
  refine ⟨x, a1, a2, fun c bp hbp h1 h2 h3 h4 => ?_⟩
  have e : p14Of c bp = ⟨recordSet, .shared, codesFull2, x.shape, 0, bp⟩ := by
    unfold p14Of
    simp only [h1, h2, h3, h4, Bool.false_eq_true, if_false]
  rw [e]
  exact a3 0 bp hbp

/-! ## A key file -/

theorem key_test14 :
    k14B ⟨recordSet, .once, keyFull.codes, keyFull.once.shape, 0, [(1, 0)]⟩ dryKeyFull.2.1 =
      true := by
  decide +kernel

theorem sharedSent_heads {S : LinShape} {u : Array OracleNotice} (h : withU S = some u) :
    ∃ T, sharedSent S = some (u.toList :: (withOmega S).toList :: T) := by
  unfold sharedSent
  rw [h]
  exact ⟨_, rfl⟩

/-- **The kind's public conditions at the typed sizes of a key of full size.** -/
theorem k14_key (item : Nat) (bp : List (Nat × Nat)) (hbp : bp ≠ []) :
    K14Cond 0 ⟨recordSet, .once, keyFull.codes, keyFull.once.shape, item, bp⟩ dryKeyFull.2.1 := by
  have hu : ∃ u, withU keyFull.once.shape = some u := by
    have h := key_test14
    unfold k14B at h
    simp only [Bool.and_eq_true] at h
    have h6 : (Option.any (fun u => decide ((pU ⟨recordSet, .once, keyFull.codes,
        keyFull.once.shape, 0, [(1, 0)]⟩ u).seeds = 1)) (withU keyFull.once.shape)) = true := h.1.2
    cases hw : withU keyFull.once.shape with
    | none =>
      rw [hw] at h6
      cases h6
    | some u => exact ⟨u, rfl⟩
  obtain ⟨u, hu⟩ := hu
  obtain ⟨T, hT⟩ := sharedSent_heads hu
  refine k14B_sound key_test14 item bp hbp (fun sent hs => ?_) ?_
  · obtain rfl : u = sent := Option.some.inj (hu.symm.trans hs)
    exact placeOk_key (c := 1) (k := 0) (by decide) hT rfl _ rfl
      (by rw [VerifiableInference.Desc.K1.parK1_sent])
  · exact placeOk_key (c := 1) (k := 1) (by decide) hT rfl _ rfl
      (by rw [VerifiableInference.Desc.K1.parK1_sent])

/-- **At every three public files in the scope of the goals**, from a planner that returns. -/
theorem k14_key_at_scope {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {p : Model.Verify.Planned} (hp : Model.Verify.planned Z.pol Z.KL (some Z.lay) = .ok p)
    (item : Nat) (bp : List (Nat × Nat)) (hbp : bp ≠ []) :
    K14Cond 0 ⟨p.chains.made.sized.key.set, .once, p.chains.made.sized.key.codes,
      p.chains.made.sized.key.once.shape, item, bp⟩ dryKeyFull.2.1 := by
  rw [key_eq_at_scope hZ hp]
  exact k14_key item bp hbp

end Desc.K14.Law
