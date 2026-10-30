-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Numbers/K13CondAt.lean: the public conditions of the kind K13 (the members' batching
and the linear
claim's first part) at the release's numbers, by Lean's kernel: in a proof file at the typed shape
of
the test on the table over the file's own codes (Johnson/Desc/K1/Law/CondReal.lean) and 13 rows; in
a key file at
the library's typed sizes of a key of full size and its 24 pending rows, and so at the planner's
sizes of the key at every three public files in the scope of the goals.

The kind's laws (K13/Law/PinA.lean: atM3_goodInA; Data.lean: pieceM3_below) ask of the written
rounds
`Declared P dZ d0 ds`: the stretch bears the entries that the block declares. So far that was held
by
runs at two stored plans. Here it follows for every stretch of written rounds with the entries and
kinds that stand in the library's written lists at the batching's place.
  stretch W i n: the entries and kinds of n written rounds from place i on
  K13Cond P codes W i msg: rows: more than one row (the batching's test on the plan) · quiet: the
      kind's quiet step in front of W's commitment, evaluated as it stands, says yes on the codes
      and
      the shape, and its message is msg: the messages of the record of W's sending ·
      declared: every stretch of written rounds with the entries and kinds of W's 2 + kCol rounds
      from
      place i on is `Declared` · caller: the library's two conditions on the proved batching's
      caller at the place, at every public record (K13/Law/Caller.lean: callerAt_ok): it holds at
      every P: no number is in it
  k13B, k13B_congr, k13B_sound: the test with code; it reads of the place's numbers the rows, the
      shape and the three numbers of work alone
  real_test13, key_test13: the test says yes: evaluations in Lean's kernel (decide +kernel)
  k13_real: at every place's numbers with 13 rows, no work and the shape of x, at the proof file's
      first written list from place 48270 on; and every K1's place with the written codes that
      announces the quiet step's message is PlaceOk 2 0 81
  k13_key, k13_key_at_scope: the like at the key file's first written list from place 18828 on

What is not claimed. That the planner's sizes of a proof at the release's files have x's shape and
leave 13 rows: no theorem; the 13 is the written round's own number. The laws' premises on letters
(the pin; AgreeAt). `Maps.Held` at these numbers: that is K13RoundsAt.lean's. FrontOk and EvalLaid,
which
speak of a record of a run. What the heads of Johnson/Desc/K1/Law/CondReal.lean and K01KeyAt.lean do
not claim.
Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Goal.Numbers.K01KeyAt
import Johnson.Desc.K13.Law.Data
import Johnson.Desc.K13.Law.Caller

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Params OnBytes.Params.Prices OnBytes.Plan OnBytes.Maker Johnson.G
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1 (PlaceOk realSized k01_real placeOk_of placeOk_key key_sent)
open Lk6.AtPlan (keyFull key_eq_at_scope)

/-- The entries and kinds of n written rounds from place i on. -/
def stretch (W : Rounds) (i n : Nat) : List (Fmt.Entry × Fmt.Kind) :=
  ((W.drop i).take n).map fun d => (d.1.entry, d.1.kind)

/-- **The kind's public conditions.** -/
structure K13Cond (P : Where) (codes : Codes) (W : Rounds) (i : Nat)
    (msg : Option (List OracleNotice)) : Prop where
  rows : 1 < P.rows
  quiet : ∃ w, quiet codes P.lin = .ok w ∧ some w.toList = msg
  declared : ∀ (dZ d0 : RDT) (ds : List RDT),
    (dZ :: d0 :: ds).map (fun d => (d.entry, d.kind)) = stretch W i (2 + P.lin.kCol) →
      Declared P dZ d0 ds
  caller : ∀ s : S, 2 ≤ (callerAt P s).n ∧ (callerAt P s).Z.OK

/-- The test with code. -/
def k13B (P : Where) (codes : Codes) (W : Rounds) (i : Nat) (msg : Option (List OracleNotice)) :
    Bool :=
  decide (1 < P.rows) && (quiet codes P.lin).toOption.any (fun w => decide (some w.toList = msg)) &&
    decide ((stretch W i (2 + P.lin.kCol)).map (·.1) =
      sigmaEntry P :: epsEntry P :: List.replicate P.lin.kCol (roundEntry P)) &&
    (stretch W i (2 + P.lin.kCol)).all fun x => decide (x.2 ≠ .sealed) && decide (x.2 ≠ .seeds)

/-- It reads the rows, the shape and the work alone. -/
theorem k13B_congr (P P' : Where) (codes : Codes) (W : Rounds) (i : Nat)
    (msg : Option (List OracleNotice)) (h1 : P.rows = P'.rows) (h2 : P.lin = P'.lin)
    (h3 : P.work = P'.work) : k13B P codes W i msg = k13B P' codes W i msg := by
  cases P
  cases P'
  simp only at h1 h2 h3
  subst h1 h2 h3
  rfl

theorem k13B_sound {P : Where} {codes : Codes} {W : Rounds} {i : Nat}
    {msg : Option (List OracleNotice)} (h : k13B P codes W i msg = true) :
    K13Cond P codes W i msg := by
  unfold k13B at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h4⟩, h5⟩ := h
  refine ⟨h1, ?_, fun dZ d0 ds hd => ?_, fun s => callerAt_ok P s⟩
  · cases hq : quiet codes P.lin with
    | error e =>
      rw [hq] at h2
      cases h2
    | ok w =>
      rw [hq] at h2
      exact ⟨w, rfl, of_decide_eq_true h2⟩
  · rw [← hd] at h4 h5
    simp only [List.map_cons, List.map_map, List.cons.injEq] at h4
    obtain ⟨e1, e2, e3⟩ := h4
    have k : ∀ d ∈ dZ :: d0 :: ds, PlainKind d := fun d hm =>
      h5 (d.entry, d.kind) (List.mem_map.2 ⟨d, hm, rfl⟩)
    have hl : ds.length = P.lin.kCol := by
      have := congrArg List.length e3
      simpa using this
    refine ⟨hl.symm, ⟨e1, k dZ (by simp)⟩, ⟨e2, k d0 (by simp)⟩,
      fun d hm => ⟨?_, k d (by simp [hm])⟩⟩
    have : d.entry ∈ List.replicate P.lin.kCol (roundEntry P) := by
      rw [← e3]
      exact List.mem_map.2 ⟨d, hm, rfl⟩
    exact (List.mem_replicate.1 this).2

/-- A place's numbers with given rows and shape, and no work. -/
def whereOf (rows : Nat) (lin : LinShape) : Where :=
  { chain := 1, piece := 0, pieceRows := 1, rows := rows, lin := lin, sent := 0 }

/-! ## A proof file -/

theorem real_test13 : (realSized.any fun p =>
    k13B (whereOf 13 p.1.shape) p.2 dryProofFull.1 48270 (K1.sentOf 2 0)[81]?) = true := by
  decide +kernel

/-- **The kind's public conditions in a proof file.** -/
theorem k13_real : ∃ x : LinSized, realSized = some (x, codesFull2) ∧ AtRecord x ∧
    ∀ P : Where, P.rows = 13 → P.lin = x.shape → P.work = (0, 0, 0) →
      K13Cond P codesFull2 dryProofFull.1 48270 (K1.sentOf 2 0)[81]? ∧
      ∀ (Q : VerifiableInference.Desc.K1.Par) (w : Array OracleNotice), Q.codes = codesFull2 →
        quiet codesFull2 P.lin = .ok w → Q.sent = w → PlaceOk 2 0 81 Q := by
  obtain ⟨x, -, -, a1, a2, -, -, -, -, -, -, -, -, -⟩ := k01_real
  refine ⟨x, a1, a2, fun P h1 h2 h3 => ?_⟩
  have h := real_test13
  rw [a1] at h
  have hc : K13Cond P codesFull2 dryProofFull.1 48270 (K1.sentOf 2 0)[81]? := by
    refine k13B_sound ?_
    rw [k13B_congr P (whereOf 13 x.shape) _ _ _ _ h1 h2 h3]
    exact h
  refine ⟨hc, fun Q w hQ hw hs => ?_⟩
  obtain ⟨w', hw', hm⟩ := hc.quiet
  obtain rfl : w' = w := Except.ok.inj (hw'.symm.trans hw)
  exact placeOk_of (c := 0) (by decide) hm.symm Q hQ (by rw [hs])

/-! ## A key file -/

theorem key_test13 : k13B (whereOf keyFull.ranges.pending keyFull.once.shape) keyFull.codes
    dryKeyFull.1 18828 (K1.sentOf 0 0)[5]? = true := by
  decide +kernel

/-- **The kind's public conditions in a key file, at the typed sizes.** -/
theorem k13_key (P : Where) (h1 : P.rows = keyFull.ranges.pending)
    (h2 : P.lin = keyFull.once.shape) (h3 : P.work = (0, 0, 0)) :
    K13Cond P keyFull.codes dryKeyFull.1 18828 (K1.sentOf 0 0)[5]? ∧
      ∀ (Q : VerifiableInference.Desc.K1.Par) (w : Array OracleNotice),
        Q.codes = keyFull.codes → quiet keyFull.codes P.lin = .ok w → Q.sent = w →
          PlaceOk 0 0 5 Q := by
  have hc : K13Cond P keyFull.codes dryKeyFull.1 18828 (K1.sentOf 0 0)[5]? := by
    refine k13B_sound ?_
    rw [k13B_congr P (whereOf keyFull.ranges.pending keyFull.once.shape) _ _ _ _ h1 h2 h3]
    exact key_test13
  refine ⟨hc, fun Q w hQ hw hs => ?_⟩
  obtain ⟨w', hw', hm⟩ := hc.quiet
  obtain rfl : w' = w := Except.ok.inj (hw'.symm.trans hw)
  exact placeOk_key (c := 0) (k := 5) (by decide) (key_sent (by decide)) hm.symm Q hQ
    (by rw [hs])

/-- **At every three public files in the scope of the goals**, from a planner that returns. -/
theorem k13_key_at_scope {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {p : Model.Verify.Planned} (hp : Model.Verify.planned Z.pol Z.KL (some Z.lay) = .ok p)
    (P : Where) (h1 : P.rows = p.chains.made.sized.key.ranges.pending)
    (h2 : P.lin = p.chains.made.sized.key.once.shape) (h3 : P.work = (0, 0, 0)) :
    K13Cond P p.chains.made.sized.key.codes dryKeyFull.1 18828 (K1.sentOf 0 0)[5]? := by
  rw [key_eq_at_scope hZ hp] at h1 h2 ⊢
  exact (k13_key P h1 h2 h3).1

end VerifiableInference.Desc.K13.Law
