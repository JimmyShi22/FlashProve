-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Compile/Batch/LateX.lean: a second form of Compile/Batch/LateX.lean.

The files under OnBytes/TypedOracleCompiler/ (namespace `TypedOracleCompiler`) are a second form of the verifier's side of
the library's compiler and of its road to soundness. They stand beside the library's own files, with
five changes:
  (1) a query holds a list of roots, and a component of a round has a list of trees; the verifier
  takes, and the analysis counts, at most `maxRt` = 2 of them;
  (2) the body of a leaf of a tree over oracles is a type that the interface names (`BatchProtocolWithLeafBody.Bd`); the
  wire has functions that write a symbol into a body and read it back;
  (3) the input of a leaf of the request tree is the slot value and, behind it, a string that comes
  with the proof string (`OneProtocolProof.rsalt`);
  (4) a Fiat-Shamir query of the format (F5) holds no external roots;
  (5) Test and Link have annotations of their own (`BatchProtocolWithLeafBody.annT`, `BatchProtocolWithLeafBody.annL`: which of their rounds are
  shared), and the depth of a request tree goes by the protocol (`QueryLayout.depthReqT`, `depthReqL`,
  `depthReq`; `QueryLayout.dReq`).
The folder has the verifier's side alone: no prover and no completeness. Nothing here is on hiding.
The names are the library's: under `TypedOracleCompiler`, names such as `Iop.QueryLayout` or
`Compile.Batch.verifyB` mean this folder's declarations, not the library's. No theorem of this
folder carries a statement from one form to the other. In the comments, "here:" marks what is other
than in the library's file.

Comments apart, every declaration of this file has the text of Compile/Batch/LateX.lean; what it
means changes with the definitions that it names.

The rest of this head is the head of Compile/Batch/LateX.lean, to be read with these changes; the
files that it names under Iop/ and Compile/Batch/ are, where this folder has a file of that name,
this folder's.

Compile/Batch/LateX.lean: the request that the verifier's own chain holds, round by round.
Definitions and lemmas for Compile/Batch/Sound.lean.

The first query of a chain (`recomputeChain`, Compile/Batch/Verifier.lean) holds `L.early x`; the query (F2)
of the round `L.late` holds x ((F1) to (F5): the formats of a query's head, `Head`,
Compile/Batch/Oracles.lean). The event E'_S (`Lane.step`, Compile/Batch/Rooted.lean) judges a query
by the state function of the request that its chain holds so far (`lastX`,
Compile/Batch/Rooted.lean).

Here, for the queries of an accepting verifier, there are two parts, which Compile/Batch/Sound.lean
joins (`stays0`, `mem_of_accepted`):
  (1) under `LateIs`: this request is `L.early x` before the round `L.late` and x from that round on
      (`instX`, `lastX_of_lateIs`);
  (2) under `LateInv` (that round is one of the local rounds before the shared ones and not the
      first): the item of a round of the verifier's chain (`Item`, with its answer `Rec`,
      Compile/Batch/Rooted.lean: what the prover message of one round of a slot's transcript is read
      from) holds what the verifier writes in that round, and `LateInv` holds in the next round
      (`VStep.late_eq`, `VStep.lateInv`).
      Otherwise the round `L.late` is not treated here: (F1), (F3), (F4), (F5) have no field xl
      (`Head.late`); a local round (F2) after the shared ones has it.
  `LateIs`    the records and the current item hold, round by round, what the verifier writes
  `LateInv`   what is known of the phase and of the rounds to come, as long as the round `L.late`
              has not come
On a word. "Late" here is said of a request that enters a chain late. Compile/Batch/Late1.lean to
Late4.lean, LateG.lean, SpecLate.lean, HopLate.lean, PubLate.lean of that folder and
Rom/DeferLate.lean use the word of programs that name the input of a query only at its release; they
have nothing to do with this file.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.Chain
import Iop.Late

noncomputable section

namespace TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- the records from round i on, and the current item, hold the requests f i, f (i + 1), .. -/
def LateIs {K : ℕ} {t : Tag} (f : ℕ → Option X) : ℕ → List (Rec lam K L t) → Item lam L t → Prop
  | i, [], cur => cur.late = f i
  | i, rc :: l, cur => rc.1.late = f i ∧ LateIs f (i + 1) l cur

/-- The request that the chain of a verifier with the request xo holds after the query of round
i. -/
def instX (L : BatchProtocolWithLeafBody I X) (xo : Option X) (i : ℕ) : Option X :=
  match L.late with
  | some n => if n ≤ i then xo else xo.map L.early
  | none => xo.map L.early

theorem lastX_aux {K : ℕ} {t : Tag} (xo : Option X) : ∀ (l : List (Rec lam K L t))
        (cur : Item lam L t) (i : ℕ) (v : Option X),
      LateIs (fun k => lateInstancePart L k xo) i l cur →
    lastX v l cur = match L.late with
      | some n => if i ≤ n ∧ n ≤ i + l.length then xo.or v else v
      | none => v
  | [], cur, i, v, h => by
      show cur.late.or v = _
      rw [show cur.late = lateInstancePart L i xo from h]
      unfold lateInstancePart
      cases hl : L.late with
      | none => simp
      | some n =>
        by_cases hn : n = i
        · subst hn; simp
        · have h1 : ¬ (i ≤ n ∧ n ≤ i + ([] : List (Rec lam K L t)).length) := by
            simp only [List.length_nil]; omega
          simp only [Option.some.injEq, hn, if_false, h1, Option.none_or]
  | rc :: l, cur, i, v, h => by
      show lastX (rc.1.late.or v) l cur = _
      rw [lastX_aux xo l cur (i + 1) _ h.2, show rc.1.late = lateInstancePart L i xo from h.1]
      unfold lateInstancePart
      cases hl : L.late with
      | none => simp
      | some n =>
        by_cases hn : n = i
        · subst hn
          have h1 : ¬ (n + 1 ≤ n ∧ n ≤ n + 1 + l.length) := by omega
          have h2 : n ≤ n ∧ n ≤ n + (rc :: l).length := by simp
          simp only [if_true, h1, if_false, h2, and_self]
        · have h1 : (i + 1 ≤ n ∧ n ≤ i + 1 + l.length) ↔ (i ≤ n ∧ n ≤ i + (rc :: l).length) := by
            simp only [List.length_cons]; omega
          simp only [Option.some.injEq, hn, if_false, Option.none_or, h1]

/-- Under `LateIs`: the request that the verifier's chain holds is `instX`. -/
theorem lastX_of_lateIs {K : ℕ} {t : Tag} (xo : Option X) (l : List (Rec lam K L t))
    (cur : Item lam L t) (h : LateIs (fun k => lateInstancePart L k xo) 0 l cur) :
    lastX (xo.map L.early) l cur = instX L xo l.length := by
  rw [lastX_aux xo l cur 0 _ h]
  unfold instX
  cases L.late with
  | none => rfl
  | some n =>
    simp only [Nat.zero_le, true_and, Nat.zero_add]
    cases xo <;> rfl

/-- the slot's transcript with the records l is in the round number |l| -/
theorem idx_trOf {K : ℕ} {t : Tag} (tr : Trace (typedOracleFamily lam K L)) :
    ∀ (s : Shape) (A : RoundSplits s) (ws : RoundsQueryLayout lam K s A)
        (prjS : (p : OPos s) → Body L → Option (OSym s p))
        (prjP : PlainPart (shapeOf L t) (annOf L t) → Option (PlainPart s A)) (l : List (Rec lam K L t))
        (cur : Item lam L t) (τ : AtV s),
      trOf tr t s A ws prjS prjP l cur = some τ → τ.idx = l.length
  | [], _, _, _, _, _, _, τ, _ => τ.elim
  | _ :: _, (_, _), (w, _), prjS, prjP, [], cur, τ, h => by
      obtain ⟨m, -, rfl⟩ := Option.map_eq_some_iff.1
        (show (msgOf tr w (fun p => prjS (.inl p)) prjP cur).map Sum.inl = some τ from h)
      rfl
  | _ :: s, (_, A), (w, ws), prjS, prjP, rc :: rest, cur, τ, h => by
      obtain ⟨m, -, h1⟩ := Option.bind_eq_some_iff.1
        (show (msgOf tr w (fun p => prjS (.inl p)) prjP rc.1).bind _ = some τ from h)
      obtain ⟨τ', h2, rfl⟩ := Option.map_eq_some_iff.1 h1
      exact congrArg (· + 1) (idx_trOf tr s A ws _ _ rest cur τ' h2)

variable {W : QueryLayout lam L}

/-- As long as the round L.late has not come, that round is not the first, the chain is in its first
local rounds, and the rounds up to that one are local. (Asked only of a chain that has a request.)
-/
def LateInv (C : Ctx W) (i : ℕ) (ph : Phase lam) (s : Shape) (A : RoundSplits s) : Prop :=
  ∀ n, L.late = some n → C.x ≠ none → i ≤ n →
    0 < n ∧ ((i = 0 ∧ ph = .first) ∨ ∃ ρ, ph = .loc ρ) ∧ RoundSplits.LocalTo (n - i) s A

section Step
variable {C : Ctx W} {r : Round} {s : Shape} {a : RAnn r} {A : RoundSplits s}
  {embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L C.t) (annOf L C.t)} {i : ℕ} {pl : r.Plain}
  {ph ph₁ : Phase lam} {cur : Item lam L C.t} {ans : FsAns lam W.K} {rt : RtC lam × RtC lam}

/-- Under `LateInv`: the item of a round of the verifier's chain holds what the verifier writes in
that round. -/
theorem VStep.late_eq (hv : VStep C.tr C.cms C.x C.salt C.rtreq embP i pl ph cur ans ph₁ rt)
    (hI : LateInv C i ph (r :: s) (a, A)) : cur.late = lateInstancePart L i C.x := by
  have key : lateInstancePart L i C.x ≠ none → (∃ ρ, ph = .loc ρ) ∧ a.kind = .lo := by
    intro h
    unfold lateInstancePart at h
    split at h
    · rename_i hl
      obtain ⟨h0, h1, h2⟩ := hI i hl h le_rfl
      rw [Nat.sub_self] at h2
      rcases h1 with ⟨rfl, -⟩ | h1
      · exact absurd h0 (lt_irrefl _)
      · exact ⟨h1, h2⟩
    · exact absurd rfl h
  cases hv with
  | f1 root ans hk => exact Eq.symm (not_not.1 fun h => by obtain ⟨⟨ρ, h1⟩, -⟩ := key h; cases h1)
  | f2 ρ root ans hk => rfl
  | join ρ rtj rt0 c ans hk hg =>
      exact Eq.symm (not_not.1 fun h => by have := (key h).2; rw [hk] at this; cases this)
  | f5 ρ0 c root ans hk =>
      exact Eq.symm (not_not.1 fun h => by obtain ⟨⟨ρ, h1⟩, -⟩ := key h; cases h1)
  | f3 ρ0 c root ans hk =>
      exact Eq.symm (not_not.1 fun h => by obtain ⟨⟨ρ, h1⟩, -⟩ := key h; cases h1)
  | f2' ρ c root ans hk => rfl

theorem VStep.lateInv (hv : VStep C.tr C.cms C.x C.salt C.rtreq embP i pl ph cur ans ph₁ rt)
    (hI : LateInv C i ph (r :: s) (a, A)) : LateInv C (i + 1) ph₁ s A := by
  intro n hl hx hn
  obtain ⟨h0, h1, h2⟩ := hI n hl hx (Nat.le_of_succ_le hn)
  obtain ⟨k, hk⟩ : ∃ k, n - i = k + 1 := ⟨n - i - 1, by omega⟩
  rw [hk] at h2
  have hk' : n - (i + 1) = k := by omega
  rw [hk']
  refine ⟨h0, Or.inr ?_, h2.2⟩
  cases hv with
  | f1 root ans hk => exact ⟨_, rfl⟩
  | f2 ρ root ans hk => exact ⟨_, rfl⟩
  | join ρ rtj rt0 c ans hk hg => have := h2.1; rw [hk] at this; cases this
  | f5 ρ0 c root ans hk => rcases h1 with ⟨-, h⟩ | ⟨ρ, h⟩ <;> cases h
  | f3 ρ0 c root ans hk => rcases h1 with ⟨-, h⟩ | ⟨ρ, h⟩ <;> cases h
  | f2' ρ c root ans hk => rcases h1 with ⟨-, h⟩ | ⟨ρ, h⟩ <;> cases h

end Step

end TypedOracleCompiler.Compile.Batch
