-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/SeedsTData.lean: the seeds' protocol's data for whoever writes it into an
interface; the lane "bad y ρ" is a lane; its count from a probability.
Why: the clause of SeedLane | SeedFirstAsk | JudgeOff asks as hypotheses "the lane of T is OK" and
"its errors lie below εs".
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.
  dSeed e  the round, as a literal: entry e with work := 0, kind seeds, no item, no tree, no
      opening: so T's positions are empty, and its verifier's message is the kit's own type, by
      unfolding [at a round with a tree extST is the default everywhere; work 0 as a hypothesis is
      no unfolding]
  noPosT, embST, prjST, prjST_emb  T at dSeed e has no oracle position: the two ways of writing
      symbols are empty functions
  lane_stBad_ok  for any protocol with local rounds alone: the lane whose state is LaneStays' stBad
      bad obeys the laws of a lane, from the wiring's laws and CountOK (joint_stBad)
  kLast, countOK_of_pr  CountOK counts the last round's verifier messages: at a lawful wire these
      are hash blocks, not seeds (exactly uniform verifier messages hold with challenges as hash
      blocks alone: Run/PlanQSLaws.lean's head): so it is not coll_count (a count of seeds): it is
      the summand that carries the bias factor. For a shape of two rounds: from "for every string y
      and first message c₀: Pr over the second round's uniform verifier messages [bad y (c₀, c)] ≤
      p": CountOK at the errors (0, kLast) and Err.Below … p. kLast: the greatest such count (no
      floor of a real)
  oneAns_of_fam  a list all of whose entries are a family's answers has one answer a query: OneAns
      without Bad3's third disjunct (JudgeAtAsk hands that): either source serves

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.SeedsT

noncomputable section

namespace TypedOracleCompiler.Slice
open TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Compile.Batch Rom _root_.Compile Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

/-- The seeds' round, as a literal. -/
@[reducible] def dSeed (e : _root_.Fmt.Entry) : PQ.RD := ⟨{ e with work := 0 }, .seeds, [], [], []⟩

theorem noPosT (C : PQ.CK) (e : _root_.Fmt.Entry) (E : ExtSpec) :
    IsEmpty (OPos (seedsT C (dSeed e) E).shape) :=
  ⟨fun p => by rcases p with p | p | p <;> exact p.elim⟩

def embST {B : Type} (C : PQ.CK) (e : _root_.Fmt.Entry) (E : ExtSpec) :
    (p : OPos (seedsT C (dSeed e) E).shape) → OSym (seedsT C (dSeed e) E).shape p → B :=
  fun p => ((noPosT C e E).false p).elim

def prjST {B : Type} (C : PQ.CK) (e : _root_.Fmt.Entry) (E : ExtSpec) :
    (p : OPos (seedsT C (dSeed e) E).shape) → B → Option (OSym (seedsT C (dSeed e) E).shape p) :=
  fun p => ((noPosT C e E).false p).elim

theorem prjST_emb {B : Type} (C : PQ.CK) (e : _root_.Fmt.Entry) (E : ExtSpec)
    (p : OPos (seedsT C (dSeed e) E).shape)
    (a : OSym (seedsT C (dSeed e) E).shape p) : prjST (B := B) C e E p (embST C e E p a) = some a :=
  ((noPosT C e E).false p).elim

/-- The lane "bad y ρ" is a lane, for any protocol with local rounds alone. -/
theorem lane_stBad_ok {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X} {W : QueryLayout lam L} {t : Tag} {Y : Type}
    {E : ExtSpec} (P : InteractiveOracleProof Y E)
    {ws : RoundsQueryLayout lam W.K P.shape (RoundSplits.allLocal P.shape)}
    {prjS : (p : OPos P.shape) → Body L → Option (OSym P.shape p)}
    {prjP : PlainPart (shapeOf L t) (annOf L t) → Option (PlainPart P.shape (RoundSplits.allLocal P.shape))}
        {ε : Err P.shape}
    {bad : E.Str → Rho P.shape → Bool} {xout : Option X → Option Y}
        {extY : Tc W → List (Dig lam) → E.Str} {N : ℕ}
    (hws : RoundsQueryLayout.OKG P.shape (RoundSplits.allLocal P.shape) ws)
        (hcount : ∀ y, CountOK P.shape ε (bad y)) :
    (laneOf W t (BatchInteractiveOracleProof.ofProto P) ws prjS prjP ε (stBad bad) xout extY).OK N :=
  laneOf_ok hws fun y x => joint_stBad N P.shape ε bad hcount y x

/-- the greatest number of second messages that are bad, over all strings and first messages -/
def kLast {Str : Type} (r0 r1 : Round) (bad : Str → Rho [r0, r1] → Bool) : ℕ :=
  sSup {n | ∃ y c0, n = cnt fun c : r1.Chal => bad y (c0, c, ()) = true}

/-- The count from a probability. -/
theorem countOK_of_pr {Str : Type} (r0 r1 : Round) (bad : Str → Rho [r0, r1] → Bool) (p : ℝ≥0∞)
    (h : ∀ y c0, pr (unif r1.Chal) {c | bad y (c0, c, ()) = true} ≤ p) :
    (∀ y, CountOK [r0, r1] (0, kLast r0 r1 bad, ()) (bad y)) ∧
        Err.Below (s := [r0, r1]) (0, kLast r0 r1 bad, ()) p := by
  have hb : BddAbove {n | ∃ y c0, n = cnt fun c : r1.Chal => bad y (c0, c, ()) = true} :=
    ⟨Fintype.card r1.Chal, by rintro n ⟨y, c0, rfl⟩; exact cnt_le_card _⟩
  refine ⟨fun y c0 => le_csSup hb ⟨y, c0, rfl⟩, by simp, ?_, trivial⟩
  rcases Set.eq_empty_or_nonempty {n | ∃ y c0, n = cnt fun c : r1.Chal => bad y (c0, c, ()) = true}
      with he | hn
  · unfold kLast
    rw [he, csSup_empty]
    simp
  · obtain ⟨y, c0, e⟩ := Nat.sSup_mem hn hb
    unfold kLast
    rw [e]
    exact (pr_unif_le_iff _ p).1 (h y c0)

/-- a list all of whose entries are a family's answers has one answer a query -/
theorem oneAns_of_fam {S : OSpec} (F : Fam S) {tr : Trace S}
    (h : ∀ e ∈ tr, e.2.2 = F e.1 e.2.1) : OneAns tr :=
  fun _ _ _ _ ha hb => (h _ ha).trans (h _ hb).symm

end TypedOracleCompiler.Slice
