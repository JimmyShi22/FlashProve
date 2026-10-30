-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/InOrderAtLater.lean: the table's test "in order" at a segment's later places:
four of its five conjuncts at the composed meaning (mgAll_inOrder_at, Johnson/Desc/Sound/MgAll.lean)
go from the chain's state in front of the place's block to the chain's state behind its yes.

  Later B own         the two blocks of these places, the digits' (K1.laterAt) and the reads'
                      (IM.k1Reads: K1.laterAt with a quiet block joined), each with K1's own block.
  EqsBAtLater         First.eqsB: the statement's codes, the request's shape, the rows' layout.
  ReqIsBAtLater       First.reqIsB: the request's words in the chain's state.
  InOrderK13AtLater   K13.Law.inOrderK13: "tidy", and the same three values.
  BackReqAtLater      the request file's bytes are a request's: it reads the public part alone.
  eqsBAtLater, reqIsBAtLater, inOrderK13AtLater, backReqAtLater   the four proofs.
  OrderSame, QuietC   what the blocks leave: the three values and the request; at the quiet block
                      the statement, the walk's own state of the calls and the request.

The first two hold at a yes on any rounds. THE THIRD WANTS TWO PREMISES MORE: K1's own block's test
on the plan has passed, and the rounds fit its declared ones, the decision being asked with their
digests struck: "tidy in front, tidy behind" goes through a sending only so (Keeps.Fits,
Johnson/Desc/Tidy/Fits.lean; K1.commitAtS_fits, Johnson/Desc/Tidy/K1Steps.lean).

It calls PlanSame, commitAtS_plan and inOrderK13_rides' (Johnson/Desc/K13/Law/InOrderRides.lean).

What is not claimed. The fifth conjunct, the base meaning's own "in order". That a description lays
these blocks at these places. That a test on the plan passes anywhere. Nothing on soundness, on an
honest prover or on hiding.

-/
import Johnson.Desc.K13.Law.InOrderRides
import Johnson.Desc.First.FillStart
import Johnson.Desc.First.FillReqIs
import Johnson.Desc.Tidy.Chains
import Johnson.Desc.K8.ReadsQuietLaws
import Johnson.Goal.Meaning.RecReadsAtt
import Johnson.Meaning.ReqBytes
import Johnson.IMR.K1Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Means (Tidy)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Law (PlanSame inOrderK13 inOrderK13_rides' commitAtS_plan)
open VerifiableInference.Desc.Ground (groundQuiet_tidy admitOn_tidy)
open OnBytes.Model.Stages (LinkH)
open IM (k1Reads k1Quiet)

variable {Cl : Type}

/-! ## 1 What "in order"'s conjuncts read, but for "tidy" -/

/-- The three values that "in order" holds against the plan stay, and the request in the chain's
state. -/
def OrderSame (s s' : S) : Prop := PlanSame s s' ∧ s'.req = s.req

theorem OrderSame.trans {a b c : S} (h : OrderSame a b) (k : OrderSame b c) : OrderSame a c :=
  ⟨h.1.trans k.1, k.2.trans h.2⟩

theorem putLink_req (s : S) (X : LinkCtx) : (s.putLink X).req = s.req := by
  unfold S.putLink
  split <;> first | rfl | (split <;> rfl)

theorem putFork_req (s : S) (X : Fork) : (s.putFork X).req = s.req := by
  unfold S.putFork
  split <;> first | rfl | (split <;> rfl)

/-- **A yes of a later moment's sending.** -/
theorem commitAtS_order (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (s s' : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s rs gs = .ok s') :
    OrderSame s s' := by
  refine ⟨commitAtS_plan P link moment arrays s rs gs s' h, ?_⟩
  obtain ⟨L, L', F', w, -, -, e⟩ := commitAtS_rec P link moment arrays s s' rs gs h
  rw [e, putFork_req, putLink_req]
  rfl

/-! ## 2 The quiet block behind the reads' sending -/

/-- The statement, the walk's own state of the calls and the request are left. -/
def QuietC (q : Block S Unit) : Prop :=
  ∀ s s' rs gs, q.decide s rs gs = .ok s' → s'.st = s.st ∧ s'.check = s.check ∧ s'.req = s.req

theorem quietC_layers (P : K8.ReadsQuiet.PG) : QuietC (K8.ReadsQuiet.layers P) := by
  intro s s' rs gs h
  have f := K8.ReadsQuiet.layers_frame h
  exact ⟨f.2.2.1, f.2.2.2.2.2.1, f.2.2.2.2.2.2.2⟩

theorem quietC_head (P : K8.ReadsQuiet.PH) : QuietC (K8.ReadsQuiet.head P) := by
  intro s s' rs gs h
  have f := K8.ReadsQuiet.head_frame h
  exact ⟨f.2.2.1, f.2.2.2.2.2.1, f.2.2.2.2.2.2.2⟩

theorem quietC_att {W : Verify.Public} {l g : Nat} {q : Block S Unit}
    (hq : First.Att.readsAtO W l g = some q) : QuietC q := by
  unfold First.Att.readsAtO at hq
  obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 hq
  intro s s' rs gs h
  obtain ⟨a, t, tl, ha, rfl⟩ := Meaning.K2.readsAtSO_eq h
  exact ⟨rfl, rfl, rfl⟩

theorem quietC_blockAt {G : Array Layer.HPlan2} {hS : Head.Shape} {HLy : Head.HL}
    {H : Head.HPlanH2} {kinds : List (Nat × Nat)} {l : Nat} {q : Block S Unit}
    (h : K8.ReadsQuiet.blockAt G hS HLy H kinds l = some q) : QuietC q := by
  unfold K8.ReadsQuiet.blockAt at h
  obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · obtain ⟨hp, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact quietC_layers _
  · split at h
    · obtain rfl := Option.some.inj h
      exact quietC_head _
    · cases h

theorem quietC_readsQuietAt {G : ProofFile.Ground} (l : Nat) (X : LinkH) (piece : Nat) (q : Block S Unit)
    (h : ProofFile.readsQuietAt G l X piece = some q) : QuietC q := by
  unfold ProofFile.readsQuietAt at h
  by_cases h1 : (X.kind == 1) = true
  · rw [if_pos h1] at h
    by_cases h2 : (piece == 4) = true
    · rw [if_pos h2] at h
      exact quietC_att h
    · rw [if_neg h2] at h
      cases h
  · rw [if_neg h1] at h
    by_cases h2 : (piece == (if X.kind == 0 then 4 else 5)) = true
    · rw [if_pos h2] at h
      exact quietC_blockAt h
    · rw [if_neg h2] at h
      cases h

theorem quietC_k1Quiet (G : ProofFile.Ground) (l : Nat) (X : LinkH) : QuietC (k1Quiet G l X) := by
  unfold k1Quiet
  dsimp only
  cases hq : ProofFile.readsQuietAt G l X (if X.kind == 0 || X.kind == 1 then 4 else 5) with
  | none => exact fun s s' rs gs h => nomatch h
  | some q => exact quietC_readsQuietAt l X _ q hq

/-- A yes of the reads' place's block is a yes of K1's own block, then one of the quiet block. -/
theorem k1Reads_parts (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (X : LinkH) (pr : ℕ)
    (reads : Option (List ℕ)) (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (k1Reads Z G l X pr reads).decide s rs gs = .ok s') :
    ∃ s₁ gs₁, (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).decide s
        (rs.take (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).rounds.length) gs₁ =
          .ok s₁ ∧ s'.st = s₁.st ∧ s'.check = s₁.check ∧ s'.req = s₁.req := by
  have h' : ((laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).decide s
      (rs.take (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).rounds.length)
      (gs.take (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).openings)).bind (fun s₁ =>
      (k1Quiet G l X).decide s₁
        (rs.drop (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).rounds.length)
        (gs.drop (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).openings)) = .ok s' := h
  obtain ⟨s₁, h1, h2⟩ := (bind_ok _ _ _).1 h'
  exact ⟨s₁, _, h1, quietC_k1Quiet G l X _ _ _ _ h2⟩

theorem k1Reads_order (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (X : LinkH) (pr : ℕ)
    (reads : Option (List ℕ)) (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (k1Reads Z G l X pr reads).decide s rs gs = .ok s') : OrderSame s s' := by
  obtain ⟨s₁, gs₁, h1, e1, e2, e3⟩ := k1Reads_parts Z G l X pr reads s s' rs gs h
  exact (commitAtS_order _ l 1 reads s s₁ _ gs₁ h1).trans
    ⟨PlanSame.of_check (by rw [e1]) e2, e3⟩

/-! ## 3 The statements -/

/-- The two blocks of a segment's later places, the digits' and the reads', each with K1's own block
in it. -/
inductive Later : Block S Unit → Block S Unit → Prop
  | digits (q : Params.First) (gp : GPar) (l piece : Nat) (digits : Option (List Nat)) :
      Later (laterAt q gp l piece 2 digits) (laterAt q gp l piece 2 digits)
  | reads (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (X : LinkH) (pr : ℕ) (reads : Option (List ℕ)) :
      Later (k1Reads Z G l X pr reads) (laterAt G.first (gpOf Z) l pr 1 reads)

/-- **F2a.** At a yes on any rounds. -/
def EqsBAtLater : Prop :=
  ∀ (B own : Block S Unit), Later B own → ∀ (cs : Codes) (sh : Params.ReqShape)
    (ly : Params.ReqLayout) (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
    B.decide s rs gs = .ok s' → First.eqsB cs sh ly s = true → First.eqsB cs sh ly s' = true

/-- **F2b.** At a yes on any rounds. -/
def ReqIsBAtLater : Prop :=
  ∀ (B own : Block S Unit), Later B own → ∀ (ws : Array UInt32) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))),
    B.decide s rs gs = .ok s' → First.reqIsB ws s = true → First.reqIsB ws s' = true

/-- **F2c.** WITH TWO PREMISES MORE THAN A BARE YES: K1's own block's test on the plan has passed,
and the rounds fit its declared ones, the decision being asked with their digests struck: "tidy"
goes through a sending only so (Keeps.Fits). -/
def InOrderK13AtLater : Prop :=
  ∀ (B own : Block S Unit), Later B own → own.planOk = true →
    ∀ (cs : Codes) (sh : Params.ReqShape) (ly : Params.ReqLayout) (s s' : S) (rs : List Fmt.RoundView)
      (gs : List (List (Nat × List UInt64))),
    roundsFit own.rounds rs = true → B.decide s (rs.map noDigest) gs = .ok s' →
    inOrderK13 cs sh ly s = true → inOrderK13 cs sh ly s' = true

/-- **F2d.** It reads the public part alone, which a step leaves. -/
def BackReqAtLater : Prop :=
  ∀ {Pp : Type} (reqB : Pp → ByteArray) (x x' : Pp × S), x'.1 = x.1 →
    (_root_.Meaning.backReq (reqB x.1)).isSome = true →
    (_root_.Meaning.backReq (reqB x'.1)).isSome = true

/-! ## 4 The proofs -/

theorem later_order {B own : Block S Unit} (hB : Later B own) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : B.decide s rs gs = .ok s') :
    OrderSame s s' := by
  cases hB with
  | digits q gp l piece digits => exact commitAtS_order _ l 2 digits s s' _ gs h
  | reads Z G l X pr reads => exact k1Reads_order Z G l X pr reads s s' rs gs h

theorem eqsBAtLater : EqsBAtLater := by
  intro B own hB cs sh ly s s' rs gs h h0
  obtain ⟨⟨a, b, c⟩, -⟩ := later_order hB s s' rs gs h
  unfold First.eqsB at h0 ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h0 ⊢
  exact ⟨⟨a.trans h0.1.1, b.trans h0.1.2⟩, c.trans h0.2⟩

theorem reqIsBAtLater : ReqIsBAtLater := by
  intro B own hB ws s s' rs gs h h0
  have e := (later_order hB s s' rs gs h).2
  unfold First.reqIsB at h0 ⊢
  simp only [decide_eq_true_eq] at h0 ⊢
  exact e.trans h0

theorem inOrderK13AtLater : InOrderK13AtLater := by
  intro B own hB hplan cs sh ly s s' rs gs hfit h h0
  refine inOrderK13_rides' ?_ (later_order hB s s' _ gs h).1 h0
  cases hB with
  | digits q gp l piece digits =>
    exact commitAtS_fits groundQuiet_tidy admitOn_tidy _ l 2 digits hplan s rs gs s' hfit h
  | reads Z G l X pr reads =>
    obtain ⟨s₁, gs₁, h1, e1, -, -⟩ := k1Reads_parts Z G l X pr reads s s' _ gs h
    have e : (rs.map noDigest).take
        (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).rounds.length =
        rs.map noDigest := by
      refine List.take_of_length_le (Nat.le_of_eq ?_)
      rw [List.length_map]
      exact Keeps.fit_length _ _ hfit
    rw [e] at h1
    rw [e1]
    exact commitAtS_fits groundQuiet_tidy admitOn_tidy _ l 1 reads hplan s rs gs₁ s₁ hfit h1

theorem backReqAtLater : BackReqAtLater := by
  intro Pp reqB x x' e h
  rw [e]
  exact h

end VerifiableInference.Desc.K1
