-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/ReadsAttAtHead.lean: K1's COMMITMENT TO THE READS WITH THE QUIET STEP BEHIND
IT, AT THE TWELVE ATTENTION LINKS (the members 14 (2 g + 1) + 5 of the flat list, g < 12) AT THEIR
SEATS IN THE PROOF FILE's OWN FIRST CHAIN: each member has one step on the chain's shape, with both
laws at the seated block's own decision, its declared rounds, and the makes of the rows behind it.
Under the head P5J.AtMgA; a joining of laws; nothing is evaluated.
  1 `readsAtt_keeps`: the quiet step's return (First.Att.readsAtSO,
    Johnson/Desc/First/Att/ReadsO.lean) leaves the mark of failure, what goes out and the statement.
  2 `readsAttGS P link arrays A`: the step at the seat: no mark; the commitment's step (commitG,
    Johnson/Desc/First/Shape/Commit.lean); then, where another house's test on the shape passes
    (tabsGC A, Johnson/Desc/K5/Honest/Law/TabsChain.lean), the quiet step at the plan's own list of
    the tables' shapes (attG (some (attFuns A)), Johnson/Desc/First/Att/ReadsOShape.lean).
    `quiet_att`, `quiet_att_rounds`: what the lot joins behind the commitment at an attention link;
    it has no round.
  **`reads_att_at`** (g < 12): with Bs what the maker's own ProofFile.baseOf returns, Xl the link 2 g + 1
    of Bs.G₀.built, reads off K1.linkNumbers, A := Bs.G₀.W.A[g], P := K1.parLater Bs.G₀.first
    (K1.gpOf Zp) (2 g + 1) 4 1: the member b at number 14 (2 g + 1) + 3 + 2 of cF.blocksInOrder: b.rounds =
    K1.rounds P; behind a yes on two rounds formsOf t.st = sendForms P ‹the number of messages in
    front› (formsOf s.st); at the step readsAttGS P (2 g + 1) reads A: where b says yes and the step
    returns, it returns the shape behind; and where the step returns, b says yes on two rounds in
    which no seed's factor is 0 and round 2 holds as many answers as the place counts, IF the test
    on values (valsTS A) passes at the state that the commitment returns on these
    rounds and on what is shown to it. EVERY PARAMETER OF THE STEP IS TIED TO A VALUE.
By IM.k1_reads_of (Johnson/IMR/K1Scope.lean), IM.ground_named (Johnson/IMR/PureJoin.lean),
Meaning.scope_plans (Johnson/Goal/Meaning/PlanShapes.lean), IM.yes_alone, IM.alone_rounds,
IM.hear_at_flat, IM.flatIx_scope; commit_carries | commit_returns (Commit.lean); commit_keeps
(DigitsAtHead.lean); commit_forms (ChainF.lean); another house's reads_carries | reads_returns
(TabsChain.lean).
Limits. "Carries" is under the step's own return. "RETURNS" TAKES, BESIDE THE TWO PREMISES ON THE
ROUNDS, ONE NAMED TEST ON VALUES AT A STATE IN THE MIDDLE OF THE MEMBER's RUN (valsTS A at what the
commitment returns): a payer must first know that state. tabsGC is enough, not shown to be needed:
the step may refuse where the member says yes. UNDER THE HEAD: that it has a member is shown in
scope, where the reader returns and `protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean);
that these three hold together, at two named sets of public files (`VerifierAndGoals.storedPublicFiles` and
`VerifierAndGoals.zGap`), in a side library (AtFullSide/Top/HeadMemberAtFull.lean, HeadMemberAtGap.lean). Of
the head the proof spends h.scope, h.reads and h.laid.opened alone. That reads is some list is not
said: at none the commitment's step never returns (commitStepG, Commit.lean), and the two laws on
the step then say nothing: their premise "the step returns" is never met. No state is shown by a
theorem at which the step returns. At the earlier hash OnBytes.secondHashFunction. Nothing on soundness,
completeness or hiding.
Terms: lean/GLOSSARY.md.
-/
import Johnson.AtFull.Shape.DigitsAtHead
import Johnson.Desc.First.Shape.ChainF
import Johnson.Desc.K5.Honest.Law.TabsChain
import Johnson.Goal.Meaning.PlanShapes
import Johnson.Goal.Meaning.PlanNames
import Johnson.IMR.K1Scope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link KindName K1.commitAtS)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.First.Att (readsAtSO readsAtO attG)
open H2K5.Honest (tabsGC valsTS attFuns reads_carries reads_returns)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)

/-! ## 1 What the quiet step leaves -/

/-- The quiet step's return leaves the mark of failure, what goes out and the statement. -/
theorem readsAtt_keeps {A : Attention.Plan} {s t : S} (h : readsAtSO A s = .ok t) :
    t.failed = s.failed ∧ t.out = s.out ∧ t.st = s.st := by
  unfold readsAtSO at h
  dsimp only at h
  split at h
  · rename_i a ha
    obtain ⟨hh, -, h⟩ := OnBytes.Params.exc_bind h
    obtain ⟨g, -, h⟩ := OnBytes.Params.exc_bind h
    obtain ⟨r, -, h⟩ := OnBytes.Params.exc_bind h
    obtain rfl := Except.ok.inj h
    exact ⟨rfl, rfl, rfl⟩
  · cases h

/-! ## 2 The reads' member at an attention link -/

/-- **The step at the seat**: no mark; the commitment to the reads (commitG,
Johnson/Desc/First/Shape/Commit.lean); then, where another house's test on the shape passes (tabsGC,
Johnson/Desc/K5/Honest/Law/TabsChain.lean), the quiet step at the plan's own list of the tables'
shapes (attG (some (attFuns A)), Johnson/Desc/First/Att/ReadsOShape.lean). -/
def readsAttGS (P : VerifiableInference.Desc.K1.Par) (link : Nat) (arrays : Option (List Nat))
    (A : Attention.Plan) (a : ChainSh) : Option ChainSh :=
  if a.marked then none
  else (commitG P link 1 arrays a).bind fun m =>
    if tabsGC A m then attG (some (attFuns A)) m else none

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- What the lot joins behind the reads' commitment at an attention link. -/
theorem quiet_att {G : ProofFile.Ground} {l g : Nat} {X : Stages.LinkH} {A : Attention.Plan}
    (hk : X.kind = 1) (hg : X.g = g) (hA : G.W.A[g]? = some A) (s : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    (IM.k1Quiet G l X).decide s rs gs = readsAtSO A s := by
  unfold IM.k1Quiet ProofFile.readsQuietAt readsAtO
  simp [hk, hg, hA, ProofFile.orLoud]

theorem quiet_att_rounds {G : ProofFile.Ground} {l g : Nat} {X : Stages.LinkH} {A : Attention.Plan}
    (hk : X.kind = 1) (hg : X.g = g) (hA : G.W.A[g]? = some A) : (IM.k1Quiet G l X).rounds = [] :=
        by
  unfold IM.k1Quiet ProofFile.readsQuietAt readsAtO
  simp [hk, hg, hA, ProofFile.orLoud]

theorem reads_att_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (g : Nat) (hg : g < 12) :
    ∃ (Bs : ProofFile.PureBase) (Xl : Stages.LinkH) (pd : Nat) (reads digits : Option (List Nat))
      (A : Attention.Plan) (b : Block S ProofFile.Cl),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      Bs.G₀.built[2 * g + 1]? = some Xl ∧
      VerifiableInference.Desc.K1.linkNumbers Bs.G₀ Xl = some (4, pd, reads, digits) ∧
      Bs.G₀.W.A[g]? = some A ∧
      cF.blocksInOrder[14 * (2 * g + 1) + 3 + 2]? = some b ∧
      b.rounds = VerifiableInference.Desc.K1.rounds (VerifiableInference.Desc.K1.parLater
        Bs.G₀.first (VerifiableInference.Desc.K1.gpOf Zp) (2 * g + 1) 4 1) ∧
      (∀ s r₁ r₂ gs t, b.decide s [r₁, r₂] gs = .ok t →
        formsOf t.st = sendForms (VerifiableInference.Desc.K1.parLater Bs.G₀.first
          (VerifiableInference.Desc.K1.gpOf Zp) (2 * g + 1) 4 1)
          (chainSh s).core.st.oracles.length (formsOf s.st)) ∧
      (∀ s rs gs t u, b.decide s rs gs = .ok t →
        readsAttGS (VerifiableInference.Desc.K1.parLater Bs.G₀.first
          (VerifiableInference.Desc.K1.gpOf Zp) (2 * g + 1) 4 1) (2 * g + 1) reads A
          (chainSh s) = some u → u = chainSh t) ∧
      ∀ s r₁ r₂ gs u,
        readsAttGS (VerifiableInference.Desc.K1.parLater Bs.G₀.first
          (VerifiableInference.Desc.K1.gpOf Zp) (2 * g + 1) 4 1) (2 * g + 1) reads A
          (chainSh s) = some u →
        (∀ y ∈ VerifiableInference.Desc.K1.seedsOf (VerifiableInference.Desc.K1.parLater Bs.G₀.first
          (VerifiableInference.Desc.K1.gpOf Zp) (2 * g + 1) 4 1) r₁, isZeroE y.2 = false) →
        (VerifiableInference.Desc.K1.answersIn r₂).length =
          (VerifiableInference.Desc.K1.parLater Bs.G₀.first (VerifiableInference.Desc.K1.gpOf Zp)
            (2 * g + 1) 4 1).answers →
        (∀ m, (K1.commitAtS (Cl := Unit) (VerifiableInference.Desc.K1.parLater Bs.G₀.first
          (VerifiableInference.Desc.K1.gpOf Zp) (2 * g + 1) 4 1) (2 * g + 1) 1 reads).decide s
          [r₁, r₂] (gs.take (K1.commitAtS (Cl := Unit) (VerifiableInference.Desc.K1.parLater
            Bs.G₀.first (VerifiableInference.Desc.K1.gpOf Zp) (2 * g + 1) 4 1) (2 * g + 1) 1
            reads).openings) = .ok m → valsTS A m = true) →
        ∃ t, b.decide s [r₁, r₂] gs = .ok t := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hl : 2 * g + 1 < 25 := by omega
  have hix : IM.k1Ix (2 * g + 1) false = 3 := by
    show 3 + (if 2 * g + 1 = 24 then 1 else 0) = 3
    rw [if_neg (by omega)]
  obtain ⟨Lk, b, Xl, pd, reads, digits, eL, eb, hX, hn, la⟩ :=
    IM.k1_reads_of h.scope h.reads O (2 * g + 1) hl
  rw [hix] at eb hn la
  obtain ⟨nam, -⟩ := IM.ground_named h.scope h.reads O.pub O.blank
  obtain ⟨-, m', -, -, -, -, fm, km, gm, -⟩ := nam g hg
  obtain rfl : m' = Xl := Option.some.inj (fm.symm.trans hX)
  obtain ⟨A, hA, -⟩ := (Meaning.scope_plans h.scope h.reads O.public).2.2.2 g hg
  have hy := IM.yes_alone la (by intro k; cases k)
  have q := IM.hear_at_flat eL eb
  rw [IM.flatIx_scope h.scope h.reads O (by omega : 2 * g + 1 ≤ 24) 3] at q
  have hdec : ∀ s t rs gs, (IM.k1Reads Zp Bs.G₀ (2 * g + 1) m' 4 reads).decide s rs gs = .ok t ↔
      ∃ m, (K1.commitAtS (Cl := Unit) (VerifiableInference.Desc.K1.parLater Bs.G₀.first
          (VerifiableInference.Desc.K1.gpOf Zp) (2 * g + 1) 4 1) (2 * g + 1) 1 reads).decide s
          (rs.take 2) (gs.take (K1.commitAtS (Cl := Unit) (VerifiableInference.Desc.K1.parLater
            Bs.G₀.first (VerifiableInference.Desc.K1.gpOf Zp) (2 * g + 1) 4 1) (2 * g + 1) 1
            reads).openings) = .ok m ∧ readsAtSO A m = .ok t := by
    intro s t rs gs
    unfold IM.k1Reads
    refine (VerifiableInference.Desc.K1.bind_ok _ _ _).trans ?_
    constructor
    · rintro ⟨m, h1, h2⟩
      rw [quiet_att km gm hA] at h2
      exact ⟨m, h1, h2⟩
    · rintro ⟨m, h1, h2⟩
      refine ⟨m, h1, ?_⟩
      rw [quiet_att km gm hA]
      exact h2
  generalize (K1.commitAtS (Cl := Unit) (VerifiableInference.Desc.K1.parLater Bs.G₀.first
    (VerifiableInference.Desc.K1.gpOf Zp) (2 * g + 1) 4 1) (2 * g + 1) 1
    reads).openings = n at hdec ⊢
  have hrd : b.rounds = VerifiableInference.Desc.K1.rounds (VerifiableInference.Desc.K1.parLater
      Bs.G₀.first (VerifiableInference.Desc.K1.gpOf Zp) (2 * g + 1) 4 1) := by
    rw [IM.alone_rounds la]
    show (IM.k1Reads Zp Bs.G₀ (2 * g + 1) m' 4 reads).rounds = _
    unfold IM.k1Reads
    show _ ++ (IM.k1Quiet Bs.G₀ (2 * g + 1) m').rounds = _
    rw [quiet_att_rounds km gm hA]
    exact List.append_nil _
  refine ⟨Bs, m', pd, reads, digits, A, b, O.made, hX, hn, hA, q, hrd,
    fun s r₁ r₂ gs t hd => ?_,
    fun s rs gs t u hd hg' => ?_, fun s r₁ r₂ gs u hg' hz hnn hv => ?_⟩
  · obtain ⟨m, h1, h2⟩ := (hdec s t [r₁, r₂] gs).1 ((hy s t [r₁, r₂] gs).1 hd).1
    rw [(readsAtt_keeps h2).2.2]
    exact commit_forms h1
  · obtain ⟨m, h1, h2⟩ := (hdec s t rs gs).1 ((hy s t rs gs).1 hd).1
    unfold readsAttGS at hg'
    split at hg'
    · cases hg'
    · obtain ⟨mm, hm', hu⟩ := Option.bind_eq_some_iff.1 hg'
      obtain rfl := commit_carries h1 hm'
      split at hu
      · rename_i hG
        rw [reads_carries A h2 hG] at hu
        exact (Option.some.inj hu).symm
      · cases hu
  · unfold readsAttGS at hg'
    split at hg'
    · cases hg'
    · rename_i hm
      obtain ⟨mm, hm', hu⟩ := Option.bind_eq_some_iff.1 hg'
      obtain ⟨m, hd, em⟩ := commit_returns (gs := gs.take n) hm' hz hnn
      split at hu
      · rename_i hG
        rw [← em] at hG hu
        obtain ⟨t, ht, -⟩ := reads_returns A hG hu (hv m hd)
        obtain ⟨k1, k2⟩ := commit_keeps hd
        obtain ⟨j1, j2, -⟩ := readsAtt_keeps ht
        have hf : s.failed = none := by
          have h1 : (chainSh s).marked = false := by simpa using hm
          have h2 : s.failed.isSome = false := h1
          simpa using h2
        refine ⟨t, (hy s t [r₁, r₂] gs).2 ⟨(hdec s t [r₁, r₂] gs).2 ⟨m, hd, ht⟩,
          j1.trans (k1.trans hf), ?_⟩⟩
        unfold ProofFile.sameReply
        rw [j2, k2]
        exact beq_self_eq_true _
      · cases hu

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.readsAtt_keeps
#print axioms Johnson.AtFull.Shape.quiet_att
#print axioms Johnson.AtFull.Shape.reads_att_at
#print axioms Johnson.AtFull.Shape.readsAttGS
#print axioms Johnson.AtFull.Shape.quiet_att_rounds
