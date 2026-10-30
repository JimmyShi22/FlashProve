-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/ReadsHeadAtHead.lean: K1's COMMITMENT TO THE READS WITH THE QUIET STEP BEHIND
IT, AT THE HEAD's LINK (member 342 of the flat list) AT ITS SEAT IN THE PROOF FILE's OWN FIRST
CHAIN: the member has one step on the chain's shape, with both laws at the seated block's own
decision, its declared rounds, and the makes of the rows behind it. Under the head P5J.AtMgA; a
joining of laws; nothing is evaluated.
  `headQuiet_keeps`: the quiet step's yes (K8.ReadsQuiet.head, Johnson/Desc/K8/ReadsQuiet.lean)
    leaves the mark of failure, what goes out and the statement.
  `readsHeadGS P arrays Q`: the step at the seat: no mark; the commitment's step (commitG,
    Johnson/Desc/First/Shape/Commit.lean); then the quiet step on the shape alone (headReadsG Q,
    Johnson/Desc/K8/ReadsQuietHeadTables.lean). `quiet_head`: what the lot joins behind the
    commitment at the head's link.
  **`reads_head_at`**: with Bs what the maker's own ProofFile.baseOf returns, Xl the link 24 of
    Bs.G₀.built, reads off K1.linkNumbers, P := K1.parLater Bs.G₀.first (K1.gpOf Zp) 24 5 1: the
    member b at number 342 of cF.blocksInOrder: b.rounds = K1.rounds P; behind a yes on two rounds formsOf
    t.st = sendForms P ‹the number of messages in front› (formsOf s.st); at the step readsHeadGS P
    reads ⟨⟨1, some 24, 5, .K1⟩, Bs.G₀.W.hS, Bs.G₀.W.HLy, Bs.G₀.W.H⟩: where b says yes and the step
    returns, it returns the shape behind; and where the step returns, b says yes on two rounds in
    which no seed's factor is 0 and round 2 holds as many answers as the place counts, IF the
    covered positions can be said at the state that the commitment returns on these rounds and on
    what is shown to it. EVERY PARAMETER OF THE STEP IS TIED TO A VALUE.
By IM.k1_reads_of (Johnson/IMR/K1Scope.lean), IM.ground_named (Johnson/IMR/PureJoin.lean),
IM.yes_alone, IM.alone_rounds, IM.hear_at_flat, IM.flatIx_scope; commit_carries | commit_returns
(Commit.lean); commit_keeps (DigitsAtHead.lean); commit_forms (ChainF.lean); headReads_carries |
headReads_returns (ReadsQuietHeadTables.lean).
Limits. "Carries" is under the step's own return (the commitment's half; the quiet half is strong).
"RETURNS" TAKES, BESIDE THE TWO PREMISES ON THE ROUNDS, ONE PREMISE ON A STATE IN THE MIDDLE OF THE
MEMBER's RUN, BEYOND ITS SHAPE: S.covered returns there (four tests on the request's words and the
heard reply's token). UNDER THE HEAD: that it has a member is shown in scope, where the reader
returns and `protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold
together, at two named sets of public files (`VerifierAndGoals.storedPublicFiles` and `VerifierAndGoals.zGap`), in a side library
(AtFullSide/Top/HeadMemberAtFull.lean, HeadMemberAtGap.lean). Of the head the proof spends h.scope,
h.reads and h.laid.opened alone. That reads is some list is not said: at none the commitment's step
never returns (commitStepG, Commit.lean), and the two laws on the step then say nothing: their
premise "the step returns" is never met. No state is shown by a theorem at which the step returns.
At the earlier hash OnBytes.secondHashFunction. Nothing on soundness, completeness or hiding.
Terms: lean/GLOSSARY.md.
-/
import Johnson.AtFull.Shape.DigitsAtHead
import Johnson.Desc.First.Shape.ChainF
import Johnson.Desc.K8.ReadsQuietHeadTables
import Johnson.IMR.K1Scope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link KindName K1.commitAtS)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.K8.ReadsQuiet (head PH headReadsG headReads_carries headReads_returns)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)

/-- The quiet step's yes leaves the mark of failure, what goes out and the statement. -/
theorem headQuiet_keeps {P : PH} {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (head P).decide s rs gs = .ok t) :
    t.failed = s.failed ∧ t.out = s.out ∧ t.st = s.st := by
  unfold head at h
  dsimp only at h
  split at h
  · rename_i a ha
    obtain ⟨_, -, h⟩ := VerifiableInference.Desc.K8.ReadsQuiet.bind_ok h
    obtain ⟨cov, -, h⟩ := VerifiableInference.Desc.K8.ReadsQuiet.bind_ok h
    obtain ⟨x, -, h⟩ := VerifiableInference.Desc.K8.ReadsQuiet.bind_ok h
    obtain ⟨tt, -, h⟩ := VerifiableInference.Desc.K8.ReadsQuiet.bind_ok h
    obtain ⟨tl, -, h⟩ := VerifiableInference.Desc.K8.ReadsQuiet.bind_ok h
    obtain rfl := Except.ok.inj h
    exact ⟨rfl, rfl, rfl⟩
  · cases h

/-- **The step at the seat**: no mark; the commitment to the reads (commitG,
Johnson/Desc/First/Shape/Commit.lean), AT LINK 24 AND MOMENT 1: these two are typed into this text;
then the quiet step on the shape alone (headReadsG, Johnson/Desc/K8/ReadsQuietHeadTables.lean). -/
def readsHeadGS (P : VerifiableInference.Desc.K1.Par) (arrays : Option (List Nat)) (Q : PH)
    (a : ChainSh) : Option ChainSh :=
  if a.marked then none else (commitG P 24 1 arrays a).bind (headReadsG Q)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- What the lot joins behind the reads' commitment at the head's link. -/
theorem quiet_head {G : ProofFile.Ground} {X : Stages.LinkH} (hX : G.built[24]? = some X)
    (hk : X.kind = 2) :
    IM.k1Quiet G 24 X = head ⟨⟨1, some 24, 5, .K1⟩, G.W.hS, G.W.HLy, G.W.H⟩ := by
  unfold IM.k1Quiet ProofFile.readsQuietAt VerifiableInference.Desc.K8.ReadsQuiet.blockAt
  have e : (G.built.toList.map fun Y => (Y.kind, Y.g))[24]? = some (2, X.g) := by
    rw [List.getElem?_map, Array.getElem?_toList, hX, ← hk]
    rfl
  simp [hk, e, ProofFile.orLoud]

theorem reads_head_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ (Bs : ProofFile.PureBase) (Xl : Stages.LinkH) (pd : Nat) (reads digits : Option (List Nat))
      (b : Block S ProofFile.Cl),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      Bs.G₀.built[24]? = some Xl ∧
      VerifiableInference.Desc.K1.linkNumbers Bs.G₀ Xl = some (5, pd, reads, digits) ∧
      cF.blocksInOrder[342]? = some b ∧
      b.rounds = VerifiableInference.Desc.K1.rounds (VerifiableInference.Desc.K1.parLater
        Bs.G₀.first (VerifiableInference.Desc.K1.gpOf Zp) 24 5 1) ∧
      (∀ s r₁ r₂ gs t, b.decide s [r₁, r₂] gs = .ok t →
        formsOf t.st = sendForms (VerifiableInference.Desc.K1.parLater Bs.G₀.first
          (VerifiableInference.Desc.K1.gpOf Zp) 24 5 1)
          (chainSh s).core.st.oracles.length (formsOf s.st)) ∧
      (∀ s rs gs t u, b.decide s rs gs = .ok t →
        readsHeadGS (VerifiableInference.Desc.K1.parLater Bs.G₀.first
          (VerifiableInference.Desc.K1.gpOf Zp) 24 5 1) reads
          ⟨⟨1, some 24, 5, .K1⟩, Bs.G₀.W.hS, Bs.G₀.W.HLy, Bs.G₀.W.H⟩
          (chainSh s) = some u → u = chainSh t) ∧
      ∀ s r₁ r₂ gs u,
        readsHeadGS (VerifiableInference.Desc.K1.parLater Bs.G₀.first
          (VerifiableInference.Desc.K1.gpOf Zp) 24 5 1) reads
          ⟨⟨1, some 24, 5, .K1⟩, Bs.G₀.W.hS, Bs.G₀.W.HLy, Bs.G₀.W.H⟩
          (chainSh s) = some u →
        (∀ y ∈ VerifiableInference.Desc.K1.seedsOf (VerifiableInference.Desc.K1.parLater Bs.G₀.first
          (VerifiableInference.Desc.K1.gpOf Zp) 24 5 1) r₁, isZeroE y.2 = false) →
        (VerifiableInference.Desc.K1.answersIn r₂).length =
          (VerifiableInference.Desc.K1.parLater Bs.G₀.first (VerifiableInference.Desc.K1.gpOf Zp)
            24 5 1).answers →
        (∀ m, (K1.commitAtS (Cl := Unit) (VerifiableInference.Desc.K1.parLater Bs.G₀.first
          (VerifiableInference.Desc.K1.gpOf Zp) 24 5 1) 24 1 reads).decide s [r₁, r₂]
          (gs.take (K1.commitAtS (Cl := Unit) (VerifiableInference.Desc.K1.parLater Bs.G₀.first
            (VerifiableInference.Desc.K1.gpOf Zp) 24 5 1) 24 1 reads).openings) = .ok m →
          (m.covered Bs.G₀.W.hS.T Bs.G₀.W.hS.V).toOption.isSome = true) →
        ∃ t, b.decide s [r₁, r₂] gs = .ok t := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b, Xl, pd, reads, digits, eL, eb, hX, hn, la⟩ :=
    IM.k1_reads_of h.scope h.reads O 24 (by decide)
  have hix : IM.k1Ix 24 false = 4 := rfl
  rw [hix] at eb hn la
  obtain ⟨-, m24, f24, k24, -⟩ := IM.ground_named h.scope h.reads O.pub O.blank
  obtain rfl : m24 = Xl := Option.some.inj (f24.symm.trans hX)
  have hy := IM.yes_alone la (by intro k; cases k)
  have q := IM.hear_at_flat eL eb
  rw [IM.flatIx_scope h.scope h.reads O (by decide : 24 ≤ 24) 4] at q
  have hq := quiet_head hX k24
  have hdec : ∀ s t rs gs, (IM.k1Reads Zp Bs.G₀ 24 m24 5 reads).decide s rs gs = .ok t ↔
      ∃ m, (K1.commitAtS (Cl := Unit) (VerifiableInference.Desc.K1.parLater Bs.G₀.first
          (VerifiableInference.Desc.K1.gpOf Zp) 24 5 1) 24 1 reads).decide s
          (rs.take 2) (gs.take (K1.commitAtS (Cl := Unit) (VerifiableInference.Desc.K1.parLater
            Bs.G₀.first (VerifiableInference.Desc.K1.gpOf Zp) 24 5 1) 24 1 reads).openings) = .ok m
                ∧
        (head ⟨⟨1, some 24, 5, .K1⟩, Bs.G₀.W.hS, Bs.G₀.W.HLy, Bs.G₀.W.H⟩).decide m (rs.drop 2)
          (gs.drop (K1.commitAtS (Cl := Unit) (VerifiableInference.Desc.K1.parLater
            Bs.G₀.first (VerifiableInference.Desc.K1.gpOf Zp) 24 5 1) 24 1 reads).openings) =
          .ok t := by
    intro s t rs gs
    unfold IM.k1Reads
    rw [hq]
    exact VerifiableInference.Desc.K1.bind_ok _ _ _
  generalize (K1.commitAtS (Cl := Unit) (VerifiableInference.Desc.K1.parLater Bs.G₀.first
    (VerifiableInference.Desc.K1.gpOf Zp) 24 5 1) 24 1 reads).openings = n at hdec ⊢
  have hrd : b.rounds = VerifiableInference.Desc.K1.rounds (VerifiableInference.Desc.K1.parLater
      Bs.G₀.first (VerifiableInference.Desc.K1.gpOf Zp) 24 5 1) := by
    rw [IM.alone_rounds la]
    show (IM.k1Reads Zp Bs.G₀ 24 m24 5 reads).rounds = _
    unfold IM.k1Reads
    rw [hq]
    exact List.append_nil _
  refine ⟨Bs, m24, pd, reads, digits, b, O.made, hX, hn, q, hrd,
    fun s r₁ r₂ gs t hd => ?_,
    fun s rs gs t u hd hg' => ?_, fun s r₁ r₂ gs u hg' hz hnn hv => ?_⟩
  · obtain ⟨m, h1, h2⟩ := (hdec s t [r₁, r₂] gs).1 ((hy s t [r₁, r₂] gs).1 hd).1
    rw [(headQuiet_keeps h2).2.2]
    exact commit_forms h1
  · obtain ⟨m, h1, h2⟩ := (hdec s t rs gs).1 ((hy s t rs gs).1 hd).1
    unfold readsHeadGS at hg'
    split at hg'
    · cases hg'
    · obtain ⟨mm, hm', hu⟩ := Option.bind_eq_some_iff.1 hg'
      obtain rfl := commit_carries h1 hm'
      rw [headReads_carries h2] at hu
      exact (Option.some.inj hu).symm
  · unfold readsHeadGS at hg'
    split at hg'
    · cases hg'
    · rename_i hm
      obtain ⟨mm, hm', hu⟩ := Option.bind_eq_some_iff.1 hg'
      obtain ⟨m, hd, em⟩ := commit_returns (gs := gs.take n) hm' hz hnn
      rw [← em] at hu
      obtain ⟨t, ht⟩ := headReads_returns hu (hv m hd) ([r₁, r₂].drop 2) (gs.drop n)
      obtain ⟨k1, k2⟩ := commit_keeps hd
      obtain ⟨j1, j2, -⟩ := headQuiet_keeps ht
      have hf : s.failed = none := by
        have h1 : (chainSh s).marked = false := by simpa using hm
        have h2 : s.failed.isSome = false := h1
        simpa using h2
      refine ⟨t, (hy s t [r₁, r₂] gs).2 ⟨(hdec s t [r₁, r₂] gs).2 ⟨m, hd, ht⟩,
        j1.trans (k1.trans hf), ?_⟩⟩
      unfold ProofFile.sameReply
      rw [j2, k2]
      exact beq_self_eq_true _

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.headQuiet_keeps
#print axioms Johnson.AtFull.Shape.quiet_head
#print axioms Johnson.AtFull.Shape.reads_head_at
#print axioms Johnson.AtFull.Shape.readsHeadGS
