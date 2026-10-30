-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/ReadsLayersAtHead.lean: K1's COMMITMENT TO THE READS WITH THE QUIET STEP BEHIND
IT, AT THE TWELVE LAYERS' LINKS (the members 14 (2 g) + 5 of the flat list, g < 12) AT THEIR SEATS
IN THE PROOF FILE's OWN FIRST CHAIN: each member has one step on the chain's shape, with both laws
at the seated block's own decision, its declared rounds, and the makes of the rows behind it. Under
the head P5J.AtMgA; a joining of laws; nothing is evaluated.
  1 `layers_keeps`: the quiet step's yes (K8.ReadsQuiet.layers) leaves the mark of failure, what
    goes out and the statement.
  2 `readsGS P link arrays t`: the step at the seat: no mark; the commitment's step (commitG,
    Johnson/Desc/First/Shape/Commit.lean); then the quiet step (layersG,
    Johnson/Desc/K8/ReadsQuietShape.lean) at the shape t of the plan's record of the smallness test.
    `quiet_layers`: what the lot joins behind the commitment at a layers' link.
  **`reads_layers_at`** (g < 12): with Bs what the maker's own ProofFile.baseOf returns, Xl the link 2 g
    of Bs.G₀.built, reads off K1.linkNumbers, hp := Bs.G₀.W.G[g], P := K1.parLater Bs.G₀.first
    (K1.gpOf Zp) (2 g) 4 1: the member b at number 14 (2 g) + 3 + 2 of cF.blocksInOrder: b.rounds = K1.rounds
    P; behind a yes on two rounds formsOf t.st = sendForms P ‹the number of messages in front›
    (formsOf s.st); at the step readsGS P (2 g) reads (tailSh hp.tl): where b says yes and the step
    returns, it returns the shape behind; and where the step returns, b says yes on two rounds in
    which no seed's factor is 0 and round 2 holds as many answers as the place counts. EVERY
    PARAMETER OF THE STEP IS TIED TO A VALUE.
By IM.k1_reads_layers (Johnson/IMR/K1Seat.lean), Meaning.plans_size | scope_plans, IM.yes_alone,
IM.alone_rounds, IM.hear_at_flat, IM.flatIx_scope; commit_carries | commit_returns (Commit.lean);
commit_keeps (DigitsAtHead.lean); commit_forms (ChainF.lean); layers_sh (ReadsQuietShape.lean).
Limits. "Carries" is under the step's own return. "Returns" takes two premises on the rounds; one of
them is a test on values in a round (no seed's factor is 0). UNDER THE HEAD: that it has a member is
shown in scope, where the reader returns and `protocolDataWellFormed` accepts (`head_of_live`,
Johnson/P5J/HeadOfLive.lean); that these three hold together, at two named sets of public files
(`VerifierAndGoals.storedPublicFiles` and `VerifierAndGoals.zGap`), in a side library (AtFullSide/Top/HeadMemberAtFull.lean,
HeadMemberAtGap.lean). Of the head the proof spends h.scope, h.reads and h.laid.opened alone. That
reads is some list is not said: at none the commitment's step never returns (commitStepG,
Commit.lean), and the two laws on the step then say nothing: their premise "the step returns" is
never met. No state is shown by a theorem at which the step returns. At the earlier hash
OnBytes.secondHashFunction. Nothing on soundness, completeness or hiding.
Terms: lean/GLOSSARY.md.
-/
import Johnson.AtFull.Shape.DigitsAtHead
import Johnson.Desc.First.Shape.ChainF
import Johnson.Desc.K8.ReadsQuietShape
import Johnson.Goal.Meaning.PlanShapes
import Johnson.Goal.Meaning.PlanNames
import Johnson.IMR.K1Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link KindName K1.commitAtS)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.K8.ReadsQuiet (layers layersG layers_sh PG)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)

/-! ## 1 What the quiet step leaves -/

/-- The quiet step's yes leaves the mark of failure, what goes out and the statement. -/
theorem layers_keeps {P : PG} {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (layers P).decide s rs gs = .ok t) :
    t.failed = s.failed ∧ t.out = s.out ∧ t.st = s.st := by
  unfold layers at h
  dsimp only at h
  split at h
  · rename_i a ha
    obtain ⟨own, -, h⟩ := OnBytes.Params.exc_bind h
    obtain ⟨tl, -, h⟩ := OnBytes.Params.exc_bind h
    obtain rfl := Except.ok.inj h
    exact ⟨rfl, rfl, rfl⟩
  · cases h

/-! ## 2 The reads' member at a layers' link -/

/-- **The step at the seat**: no mark; the commitment to the reads (commitG,
Johnson/Desc/First/Shape/Commit.lean); then the quiet step (layersG,
Johnson/Desc/K8/ReadsQuietShape.lean) at the shape t of the plan's record of the smallness test. -/
def readsGS (P : VerifiableInference.Desc.K1.Par) (link : Nat) (arrays : Option (List Nat))
    (t : TailSh) (a : ChainSh) : Option ChainSh :=
  if a.marked then none else (commitG P link 1 arrays a).bind (layersG t)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- What the lot joins behind the reads' commitment at a layers' link: the quiet step at the plan's
record of the smallness test of the link's group. -/
theorem quiet_layers {G : ProofFile.Ground} {l g : Nat} {X : Stages.LinkH} {hp : Layer.HPlan2}
    (hX : G.built[l]? = some X) (hk : X.kind = 0) (hg : X.g = g) (hG : G.W.G[g]? = some hp) :
    IM.k1Quiet G l X = layers ⟨⟨1, some l, 4, .K1⟩, hp.tl⟩ := by
  unfold IM.k1Quiet ProofFile.readsQuietAt VerifiableInference.Desc.K8.ReadsQuiet.blockAt
  have e : (G.built.toList.map fun Y => (Y.kind, Y.g))[l]? = some (0, g) := by
    rw [List.getElem?_map, Array.getElem?_toList, hX, ← hk, ← hg]
    rfl
  simp [hk, e, hG, ProofFile.orLoud]

theorem reads_layers_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (g : Nat) (hg : g < 12) :
    ∃ (Bs : ProofFile.PureBase) (Xl : Stages.LinkH) (pd : Nat) (reads digits : Option (List Nat))
      (hp : Layer.HPlan2) (b : Block S ProofFile.Cl),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      Bs.G₀.built[2 * g]? = some Xl ∧
      VerifiableInference.Desc.K1.linkNumbers Bs.G₀ Xl = some (4, pd, reads, digits) ∧
      Bs.G₀.W.G[g]? = some hp ∧
      cF.blocksInOrder[14 * (2 * g) + 3 + 2]? = some b ∧
      b.rounds = VerifiableInference.Desc.K1.rounds (VerifiableInference.Desc.K1.parLater
        Bs.G₀.first (VerifiableInference.Desc.K1.gpOf Zp) (2 * g) 4 1) ∧
      (∀ s r₁ r₂ gs t, b.decide s [r₁, r₂] gs = .ok t →
        formsOf t.st = sendForms (VerifiableInference.Desc.K1.parLater Bs.G₀.first
          (VerifiableInference.Desc.K1.gpOf Zp) (2 * g) 4 1)
          (chainSh s).core.st.oracles.length (formsOf s.st)) ∧
      (∀ s rs gs t u, b.decide s rs gs = .ok t →
        readsGS (VerifiableInference.Desc.K1.parLater Bs.G₀.first
          (VerifiableInference.Desc.K1.gpOf Zp) (2 * g) 4 1) (2 * g) reads (tailSh hp.tl)
          (chainSh s) = some u → u = chainSh t) ∧
      ∀ s r₁ r₂ gs u,
        readsGS (VerifiableInference.Desc.K1.parLater Bs.G₀.first
          (VerifiableInference.Desc.K1.gpOf Zp) (2 * g) 4 1) (2 * g) reads (tailSh hp.tl)
          (chainSh s) = some u →
        (∀ y ∈ VerifiableInference.Desc.K1.seedsOf (VerifiableInference.Desc.K1.parLater Bs.G₀.first
          (VerifiableInference.Desc.K1.gpOf Zp) (2 * g) 4 1) r₁, isZeroE y.2 = false) →
        (VerifiableInference.Desc.K1.answersIn r₂).length =
          (VerifiableInference.Desc.K1.parLater Bs.G₀.first (VerifiableInference.Desc.K1.gpOf Zp)
            (2 * g) 4 1).answers →
        ∃ t, b.decide s [r₁, r₂] gs = .ok t := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b, Xl, pd, reads, digits, eL, eb, hX, hk, hgg, hn, la⟩ :=
    IM.k1_reads_layers h.scope h.reads O g hg
  have hsz : Bs.G₀.W.G.size = 12 := by
    rw [Meaning.plans_size O.public, (Meaning.scope_plans h.scope h.reads O.public).2.1]
  obtain ⟨hp, hG⟩ : ∃ hp, Bs.G₀.W.G[g]? = some hp :=
    ⟨_, Array.getElem?_eq_getElem (by rw [hsz]; exact hg)⟩
  have hy := IM.yes_alone la (by intro k; cases k)
  have q := IM.hear_at_flat eL eb
  rw [IM.flatIx_scope h.scope h.reads O (by omega : 2 * g ≤ 24) 3] at q
  have hq := quiet_layers hX hk hgg hG
  have hdec : ∀ s t rs gs, (IM.k1Reads Zp Bs.G₀ (2 * g) Xl 4 reads).decide s rs gs = .ok t ↔
      ∃ m, (K1.commitAtS (Cl := Unit) (VerifiableInference.Desc.K1.parLater Bs.G₀.first
          (VerifiableInference.Desc.K1.gpOf Zp) (2 * g) 4 1) (2 * g) 1 reads).decide s
          (rs.take 2) (gs.take (K1.commitAtS (Cl := Unit) (VerifiableInference.Desc.K1.parLater
            Bs.G₀.first (VerifiableInference.Desc.K1.gpOf Zp) (2 * g) 4 1) (2 * g) 1
            reads).openings) = .ok m ∧
        (layers ⟨⟨1, some (2 * g), 4, .K1⟩, hp.tl⟩).decide m (rs.drop 2)
          (gs.drop (K1.commitAtS (Cl := Unit) (VerifiableInference.Desc.K1.parLater
            Bs.G₀.first (VerifiableInference.Desc.K1.gpOf Zp) (2 * g) 4 1) (2 * g) 1
            reads).openings) = .ok t := by
    intro s t rs gs
    unfold IM.k1Reads
    rw [hq]
    exact VerifiableInference.Desc.K1.bind_ok _ _ _
  generalize (K1.commitAtS (Cl := Unit) (VerifiableInference.Desc.K1.parLater Bs.G₀.first
    (VerifiableInference.Desc.K1.gpOf Zp) (2 * g) 4 1) (2 * g) 1 reads).openings = n at hdec
  have hrd : b.rounds = VerifiableInference.Desc.K1.rounds (VerifiableInference.Desc.K1.parLater
      Bs.G₀.first (VerifiableInference.Desc.K1.gpOf Zp) (2 * g) 4 1) := by
    rw [IM.alone_rounds la]
    show (IM.k1Reads Zp Bs.G₀ (2 * g) Xl 4 reads).rounds = _
    unfold IM.k1Reads
    rw [hq]
    exact List.append_nil _
  refine ⟨Bs, Xl, pd, reads, digits, hp, b, O.made, hX, hn, hG, q, hrd,
    fun s r₁ r₂ gs t hd => ?_,
    fun s rs gs t u hd hg' => ?_, fun s r₁ r₂ gs u hg' hz hnn => ?_⟩
  · obtain ⟨m, h1, h2⟩ := (hdec s t [r₁, r₂] gs).1 ((hy s t [r₁, r₂] gs).1 hd).1
    rw [(layers_keeps h2).2.2]
    exact commit_forms h1
  · obtain ⟨m, h1, h2⟩ := (hdec s t rs gs).1 ((hy s t rs gs).1 hd).1
    unfold readsGS at hg'
    split at hg'
    · cases hg'
    · obtain ⟨m', hm', hu⟩ := Option.bind_eq_some_iff.1 hg'
      obtain rfl := commit_carries h1 hm'
      have e := layers_sh ⟨⟨1, some (2 * g), 4, .K1⟩, hp.tl⟩ m (rs.drop 2) (gs.drop n)
      rw [h2] at e
      exact (Option.some.inj (e.trans hu)).symm
  · unfold readsGS at hg'
    split at hg'
    · cases hg'
    · rename_i hm
      obtain ⟨m', hm', hu⟩ := Option.bind_eq_some_iff.1 hg'
      obtain ⟨m, hd, em⟩ := commit_returns (gs := gs.take n) hm' hz hnn
      have e := layers_sh ⟨⟨1, some (2 * g), 4, .K1⟩, hp.tl⟩ m ([r₁, r₂].drop 2) (gs.drop n)
      rw [em, hu] at e
      obtain ⟨t, ht, -⟩ := Option.map_eq_some_iff.1 e
      have ht' : (layers ⟨⟨1, some (2 * g), 4, .K1⟩, hp.tl⟩).decide m ([r₁, r₂].drop 2)
          (gs.drop n) = .ok t := by
        cases hh : (layers ⟨⟨1, some (2 * g), 4, .K1⟩, hp.tl⟩).decide m ([r₁, r₂].drop 2)
            (gs.drop n) with
        | error w => rw [hh] at ht; cases ht
        | ok t' => rw [hh] at ht; rw [Option.some.inj ht]
      obtain ⟨k1, k2⟩ := commit_keeps hd
      obtain ⟨j1, j2, -⟩ := layers_keeps ht'
      have hf : s.failed = none := by
        have h1 : (chainSh s).marked = false := by simpa using hm
        have h2 : s.failed.isSome = false := h1
        simpa using h2
      refine ⟨t, (hy s t [r₁, r₂] gs).2 ⟨(hdec s t [r₁, r₂] gs).2 ⟨m, hd, ht'⟩,
        j1.trans (k1.trans hf), ?_⟩⟩
      unfold ProofFile.sameReply
      rw [j2, k2]
      exact beq_self_eq_true _

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.layers_keeps
#print axioms Johnson.AtFull.Shape.quiet_layers
#print axioms Johnson.AtFull.Shape.reads_layers_at
#print axioms Johnson.AtFull.Shape.readsGS
