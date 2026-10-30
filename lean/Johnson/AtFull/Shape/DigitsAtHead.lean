-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/DigitsAtHead.lean: K1's COMMITMENT TO THE DIGITS AT ITS SEAT IN THE PROOF
FILE's OWN FIRST CHAIN, AT ALL 25 LINKS: the member of the flat list has one step on the chain's
shape, with both laws at the seated block's own decision. Under the head P5J.AtMgA; nothing is
evaluated.

  1 `putLink_keeps`, `putFork_keeps`, `commit_keeps`: a commitment's yes leaves the mark of failure
    and what goes out.
  2 `commitGS`: the step at the seat: no mark, then commitG (Johnson/Desc/First/Shape/Commit.lean).
    **`digits_at`**: for l < 25: with Bs what the maker's own ProofFile.baseOf returns at the public part
    (one value: baseOf is a function), Xl the link as built in its ground Bs.G₀, and the link's
    numbers (K1.linkNumbers Bs.G₀ Xl, which names the digits' arrays): the member b at number 14 l
    + k1Ix l true + 2 of cF.blocksInOrder is such that: where b says yes and commitGS returns, it returns
    the shape behind; and where commitGS returns, b says yes on two rounds in which no seed's
    factor is 0 and round 2 holds as many answers as the place counts.

By IM.k1_digits_of (Johnson/IMR/K1Scope.lean: the seat holds K1's own block alone), IM.yes_alone
(Johnson/IMR/SeatForm.lean: the seated yes is the block's yes, no mark, the reply as it was),
IM.hear_at_flat and IM.flatIx_scope (the number in the flat list).

Limits. The two premises on the rounds stand as in SendCore.lean. The reads' members, behind whose
block a quiet step lies, are not here. No state is shown at which commitGS returns. That the head
has a member is shown in scope, where the reader returns and `protocolDataWellFormed` accepts (`head_of_live`,
Johnson/P5J/HeadOfLive.lean); that these three hold together, at two named sets of public files, in
a side library. At the format's second hash function. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Shape.Commit
import Johnson.IMR.K1Scope
import Johnson.IMR.FlatScope
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link KindName K1.commitAtS)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)

/-! ## 1 What a commitment leaves -/

theorem putLink_keeps (s : S) (L : LinkCtx) :
    (s.putLink L).failed = s.failed ∧ (s.putLink L).out = s.out := by
  unfold S.putLink
  split
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

theorem putFork_keeps (s : S) (F : Fork) :
    (s.putFork F).failed = s.failed ∧ (s.putFork F).out = s.out := by
  unfold S.putFork
  split
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

/-- A commitment's yes leaves the mark and what goes out. -/
theorem commit_keeps {P : VerifiableInference.Desc.K1.Par} {link moment : Nat}
    {arrays : Option (List Nat)} {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (K1.commitAtS (Cl := Unit) P link moment arrays).decide s rs gs = .ok t) :
    t.failed = s.failed ∧ t.out = s.out := by
  simp only [K1.commitAtS] at h
  split at h
  · rename_i L F tl _ _ _
    cases hb : (VerifiableInference.Desc.K1.commitOwn (Cl := Unit) P link moment arrays).decide
        ⟨VerifiableInference.Desc.K1.owedOf s,
          ⟨L, F, tl, VerifiableInference.Desc.K1.stateOf s ()⟩⟩ rs gs with
    | error e => simp [hb, Except.map] at h
    | ok y =>
      simp only [hb, Except.map, Except.ok.injEq] at h
      subst h
      exact ⟨((putFork_keeps _ _).1.trans (putLink_keeps _ _).1),
        ((putFork_keeps _ _).2.trans (putLink_keeps _ _).2)⟩
  · cases h

/-! ## 2 The digits' commitment at its seat, at all 25 links -/

/-- **The step at the seat.** -/
def commitGS (P : VerifiableInference.Desc.K1.Par) (link moment : Nat)
    (arrays : Option (List Nat)) (a : ChainSh) : Option ChainSh :=
  if a.marked then none else commitG P link moment arrays a

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

theorem digits_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25) :
    ∃ (Bs : ProofFile.PureBase) (Xl : Stages.LinkH) (pr : Nat) (reads digits : Option (List Nat))
      (b : Block S ProofFile.Cl),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      Bs.G₀.built[l]? = some Xl ∧
      VerifiableInference.Desc.K1.linkNumbers Bs.G₀ Xl =
        some (pr, IM.k1Ix l true + 1, reads, digits) ∧
      cF.blocksInOrder[14 * l + IM.k1Ix l true + 2]? = some b ∧
      (∀ s rs gs t u, b.decide s rs gs = .ok t →
        commitGS (VerifiableInference.Desc.K1.parLater Bs.G₀.first
          (VerifiableInference.Desc.K1.gpOf Zp) l (IM.k1Ix l true + 1) 2) l 2 digits
          (chainSh s) = some u → u = chainSh t) ∧
      ∀ s r₁ r₂ gs u,
        commitGS (VerifiableInference.Desc.K1.parLater Bs.G₀.first
          (VerifiableInference.Desc.K1.gpOf Zp) l (IM.k1Ix l true + 1) 2) l 2 digits
          (chainSh s) = some u →
        (∀ y ∈ VerifiableInference.Desc.K1.seedsOf (VerifiableInference.Desc.K1.parLater Bs.G₀.first
          (VerifiableInference.Desc.K1.gpOf Zp) l (IM.k1Ix l true + 1) 2) r₁,
          isZeroE y.2 = false) →
        (VerifiableInference.Desc.K1.answersIn r₂).length =
          (VerifiableInference.Desc.K1.parLater Bs.G₀.first (VerifiableInference.Desc.K1.gpOf Zp) l
            (IM.k1Ix l true + 1) 2).answers →
        ∃ t, b.decide s [r₁, r₂] gs = .ok t := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b, Xl, pr, reads, digits, eL, eb, hX, hn, la⟩ :=
    IM.k1_digits_of h.scope h.reads O l hl
  have hy := IM.yes_alone la (by intro k; cases k)
  have q := IM.hear_at_flat eL eb
  rw [IM.flatIx_scope h.scope h.reads O (by omega : l ≤ 24) (IM.k1Ix l true)] at q
  refine ⟨Bs, Xl, pr, reads, digits, b, O.made, hX, hn, q, fun s rs gs t u hd hg => ?_,
    fun s r₁ r₂ gs u hg hz hnn => ?_⟩
  · have hd' := ((hy s t rs gs).1 hd).1
    unfold commitGS at hg
    split at hg
    · cases hg
    · exact commit_carries hd' hg
  · unfold commitGS at hg
    split at hg
    · cases hg
    · rename_i hm
      obtain ⟨t, ht, -⟩ := commit_returns (gs := gs) hg hz hnn
      obtain ⟨k1, k2⟩ := commit_keeps ht
      have hf : s.failed = none := by
        have h1 : (chainSh s).marked = false := by simpa using hm
        have h2 : s.failed.isSome = false := h1
        simpa using h2
      refine ⟨t, (hy s t [r₁, r₂] gs).2 ⟨ht, k1.trans hf, ?_⟩⟩
      unfold ProofFile.sameReply
      rw [k2]
      exact beq_self_eq_true _

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.commit_keeps
#print axioms Johnson.AtFull.Shape.digits_at
#print axioms Johnson.AtFull.Shape.putLink_keeps
#print axioms Johnson.AtFull.Shape.putFork_keeps
