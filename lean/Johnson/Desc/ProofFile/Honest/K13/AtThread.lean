-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/AtThread.lean: kind K13, the members' batching: WHAT A CHAIN's
THREAD ASKS AT A MEMBER (Honest/Thread/Pays.lean: `Plays`, `Accepted`, and the step of which
`Behind` and `Exchange` speak), AT THE KIND's MEMBER, general in the thread's fields. Statements
with their proofs, over Debts.lean and DebtsKit.lean of this folder.
Main names:
  `AtK13 T b weights pile P`: the member number b of the thread's list has the kind's rounds, states
    no oracle message, and the kind's half stands at its place among the thread's halves.
  `k13_thread_plays`: **`Plays T b`, from `AtK13` alone**: no premise on the thread's sentence.
  `k13_thread_accepted`: **`Accepted T fall b`, at every `fall`**, at all coins, from `AtK13` and
    two premises on the thread's sentence in front: it gives `K13Guards`; and the member accepts
    wherever `atM3 P` does.
  `k13_thread_stepped`: **behind the member's step**, from `K13Front` beside: the state is
    `withClaim`, and the row of its claim is true of the witness: what a proof of `Behind` or of
    `Exchange` can use.

What is not claimed. THE HEAVY HALF OF `Accepted` IS A PREMISE HERE: that the thread's sentence in
front gives the nine guards. `Behind`, `Exchange` and `RidesPast` themselves: they speak in a
thread's fields (its form, its items' meaning), which are free here. That the two premises of
`k13_thread_accepted` hold at the first chain's thread. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K13.Debts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes
open OnBytes.Slice (GE)
open VerifiableInference.Desc (Block Place OpenedColumn)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Ground (takeMasksP)
open VerifiableInference.Desc.K13 (Where battRounds atM3)
open VerifiableInference.Desc.K13.Law (Wit ρg Holds dOf)
open VerifiableInference.Desc.K13.Honest (withClaim)

variable {Bk : ProverCoinCounts} {Cl Cl' W₀ Rc Xi Tr X Pb : Type}

variable (T : Thread Bk S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)

/-- **The member number b is the kind's**, beside the kind's half: it declares the kind's rounds; it
states no oracle message; among the thread's halves the kind's stands at its place. -/
structure AtK13 (b : Nat) (weights : W₀ → Weights) (pile : PileOf Xi) (P : Where) : Prop where
  rounds : ∀ blk, T.bs[b]? = some blk → blk.rounds = battRounds P
  oracles : ∀ blk, T.bs[b]? = some blk → blk.oracles = List.replicate (2 + P.lin.kCol) []
  half : ∀ blk, T.bs[b]? = some blk →
    (T.hs.find? fun h => h.place == blk.place) = some (proverSideOfClaimCombination weights pile P)

variable {T} {b : Nat} {weights : W₀ → Weights} {pile : PileOf Xi} {P : Where}

/-- **It plays**: at all coins, with no premise on the thread's sentence in front. -/
theorem k13_thread_plays (h : AtK13 T b weights pile P) : Plays T b := by
  intro blk hb k s m En ds l _ hd _ hl
  obtain ⟨p, hp, -, hc⟩ := k13_moved weights pile P blk (h.rounds blk hb) (h.oracles blk hb)
    (h.half blk hb) hl m ds hd
  refine ⟨_, [], ⟨⟨l, hl, hp⟩, hc _ _ _ _⟩, ?_⟩
  rw [fresh_none T hb (by rw [h.oracles blk hb]; simp)]
  intro σ hσ
  cases hσ

/-- **It is accepted**, at every `fall`: the kind's member has no fall: AT ALL COINS, from two
premises on the thread's sentence in front: it gives the guards; and the member accepts wherever
`atM3 P` does. -/
theorem k13_thread_accepted (h : AtK13 T b weights pile P)
    (hdec : ∀ blk, T.bs[b]? = some blk → ∀ k s m En, Thr T b k s m En → ∀ rs gs t',
      (atM3 (Cl := Cl') P).decide s rs gs = .ok t' → blk.decide s rs gs = .ok t')
    (hG : ∀ k s m En, Thr T b k s m En → K13Guards P s)
    (fall : Nat → S → List Fmt.Drawn → Option String) : Accepted T fall b := by
  intro blk hb k s m En ds y cols hT hd _ _ hM
  obtain ⟨⟨l, hl, hy⟩, hc⟩ := hM
  obtain ⟨s', hst⟩ := k13_accepted weights pile P blk (h.rounds blk hb) (h.oracles blk hb)
    (h.half blk hb) hl (hdec blk hb k s m En hT) m ds hd (hG k s m En hT) _ _ _ _ hy hc
  exact ⟨s', ⟨⟨l, hl, hy⟩, hc⟩, hst⟩

/-- **Behind the member's step**: from the guards and `K13Front` in front, at a witness W: the state
behind is `withClaim`, at what the verifier's taking returns, and the row of its claim is true of W.
-/
theorem k13_thread_stepped (h : AtK13 T b weights pile P) {blk : Block S Cl}
    (hb : T.bs[b]? = some blk)
    {k : Coins Bk} {s s' : S} {m : Mid (Local W₀ Rc Xi Tr) X} {En : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn}
    (hdec : ∀ rs gs t', (atM3 (Cl := Cl') P).decide s rs gs = .ok t' →
      blk.decide s rs gs = .ok t')
    (hd : drawsFit blk.rounds ds = true) (hG : K13Guards P s)
    (W : Wit GE P.lin.matrixRows P.lin.kCol)
    (hA : ∀ c : RowCoins (proverSideOfClaimCombination (Rc := Rc) (Tr := Tr) (X := X) weights pile P).parts,
      lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) blk.place (proverSideOfClaimCombination weights pile P).parts 0 =
        .ok c → K13Front weights pile P s m (coinsE c.2.1.2.1.1) W)
    (hS : T.Stepped blk k s m En ds y cols s') :
    ∃ t msg row, takeMasksP (dOf s) s.out.indexMasks (Batt.masksOf P.lin.kCol) = some t ∧
      linMessageW P.lin = some msg ∧ s' = withClaim s t.2.st msg row ∧ Holds ρg W row := by
  obtain ⟨⟨⟨l, hl, hy⟩, hc⟩, hst⟩ := hS
  obtain ⟨t, msg, row, ht, hmsg, hst', hrow⟩ := k13_stepped weights pile P blk (h.rounds blk hb)
    (h.oracles blk hb) (h.half blk hb) hl hdec m ds hd hG W hA _ _ _ _ hy hc
  refine ⟨t, msg, row, ht, hmsg, ?_, hrow⟩
  exact (congrArg Prod.fst (Except.ok.inj (hst.symm.trans hst')))

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13_thread_plays
#print axioms ProofFile.Honest.K13.k13_thread_accepted
#print axioms ProofFile.Honest.K13.k13_thread_stepped
