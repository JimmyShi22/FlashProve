-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/ToldCommitAt.lean: THE TOLD SYSTEM'S COMMITTER AT THE NUMBER OF A PAIR IS THE TOLD
SYSTEM'S COMMITTER AT THESE TWO COINS FIXED. Statements and proofs; general in the told record.

Why. Johnson/Top/ToldReach.lean says which coins the SCHEME's committer takes at a number. The goals
on binding speak of the SYSTEM's committer (`Rec.tokenArgumentSystem`, Johnson/Top/FrontEnc.lean), which runs
the scheme's at the number, asks the hash function at the key's code and keeps the answer. Here the
step between the two is stated, so that "every setting of coins is reached" can be said of the term
of which the goals speak (a reader's ask).

Main names.
  `Rec.commitE_eq` (namespace `VerifiableInference.Rec`): `commitE` at the number n is: the scheme's
    committer at n, then the key's digest. By `withCoins_bind_of_drawsNoCoin`
    (ZKCP/WithCoinsBind.lean) and `withCoins_ofRom` (Rom/WithCoins.lean).
  `Rec.commit_systemE_congr`: two schemes with one code of keys whose committers agree at an index,
    at the numbers n and n': the two systems' committers there are one algorithm, whatever the two
    bounds.
  `enumOne r` (namespace `VerifiableInference.OnPublicFiles`): the enumeration with the one member r.
  **`commit_systemOn_reach`**: the committer of `(T.withCommit ri sl b₀ prove).systemOn back nt` at
    the number a + (ri.n + 1) c IS the committer of `(T.withCommit (enumOne (ri.e a)) (enumOne (sl.e
    c)) b₀ prove).systemOn back nt` at the number 0: THE COMMITTER WITH THE COINS (ri.e a, sl.e c)
    FIXED. Premise: the public reading draws nothing; hn: the number lies within the input's bound.

Limits. An equation between two terms of this library: nothing on any program. Nothing on whether ri
or sl is onto anything (Johnson/Top/ToldReachAll.lean).
Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.ToldReach
import ZKCP.WithCoinsBind

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Rec
open Rom ZKCP

variable {I X IVK ISK Pf : Type}

/-- `commitE` at a number: the scheme's committer at that number, then the key's digest. -/
theorem commitE_eq (G : ZKCP.Gen.Arg (rom 256) I X Unit IVK ISK Pf) (enc : IVK → Option ZKCP.Str)
    (bound : ℕ) (i : I) (coins : Fin (bound + 1)) :
    commitE G enc bound i coins =
      ((ofRom ((G.C i).withCoins coins.val)).bind fun keys =>
        (ZKCP.keyDigest enc keys.1).mapO fun digest => (digest, keys)).mapO Prod.fst := by
  unfold commitE digestKeyScheme
  show ((((ofRom (G.C i)).bind fun keys =>
      (ZKCP.keyDigest enc keys.1).mapO fun digest => (digest, keys))).withCoins coins.val).mapO
        Prod.fst = _
  rw [ZKCP.OComp.withCoins_bind_of_drawsNoCoin
    (fun keys : IVK × ISK => (ZKCP.keyDigest enc keys.1).mapO fun digest => (digest, keys))
    (fun keys => ZKCP.OComp.DrawsNoCoin.mapO _ _ (ZKCP.drawsNoCoin_keyDigest enc keys.1)),
    withCoins_ofRom]

/-- **Two systems whose schemes' committers agree at two numbers commit alike there.** -/
theorem commit_systemE_congr (G G' : ZKCP.Gen.Arg (rom 256) I X Unit IVK ISK Pf)
    (enc : IVK → Option ZKCP.Str) (bound bound' : ℕ)
    (build : List Token × List Token → List Token → Option X) (π₀ : IVK × Pf)
    (nextToken : I → List Token → Option Token) (i : I) (n : Fin (bound + 1))
    (n' : Fin (bound' + 1)) (h : (G.C i).withCoins n.val = (G'.C i).withCoins n'.val) :
    (tokenArgumentSystem G enc bound build π₀ nextToken).commit i n =
      (tokenArgumentSystem G' enc bound' build π₀ nextToken).commit i n' := by
  show deterministicOf (commitE G enc bound i n) = deterministicOf (commitE G' enc bound' i n')
  rw [commitE_eq, commitE_eq, h]

end VerifiableInference.Rec

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- The enumeration with one member. -/
def enumOne {β : Type} (r : β) : Enum β := ⟨0, fun _ => r⟩

variable {R : InnerCompilerInput} (T : LayoutsByPublicReading R) (ri : Enum R.protocol.EncodingRandomness) (sl : Enum (ℕ → Bits)) (b₀ : R.LeafBody)
  (prove : R.Index × R.protocol.EncodingRandomness × (ℕ → Bits) → (l : List (R.Instance × Unit)) →
    Rom.OComp (rom 256) (ZKCP.Gen.Slots (OfflineLinkOnlineProof 256 R.protocol R.offlineRoundSplits R.linkRoundSplits) l))

/-- **THE SYSTEM'S COMMITTER AT THE NUMBER OF A PAIR IS THE COMMITTER WITH THESE TWO COINS FIXED.**
-/
theorem commit_systemOn_reach {J : Type} (back : J → R.Index) (nt : J → List Token → Option Token)
    (noCoin : T.Pub.NoCoin) (j : J) (a : Fin (ri.n + 1)) (c : Fin (sl.n + 1))
    (hn : a.val + (ri.n + 1) * c.val < R.coinBound + 1) :
    ((T.withCommit ri sl b₀ prove).systemOn back nt).commit j ⟨a.val + (ri.n + 1) * c.val, hn⟩ =
      ((T.withCommit (enumOne (ri.e a)) (enumOne (sl.e c)) b₀ prove).systemOn back nt).commit j
        (⟨0, Nat.succ_pos _⟩ : Fin (R.coinBound + 1)) := by
  refine Rec.commit_systemE_congr ((T.withCommit ri sl b₀ prove).schemeOn back)
    ((T.withCommit (enumOne (ri.e a)) (enumOne (sl.e c)) b₀ prove).schemeOn back) T.encT R.coinBound
    R.coinBound R.buildInstance T.π₀ nt j _ _ ?_
  show (T.commitBehind ri sl b₀ (back j)).withCoins (a.val + (ri.n + 1) * c.val) =
    (T.commitBehind (enumOne (ri.e a)) (enumOne (sl.e c)) b₀ (back j)).withCoins 0
  rw [commitBehind_reach T ri sl b₀ noCoin (back j) a c]
  exact (commitBehind_reach T (enumOne (ri.e a)) (enumOne (sl.e c)) b₀ noCoin (back j) 0 0).symm

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.Rec.commitE_eq
#print axioms VerifiableInference.Rec.commit_systemE_congr
#print axioms VerifiableInference.OnPublicFiles.commit_systemOn_reach
