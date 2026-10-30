-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/DigestKeyWithOpenings.lean: "whoever opens a key opens it to the extracted index" passes
from a scheme A to the scheme `A.digestKey enc` (ZKCP/DigestKey.lean), in which the verifier's key
is the digest of the verifier's key of A.

The statement is index binding of the scheme with openings in place of proofs (`withOpenings`,
ZKCP/WithOpenings.lean).
  `HasIndexBindingWith.withOpenings_digestKey`   if `A.withOpenings` has it with the index part of E
        and the bound β, then `(A.digestKey enc).withOpenings` has it with the index part of
        `E.digestKey enc` and the bound β tC (tO + tS) + (tC + tO + tS + 2)² / 2^λ
tC and tO bound the queries of the adversary's committer and opener; tS bounds those of A's
committer at every index.
Conditions: the coding is one to one, and every key that A's committer can output has a code. The
second cannot be dropped: all keys without a code have the digest of zeros, so whoever outputs that
digest could open it to any index whose key has no code, and the extractor gives nothing (an
argument; no theorem).
How. An opening of a digest is turned into a proof for the verifier `verifyDigestKey` over
`A.withOpenings`: the opener runs A's committer at the index and number that it names, and sends the
key that this returns. That verifier accepts where the digest is opened. Then
`HasIndexBindingWith.digestKey` (Compile/DigestKeyBinding.lean) applies. The run of A's committer is
counted among the opener's queries, hence tO + tS.
Limits: Compile/DigestKeyArg.lean; one opening in a run.
-/
import Compile.DigestKeyBinding
import ZKCP.WithOpenings
import ZKCP.WithCoinsBind

set_option autoImplicit false

open scoped ENNReal

namespace ZKCP

variable {lam : ℕ} {I X W IVK ISK Pf : Type}

namespace OComp

variable {α β : Type}

/-- A probability that does not read the query log of the first step. -/
theorem prob_run_withTrace_bind (f : Oracle lam) (c : OComp lam α) (g : α → OComp lam β)
    (E : Set β) :
    prob ((c.withTrace.bind fun o => g o.1).run f) E = prob ((c.bind g).run f) E := by
  rw [run_bind, run_bind, prob_bind, prob_bind,
    expect_withTrace f c fun a => prob ((g a).run f) E]

end OComp

/-- Under each hash function: the verifier's key of `A.digestKey enc` at an index and a number is
the digest of the verifier's key of A at these. -/
theorem run_commitAt_digestKey (A : Arg lam I X W IVK ISK Pf) (enc : IVK → Option Str)
    (f : Oracle lam) (i : I) (coins : ℕ) :
    ((A.digestKey enc).commitAt i coins).run f
      = ((A.commitAt i coins).run f).map (digestUnder f enc) := by
  show ((((A.C i).bind fun keys =>
      (keyDigest enc keys.1).mapO fun digest => (digest, keys)).withCoins coins).mapO
        Prod.fst).run f = ((((A.C i).withCoins coins).mapO Prod.fst).run f).map _
  rw [OComp.withCoins_bind_of_drawsNoCoin
      (fun keys : IVK × ISK => (keyDigest enc keys.1).mapO fun digest => (digest, keys))
      (fun keys => OComp.DrawsNoCoin.mapO _ _ (drawsNoCoin_keyDigest enc keys.1)),
    OComp.run_mapO, OComp.run_mapO, run_bind, PMF.map_bind, PMF.map_comp]
  show _ = ((A.C i).withCoins coins |>.run f).bind fun keys =>
    PMF.pure (digestUnder f enc keys.1)
  refine congrArg _ (funext fun keys => ?_)
  rw [OComp.run_mapO, run_keyDigest, PMF.pure_map, PMF.pure_map]

/-- Every key that A's committer returns at a given number has a code, if every key that it can
output has one. -/
theorem Arg.KeysHaveCodes.commitAt {A : Arg lam I X W IVK ISK Pf} {enc : IVK → Option Str}
    (h : A.KeysHaveCodes enc) (f : Oracle lam) (i : I) (coins : ℕ) :
    ∀ key ∈ ((A.commitAt i coins).run f).support, enc key ≠ none := by
  intro key hkey
  have hkey' : key ∈ ((((A.C i).withCoins coins).run f).map Prod.fst).support := by
    rw [← OComp.run_mapO]
    exact hkey
  obtain ⟨keys, hk, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hkey'
  exact h i f keys (OComp.support_run_withCoins f _ _ hk)

namespace DigestKey

/-- Under one hash function, at one opening x of the digest d: the verifier that runs the committer
of `A.digestKey enc` again accepts only if `verifyDigestKey` over `A.withOpenings` accepts the key
that A's committer returns at x. -/
theorem withOpenings_step (A : Arg lam I X W IVK ISK Pf) {enc : IVK → Option Str}
    (hcode : A.KeysHaveCodes enc) (f : Oracle lam) (d : Digest lam) (x : I × ℕ) (ι : Option I)
    (T : Set (BindingOutcome I (I × ℕ) Unit)) :
    prob ((((A.digestKey enc).withOpenings.V d x ()).bind fun b =>
        (.pure ⟨b, ι, x, ()⟩ : OComp lam (BindingOutcome I (I × ℕ) Unit))).run f) T
      ≤ prob ((((A.commitAt x.1 x.2).mapO fun key => (x, (key, ()))).bind fun o =>
        (verifyDigestKey A.withOpenings.V enc d o.1 o.2).bind fun b =>
        (.pure ⟨b, ι, o.1, ()⟩ : OComp lam (BindingOutcome I (I × ℕ) Unit))).run f) T := by
  classical
  obtain ⟨key, hkey⟩ := OComp.DrawsNoCoin.run f _ (A.drawsNoCoin_commitAt x.1 x.2)
  have hne : enc key ≠ none := hcode.commitAt f x.1 x.2 key (by
    rw [hkey]
    exact (PMF.mem_support_pure_iff _ _).2 rfl)
  cases hs : enc key with
  | none => exact absurd hs hne
  | some s =>
    have hB : ((A.digestKey enc).commitAt x.1 x.2).run f = PMF.pure (f s) := by
      rw [run_commitAt_digestKey, hkey, PMF.pure_map, digestUnder_of_some f hs]
    rw [OComp.mapO_bind, run_bind, run_bind, hkey, PMF.pure_bind, run_bind,
      run_verifyDigestKey A.withOpenings.V f d x (key, ()) hs]
    by_cases hd : f s = d
    · rw [(A.digestKey enc).run_withOpenings_V_of_eq f d x () hB hd, PMF.pure_bind, if_pos hd,
        A.run_withOpenings_V_of_eq f key x () hkey rfl, PMF.pure_bind]
    · rw [(A.digestKey enc).run_withOpenings_V_of_ne f d x () hB hd, PMF.pure_bind, if_neg hd,
        show (OComp.pure false : OComp lam Bool).run f = PMF.pure false from rfl, PMF.pure_bind]

end DigestKey

open DigestKey in
/-- "Whoever opens a key opens it to the extracted index" passes to `A.digestKey enc`, if the coding
is one to one and every key that A's committer can output has a code: with the index part of
`E.digestKey enc` and the bound β tC (tO + tS) + (tC + tO + tS + 2)² / 2^λ, where tS bounds the
queries of A's committer at every index. -/
theorem HasIndexBindingWith.withOpenings_digestKey {A : Arg lam I X W IVK ISK Pf}
    {E : Extractor lam I X W IVK Pf} {β : ℕ → ℕ → ℝ≥0∞}
    (h : HasIndexBindingWith (openingRelation I) A.withOpenings E.withOpenings β)
    {enc : IVK → Option Str} (hinj : CodeIsOneToOne enc) (hcode : A.KeysHaveCodes enc) {tS : ℕ}
    (hS : ∀ i, (A.C i).QueryBound tS) :
    HasIndexBindingWith (openingRelation I) (A.digestKey enc).withOpenings (E.digestKey
        enc).withOpenings
      fun tC tO => β tC (tO + tS) + (((tC + (tO + tS) + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ lam := by
  have hb := h.digestKey hinj
  intro tC tO St Ct Pt hC hP
  refine le_trans (MeasureTheory.lintegral_mono fun f => ?_)
    (hb tC (tO + tS) St Ct
      (fun st => (Pt st).bind fun o => (A.commitAt o.1.1 o.1.2).mapO fun key => (o.1, (key, ())))
      hC fun st => OComp.QueryBound.bind _ tS
        (fun o => OComp.QueryBound.mapO _ _ tS (A.queryBound_commitAt o.1.1 o.1.2 tS (hS o.1.1)))
        (Pt st) tO (hP st))
  show prob ((Ct.withTrace.bind fun c => (Pt c.1.2).withTrace.bind fun o =>
        ((A.digestKey enc).withOpenings.V c.1.1 o.1.1 o.1.2).bind fun b =>
        (.pure ⟨b, (E.digestKey enc).Ei c.1.1 c.2, o.1.1, ()⟩ :
          OComp lam (BindingOutcome I (I × ℕ) Unit))).run f) (bindingBad (openingRelation I))
    ≤ prob ((Ct.withTrace.bind fun c => ((Pt c.1.2).bind fun o =>
          (A.commitAt o.1.1 o.1.2).mapO fun key => (o.1, (key, ()))).withTrace.bind fun o =>
        (verifyDigestKey A.withOpenings.V enc c.1.1 o.1.1 o.1.2).bind fun b =>
        (.pure ⟨b, (E.digestKey enc).Ei c.1.1 c.2, o.1.1, ()⟩ :
          OComp lam (BindingOutcome I (I × ℕ) Unit))).run f) (bindingBad (openingRelation I))
  rw [run_bind, run_bind, prob_bind, prob_bind]
  refine expect_mono _ fun c => ?_
  refine le_trans (le_of_eq (OComp.prob_run_withTrace_bind f (Pt c.1.2)
      (fun o => ((A.digestKey enc).withOpenings.V c.1.1 o.1 o.2).bind fun b =>
        (.pure ⟨b, (E.digestKey enc).Ei c.1.1 c.2, o.1, ()⟩ :
          OComp lam (BindingOutcome I (I × ℕ) Unit))) _))
    (le_trans ?_ (le_of_eq (OComp.prob_run_withTrace_bind f
      ((Pt c.1.2).bind fun o => (A.commitAt o.1.1 o.1.2).mapO fun key => (o.1, (key, ())))
      (fun o => (verifyDigestKey A.withOpenings.V enc c.1.1 o.1 o.2).bind fun b =>
        (.pure ⟨b, (E.digestKey enc).Ei c.1.1 c.2, o.1, ()⟩ :
          OComp lam (BindingOutcome I (I × ℕ) Unit))) _).symm))
  rw [OComp.bind_bind, run_bind, run_bind, prob_bind, prob_bind]
  exact expect_mono _ fun o =>
    withOpenings_step A hcode f c.1.1 o.1 ((E.digestKey enc).Ei c.1.1 c.2) _

end ZKCP
