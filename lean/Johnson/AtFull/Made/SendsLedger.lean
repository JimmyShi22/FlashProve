-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/SendsLedger.lean: `Johnson.G.sendsFrom` returns seven given chains, FROM ITS
ELEVEN STEPS' RETURNS: four small ones (`wSend` and `linSharedSends`, for the key and for the proof)
and seven calls of its inner routine `oneOf` (Johnson/G/SendsListed.lean), one a chain. Over the
law `sendsFrom_one` (that file; := rfl).

  `sendsFrom_of_parts`: the ledger, at any record c whose key and proof have three plans each.
  `sendsFrom_free`: `sendsFrom` reads neither the seven strings of bytes nor the digest: := rfl.

Limits. A JOINING. IT PAYS NO PREMISE. No soundness is claimed.
-/
import Johnson.G.SendsListed
import Johnson.G.MadeFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params Johnson.G Johnson.G.MadeFree

/-- sendsFrom reads neither the bytes nor the digest. -/
theorem sendsFrom_free (c : Configured) : sendsFrom c = sendsFrom ((freeOf c).at Hung.none) := rfl

/-- **`sendsFrom` returns.** -/
theorem sendsFrom_of_parts {c : Configured} {k0 k1 k2 p0 p1 p2 : Planned} {w1 w2 : Listed}
    {s1 s2 : List Listed} {K0 K1 K2 En P0 P1 P2 : ChainSends}
    (hk : c.key = [k0, k1, k2]) (hp : c.proof = [p0, p1, p2])
    (a₁ : wSend c.sized.key.once.shape = .ok w1)
    (a₂ : linSharedSends c.sized.key.once.shape c.sized.set.samples = .ok s1)
    (a₃ : wSend c.sized.proof.batch.shape = .ok w2)
    (a₄ : linSharedSends c.sized.proof.batch.shape c.sized.set.samples = .ok s2)
    (b₀ : oneOf "key" 0 c.sized.key.codes
      ([⟨"the index-mask message", [c.sized.key.once.input]⟩,
        ⟨"the multiplicities", (Wf.messageOf c.sized.key.ranges.x).toList⟩] ++
        ioppSends "the ranges' test" c.sized.set.samples c.sized.key.ranges.x.choice.masksRide 1
          c.sized.key.ranges.x.stages ++ [w1]) k0 = .ok K0)
    (b₁ : oneOf "key" 1 c.sized.key.codes s1 k1 = .ok K1)
    (b₂ : oneOf "key" 2 c.sized.key.codes (ioppSends "the own test" c.sized.set.samples
      c.sized.key.once.shape.choice.masksRide 1 c.sized.key.once.shape.testOwn) k2 = .ok K2)
    (b₃ : oneOf "entry" 0 c.sized.entryCodes
      (⟨"the link's message", (linkMessage c.sized.link.shape c.sized.set.samples).toList⟩ ::
        ioppSends "the link's test" c.sized.set.samples c.sized.link.shape.choice.masksRide 1
          c.sized.link.shape.test) c.entry = .ok En)
    (b₄ : oneOf "proof" 0 c.sized.proof.codes
      (frameSends c.sized.proof c.sized.set.samples 0 (reqGroups c.sized.proof.request).toList
        c.sized.proof.request.link ++ [w2]) p0 = .ok P0)
    (b₅ : oneOf "proof" 1 c.sized.proof.codes s2 p1 = .ok P1)
    (b₆ : oneOf "proof" 2 c.sized.proof.codes (ioppSends "the own test" c.sized.set.samples
      c.sized.proof.batch.shape.choice.masksRide 1 c.sized.proof.batch.shape.testOwn) p2 =
      .ok P2) :
    sendsFrom c = .ok [K0, K1, K2, En, P0, P1, P2] := by
  rw [sendsFrom_one, hk, hp]
  simp only [a₁, a₂, a₃, a₄, b₀, b₁, b₂, b₃, b₄, b₅, b₆, bind, Except.bind, List.mapM_cons,
    List.mapM_nil, id, pure, Except.pure]

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.sendsFrom_free
#print axioms Johnson.AtFull.Made.sendsFrom_of_parts
