-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/KeySendsOne.lean: a light file: sendsFrom's inner routine under a name,
and what sendsFrom's return says of its first three. It comes out of the file
IMR/KeySendsLaw.lean, which is not in this library, so that it
stands over Johnson/G/SendsFrom.lean and the tool exc_bind alone. Every name
is IM.‹name›.

What is said.
  oneSend          sendsFrom's inner routine «one» (Johnson/G/SendsFrom.lean), to the token, under a
                   name of its own: a chain's list of sendings of its codes, the listed sendings and
                   its priced plan. That it is that routine is Lean's word: a «rfl» in
                   sendsFrom_key.
  keyListed0       the list that sendsFrom hands it for the key file's first chain.
  sendsFrom_key    **a law by unfolding** (after sendsFrom_key_codes,
                   Johnson/RunOne/Law/KeyInScope.lean): where sendsFrom c returns k0 :: k1 :: k2 ::
                   r and c.key = [K0, K1, K2]: k0, k1, k2 are what oneSend returns at c.sized.key,
                   c.sized.set.samples and K0, K1, K2. General in c: no evaluation, no written
                   value. It reads nothing of the proof file's sizes or plans.
A kin, not a twin: Key.sendsOfChain (Johnson/Desc/Key/Source.lean; by its own head «the
function one inside sendsOf, its text, at a plan's entries as read») walks a plan's entries; oneSend
walks the priced rounds, as sendsFrom does. That the two agree at P.plan.entries is a lemma
(`one_eq`, Johnson/HB/LLHARD/KB9/FileSends.lean), not shown here.
What is not claimed. That sendsFrom returns anywhere. Nothing on written values. No soundness.

-/
import Johnson.G.SendsFrom
import OnBytes.Params.ConfigureLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IM

open OnBytes OnBytes.Params
open Johnson.G
open OnBytes.Params (exc_bind)

/-- sendsFrom's inner routine, to the token. -/
def oneSend (file : String) (ch : Nat) (codes : Codes) (l : List Listed) (P : Planned) :
    Except String ChainSends := do
  let R := P.rounds.toArray
  let seeds := P.rounds.zipIdx.filter fun r => r.1.entry.name == "SEND seed"
  unless seeds.length == l.length do
    throw s!"{file} {ch}: {l.length} sendings listed, {seeds.length} entries SEND seed"
  let out ← (seeds.zip l).mapM fun (r, s) => do
    unless treesOf codes s.sent.toArray == some r.1.entry.roots do
      throw s!"{file} {ch}, entry {r.2 + 1} ({s.label}): the trees are not the entry's roots"
    match R[r.2 + 1]? with
    | some b => pure (⟨r.2 + 1, s.label, s.sent, r.1.entry, b.entry⟩ : Sending)
    | none => throw s!"{file} {ch}, entry {r.2 + 1}: no entry behind it"
  pure ⟨file, ch, codes, out⟩

/-- The sendings that sendsFrom lists for the key file's first chain; w: W's. -/
def keyListed0 (z : Plan.KeySized) (a : Nat) (w : Listed) : List Listed :=
  [⟨"the index-mask message", [z.once.input]⟩,
    ⟨"the multiplicities", (Wf.messageOf z.ranges.x).toList⟩] ++
    ioppSends "the ranges' test" a z.ranges.x.choice.masksRide 1 z.ranges.x.stages ++ [w]

/-- **What sendsFrom's return says of its first three.** -/
theorem sendsFrom_key {c : Configured} {k0 k1 k2 : ChainSends} {r : List ChainSends}
    {K0 K1 K2 : Planned} (h : sendsFrom c = .ok (k0 :: k1 :: k2 :: r))
    (hk : c.key = [K0, K1, K2]) :
    ∃ w s, wSend c.sized.key.once.shape = .ok w ∧
      linSharedSends c.sized.key.once.shape c.sized.set.samples = .ok s ∧
      oneSend "key" 0 c.sized.key.codes (keyListed0 c.sized.key c.sized.set.samples w) K0 =
        .ok k0 ∧
      oneSend "key" 1 c.sized.key.codes s K1 = .ok k1 ∧
      oneSend "key" 2 c.sized.key.codes
        (ioppSends "the own test" c.sized.set.samples c.sized.key.once.shape.choice.masksRide 1
          c.sized.key.once.shape.testOwn) K2 = .ok k2 := by
  unfold sendsFrom at h
  extract_lets z a one K B x at h
  have e1 : one = oneSend := rfl
  rw [hk] at h
  split at h
  · rename_i q0 q1 q2 p0 p1 p2 hq hp
    obtain ⟨rfl, rfl, rfl⟩ : K0 = q0 ∧ K1 = q1 ∧ K2 = q2 := by
      simpa using hq
    obtain ⟨w1, hw1, h⟩ := exc_bind h
    obtain ⟨s1, hs1, h⟩ := exc_bind h
    obtain ⟨w2, _, h⟩ := exc_bind h
    obtain ⟨s2, _, h⟩ := exc_bind h
    rw [List.mapM_cons] at h
    obtain ⟨a0, h0, h⟩ := exc_bind h
    obtain ⟨r0, hr0, h⟩ := exc_bind h
    rw [List.mapM_cons] at hr0
    obtain ⟨a1, h1, hr0⟩ := exc_bind hr0
    obtain ⟨r1, hr1, hr0⟩ := exc_bind hr0
    rw [List.mapM_cons] at hr1
    obtain ⟨a2, h2, hr1⟩ := exc_bind hr1
    obtain ⟨r2, _, hr1⟩ := exc_bind hr1
    cases hr1
    cases hr0
    cases h
    rw [e1] at h0 h1 h2
    exact ⟨w1, s1, hw1, hs1, h0, h1, h2⟩
  · cases h

end IM

#print axioms IM.sendsFrom_key
