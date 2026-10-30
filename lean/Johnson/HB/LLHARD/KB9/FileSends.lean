-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB9/FileSends.lean: THE SENDINGS THAT ARE MADE ANEW OF A KEY FILE's THREE CHAINS
AS READ (`sendsOfKey`, Johnson/Desc/Key/Source.lean) ARE THE FIRST THREE OF WHAT
`Johnson.G.sendsFrom` MAKES OF THE PLANNER's VALUE. General: no written value, nothing asked of
Lean's kernel. With it the named test "made" has no premise on `sendsOfKey` left: of the sendings it
takes the return of `sendsFrom` alone, which is a premise still.

Why. `sendsFrom` walks a planner's priced rounds by an inner routine; Johnson/IMR/KeySendsOne.lean
has that routine under a name (`IM.oneSend`) and what `sendsFrom`'s return says of its first three
(`IM.sendsFrom_key`). `sendsOfChain` is, by its own head, that
routine's text at a plan's entries as read. A planner's plan has as entries its rounds' entries, by
definition (`Planned.plan`, OnBytes/Params/Planner.lean). So the two agree.

  `a_mapM_map`: a step along a list that was mapped.
  **`one_eq`**: `IM.oneSend file ch codes l P = sendsOfChain file ch codes l P.plan.entries`.
  **`sends_of_from`**: where `sendsFrom made` returns a list that begins with k0, k1, k2, made has
    three plans for the key, the three plans as read are these, four items as read are the sized
    ones, and the plan's number of answers is the setting's: `sendsOfKey k = .ok (k0, k1, k2)`.
  **`made_of_from`**: so the clause "made" (`made_ok`, Johnson/HB/LLHARD/KB9/FileMade.lean) at what
    `sourceOf m` returns.

Limits. Every return is a premise; so are the equations on the chains as read. Nothing on what the
sendings are. Nothing on soundness.
-/
import Johnson.HB.LLHARD.KB9.FileMade
import Johnson.IMR.KeySendsOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB9
open OnBytes OnBytes.Params
open Johnson.G (Listed Sending ChainSends sendsFrom)
open Johnson.G.OfPlan (Made)
open VerifiableInference.Desc.Key (sendsOfChain sendsOfKey madeAgainOk sourceOf Source)

/-- A step along a list that was mapped. -/
theorem a_mapM_map {α β γ : Type} (f : α → β) (g : β → Except String γ) :
    ∀ l : List α, (l.map f).mapM g = l.mapM fun x => g (f x)
  | [] => rfl
  | a :: l => by
    rw [List.map_cons, List.mapM_cons, List.mapM_cons, a_mapM_map f g l]

/-- **The inner routine of `sendsFrom` is `sendsOfChain` at the plan's entries.** -/
theorem one_eq (file : String) (ch : Nat) (codes : Codes) (l : List Listed) (P : Planned) :
    IM.oneSend file ch codes l P = sendsOfChain file ch codes l P.plan.entries := by
  have eS : ((P.rounds.map (·.entry)).zipIdx.filter fun r => r.1.name == "SEND seed") =
      (P.rounds.zipIdx.filter fun r => r.1.entry.name == "SEND seed").map
        (Prod.map (·.entry) id) := by
    rw [List.zipIdx_map, List.filter_map]
    rfl
  have eR : ∀ i : Nat, (P.rounds.map (·.entry)).toArray[i]? =
      (P.rounds.toArray[i]?).map PlanRound.entry := by
    intro i
    rw [List.getElem?_toArray, List.getElem?_toArray, List.getElem?_map]
  have eP : P.plan.entries = P.rounds.map (·.entry) := rfl
  unfold IM.oneSend sendsOfChain
  rw [eP]
  dsimp only
  rw [eS, List.length_map, List.zip_map_left, a_mapM_map]
  have eF : (fun x : (PlanRound × Nat) × Listed =>
      (match Prod.map (Prod.map (·.entry) id) id x with
      | (r, s) => do
        unless treesOf codes s.sent.toArray == some r.1.roots do
          throw s!"{file} {ch}, entry {r.2 + 1} ({s.label}): the trees are not the entry's roots"
        match (P.rounds.map (·.entry)).toArray[r.2 + 1]? with
        | some b => pure (⟨r.2 + 1, s.label, s.sent, r.1, b⟩ : Sending)
        | none => throw s!"{file} {ch}, entry {r.2 + 1}: no entry behind it" :
        Except String Sending)) =
      fun x => (match x with
      | (r, s) => do
        unless treesOf codes s.sent.toArray == some r.1.entry.roots do
          throw s!"{file} {ch}, entry {r.2 + 1} ({s.label}): the trees are not the entry's roots"
        match P.rounds.toArray[r.2 + 1]? with
        | some b => pure (⟨r.2 + 1, s.label, s.sent, r.1.entry, b.entry⟩ : Sending)
        | none => throw s!"{file} {ch}, entry {r.2 + 1}: no entry behind it" :
        Except String Sending) := by
    funext x
    obtain ⟨⟨r, i⟩, s⟩ := x
    dsimp only [Prod.map, id]
    rw [eR]
    cases P.rounds.toArray[i + 1]? <;> rfl
  exact (congrArg (fun F => (do
    unless (P.rounds.zipIdx.filter fun r => r.1.entry.name == "SEND seed").length == l.length do
      throw s!"{file} {ch}: {l.length} sendings listed, {(P.rounds.zipIdx.filter fun r =>
        r.1.entry.name == "SEND seed").length} entries SEND seed"
    let out ← ((P.rounds.zipIdx.filter fun r => r.1.entry.name == "SEND seed").zip l).mapM F
    pure ⟨file, ch, codes, out⟩ : Except String ChainSends)) eF).symm

/-- **What is made anew of the chains as read is what was made of the planner's value.** -/
theorem sends_of_from {made : Configured} {k : KeyChains} {P1 P2 P3 : Planned}
    {k0 k1 k2 : ChainSends} {r : List ChainSends}
    (hs : sendsFrom made = .ok (k0 :: k1 :: k2 :: r)) (hk : made.key = [P1, P2, P3])
    (q1 : k.oneTime.given.plan = P1.plan) (q2 : k.shared.given.plan = P2.plan)
    (q3 : k.second.given.plan = P3.plan)
    (i1 : k.oneTime.indexMasks = made.sized.key.once.input)
    (i2 : k.oneTime.ranges = made.sized.key.ranges.x)
    (i4 : k.oneTime.codes = made.sized.key.codes)
    (i5 : k.oneTime.lin = made.sized.key.once.shape)
    (ha : k.oneTime.given.plan.samples = made.sized.set.samples) :
    sendsOfKey k = .ok (k0, k1, k2) := by
  obtain ⟨w, s, a1, a2, a3, a4, a5⟩ := IM.sendsFrom_key hs hk
  rw [one_eq] at a3 a4 a5
  refine sendsOfKey_of (w := w) (sh := s) ?_ ?_ ?_ ?_ ?_
  · rw [i5]
    exact a1
  · rw [i5, ha]
    exact a2
  · rw [i4, i1, i2, ha, q1]
    exact a3
  · rw [i4, q2]
    exact a4
  · rw [i4, i5, ha, q3]
    exact a5

/-- **THE CLAUSE "made", WITH NO PREMISE ON `sendsOfKey`**: of the sendings it takes what
`sendsFrom` returned. -/
theorem made_of_from {m : Made} {X : Source} (r1 : sourceOf m = .ok X) {P1 P2 P3 : Planned}
    {r : List ChainSends}
    (hs : sendsFrom m.p.chains.made = .ok (m.key.1 :: m.key.2.1 :: m.key.2.2 :: r))
    (hk : m.p.chains.made.key = [P1, P2, P3])
    (q1 : m.p.chains.key.oneTime.given.plan = P1.plan)
    (q2 : m.p.chains.key.shared.given.plan = P2.plan)
    (q3 : m.p.chains.key.second.given.plan = P3.plan)
    (i1 : m.p.chains.key.oneTime.indexMasks = m.p.chains.made.sized.key.once.input)
    (i2 : m.p.chains.key.oneTime.ranges = m.p.chains.made.sized.key.ranges.x)
    (i4 : m.p.chains.key.oneTime.codes = m.p.chains.made.sized.key.codes)
    (i5 : m.p.chains.key.oneTime.lin = m.p.chains.made.sized.key.once.shape)
    (ha : m.p.chains.key.oneTime.given.plan.samples = m.p.chains.made.sized.set.samples) :
    madeAgainOk X.Y = true :=
  made_ok r1 i5 (sends_of_from hs hk q1 q2 q3 i1 i2 i4 i5 ha)

end Johnson.KB9

#print axioms Johnson.KB9.a_mapM_map
#print axioms Johnson.KB9.one_eq
#print axioms Johnson.KB9.sends_of_from
#print axioms Johnson.KB9.made_of_from
