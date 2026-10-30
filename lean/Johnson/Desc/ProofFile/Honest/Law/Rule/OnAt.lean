-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/OnAt.lean: `On`, from `Owed.owed` (Honest/Owed.lean), for one
chain. Take a part before which the verifier has not rejected, which is given its coins and has
played its rounds, and whose keys form one contiguous stretch of its chain's keys. Then the
parameter `On` of its list holds at the blocks that the part carries, at the state of the prover's
run, and at what has been produced before the part (`on_chain`). The chain's own lemmas on the run
at an address (Honest/Law/RunAtFile.lean, Honest/Law/RunMidFile.lean, Honest/Law/RunBefore.lean;
Honest/Law/Rule/MidDry.lean, Honest/Law/Rule/OpenedRun.lean) are hypotheses here;
Honest/Law/Rule/OnFile.lean supplies them. The state of `Owed.owed` and the state at which `On` is
wanted are shown to be one field by field; for the field `opened` by `OpenedAt`
(Honest/Law/Rule/OpenedAt.lean) at both: `hopen`, which `row_here` (Honest/Law/Rule/RowHere.lean)
hands, and the last clause of `hmid`. It is
the fifteenth piece of the proof of `rowOk_of` (Honest/Law/Rule/Bridge.lean: from `Owed` to
`RowOk`).

  1  `seat_inv`, `asked_is`   two small lemmas
  2  `on_at`   `Lettered.owedAt`, read at one `Member`
  3  `on_chain`   the main lemma

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.RunAtFile
import Johnson.Desc.ProofFile.Honest.Law.Rule.OnTools
import Johnson.Desc.ProofFile.Honest.Law.Rule.Seat
import Johnson.Desc.ProofFile.Honest.Law.Rule.Reads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place Oracle)

variable {Xi S Cl V W Y Pb : Type}

/-! ## 1 Two small lemmas -/

theorem seat_inv {Bk : ProverCoinCounts} {bs : List (Block S Cl)} {Ls : List (Lettered Bk S Cl V W Y Pb)}
    {b : Block S Cl} {p : Side S Cl V W Y Pb × OnT V W Y Pb} (h : seatOf bs Ls b = some p) :
    ∃ L ∈ Ls, L.side bs = some p.1 ∧ p.2 = L.On := by
  unfold seatOf at h
  cases hh : Ls.find? fun L => L.place == b.place with
  | none =>
    rw [hh] at h
    cases h
  | some L =>
    rw [hh] at h
    have h' : ((L.side bs).map fun σ => (σ, L.On)) = some p := h
    cases hs : L.side bs with
    | none =>
      rw [hs] at h'
      cases h'
    | some σ =>
      rw [hs] at h'
      have e : (σ, L.On) = p := Option.some.inj h'
      subst e
      exact ⟨L, List.mem_of_find?_eq_some hh, hs, rfl⟩

/-- The stored positions that a run reads are those that the declared rounds read. -/
theorem asked_is {F : FileDescription Xi} {ρ : Draws} {stored : Nat → Nat → Option (List UInt64)} (r : Run)
    (h : RunOk F ρ stored r.played.1 r.played.2.1 r.played.2.2 r.reads.1 r.reads.2.1 r.reads.2.2) :
    r.storedAsked = storedAsks F ρ := by
  unfold Run.storedAsked storedAsks
  rw [← h.bare, List.filterMap_map]
  rfl

/-! ## 2 `owedAt` at one `Member` -/

theorem on_at {Bk : ProverCoinCounts} (ch : Nat) (bs : List (Block S Cl)) (L : Lettered Bk S Cl V W Y Pb)
    (σ : Side S Cl V W Y Pb) (hσ : L.side bs = some σ) (u : Member V W Y Pb) (hu : u ∈ σ.members)
    (k : Coins Bk) (mid : Addr → Except Refusal (Mid W Y)) (r : Run)
    (st : List (Nat × Nat × List UInt64)) (called : Addr → Bool)
    (howed : L.owedAt bs k ch mid r st called)
    (hc : called ⟨σ.block.place, u.number⟩ = true) {c : u.part.Coins}
    (hl : lendPart Bk (Bk.rowsOf ch) (k.look ch) ⟨σ.block.place, u.number⟩ u.part = .ok c)
    {m : Mid W Y} (hm : ∀ m', mid ⟨σ.block.place, u.number⟩ = .ok m' → m' = m) {front : Before}
    (hb : r.beforeAt st ⟨σ.block.place, u.number⟩ = front) : L.On u c.2.2 m front := by
  obtain ⟨-, h2, -⟩ := side_ok hσ
  rw [h2] at hc hl hm hb
  obtain ⟨ca, m', g1, g2, g3⟩ := (howed σ hσ u hu).2 hc
  rw [hm m' g2, hb] at g3
  unfold carriedAt at g1
  rw [hl] at g1
  cases g1
  exact g3

/-! ## 3 The main lemma -/

/-- **`On`, at a part of one chain.** `ss`, `dsAll`, `pl`: the chain's `Step`s, challenges and
rounds as produced. `base`: what a part of this chain is shown of the other chains. `hA`, `hmid`,
`hbef`: the chain's own lemmas on the run at the address. `pr`: free; the callers lay `preOf`
(Honest/Rule.lean): `hopen` and the last clause of `hmid` say `OpenedAt`
(Honest/Law/Rule/OpenedAt.lean) at it, of the two states that are to be one. -/
theorem on_chain {F : FileDescription Xi} {Bk : ProverCoinCounts} {pr : List (Nat × Nat × List Fmt.DeclaredRound)}
    (ρ : Draws)
    (stored : Nat → Nat → Option (List UInt64)) (ch : Nat) (bs : List (Block S Cl))
    (L : Lettered Bk S Cl V W Y Pb) (σ : Side S Cl V W Y Pb) (hσ : L.side bs = some σ)
    (u : Member V W Y Pb) (hu : u ∈ σ.members) (k : Coins Bk)
    (mid : Addr → Except Refusal (Mid W Y)) (r : RunC F)
    (howed : L.owedAt bs k ch mid r.run (storedShown stored r.run.storedAsked) r.called)
    (hRO : RunOk F ρ stored r.run.played.1 r.run.played.2.1 r.run.played.2.2 r.run.reads.1
      r.run.reads.2.1 r.run.reads.2.2)
    (ss : List (Step W Y)) (dsAll : List Fmt.Drawn)
    (keys : List (Addr × Option (State W Y → Y))) (hk : ss.map Step.key = keys) (m₀ : Mid W Y)
    (pl : List Played)
    (hA : ss.any (·.addr == ⟨σ.block.place, u.number⟩) = true →
      At r.run ⟨σ.block.place, u.number⟩ ch pl ss dsAll)
    (base : List (Nat × Shown × Fmt.Drawn)) (tree : Nat → List Nat)
    (hmid : ss.any (·.addr == ⟨σ.block.place, u.number⟩) = true →
      ((ss.drop (ss.takeWhile fun s => s.addr != ⟨σ.block.place, u.number⟩).length).take
        (ss.filter fun s => s.addr == ⟨σ.block.place, u.number⟩).length =
          ss.filter fun s => s.addr == ⟨σ.block.place, u.number⟩) →
      r.called ⟨σ.block.place, u.number⟩ = true → ∀ m', mid ⟨σ.block.place, u.number⟩ = .ok m' →
      m'.seen = roundsOff base ++ roundsOf (pl.take
        (ss.takeWhile fun s => s.addr != ⟨σ.block.place, u.number⟩).length) ∧
      m'.st = (dryAt keys dsAll m₀ ⟨σ.block.place, u.number⟩).st ∧
      m'.loc = (dryAt keys dsAll m₀ ⟨σ.block.place, u.number⟩).loc ∧
      OpenedAt pr m' (r.run.beforeAt (storedShown stored (storedAsks F ρ))
        ⟨σ.block.place, u.number⟩))
    (hbef : ss.any (·.addr == ⟨σ.block.place, u.number⟩) = true →
      ((ss.drop (ss.takeWhile fun s => s.addr != ⟨σ.block.place, u.number⟩).length).take
        (ss.filter fun s => s.addr == ⟨σ.block.place, u.number⟩).length =
          ss.filter fun s => s.addr == ⟨σ.block.place, u.number⟩) →
      ∀ st, r.run.beforeAt st ⟨σ.block.place, u.number⟩ = ⟨base ++ shownBy ch tree (pl.take
        (ss.takeWhile fun s => s.addr != ⟨σ.block.place, u.number⟩).length) 0, st⟩)
    (v : Option V) (ds : List Fmt.Drawn) (Z : Stand F) (c : u.part.Coins) (m : Mid W Y)
    (y₁ : List Played × Mid W Y) (lp la : List Played)
    (kp ku kq : List (Addr × Option (State W Y → Y)))
    (hfront : Z.laid.front ch (storedShown stored (storedAsks F ρ)) =
      ⟨base ++ shownBy ch tree lp 0, storedShown stored (storedAsks F ρ)⟩)
    (hfin : pl = lp ++ y₁.1 ++ la) (hne : y₁.1 ≠ [])
    (hseg : SegAt keys ⟨σ.block.place, u.number⟩ kp ku kq) (hlp : lp.length = kp.length)
    (hl : lendPart Bk (Bk.rowsOf ch) (k.look ch) ⟨σ.block.place, u.number⟩ u.part = .ok c)
    (hplay : play (u.part.steps σ.block.name ⟨σ.block.place, u.number⟩ u.rounds v c) ds [] m =
      .ok y₁)
    (e1 : (dryAt keys dsAll m₀ ⟨σ.block.place, u.number⟩).st = m.st)
    (e2 : (dryAt keys dsAll m₀ ⟨σ.block.place, u.number⟩).loc = m.loc)
    (hseen : m.seen = (Z.laid.front ch (storedShown stored (storedAsks F ρ))).seen)
    (hopen : OpenedAt pr m (Z.laid.front ch (storedShown stored (storedAsks F ρ)))) :
    L.On u c.2.2 m (Z.laid.front ch (storedShown stored (storedAsks F ρ))) := by
  obtain ⟨hin, hn, hlen, hany⟩ := hseg.steps hk
  have htake : pl.take kp.length = lp := by
    rw [hfin, List.append_assoc]
    exact List.take_left' hlp
  have hdrop : pl.drop kp.length = y₁.1 ++ la := by
    rw [hfin, List.append_assoc]
    exact List.drop_left' hlp
  have hsegL : (ss.drop (ss.takeWhile fun s => s.addr != ⟨σ.block.place, u.number⟩).length).take
        (ss.filter fun s => s.addr == ⟨σ.block.place, u.number⟩).length = ss.filter fun s => s.addr
            == ⟨σ.block.place, u.number⟩ := by
    rw [hn, hlen]
    exact (filter_stretch _ _ _ _ hin.front hin.own hin.behind).symm
  have hpos : 0 < ku.length :=
    Nat.pos_of_ne_zero fun e => hseg.pos (List.eq_nil_of_length_eq_zero e)
  have hcalled : r.called ⟨σ.block.place, u.number⟩ = true :=
    called_of (hA hany) hin hpos (by
      rw [hdrop]
      exact head_told hplay (part_moves _ _ _ _ _ _) hne la)
  have hb := hbef hany hsegL (storedShown stored (storedAsks F ρ))
  rw [hn, htake, ← hfront] at hb
  rw [asked_is r.run hRO] at howed
  refine on_at ch bs L σ hσ u hu k mid r.run _ r.called howed hcalled hl (fun m' hm' => ?_) hb
  obtain ⟨s1, s2, s3, s4⟩ := hmid hany hsegL hcalled m' hm'
  have h4 : m'.opened = m.opened := by
    unfold OpenedAt at s4 hopen
    rw [s4, hb, hopen]
  refine mid_ext (s2.trans e1) (s3.trans e2) ?_ h4
  rw [s1, hn, htake, hseen, hfront]
  show _ = roundsOff (base ++ shownBy ch tree lp 0)
  unfold roundsOff
  rw [List.map_append]
  show _ = roundsOff base ++ roundsOff (shownBy ch tree lp 0)
  rw [roundsOff_by]
  rfl

end ProofFile.Honest

#print axioms ProofFile.Honest.seat_inv
#print axioms ProofFile.Honest.asked_is
#print axioms ProofFile.Honest.on_at
#print axioms ProofFile.Honest.on_chain
