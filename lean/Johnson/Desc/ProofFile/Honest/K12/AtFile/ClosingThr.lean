-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/ClosingThr.lean: at a stand of the first chain's thread in
front of its proximity test: the way in returns, and the state on entry `doorL` takes no default and
agrees with the record that the way in returns, but for the rows' targets: at EVERY front that shows
just the rounds of the stand. General in the thread's letters.

  `enters_of_shape`   the chain's book-keeping at the test's place and no mark: the way in returns
  `enters_of_form`    so at a stand that meets the thread's clause (P) there
  `door_of_made`      the description's own fold at any columns: the door is at hand and agrees
  `door_at_thr`       the statement at a stand of `Thr`

By what. The thread's clause (P), `Thread.Form`: `form` says no mark, `formP` is the table's promise
`onAt` (Johnson/Desc/First/Borders.lean), which holds `shapeAt`: the chain stands at its finish and
no count of rows waits. The thread's clause (X), `Thread.Made`: the description's own fold over the
blocks in front returns s at the rounds seen and at the columns read. `doorTryZ_of_fold`
(K12/Blind/DoorL.lean) takes any columns, so the door's made-up columns give the same state once
wiped; `doorZ_agree`, `atHandZ_of_try`, `enterFinish_alike` there.

Hypotheses of `door_at_thr`. hcut, hlen: the thread's list is cut at the test's block, with b blocks
in front. hp: no block in front bears its place. hk: every block in front keeps the wiping
(`keepsInFront_L`, K12/Blind/KeepsAtFinish.lean, pays that in the goals' scope). hps: the thread's
places stand the test's place at border b. hstart: `start` is the chain's first state at every input.

Limits.
- hcut, hlen, hp, hk, hps and hstart are letters' facts, asked here; nothing ties `L.ps` to `L.bs`.
- A stand of `Thr` is a hypothesis: that a run reaches one is not said here.
- What agrees with the verifier's record agrees but for targets: `doorL`'s value is not that record.
- The fronts spoken of show just the rounds of the stand. At a front that shows other rounds nothing
  is said.
- Nothing on completeness, soundness or hiding.

NOT IN FRONT OF A LAW OVER COINS: `enters_of_form`, `door_at_thr` bear this label; the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean. Their ground: the thread's clauses (P) and (X), read at a stand of `Thr` as a premise.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingStand
import Johnson.Desc.ProofFile.Honest.K12.Blind.DoorL
import Johnson.Desc.ProofFile.Honest.K12.AtProof.Places
import Johnson.Desc.ProofFile.Honest.Thread.First

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open VerifiableInference.Desc (Block Place OpenedColumn foldBlocks)
open VerifiableInference.Desc.K12 (T12 enterFinish)
open VerifiableInference.Desc.First (S ModelPart shapeAt standOf standAt mayWait onAt Stand)
open ProofFile.Honest.K10 (Keeps wipeS)
open ProofFile.Honest.K12.AtProof (placeL)
open ProofFile.Honest.K12.Blind (doorL atHandL atHandZ_of_try doorZ_agree doorTryZ_of_fold
  enterFinish_alike)

/-- **The chain stands at its finish, no count waits and no mark: the way in returns.** -/
theorem enters_of_shape {links : List ModelPart} {s : S}
    (h : shapeAt links (some placeL) s = true) (hf : s.failed.isNone = true) :
    ∃ T, enterFinish s = .ok T := by
  have e1 : standAt links placeL = Stand.fin := rfl
  have e2 : mayWait links placeL = false := rfl
  have h' : (standOf s == standAt links placeL && (s.noneWaits || mayWait links placeL) &&
      s.link?.all fun L => placeL.link == some L.link) = true := h
  rw [e1, e2, Bool.or_false] at h'
  simp only [Bool.and_eq_true, beq_iff_eq] at h'
  obtain ⟨⟨h1, h2⟩, -⟩ := h'
  obtain ⟨o, ho⟩ : ∃ o, s.here = .fin o := by
    cases hx : s.here <;> simp only [standOf, hx] at h1 <;> first
      | exact ⟨_, rfl⟩
      | cases h1
      | (split at h1 <;> cases h1)
  refine ⟨{ st := s.st, book := s.book, roots := s.roots, g := o.fr.group, pass := .nothing
            mask := o.mask }, ?_⟩
  simp only [enterFinish, ho, h2, hf]
  rfl

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok M : Type}

/-- **At the thread's clause (P), at a border in front of the test's place, the way in returns.** -/
theorem enters_of_form (L : ProofFile.Honest.FirstThread.Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok M) {b : ℕ}
    (hps : L.ps[b]? = some placeL) {k : Coins Bk} {s : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} (h : L.thread.Form b k s m) : ∃ T, enterFinish s = .ok T := by
  obtain ⟨h1, h2⟩ := h
  have hf : s.failed.isNone = true := h1
  have h3 : onAt L.N L.mgP L.links L.ps[b]?
      (((VerifiableInference.Desc.First.openSets L.links L.ps
        (VerifiableInference.Desc.First.start L.links))[b]?).getD [])
      (((VerifiableInference.Desc.First.pubSets L.mgP.more L.links L.ps)[b]?).getD [])
      (L.thread.seat k m s) ProofFile.Honest.FirstThread.noStrs := h2
  rw [hps] at h3
  obtain ⟨-, h4⟩ := h3
  rcases h4 with h4 | ⟨h4, -⟩
  · exact absurd (Option.isNone_iff_eq_none.1 hf) h4
  · simp only [Bool.and_eq_true] at h4
    exact enters_of_shape h4.1.1.1.1.1 hf

/-- **Where the description's own fold over the blocks in front returns s at the stand's rounds, at
any columns, the door is at hand and agrees with the record that the way in returns.** -/
theorem door_of_made {W Y : Type} (bs pre t : List (Block S Cl)) (blk : Block S Cl)
    (hcut : bs = pre ++ blk :: t) (hp : ∀ y ∈ pre, y.place ≠ blk.place)
    (hk : ∀ y ∈ pre, Keeps wipeS 0 y) (start : W → S) (fall : T12) (w : W) (fr : Front Y) {s : S}
    {cs : List OpenedColumn} (h : foldBlocks 0 pre (start w) fr.seen.rounds cs = .ok (s, [], [])) {T : T12}
    (hT : enterFinish s = .ok T) :
    atHandL bs start blk.place w fr = true ∧
      Blind.Agree (doorL bs start blk.place fall w fr) T := by
  have e := doorTryZ_of_fold wipeS enterFinish pre t blk hp hk enterFinish_alike start w fr
    (cs := cs) (r := (s, [], [])) h
  rw [← hcut] at e
  have e' : Blind.doorTryZ enterFinish bs start blk.place w fr = (enterFinish s).map Blind.wipeT := e
  refine ⟨?_, doorZ_agree fall e' hT⟩
  have a := atHandZ_of_try e'
  rw [hT] at a
  exact a

/-- **At a stand of the thread in front of the test: the way in returns, and at every front that shows
just the stand's rounds the door takes no default and agrees with what the way in returns.** -/
theorem door_at_thr (L : ProofFile.Honest.FirstThread.Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok M) {b : ℕ}
    (pre t : List (Block S Cl)) (blk : Block S Cl) (hcut : L.bs = pre ++ blk :: t)
    (hlen : pre.length = b) (hp : ∀ y ∈ pre, y.place ≠ blk.place)
    (hk : ∀ y ∈ pre, Keeps wipeS 0 y) (hps : L.ps[b]? = some placeL)
    (start : Local W₀ Rc Xi Tr → S) (hstart : ∀ w, start w = L.first (L.pubOf w.x)) (fall : T12)
    {k : Coins Bk} {s : S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
    (h : Thr L.thread b k s m E) :
    ∃ T, enterFinish s = .ok T ∧ ∀ fr : Front X, fr.seen.rounds = m.seen →
      atHandL L.bs start blk.place m.st.input fr = true ∧
        Blind.Agree (doorL L.bs start blk.place fall m.st.input fr) T := by
  have h' := h
  unfold Thr Thread.Made at h'
  obtain ⟨-, -, hF, -, ⟨-, -, -, -, s₀, cols, hb, -, hf⟩, -, -⟩ := h'
  obtain ⟨T, hT⟩ := enters_of_form L hps hF
  refine ⟨T, hT, fun fr hr => ?_⟩
  have hb' : s₀ = L.first (L.pubOf m.st.input.x) := hb
  have hf' : foldBlocks 0 (L.bs.take b) s₀ (m.seen.drop 0) cols = .ok (s, [], []) := hf
  have e1 : L.bs.take b = pre := by
    rw [hcut, ← hlen]
    exact List.take_left' rfl
  rw [e1, List.drop_zero, hb', ← hstart, ← hr] at hf'
  exact door_of_made L.bs pre t blk hcut hp hk start fall m.st.input fr hf' hT

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.enters_of_shape
#print axioms ProofFile.Honest.K12.enters_of_form
#print axioms ProofFile.Honest.K12.door_of_made
#print axioms ProofFile.Honest.K12.door_at_thr
