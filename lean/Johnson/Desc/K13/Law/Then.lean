-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/Then.lean: a rule for two blocks joined as one (`Block.andThen`), where the
second has no round: what the first owes and has, with what goes back over the second, is what the
joined block owes. General in the blocks and in the record. Statements with their proofs.
Main names:
  `roundsFit_length`, `regroup_length`, `openings_from`, `groupsOf_length`: counts of the format.
  `one_ok`, `one_of`: the fold at one block says yes exactly if the rounds are as many as the
    block's, the block's step says yes, and no column is left.
  `andThen_decide`, `step_then`: the joined block's decision and step.
  `Piece.then`, `out_then`: the joined piece; where it says yes, the first piece has said yes at the
    same transcript, and the second block's decision on the record that it left.
  `goodIn_then`: **the rule.**
Used of `verify-on-bytes`: nothing.

What is not claimed. Nothing where the second block has a round. The second block is handed no
round and no column: that it reads none is so by the format's cut. The errors are the first piece's.
That the joined piece is owed just its stretch and that its trees are listed, if the first piece is:
Johnson/Desc/K13/Law/Joint.lean.

-/
import Johnson.Desc.K13.Law.M3On

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes Iop Run
open OnBytes.Maker
open VerifiableInference.Desc.Sound (Frame Piece foldRun)

variable {T Cl W : Type}

/-- Rounds that have the declared form are as many as are declared. -/
theorem roundsFit_length : ∀ (ds : List Fmt.DeclaredRound) (rs : List Fmt.RoundView),
    roundsFit ds rs = true → rs.length = ds.length
  | [], [], _ => rfl
  | d :: ds, r :: rs, h => by
    unfold roundsFit at h
    have h' := (Bool.and_eq_true_iff.1 h).2
    rw [List.length_cons, List.length_cons, roundsFit_length ds rs h']
  | [], _ :: _, h => by simp [roundsFit] at h
  | _ :: _, [], h => by simp [roundsFit] at h

/-- As many groups of columns as lengths. -/
theorem regroup_length : ∀ (ns : List ℕ) (cols : List OpenedColumn), (regroup ns cols).length = ns.length
  | [], _ => rfl
  | _ :: ns, _ => congrArg (· + 1) (regroup_length ns _)

/-- The count of a block's groups, from any start. -/
theorem openings_from : ∀ (ds : List Fmt.DeclaredRound) (a : ℕ),
    ds.foldl (fun n r => n + r.stored.length + r.opens.length) a =
      a + (ds.map fun r => r.stored.length + r.opens.length).sum
  | [], a => by simp
  | d :: ds, a => by
    rw [List.foldl_cons, openings_from ds, List.map_cons, List.sum_cons]
    omega

/-- The groups that are read are as many as the rounds' stored parts and trees. -/
theorem groupsOf_length (ft : ℕ) : ∀ (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn),
    Rs.length = ds.length →
    (groupsOf ft ds Rs).length = (ds.map fun r => r.stored.length + r.opens.length).sum
  | [], [], _ => rfl
  | d :: ds, R :: Rs, h => by
    unfold groupsOf
    rw [List.length_append, List.length_append, List.length_map, List.length_map,
      groupsOf_length ft ds Rs (by simpa using h), List.map_cons, List.sum_cons]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- **Where the fold at one block says yes**: the rounds are as many as the block's, the block's
step has said yes, and no column is left. -/
theorem one_ok {name : String} {ft : ℕ} {b : Block T Cl} {s s' : T} {v : Fmt.View}
    (h : (chainAt name ft [b] s v).toOption = some s') :
    v.rounds.length = b.rounds.length ∧
      ∃ k, b.step ft s v.rounds v.opened = .ok (s', k) ∧ v.opened.drop k = [] := by
  unfold chainAt at h
  simp only [List.isEmpty_cons, Bool.false_eq_true, if_false] at h
  cases hfb : foldBlocks ft [b] s v.rounds v.opened with
  | error e =>
    rw [hfb] at h
    cases h
  | ok z =>
    obtain ⟨s1, rs1, c1⟩ := z
    rw [hfb] at h
    simp only [foldBlocks, List.splitAt_eq] at hfb
    split at hfb
    · cases hfb
    · next hlen =>
      split at hfb
      · cases hfb
      · next s2 k hst =>
        obtain ⟨rfl, rfl, rfl⟩ : s2 = s1 ∧ v.rounds.drop b.rounds.length = rs1 ∧
            v.opened.drop k = c1 := by
          have := Except.ok.inj hfb
          exact ⟨congrArg (·.1) this, congrArg (·.2.1) this, congrArg (·.2.2) this⟩
        cases hd : v.rounds.drop b.rounds.length with
        | cons _ _ =>
          rw [hd] at h
          cases h
        | nil =>
          cases hc : v.opened.drop k with
          | cons _ _ =>
            rw [hd, hc] at h
            cases h
          | nil =>
            rw [hd, hc] at h
            obtain rfl := Option.some.inj h
            have ht := List.take_of_length_le (List.drop_eq_nil_iff.1 hd)
            rw [ht] at hst hlen
            exact ⟨not_not.1 hlen, k, hst, hc⟩

/-- And the other way round. -/
theorem one_of {name : String} {ft : ℕ} {b : Block T Cl} {s s' : T} {v : Fmt.View} {k : ℕ}
    (hl : v.rounds.length = b.rounds.length) (hst : b.step ft s v.rounds v.opened = .ok (s', k))
    (hc : v.opened.drop k = []) : (chainAt name ft [b] s v).toOption = some s' := by
  unfold chainAt
  simp only [List.isEmpty_cons, Bool.false_eq_true, if_false, foldBlocks, List.splitAt_eq]
  rw [List.take_of_length_le (le_of_eq hl), List.drop_of_length_le (le_of_eq hl)]
  simp [hl, hst, hc, Except.toOption]

/-- The joined block's decision, on as many rounds and groups as the first block has. -/
theorem andThen_decide (nm : String) (p q : Block T Cl) (s : T) (RS : List Fmt.RoundView)
    (GS : List (List (Nat × List UInt64))) (h1 : RS.length = p.rounds.length)
    (h2 : GS.length = p.openings) :
    (p.andThen nm q).decide s RS GS = (p.decide s RS GS).bind fun m => q.decide m [] [] := by
  show (p.decide s (RS.take p.rounds.length) (GS.take p.openings)).bind (fun m =>
    q.decide m (RS.drop p.rounds.length) (GS.drop p.openings)) = _
  rw [List.take_of_length_le (le_of_eq h1), List.drop_of_length_le (le_of_eq h1),
    List.take_of_length_le (le_of_eq h2), List.drop_of_length_le (le_of_eq h2)]

/-- **Where the joined block's step says yes**, the first block's step has said yes on the same
rounds and columns, and the second block's decision on what it left. -/
theorem step_then {nm : String} {p q : Block T Cl} (hq : q.rounds = []) {ft : ℕ} {s s' : T}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} {k : ℕ}
    (h : (p.andThen nm q).step ft s rs cols = .ok (s', k)) :
    ∃ mid, p.step ft s rs cols = .ok (mid, k) ∧ q.decide mid [] [] = .ok s' := by
  have hr : (p.andThen nm q).rounds = p.rounds := by
    show p.rounds ++ q.rounds = _
    rw [hq, List.append_nil]
  simp only [Block.step, bind_ok, dneed_ok, pure_ok, hr] at h ⊢
  obtain ⟨_, h1, _, h2, s3, hdec, he⟩ := h
  have hlen := roundsFit_length _ _ h1
  rw [andThen_decide nm p q s _ _ (by rw [List.length_map, hlen]) (by
    rw [regroup_length, List.length_map, groupsOf_length ft _ _ (by rw [List.length_map, hlen])]
    unfold Block.openings
    rw [openings_from, Nat.zero_add])] at hdec
  obtain ⟨mid, hm, hqd⟩ := ebind_ok.1 hdec
  obtain rfl : s3 = s' := congrArg Prod.fst he
  exact ⟨mid, ⟨(), h1, (), h2, mid, hm, congrArg (Prod.mk mid) (congrArg Prod.snd he)⟩, hqd⟩

/-- The piece with a block without a round joined behind its block. -/
def Piece.then {C : PQ.CK} {F : Frame} (pc : Piece C F T Cl W) (nm : String) (q : Block T Cl) :
    Piece C F T Cl W :=
  { pc with b := pc.b.andThen nm q }

/-- **Where the joined piece says yes**, the first piece has said yes at the same transcript, with
the same oracles behind it, and the second block's decision on the record that it left. -/
theorem out_then {C : PQ.CK} {F : Frame} (pc : Piece C F T Cl W) (nm : String) (q : Block T Cl)
    (hq : q.rounds = []) {a b : T × F.E.Str} {τ : Tr (uLT C pc.ds)}
    (h : (Piece.then pc nm q).ior.red.out a τ = some b) :
    ∃ mid, pc.ior.red.out a τ = some (mid, b.2) ∧ q.decide mid [] [] = .ok b.1 := by
  have hb' : (if sTests C pc.stage a.2 τ then (Piece.then pc nm q).run a.1 (sView C pc.stage a.2 τ)
      else none).map (fun xo => (xo, pc.ior.imp a.2 τ)) = some b := h
  have goal' : ∀ mid, ((if sTests C pc.stage a.2 τ then pc.run a.1 (sView C pc.stage a.2 τ)
      else none).map (fun xo => (xo, pc.ior.imp a.2 τ)) = some (mid, b.2)) →
      pc.ior.red.out a τ = some (mid, b.2) := fun _ h => h
  split at hb'
  · next ht =>
    cases hrun : (Piece.then pc nm q).run a.1 (sView C pc.stage a.2 τ) with
    | none =>
      rw [hrun] at hb'
      cases hb'
    | some s' =>
      rw [hrun] at hb'
      obtain rfl := Option.some.inj hb'
      obtain ⟨hl, k, hst, hc⟩ := one_ok hrun
      obtain ⟨mid, hp, hqd⟩ := step_then hq hst
      have hl' : (sView C pc.stage a.2 τ).rounds.length + pc.back.length = pc.b.rounds.length := by
        have e : (pc.b.andThen nm q).rounds.length = pc.b.rounds.length := by
          show (pc.b.rounds ++ q.rounds).length = _
          rw [hq, List.append_nil]
        have hl2 : ((sView C pc.stage a.2 τ).rounds ++ pc.back).length =
            (pc.b.andThen nm q).rounds.length := hl
        rw [← List.length_append, hl2, e]
      refine ⟨mid, goal' mid ?_, hqd⟩
      rw [if_pos ht]
      have hrun' : pc.run a.1 (sView C pc.stage a.2 τ) = some mid :=
        one_of (by rw [← hl']; exact List.length_append) hp hc
      rw [hrun']
      rfl
  · cases hb'

/-- **The rule.** If the first piece has what it owes, between (on, R) and (onM, RM), and over the
second block, which has no round, the promise is kept and a witness goes back from R' to RM, then
the joined piece has what it owes between (on, R) and (on', R'), at the first piece's errors. -/
theorem goodIn_then {C : PQ.CK} {F : Frame} (pc : Piece C F T Cl W) (nm : String) (q : Block T Cl)
    (hq : q.rounds = []) (on onM on' : T × F.E.Str → Prop) (R RM R' : T × F.E.Str → W → Prop)
    (h1 : pc.GoodIn on onM R RM)
    (h2 : ∀ mid s' y, onM (mid, y) → q.decide mid [] [] = .ok s' →
      on' (s', y) ∧ ∀ w, R' (s', y) w → RM (mid, y) w) :
    (Piece.then pc nm q).GoodIn on on' R R' := by
  intro a ha
  refine Doomed.mono _ _ ?_ (h1 a ha)
  intro τ hτ b hb
  obtain ⟨mid, hp, hqd⟩ := out_then pc nm q hq hb
  obtain ⟨hm, hback⟩ := hτ _ hp
  obtain ⟨ho, hr⟩ := h2 mid b.1 b.2 hm hqd
  exact ⟨ho, fun w hw => hback w (hr w hw)⟩

end VerifiableInference.Desc.K13.Law
