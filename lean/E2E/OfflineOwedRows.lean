-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineOwedRows.lean: the field `owed` of `OwedRest` (E2E/OfflineClauses.lean) at six of the seven
rows of the offline file's first chain, in that field's own form: a member of the muted rows' first
list, at a run of `runC` that has returned.

  `RowConditions.AsksNothing`, `RowConditions.AsksBud`   what is asked of a row's letters
  `owed_quiet_rows`      the two lookups and the batching, at letters that ask nothing: `owedAt` holds
  `SendersBudAtRun`      THE RESIDUE at the three sendings, at one run: the sender's bound on queried
                         positions at the positions that the run reads of the sender's trees
  `owed_sender_rows`     the three sendings, at the senders' letters: `owedAt` from that residue
  (`SenderBudAtDraws`: the residue in closed form, at one sender: no input, no coin, no run: the frame's own
  `BudDebts.bud₁` there. The definition: Johnson/M1/KeySenderBud.lean.)
  `sender_bud_at_run`, `senders_bud_at_run`   the closed form gives the residue at every run that has
                         returned at draws that the description's rounds can draw

AT LETTERS THAT ASK NOTHING `owedAt` IS NOT FREE: of a part that the run has called it asks that the book
gives its carried blocks and that `midAtW` returns a state. Both are paid here from the run's return
(E2E/OfflineOwedFirst.lean), with no invariant of a thread.

Premises. The description's test on its plan; the book's tests; the run has returned. No premise on a
simulator or on `Side.fits`. `SendersBudAtRun` is a DEFINITION; no member of `SenderBudAtDraws` is shown in
this file. Not the ranges' row, nor any row of the shared or the last chain. Nothing on any property.
-/
import E2E.OfflineOwedFirst
import E2E.OfflineSides
import Johnson.M1.KeySenderBud
import Johnson.Desc.ProofFile.Honest.Law.Rule.Mute

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place Oracle)
open OnBytes (TableKey)
open OnBytes.SendSim.At (budAt)
open OnBytes.M1 (SenderBudAtDraws)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver)
open AtPublicFiles.KeyBook (idxPlace msgPlace lookPlace battPlace wPlace)

/-! ## 1 What is asked of a row's letters -/

section Letters
variable {Bk : ProverCoinCounts} {S V W Y Pb : Type}

/-- The condition at a part's start and the condition on the positions hold everywhere. -/
def RowConditions.AsksNothing (c : RowConditions Bk S V W Y Pb) : Prop :=
  (∀ u ca m front, c.atPart u ca m front) ∧ ∀ n ds asks, c.positions n ds asks

/-- The letters that say nothing ask nothing. -/
theorem RowConditions.bare_asksNothing :
    (RowConditions.bare : RowConditions Bk S V W Y Pb).AsksNothing :=
  ⟨fun _ _ _ _ => trivial, fun _ _ _ => trivial⟩

/-- The condition at a part's start holds everywhere, and the condition on the positions holds where the
sender's bound on queried positions does. -/
def RowConditions.AsksBud (P : VerifiableInference.Desc.K1.Par) (c : RowConditions Bk S V W Y Pb) : Prop :=
  (∀ u ca m front, c.atPart u ca m front) ∧ ∀ n ds asks, budAt P asks → c.positions n ds asks

/-- A member's number is below the row's length, from the first number on. -/
theorem member_number_lt : ∀ (row : List (Part V W Y × Sim Pb)) (j : Nat)
    (rs : List (Fmt.DeclaredRound × List Oracle)), ∀ u ∈ membersOf row j rs, u.number < j + row.length
  | [], _, _, _, hu => by cases hu
  | y :: row, j, rs, u, hu => by
    have hu' : u ∈ (⟨j, rs.take y.1.moves.length, y.1, y.2⟩ : Member V W Y Pb) ::
        membersOf row (j + 1) (rs.drop y.1.moves.length) := hu
    rcases List.mem_cons.1 hu' with rfl | g
    · show j < j + (row.length + 1)
      omega
    · have := member_number_lt row (j + 1) _ u g
      show u.number < j + (row.length + 1)
      omega

end Letters

/-! ## 2 The rows -/

section Rows
variable {W₀ Rc X₀ X Wk : Type} {Fx : FileDescription KeyInst} {Bk : ProverCoinCounts} {K : KeyParts W₀ Rc X₀ X Wk}
  {S : OfflineSimulators} {c : ConditionsByChain Fx Bk W₀ Rc TableKey Unit X₀ X}
  {H : Prover W₀ Rc KeyInst TableKey Unit X₀ X} {w₀ : W₀} {rc : Rc} {x : KeyInst} {k : Coins Bk}
  {ρ : Draws} {r : RunC Fx}

/-- **The two lookups and the batching, at letters that ask nothing.** -/
theorem owed_quiet_rows (plan : Fx.planOk = true) (book : Bk.word Fx = none)
    (h : runC Fx Bk ((offlineRows Fx Bk K S c).mute.prover H) w₀ rc x k ρ = .ok r)
    (st : List (Nat × Nat × List UInt64))
    (hc : ∀ p, (p = lookPlace 0 ∨ p = lookPlace 1 ∨ p = battPlace) → (c.first p).AsksNothing) :
    ∀ L ∈ (offlineRows Fx Bk K S c).mute.first,
      (L.place = lookPlace 0 ∨ L.place = lookPlace 1 ∨ L.place = battPlace) →
      L.owedAt Fx.first.blocksInOrder k 0
        (fun a => orRefused (midAtW Fx Bk ((offlineRows Fx Bk K S c).mute.prover H) w₀ rc x k ρ a))
        r.run st r.called := by
  intro L hL hp
  obtain ⟨L', hL', e⟩ := List.mem_map.1 hL
  obtain ⟨g, hg, e'⟩ := List.mem_map.1 hL'
  subst e'
  subst e
  have hq := hc g.place hp
  exact owedAt_first_of plan book h hL st (fun u ca m front => hq.1 u ca m front)
    fun _ _ _ _ => hq.2 _ _ _

/-- **THE RESIDUE AT THE THREE SENDINGS, AT ONE RUN**: each sender's bound on queried positions, at the
positions that the run reads of that sender's trees. A definition. -/
def SendersBudAtRun (K : KeyParts W₀ Rc X₀ X Wk) (r : Run) : Prop :=
  budAt K.idx.P (r.askedAt ⟨idxPlace, 0⟩) ∧ budAt K.msg.P (r.askedAt ⟨msgPlace, 0⟩) ∧
    budAt K.w.P (r.askedAt ⟨wPlace, 0⟩)

/-- A half of the first chain at a sending's place has one part. -/
theorem sender_parts_one (hA : K.AtPlaces) {g : Placed (AtPublicFiles.KeyFile.In1 W₀ Rc) (AtPublicFiles.KeyFile.In1 W₀ Rc) X}
    (hg : g ∈ (keyProver K).first)
    (hp : g.place = idxPlace ∨ g.place = msgPlace ∨ g.place = wPlace) : g.parts.length = 1 := by
  have hm : (g.place, g.parts.length) ∈
      (keyProver K).first.map (fun g => (g.place, g.parts.length)) := List.mem_map.2 ⟨g, hg, rfl⟩
  rw [first_counts K, hA.idx, hA.msg, hA.look0, hA.look1, hA.rng, hA.batt, hA.w] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  rcases hm with ⟨e, l⟩ | ⟨e, l⟩ | ⟨e, l⟩ | ⟨e, l⟩ | ⟨e, l⟩ | ⟨e, l⟩ | ⟨e, l⟩
  · exact l
  · exact l
  · rcases hp with q | q | q <;> exact absurd (q.symm.trans e) (by decide)
  · rcases hp with q | q | q <;> exact absurd (q.symm.trans e) (by decide)
  · rcases hp with q | q | q <;> exact absurd (q.symm.trans e) (by decide)
  · rcases hp with q | q | q <;> exact absurd (q.symm.trans e) (by decide)
  · exact l

/-- **The three sendings, at the senders' letters**: `owedAt` from the residue. -/
theorem owed_sender_rows (plan : Fx.planOk = true) (book : Bk.word Fx = none)
    (h : runC Fx Bk ((offlineRows Fx Bk K S c).mute.prover H) w₀ rc x k ρ = .ok r)
    (st : List (Nat × Nat × List UInt64)) (hA : K.AtPlaces)
    (hi : (c.first idxPlace).AsksBud K.idx.P) (hm : (c.first msgPlace).AsksBud K.msg.P)
    (hw : (c.first wPlace).AsksBud K.w.P) (hb : SendersBudAtRun K r.run) :
    ∀ L ∈ (offlineRows Fx Bk K S c).mute.first,
      (L.place = idxPlace ∨ L.place = msgPlace ∨ L.place = wPlace) →
      L.owedAt Fx.first.blocksInOrder k 0
        (fun a => orRefused (midAtW Fx Bk ((offlineRows Fx Bk K S c).mute.prover H) w₀ rc x k ρ a))
        r.run st r.called := by
  intro L hL hp
  obtain ⟨L', hL', e⟩ := List.mem_map.1 hL
  obtain ⟨g, hg, e'⟩ := List.mem_map.1 hL'
  subst e'
  subst e
  have hp' : g.place = idxPlace ∨ g.place = msgPlace ∨ g.place = wPlace := hp
  have h1 := sender_parts_one hA hg hp'
  have hzero : ∀ σ, ((rowOf (Cl := Fx.Cl) g (S.byChain.first g.place) (c.first g.place)).mute).side
      Fx.first.blocksInOrder = some σ → ∀ u ∈ σ.members, u.number = 0 := by
    intro σ hσ u hu
    have hσ' : Side.seated Fx.first.blocksInOrder g.place (partsBeside g.parts (S.byChain.first g.place)) [] =
        some σ := hσ
    have hrow : σ.row = partsBeside g.parts (S.byChain.first g.place) := by
      unfold Side.seated at hσ'
      obtain ⟨m, _, rfl⟩ := Option.map_eq_some_iff.1 hσ'
      rfl
    have hlt := member_number_lt σ.row 0 _ u hu
    rw [hrow, partsBeside_length, h1] at hlt
    omega
  have key : ∀ (P : VerifiableInference.Desc.K1.Par) (p : Place), g.place = p → (c.first p).AsksBud P →
      budAt P (r.run.askedAt ⟨p, 0⟩) →
      ((rowOf (Cl := Fx.Cl) g (S.byChain.first g.place) (c.first g.place)).mute).owedAt Fx.first.blocksInOrder k 0
        (fun a => orRefused (midAtW Fx Bk ((offlineRows Fx Bk K S c).mute.prover H) w₀ rc x k ρ a))
        r.run st r.called := by
    intro P p ep hq hbp
    subst ep
    refine owedAt_first_of plan book h hL st (fun u ca m front => hq.1 u ca m front)
      fun σ hσ u hu => hq.2 _ _ _ ?_
    rw [hzero σ hσ u hu]
    exact hbp
  rcases hp' with q | q | q
  · exact key _ _ q hi hb.1
  · exact key _ _ q hm hb.2.1
  · exact key _ _ q hw hb.2.2

/-! ## 3 The residue in closed form -/

/-- **The closed form gives the bound at a run that has returned**, at a half of one part. -/
theorem sender_bud_at_run (plan : Fx.planOk = true) (book : Bk.word Fx = none)
    (h : runC Fx Bk ((offlineRows Fx Bk K S c).mute.prover H) w₀ rc x k ρ = .ok r)
    (hρ : ρ.due Fx = true) {g : Placed (AtPublicFiles.KeyFile.In1 W₀ Rc) (AtPublicFiles.KeyFile.In1 W₀ Rc) X}
    (hg : g ∈ (keyProver K).first) (h1 : g.parts.length = 1)
    (hside : g.place ∈ Fx.first.blocksInOrder.map (·.place)) {P : VerifiableInference.Desc.K1.Par}
    (hP : g.place = P.place) (hd : SenderBudAtDraws Fx P) : budAt P (r.run.askedAt ⟨g.place, 0⟩) := by
  have hL : (rowOf (Cl := Fx.Cl) g (S.byChain.first g.place) (c.first g.place)).mute ∈
      (offlineRows Fx Bk K S c).mute.first :=
    List.mem_map.2 ⟨_, List.mem_map.2 ⟨g, hg, rfl⟩, rfl⟩
  obtain ⟨σ, hσ⟩ := Option.isSome_iff_exists.1 (side_isSome
    (rowOf (Cl := Fx.Cl) g (S.byChain.first g.place) (c.first g.place)).mute Fx.first.blocksInOrder [] hside)
  have hσ' : Side.seated Fx.first.blocksInOrder g.place (partsBeside g.parts (S.byChain.first g.place)) [] =
      some σ := hσ
  have hrow : σ.row = partsBeside g.parts (S.byChain.first g.place) := by
    unfold Side.seated at hσ'
    obtain ⟨m, _, rfl⟩ := Option.map_eq_some_iff.1 hσ'
    rfl
  have hlen : σ.row.length = 1 := by rw [hrow, partsBeside_length, h1]
  obtain ⟨y, hy⟩ := List.length_eq_one_iff.1 hlen
  have hu : (⟨0, (σ.block.rounds.zip σ.block.oracles).take y.1.moves.length, y.1, y.2⟩ :
      Member (AtPublicFiles.KeyFile.In1 W₀ Rc) (AtPublicFiles.KeyFile.In1 W₀ Rc) X KeyInst) ∈ σ.members := by
    unfold Side.members
    rw [hy]
    exact List.mem_cons_self
  obtain ⟨⟨f2, f3⟩, ⟨pre, t, hcut, -, hask⟩, -⟩ := first_part_at_run plan book h hL hσ hu
  have hmv : y.1.moves.length = σ.block.rounds.length := by
    rw [hy] at f2
    simpa using f2
  have hwhole : (σ.block.rounds.zip σ.block.oracles).take y.1.moves.length =
      σ.block.rounds.zip σ.block.oracles := by
    refine List.take_of_length_le ?_
    rw [List.length_zip, f3, Nat.min_self, hmv]
  have hz : σ.roundsTo 0 = 0 := rfl
  have hask' : r.run.askedAt ⟨g.place, 0⟩ =
      asksFrom (treeAsks Fx ρ 0)
        (((σ.block.rounds.zip σ.block.oracles).take y.1.moves.length).map (·.2.length))
        (((rowsOfChain Fx.first.blocksInOrder).take
          ((pre.flatMap (·.rounds)).length + σ.roundsTo 0)).map (·.2.length)).sum := hask
  rw [hask', hwhole, hz, Nat.add_zero]
  exact hd pre σ.block t hcut ((side_place hσ).trans hP) ρ hρ

/-- **The closed form at the three senders gives the residue at every run that has returned.** -/
theorem senders_bud_at_run (plan : Fx.planOk = true) (book : Bk.word Fx = none)
    (h : runC Fx Bk ((offlineRows Fx Bk K S c).mute.prover H) w₀ rc x k ρ = .ok r)
    (hρ : ρ.due Fx = true) (hA : K.AtPlaces)
    (hside : ∀ p, (p = idxPlace ∨ p = msgPlace ∨ p = wPlace) → p ∈ Fx.first.blocksInOrder.map (·.place))
    (di : SenderBudAtDraws Fx K.idx.P)
    (dm : SenderBudAtDraws Fx K.msg.P) (dw : SenderBudAtDraws Fx K.w.P) :
    SendersBudAtRun K r.run := by
  have m1 : K1.proverSideOfSending K.idx ∈ (keyProver K).first := by
    rw [AtPublicFiles.KeyFile.keyProver_first]
    simp
  have m2 : K1.proverSideOfSending K.msg ∈ (keyProver K).first := by
    rw [AtPublicFiles.KeyFile.keyProver_first]
    simp
  have m3 : K1.proverSideOfSending K.w ∈ (keyProver K).first := by
    rw [AtPublicFiles.KeyFile.keyProver_first]
    simp
  have e1 : (K1.proverSideOfSending (V := AtPublicFiles.KeyFile.In1 W₀ Rc) K.idx).place = idxPlace := hA.idx
  have e2 : (K1.proverSideOfSending (V := AtPublicFiles.KeyFile.In1 W₀ Rc) K.msg).place = msgPlace := hA.msg
  have e3 : (K1.proverSideOfSending (V := AtPublicFiles.KeyFile.In1 W₀ Rc) K.w).place = wPlace := hA.w
  have b1 := sender_bud_at_run plan book h hρ m1 rfl (e1 ▸ hside _ (Or.inl rfl)) rfl di
  have b2 := sender_bud_at_run plan book h hρ m2 rfl (e2 ▸ hside _ (Or.inr (Or.inl rfl))) rfl dm
  have b3 := sender_bud_at_run plan book h hρ m3 rfl (e3 ▸ hside _ (Or.inr (Or.inr rfl))) rfl dw
  rw [e1] at b1
  rw [e2] at b2
  rw [e3] at b3
  exact ⟨b1, b2, b3⟩

end Rows

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.RowConditions.bare_asksNothing
#print axioms AtPublicFiles.OfflineRows.member_number_lt
#print axioms AtPublicFiles.OfflineRows.owed_quiet_rows
#print axioms AtPublicFiles.OfflineRows.sender_parts_one
#print axioms AtPublicFiles.OfflineRows.owed_sender_rows
#print axioms AtPublicFiles.OfflineRows.sender_bud_at_run
#print axioms AtPublicFiles.OfflineRows.senders_bud_at_run
