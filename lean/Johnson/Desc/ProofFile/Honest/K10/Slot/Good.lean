-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Slot/Good.lean: the closing of a segment (K10) in the frame's slot: the closing's row
meets the fields fits, exact and fresh of the frame's `Good` (Honest/Side.lean). Statements and proofs on the frame's
definitions. What follows from `Good` is not said here: exact and fresh say that two laws are equal, in the frame's
letters.

  `slotRow J`        the row: the total part at the job J, with the simulator's form
  `CloseSeated σ J`  what is asked of a side: the block at the closing's place, with that row, the kind's rounds and
      oracle messages, and the kind's test on the plan
  `closeSeated_of_seated`  `Side.seated` gives it, where every block of the list at that place has those rounds
  `slot_members`     the side has one member: `closeAt true J` (Honest/K10/Sim.lean)
  `slot_fits`        the list and the sub-protocol fit
  `slot_exact`       the field exact, at ANY On and bud: `close_exact` (Honest/K10/SimSent.lean): the law of what the
      part shows, over the spent run, is the law of what the simulator lays, over its own 2 k + 1 coins, at EVERY list
      of challenges that the rounds can draw, whatever the job's data are
  `slot_fresh`       the field fresh, at ANY bud: under one premise on the book: no entry spends a coin of this part.
      The part owns no coin: both sides are drawn over one point: it is NOT the owner's fresh
  `slot_good`        `Good` as one term AT A := False: PLAYS AND ACC ARE MET FOR NOTHING THERE: fits, exact and fresh
      alone say something in this term
  `slot_good_letters`  the same at any A and B, with plays and acc as premises
  `slotLettered`, `slot_goodAt`  the row with its letters; the form that the frame's rule takes, at the chain's list and
      any falls. IN FORM ALONE, and met for nothing where no block of the list stands at the place

Limits. THE SPENDER'S HALF ALONE: the 2 k + 1 coins that the part spends are drawn here as uniform and independent of
all else, and that is what `Good.exact` asks; that they are so in a run is the owner's `fresh`, at the part that sends
the fold's fresh mask (K1 at the first segment, K2 at the others): not here. `Good` at A := False says nothing of what
the verifier accepts behind the closing. That the premises can be met at the written rounds: Honest/K10/Slot/Written.lean.
The premise on the book at any book is not shown here. No property of the protocol is claimed: nothing is said on its
soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.SimSent
import Johnson.Desc.ProofFile.Honest.Rule
import Johnson.Desc.ProofFile.Honest.Small.Book

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.Slot
open VerifiableInference VerifiableInference.Desc
open ProofFile.Honest.Small (noneSpent spentBy_of_noneSpent)

variable {S Cl V W X Pb : Type}

/-- The row: the total part at the job, with the simulator's form. -/
def slotRow (J : CloseJob W) : List (Part V W X × Sim Pb) :=
  [(closePart (foldShellT true J foldWords), closeSim J.pub.par)]

/-- What is asked of a side. -/
structure CloseSeated (σ : Side S Cl V W X Pb) (J : CloseJob W) : Prop where
  place : σ.block.place = closePlace J.pub.par
  row : σ.row = slotRow J
  rounds : σ.block.rounds = (closeRounds J.pub.par).map (·.1)
  oracles : σ.block.oracles = (closeRounds J.pub.par).map (·.2)
  plan : closePlan J.pub.par

/-- `Side.seated` gives it. -/
theorem closeSeated_of_seated {bs : List (Block S Cl)} {J : CloseJob W} {fs : List (Fall S)}
    {σ : Side S Cl V W X Pb}
    (hσ : Side.seated bs (closePlace J.pub.par) (slotRow J) fs = some σ)
    (hb : ∀ b ∈ bs, b.place = closePlace J.pub.par →
      b.rounds = (closeRounds J.pub.par).map (·.1) ∧ b.oracles = (closeRounds J.pub.par).map (·.2))
    (hp : closePlan J.pub.par) : CloseSeated σ J := by
  obtain ⟨blk, hf, rfl⟩ := Option.map_eq_some_iff.1 hσ
  have hq : blk.place = closePlace J.pub.par := by simpa using List.find?_some hf
  obtain ⟨hr, ho⟩ := hb blk (List.mem_of_find?_eq_some hf) hq
  exact ⟨hq, rfl, hr, ho, hp⟩

/-- The side has one member. -/
theorem slot_members {σ : Side S Cl V W X Pb} {J : CloseJob W} (h : CloseSeated σ J) :
    σ.members = [closeAt true J] := by
  refine members_is true J σ h.row ?_
  rw [h.rounds, h.oracles, List.zip_map']
  exact List.map_id' _

/-- The list and the sub-protocol fit. -/
theorem slot_fits {σ : Side S Cl V W X Pb} {J : CloseJob W} (h : CloseSeated σ J) :
    σ.fits = true := by
  unfold Side.fits
  have e1 : σ.row.zipIdx.all (fun s => s.1.2.addr == ⟨σ.block.place, s.2⟩) = true := by
    rw [h.row]
    show ((closeSim (Pb := Pb) J.pub.par).addr == ⟨σ.block.place, 0⟩ && true) = true
    rw [h.place, Bool.and_true]
    exact beq_self_eq_true _
  have e2 : σ.half.rounds = σ.block.rounds.length := by
    show (σ.row.map (·.1)).foldl (fun n p => n + p.moves.length) 0 = _
    rw [h.row]
    show 0 + (closePart (V := V) (X := X) (foldShellT true J foldWords)).moves.length = _
    rw [moves_len, h.rounds, List.length_map, Nat.zero_add]
  have e3 : σ.block.oracles.length = σ.block.rounds.length := by
    rw [h.rounds, h.oracles, List.length_map, List.length_map]
  rw [e1, e2, e3, beq_self_eq_true]
  rfl

/-- **The field exact, at any On and bud.** -/
theorem slot_exact (φ : Face V W Pb) {σ : Side S Cl V W X Pb} {J : CloseJob W} (h : CloseSeated σ J)
    (chain firstTree : Nat)
    (On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) :
    ∀ u ∈ σ.members, ∀ ca m front ds asks, On u ca m front → m.seen = front.seen →
      drawsFit (u.rounds.map (·.1)) ds = true → bud u.number ds asks →
      front.holds chain firstTree (u.rounds.map (·.1)) ds = true →
      u.part.stopAt (φ.sees m.st.input) m.loc ds ≠ some .hid →
      (Prob.unif (Cs u.part.takes × CsAll u.part.spends)).map
          (fun c => σ.shows φ u (c.1, c.2, ca) m ds asks) =
        (Prob.unif (Cs u.sim.takes)).map fun c => u.tells φ c m.st.input front ds asks := by
  intro u hu ca m front ds asks _ hs hd _ hh hst
  rw [slot_members h, List.mem_singleton] at hu
  subst hu
  exact close_exact J h.plan σ φ chain firstTree ca m front ds asks
    (fun hf => Bool.noConfusion hf) hs hd trivial hh hst

/-- **The field fresh, at any bud**: under the one premise on the book. The part owns no coin: without content. -/
theorem slot_fresh (φ : Face V W Pb) {σ : Side S Cl V W X Pb} {J : CloseJob W} (h : CloseSeated σ J)
    (Bk : ProverCoinCounts) (ord : List Place) (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop)
    (hB : noneSpent Bk ⟨σ.block.place, 0⟩ = true) :
    ∀ u ∈ σ.members, ∀ (q : Addr) sp ca m ds asks,
      drawsFit (u.rounds.map (·.1)) ds = true → bud u.number ds asks →
      u.part.stopAt (φ.sees m.st.input) m.loc ds ≠ some .hid →
      (Prob.unif (Cs u.part.takes)).map (fun c =>
          (cutAll c (Bk.spentBy ⟨σ.block.place, u.number⟩ q), σ.shows φ u (c, sp, ca) m ds asks,
            cutAll c (Bk.knownBy ord ⟨σ.block.place, u.number⟩ q))) =
        (Prob.unif (CsAll ((Bk.spentBy ⟨σ.block.place, u.number⟩ q).map Ahead.named) ×
            Cs u.part.takes)).map fun a =>
          (some a.1, σ.shows φ u (a.2, sp, ca) m ds asks,
            cutAll a.2 (Bk.knownBy ord ⟨σ.block.place, u.number⟩ q)) := by
  intro u hu q sp ca m ds asks _ _ _
  rw [slot_members h, List.mem_singleton] at hu
  subst hu
  exact fresh_of_nil _ (spentBy_of_noneSpent hB q) _ _

/-- **`Good` at the side, as one term, AT A := False**: plays and acc are met for nothing there. -/
theorem slot_good (pre : List (Nat × Nat × List Fmt.DeclaredRound)) (φ : Face V W Pb) {σ : Side S Cl V W X Pb}
    {J : CloseJob W} (h : CloseSeated σ J)
    (Bk : ProverCoinCounts) (ord : List Place) (chain firstTree : Nat)
    (B : Coins Bk → S → Mid W X → Env → Prop)
    (On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop)
    (hB : noneSpent Bk ⟨σ.block.place, 0⟩ = true) :
    Good pre φ σ Bk ord chain firstTree (fun _ _ _ _ => False) B On bud :=
  { fits := slot_fits h
    plays := fun _ _ _ _ _ hA => hA.elim
    acc := fun _ _ _ _ _ hA => hA.elim
    exact := fun u hu ca m front ds asks a b _ c d e f =>
      slot_exact φ h chain firstTree On bud u hu ca m front ds asks a b c d e f
    fresh := slot_fresh φ h Bk ord bud hB }

/-- **`Good` at the side at any letters A and B**: `plays` and `acc` come from `g`, a `Good` at the same letters and any On₀
and bud₀ (at a bud₀ that is never met its exact and fresh ask nothing): they are the kind's sentences at a thread
(Honest/K10/Thr/Plays.lean, Yes.lean). fits, exact and fresh are this file's. -/
theorem slot_good_letters (pre : List (Nat × Nat × List Fmt.DeclaredRound)) (φ : Face V W Pb)
    {σ : Side S Cl V W X Pb} {J : CloseJob W} (h : CloseSeated σ J)
    (Bk : ProverCoinCounts) (ord : List Place) (chain firstTree : Nat)
    (A B : Coins Bk → S → Mid W X → Env → Prop)
    (On₀ On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (bud₀ bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop)
    (hB : noneSpent Bk ⟨σ.block.place, 0⟩ = true)
    (g : Good pre φ σ Bk ord chain firstTree A B On₀ bud₀) :
    Good pre φ σ Bk ord chain firstTree A B On bud :=
  { fits := slot_fits h
    plays := g.plays
    acc := g.acc
    exact := fun u hu ca m front ds asks a b _ c d e f =>
      slot_exact φ h chain firstTree On bud u hu ca m front ds asks a b c d e f
    fresh := slot_fresh φ h Bk ord bud hB }

/-- **The row with its letters**: A := False. -/
def slotLettered (Bk : ProverCoinCounts) (J : CloseJob W) (B : Coins Bk → S → Mid W X → Env → Prop)
    (On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) : Lettered Bk S Cl V W X Pb :=
  { place := closePlace J.pub.par, row := slotRow J, A := fun _ _ _ _ => False, B := B, On := On, bud := bud }

/-- **The form that the frame's rule takes**, at the chain's list and its falls. IN FORM ALONE. -/
theorem slot_goodAt (pre : List (Nat × Nat × List Fmt.DeclaredRound)) (φ : Face V W Pb) (Bk : ProverCoinCounts) (J : CloseJob W) (bs : List (Block S Cl))
    (ord : List Place) (chain firstTree : Nat) (fs : List (Fall S))
    (B : Coins Bk → S → Mid W X → Env → Prop)
    (On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop)
    (hb : ∀ b ∈ bs, b.place = closePlace J.pub.par →
      b.rounds = (closeRounds J.pub.par).map (·.1) ∧ b.oracles = (closeRounds J.pub.par).map (·.2))
    (hp : closePlan J.pub.par)
    (hB : noneSpent Bk (closeAddr J.pub.par) = true) :
    (slotLettered (S := S) (Cl := Cl) Bk J B On bud).goodAt pre φ bs ord chain firstTree fs := by
  intro σ hσ
  have h : CloseSeated σ J := closeSeated_of_seated hσ hb hp
  exact slot_good _ φ h Bk ord chain firstTree B On bud (by rw [h.place]; exact hB)

end ProofFile.Honest.K10.Slot

#print axioms ProofFile.Honest.K10.Slot.closeSeated_of_seated
#print axioms ProofFile.Honest.K10.Slot.slot_members
#print axioms ProofFile.Honest.K10.Slot.slot_fits
#print axioms ProofFile.Honest.K10.Slot.slot_exact
#print axioms ProofFile.Honest.K10.Slot.slot_fresh
#print axioms ProofFile.Honest.K10.Slot.slot_good
#print axioms ProofFile.Honest.K10.Slot.slot_good_letters
#print axioms ProofFile.Honest.K10.Slot.slot_goodAt
