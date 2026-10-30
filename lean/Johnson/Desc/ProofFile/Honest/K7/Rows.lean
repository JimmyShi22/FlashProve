-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K7/Rows.lean: the round that names the next token (kind K7), with its
simulator, in the form in which the frame takes a lot's rows.

The round sends one value, and that value is part of the public instance. It takes no coin, has no
stop, reads no column and sends no table. So its simulator makes the same value from the public
instance, and the two sides of the field `exact` are one fixed value. The part owns no coin, so the
field `fresh` says nothing here.

  `replyUnlettered`, `replySLot`   the row at a link and a piece; the lot, with no condition before
                   its part and with every position allowed
  `replySLot_toHLot`   the lot without its simulators is the lot that the fillings lay
  `ReplyBlock`    three facts on the sub-protocol that stands at the place
  `replyMember`, `reply_members`   the side's one member
  `reply_side_fits`   the field `fits`
  `replyShows`, `reply_shows`   what the member shows, at every coin
  `reply_good`, `seated_place`, `reply_good_seated`, `reply_hand`   `Good` at the side, at the value
                   of `Side.seated`, and what `file_owed_rows` asks at the laid row
  `ReplyBlockAtScope`   a statement: the description's own member meets `ReplyBlock`

What is stated, and what is not. `Good` is stated at A := B := False: the fields `plays` and `acc` are
met for nothing, and nothing is said of the playing or of the verifier's answer. Where the request's
last position is not covered the last test asks that the asked token is 0: that is a sentence on
acceptance. The premise on the book follows from no test of `ProverCoinCounts.clauses`; `bookWhole_spent_nil`
(Honest/BookOwners.lean) gives it at a whole book. These statements hold at every instance and every state, so no type here shuts out a
request on which the model has no value. But a part is handed an input only through `ready`, which
refuses where the request has no trace: what the honest prover does there is not said here.
-/
import Johnson.Desc.ProofFile.Honest.K7.Plays
import Johnson.Desc.ProofFile.Honest.Thread.RowsMore
import Johnson.Desc.ProofFile.Honest.KindSheet
import Johnson.Desc.ProofFile.Honest.Law.ToyLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place)
open ProofFile.Honest.Small (play_row_whole)

variable {W₀ Rc Tr X : Type}

/-! ## 1 The row and the lot -/

/-- **The row at a link and a piece.** The simulator needs nothing of the state, so the condition
before the part asks nothing; the part sends no table, so every position is allowed. -/
def replyUnlettered (link piece : Nat) :
    Unlettered (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst :=
  ⟨⟨1, some link, piece, .K7⟩, replyRow link piece, fun _ _ _ _ => True, fun _ _ _ => True⟩

/-- **The lot**: one row, at the place at which `replyLot` lays the half. -/
def replySLot : SLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst :=
  { name := (replyLot (W₀ := W₀) (Rc := Rc) (Tr := Tr) (X := X)).name
    rows := fun _ G => [replyUnlettered (G.built.size - 1) 1] }

/-- **The lot without its simulators is the lot that the fillings lay.** -/
theorem replySLot_toHLot :
    (replySLot (W₀ := W₀) (Rc := Rc) (Tr := Tr) (X := X)).toHLot = replyLot := rfl

/-! ## 2 The side -/

/-- **What the sub-protocol at the place is**: it stands at the place; its rounds are the kind's one
round; that round has no oracle message. A hypothesis's form. -/
structure ReplyBlock {S Cl : Type} (b : Block S Cl) (link piece : Nat) : Prop where
  place : b.place = ⟨1, some link, piece, .K7⟩
  rounds : b.rounds = VerifiableInference.Desc.Kinds.Reply.rounds
  oracles : b.oracles = [[]]

/-- **The side's one member.** -/
def replyMember (link piece : Nat) :
    Member (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst :=
  ⟨0, VerifiableInference.Desc.Kinds.Reply.rounds.zip [[]], replyPart, replySim link piece⟩

section
variable {S Cl : Type} {σ : Side S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst}
  {link piece : Nat}

theorem reply_members (hr : σ.row = replyRow link piece) (hb : ReplyBlock σ.block link piece) :
    σ.members = [replyMember link piece] := by
  unfold Side.members
  rw [hr, hb.rounds, hb.oracles]
  rfl

/-- **The field `fits`.** -/
theorem reply_side_fits (hr : σ.row = replyRow link piece) (hb : ReplyBlock σ.block link piece) :
    σ.fits = true := by
  unfold Side.fits
  have e1 : (σ.row.zipIdx.all fun s => s.1.2.addr == ⟨σ.block.place, s.2⟩) = true := by
    rw [hr, hb.place]
    show ((replySim link piece).addr == ⟨⟨1, some link, piece, .K7⟩, 0⟩ && true) = true
    rw [Bool.and_true]
    exact beq_self_eq_true _
  have e2 : σ.half.rounds = σ.block.rounds.length := by
    unfold Side.half
    rw [hr, hb.rounds]
    rfl
  have e3 : σ.block.oracles.length = σ.block.rounds.length := by
    rw [hb.oracles, hb.rounds]
    rfl
  show (_ && _ == _ && _ == _) = true
  rw [e1, e2, e3, beq_self_eq_true]
  rfl

end

/-- The round's one value, and no column. -/
def replyShows (x : Inst) : List Shown := [⟨[.e (OnBytes.Slice.ofE (replyOf x))], []⟩]

/-- **What the member shows**, at every coin, every state and every challenge. -/
theorem reply_shows {S Cl : Type}
    (σ : Side S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst) (link piece : Nat)
    (c : (replyMember (W₀ := W₀) (Rc := Rc) (Tr := Tr) (X := X) link piece).part.Coins)
    (m : Mid (Local W₀ Rc Inst Tr) X) (d : Fmt.Drawn) (asks : List (List (List Nat))) :
    σ.shows Face.own (replyMember link piece) c m [d] asks = some (replyShows m.st.input.x) := by
  have hp := play_row_whole σ.block.name σ.block.place (Face.own.sees m.st.input)
    [(replyPart : Part (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X)] 0
    (VerifiableInference.Desc.Kinds.Reply.rounds.zip [[]]) (c, ()) [d] [] m
    [replyShown σ.block.name σ.block.place m.st.input.x d] rfl (reply_fits _ _ _ d)
    (reply_played _ _ _ _ _ d)
  have he : (replyMember (W₀ := W₀) (Rc := Rc) (Tr := Tr) (X := X) link piece).part.steps
      σ.block.name ⟨σ.block.place, (replyMember (W₀ := W₀) (Rc := Rc) (Tr := Tr) (X := X) link
        piece).number⟩ (replyMember (W₀ := W₀) (Rc := Rc) (Tr := Tr) (X := X) link piece).rounds
      (Face.own.sees m.st.input) c =
      rowSteps σ.block.name σ.block.place (Face.own.sees m.st.input)
        [(replyPart : Part (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X)] 0
        (VerifiableInference.Desc.Kinds.Reply.rounds.zip [[]]) (c, ()) := by
    unfold rowSteps
    simp only [List.append_nil]
    rfl
  unfold Side.shows
  rw [he, hp]
  rfl

/-- **The member shows something**, at every coin, at every On and bud. -/
theorem reply_shows_some {S Cl : Type} (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (chain firstTree : Nat)
    {σ : Side S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst} {link piece : Nat}
    {On : (u : Member (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst) →
      CsAll u.part.carries → Mid (Local W₀ Rc Inst Tr) X → Before → Prop}
    {bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop}
    (hr : σ.row = replyRow link piece) (hb : ReplyBlock σ.block link piece) :
    ShowsSome pre Face.own σ chain firstTree On bud := by
  intro u hu ca m front ds asks _ _ _ hd _ _ _ c
  rw [reply_members hr hb] at hu
  obtain rfl := List.mem_singleton.1 hu
  have hd' : drawsFit VerifiableInference.Desc.Kinds.Reply.rounds ds = true := hd
  obtain ⟨d, rfl⟩ : ∃ d, ds = [d] := one_draw hd'
  rw [reply_shows σ link piece (c.1, c.2, ca) m d asks]
  exact fun e => by cases e

/-- **`Good` at the side**, at A := B := False, at every On and bud: the proof reads neither. Under
the block's three facts and the premise on the book: no entry spends a coin of this part. -/
theorem reply_good {S Cl : Type} (pre : List (Nat × Nat × List Fmt.DeclaredRound)) (Bk : ProverCoinCounts)
    (ord : List Place) (chain firstTree : Nat)
    {σ : Side S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst} {link piece : Nat}
    {On : (u : Member (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst) →
      CsAll u.part.carries → Mid (Local W₀ Rc Inst Tr) X → Before → Prop}
    {bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop}
    (hr : σ.row = replyRow link piece) (hb : ReplyBlock σ.block link piece)
    (hk : ∀ q, Bk.spentBy ⟨σ.block.place, 0⟩ q = []) :
    Good pre Face.own σ Bk ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False)
      On bud := by
  have hm := reply_members hr hb
  refine
    { fits := reply_side_fits hr hb
      plays := fun _ _ _ _ _ h => h.elim
      acc := fun _ _ _ _ _ h => h.elim
      exact := ?_
      fresh := ?_ }
  · intro u hu ca m front ds asks _ _ _ hd _ _ _
    rw [hm] at hu
    obtain rfl := List.mem_singleton.1 hu
    have hd' : drawsFit VerifiableInference.Desc.Kinds.Reply.rounds ds = true := hd
    obtain ⟨d, rfl⟩ : ∃ d, ds = [d] := one_draw hd'
    exact map_unif_point (some (replyShows m.st.input.x)) _ _
      (fun c => reply_shows σ link piece (c.1, c.2, ca) m d asks) (fun _ => rfl)
  · intro u hu p sp ca m ds asks _ _ _
    rw [hm] at hu
    obtain rfl := List.mem_singleton.1 hu
    exact fresh_of_nil _ (hk p) _ _

/-- What `Side.seated` returns stands at the place asked for, with the row handed to it. -/
theorem seated_place {S Cl V W Y Pb : Type} {bs : List (Block S Cl)} {a : Place}
    {row : List (Part V W Y × Sim Pb)} {fs : List (Fall S)} {σ : Side S Cl V W Y Pb}
    (h : Side.seated bs a row fs = some σ) : σ.block.place = a ∧ σ.row = row := by
  obtain ⟨b, hf, rfl⟩ := Option.map_eq_some_iff.1 h
  have e₀ := List.find?_some hf
  have e : (b.place == a) = true := e₀
  exact ⟨beq_iff_eq.1 e, rfl⟩

/-- **The same at the value of `Side.seated`.** -/
theorem reply_good_seated {S Cl : Type} (pre : List (Nat × Nat × List Fmt.DeclaredRound)) (Bk : ProverCoinCounts)
    (ord : List Place) (chain firstTree : Nat) (bs : List (Block S Cl)) (fs : List (Fall S))
    {σ : Side S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst} {link piece : Nat}
    (hσ : Side.seated bs (⟨1, some link, piece, .K7⟩ : Place) (replyRow link piece) fs = some σ)
    (hrounds : σ.block.rounds = VerifiableInference.Desc.Kinds.Reply.rounds)
    (horacles : σ.block.oracles = [[]])
    (hk : ∀ q, Bk.spentBy ⟨⟨1, some link, piece, .K7⟩, 0⟩ q = []) :
    Good pre Face.own σ Bk ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False)
      (fun _ _ _ _ => True) (fun _ _ _ => True) := by
  obtain ⟨hp, hr⟩ := seated_place hσ
  exact reply_good pre Bk ord chain firstTree hr ⟨hp, hrounds, horacles⟩ (by rw [hp]; exact hk)

/-- **What the rule `file_owed_rows` asks at the laid row**, from the facts on whichever member
stands at the place. -/
theorem reply_hand {S Cl : Type} {Bk : ProverCoinCounts} (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (ord : List Place) (chain firstTree : Nat) (bs : List (Block S Cl)) (fs : List (Fall S))
    (link piece : Nat)
    (T : Local W₀ Rc Inst Tr →
      Thread Bk S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst)
    (Sd : Local W₀ Rc Inst Tr → Nat → Coins Bk → Mid (Local W₀ Rc Inst Tr) X → Prop)
    (hB : ∀ σ : Side S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst,
      Side.seated bs (⟨1, some link, piece, .K7⟩ : Place) (replyRow link piece) fs = some σ →
        σ.block.rounds = VerifiableInference.Desc.Kinds.Reply.rounds ∧ σ.block.oracles = [[]])
    (hk : ∀ q, Bk.spentBy ⟨⟨1, some link, piece, .K7⟩, 0⟩ q = []) :
    ∀ σ, ((replyUnlettered link piece).lay T Sd bs).side bs fs = some σ →
      ∃ A' B', Good pre Face.own σ Bk ord chain firstTree A' B'
        ((replyUnlettered link piece).lay T Sd bs).On
        ((replyUnlettered link piece).lay T Sd bs).bud :=
  hand_of_seated (replyUnlettered link piece) T Sd bs fun σ h =>
    ⟨_, _, reply_good_seated pre Bk ord chain firstTree bs fs h (hB σ h).1 (hB σ h).2 hk⟩

/-! ## 3 At the description's own member: a statement -/

/-- **The description's own member at the place meets the block's facts**, at a chain c and the last
link's number. -/
def ReplyBlockAtScope {S Cl : Type} (bs : List (Block S Cl)) (link : Nat) : Prop :=
  ∀ b, (bs.find? fun x => x.place == (⟨1, some link, 1, .K7⟩ : Place)) = some b →
    b.rounds = VerifiableInference.Desc.Kinds.Reply.rounds ∧ b.oracles = [[]]

end ProofFile.Honest

#print axioms ProofFile.Honest.replyUnlettered
#print axioms ProofFile.Honest.replySLot
#print axioms ProofFile.Honest.replySLot_toHLot
#print axioms ProofFile.Honest.ReplyBlock
#print axioms ProofFile.Honest.replyMember
#print axioms ProofFile.Honest.reply_members
#print axioms ProofFile.Honest.reply_side_fits
#print axioms ProofFile.Honest.replyShows
#print axioms ProofFile.Honest.reply_shows
#print axioms ProofFile.Honest.reply_shows_some
#print axioms ProofFile.Honest.reply_good
#print axioms ProofFile.Honest.seated_place
#print axioms ProofFile.Honest.reply_good_seated
#print axioms ProofFile.Honest.reply_hand
#print axioms ProofFile.Honest.ReplyBlockAtScope
