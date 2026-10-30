-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/Plays.lean: the kind "the code switch" (K2): THE KIND's OWN
HALF PLAYS: at a sub-protocol of two rounds whose stated shapes are the sending's, under named
public tests, at EVERY coin, EVERY two challenges and EVERY stand of the run in front whose input's
public instance passes the test on the filling, the frame's own `play` (Honest/Frame.lean) over the
half's two rounds RETURNS: no move refuses, and both messages pass the frame's test on their shape
(`Sending.fits`). One definition, a list of public data; statements with their proofs.

  `treeShapes`      a sending's trees: stated length and width, in the order of the roots
  `core_some`       what the two rounds show (`coreShows`, Honest/K2/Law/SwitchMoves.lean) at the
                    lot's own sender and at main rows' data that was not refused is not the one
                    symbol
  `part_plays`      so the lifted part's two rounds, played alone, return: where what the part reads
                    of the input returns what the fold in front leaves
  `half_steps`      the half's rounds at a sub-protocol of two rounds are that part's
  `half_plays`      THE HALF, at any closing that returns at the stand
  `lot_plays_fit`   the same AT `Good.plays`' OWN TERM (Honest/Side.lean): at every list of
                    challenges that the sub-protocol's rounds can draw (`drawsFit`)
  `lot_plays`       THE HALF OF THE KIND's ONE LOT (`switchLot`, Honest/K2/AtPlan.lean: the closing
                    `lotClosingAt`): the closing's two public tests in the stead of "it returns"

THE PREMISES: ALL ARE TESTS OR EQUATIONS ON PUBLIC DATA, but hl of part_plays and half_plays, which
is asked at the stand's hidden readers and at the carried coins: these two never stand in front of a
law over coins; the last is asked at the public instance of the stand's own input (m.st.input.x). On
the place: `Sizes.serves` (Johnson/Desc/K2/Honest/Carrying.lean) · `Sizes.roomy`
(Honest/K2/Part.lean) · `placeFits` (Honest/K2/Law/PlanAsks.lean) · `closingOk`
(Honest/K2/Sim.lean). On the sub-protocol against the place, four equations: its first round states
no item but roots; the oracle messages beneath these have the lengths and widths of the sending's
trees; its second round states as many answers as the sending has, and nothing else; no oracle
message stands beneath it. On the filling at the input's public instance: `publicOk`.

By: `lifted_shows` (Honest/K2/Law/SwitchShows.lean) · `rowsAll_returns` (Honest/K2/Law/Laid.lean) ·
`returnsLaw` (Honest/K2/Law/SegmentAlike.lean) · `zipIdx_fst` (Honest/K2/Law/SwitchFrame.lean) ·
`draws_two` (Honest/K2/Law/ExactProof.lean) · `length_answers` (Johnson/Prover/Send/Form.lean: the
shared sending's writer's). Some steps are `simp` or `simp only` at the definitions named there.

Limits. THE PREMISES ARE SHOWN MET NOWHERE HERE: no test is evaluated, and that the description's
own sub-protocol at a place of the kind meets the four equations is not shown; nor that the
sub-protocol which the description seats at such a place, with what is joined around the kind's own,
has the kind's rounds and oracle messages. IT IS ON RETURNING ALONE: nothing on what is sent, nor on
whether the verifier's step says yes to it. The book's lending of the coins, the laying of the
columns and what holds behind a step that accepts (the other clauses of the end of `Good.plays`,
Honest/Side.lean) are not spoken of; the part's stops never stop, by its text. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.SwitchShows
import Johnson.Desc.ProofFile.Honest.K2.Law.SwitchFrame
import Johnson.Desc.ProofFile.Honest.K2.Law.Laid
import Johnson.Desc.ProofFile.Honest.K2.Law.PlanAsks
import Johnson.Desc.ProofFile.Honest.K2.Law.SegmentAlike
import Johnson.Desc.ProofFile.Honest.K2.Law.ExactProof
import Johnson.Prover.Send.Form

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Oracle itemOf)
open VerifiableInference.Desc.K2.Honest (Sizes)

variable {V W X W₀ Rc Xi Tr S Cl : Type}

/-- A sending's trees: stated length and width, in the order of the roots. If `treesMade` returns
nothing the list has no member: `getD` falls back on an empty record; coins and inputs are not read.
-/
def treeShapes (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice) : List (Nat × Nat) :=
  ((VerifiableInference.Desc.Own.treesMade codes sent).getD {}).shapes.toList.map fun t =>
    (t.logN, t.mainWidth + t.maskWidth)

/-- **At the lot's own sender the two rounds show something.** D: the main rows' data. -/
theorem core_some (table : FreshTable) (Z : Sizes) (others : Array OnBytes.OracleNotice) (k : Nat)
    (d₁ d₂ : Fmt.DeclaredRound) (o₁ o₂ : List Oracle) (x₁ : Fmt.Drawn)
    (asks : List (List (List Nat))) (D : Nat → Nat → Nat → Cb.Gl.E)
    (c : Cs (sendingDue Z.codes (switchSent Z others) (switchFresh Z others k)))
    (hs : Z.serves = true) (hr : Z.roomy = true)
    (hf : K1.sendFits (sendingPar Z.codes (switchSent Z others))
      (rideOf (switchSent Z others) (switchFresh Z others k)) = true)
    (h1 : d₁.items.filter (· != .root) = [])
    (h2 : o₁.map (fun o => (o.logLength, o.words)) = treeShapes Z.codes (switchSent Z others))
    (h3 : d₂.items.filter (· != .root) =
      List.replicate (sendingPar Z.codes (switchSent Z others)).answers .answer)
    (h4 : o₂ = []) :
    (coreShows (coreSender table) Z others k d₁ d₂ o₁ o₂ x₁ asks (.ok D) c).isSome = true := by
  obtain ⟨R, hR⟩ := rowsAll_returns hf table D c
  have f1 : ∀ T : List Table, T.map (fun t => (t.logLength, t.words)) =
      treeShapes Z.codes (switchSent Z others) → (⟨[], T⟩ : Sending).fits d₁ o₁ = true := by
    intro T hT
    unfold Sending.fits
    rw [h1, h2, hT]
    simp
  have f2 : ∀ A : List Cb.Gl.E, A.length = (sendingPar Z.codes (switchSent Z others)).answers →
      (⟨A.map .answer, []⟩ : Sending).fits d₂ o₂ = true := by
    intro A hA
    unfold Sending.fits
    rw [h3, h4, ← hA]
    have : (A.map Said.answer).map (fun v => itemOf v.got) =
        List.replicate A.length Fmt.Item.answer := by
      rw [List.map_map]
      exact List.eq_replicate_iff.2 ⟨by rw [List.length_map], fun b hb => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hb
        rfl⟩
    rw [this]
    simp
  unfold coreShows
  rw [hs, hr]
  simp only [Bool.not_true, Bool.false_eq_true, if_false, Except.toOption, Option.bind_some]
  simp only [coreSender, hR, Except.map, Option.bind_some]
  rw [if_pos (f1 _ (by
    rw [List.map_map]
    exact zipIdx_fst (fun t : OnBytes.TreeShape => (t.logN, t.mainWidth + t.maskWidth)) _ 0))]
  rw [if_pos (f2 _ (by rw [List.length_map, Johnson.Prover.Send.length_answers]))]
  rfl

/-- **The lifted part's two rounds, played alone, return.** -/
theorem part_plays (table : FreshTable) (Z : Sizes) (others : Array OnBytes.OracleNotice) (k : Nat)
    (carries : List (String × Due)) (see : V → Unit) (wit : W → SwitchAsk) (get : X → Unit)
    (set : X → Unit → X) (nm : String) (ad : Addr) (d₁ d₂ : Fmt.DeclaredRound) (o₁ o₂ : List Oracle)
    (v : Option V) (c : Cs (sendingDue Z.codes (switchSent Z others) (switchFresh Z others k)))
    (ca : CsAll carries) (x₁ x₂ : Fmt.Drawn) (m : Mid W X)
    (hs : Z.serves = true) (hr : Z.roomy = true)
    (hf : K1.sendFits (sendingPar Z.codes (switchSent Z others))
      (rideOf (switchSent Z others) (switchFresh Z others k)) = true)
    (h1 : d₁.items.filter (· != .root) = [])
    (h2 : o₁.map (fun o => (o.logLength, o.words)) = treeShapes Z.codes (switchSent Z others))
    (h3 : d₂.items.filter (· != .root) =
      List.replicate (sendingPar Z.codes (switchSent Z others)).answers .answer)
    (h4 : o₂ = [])
    (hl : ((wit m.st.input).left m.st.heard (Stretch.carried carries ca)).toOption.isSome = true) :
    ∃ y, play (((switchPart (coreSender table) Z others k carries).lift see wit get set).steps nm ad
      [(d₁, o₁), (d₂, o₂)] v (c, (), ca)) [x₁, x₂] [] m = .ok y := by
  have hD : ∃ D, switchRowsAt Z carries ca (m.st.narrow wit get) 0 = .ok D := by
    unfold switchRowsAt State.narrow
    simp only [Nat.sub_zero, List.take_length]
    cases e : (wit m.st.input).left m.st.heard (Stretch.carried carries ca) with
    | ok L => exact ⟨_, rfl⟩
    | error s =>
      rw [e] at hl
      cases hl
  obtain ⟨D, hD⟩ := hD
  have h := lifted_shows (coreSender table) Z others k carries see wit get set nm ad d₁ d₂ o₁ o₂ v c
    ca x₁ x₂ m []
  rw [hD] at h
  have hc := core_some table Z others k d₁ d₂ o₁ o₂ x₁ [] D c hs hr hf h1 h2 h3 h4
  rw [← h] at hc
  cases e : play (((switchPart (coreSender table) Z others k carries).lift see wit get set).steps nm
      ad [(d₁, o₁), (d₂, o₂)] v (c, (), ca)) [x₁, x₂] [] m with
  | ok y => exact ⟨y, rfl⟩
  | error s =>
    rw [e] at hc
    cases hc

/-- The half's rounds at a sub-protocol of two rounds are its one part's. -/
theorem half_steps (Sd : Sender) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) (b : Block S Cl) (r₁ r₂ : Fmt.DeclaredRound × List Oracle)
    (hb : b.rounds.zip b.oracles = [r₁, r₂]) (v : Option (Local W₀ Rc Xi Tr))
    (c : RowCoins (switchHalf (X := X) Sd D readers closing p).parts) :
    (switchHalf (X := X) Sd D readers closing p).steps b v c =
      ((switchPart Sd p.sizes p.others p.foldVars p.carries).lift (fun _ => ())
        (switchWit D readers closing p) (fun _ => ()) fun x _ => x).steps b.name ⟨b.place, 0⟩
        [r₁, r₂] v c.1 := by
  unfold Placed.steps
  rw [hb]
  show _ ++ [] = _
  rw [List.append_nil]
  rfl

/-- **THE HALF PLAYS**, at any closing that returns at the stand. -/
theorem half_plays (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers) (closing : Closing)
    (p : SwitchPlace) (b : Block S Cl) (d₁ d₂ : Fmt.DeclaredRound) (o₁ o₂ : List Oracle)
    (hb : b.rounds.zip b.oracles = [(d₁, o₁), (d₂, o₂)]) (v : Option (Local W₀ Rc Xi Tr))
    (c : RowCoins (switchHalf (X := X) (coreSender freshTable) D readers closing p).parts)
    (x₁ x₂ : Fmt.Drawn) (m : Mid (Local W₀ Rc Xi Tr) X)
    (hs : p.sizes.serves = true) (hr : p.sizes.roomy = true) (hf : placeFits p = true)
    (h1 : d₁.items.filter (· != .root) = [])
    (h2 : o₁.map (fun o => (o.logLength, o.words)) =
      treeShapes p.sizes.codes (switchSent p.sizes p.others))
    (h3 : d₂.items.filter (· != .root) =
      List.replicate (sendingPar p.sizes.codes (switchSent p.sizes p.others)).answers .answer)
    (h4 : o₂ = [])
    (hl : (closing p (D m.st.input.x) (readers m.st.input) m.st.heard
      (Stretch.carried p.carries c.1.2.2)).toOption.isSome = true) :
    ∃ y, play ((switchHalf (X := X) (coreSender freshTable) D readers closing p).steps b v c)
      [x₁, x₂] [] m = .ok y := by
  rw [half_steps (coreSender freshTable) D readers closing p b (d₁, o₁) (d₂, o₂) hb v c]
  exact part_plays freshTable p.sizes p.others p.foldVars p.carries (fun _ => ())
    (switchWit D readers closing p) (fun _ => ()) (fun x _ => x) b.name ⟨b.place, 0⟩ d₁ d₂ o₁ o₂ v
    c.1.1 c.1.2.2 x₁ x₂ m hs hr hf h1 h2 h3 h4 hl

/-- **THE HALF OF THE KIND's ONE LOT PLAYS.** -/
theorem lot_plays (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (lay : OnBytes.Params.ReqLayout) (segs : List SegmentPub)
    (p : SwitchPlace) (b : Block S Cl) (d₁ d₂ : Fmt.DeclaredRound) (o₁ o₂ : List Oracle)
    (hb : b.rounds.zip b.oracles = [(d₁, o₁), (d₂, o₂)]) (v : Option (Local W₀ Rc Xi Tr))
    (c : RowCoins (switchHalf (X := X) (coreSender freshTable) D readers
      (lotClosingAt lay segs) p).parts)
    (x₁ x₂ : Fmt.Drawn) (m : Mid (Local W₀ Rc Xi Tr) X)
    (hs : p.sizes.serves = true) (hr : p.sizes.roomy = true) (hf : placeFits p = true)
    (h1 : d₁.items.filter (· != .root) = [])
    (h2 : o₁.map (fun o => (o.logLength, o.words)) =
      treeShapes p.sizes.codes (switchSent p.sizes p.others))
    (h3 : d₂.items.filter (· != .root) =
      List.replicate (sendingPar p.sizes.codes (switchSent p.sizes p.others)).answers .answer)
    (h4 : o₂ = [])
    (hc : closingOk freshTable (segs.take p.link) p = true)
    (hp : publicOk D lay p (segs.take p.link) m.st.input.x = true) :
    ∃ y, play ((switchHalf (X := X) (coreSender freshTable) D readers
      (lotClosingAt lay segs) p).steps b v c) [x₁, x₂] [] m = .ok y :=
  half_plays D readers (lotClosingAt lay segs) p b d₁ d₂ o₁ o₂ hb v c x₁ x₂ m hs hr hf h1 h2 h3 h4
    ((returnsLaw D readers lay segs p hc m.st.input m.st.heard c.1.2.2).trans hp)

/-- **The same at every list of challenges that the sub-protocol's rounds can draw.** -/
theorem lot_plays_fit (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (lay : OnBytes.Params.ReqLayout) (segs : List SegmentPub)
    (p : SwitchPlace) (b : Block S Cl) (d₁ d₂ : Fmt.DeclaredRound) (o₁ o₂ : List Oracle)
    (hr₂ : b.rounds = [d₁, d₂]) (ho₂ : b.oracles = [o₁, o₂]) (v : Option (Local W₀ Rc Xi Tr))
    (c : RowCoins (switchHalf (X := X) (coreSender freshTable) D readers
      (lotClosingAt lay segs) p).parts)
    (ds : List Fmt.Drawn) (hd : drawsFit b.rounds ds = true) (m : Mid (Local W₀ Rc Xi Tr) X)
    (hs : p.sizes.serves = true) (hr : p.sizes.roomy = true) (hf : placeFits p = true)
    (h1 : d₁.items.filter (· != .root) = [])
    (h2 : o₁.map (fun o => (o.logLength, o.words)) =
      treeShapes p.sizes.codes (switchSent p.sizes p.others))
    (h3 : d₂.items.filter (· != .root) =
      List.replicate (sendingPar p.sizes.codes (switchSent p.sizes p.others)).answers .answer)
    (h4 : o₂ = [])
    (hc : closingOk freshTable (segs.take p.link) p = true)
    (hp : publicOk D lay p (segs.take p.link) m.st.input.x = true) :
    ∃ y, play ((switchHalf (X := X) (coreSender freshTable) D readers
      (lotClosingAt lay segs) p).steps b v c) ds [] m = .ok y := by
  rw [hr₂] at hd
  obtain ⟨x₁, x₂, rfl, _⟩ := draws_two d₁ d₂ ds hd
  exact lot_plays D readers lay segs p b d₁ d₂ o₁ o₂ (by rw [hr₂, ho₂]; rfl) v c x₁ x₂ m hs hr hf
    h1 h2 h3 h4 hc hp

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.treeShapes
#print axioms ProofFile.Honest.K2.Law.core_some
#print axioms ProofFile.Honest.K2.Law.part_plays
#print axioms ProofFile.Honest.K2.Law.half_steps
#print axioms ProofFile.Honest.K2.Law.half_plays
#print axioms ProofFile.Honest.K2.Law.lot_plays
#print axioms ProofFile.Honest.K2.Law.lot_plays_fit
