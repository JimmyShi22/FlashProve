-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/Joint.lean: the two places of kind K13 on the first chain as one row of pieces:
the batching's joined block, then W's commitment with the kind's block behind it. Statements with
their proofs.
Main names:
  `KeepsEnd B`: a condition on a block's own decision: on as many rounds as it declares, its yes
    leaves the codes, the rows on the table and what goes on to the third chain as they are.
  `piece_ok_len`: where a piece says yes, its block's own decision has said yes on as many rounds as
    the block declares.
  `commit_goodIn`: a piece whose block keeps these, whose extractor is the identity, has what it
    owes between `FrontOk P` with all rows true and the same, at any errors, for a pin that goes
    back.
  `then_owed`, `then_listed`: a block without a round joined behind leaves `Owed` and `Listed`.
  `joint`: **the two pieces in a row**, each between its two places.
Used of `verify-on-bytes`: nothing beside what Johnson/Desc/K13/Law/AtM4.lean names.

What is not claimed. That W's commitment keeps these three (`KeepsEnd`): a premise here. That its
extractor may be the identity where W's own pin is to be promised behind it: no such promise is made
here. `WIs` stands in what is behind the row: see Johnson/Desc/K13/Law/Eval.lean. `Declared` is a
test on a plan's written rounds: an evaluation at two stored sets' public files, a small and a
full-size one, said yes, and five controls said no; no theorem says it of a plan. `Local` asks only
that the decoder reads the stored table and the earlier trees: every such function meets it. A
decoder that reads the oracles alone singles out one member of a list whatever the samples in the
record say: so the laws at such a decoder are idle for the witness that the samples pin. The form to
carry on is that of Johnson/Desc/K13/Law/PinA.lean. No piece in front is shown to promise that the
record's number of the index masks' message is idx. The number nR of the matrix's rows is a free
letter: that it is the plan's is said nowhere but in Johnson/Desc/K13/Law/Caller.lean.

-/
import Johnson.Desc.K13.Law.Tries2
import Johnson.Desc.K13.Law.Laid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice Iop Run
open OnBytes.Maker
open OnBytes.Means (Words)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (Frame Piece EachGoodIn)

variable {Cl W : Type} {nR : ℕ}

/-- On as many rounds as the block declares, its yes leaves the codes, the rows on the table and
what goes on to the third chain as they are. -/
def KeepsEnd (B : Block S Cl) : Prop :=
  ∀ s s' rs gs, rs.length = B.rounds.length → B.decide s rs gs = .ok s' →
    s'.st.codes = s.st.codes ∧ s'.rows = s.rows ∧ linAt s' = linAt s

/-- Where a piece says yes, its block's own decision has said yes on as many rounds as the block
declares. General in the piece. -/
theorem piece_ok_len {T : Type} {C : PQ.CK} {F : Frame} (p : Piece C F T Cl W) {a b : T × F.E.Str}
    {τ : Tr (uLT C p.ds)} (h : p.ior.red.out a τ = some b) :
    ∃ rs gs, rs.length = p.b.rounds.length ∧ p.b.decide a.1 rs gs = .ok b.1 := by
  have hb' : (if sTests C p.stage a.2 τ then p.run a.1 (sView C p.stage a.2 τ) else none).map
      (fun xo => (xo, p.ior.imp a.2 τ)) = some b := h
  split at hb'
  · cases hrun : p.run a.1 (sView C p.stage a.2 τ) with
    | none =>
      rw [hrun] at hb'
      cases hb'
    | some s' =>
      rw [hrun] at hb'
      obtain rfl := Option.some.inj hb'
      obtain ⟨gs, hfit, hdec⟩ := single_ok hrun
      exact ⟨_, gs, by rw [List.length_map]; exact roundsFit_length _ _ hfit, hdec⟩
  · cases hb'

/-- **A piece whose block keeps the chain's end has what it owes**, at any errors. -/
theorem commit_goodIn {F : Frame} (P : Where) (pcW : Piece (ckP .two) F S Cl W)
    (hext : ∀ a τ w, pcW.ext a τ w = w) (hK : KeepsEnd pcW.b) {k : ℕ} (rw : W → Wit GE nR k)
    (Pin : F.E.Str → W → Prop)
    (hback : ∀ a τ b w, pcW.ior.red.out a τ = some b → Pin b.2 w → Pin a.2 w) :
    pcW.GoodIn (FrontOk P) (FrontOk P) (RowsHold rw Pin) (RowsHold rw Pin) := by
  intro a ha
  refine Doomed.of_forall _ _ fun τ b hb => ?_
  obtain ⟨rs, gs, hl, hdec⟩ := piece_ok_len pcW hb
  obtain ⟨hc, hr, hlin⟩ := hK _ _ _ _ hl hdec
  refine ⟨fun l hl' => ?_, fun w hw => ?_⟩
  · have h1 := ha l (by rw [← hlin]; exact hl')
    exact ⟨h1.1, by show P.lin.kCol ≤ (linLayW b.1.st.codes P.lin).bits; rw [hc]; exact h1.2⟩
  · rw [hext]
    exact ⟨hback a τ b w hb hw.1, by rw [← hr]; exact hw.2⟩

/-- A block without a round joined behind leaves "the block is owed just its stretch". -/
theorem then_owed {T : Type} {C : PQ.CK} {F : Frame} (pc : Piece C F T Cl W) (nm : String)
    (q : Block T Cl) (hq : q.rounds = []) (h : pc.Owed) : (Piece.then pc nm q).Owed := by
  have hr : (pc.b.andThen nm q).rounds = pc.b.rounds := by
    show pc.b.rounds ++ q.rounds = _
    rw [hq, List.append_nil]
  refine ⟨?_, fun y τ => ?_⟩
  · show pc.ds.length + pc.back.length = (pc.b.andThen nm q).rounds.length
    rw [hr]
    exact h.1
  · have h2 := h.2 y τ
    show (List.flatMap id (groupsOf F.ft (pc.b.andThen nm q).rounds _)).length = _
    rw [hr]
    exact h2

/-- And "its trees are listed", which does not read the block. -/
theorem then_listed {T : Type} {C : PQ.CK} {F : Frame} (pc : Piece C F T Cl W) (nm : String)
    (q : Block T Cl) (h : pc.Listed) : (Piece.then pc nm q).Listed := h

/-- The conditions at the three places of the row. -/
def jointOn {F : Frame} (P : Where) (idx : ℕ) : ℕ → S × F.E.Str → Prop
  | 0 => fun a => a.1.out.indexMasks = idx
  | 1 => FrontOk P
  | _ => fun b => EvalLaid P b.1

/-- The relations at the three places of the row. -/
def jointR {F : Frame} (P : Where) (idx : ℕ) (rwM : W → Fin nR → (Fin P.lin.kCol → Bool) → GE)
    (rwW : W → Words GE) (dec : F.E.Str → Wit GE nR P.lin.kCol) : ℕ → S × F.E.Str → W → Prop
  | 0 | 1 => RowsHold (fun w => witOf (rwM w) (rwW w))
      (pinOf2 idx (fun w => witOf (rwM w) (rwW w)) dec)
  | _ => Behind P rwM rwW (pinOf2 idx (fun w => witOf (rwM w) (rwW w)) dec)

/-- **The two pieces in a row**, each between its two places: the batching's joined block; W's
commitment with the kind's block behind it. -/
theorem joint (F : Frame) (P : Where) (base : ℕ) (dZ d0 : RDT) (ds : List RDT)
    (hD : Declared P dZ d0 ds) (idx : ℕ) (rwM : W → Fin nR → (Fin P.lin.kCol → Bool) → GE)
    (rwW : W → Words GE) (dec : F.E.Str → Wit GE nR P.lin.kCol) (hloc : Local base dec)
    (pcW : Piece (ckP .two) F S Cl W) (hext : ∀ a τ w, pcW.ext a τ w = w) (hK : KeepsEnd pcW.b)
    (hlocW : Local pcW.base dec) :
    EachGoodIn (jointOn P idx) (jointR P idx rwM rwW dec) 0
      [pieceM3 F P base dZ d0 ds,
        Piece.then pcW "W's commitment, the own group and (Eval)" (rowsB atS P)] :=
  ⟨atM3_at_joint F P base dZ d0 ds hD idx rwM rwW dec hloc,
    atM4_goodIn_laid P pcW (FrontOk P) _ rwM rwW _
      (commit_goodIn P pcW hext hK _ _
        (back_of_reads pcW _ fun y y' w h1 h2 hw => by
          have e : dec y = dec y' := hlocW y y' h1 h2
          show AgreeAt idx _ (dec y')
          rw [← e]
          exact hw)),
    trivial⟩

end VerifiableInference.Desc.K13.Law
