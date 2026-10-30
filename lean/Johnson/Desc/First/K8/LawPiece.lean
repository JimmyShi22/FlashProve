-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawPiece.lean: THE SMALLNESS TEST, ITS FIRST HALF, AS A PIECE OF THE RULE OF
COMPOSITION: THE KIND'S BLOCK, AT ITS OWN STRETCH, IS GOOD BETWEEN ITS TWO BOUNDARIES.

The rule of composition for one hash chain (Johnson/Desc/Sound/ChainRule.lean) asks ONE premise of
each block (`EachGood`): the block, run by the chain's own fold on its own stretch of written rounds
(`Piece.bk`), has the library's property `KObj.BK.Good` between what stands at the boundary in front
of it and what stands behind it. `PieceGood` (proved there: `pieceGood`) gives that premise from a
proved reduction of the library. Here its premises are met by the kind's own text
(Johnson/Desc/First/K8/Hear.lean) and the proved block for the draw of the matrix
(`KObj.KTailRngOn`, Johnson/Top/H/TailRngOn.lean), whoever calls that block.
  `chainAt_one`: a chain of one block with one round: its yes is the block's yes as a step.
  `piece seat p base e`: the kind's block with its stretch: one written round (`rdt p`); the
    extractor hands the witness through; e: its error: how many values of the written challenge may
    rescue a prover that has lost.
  `piece_out`: where the piece's reduction puts out: the round's test of work passed; the block said
    yes as a step on the view of the written transcript; the oracles behind are the stage's.
  `Reads seat p base e d`: THE LETTERS: how a statement at the boundary (the carried record and the
    frame's oracles) is read as a statement of the proved block's caller d, how a witness is read,
    how the matrix is read off the record; with two laws: what the seat lays is read back; the
    block's own writing, and its stretch, do not turn the reading of the statement.
  `onA`, `relA`, `onB`, `relB`: what stands at the two boundaries: the proved block's own joints,
    read through the letters. Behind the block the matrix of the typed statement is the one whose
    list lies in the record.
  `piece_good`: **THE PIECE IS GOOD** between them, if the place's numbers are the caller's
    (`Fits`), the caller's sizes meet the proved block's one condition, and e is at least the proved
    block's count times the sampler's own bound.
Definitions, statements and proofs.

Limits. NO CALLER IS NAMED: d and the letters are parameters: that there are letters at the carried
record of the first chain and a caller made of the public record over the frame's own oracle
messages is owed. A caller whose condition holds of no statement, or letters that read every
statement as one outside it, make the theorem true and empty. `relB` speaks of every typed matrix
whose list lies in the record (two typed matrices have one list if they differ in the idle bit of a
0 alone; the proved block's joint reads a matrix by its entries' values alone); `onB` says that
there is one. Nothing on the neighbours; nothing on acceptance.


-/
import Johnson.Desc.First.K8.LawView
import Johnson.Desc.Sound.ChainRuleProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open Iop Prob Cb.Pv.Tail OnBytes.Slice OnBytes.Maker OnBytes.Tie.Pv.Row OnBytes.Tie.Pv.Tail KObj
    KObj.RowCar KObj.TailRow
  VerifiableInference.OnPublicFiles VerifiableInference.Desc.Sound

/-- A chain of one block with one round: its yes is the block's yes as a step, on that round and all
the columns. -/
theorem chainAt_one {S Cl : Type} (name : String) (ft : Nat) (b : Block S Cl) (hb : b.rounds.length
    = 1) (s s' : S)
    (r : Fmt.RoundView) (cols : List Col) (h : chainAt name ft [b] s ⟨[r], cols⟩ = .ok s') :
    ∃ k, b.step ft s [r] cols = .ok (s', k) := by
  cases hs : b.step ft s [r] cols with
  | error e => simp [chainAt, foldBlocks, hb, hs] at h
  | ok x =>
    simp [chainAt, foldBlocks, hb, hs] at h
    cases hd : List.drop x.2 cols with
    | nil =>
      rw [hd] at h
      obtain rfl : x.1 = s' := by simpa using h
      exact ⟨x.2, rfl⟩
    | cons c l =>
      rw [hd] at h
      simp at h

section
variable {S Cl W : Type} {F : Frame}

/-- The kind's block with its stretch. -/
def piece (seat : Seat S) (p : Par) (base e : ℕ) : Piece (Run.ckP .two) F S Cl W where
  b := approximateRangeProofDrawKind seat p
  base := base
  ds := [rdt p]
  ext := fun _ _ w => w
  err := ((e, ()) : ℕ × Unit)

/-- Where the piece's reduction puts out. -/
theorem piece_out (seat : Seat S) (p : Par) (base e : ℕ) (a a' : S × F.E.Str)
    (m : (roundT (Run.ckP .two) (rdt p)).up.Msg) (c : (roundT (Run.ckP .two) (rdt p)).up.Chal)
    (h : (piece (Cl := Cl) (W := W) (F := F) seat p base e).ior.red.out a
      ((m, c, ()) : Tr (uLT (Run.ckP .two) [rdt p])) = some a') :
    okT [rdt p] ((m, c, ()) : Tr (uLT (Run.ckP .two) [rdt p])) ∧
      (∃ cols k, (approximateRangeProofDrawKind (Cl := Cl) seat p).step F.ft a.1
        (vT [rdt p] ((m, c, ()) : Tr (uLT (Run.ckP .two) [rdt p]))) cols = .ok (a'.1, k)) ∧
      a'.2 = (piece (Cl := Cl) (W := W) (F := F) seat p base e).ior.imp a.2
        ((m, c, ()) : Tr (uLT (Run.ckP .two) [rdt p])) := by
  have h' : ((piece (Cl := Cl) (W := W) (F := F) seat p base e).ior.out a.1 a.2
      ((m, c, ()) : Tr (uLT (Run.ckP .two) [rdt p]))).map (fun xo =>
        (xo, (piece (Cl := Cl) (W := W) (F := F) seat p base e).ior.imp a.2
          ((m, c, ()) : Tr (uLT (Run.ckP .two) [rdt p])))) = some a' := h
  cases ho : (piece (Cl := Cl) (W := W) (F := F) seat p base e).ior.out a.1 a.2
      ((m, c, ()) : Tr (uLT (Run.ckP .two) [rdt p])) with
  | none => rw [ho] at h'; simp at h'
  | some st' =>
    rw [ho] at h'
    obtain rfl : (st', (piece (Cl := Cl) (W := W) (F := F) seat p base e).ior.imp a.2
        ((m, c, ()) : Tr (uLT (Run.ckP .two) [rdt p]))) = a' := by simpa using h'
    have ho' : (if sTests (Run.ckP .two) (piece (Cl := Cl) (W := W) (F := F) seat p base e).stage
        a.2
          ((m, c, ()) : Tr (uLT (Run.ckP .two) [rdt p])) then
        (piece (Cl := Cl) (W := W) (F := F) seat p base e).run a.1
          (sView (Run.ckP .two) (piece (Cl := Cl) (W := W) (F := F) seat p base e).stage a.2
            ((m, c, ()) : Tr (uLT (Run.ckP .two) [rdt p]))) else none) = some st' := ho
    by_cases ht : sTests (Run.ckP .two) (piece (Cl := Cl) (W := W) (F := F) seat p base e).stage a.2
        ((m, c, ()) : Tr (uLT (Run.ckP .two) [rdt p])) = true
    · rw [if_pos ht] at ho'
      have hpass : okT [rdt p] ((m, c, ()) : Tr (uLT (Run.ckP .two) [rdt p])) := by
        simp only [sTests, Bool.and_eq_true] at ht
        exact ht.1.1
      have hr : (chainAt (approximateRangeProofDrawKind (Cl := Cl) seat p).name F.ft [approximateRangeProofDrawKind (Cl := Cl) seat p] a.1
          ⟨[rvOne (rdt p) m c], (sView (Run.ckP .two) (piece (Cl := Cl) (W := W) (F := F) seat p
              base e).stage a.2
            ((m, c, ()) : Tr (uLT (Run.ckP .two) [rdt p]))).opened⟩).toOption = some st' := ho'
      cases hc : chainAt (approximateRangeProofDrawKind (Cl := Cl) seat p).name F.ft [approximateRangeProofDrawKind (Cl := Cl) seat p] a.1
          ⟨[rvOne (rdt p) m c], (sView (Run.ckP .two) (piece (Cl := Cl) (W := W) (F := F) seat p
              base e).stage a.2
            ((m, c, ()) : Tr (uLT (Run.ckP .two) [rdt p]))).opened⟩ with
      | error x => rw [hc] at hr; simp [Except.toOption] at hr
      | ok s1 =>
        rw [hc] at hr
        obtain rfl : s1 = st' := by simpa [Except.toOption] using hr
        obtain ⟨k, hk⟩ := chainAt_one _ _ _ rfl _ _ _ _ hc
        exact ⟨hpass, ⟨_, k, by rw [vT_one]; exact hk⟩, rfl⟩
    · rw [if_neg ht] at ho'
      simp at ho'

/-- **The letters**: how what stands at a boundary of the chain is read as what the proved block's
caller d speaks of. -/
structure Reads (Cl W : Type) (F : Frame) (seat : Seat S) (p : Par) (base e : ℕ) (d : TailCallerOn)
    where
  /-- a statement at the boundary, as a statement in front of the proved block -/
  rd : S × F.E.Str → (KTailRngOn.src d).X × (KTailRngOn.src d).E.Str
  /-- a witness, as a witness of the proved block's joints -/
  wit : W → (KTailRngOn.src d).W
  /-- the matrix's list, off the record -/
  cf : S → Array Int
  /-- what the seat lays is read back -/
  cf_lay : ∀ (st st' : S) (mm : Array Int) (f : Array Nat), seat.lay st mm f = .ok st' → cf st' = mm
  /-- the block's own writing, and its stretch, do not turn the reading of the statement -/
  keeps : ∀ (st st' : S) (mm : Array Int) (f : Array Nat) (y : F.E.Str) (τ : Tr (uLT (Run.ckP .two)
      [rdt p])),
    seat.lay st mm f = .ok st' →
      rd (st', (piece (Cl := Cl) (W := W) (F := F) seat p base e).ior.imp y τ) = rd (st, y)

variable {seat : Seat S} {p : Par} {base e : ℕ} {d : TailCallerOn}

/-- The statement behind the proved block, at the matrix β. -/
def Reads.behind (Q : Reads Cl W F seat p base e d) (a : S × F.E.Str) (β : Dr d.c.s) :
    (KTailRngOn.dst d).X × (KTailRngOn.dst d).E.Str :=
  ((((Q.rd a).1.1, β), (Q.rd a).1.2), (Q.rd a).2)

/-- In front of the block: the proved block's first joint, read through the letters. -/
def Reads.onA (Q : Reads Cl W F seat p base e d) (a : S × F.E.Str) : Prop := (KTailRngOn.src d).on
    (Q.rd a)
def Reads.relA (Q : Reads Cl W F seat p base e d) (a : S × F.E.Str) (w : W) : Prop :=
  (KTailRngOn.src d).relR (Q.rd a) (Q.wit w)

/-- Behind it: the proved block's second joint, at every typed matrix whose list lies in the record;
there is one. -/
def Reads.onB (Q : Reads Cl W F seat p base e d) (a : S × F.E.Str) : Prop :=
  (∃ β : Dr d.c.s, Q.cf a.1 = listOf β) ∧ ∀ β : Dr d.c.s, Q.cf a.1 = listOf β → (KTailRngOn.dst
      d).on (Q.behind a β)
def Reads.relB (Q : Reads Cl W F seat p base e d) (a : S × F.E.Str) (w : W) : Prop :=
  ∀ β : Dr d.c.s, Q.cf a.1 = listOf β → (KTailRngOn.dst d).relR (Q.behind a β) (Q.wit w)

/-- What a yes of the piece gives, through the letters. -/
theorem Reads.of_out (Q : Reads Cl W F seat p base e d) (hf : Fits p d.c.s) (a a' : S × F.E.Str)
    (m : (roundT (Run.ckP .two) (rdt p)).up.Msg) (c : (roundT (Run.ckP .two) (rdt p)).up.Chal)
    (h : (piece (Cl := Cl) (W := W) (F := F) seat p base e).ior.red.out a
      ((m, c, ()) : Tr (uLT (Run.ckP .two) [rdt p])) = some a') :
    okT [rdt p] ((m, c, ()) : Tr (uLT (Run.ckP .two) [rdt p])) ∧ Q.cf a'.1 = listOf (matrixOf hf c)
        ∧
      Q.rd a' = Q.rd a := by
  obtain ⟨hok, ⟨cols, k, hstep⟩, himp⟩ := piece_out seat p base e a a' m c h
  have hl := ((hear_law_view (Cl := Cl) hf seat m c F.ft a.1 a'.1 k cols).1 hstep).2.2.2.2.2.2.2.2.1
  refine ⟨hok, Q.cf_lay _ _ _ _ hl, ?_⟩
  have hk := Q.keeps a.1 a'.1 _ _ a.2 ((m, c, ()) : Tr (uLT (Run.ckP .two) [rdt p])) hl
  rw [← himp] at hk
  exact hk

/-- **THE PIECE IS GOOD between its two boundaries.** -/
theorem piece_good (Q : Reads Cl W F seat p base e d) (hf : Fits p d.c.s) (hOK : d.c.s.OK)
    (he : (Fintype.card (Dr d.c.s) / 2 ^ d.c.s.tau) * (Run.bsRound .two (rdt p).entry (rdt
        p).kind).w ≤ e) :
    ((piece (Cl := Cl) (W := W) (F := F) seat p base e).bk Q.onA Q.onB Q.relA Q.relB).Good := by
  refine pieceGood S Cl W (Run.ckP .two) F (piece seat p base e) _ _ _ _ (KTailRngOn.blk d).R.red
    (fun _ => rngCarS d (rdt p) (onlyTrits hf)) (KTailRngOn.blk d).err Q.rd Q.onA Q.onB
        (KTailRngOn.src d).on
    Q.relA Q.relB (KTailRngOn.src d).relR (KTailRngOn.dst d).relR (KTailRngOn.blk d).ext ?_ ?_ ?_ ?_
        ?_
  · intro _
    exact rngCarS_fits d (rdt p) (onlyTrits hf) (Nat.zero_le _) _ e he
  · intro _ h
    exact h
  · intro a τ a' w _ hout hB
    obtain ⟨m, c, ⟨⟩⟩ := τ
    obtain ⟨hok, hcf, hrd⟩ := Q.of_out hf a a' m c hout
    obtain ⟨τ', h1, h2, _⟩ :=
      hearPlace d hf (rvOne (rdt p) m c) [] m c (Q.rd a) [] hok (by rw [vT_one]; rfl)
    refine ⟨τ', _, Q.wit w, h1, h2, ?_, fun h => h⟩
    have hb := hB (matrixOf hf c) hcf
    unfold Reads.behind at hb
    rw [hrd] at hb
    exact hb
  · intro a τ a' hout ha
    obtain ⟨m, c, ⟨⟩⟩ := τ
    obtain ⟨_, hcf, hrd⟩ := Q.of_out hf a a' m c hout
    refine ⟨⟨matrixOf hf c, hcf⟩, fun β _ => ?_⟩
    unfold Reads.behind
    rw [hrd]
    exact ha
  · exact (KTailRngOn_good d hOK).know.conseq (fun _ h => h) (fun _ _ _ h => h) (fun _ _ h => Or.inl
      h)

end

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.chainAt_one
#print axioms VerifiableInference.Desc.First.K8.piece_out
#print axioms VerifiableInference.Desc.First.K8.piece_good
