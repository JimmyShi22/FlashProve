-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/KeepsAtPlace.lean: K9's CLAUSE OF "KEEPS" FOR THE WHOLE MEMBER, IN ONE FORM, AS A
FUNCTION OF THE PLACE: what an accepting step of a member of the kind K9 leaves and turns of the verifier's state. K9
has three members a segment, each with a clause of its own (`K9Keeps`, Honest/K9/Keeps.lean; `EqKeeps`, `ShutKeeps`,
Honest/K9/CloseKeeps.lean); here ONE TERM over the three, picked by the place's segment and piece, and both ways
between it and the three at the seated blocks' own places. One definition; statements and proofs ON THE VERIFIER's
TEXT; no thread, no prover; no goal is stated.
  **`k9KeepsAt c Z a s s'`**   c: the first chain · Z: the public part · a: the place: s' bears no mark of failure;
      and, l the place's segment, Lk the chain's link at l, p K9's numbers at l (`IM.k9At Z l`): at the piece p.piece:
      `K9Keeps p ‹Lk's gatherer› s s'` · at the piece p.pieceEq: `EqKeeps s s'` · at the piece p.pieceEq + 2:
      `ShutKeeps s s'`
OF THE PLACE IT READS THE SEGMENT AND THE PIECE ALONE: not the chain, not the kind. AT A PLACE WHOSE SEGMENT AND PIECE
ARE NONE OF K9's THREE (another piece, no segment, or a segment at which the chain has no link or K9 no numbers) IT
SAYS "NO MARK BEHIND" AND NOTHING ELSE: neither true nor false outright.  `k9KeepsAt_of`   the tool: from the three
arms at one segment's link and numbers. No two arms fire at one place: p.pieceEq = p.piece + 2 for every p that
`IM.k9At` gives
  `k9KeepsAt_bat`, `k9KeepsAt_eq`, `k9KeepsAt_shut`   from each member's own clause: the one form at the seated
      block's own place
  `bat_of_k9KeepsAt`, `eq_of_k9KeepsAt`, `shut_of_k9KeepsAt`   and back
  `piece_at_seat`   under an opening in the goals' scope: p.piece is the number of the segment's hearing kinds + 1
      (the library's `IM.k9_alone`): so the closing's addresses `IM.cAt l (IM.subAt l) 0 | 2 .K9` have the pieces
      p.pieceEq, p.pieceEq + 2 (drawn within the two step lemmas: no theorem of its own)
  **`k9KeepsAt_step_bat`**, **`k9KeepsAt_step_eq`**, **`k9KeepsAt_step_shut`**   under the library's head, l < 25, at
      whatever block blk stands at the member's number in the first chain's flat list: a yes of blk's step from s to
      s' ⊢ `k9KeepsAt cF Zp blk.place s s'`
  `kind_bat_at`, `kind_eq_at`, `kind_shut_at`   there blk.place.kind = .K9: what the frame's `head_keeps_kind`
      (Honest/Thread/KeepsBy.lean) asks beside its own block's line, which stands at the thread's list of blocks, not
      at `cF.blocksInOrder`: that tie is the caller's (the frame's `sits_head`). To the letter at κ := .K9 BY READING:
      KeepsBy.lean is not in the tree that rode
THE WAY BACK IS TYPED AT THE SEATS ALONE: under the head its caller opens `seats_at_head`, ties blk to the seated
block by the block's line, and pays the piece's equation by `piece_at_seat` with `IM.k9Where_fields`, as the two step
lemmas do within: no lemma of ours. AT THE BATCHING WHAT IS LEFT IS NO FIELD OF THE CLAUSE: it is drawn by
`K9Keeps.left`, under a premise on each kind's run (Honest/K9/Keeps.lean's head).
WHAT IS NOT CLAIMED. That a yes is there. What the three clauses do not say. That the frame's letter is laid at this
term: f .K9 := `k9KeepsAt cF Zp` fits the frame's `kpBy` by reading of its type: not typed. No member: called by no
line. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.XkAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First

/-- **K9's clause for the whole member, by the place.** -/
def k9KeepsAt (c : Chain S Claim) (Z : ProofFile.Pub) (a : Place) (s s' : S) : Prop :=
  s'.failed = none ∧ ∀ l Lk p, a.link = some l → c.links[l]? = some Lk → IM.k9At Z l = some p →
    (a.piece = p.piece → K9Keeps p (claimsInBy Lk.each Lk.hear Lk.order) s s') ∧
    (a.piece = p.pieceEq → EqKeeps s s') ∧ (a.piece = p.pieceEq + 2 → ShutKeeps s s')

variable {c : Chain S Claim} {Z : ProofFile.Pub} {l : ℕ} {Lk : Link S Claim} {p : Desc.K9.Where}

/-- From one of the three at its piece: the two other arms are idle, for p.pieceEq = p.piece + 2. -/
theorem k9KeepsAt_of {a : Place} {s s' : S} (hl : a.link = some l) (hL : c.links[l]? = some Lk)
    (hp : IM.k9At Z l = some p) (hm : s'.failed = none)
    (h1 : a.piece = p.piece → K9Keeps p (claimsInBy Lk.each Lk.hear Lk.order) s s')
    (h2 : a.piece = p.pieceEq → EqKeeps s s') (h3 : a.piece = p.pieceEq + 2 → ShutKeeps s s') :
    k9KeepsAt c Z a s s' := by
  refine ⟨hm, fun l' Lk' p' e1 e2 e3 => ?_⟩
  obtain rfl : l = l' := Option.some.inj (hl.symm.trans e1)
  obtain rfl : Lk = Lk' := Option.some.inj (hL.symm.trans e2)
  obtain rfl : p = p' := Option.some.inj (hp.symm.trans e3)
  exact ⟨h1, h2, h3⟩

/-- The batching's clause gives the one form at the batching's own place. -/
theorem k9KeepsAt_bat {kk : ℕ} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree c Z l kk Lk p w)
    {s s' : S} (K : K9Keeps p (claimsInBy Lk.each Lk.hear Lk.order) s s') :
    k9KeepsAt c Z (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).place s s' := by
  obtain ⟨-, e2, e3⟩ := IM.k9Where_fields Sd.numbers
  rw [Sd.seat]
  refine k9KeepsAt_of (l := l) (by rw [e2]) Sd.link Sd.numbers K.mark (fun _ => K) (fun e => ?_) fun e => ?_
  · exact absurd e (by show p.piece ≠ p.pieceEq; omega)
  · exact absurd e (by show p.piece ≠ p.pieceEq + 2; omega)

/-- And back. -/
theorem bat_of_k9KeepsAt {kk : ℕ} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree c Z l kk Lk p w)
    {s s' : S} (K : k9KeepsAt c Z (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).place s s') :
    K9Keeps p (claimsInBy Lk.each Lk.hear Lk.order) s s' := by
  obtain ⟨-, e2, -⟩ := IM.k9Where_fields Sd.numbers
  rw [Sd.seat] at K
  exact (K.2 l Lk p (by rw [e2]) Sd.link Sd.numbers).1 rfl

variable {Q : Close.Par} {bE bS : Block S Claim}

/-- The clause of "the one equation" gives the one form at that block's own place. pc: the piece of its address. -/
theorem k9KeepsAt_eq (H : SeatedClose c Z l Lk p Q bE bS)
    (pc : (IM.cAt l (IM.subAt l) 0 .K9).piece = p.pieceEq) {s s' : S} (K : EqKeeps s s') :
    k9KeepsAt c Z bE.place s s' := by
  obtain ⟨-, -, e3⟩ := IM.k9Where_fields H.numbers
  rw [IM.alone_place H.aloneE]
  refine k9KeepsAt_of (l := l) rfl H.link H.numbers K.mark (fun e => ?_) (fun _ => K) fun e => ?_
  · exact absurd (pc.symm.trans e) (by omega)
  · exact absurd (pc.symm.trans e) (by omega)

/-- And back. -/
theorem eq_of_k9KeepsAt (H : SeatedClose c Z l Lk p Q bE bS)
    (pc : (IM.cAt l (IM.subAt l) 0 .K9).piece = p.pieceEq) {s s' : S} (K : k9KeepsAt c Z bE.place s s') :
    EqKeeps s s' := by
  rw [IM.alone_place H.aloneE] at K
  exact (K.2 l Lk p rfl H.link H.numbers).2.1 pc

/-- The clause of "the segment is shut" gives the one form at that block's own place. -/
theorem k9KeepsAt_shut (H : SeatedClose c Z l Lk p Q bE bS)
    (pc : (IM.cAt l (IM.subAt l) 2 .K9).piece = p.pieceEq + 2) {s s' : S} (K : ShutKeeps s s') :
    k9KeepsAt c Z bS.place s s' := by
  obtain ⟨-, -, e3⟩ := IM.k9Where_fields H.numbers
  rw [IM.alone_place H.aloneS]
  refine k9KeepsAt_of (l := l) rfl H.link H.numbers K.mark (fun e => ?_) (fun e => ?_) fun _ => K
  · exact absurd (pc.symm.trans e) (by omega)
  · exact absurd (pc.symm.trans e) (by omega)

/-- And back. -/
theorem shut_of_k9KeepsAt (H : SeatedClose c Z l Lk p Q bE bS)
    (pc : (IM.cAt l (IM.subAt l) 2 .K9).piece = p.pieceEq + 2) {s s' : S} (K : k9KeepsAt c Z bS.place s s') :
    ShutKeeps s s' := by
  rw [IM.alone_place H.aloneS] at K
  exact (K.2 l Lk p rfl H.link H.numbers).2.2 pc

/-- K9's piece at a segment, in the goals' scope. -/
theorem piece_at_seat {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hl : l < 25) (hp : IM.k9At Z l = some p) :
    p.piece = (kindsBeforeBatching (IM.subAt l) (l == 0)).length + 1 := by
  obtain ⟨_, p', _, hp', e, _⟩ := IM.k9_alone O l (IM.subAt l) (IM.subs_scope hS hR O l hl)
  obtain rfl : p' = p := Option.some.inj (hp'.symm.trans hp)
  exact e

section
variable {Zl : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} (h : P5J.AtMgA OnBytes.secondHashFunction Zl D r Zp Np cF x) (hl : l < 25)
  {blk : Block S ProofFile.Cl} (ft : ℕ) {s s' : S}
include h hl

/-- The block at the batching's number stands at a place of the kind K9. -/
theorem kind_bat_at (hb : cF.blocksInOrder[14 * l + IM.nAt l + 2]? = some blk) : blk.place.kind = .K9 := by
  obtain ⟨Lk, p, w, Q, bE, bS, Sd, -⟩ := seats_at_head h hl
  obtain rfl := Option.some.inj (hb.symm.trans Sd.batching)
  rw [Sd.seat]

/-- The like at "the one equation". -/
theorem kind_eq_at (hb : cF.blocksInOrder[14 * l + IM.nAt l + 4 + 0]? = some blk) : blk.place.kind = .K9 := by
  obtain ⟨Lk, p, w, Q, bE, bS, Sd, H⟩ := seats_at_head h hl
  have e := H.atE
  rw [Sd.hears] at e
  obtain rfl := Option.some.inj (hb.symm.trans e)
  rw [IM.alone_place H.aloneE]

/-- The like at "the segment is shut". -/
theorem kind_shut_at (hb : cF.blocksInOrder[14 * l + IM.nAt l + 4 + 2]? = some blk) : blk.place.kind = .K9 := by
  obtain ⟨Lk, p, w, Q, bE, bS, Sd, H⟩ := seats_at_head h hl
  have e := H.atS
  rw [Sd.hears] at e
  obtain rfl := Option.some.inj (hb.symm.trans e)
  rw [IM.alone_place H.aloneS]

/-- **The one form behind the batching's yes.** -/
theorem k9KeepsAt_step_bat (hb : cF.blocksInOrder[14 * l + IM.nAt l + 2]? = some blk) (hy : IM.Yes ft blk s s') :
    k9KeepsAt cF Zp blk.place s s' := by
  obtain ⟨Lk, p, w, Q, bE, bS, Sd, -⟩ := seats_at_head h hl
  obtain rfl := Option.some.inj (hb.symm.trans Sd.batching)
  obtain ⟨rs, cols, n, hstep⟩ := hy
  exact k9KeepsAt_bat Sd (k9Keeps_of_step Sd ft s s' rs cols n hstep)

/-- **The one form behind the yes of "the one equation".** -/
theorem k9KeepsAt_step_eq (hb : cF.blocksInOrder[14 * l + IM.nAt l + 4 + 0]? = some blk) (hy : IM.Yes ft blk s s') :
    k9KeepsAt cF Zp blk.place s s' := by
  obtain ⟨Lk, p, w, Q, bE, bS, Sd, H⟩ := seats_at_head h hl
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have e := H.atE
  rw [Sd.hears] at e
  obtain rfl := Option.some.inj (hb.symm.trans e)
  obtain ⟨rs, cols, n, hstep⟩ := hy
  obtain ⟨-, -, e3⟩ := IM.k9Where_fields H.numbers
  have e1 := piece_at_seat h.scope h.reads O hl H.numbers
  exact k9KeepsAt_eq H (by show _ + 3 + 0 = p.pieceEq; omega) (H.eqKeeps ft s s' rs cols n hstep)

/-- **The one form behind the yes of "the segment is shut".** -/
theorem k9KeepsAt_step_shut (hb : cF.blocksInOrder[14 * l + IM.nAt l + 4 + 2]? = some blk) (hy : IM.Yes ft blk s s') :
    k9KeepsAt cF Zp blk.place s s' := by
  obtain ⟨Lk, p, w, Q, bE, bS, Sd, H⟩ := seats_at_head h hl
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have e := H.atS
  rw [Sd.hears] at e
  obtain rfl := Option.some.inj (hb.symm.trans e)
  obtain ⟨rs, cols, n, hstep⟩ := hy
  obtain ⟨-, -, e3⟩ := IM.k9Where_fields H.numbers
  have e1 := piece_at_seat h.scope h.reads O hl H.numbers
  exact k9KeepsAt_shut H (by show _ + 3 + 2 = p.pieceEq + 2; omega) (H.shutKeeps ft s s' rs cols n hstep)

end

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.k9KeepsAt_of
#print axioms ProofFile.Honest.K9.k9KeepsAt_bat
#print axioms ProofFile.Honest.K9.bat_of_k9KeepsAt
#print axioms ProofFile.Honest.K9.k9KeepsAt_eq
#print axioms ProofFile.Honest.K9.eq_of_k9KeepsAt
#print axioms ProofFile.Honest.K9.k9KeepsAt_shut
#print axioms ProofFile.Honest.K9.shut_of_k9KeepsAt
#print axioms ProofFile.Honest.K9.piece_at_seat
#print axioms ProofFile.Honest.K9.kind_bat_at
#print axioms ProofFile.Honest.K9.kind_eq_at
#print axioms ProofFile.Honest.K9.kind_shut_at
#print axioms ProofFile.Honest.K9.k9KeepsAt_step_bat
#print axioms ProofFile.Honest.K9.k9KeepsAt_step_eq
#print axioms ProofFile.Honest.K9.k9KeepsAt_step_shut
#print axioms ProofFile.Honest.K9.k9KeepsAt
