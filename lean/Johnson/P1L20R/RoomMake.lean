-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1L20R/RoomMake.lean: THE MAKE OF THE FACT ON THE INDEX MASKS' ROOM, BOTH CLAUSES:
`RoomOwes.make` (RoomFold.lean) at start := `ProofFile.startS Z` and
free0 := `free0Of Bs.G₀.first (gpOf Z)`: behind an accepting step, from the first state, of number 2
of the first chain's flat list (link 0's first sub-protocol, with "opened" joined behind it) the
message that the frame's test on the index masks finds (1) has the fresh ledger and (2) is a member
of no group. A JOINING of four groups of files. Theorems with their proofs. The
statements are those files', to the letter.

  `first_step_is`: a block of a lot of the kind K1 at link 0, piece 1, that accepts a step: the
    decision of `K1.firstSegmentOpening` accepts at two rounds: `lot_K1`, `k1_mem`,
    `numbers_pieces` (Johnson/IMR/K1Seat.lean); `K1.step_ok`.
  `first_step_atStart`: from the first state: that state's shape has a notice at the start
    (`ProofFile.Law.firstAtS_atStart`, Johnson/Desc/K1/Law/FirstMakeFacts.lean).
  `startS_groups`: a first state from which the opening accepts has no group.
  `first_step_out`: behind such a step the message that `IndexMasksAt` finds is a member of no
    group: `K1.firstAtS_group` (Johnson/Desc/K1/Law/GroupAtRecord.lean: the opening makes one group,
    of its own messages alone) and `K1.firstAtS_im` (K1/Law/FirstIndexMasks.lean: what is found is
    the sending's last message).
  `room_make`: the first clause: by `make_at` (RoomFold.lean) and `first_sending_fresh`
    (K12LotR/FirstSendingFresh.lean) with `ground_last_maskRows`, `ground_last_answers`.
  `room_make_out`: the second clause: by `make_out_at` (RoomFold.lean).
  **`room_make_both`**: `RoomOwes.make`, whole. `roomOwes_of_keep`: `RoomOwes` from its field `keep`
    alone: so Lean holds `room_make_both` against the structure's own field.

Limits. Nothing on soundness. `RoomOwes.keep` stays owed. Laws from an accept: idle where the step
rejects.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P1L20R.RoomFold
import Johnson.K12LotR.FirstSendingFresh
import Johnson.Desc.K1.Law.FirstMakeFacts
import Johnson.Desc.K1.Law.GroupAtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1L20

open VerifiableInference.Desc (Block Chain FileDescription KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1 (free0Of gpOf first_sending_fresh firstSegmentOpening firstPar)
open Johnson.Desc.First.Walk.Tied
open Johnson.Desc.First.Walk.Props (IndexMasksAt)
open ProofFile (Cl)

/-- Link 0's first sub-protocol, as its lot has it, is the first segment's opening: an accepting
step of it is an accept of that opening's decision, at two rounds. -/
theorem first_step_is {Z : ProofFile.Pub} {G : ProofFile.Ground} (b' : Block S Cl) (s : S)
    (rs : List Fmt.RoundView) (cols : List VerifiableInference.Desc.OpenedColumn) (m : S) (n : ℕ)
    (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G) (hk : b'.place.kind = KindName.K1)
    (hl : b'.place.link = some 0) (hpc : b'.place.piece = 1)
    (hst : b'.step 0 s rs cols = .ok (m, n)) :
    ∃ r₁ r₂ gs, (firstSegmentOpening G.first (gpOf Z) : Block S Unit).decide s [r₁, r₂] gs = .ok m := by
  obtain ⟨L, hL, hb⟩ := hlot
  obtain ⟨x, hx, rfl⟩ := IM.lot_K1 hL hb hk hl
  rcases IM.k1_mem hx with rfl | ⟨l', X, pr, pd, reads, digits, hX, hn, rfl | rfl⟩
  · obtain ⟨hfit, gs, hd⟩ := VerifiableInference.Desc.K1.step_ok 0 _ s m rs cols n hst
    have hfit' : VerifiableInference.Desc.roundsFit
        (VerifiableInference.Desc.K1.rounds (firstPar G.first (gpOf Z))) rs = true := hfit
    unfold VerifiableInference.Desc.K1.rounds at hfit'
    rcases rs with _ | ⟨a, _ | ⟨b, _ | ⟨c, tl⟩⟩⟩
    · simp [VerifiableInference.Desc.roundsFit] at hfit'
    · simp [VerifiableInference.Desc.roundsFit] at hfit'
    · exact ⟨_, _, gs, hd⟩
    · simp [VerifiableInference.Desc.roundsFit] at hfit'
  · exfalso
    have epc : pr = 1 := hpc
    rcases IM.numbers_pieces hn with ⟨h', -⟩ | ⟨h', -⟩ <;> omega
  · exfalso
    have epc : pd = 1 := hpc
    rcases IM.numbers_pieces hn with ⟨-, h'⟩ | ⟨-, h'⟩ <;> omega

section
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub} {G : ProofFile.Ground}

/-- Where it accepts a step from the first state, that state's shape has a notice at the start. -/
theorem first_step_atStart (h : ProofFile.pubPlain o pol lay KL = .ok Z) (z : ProofFile.InstPub)
    (b' : Block S Cl) (rs : List Fmt.RoundView) (cols : List VerifiableInference.Desc.OpenedColumn) (m : S) (n : ℕ)
    (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G) (hk : b'.place.kind = KindName.K1)
    (hl : b'.place.link = some 0) (hpc : b'.place.piece = 1)
    (hst : b'.step 0 (ProofFile.startS Z z) rs cols = .ok (m, n)) :
    (ProofFile.startS Z z).check.frame.shape.atStart ≠ [] := by
  obtain ⟨r₁, r₂, gs, hd⟩ := first_step_is b' _ rs cols m n hlot hk hl hpc hst
  exact ProofFile.Law.firstAtS_atStart h z G.first (gpOf Z) _ gs m hd

/-- A first state from which the opening accepts has no group. -/
theorem startS_groups (h : ProofFile.pubPlain o pol lay KL = .ok Z) (z : ProofFile.InstPub)
    (q : OnBytes.Params.First) (gp : _root_.Desc.Plain.GPar) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) (m : S)
    (hd : (firstSegmentOpening q gp : Block S Unit).decide (ProofFile.startS Z z) rs gs = .ok m) :
    (ProofFile.startS Z z).st.groups = #[] := by
  cases hz : ((Z.s₀.withReq (OnBytes.Model.Verify.words32 z.request)).reqOk Z.p.X.T
      Z.p.X.P.h.V) with
  | false =>
    rw [(ProofFile.Law.startS_blank Z z hz).1] at hd
    exact absurd hd (ProofFile.Law.firstAtS_blank q gp rs gs m)
  | true =>
    have e0 := ProofFile.Law.startP_is (ProofFile.Law.pubBy_start h)
    unfold ProofFile.startS
    dsimp only
    rw [if_pos hz]
    show Z.s₀.st.groups = #[]
    rw [e0]
    rfl

/-- **Behind such a step the message that the frame's test on the index masks finds is a member of
no group.** -/
theorem first_step_out (h : ProofFile.pubPlain o pol lay KL = .ok Z) (z : ProofFile.InstPub)
    (b' : Block S Cl) (rs : List Fmt.RoundView) (cols : List VerifiableInference.Desc.OpenedColumn) (m : S) (n : ℕ)
    (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G) (hk : b'.place.kind = KindName.K1)
    (hl : b'.place.link = some 0) (hpc : b'.place.piece = 1)
    (hst : b'.step 0 (ProofFile.startS Z z) rs cols = .ok (m, n)) (room im : ℕ)
    (hi : IndexMasksAt room m.check m.st.oracles im) : ∀ Gr ∈ m.st.groups, im ∉ Gr.members := by
  obtain ⟨r₁, r₂, gs, hd⟩ := first_step_is b' _ rs cols m n hlot hk hl hpc hst
  have hne := ProofFile.Law.firstAtS_atStart h z G.first (gpOf Z) _ gs m hd
  have hg0 := startS_groups h z G.first (gpOf Z) _ gs m hd
  obtain ⟨hO, -, hlt⟩ := VerifiableInference.Desc.K1.firstAtS_group G.first (gpOf Z) _ m r₁ r₂ gs hd
  obtain ⟨-, him⟩ := VerifiableInference.Desc.K1.firstAtS_im G.first (gpOf Z) _ m r₁ r₂ gs hd hne
    room im hi
  obtain ⟨G₀, hG₀, -, -, hmem⟩ := hO.made
  have hsz := hO.size
  rw [hg0] at hG₀ hsz
  intro Gr hGr hin
  obtain ⟨j, hj, ej⟩ := Array.mem_iff_getElem.1 hGr
  have hj0 : j = 0 := by
    have : m.st.groups.size = 1 := hsz
    omega
  subst hj0
  have e1 : m.st.groups[0]? = some Gr := by
    rw [Array.getElem?_eq_getElem hj, ej]
  obtain rfl : G₀ = Gr := Option.some.inj (hG₀.symm.trans e1)
  have := (hmem im).1 (Array.mem_toList_iff.2 hin)
  omega

end

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The make's first clause.** -/
theorem room_make (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ b z s', c.blocksInOrder[2]? = some b → StepYes 0 b (ProofFile.startS Z z) s' →
      leftIsB (free0Of Bs.G₀.first (gpOf Z)) s' = true := by
  intro b z s' hb hy
  refine make_at hS hR O (s := ProofFile.startS Z z) (fun b' rs cols m n hlot hk hl hpc hst room im hi =>
          ?_) b s' hb hy
  exact first_sending_fresh (ProofFile.Law.ground_last_maskRows O.pub O.blank (gpOf Z))
    (ProofFile.Law.ground_last_answers O.pub O.blank (gpOf Z)) b' _ rs cols m n hlot hk hl hpc
    (first_step_atStart O.pub z b' rs cols m n hlot hk hl hpc hst) hst room im hi

/-- **The make's second clause.** -/
theorem room_make_out (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ b z s', c.blocksInOrder[2]? = some b → StepYes 0 b (ProofFile.startS Z z) s' → outOfGroupsB s' = true :=
  fun b z s' hb hy => make_out_at hS hR O (s := ProofFile.startS Z z)
    (fun b' rs cols m n hlot hk hl hpc hst room im hi =>
      first_step_out O.pub z b' rs cols m n hlot hk hl hpc hst room im hi) b s' hb hy

/-- **THE MAKE, WHOLE.** -/
theorem room_make_both (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ b z s', c.blocksInOrder[2]? = some b → StepYes 0 b (ProofFile.startS Z z) s' →
      leftIsB (free0Of Bs.G₀.first (gpOf Z)) s' = true ∧ outOfGroupsB s' = true :=
  fun b z s' hb hy => ⟨room_make hS hR O b z s' hb hy, room_make_out hS hR O b z s' hb hy⟩

/-- **So of `RoomOwes` the keeping alone is left**: Lean holds `room_make_both` against the
structure's own field `make`. -/
theorem roomOwes_of_keep (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hk : ∀ k, 3 ≤ k → k < 355 → isOurs k = false → ∀ b z s s',
      Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s) → c.blocksInOrder[k]? = some b → StepYes 0 b s s' →
      outOfGroupsB s = true → ∀ n, leftIsB n s = true →
        leftIsB n s' = true ∧ outOfGroupsB s' = true) :
    RoomOwes c (ProofFile.startS Z) (free0Of Bs.G₀.first (gpOf Z)) :=
  ⟨room_make_both hS hR O, hk⟩

end

end P1L20

#print axioms P1L20.first_step_is
#print axioms P1L20.first_step_atStart
#print axioms P1L20.startS_groups
#print axioms P1L20.first_step_out
#print axioms P1L20.room_make
#print axioms P1L20.room_make_out
#print axioms P1L20.room_make_both
#print axioms P1L20.roomOwes_of_keep
