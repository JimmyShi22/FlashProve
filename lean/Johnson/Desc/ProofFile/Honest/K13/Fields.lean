-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K13/Fields.lean: kind K13, the members' batching: the three conditions
`fits`, `exact` and `fresh` of `Good` (Honest/Side.lean) at a side that has the kind's row, laid
into one term of `Good`. Statements with their proofs; no definition.

The form. The frame's rule for a file (`file_owed_rows`, Honest/Thread/Rows.lean, its hypothesis
`hand₁`) asks of the author of a row a term of `Good` at that row's side at any conditions A and B.
Of that term it reads `fits`, `exact` and `fresh`; `plays` and `acc` at its own A and B it makes
from its other hypotheses. So the term here stands at A := B := False, where `plays` and `acc` hold
vacuously. It is the kind's share of the hypothesis `hand₁` and of nothing else: it says nothing
about a run, about the verifier's acceptance or about any state. The field `good` of `Owed`
(Honest/Owed.lean) asks `plays` and `acc` at the row's own A and B too; only at rows whose A and B
are struck (`file_owed_rows_mute`, Honest/Thread/RowsMute.lean) is this term all that `good` asks.

  `k13_bud`   the kind's `bud` (RowsLot.lean of this folder) holds everywhere
  `k13_takes`   each part of the kind's row takes no coin of its own
  `fits_field`   the condition `fits`: the row has one move for each round, each simulator names its
     part's address, and there are as many lists of oracle messages as rounds
  `k13_numbers`   the members of such a side have the numbers 0 and 1
  `k13_no_send_seed`   no round of a sub-protocol with the kind's rounds is named "SEND seed"
  `sideSeated_row`, `sideSeated_place`, `sideSeated_mem`   what `Side.seated` returns: the row and
     the place that it is given, and a sub-protocol of the list. No kind is named
  `k13_good_of_due`   the term, at every book that passes its own tests and has no coin for the
     kind's two parts

`fresh` at this kind. The condition speaks of a part as the owner of coins. The kind's parts own
none, so it asks only that the book lets nobody spend a coin of theirs, and that follows from the
book's own tests (`freshMember_in_chain`, Honest/Small/FreshNoCoin.lean). The sentence with weight
is about the block that part 1 borrows: it is the condition `fresh` at the part that owns these
coins in the book, at part 1's address. It is not shown in this folder.

Limits.
  * The hypotheses of `k13_good_of_due`: the sub-protocol has the kind's rounds and declares no
    oracle message (hr, ho); the library's test on the shape accepts (hk); the book passes its tests
    at a description in whose first chain the place is (hw, hp, ha); the first chain's table has no
    coin for the two parts (hd). FieldsAtHead.lean of this folder proves them at the proof file's
    own description and book.
  * `exact` is the borrower's half: see the Limits of Exact.lean of this folder.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.K13.Exact
import Johnson.Desc.ProofFile.Honest.K13.RowsLot
import Johnson.Desc.ProofFile.Honest.K13.PlanPartsAtM3
import Johnson.Desc.ProofFile.Honest.Small.FreshNoCoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open VerifiableInference.Desc (Block FileDescription Place)
open VerifiableInference.Desc.K13 (Where battRounds)
open VerifiableInference.Desc.Part.MaskedSum (shapeOk)
open ProofFile.Honest.Small (exactAt_of_exact freshMember_in_chain)

variable {S Cl V W X Pb W₀ Rc Xi Tr : Type}

/-- The kind's `bud` holds at every number, all challenges and all lists of positions. -/
theorem k13_bud (n : Nat) (ds : List Fmt.Drawn) (asks : List (List (List Nat))) :
    k13Bud n ds asks := trivial

/-- Each part of the kind's row takes no coin of its own. -/
theorem k13_takes (weights : W₀ → Weights) (pile : PileOf Xi) (p : Where) :
    ∀ q ∈ k13Row (Rc := Rc) (Tr := Tr) (X := X) weights pile p, q.takes = ⟨0, 0⟩ := by
  intro q hq
  rcases List.mem_cons.1 hq with rfl | hq
  · rfl
  · rcases List.mem_cons.1 hq with rfl | hq
    · rfl
    · cases hq

/-- **The condition `fits`** at a side that has the kind's row beside a sub-protocol with the kind's
place and rounds, which declares no oracle message. -/
theorem fits_field (weights : W₀ → Weights) (pile : PileOf Xi) (p : Where)
    (σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)
    (hrow : σ.row = k13Pairs weights pile p) (hp : σ.block.place = k13Place p)
    (hr : σ.block.rounds = battRounds p)
    (ho : σ.block.oracles = List.replicate (2 + p.lin.kCol) []) : σ.fits = true := by
  have h1 : (σ.row.zipIdx.all fun s => s.1.2.addr == ⟨σ.block.place, s.2⟩) = true := by
    rw [hrow, hp]
    show ((⟨k13Place p, 0⟩ : Addr) == ⟨k13Place p, 0⟩ &&
      (((⟨k13Place p, 1⟩ : Addr) == ⟨k13Place p, 1⟩) && true)) = true
    simp
  have h2 : σ.half.rounds = 2 + p.lin.kCol := by
    show (⟨σ.block.place, σ.row.map (·.1)⟩ : Placed _ _ X).rounds = _
    rw [hrow, k13Pairs_parts]
    exact k13Half_rounds weights pile p
  unfold Side.fits
  rw [h1, h2, hr, ho, battRounds_length, List.length_replicate]
  simp

/-- The members of such a side have the numbers 0 and 1. -/
theorem k13_numbers (weights : W₀ → Weights) (pile : PileOf Xi) (p : Where)
    (σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)
    (hrow : σ.row = k13Pairs weights pile p) (hr : σ.block.rounds = battRounds p)
    (ho : σ.block.oracles = List.replicate (2 + p.lin.kCol) []) :
    ∀ u ∈ σ.members, u.number < 2 := by
  intro u hu
  rw [k13_members weights pile p σ hrow hr ho] at hu
  rcases List.mem_cons.1 hu with rfl | hu
  · exact Nat.zero_lt_two
  · rcases List.mem_cons.1 hu with rfl | hu
    · exact Nat.one_lt_two
    · cases hu

/-- No round of a sub-protocol with the kind's rounds is named "SEND seed". (That none is named
"FOLD epsilon": `k13_no_fold_epsilon`, PlanPartsAtM3.lean of this folder.) -/
theorem k13_no_send_seed {b : Block S Cl} {p : Where} (hr : b.rounds = battRounds p) :
    ∀ r ∈ b.rounds, r.entry.name ≠ "SEND seed" := by
  intro r hm
  have hn : r.entry.name ∈ (battRounds p).map (·.entry.name) :=
    List.mem_map.2 ⟨r, hr ▸ hm, rfl⟩
  rw [k13_names] at hn
  rcases List.mem_cons.1 hn with e | hn
  · rw [e]
    decide
  · rcases List.mem_cons.1 hn with e | hn
    · rw [e]
      decide
    · rw [List.eq_of_mem_replicate hn]
      decide

/-- The side that `Side.seated` returns has the row that it is given. -/
theorem sideSeated_row {bs : List (Block S Cl)} {a : Place} {row : List (Part V W X × Sim Pb)}
    {fs : List (Fall S)} {σ : Side S Cl V W X Pb} (h : Side.seated bs a row fs = some σ) :
    σ.row = row := by
  obtain ⟨b, -, rfl⟩ := Option.map_eq_some_iff.1 h
  rfl

/-- Its sub-protocol is at the place that it is given. -/
theorem sideSeated_place {bs : List (Block S Cl)} {a : Place} {row : List (Part V W X × Sim Pb)}
    {fs : List (Fall S)} {σ : Side S Cl V W X Pb} (h : Side.seated bs a row fs = some σ) :
    σ.block.place = a := by
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 h
  have hq := List.find?_some (p := fun x : Block S Cl => x.place == a) hb
  exact beq_iff_eq.1 hq

/-- Its sub-protocol is one of the list. -/
theorem sideSeated_mem {bs : List (Block S Cl)} {a : Place} {row : List (Part V W X × Sim Pb)}
    {fs : List (Fall S)} {σ : Side S Cl V W X Pb} (h : Side.seated bs a row fs = some σ) :
    σ.block ∈ bs := by
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 h
  exact List.mem_of_find?_eq_some hb

/-- **`fits`, `exact` and `fresh` as one term of `Good`, at A and B that are False**, at every book
that passes its own tests and has no coin for the kind's two parts. `plays` and `acc` hold
vacuously: the term is what the frame's rule takes from a row's author, and shows nothing beyond the
three conditions. It holds at every `pre`, face, order of places, chain number and first tree. -/
theorem k13_good_of_due {Xi' : Type} {F : FileDescription Xi'} {Bk : ProverCoinCounts}
    (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (weights : W₀ → Weights) (pile : PileOf Xi) (p : Where)
    (hk : shapeOk (k13Shape p.lin.kCol) = true)
    (φ : Face (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Pb) {bs : List (Block S Cl)}
    {fs : List (Fall S)} {σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    (hσ : Side.seated bs (k13Place p) (k13Pairs weights pile p) fs = some σ)
    (hr : σ.block.rounds = battRounds p)
    (ho : σ.block.oracles = List.replicate (2 + p.lin.kCol) [])
    (hw : Bk.word F = none) (hp : F.placesOk = true) (ha : k13Place p ∈ placesAt F 0)
    (hd : ∀ j, j < 2 → dueAt (Bk.rowsOf 0) ⟨k13Place p, j⟩ = ⟨0, 0⟩)
    (ord : List Place) (chain firstTree : Nat) :
    Good pre φ σ Bk ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False) k13On
      k13Bud where
  fits := fits_field weights pile p σ (sideSeated_row hσ) (sideSeated_place hσ) hr ho
  plays := fun _ _ _ _ _ hA => hA.elim
  acc := fun _ _ _ _ _ hA => hA.elim
  exact := fun u hu => exactAt_of_exact pre
    (k13_exactMember weights pile p hk φ σ (sideSeated_row hσ) hr ho chain firstTree k13On k13Bud
      u hu)
  fresh := fun u hu => freshMember_in_chain hw hp (Or.inl rfl) φ σ
    (by rw [sideSeated_place hσ]; exact ha) ord k13Bud u
    (by
      rw [sideSeated_place hσ]
      exact hd u.number (k13_numbers weights pile p σ (sideSeated_row hσ) hr ho u hu))

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13_bud
#print axioms ProofFile.Honest.K13.k13_takes
#print axioms ProofFile.Honest.K13.fits_field
#print axioms ProofFile.Honest.K13.k13_numbers
#print axioms ProofFile.Honest.K13.k13_no_send_seed
#print axioms ProofFile.Honest.K13.sideSeated_row
#print axioms ProofFile.Honest.K13.sideSeated_place
#print axioms ProofFile.Honest.K13.sideSeated_mem
#print axioms ProofFile.Honest.K13.k13_good_of_due
