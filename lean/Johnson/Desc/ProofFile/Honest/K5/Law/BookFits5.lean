-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/BookFits5.lean: conditional: THE WHOLE BOOK OF COINS PASSES THE
KIND K5's TEST ON THE BOOK (`bookFits`, Plays.lean in this folder; K5: the attention sub-protocol's
own rounds) AT THE KIND's MEMBER: the book's cut at the place is the row's; the book's table for the
first chain has no row, and the book no entry, for a part beyond the row's. General in the
description first; then under the library's head, at the book of the prover that the maker `onlineProverFromPublicFiles`
returns, at each of the twelve groups. Statements with their proofs; no definition; nothing is
evaluated.

  `units_cons`, `units_walk`   along the verifier's script the book's maker cuts the names of the
                     rounds as the row's shapes count their rounds: no premise but the maker's fuel
  `k5_partsCut`      **the maker's cut at the member is the row's cut** (`partsCut`,
                     Honest/BookOf.lean; `H2K5.Honest.cut`, Johnson/Desc/K5/Honest/Faces.lean):
                     CONDITIONAL: the member stands at a place of the kind, with the plan's rounds
  `entriesOf_ne`, `k5_rounds_ne`   the kind's table of rounds is not empty: no premise
  `k5_bookFits_of_whole`  CONDITIONAL: hB: `bookWhole F p0 p1 p2 M = .ok B`; hp: the description's
                     test on its places accepts; the member stands in the first chain's list, at the
                     seat's place, with the plan's rounds; the plan's numbers are the seat's
  `k5_bookFits_at_maker`  CONDITIONAL: h: the library's head (`P5J.AtMgA`); g is below 12; hA: the
                     maker returns A at a filling P, P a letter; a is the plan of group g; the
                     seat's reader of the key points is a letter too

What it is for. `k5_steps_return` (Plays.lean) has "`chainSteps` returns at the member" from
`K5Seated`, this test and "`lendRow` lends the row its coins". This file pays the test at the
maker's book.

By. The cut in the book: `bookWhole_cut_first` (Honest/Small/CutOfBook.lean). No row, no entry
beyond: `bookWhole_tests_at` (Honest/Small/StepsOfBook.lean), at `k5_no_seed`, `k5_no_fold`
(StatedK5.lean). What this file adds to these two is the right side of the test on the cut. The
member: `k5_member` (Member.lean). The maker's book:
`parts_of_atPure` (ReturnsOf.lean).

Limits. Implications: that the book's maker returns, that `onlineProverFromPublicFiles` returns, and the head are
premises here. A test on public data: names of rounds, places, counts. Nothing on what the book
lends, on `lendRow`, or on whether a run reaches the member. The maker reads names: a round under
another name is cut otherwise. The full size and the earlier hash `OnBytes.secondHashFunction` in the last
theorem alone. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Small.StepsOfBook
import Johnson.Desc.ProofFile.Honest.Small.CutOfBook
import Johnson.Desc.ProofFile.Honest.K5.Law.StatedK5
import Johnson.Desc.ProofFile.Honest.K5.Law.SeatReturns
import Johnson.Desc.ProofFile.Honest.K5.Law.ReturnsOf
import Johnson.RunOne.Sound.KeyListsAtFK

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block FileDescription Place Chain)
open VerifiableInference.Desc.Part (MaskedSum.Var MaskedSum.Ends MaskedSum.entries MaskedSum.entry)
open VerifiableInference.Desc.First.Att.P (Par rounds Stage script entriesOf)
open H2K5.Honest (PartShape shapes shapesOf)
open P5J (AtMgA TS)

/-! ## 1 The maker's cut along the script -/

/-- One unit off the head of the list of names. -/
theorem units_cons (c : String) (u ns2 : List String) (K : Nat)
    (hu : unitLen ((c :: u) ++ ns2) = (c :: u).length) :
    unitsOf (K + 1) ((c :: u) ++ ns2) = (c :: u).length :: unitsOf K ns2 := by
  show unitLen ((c :: u) ++ ns2) ::
    unitsOf K (((c :: u) ++ ns2).drop (unitLen ((c :: u) ++ ns2))) = _
  rw [hu, List.drop_left]

/-- **ALONG THE SCRIPT THE MAKER's UNITS ARE THE SHAPES' NUMBERS OF ROUNDS.** CONDITIONAL: K, the
fuel of the maker's cut, is no less than the number of entries. -/
theorem units_walk : ∀ (l : List Stage) (lead K : Nat), (entriesOf lead l).length ≤ K →
    unitsOf K ((entriesOf lead l).map (·.name)) = (shapesOf lead l).map (·.rounds)
  | [], _, K, _ => by cases K <;> rfl
  | .scalars n :: l, lead, K, hK => units_walk l (lead + n) K hK
  | .batch rows :: l, lead, K, hK => by
    cases K with
    | zero => exact absurd hK (Nat.not_succ_le_zero _)
    | succ K =>
      have ih := units_walk l 0 K (Nat.le_of_succ_le_succ hK)
      have hu : unitLen (("BAT-sigma" :: []) ++ (entriesOf 0 l).map (·.name)) =
          ("BAT-sigma" :: ([] : List String)).length := by simp [unitLen]
      show unitsOf (K + 1) (("BAT-sigma" :: []) ++ (entriesOf 0 l).map (·.name)) =
        1 :: (shapesOf 0 l).map (·.rounds)
      rw [units_cons "BAT-sigma" [] _ K hu, ih]
      rfl
  | .point n :: l, lead, K, hK => by
    cases K with
    | zero => exact absurd hK (Nat.not_succ_le_zero _)
    | succ K =>
      have ih := units_walk l 0 K (Nat.le_of_succ_le_succ hK)
      have hu : unitLen (("ZERO" :: []) ++ (entriesOf 0 l).map (·.name)) =
          ("ZERO" :: ([] : List String)).length := by simp [unitLen]
      show unitsOf (K + 1) (("ZERO" :: []) ++ (entriesOf 0 l).map (·.name)) =
        1 :: (shapesOf 0 l).map (·.rounds)
      rw [units_cons "ZERO" [] _ K hu, ih]
      rfl
  | .sum vs e :: l, lead, K, hK => by
    have hlen : (entriesOf lead (.sum vs e :: l)).length =
        (vs.length + 3) + (entriesOf 0 l).length := by
      show (MaskedSum.entries ⟨lead, vs, some e⟩ ++ entriesOf 0 l).length = _
      rw [List.length_append]
      simp [MaskedSum.entries]
    cases K with
    | zero =>
      rw [hlen] at hK
      omega
    | succ K =>
      have ih := units_walk l 0 K (by rw [hlen] at hK; omega)
      have hu : unitLen (("PSC epsilon" :: ((vs.map fun _ => "PSC round") ++
          ["PSC Y", "PSC values"])) ++ (entriesOf 0 l).map (·.name)) =
          ("PSC epsilon" :: ((vs.map fun _ : MaskedSum.Var => "PSC round") ++
            ["PSC Y", "PSC values"])).length := by
        have e2 : (("PSC epsilon" :: ((vs.map fun _ : MaskedSum.Var => "PSC round") ++
            ["PSC Y", "PSC values"])) ++ (entriesOf 0 l).map (·.name)) =
            "PSC epsilon" :: ((vs.map fun _ : MaskedSum.Var => "PSC round") ++
              "PSC Y" :: "PSC values" :: (entriesOf 0 l).map (·.name)) := by simp
        rw [e2, unitLen_sum]
        simp
      show unitsOf (K + 1) ((MaskedSum.entries ⟨lead, vs, some e⟩ ++ entriesOf 0 l).map (·.name)) =
        (vs.length + 3) :: (shapesOf 0 l).map (·.rounds)
      rw [List.map_append, entries_names, units_cons "PSC epsilon" _ _ K hu, ih]
      simp

/-- **THE MAKER's CUT AT K5's MEMBER IS THE ROW's CUT.** CONDITIONAL: the member stands at a place
of the kind K5; its rounds are the plan's. -/
theorem k5_partsCut {S Cl : Type} (blk : Block S Cl) (p : Par) (hk : blk.place.kind = .K5)
    (hr : blk.rounds = rounds p) : partsCut blk = H2K5.Honest.cut p.own := by
  unfold partsCut
  rw [hk, hr, rounds_names, cutOfNames_K5]
  exact units_walk (script p.own) 0 _ (by rw [List.length_map])

/-! ## 2 The kind's table of rounds is not empty -/

/-- A list of stages that holds a batching has an entry. -/
theorem entriesOf_ne : ∀ (l : List Stage) (lead rows : Nat), Stage.batch rows ∈ l →
    entriesOf lead l ≠ []
  | [], _, _, h => by cases h
  | .scalars n :: l, lead, rows, h => by
    rcases List.mem_cons.1 h with h | h
    · cases h
    · exact entriesOf_ne l (lead + n) rows h
  | .batch _ :: l, lead, rows, _ => List.cons_ne_nil _ _
  | .point _ :: l, lead, rows, _ => List.cons_ne_nil _ _
  | .sum vs e :: l, lead, rows, _ => by
    intro h0
    have h1 : MaskedSum.entries ⟨lead, vs, some e⟩ ++ entriesOf 0 l = [] := h0
    have h2 := congrArg (List.map (·.name)) (List.append_eq_nil_iff.1 h1).1
    rw [entries_names] at h2
    cases h2

/-- **The kind's table of rounds is not empty.** No premise. -/
theorem k5_rounds_ne (p : Par) : rounds p ≠ [] := by
  intro h0
  have h1 : (entriesOf 0 (script p.own)).map (·.name) = [] := by
    rw [← rounds_names, h0]
    rfl
  have hm : Stage.batch 2 ∈ script p.own := by
    unfold script
    dsimp only
    refine List.mem_append_right _ ?_
    iterate 4 apply List.mem_cons_of_mem
    exact List.mem_cons_self ..
  exact entriesOf_ne (script p.own) 0 2 hm (List.map_eq_nil_iff.1 h1)

/-! ## 3 The test on the book -/

/-- **THE WHOLE BOOK PASSES K5's TEST AT K5's MEMBER.** CONDITIONAL: hB: the book's maker returns B;
hp: the description's test on its places accepts; hb: the member stands in the first chain's list;
hpl: at the seat's place; hr: its rounds are the plan's; hx: the plan's numbers are the seat's. -/
theorem k5_bookFits_of_whole {Xi : Type} {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends}
    {M : Merges} {B : ProverCoinCounts} (hB : bookWhole F p0 p1 p2 M = .ok B) (hp : F.placesOk = true)
    {blk : Block F.S₁ F.Cl} (hb : blk ∈ F.first.blocksInOrder) (p : Par) (Z : Seat5)
    (hpl : blk.place = Z.place) (hr : blk.rounds = rounds p) (hx : p.own = Z.P.x) :
    bookFits B (B.rowsOf 0) Z = true := by
  have hk : blk.place.kind = .K5 := by rw [hpl]; rfl
  have hs := k5_no_seed blk p hr
  have hf := k5_no_fold blk p hr
  have hc := k5_partsCut blk p hk hr
  have c1 : B.cuts.lookup Z.place = some (H2K5.Honest.cut Z.P.x) := by
    rw [← hpl, ← hx, ← hc]
    exact bookWhole_cut_first hB hp hb (by rw [hr]; exact k5_rounds_ne p)
  have hl : (partsCut blk).length ≤ (shapes Z.P.x).length := by
    rw [hc, hx]
    exact Nat.le_of_eq (List.length_map _)
  obtain ⟨c2, c3⟩ := bookWhole_tests_at hB hp hb hs hf hl
  rw [hpl] at c2 c3
  unfold bookFits
  rw [c1, c2, c3]
  simp

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **UNDER THE HEAD THE MAKER's BOOK PASSES K5's TEST AT EACH OF THE TWELVE GROUPS.** CONDITIONAL:
h; g is below 12; hA: the maker returns A at a filling P; a is the plan of group g. General in the
filling's types and in the seat's reader keyOf of the key points, which the test does not read. -/
theorem k5_bookFits_at_maker (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : Nat} (hg : g < 12)
    {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) {a : OnBytes.Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a)
    {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array OnBytes.E)} :
    bookFits A.B (A.B.rowsOf 0) (seatOf keyOf Zp A.G cF g a) = true := by
  obtain ⟨m, -⟩ := parts_of_atPure hA
  have eF : A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF := Except.ok.inj (m.desc.symm.trans h.laid.value)
  obtain ⟨_, _, _, _, p0, p1, p2, -, hB⟩ := m.book
  rw [eF] at hB
  have hp : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).placesOk = true :=
    Johnson.RunOne.Sound.placesOk_of_planOk _ h.laid.planOk
  obtain ⟨blk, a', hm, Pl, Dc⟩ := k5_member h hg
  obtain rfl : a' = a := Option.some.inj (Pl.plan.symm.trans ha)
  have hb : blk ∈ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder := List.mem_of_getElem? hm
  exact k5_bookFits_of_whole hB hp hb (parAt Zp g a') (seatOf keyOf Zp A.G cF g a') Dc.place
    Dc.rounds rfl

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.units_cons
#print axioms ProofFile.Honest.K5.units_walk
#print axioms ProofFile.Honest.K5.k5_partsCut
#print axioms ProofFile.Honest.K5.entriesOf_ne
#print axioms ProofFile.Honest.K5.k5_rounds_ne
#print axioms ProofFile.Honest.K5.k5_bookFits_of_whole
#print axioms ProofFile.Honest.K5.k5_bookFits_at_maker
