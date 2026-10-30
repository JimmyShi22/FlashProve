-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/Proofs.lean: the proofs of `HeadMergePlays`,
`HeadMergeAlone` and `HeadMergeNoRead` (Honest/K11/Plays/Statement.lean), to the letter. Lemmas;
none of the library's goals.

How. The row's rounds are cut between its two parts (`rowSteps`, Honest/Frame.lean), and `play` goes
through a cut (`play_append`, Honest/Law/Play.lean). The first part's one round: a part without a
stop whose message fits is played as it says (`play_steps_whole`, Honest/SumLaw/PlaysWhole.lean).
The second part is the lifted `sumPart`: `plays_unit_sumPart` (Honest/SumLaw/PlaysSum.lean), whose
premises are paid here: the declared rounds state the call's scalars (`statedBy_like`,
Honest/SumLaw/Fits.lean), and the challenges are as many as the moves (`drawsFit_length`,
Honest/Law/Along.lean; `sumGs_count`, Honest/SumLaw/Counts.lean). Played alone: `alone_sumPart`
(Honest/SumLaw/Out.lean). No table, no column: `tablesOf_said`, `fillCols_none`
(Honest/SumLaw/PlaysSum.lean, LiftSame.lean).

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.Statement
import Johnson.Desc.ProofFile.Honest.SumLaw.LiftSame
import Johnson.Desc.ProofFile.Honest.Law.Along

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Model (WsClaim RoundName)
open VerifiableInference.Desc (Block OpenedColumn Oracle)
open VerifiableInference.Desc.Part.MaskedSum (entries)
open Johnson.Desc.First.ForkMerge (HeadMergeP mergeEntries)
open ProofFile.Honest.SumLaw (alone SumCoins sumOut saidPlayed sumGs sumGs_count lift_moves_count
  statedBy_like StatedBy play_steps_whole plays_unit_sumPart alone_sumPart tablesOf_said
  fillCols_none roundsOf_said)

/-- Declared rounds beside as many empty lists of oracle messages. -/
theorem zip_none {α : Type} (f : α → Fmt.DeclaredRound) : ∀ (l : List α),
    (l.map f).zip (List.replicate l.length ([] : List Oracle)) = l.map fun e => (f e, [])
  | [] => rfl
  | e :: l => by
    show (f e, []) :: ((l.map f).zip (List.replicate l.length [])) = _
    rw [zip_none f l]
    rfl

/-- The merge has lk + 4 rounds. -/
theorem mergeEntries_length (lk n work : Nat) : (mergeEntries lk n work).length = lk + 4 := by
  simp [mergeEntries]

/-- The sumcheck's entries among the merge's. -/
def sumEntries (lk work : Nat) : List Fmt.Entry := (mergeEntries lk 1 work).tail

/-- They state the bytes, answers and roots of the call's own entries. -/
theorem sumEntries_like (lk work : Nat) :
    ((sumEntries lk work).map fun e => (({ entry := e }, []) : Fmt.DeclaredRound × List Oracle)).map
        (fun r => (r.1.entry.msg, r.1.entry.answers, r.1.entry.roots)) =
      (entries (headMergeShape lk)).map fun e => (e.msg, e.answers, e.roots) := by
  simp [sumEntries, mergeEntries, entries, headMergeShape,
    VerifiableInference.Desc.Part.MaskedSum.entry, List.map_replicate]
  exact Or.inr rfl

/-- As many challenges as the sumcheck's part has moves. -/
theorem draws_count (lk work : Nat) (n₁ n₂ : String) (lay : OnBytes.Model.WsLay) (hl : lay.lk = lk)
    (d₀ : Fmt.Drawn) (ds : List Fmt.Drawn)
    (h : drawsFit ((mergeEntries lk 1 work).map fun e => { entry := e }) (d₀ :: ds) = true) :
    ds.length = (sumGs n₁ n₂ (headMergeJob lay)).length := by
  have a := drawsFit_length _ _ h
  rw [List.length_map, mergeEntries_length, List.length_cons] at a
  rw [sumGs_count]
  show ds.length = (List.replicate lay.lk _).length + 3
  rw [List.length_replicate, hl]
  omega

/-- **The sumcheck's rounds are those of the part played alone.** -/
theorem headMergeAlone : HeadMergeAlone := by
  intro W₀ Rc Xi Tr X P claims weights c d₀ ds m h
  exact alone_sumPart _ _ (headMergeJob P.lay) c _ _ ds
    (draws_count P.lay.lk P.work _ _ P.lay rfl d₀ ds h)

/-- **The row's rounds send no table and read no column.** -/
theorem headMergeNoRead : HeadMergeNoRead := by
  intro P name a d₀ out chain firstTree stored tree ds back
  refine ⟨tablesOf_said name ⟨a, 1⟩ out, fillCols_none chain firstTree stored tree _ ds ?_ back⟩
  intro r hr
  obtain ⟨e, _, rfl⟩ := List.mem_map.1 hr
  exact ⟨rfl, rfl⟩

/-- **The row is played**: what `play` returns, whole. -/
theorem headMergePlays : HeadMergePlays := by
  intro W₀ Rc Xi Tr X S Cl blk P claims weights v q c d₀ ds back m hr ho hd
  rw [hr] at hd
  have hl := draws_count P.lay.lk P.work (runName maskRowRun ⟨headMergePlace P, 1⟩ "sum")
    (runName indexMaskRun ⟨headMergePlace P, 1⟩ "ends") P.lay rfl d₀ ds hd
  have hz : blk.rounds.zip blk.oracles =
      (mergeEntries P.lay.lk 1 P.work).map fun e => (({ entry := e } : Fmt.DeclaredRound), []) := by
    rw [hr, ho, ← mergeEntries_length P.lay.lk 1 P.work]
    exact zip_none _ _
  have hsplit : (mergeEntries P.lay.lk 1 P.work).map
        (fun e => ((({ entry := e } : Fmt.DeclaredRound), []) : Fmt.DeclaredRound × List Oracle)) =
      ({ entry := { name := RoundName.batSigma.name, work := P.work, drawE := 1, rows := 1 } },
          []) ::
        (sumEntries P.lay.lk P.work).map fun e => ({ entry := e }, []) := rfl
  have hlen : ((sumEntries P.lay.lk P.work).map
      fun e => ((({ entry := e } : Fmt.DeclaredRound), []) : Fmt.DeclaredRound × List Oracle)).length =
      P.lay.lk + 3 := by
    have := mergeEntries_length P.lay.lk 1 P.work
    simp only [sumEntries, List.length_map, List.length_tail]
    omega
  have hmv : (headMergeSum (Rc := Rc) (Tr := Tr) (X := X) P claims weights).moves.length =
      P.lay.lk + 3 := by
    show ((sumPart (V := Unit) _ _ (headMergeJob P.lay)).lift _ _ _ _).moves.length = _
    rw [lift_moves_count]
    show (List.replicate P.lay.lk _).length + 3 = _
    rw [List.length_replicate]
  have hst : StatedBy (scalarsOf (headMergeJob P.lay).shape)
      ((sumEntries P.lay.lk P.work).map fun e => ({ entry := e }, [])) :=
    statedBy_like (headMergeShape P.lay.lk) _ (sumEntries_like P.lay.lk P.work) (by
      intro r hr'
      obtain ⟨e, _, rfl⟩ := List.mem_map.1 hr'
      rfl)
  have h1 : play ((headMergeDraw (V := Local W₀ Rc Xi Tr) (W := Local W₀ Rc Xi Tr) (X := X)).steps
      blk.name ⟨blk.place, 0⟩
      [({ entry := { name := RoundName.batSigma.name, work := P.work, drawE := 1, rows := 1 } },
        [])]
      v (q, (), ())) [d₀] back m =
      .ok ([⟨blk.name, blk.place, 0, true, [], [], d₀⟩],
        ⟨⟨m.st.input, m.st.heard ++ [d₀], m.st.own⟩, m.loc ++ [d₀], m.seen ++ [⟨[], d₀⟩],
          m.opened⟩) :=
    play_steps_whole _ (fun _ _ => rfl) (fun _ _ _ => rfl) blk.name ⟨blk.place, 0⟩ _ v _ [d₀] back m
      _ (by simp [SumLaw.fitsFrom, headMergeDraw, quietPart, Sending.fits, Fmt.DeclaredRound.items,
          Fmt.Entry.cut]) rfl
  have h2 := plays_unit_sumPart (X := X) (fun _ : Local W₀ Rc Xi Tr => ())
    (headMergeWit (Rc := Rc) (Tr := Tr) claims weights)
    (runName maskRowRun ⟨headMergePlace P, 1⟩ "sum")
    (runName indexMaskRun ⟨headMergePlace P, 1⟩ "ends") (headMergeJob P.lay) c
    (by
      intro w hw
      rw [(List.mem_replicate.1 hw).2]
      decide)
    blk.name ⟨blk.place, 1⟩ _ hst v ds hl (back.drop 1)
    ⟨⟨m.st.input, m.st.heard ++ [d₀], m.st.own⟩, m.loc ++ [d₀], m.seen ++ [⟨[], d₀⟩], m.opened⟩
  show play (rowSteps blk.name blk.place v
      [headMergeDraw, headMergeSum P claims weights] 0 (blk.rounds.zip blk.oracles)
      ((q, (), ()), c, ())) ([d₀] ++ ds) back m = _
  rw [hz, hsplit]
  show play (_ ++ ((headMergeSum P claims weights).steps blk.name ⟨blk.place, 1⟩
      (List.take (headMergeSum (Rc := Rc) (Tr := Tr) (X := X) P claims weights).moves.length
        ((sumEntries P.lay.lk P.work).map fun e => ({ entry := e }, []))) v c ++ []))
      ([d₀] ++ ds) back m = _
  rw [List.append_nil, hmv, List.take_of_length_le (Nat.le_of_eq hlen),
    play_append _ _ [d₀] ds back m rfl]
  erw [h1]
  show ((play _ ds (back.drop 1) _).map _) = _
  erw [h2]
  simp only [Except.map, headMergeSaid, headMergeEntry, List.tail_cons, List.append_assoc,
    List.cons_append, List.nil_append]
  rfl

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.zip_none
#print axioms ProofFile.Honest.K11.mergeEntries_length
#print axioms ProofFile.Honest.K11.sumEntries_like
#print axioms ProofFile.Honest.K11.draws_count
#print axioms ProofFile.Honest.K11.headMergeAlone
#print axioms ProofFile.Honest.K11.headMergeNoRead
#print axioms ProofFile.Honest.K11.headMergePlays
