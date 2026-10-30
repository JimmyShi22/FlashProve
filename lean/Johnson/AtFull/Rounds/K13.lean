-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rounds/K13.lean: THE DECLARED ROUNDS OF THE SUB-PROTOCOLS OF K13's THREE LOTS
(K13.lot · K13.lot4 · K13.lotEnd: Johnson/Desc/ProofFile/Lot/K13.lean · K13At4.lean · K13End.lean)
ARE THE WRITTEN LISTS UNDER THE WRITTEN NAMES AT THEIR PLACES ("M:3" · "M:4" · "seal:5").
WHAT IT DOES NOT PAY. No premise of the rows is paid here: that the public part Z of the full-size
files has hw (or hc and hp), hk, hr, hcd, hl is not shown. That the places are the written ones
(B.spots = spotsW) is not shown. No example of any description is given. Nothing on soundness.
Why. A description's declared rounds are its sub-protocols' rounds in a row. ProofFile.Sk.lists_are
(Johnson/Desc/ProofFile/Law/Skel/SkelLists.lean) with ProofFile.Sk.Full.rows_by_place (…/Full/Names.lean)
asks of each block b of each lot: b has no round, or b.rounds = listAt (nameW b.place)
(Johnson/AtFull/Rounds/ListAt.lean). Here: the three lots of the first chain's end.
  LAWS, at every public part Z and every ground G, no hypothesis:
  roundsM3 rows kCol w   the members' batching's rounds off five numbers; batt_eq: K13.battRounds is
                    that, by unfolding
  worksM3 cuts plan the three numbers of proof-of-work bits that K13.whereOf reads off the plan's
                    entries at the step "M.0.call" and the two behind it; works_eq
  **m3_rounds**     the lot has one block, at ⟨1, none, 3, .K13⟩; its rounds read
                    Z.first.pendingRows · Z.first.lin.kCol · Z.cuts and Z.plans.1 (through worksM3)
  roundsM4 codes lin · **m4_rounds**   the lot has one block, at ⟨1, none, 4, .K1⟩, or none; its
                    rounds read Z.first.codes · Z.first.lin. The own group's number, the samples'
                    number and the first tree's enter no round.
  **m5_rounds**     the lot has one block, at ⟨1, none, 5, .frame⟩; its one round is the sealing
                    round: it reads nothing of Z
  CLOSED FACTS, by Lean's kernel; the three lists each with negative tests stated "= false":
  names_at          nameW at the three places; m3_works: the three numbers at the written values
  works_at          worksM3 reads at the step's own offset: on a small table of steps
  m3_list · m3_bent · m4_list · m4_bent · m5_list · m5_bent
  THE ROWS:
  **lot_seen · lot4_seen · lotEnd_seen**   the lot's blocks are ONE, at this place, with this list
  lot_rounds · lot4_rounds · lotEnd_rounds   the same, block by block
  **lot_lst · lot4_lst · lotEnd_lst**   in the form that rows_by_place takes; three_lst: all three
                    (its hk is had from hl by the first rows' closed fact m3_written)
  works_of_written  hw from hc and hp · works_of_first: from hc, he and hE · works_of_pub: from hc,
                    he and hZ
THE HYPOTHESES, BY FIELD. hk : Z.first.lin.kCol = 18 · hr : Z.first.pendingRows = 13 ·
hcd · hl : codes and lin are proofSizedFull's: these four are the first rows' own
(Johnson/AtFull/Desc/Lots/K13LotRows.lean).
ONE HYPOTHESIS THAT THE FIRST ROWS HAVE NOT: hw : worksM3 Z.cuts Z.plans.1 = (0, 0, 0). A skeleton
holds the NUMBER of rounds; the rounds themselves hold the proof-of-work bits, which K13.whereOf
reads off the plan's entries Z.plans.1. IT CAN BE HAD FROM THE FIRST ROWS' OWN hc AND he AND THE
PUBLIC PART's RETURN: works_of_pub, under hZ : ProofFile.pubBy made st pol lay KL = .ok Z (ProofFile.pubPlain is
that, by unfolding): the entries of the public part's declared rounds are the plan's own entries
(pubBy_entries, Johnson/Goal/Numbers/PlanWrittenPlans.lean: by the public part's make alone). So no
new field of Z is asked. THE ROWS THEMSELVES take no hS, hR, hZ or hG; works_of_pub takes hZ.
The theorem plans_written of that same file is NOT called: it stands under "the value is laid".
The first rows' hg (the own group) is not wanted here; he only through hw.
cutWritten is Johnson.AtFull.Cut.cutWritten (Johnson/AtFull/Cut/CutWrittenLit.lean), as in the first
rows and in the other kinds' rows: one constant.
NOTE: As with the first rows: the hypotheses are to be paid without the entry tests' comparisons.
The recursion limit is raised (maxRecDepth 1000000) at the kernel's facts, for elaboration.

-/
import Johnson.AtFull.Rounds.ListAt
import Johnson.AtFull.Desc.Lots.K13LotRows
import Johnson.Desc.ProofFile.Law.Skel.SkelLists
import Johnson.Desc.ProofFile.Law.Skel.Full.Names
import Johnson.Goal.Numbers.PlanWrittenPlans

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Rounds.K13
open OnBytes OnBytes.Params
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.First (Cut S)
open VerifiableInference.PlanWritten (proofSizedFull)
open ProofFile (Pub Lot Ground)
open ProofFile.Sk (Lst)
open ProofFile.Sk.Full (nameW)
open Johnson.AtFull.K4Sent (esWritten)
open Johnson.AtFull.Cut (cutWritten)
open VerifiableInference.Desc.K13.LotRows (fromM3 parM4)

/-! ## What the rounds read -/

/-- The rounds of the members' batching, off the pile's rows, the columns' number and the three
numbers of proof-of-work bits. -/
def roundsM3 (rows kCol : ℕ) (w : ℕ × ℕ × ℕ) : List Fmt.DeclaredRound :=
  { entry := { name := "BAT-sigma", work := w.1, drawE := 1, rows := rows } } ::
    { entry := { name := "PSC epsilon", work := w.2.1, msg := 24, drawE := 1 } } ::
      List.replicate kCol { entry := { name := "PSC round", work := w.2.2, msg := 48, drawE := 1 } }

/-- The kind's own rounds are these. -/
theorem batt_eq (p : VerifiableInference.Desc.K13.Where) :
    VerifiableInference.Desc.K13.battRounds p = roundsM3 p.rows p.lin.kCol p.work := rfl

/-- The proof-of-work bits of the plan's entries at the step "M.0.call" and the two behind it; 0
where the plan has no such entry: as K13.whereOf reads them. -/
def worksM3 (cuts : List Cut) (plan : List Fmt.Entry) : ℕ × ℕ × ℕ :=
  let w := fun (i : ℕ) => ((plan[fromM3 cuts + i]?).map (·.work)).getD 0
  (w 0, w 1, w 2)

theorem works_eq (Z : Pub) :
    (VerifiableInference.Desc.K13.whereOf Z).work = worksM3 Z.cuts Z.plans.1 := by
  unfold worksM3
  rw [← VerifiableInference.Desc.K13.LotRows.from_eq]
  rfl

/-- The rounds of W's commitment; none where the shape has no message W. -/
def roundsM4 (codes : Codes) (lin : LinShape) : Option (List Fmt.DeclaredRound) :=
  (linMessageW lin).map fun msg => VerifiableInference.Desc.K1.rounds (parM4 codes 0 msg)

/-- A block's place and its rounds. -/
def seen (b : Block S ProofFile.Cl) : Place × List Fmt.DeclaredRound := (b.place, b.rounds)

/-- From the list of what is seen to each block. -/
theorem of_seen {bs : List (Block S ProofFile.Cl)} {a : Place} {r : List Fmt.DeclaredRound}
    (h : bs.map seen = [(a, r)]) : ∀ b ∈ bs, b.place = a ∧ b.rounds = r := by
  intro b hb
  have hm : seen b ∈ bs.map seen := List.mem_map_of_mem hb
  rw [h, List.mem_singleton] at hm
  exact ⟨congrArg Prod.fst hm, congrArg Prod.snd hm⟩

/-! ## The laws: at every public part and every ground -/

/-- **The members' batching.** -/
theorem m3_rounds (Z : Pub) (G : Ground) :
    ((VerifiableInference.Desc.K13.lot Z).blocks G).map seen =
      [(⟨1, none, 3, .K13⟩,
        roundsM3 Z.first.pendingRows Z.first.lin.kCol (worksM3 Z.cuts Z.plans.1))] := by
  rw [← works_eq]
  show [((⟨1, none, 3, .K13⟩ : Place), ([] ++ VerifiableInference.Desc.K13.battRounds
    (VerifiableInference.Desc.K13.whereOf Z)) ++ [])] = _
  rw [List.nil_append, List.append_nil, batt_eq]
  rfl

/-- **W's commitment, the own group and (Eval).** -/
theorem m4_rounds (Z : Pub) (G : Ground) :
    ((VerifiableInference.Desc.K13.lot4 Z).blocks G).map seen =
      ((roundsM4 Z.first.codes Z.first.lin).map fun r =>
        ((⟨1, none, 4, .K1⟩ : Place), r)).toList := by
  have e : (VerifiableInference.Desc.K13.lot4 Z).blocks G =
      ((VerifiableInference.Desc.K13.wBlock Z).toList.map
        (VerifiableInference.Desc.K13.atM4 (VerifiableInference.Desc.K13.whereOf Z))).map
          (fun b => b.retype) ++ [] := rfl
  rw [e, List.append_nil]
  unfold VerifiableInference.Desc.K13.wBlock VerifiableInference.Desc.K1.wAt roundsM4
  cases linMessageW Z.first.lin with
  | none => rfl
  | some msg =>
    show [((⟨1, none, 4, .K1⟩ : Place), VerifiableInference.Desc.K1.rounds _ ++ [])] = [_]
    rw [List.append_nil]
    rfl

/-- **The first chain's end.** -/
theorem m5_rounds (Z : Pub) (G : Ground) :
    ((VerifiableInference.Desc.K13.lotEnd Z).blocks G).map seen =
      [(⟨1, none, 5, .frame⟩, [VerifiableInference.Desc.ChainEnd.sealRound])] := rfl

/-! ## The closed facts, by Lean's kernel -/

set_option maxRecDepth 1000000 in
/-- The written names at the three places; and a place that no written spot has bears the empty
name. -/
theorem names_at : nameW ⟨1, none, 3, .K13⟩ = "M:3" ∧ nameW ⟨1, none, 4, .K1⟩ = "M:4" ∧
    nameW ⟨1, none, 5, .frame⟩ = "seal:5" ∧ nameW ⟨1, none, 6, .frame⟩ = "" :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 1000000 in
/-- The three numbers at the written values; the three entries are there (so no 0 is the idle one of
an absent entry) and bear the three rounds' names. -/
theorem m3_works : worksM3 cutWritten esWritten = (0, 0, 0) ∧ fromM3 cutWritten = 48270 ∧
    ((List.range 3).map fun i => (esWritten[48270 + i]?).map (·.name)) =
      [some "BAT-sigma", some "PSC epsilon", some "PSC round"] :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **worksM3 reads at the step's own offset.** A small table: one round in front of the step
"M.0.call". A bit of work on the entry in front and on the entry behind the three is not seen; on
the first, the second, the third of the three it is seen, each at its own seat. -/
theorem works_at :
    worksM3 [⟨"x", "", 0, "", 1⟩, ⟨"M.0.call", "", 0, "", 3⟩] [{ name := "a", work := 1 },
      { name := "b" }, { name := "c" }, { name := "d" }, { name := "e", work := 1 }] = (0, 0, 0) ∧
    worksM3 [⟨"x", "", 0, "", 1⟩, ⟨"M.0.call", "", 0, "", 3⟩] [{ name := "a" },
      { name := "b", work := 1 }, { name := "c", work := 2 }, { name := "d", work := 3 },
      { name := "e" }] = (1, 2, 3) :=
  ⟨by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 1000000 in
/-- **The members' batching at the written values**: twenty rounds. -/
theorem m3_list : roundsM3 13 18 (0, 0, 0) = listAt "M:3" ∧ (listAt "M:3").length = 20 :=
  ⟨by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 1000000 in
/-- **Negative tests.** Each alters a member and keeps the length, but for the fifth: one row fewer
in the pile (the first round) · a bit of work on the first, on the second, on each later round · one
column fewer · worksM3 sees a bit of work on the third entry. -/
theorem m3_bent :
    decide (roundsM3 12 18 (0, 0, 0) = listAt "M:3") = false ∧
    decide (roundsM3 13 18 (1, 0, 0) = listAt "M:3") = false ∧
    decide (roundsM3 13 18 (0, 1, 0) = listAt "M:3") = false ∧
    decide (roundsM3 13 18 (0, 0, 1) = listAt "M:3") = false ∧
    decide (roundsM3 13 17 (0, 0, 0) = listAt "M:3") = false ∧
    decide (worksM3 [⟨"M.0.call", "", 0, "", 3⟩]
      [{ name := "a" }, { name := "b" }, { name := "c", work := 1 }] = (0, 0, 0)) = false :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

set_option maxRecDepth 1000000 in
/-- **W's commitment at the written values**: the shape has a message W; two rounds. -/
theorem m4_list : roundsM4 proofSizedFull.codes proofSizedFull.batch.shape = some (listAt "M:4") ∧
    (listAt "M:4").length = 2 :=
  ⟨by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 1000000 in
/-- **Negative tests.** Against the written list of another commitment, of two rounds too, whose
second round is the same (so the first differs) · at a shape whose W has one answer more to its
out-of-domain sample: that what it returns is not the written list is all that is stated of it. -/
theorem m4_bent :
    decide (roundsM4 proofSizedFull.codes proofSizedFull.batch.shape = some (listAt "G0:4")) =
      false ∧ (listAt "G0:4").length = 2 ∧ (listAt "G0:4")[1]? = (listAt "M:4")[1]? ∧
    decide (roundsM4 proofSizedFull.codes { proofSizedFull.batch.shape with
      w := { proofSizedFull.batch.shape.w with
        answers := proofSizedFull.batch.shape.w.answers + 1 } } = some (listAt "M:4")) = false :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 1000000 in
/-- **The end at the written values**: one round. -/
theorem m5_list : [VerifiableInference.Desc.ChainEnd.sealRound] = listAt "seal:5" := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **Negative tests.** A sealing round that owes a row · against another written list of one
round. -/
theorem m5_bent :
    decide ([({ entry := { name := "SEAL", rows := 1 } } : Fmt.DeclaredRound)] = listAt "seal:5") =
      false ∧
    decide ([VerifiableInference.Desc.ChainEnd.sealRound] = listAt "G0:5") = false ∧
    (listAt "G0:5").length = 1 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ## The rows -/

/-- hw, from the first rows' hc and the plan's entries as written. -/
theorem works_of_written {Z : Pub} (hc : Z.cuts = cutWritten) (hp : Z.plans.1 = esWritten) :
    worksM3 Z.cuts Z.plans.1 = (0, 0, 0) := by
  rw [hc, hp]
  exact m3_works.1

/-- hw, from the first rows' hc and he, where the entries of the declared rounds are the plan's. -/
theorem works_of_first {Z : Pub} (hE : Z.D.1.map (·.entry) = Z.plans.1) (hc : Z.cuts = cutWritten)
    (he : Z.D.1.map (·.entry) = esWritten) : worksM3 Z.cuts Z.plans.1 = (0, 0, 0) :=
  works_of_written hc (hE.symm.trans he)

/-- **hw, from the first rows' hc and he and the public part's return.** -/
theorem works_of_pub
    {made : ByteArray → ByteArray → ByteArray → Except String Johnson.G.OfPlan.Made}
    {st : ProofFile.Starts} {pol lay KL : ByteArray} {Z : Pub}
    (hZ : ProofFile.pubBy made st pol lay KL = .ok Z) (hc : Z.cuts = cutWritten)
    (he : Z.D.1.map (·.entry) = esWritten) : worksM3 Z.cuts Z.plans.1 = (0, 0, 0) :=
  works_of_first (VerifiableInference.PlanWritten.pubBy_entries hZ).1 hc he

/-- **The members' batching: the lot's blocks are one, at this place, with this list**, UNDER
THREE PREMISES: worksM3 reads (0, 0, 0) off the plan's entries (hw), 18 columns (hk), 13 rows in
the pile (hr). -/
theorem lot_seen {Z : Pub} (G : Ground) (hw : worksM3 Z.cuts Z.plans.1 = (0, 0, 0))
    (hk : Z.first.lin.kCol = 18) (hr : Z.first.pendingRows = 13) :
    ((VerifiableInference.Desc.K13.lot Z).blocks G).map seen =
      [(⟨1, none, 3, .K13⟩, listAt "M:3")] := by
  rw [m3_rounds, hw, hk, hr, m3_list.1]

/-- **W's commitment: the lot's blocks are one, at this place, with this list**, UNDER TWO
PREMISES: the codes (hcd) and the linear claims' shape (hl) are proofSizedFull's. -/
theorem lot4_seen {Z : Pub} (G : Ground) (hcd : Z.first.codes = proofSizedFull.codes)
    (hl : Z.first.lin = proofSizedFull.batch.shape) :
    ((VerifiableInference.Desc.K13.lot4 Z).blocks G).map seen =
      [(⟨1, none, 4, .K1⟩, listAt "M:4")] := by
  rw [m4_rounds, hcd, hl, m4_list.1]
  rfl

/-- **The end: the lot's blocks are one, at this place, with this list.** At every public part. -/
theorem lotEnd_seen (Z : Pub) (G : Ground) :
    ((VerifiableInference.Desc.K13.lotEnd Z).blocks G).map seen =
      [(⟨1, none, 5, .frame⟩, listAt "seal:5")] := by
  rw [m5_rounds, m5_list]

/-- The members' batching, block by block, under lot_seen's three premises (hw · hk · hr). -/
theorem lot_rounds {Z : Pub} (G : Ground) (hw : worksM3 Z.cuts Z.plans.1 = (0, 0, 0))
    (hk : Z.first.lin.kCol = 18) (hr : Z.first.pendingRows = 13) :
    ∀ b ∈ (VerifiableInference.Desc.K13.lot Z).blocks G,
      b.place = ⟨1, none, 3, .K13⟩ ∧ b.rounds = listAt "M:3" :=
  of_seen (lot_seen G hw hk hr)

/-- W's commitment, block by block, under lot4_seen's two premises (hcd · hl). -/
theorem lot4_rounds {Z : Pub} (G : Ground) (hcd : Z.first.codes = proofSizedFull.codes)
    (hl : Z.first.lin = proofSizedFull.batch.shape) :
    ∀ b ∈ (VerifiableInference.Desc.K13.lot4 Z).blocks G,
      b.place = ⟨1, none, 4, .K1⟩ ∧ b.rounds = listAt "M:4" :=
  of_seen (lot4_seen G hcd hl)

/-- The end, block by block. At every public part. -/
theorem lotEnd_rounds (Z : Pub) (G : Ground) :
    ∀ b ∈ (VerifiableInference.Desc.K13.lotEnd Z).blocks G,
      b.place = ⟨1, none, 5, .frame⟩ ∧ b.rounds = listAt "seal:5" :=
  of_seen (lotEnd_seen Z G)

/-- **The row of K13.lot**, as ProofFile.Sk.Full.rows_by_place takes it at Q := Lst listAt, UNDER
lot_seen's THREE PREMISES (hw · hk · hr). -/
theorem lot_lst {Z : Pub} (G : Ground) (hw : worksM3 Z.cuts Z.plans.1 = (0, 0, 0))
    (hk : Z.first.lin.kCol = 18) (hr : Z.first.pendingRows = 13) :
    ∀ b ∈ (VerifiableInference.Desc.K13.lot Z).blocks G, Lst listAt (nameW b.place) b.rounds := by
  intro b hb
  obtain ⟨h1, h2⟩ := lot_rounds G hw hk hr b hb
  rw [h1, names_at.1]
  exact Or.inr h2

/-- **The row of K13.lot4**, UNDER lot4_seen's TWO PREMISES (hcd · hl). -/
theorem lot4_lst {Z : Pub} (G : Ground) (hcd : Z.first.codes = proofSizedFull.codes)
    (hl : Z.first.lin = proofSizedFull.batch.shape) :
    ∀ b ∈ (VerifiableInference.Desc.K13.lot4 Z).blocks G, Lst listAt (nameW b.place) b.rounds := by
  intro b hb
  obtain ⟨h1, h2⟩ := lot4_rounds G hcd hl b hb
  rw [h1, names_at.2.1]
  exact Or.inr h2

/-- **The row of K13.lotEnd.** At every public part. -/
theorem lotEnd_lst (Z : Pub) (G : Ground) :
    ∀ b ∈ (VerifiableInference.Desc.K13.lotEnd Z).blocks G,
      Lst listAt (nameW b.place) b.rounds := by
  intro b hb
  obtain ⟨h1, h2⟩ := lotEnd_rounds Z G b hb
  rw [h1, names_at.2.2.1]
  exact Or.inr h2

/-- **All three**, UNDER FOUR PREMISES: hw · hr · hcd · hl. The number of columns (hk) is had from
hl by the first rows' closed fact. -/
theorem three_lst {Z : Pub} (G : Ground) (hw : worksM3 Z.cuts Z.plans.1 = (0, 0, 0))
    (hr : Z.first.pendingRows = 13) (hcd : Z.first.codes = proofSizedFull.codes)
    (hl : Z.first.lin = proofSizedFull.batch.shape) :
    ∀ L ∈ [VerifiableInference.Desc.K13.lot Z, VerifiableInference.Desc.K13.lot4 Z,
        VerifiableInference.Desc.K13.lotEnd Z],
      ∀ b ∈ L.blocks G, Lst listAt (nameW b.place) b.rounds := by
  have hk : Z.first.lin.kCol = 18 := by
    rw [hl]
    exact VerifiableInference.Desc.K13.LotRows.m3_written.2.2.1
  intro L hL
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with rfl | rfl | rfl
  · exact lot_lst G hw hk hr
  · exact lot4_lst G hcd hl
  · exact lotEnd_lst Z G

end Johnson.AtFull.Rounds.K13

#print axioms Johnson.AtFull.Rounds.K13.batt_eq
#print axioms Johnson.AtFull.Rounds.K13.works_eq
#print axioms Johnson.AtFull.Rounds.K13.of_seen
#print axioms Johnson.AtFull.Rounds.K13.m3_rounds
#print axioms Johnson.AtFull.Rounds.K13.m4_rounds
#print axioms Johnson.AtFull.Rounds.K13.m5_rounds
#print axioms Johnson.AtFull.Rounds.K13.names_at
#print axioms Johnson.AtFull.Rounds.K13.m3_works
#print axioms Johnson.AtFull.Rounds.K13.works_at
#print axioms Johnson.AtFull.Rounds.K13.m3_list
#print axioms Johnson.AtFull.Rounds.K13.m3_bent
#print axioms Johnson.AtFull.Rounds.K13.m4_list
#print axioms Johnson.AtFull.Rounds.K13.m4_bent
#print axioms Johnson.AtFull.Rounds.K13.m5_list
#print axioms Johnson.AtFull.Rounds.K13.m5_bent
#print axioms Johnson.AtFull.Rounds.K13.works_of_written
#print axioms Johnson.AtFull.Rounds.K13.works_of_first
#print axioms Johnson.AtFull.Rounds.K13.works_of_pub
#print axioms Johnson.AtFull.Rounds.K13.lot_seen
#print axioms Johnson.AtFull.Rounds.K13.lot4_seen
#print axioms Johnson.AtFull.Rounds.K13.lotEnd_seen
#print axioms Johnson.AtFull.Rounds.K13.lot_rounds
#print axioms Johnson.AtFull.Rounds.K13.lot4_rounds
#print axioms Johnson.AtFull.Rounds.K13.lotEnd_rounds
#print axioms Johnson.AtFull.Rounds.K13.lot_lst
#print axioms Johnson.AtFull.Rounds.K13.lot4_lst
#print axioms Johnson.AtFull.Rounds.K13.lotEnd_lst
#print axioms Johnson.AtFull.Rounds.K13.three_lst
