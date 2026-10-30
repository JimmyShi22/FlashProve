-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/RowsK5.lean: CONDITIONAL: at the member of a `Thread` at which
the half of an attention segment's own rounds is seated: every row that the verifier makes of the
kind's masked sumchecks is worth 0. Definitions of propositions, and statements with their proofs.
The reading is the library's own (`Reading.gl`); the world is any.

What is joined: the kind's hearing, sumcheck by sumcheck (Honest/K5/Law/Along.lean); the rows' worth
(Honest/K5/Law/RowsAt.lean); the honest side at the member (Honest/K5/Law/AtMember.lean); "taking
the sealed digest out of the played rounds changes nothing at this member" (`k5_bare`,
Honest/K5/Law/Plays.lean).

THE MAIN STATEMENT IS CONDITIONAL ON `ValuesAt`: for each sumcheck the clauses on VALUES. NONE OF
THEM IS SHOWN HERE.
Main names:
  `summandAt_unit`, `summandAt_iSE`, `_iVM`, `_iVD`, `_iSF`, `_iSD`, `_iHB`
                     which summand stands at which part of the row
  `CoinsUnder`       the coins under a sumcheck's own slots, at what the book lends the part
  `PartVals`         the clauses on values for one part: tame; the number of end values; the coins
                     under the sumcheck's own slots; the start form's worth; the further clause
  `ValuesAt`         these for all parts that are sumchecks, at the verifier's own weights
  `honestSum_heard`  `HonestSum` at the rounds as the kind's decision is handed them
  `rows_zero_k5`     **every row is worth 0**

Limits. Nothing on the other claims of the kind. Nothing is claimed on soundness, completeness or
hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.AtMember

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes (E zeroE)
open OnBytes.Model (Reading Aff Fork World)
open OnBytes.Slice (GE)
open VerifiableInference.Desc (Block noDigest)
open VerifiableInference.Desc.Part (MaskedSum.Heard)
open VerifiableInference.Desc.Part.MaskedSum (Var Ends Call ownSlots)
open VerifiableInference.Desc.First.Att.P (Par Geo UnitG Heard Left leftP leftP_spec hear chal
  scoreW weights inner wDivision wBelow wOn wAtIndex wCells batched)
open ProofFile.Honest.SumLaw (SumCoins hidingCoin)
open H2K5.Honest (Summand K5In shapes iSE iVM iVD iSF iSD iHB keyVars sK sSE sVM sVD sSF sSD sHB)

/-! ## 1 Which summand stands at which part -/

section
variable (Z : Seat5) (w : K5In) (heard ds : List Fmt.Drawn)

/-- The row's choice of a summand, by the part's number: its text. -/
theorem jobs_sum (P : H2K5.Honest.Pub5) (q : Nat) (w : K5In) (c : H2K5.Honest.Chal) :
    (jobs P).sum q w c =
      if q < P.x.score.length then sK P w c q
      else if q == iSE P.x then sSE P w c
      else if q == iVM P.x then sVM P w c
      else if q == iVD P.x then sVD P w c
      else if q == iSF P.x then sSF P w c
      else if q == iSD P.x then sSD P w c
      else sHB P w c := rfl

theorem RowsK5.neB {a b : Nat} (h : a ≠ b) : ¬ (a == b) = true := fun e => h (beq_iff_eq.1 e)

theorem summandAt_unit {i : Nat} (h : i < Z.P.x.score.length) : summandAt Z w heard ds i =
    sK Z.P w (chalOf Z (heard ++ ds.take (H2K5.Honest.firstOf Z.P.x i))) i := by
  unfold summandAt
  rw [jobs_sum, if_pos h]

theorem summandAt_iSE : summandAt Z w heard ds (iSE Z.P.x) =
    sSE Z.P w (chalOf Z (heard ++ ds.take (H2K5.Honest.firstOf Z.P.x (iSE Z.P.x)))) := by
  unfold summandAt
  rw [jobs_sum,
    if_neg (by unfold iSE; omega),
    if_pos (beq_self_eq_true _)]

theorem summandAt_iVM : summandAt Z w heard ds (iVM Z.P.x) =
    sVM Z.P w (chalOf Z (heard ++ ds.take (H2K5.Honest.firstOf Z.P.x (iVM Z.P.x)))) := by
  unfold summandAt
  rw [jobs_sum,
    if_neg (by unfold iVM; omega),
    if_neg (RowsK5.neB (by unfold iVM iSE; omega)),
    if_pos (beq_self_eq_true _)]

theorem summandAt_iVD : summandAt Z w heard ds (iVD Z.P.x) =
    sVD Z.P w (chalOf Z (heard ++ ds.take (H2K5.Honest.firstOf Z.P.x (iVD Z.P.x)))) := by
  unfold summandAt
  rw [jobs_sum,
    if_neg (by unfold iVD; omega),
    if_neg (RowsK5.neB (by unfold iVD iSE; omega)),
    if_neg (RowsK5.neB (by unfold iVD iVM; omega)),
    if_pos (beq_self_eq_true _)]

theorem summandAt_iSF : summandAt Z w heard ds (iSF Z.P.x) =
    sSF Z.P w (chalOf Z (heard ++ ds.take (H2K5.Honest.firstOf Z.P.x (iSF Z.P.x)))) := by
  unfold summandAt
  rw [jobs_sum,
    if_neg (by unfold iSF; omega),
    if_neg (RowsK5.neB (by unfold iSF iSE; omega)),
    if_neg (RowsK5.neB (by unfold iSF iVM; omega)),
    if_neg (RowsK5.neB (by unfold iSF iVD; omega)),
    if_pos (beq_self_eq_true _)]

theorem summandAt_iSD : summandAt Z w heard ds (iSD Z.P.x) =
    sSD Z.P w (chalOf Z (heard ++ ds.take (H2K5.Honest.firstOf Z.P.x (iSD Z.P.x)))) := by
  unfold summandAt
  rw [jobs_sum,
    if_neg (by unfold iSD; omega),
    if_neg (RowsK5.neB (by unfold iSD iSE; omega)),
    if_neg (RowsK5.neB (by unfold iSD iVM; omega)),
    if_neg (RowsK5.neB (by unfold iSD iVD; omega)),
    if_neg (RowsK5.neB (by unfold iSD iSF; omega)),
    if_pos (beq_self_eq_true _)]

theorem summandAt_iHB : summandAt Z w heard ds (iHB Z.P.x) =
    sHB Z.P w (chalOf Z (heard ++ ds.take (H2K5.Honest.firstOf Z.P.x (iHB Z.P.x)))) := by
  unfold summandAt
  rw [jobs_sum,
    if_neg (by unfold iHB; omega),
    if_neg (RowsK5.neB (by unfold iHB iSE; omega)),
    if_neg (RowsK5.neB (by unfold iHB iVM; omega)),
    if_neg (RowsK5.neB (by unfold iHB iVD; omega)),
    if_neg (RowsK5.neB (by unfold iHB iSF; omega)),
    if_neg (RowsK5.neB (by unfold iHB iSD; omega))]

end

/-! ## 2 The clauses on values, part by part -/

variable {Bk : ProverCoinCounts} {S Cl W₀ Rc Xi Tr X Pb : Type}

/-- **At the coins that the book lends the part number q, the world has the hiding polynomial's
coins under the sumcheck's own slots.** rows, look: what the book lends from. wit: the way from the
run's input to the segment's cells. hh: what the hearing holds of the sumcheck. It is a definition:
a premise's form. Whoever ties the mask row to the coins is meant to show it. -/
def CoinsUnder (V X : Type) (Bk : ProverCoinCounts) (rows : List (Addr × Due))
    (look : Addr → (d : Due) × Cs d) (Z : Seat5) (wit : V → K5In) (Wd : World GE) (q : Nat)
    (dn : List Nat) (e : Ends) (hh : MaskedSum.Heard) : Prop :=
  ∀ lead : Nat, (shapes Z.P.x)[q]? = some (.sum ⟨lead, dn.map Var.plain, some e⟩) →
    ∀ cq : SumCoins (nameOf Z.place q "sum") (nameOf Z.place q "ends")
      (jobQ Z ⟨lead, dn.map Var.plain, some e⟩ q),
    lendPart Bk rows look ⟨Z.place, q⟩
      ((partAt Z.place (chalOf Z) (jobs Z.P) (.sum ⟨lead, dn.map Var.plain, some e⟩, q)).lift
        (V := V) (X := X) (fun _ => ()) wit (fun _ => ()) fun x _ => x) = .ok cq →
    ∀ i, i < ownSlots (Call.all ⟨lead, dn.map Var.plain, some e⟩) →
      Wd.slot (hh.first + i) = hidingCoin cq i

/-- **The clauses on values for the sumcheck that is part q**, in a run: the premises of
`honestSum_at` that speak of values, gathered. rows, look: what the book lends from. w: the
segment's cells. heard, ds: the challenges in front of the member, and its own. It is a definition:
a premise's form. Nothing is claimed of it. -/
structure PartVals (V X : Type) (Bk : ProverCoinCounts) (rows : List (Addr × Due))
    (look : Addr → (d : Due) × Cs d) (Z : Seat5) (wit : V → K5In) (w : K5In)
    (heard ds : List Fmt.Drawn) (Wd : World GE) (q : Nat) (C : Aff) (dn : List Nat) (e : Ends)
    (hh : MaskedSum.Heard) (Good : Summand → Prop) : Prop where
  /-- part q of the row is a sumcheck with these variables and ends -/
  shape : ∃ lead, (shapes Z.P.x)[q]? = some (.sum ⟨lead, dn.map Var.plain, some e⟩)
  tame : (summandAt Z w heard ds q).Tame Reading.gl dn e.dY
  ends : (summandAt Z w heard ds q).ends = e.n
  coins : CoinsUnder V X Bk rows look Z wit Wd q dn e hh
  start : C.value Reading.gl Wd = Reading.gl.val (summandAt Z w heard ds q).total
  good : Good (summandAt Z w heard ds q)

/-- The numbers of coefficients of the sumcheck on the key at the index, in the plan's numbers.
`keyVars` (Johnson/Desc/K5/Honest/Law/Named.lean) is this list under `Var.plain`, by unfolding.
`sdDs` (Johnson/Desc/K5/Honest/Law/TameSD.lean) has the same form in the shape's numbers; that the
two lists are equal asks that the plan's numbers are the shape's, which is not shown here. -/
def keyDs (x : OnBytes.Params.AttentionRounds) : List Nat :=
  List.replicate x.lt 3 ++ List.replicate x.lgk (x.lt + 3) ++ List.replicate x.lt (x.lt + 2)

/-- **The clauses on values for all the kind's masked sumchecks**, each at the weights that the
verifier's text lays. It is a definition: a premise's form. -/
structure ValuesAt (V X : Type) (Bk : ProverCoinCounts) (rows : List (Addr × Due))
    (look : Addr → (d : Due) × Cs d) (Z : Seat5) (wit : V → K5In) (w : K5In)
    (heard ds : List Fmt.Drawn) (Wd : World GE) (g : Geo) (zk : Array (Array E)) (hd : Heard) :
    Prop where
  score : ∀ (i : Nat) (u : Nat × Nat) (o : Nat × MaskedSum.Heard) (ug : UnitG) (Wt : Array E),
    Z.P.x.score[i]? = some u → hd.scores[i]? = some o → g.scores[i]? = some ug →
    scoreW g ug (zk.getD ug.call #[]) (chal o.2) = some Wt →
    PartVals V X Bk rows look Z wit w heard ds Wd i (.slot (o.1 + 6)) (List.replicate u.1 4)
      (prodEnds u.2) o.2 (GoodProducts (prodEnds u.2) o.2 Wt)
  division : ∀ wl : UnitG, g.single .wl = some wl →
    (weights wl (zk.getD wl.call #[])).size = g.NP →
    PartVals V X Bk rows look Z wit w heard ds Wd (iSE Z.P.x) (.slot (hd.five + 1))
      (List.replicate Z.P.x.e 4) (prodEnds Z.P.x.pairs) hd.division
      (GoodProducts (prodEnds Z.P.x.pairs) hd.division
        (wDivision g (weights wl (zk.getD wl.call #[])) (inner wl (zk.getD wl.call #[])) hd))
  below : ∀ wl : UnitG, g.single .wl = some wl →
    (weights wl (zk.getD wl.call #[])).size = g.NP →
    PartVals V X Bk rows look Z wit w heard ds Wd (iVM Z.P.x) (.slot hd.values)
      (List.replicate Z.P.x.valueM 4) (prodEnds Z.P.x.pairs) hd.below
      (GoodProducts (prodEnds Z.P.x.pairs) hd.below
        (wBelow g (weights wl (zk.getD wl.call #[])) (inner wl (zk.getD wl.call #[])) hd))
  on : ∀ wl : UnitG, g.single .wl = some wl →
    (weights wl (zk.getD wl.call #[])).size = g.NP →
    PartVals V X Bk rows look Z wit w heard ds Wd (iVD Z.P.x) (.slot (hd.values + 1))
      (List.replicate Z.P.x.valueD 4) (prodEnds Z.P.x.pairs) hd.on
      (GoodProducts (prodEnds Z.P.x.pairs) hd.on
        (wOn g (weights wl (zk.getD wl.call #[])) (inner wl (zk.getD wl.call #[])) hd))
  atIndex : PartVals V X Bk rows look Z wit w heard ds Wd (iSF Z.P.x)
    (batched Z.P.x.pairs hd.om hd.maxima 1 0) (List.replicate Z.P.x.attained 4)
    (prodEnds Z.P.x.pairs) hd.atIndex
    (GoodProducts (prodEnds Z.P.x.pairs) hd.atIndex (wAtIndex g hd))
  key : PartVals V X Bk rows look Z wit w heard ds Wd (iSD Z.P.x)
    (batched Z.P.x.pairs hd.om' hd.atIndex.sEnd 2 1) (keyDs Z.P.x) (keyEnds Z.P.x) hd.key
    (GoodKey g (keyVars Z.P.x) (keyEnds Z.P.x) (chal hd.atIndex) hd.om')
  cells : PartVals V X Bk rows look Z wit w heard ds Wd (iHB Z.P.x) (.ofConst zeroE)
    (List.replicate Z.P.x.bits 4) (prodEnds Z.P.x.pairs) hd.cells
    (GoodProducts (prodEnds Z.P.x.pairs) hd.cells (wCells g hd))

/-! ## 3 At the member -/

variable (T : Thread Bk S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) {b : Nat}
  {cells : Tr → Cells} {Z : Seat5} {p : Par} {blk : Block S Cl}

/-- `HonestSum` at the rounds as the kind's decision is handed them, from the clauses on values.
CONDITIONAL as `honestSum_at`. -/
theorem honestSum_heard (Hs : K5Seated T b cells Z p blk) {rows : List (Addr × Due)}
    {look : Addr → (d : Due) × Cs d} {v : Option (Local W₀ Rc Xi Tr)}
    {l : List (Step (Local W₀ Rc Xi Tr) X)} {ds : List Fmt.Drawn}
    (hd : drawsFit blk.rounds ds = true) (hl : chainSteps Bk rows look v [blk] T.hs = .ok l)
    {m : Mid (Local W₀ Rc Xi Tr) X} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
    (hp : play l ds [] m = .ok y) {Wd : World GE} {q : Nat} {C : Aff} {dn : List Nat} {e : Ends}
    {hh : MaskedSum.Heard} {Good : Summand → Prop}
    (P : PartVals (Local W₀ Rc Xi Tr) X Bk rows look Z
      (fun t : Local W₀ Rc Xi Tr => inOf Z.P.S Z.link (cells t.trace))
      (inOf Z.P.S Z.link (cells m.st.input.trace)) m.st.heard ds Wd q C dn e hh Good) :
    HonestSum Z.P.x ((roundsOf y.1).map noDigest) Wd q C (dn.map Var.plain) e hh Good := by
  obtain ⟨lead, hq⟩ := P.shape
  rw [k5_bare T Hs hd hp]
  exact honestSum_at T Hs hd hl hp Wd q C lead dn e hh Good hq P.tame P.ends (P.coins lead hq)
    P.start P.good

/-- **At the member, every row that the verifier makes of the kind's masked sumchecks is worth 0**,
in any world. CONDITIONAL on: the kind's half is seated at the member; the challenges fit; the
member's Steps are made and `play` has returned; the kind's hearing has returned on the rounds
played, from a sized ledger; the verifier's text for the rows has returned them at the ledger
behind; AND ON THE CLAUSES ON VALUES (`ValuesAt`), none of which is shown here. -/
theorem rows_zero_k5 (Hs : K5Seated T b cells Z p blk) {rows : List (Addr × Due)}
    {look : Addr → (d : Due) × Cs d} {v : Option (Local W₀ Rc Xi Tr)}
    {l : List (Step (Local W₀ Rc Xi Tr) X)} {ds : List Fmt.Drawn}
    (hd : drawsFit blk.rounds ds = true) (hl : chainSteps Bk rows look v [blk] T.hs = .ok l)
    {m : Mid (Local W₀ Rc Xi Tr) X} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
    (hp : play l ds [] m = .ok y) {F G : Fork} {h5 : Heard} {rest : List Fmt.RoundView} {lead : Nat}
    (hz : OnBytes.Model.Road.Sized F)
    (hh : hear Z.P.x (F, (roundsOf y.1).map noDigest, 0) = some (h5, G, rest, lead)) {g : Geo}
    {zk : Array (Array E)} {L : Left} (hL : leftP g zk h5 G = some L) {Wd : World GE}
    (Vs : ValuesAt (Local W₀ Rc Xi Tr) X Bk rows look Z
      (fun t : Local W₀ Rc Xi Tr => inOf Z.P.S Z.link (cells t.trace))
      (inOf Z.P.S Z.link (cells m.st.input.trace)) m.st.heard ds Wd g zk h5) :
    RowsZero Wd L := by
  have e4 : ∀ n : Nat, (List.replicate n 4).map Var.plain = prodVs n := fun n => by
    unfold prodVs
    rw [List.map_replicate]
  refine rows_zero (along_of_hear_road hz hh) (leftP_spec hL)
    ⟨fun i u o ug Wt hu ho hug hW => ?_, fun wl hwl hs => ?_, fun wl hwl hs => ?_,
      fun wl hwl hs => ?_, ?_,
      honestSum_heard T Hs hd hl hp Vs.key, ?_⟩
  · rw [← e4]
    exact honestSum_heard T Hs hd hl hp (Vs.score i u o ug Wt hu ho hug hW)
  · rw [← e4]
    exact honestSum_heard T Hs hd hl hp (Vs.division wl hwl hs)
  · rw [← e4]
    exact honestSum_heard T Hs hd hl hp (Vs.below wl hwl hs)
  · rw [← e4]
    exact honestSum_heard T Hs hd hl hp (Vs.on wl hwl hs)
  · rw [← e4]
    exact honestSum_heard T Hs hd hl hp Vs.atIndex
  · rw [← e4]
    exact honestSum_heard T Hs hd hl hp Vs.cells

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.jobs_sum
#print axioms ProofFile.Honest.K5.RowsK5.neB
#print axioms ProofFile.Honest.K5.summandAt_unit
#print axioms ProofFile.Honest.K5.summandAt_iSE
#print axioms ProofFile.Honest.K5.summandAt_iVM
#print axioms ProofFile.Honest.K5.summandAt_iVD
#print axioms ProofFile.Honest.K5.summandAt_iSF
#print axioms ProofFile.Honest.K5.summandAt_iSD
#print axioms ProofFile.Honest.K5.summandAt_iHB
#print axioms ProofFile.Honest.K5.honestSum_heard
#print axioms ProofFile.Honest.K5.rows_zero_k5
