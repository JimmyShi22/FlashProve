-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/AtMember.lean: CONDITIONAL: at the member of a `Thread` at
which the half of an attention segment's own rounds is seated: the honest side of one masked
sumcheck, in the form that the statements on the rows ask (`HonestSum`, Honest/K5/Law/RowsAt.lean).
Two definitions, and one statement with its proof.

What is joined: "the stretch of part q of the played rounds is what that part says when it is played
alone" and "the part's share of the challenges has the call's numbers of elements" (`k5_cut`,
`k5_drawsOk`, Honest/K5/Law/Stretch.lean).

Main names:
  `jobQ`          the job of the row's part number q: the text of the row
  `summandAt`      the summand of part q in a run: at the segment's cells and at the challenges
                   heard up to the part's first round
  `honestSum_at`   **`HonestSum` at the rounds played.** CONDITIONAL on: the half is seated; the
                   challenges fit; `play` has returned; part q is a sumcheck of plain variables with
                   ends; AND ON THE CLAUSES ON VALUES, which stay premises: tame, the number of end
                   values, the coins under the sumcheck's own slots, the start form's worth, the
                   further clause. Whoever lays the summand, ties the mask row to the coins and
                   states the start is meant to show these

Limits. No clause on a value is shown here. Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.RowsAt
import Johnson.Desc.ProofFile.Honest.K5.Law.Stretch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes (E zeroE)
open OnBytes.Model (Reading Aff Fork World)
open OnBytes.Slice (GE)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Part (MaskedSum.Heard)
open VerifiableInference.Desc.Part.MaskedSum (Var Ends Call ownSlots)
open VerifiableInference.Desc.First.Att.P (Par)
open ProofFile.Honest.SumLaw (SumCoins hidingCoin)
open H2K5.Honest (Summand K5In shapes)

variable {Bk : ProverCoinCounts} {S Cl W₀ Rc Xi Tr X Pb : Type}

/-- The job of the row's part number q, at the call k: the text of the row. -/
abbrev jobQ (Z : Seat5) (k : Call) (q : Nat) : SumJob K5In Unit :=
  jobOf k (fun w fr => (jobs Z.P).alone q w (chalOf Z fr.heard)) fun w fr =>
    (jobs Z.P).sum q w (chalOf Z fr.heard)

/-- The summand of part q in a run: at the segment's cells, and at the challenges heard up to the
part's first round. heard: the challenges in front of the member. ds: the member's own. -/
def summandAt (Z : Seat5) (w : K5In) (heard ds : List Fmt.Drawn) (q : Nat) : Summand :=
  (jobs Z.P).sum q w (chalOf Z (heard ++ ds.take (H2K5.Honest.firstOf Z.P.x q)))

variable (T : Thread Bk S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) {b : Nat}
  {cells : Tr → Cells} {Z : Seat5} {p : Par} {blk : Block S Cl}

/-- **At the member, the honest side of the sumcheck that is part q**: `HonestSum` at the rounds
played. CONDITIONAL on: the kind's half is seated at the member; the challenges are such as its
rounds can draw; the member's Steps are made and `play` has returned; part q of the row is a
sumcheck of plain variables with ends; AND ON THE CLAUSES ON VALUES, at the part's own summand in
this run: it is tame and has the call's end values; at the coins that the book lends the part, the
world has the hiding polynomial's coins under the sumcheck's own slots; the start form is worth the
summand's total; the further clause. -/
theorem honestSum_at (Hs : K5Seated T b cells Z p blk) {rows : List (Addr × Due)}
    {look : Addr → (d : Due) × Cs d} {v : Option (Local W₀ Rc Xi Tr)}
    {l : List (Step (Local W₀ Rc Xi Tr) X)} {ds : List Fmt.Drawn}
    (hd : drawsFit blk.rounds ds = true) (hl : chainSteps Bk rows look v [blk] T.hs = .ok l)
    {m : Mid (Local W₀ Rc Xi Tr) X} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
    (hp : play l ds [] m = .ok y) (Wd : World GE) (q : Nat) (C : Aff) (lead : Nat)
    (dn : List Nat) (e : Ends) (hh : MaskedSum.Heard) (Good : Summand → Prop)
    (hq : (shapes Z.P.x)[q]? = some (.sum ⟨lead, dn.map Var.plain, some e⟩))
    (hT : (summandAt Z (inOf Z.P.S Z.link (cells m.st.input.trace)) m.st.heard ds q).Tame
      Reading.gl dn e.dY)
    (hn : (summandAt Z (inOf Z.P.S Z.link (cells m.st.input.trace)) m.st.heard ds q).ends = e.n)
    (hm : ∀ cq : SumCoins (nameOf Z.place q "sum") (nameOf Z.place q "ends")
        (jobQ Z ⟨lead, dn.map Var.plain, some e⟩ q),
      lendPart Bk rows look ⟨Z.place, q⟩
        ((partAt Z.place (chalOf Z) (jobs Z.P) (.sum ⟨lead, dn.map Var.plain, some e⟩, q)).lift
          (V := Local W₀ Rc Xi Tr) (X := X) (fun _ => ())
          (fun t : Local W₀ Rc Xi Tr => inOf Z.P.S Z.link (cells t.trace)) (fun _ => ())
          fun x _ => x) = .ok cq →
      ∀ i, i < ownSlots (Call.all ⟨lead, dn.map Var.plain, some e⟩) →
        Wd.slot (hh.first + i) = hidingCoin cq i)
    (hσ : C.value Reading.gl Wd = Reading.gl.val
      (summandAt Z (inOf Z.P.S Z.link (cells m.st.input.trace)) m.st.heard ds q).total)
    (hG : Good (summandAt Z (inOf Z.P.S Z.link (cells m.st.input.trace)) m.st.heard ds q)) :
    HonestSum Z.P.x (roundsOf y.1) Wd q C (dn.map Var.plain) e hh Good := by
  obtain ⟨cq, hlend, ha⟩ := k5_cut T Hs hd hl hp q (.sum ⟨lead, dn.map Var.plain, some e⟩) hq
  exact ⟨Unit, K5In, Unit, nameOf Z.place q "sum", nameOf Z.place q "ends",
    ⟨lead, dn.map Var.plain, some e⟩, fun w fr => (jobs Z.P).alone q w (chalOf Z fr.heard),
    fun w fr => (jobs Z.P).sum q w (chalOf Z fr.heard), cq,
    ⟨inOf Z.P.S Z.link (cells m.st.input.trace),
      m.st.heard ++ ds.take (H2K5.Honest.firstOf Z.P.x q), ()⟩,
    m.shown.plus ((roundsOf y.1).take (H2K5.Honest.firstOf Z.P.x q)),
    (ds.drop (H2K5.Honest.firstOf Z.P.x q)).take ((dn.map Var.plain).length + 3), dn, hq, rfl, hT,
    hn, k5_drawsOk T Hs hd q _ hq, ha, hm cq hlend, hσ, hG⟩

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.honestSum_at
