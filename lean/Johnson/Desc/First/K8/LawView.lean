-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawView.lean: THE SMALLNESS TEST, ITS FIRST HALF: ITS LAW AT THE VIEW THAT IS
MADE OF A WRITTEN TRANSCRIPT.

Johnson/Desc/First/K8/Law.lean's `hear_law` speaks of a round r under four premises: it shows
nothing of the prover's, no drawn element, no position, and its list of entries is the one that the
kit with hash blocks makes of a written verifier message.
Here these four are PAID at the library's reading of a written transcript (`vT`, `rvOne`:
OnBytes/Tie/Pv/Row/ViewT.lean): so the law holds at every written transcript of the kind's round,
with no premise on the round.
  `rdt p`: the kind's declared round as a round's data of a file's chain (OnBytes/Maker/Trees.lean);
    `rdOf_rdt`.
  `view_round`: the four premises, at `rvOne (rdt p) m c`.
  `hear_law_view`: THE LAW AT ALL WRITTEN TRANSCRIPTS: the block, as the fold calls it on the view
    of (m, c), says yes and hands on st' iff its eight tests hold and st' is what the seat lays from
    the list of the typed challenge of c.
  `hearPlace`, `hearPlace_record`: the twins of the library's `rngPlace` and `rngPlace_record`
    (Johnson/Top/H/TailPlaces.lean), which are about the routine drawMatrixF. `hearPlace`
    NAMES THE KIND'S DECLARED ROUND, NOT ITS BLOCK; `hearPlace_record` is of the kind's own text:
    the law of Johnson/Top/H/RowMeet.lean at the block `KTailRngOn.blk d` and the library's maps
    `rngCarS`; and what the record holds behind it.
Definitions, statements and proofs. Limits: that the view which a file's check shows the block is
`vT` of the written transcript is the reading's law, stated elsewhere.


-/
import Johnson.Desc.First.K8.LawAtS
import Johnson.Top.H.TailPlaces

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open Iop Prob Cb.Pv.Tail OnBytes.Slice OnBytes.Maker OnBytes.Tie.Pv.Row OnBytes.Tie.Pv.Tail KObj
    KObj.RowCar KObj.TailRow
  VerifiableInference.OnPublicFiles

/-- The kind's declared round, as a round's data of a file's chain: it sends no root and opens
nothing. -/
def rdt (p : Par) : RDT :=
  { entry := (round p).entry, kind := .entries, items := (round p).items, trees := [], opens := [],
      stored := [] }

theorem rdOf_rdt (p : Par) : rdOf (rdt p) = rd p := rfl

/-- A round that draws matrix entries alone has no element and no position in its record. -/
theorem collect_rest {ds : List Fmt.Draw} {n : ℕ} (h : ds = [.trits n]) (v : Run.Vals .two ds) :
    (Fmt.collect (Run.outAll .two ds v)).elems = [] ∧ (Fmt.collect (Run.outAll .two ds v)).poss = []
        := by
  subst h
  exact ⟨rfl, rfl⟩

/-- The kind's round cuts no item out of the prover's message: there is none. -/
theorem items_nil (p : Par) : (round p).items = [] := by
  simp [round, Fmt.DeclaredRound.items, Fmt.Entry.cut]

theorem gots_nil {l : List Fmt.Item} (h : l = []) (x : Run.PQ.PlainOf l) : Run.PQ.PlainOf.gots l x =
    [] := by
  subst h
  rfl

section
variable {p : Par} {s : Size} (hf : Fits p s)

include hf in
/-- The four premises of `hear_law`, at the library's reading of a written round. -/
theorem view_round (m : (roundT (Run.ckP .two) (rdt p)).up.Msg) (c : (roundT (Run.ckP .two) (rdt
    p)).up.Chal) :
    (rvOne (rdt p) m c).vals = [] ∧ (rvOne (rdt p) m c).drawn.elems = [] ∧
      (rvOne (rdt p) m c).drawn.poss = [] ∧ (rvOne (rdt p) m c).drawn.trits = kitTrits (p := p) c :=
          by
  have hr := collect_rest (onlyTrits hf) (valsOf (rd p) c)
  exact ⟨gots_nil (items_nil p) _, hr.1, hr.2, rfl⟩

/-- **THE LAW AT ALL WRITTEN TRANSCRIPTS OF THE ROUND.** -/
theorem hear_law_view {S Cl : Type} (seat : Seat S) (m : (roundT (Run.ckP .two) (rdt p)).up.Msg)
    (c : (roundT (Run.ckP .two) (rdt p)).up.Chal) (ft : Nat) (st st' : S) (n : Nat) (cols : List
        Col) :
    (approximateRangeProofDrawKind (Cl := Cl) seat p).step ft st (vT [rdt p] ((m, c, ()) : Tr (uLT (Run.ckP .two) [rdt p])))
        cols =
        .ok (st', n) ↔
      (seat.closed st = true ∧ seat.nothingOwed st = true ∧ seat.drawn st = false ∧
        seat.matrices st = p.ks.length ∧ seat.ks st = p.ks ∧ seat.ms st = p.ms ∧
        seat.tau st = p.tau ∧ seat.tabs st = tabs p ∧
        seat.lay st (listOf (matrixOf hf c)) (firstColumns p) = .ok st' ∧ n = 0) := by
  obtain ⟨h1, h2, h3, h4⟩ := view_round hf m c
  rw [vT_one]
  exact hear_law (Cl := Cl) hf seat c ft st st' n cols _ h1 h2 h3 h4

end

/-- The law of RowMeet.lean at the draw, for a run that takes one round: the twin of the library's
`rngPlace`. -/
theorem hearPlace {p : Par} (d : TailCallerOn) (hf : Fits p d.c.s) (r : Fmt.RoundView) (left' : List
           Fmt.RoundView)
    (m : (roundT (Run.ckP .two) (rdt p)).up.Msg) (c : (roundT (Run.ckP .two) (rdt p)).up.Chal)
    (a : (KTailRngOn.src d).X × (KTailRngOn.src d).E.Str) :
    PlaceAt (vT [rdt p]) (okT [rdt p]) (KTailRngOn.blk d) (rngCarS d (rdt p) (onlyTrits hf))
      ((m, c, ()) : Tr (uLT (Run.ckP .two) [rdt p])) (r :: left') a left'
      (((a.1.1, matrixOf hf c), a.1.2), a.2) := by
  intro rest hok hp
  have hpass : GChal.pass (b := (rdt p).entry.work) c = true := (okT_one (rdt p) m c).1 hok
  have e : r :: left' = rvOne (rdt p) m c :: rest := hp
  have e1 : chalTo (rdOf (rdt p)) (matOf d.c.s (rdOf (rdt p)) (onlyTrits hf)) c =
      some (matOf d.c.s (rdOf (rdt p)) (onlyTrits hf) (valsOf (rdOf (rdt p)) c)) := if_pos hpass
  refine ⟨((((), ()), matOf d.c.s (rdOf (rdt p)) (onlyTrits hf) (valsOf (rdOf (rdt p)) c), ()) :
    Tr [IOR.drawRound (Dr d.c.s)]), ?_, rfl, (List.cons.inj e).2⟩
  show (chalTo (rdOf (rdt p)) (matOf d.c.s (rdOf (rdt p)) (onlyTrits hf)) c).bind _ = _
  rw [e1]
  rfl

/-- Behind a yes of the kind's block on the first of the rounds still to be taken, where these begin
with the view of (m, c): the record is what the seat lays from the list of that typed challenge: the
twin of `rngPlace_record`. -/
theorem hearPlace_record {S Cl : Type} {p : Par} {s : Size} (hf : Fits p s) (seat : Seat S) (r :
    Fmt.RoundView)
    (left' rest : List Fmt.RoundView) (m : (roundT (Run.ckP .two) (rdt p)).up.Msg)
    (c : (roundT (Run.ckP .two) (rdt p)).up.Chal) (ft : Nat) (st st' : S) (n : Nat) (cols : List
        Col)
    (hp : r :: left' = vT [rdt p] ((m, c, ()) : Tr (uLT (Run.ckP .two) [rdt p])) ++ rest)
    (h : (approximateRangeProofDrawKind (Cl := Cl) seat p).step ft st [r] cols = .ok (st', n)) :
    seat.lay st (listOf (matrixOf hf c)) (firstColumns p) = .ok st' ∧ left' = rest := by
  have e : r :: left' = rvOne (rdt p) m c :: rest := hp
  obtain ⟨rfl, rfl⟩ := List.cons.inj e
  have h' := (hear_law_view (Cl := Cl) hf seat m c ft st st' n cols).1 (by rw [vT_one]; exact h)
  exact ⟨h'.2.2.2.2.2.2.2.2.1, rfl⟩

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.view_round
#print axioms VerifiableInference.Desc.First.K8.hear_law_view
#print axioms VerifiableInference.Desc.First.K8.hearPlace
#print axioms VerifiableInference.Desc.First.K8.hearPlace_record
