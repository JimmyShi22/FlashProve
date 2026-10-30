-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormSeatsLaws.lean: THE FORM's HALF AT THE LINK's FRONT: K15's LAST TWO BLOCKS'
FUNCTIONS ("LINK", "LINK phi": link, phi, Johnson/Desc/K15/K15.lean) RETURN; the records behind are
written out; and what is carried (LinkSeats, Johnson/Prover/Link/FormSeats.lean) holds behind them.

Main names.
  foldSeat_of     a fold is seated, from raw facts on the record.
  FoldSeat.congr, LinkSeats.laid   rows that meet the sentences leave what is carried.
  linkPhi_yes     "LINK phi".
  mapM_some, locOne_yes, linkLoc_yes   "LINK".

How. The makers return (FormMake.lean); their rows meet RowClauses' sentences
(FormRowsLaws.lean); the
ground takes such rows (FormMake.lean).

Limits. LinkSeats is a premise: the two joinings and the sending in front are not here. That each
drawn location has its column among those handed is a premise: it is Block.step's second test's
matter. FOR ALL DRAWS.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormSeats
import Johnson.Desc.K14.Law.Weights

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.Ground
open Desc.K15 (St Par15)
open Desc.K14.Law (PlacedU tableBits_main vectorRoom_le le_roundUp)

/-- **A fold is seated**, from raw facts on the record. -/
theorem foldSeat_of (T : Statement) (G : Group) (S : FoldeqShape) (u : FoldedRow)
    (x : OnBytes.Oracle) (places : List PadPlace) (hx : T.oracles[u.oracle]? = some x)
    (hs : x.shape = S.u) (hp : x.pad = places.map (fun p => (p.part, p.index)))
    (hP : Send.pad T.codes S.u = some places) (hl : u.lay = vectorLay T.codes S.u S.rowsHigh)
    (hok : foldeqOk T.codes S = true) (hm : u.oracle ∈ G.members) (hi : G.inRun = false) :
    FoldSeat T G S u := by
  have hF := hok
  simp only [foldeqOk, FoldeqShape.ok, Bool.and_eq_true, decide_eq_true_eq] at hF
  have c0 : S.index.ok = true := hF.1.1.1.1.1.1.1
  have c1 : 0 < S.u.mainRows := hF.1.1.1.1.1.2
  have c2 : S.entries ≤ vectorRoom T.codes S.u S.rowsHigh := hF.2
  have tU := tableBits_main T _ x hx (by rw [hs]; omega) S.rowsHigh
  rw [hs] at tU
  have hE : S.entries ≤ 2 ^ u.lay.bits := by
    rw [hl]
    exact Nat.le_trans c2 (vectorRoom_le _ _ _)
  have e2 : S.index.code.ell ≤ S.tailFirst := le_roundUp _ _ (Nat.two_pow_pos _)
  have hell : 1 ≤ S.index.code.ell := by
    simp only [IndexShape.ok, Code.ok, Bool.and_eq_true, decide_eq_true_eq] at c0
    exact c0.1.1.1.1.1.1.1.2
  have hbits : u.lay.bits ≤ 63 := by
    by_contra c
    have h60 : 60 < (vectorLay T.codes S.u S.rowsHigh).bits := by
      rw [← hl]
      omega
    have hz : vectorRoom T.codes S.u S.rowsHigh = 0 := by
      unfold vectorRoom
      dsimp only
      split_ifs <;> first | rfl | exact absurd h60 ‹_›
    unfold FoldeqShape.entries at c2
    omega
  unfold FoldeqShape.entries at hE
  refine ⟨⟨tU.1, by rw [tU.2, hl], Desc.K14.Law.ceilLog2_le _ _ (by omega), hE, ?_⟩, hm, hi, hbits,
    c0,
    padsFar_of T S u places (fun y hy => by
      rw [hx] at hy
      obtain rfl := Option.some.inj hy
      exact hp) hP hl hok⟩
  unfold FoldeqShape.tailFirst
  exact Nat.mul_mod_left _ _

/-- A seat reads of the statement its messages and codes alone, and of the group its members and its
mark. -/
theorem FoldSeat.congr {T T' : Statement} {G G' : Group} {S : FoldeqShape} {u : FoldedRow}
    (ho : T'.oracles = T.oracles) (hc : T'.codes = T.codes) (hm : G'.members = G.members)
    (hi : G'.inRun = G.inRun) (h : FoldSeat T G S u) : FoldSeat T' G' S u :=
  ⟨⟨by
      have := h.placed.has
      unfold Statement.has at this ⊢
      rw [ho]
      exact this, by rw [tableBits_congr' ho hc]; exact h.placed.bits, h.placed.room,
      h.placed.roomTail, h.placed.aligned⟩,
    hm ▸ h.member, hi.trans h.idle, h.bits, h.shape, fun x hx => h.far x (ho ▸ hx)⟩

/-- **Rows that meet the sentences, laid on the group, leave what is carried.** -/
theorem LinkSeats.laid {p : Par15} {d : St} {G : Group} (H : LinkSeats p d G) (rows : List Row)
    (hr : ∀ row ∈ rows, K9L.RowClauses d.st G row) :
    LinkSeats p { d with st := withRows d.st d.loc.g rows }
      { G with rows := G.rows ++ rows.toArray } := by
  obtain ⟨h1, h2⟩ := withRows_oracles d.loc.g rows d.st
  refine ⟨withRows_group d.loc.g rows d.st G H.group,
    FoldSeat.congr (T := d.st) (G := G) h1 h2 rfl rfl H.s0,
    FoldSeat.congr (T := d.st) (G := G) h1 h2 rfl rfl H.s1, H.gamma, fun row hrow => ?_⟩
  have hrow' : row ∈ G.rows.toList ++ rows := by simpa using hrow
  refine RowClauses.congr (T := d.st) (G := G) h1 h2 rfl rfl ?_
  rcases List.mem_append.1 hrow' with c | c
  · exact H.rows row c
  · exact hr row c

/-- **"LINK phi" says yes.** -/
theorem linkPhi_yes (p : Par15) (d : St) (G : Group) (r : Fmt.RoundView) (H : LinkSeats p d G)
    (hr : r.drawn.elems.length = p.S.entryBits) :
    ∃ row, Desc.K15.phi p d [r] = some { d with st := withRows d.st d.loc.g [row] } ∧
      LinkSeats p { d with st := withRows d.st d.loc.g [row] }
        { G with rows := G.rows ++ [row].toArray } := by
  obtain ⟨row, hrow⟩ := eqPhi_some p.S (Desc.K14.drawn r) d.loc.o0 d.loc.o1
    (by unfold Desc.K14.drawn; rw [List.length_map, hr])
  have hc := eqPhi_clauses d.st G p.S p.samples _ _ _ row hrow H.s0 H.s1
  refine ⟨row, ?_, H.laid [row] fun x hx => by rw [List.mem_singleton.1 hx]; exact hc⟩
  show (do addRowP d d.loc.g (← Desc.K15.eqPhi p.S (Desc.K14.drawn r) d.loc.o0 d.loc.o1)) = _
  rw [hrow]
  exact addRowP_yes d d.loc.g G row H.group hc

/-- A list of makers that all return, returns; and each row made is some maker's. -/
theorem mapM_some {α β : Type} (f : α → Option β) : ∀ (l : List α),
    (∀ a ∈ l, ∃ b, f a = some b) →
    ∃ bs, l.mapM f = some bs ∧ ∀ b ∈ bs, ∃ a ∈ l, f a = some b
  | [], _ => ⟨[], rfl, fun _ h => absurd h (by simp)⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a List.mem_cons_self
    obtain ⟨bs, h1, h2⟩ := mapM_some f l fun x hx => h x (List.mem_cons_of_mem _ hx)
    refine ⟨b :: bs, by rw [List.mapM_cons, hb, h1]; rfl, fun c hc => ?_⟩
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ⟨a, List.mem_cons_self, hb⟩
    · obtain ⟨x, hx, e⟩ := h2 c hc
      exact ⟨x, List.mem_cons_of_mem _ hx, e⟩

/-- **One table's share of "LINK".** -/
theorem locOne_yes (p : Par15) (d : St) (G : Group) (further : Bool) (draws : List Nat)
    (cols : List (Nat × List UInt64)) (H : LinkSeats p d G)
    (hc : ∀ x ∈ draws, ∃ c, cols.lookup x = some c ∧ 2 ^ p.S.table.v ≤ c.length) :
    ∃ rows, Desc.K15.locOne p d further draws cols (if further then d.loc.o1 else d.loc.o0) =
        some { d with st := withRows d.st d.loc.g rows } ∧
      LinkSeats p { d with st := withRows d.st d.loc.g rows }
        { G with rows := G.rows ++ rows.toArray } := by
  have hseat : FoldSeat d.st G (p.S.side further p.samples)
      (if further then d.loc.o1 else d.loc.o0) := by
    cases further
    · exact H.s0
    · exact H.s1
  have hw : (Desc.K15.weights d.loc).size = 2 ^ p.S.table.v := by
    unfold Desc.K15.weights
    rw [Desc.K14.Law.eqTable_size, H.gamma]
  obtain ⟨rows, h1, h2⟩ := mapM_some (fun x => do
      Desc.K14.locX (p.S.side further p.samples) x (Desc.K15.weights d.loc)
        ((← cols.lookup x).toArray) (if further then d.loc.o1 else d.loc.o0)) draws
    fun x hx => by
      obtain ⟨c, e1, e2⟩ := hc x hx
      obtain ⟨row, hrow⟩ := locX_some (p.S.side further p.samples) x (Desc.K15.weights d.loc)
        c.toArray (if further then d.loc.o1 else d.loc.o0) (by rw [hw]; simpa using e2)
      exact ⟨row, by simp only [e1, Option.bind_eq_bind, Option.bind_some]; exact hrow⟩
  have hcl : ∀ row ∈ rows, K9L.RowClauses d.st G row := by
    intro row hrow
    obtain ⟨x, _, e⟩ := h2 row hrow
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at e
    obtain ⟨c, _, e⟩ := e
    exact locX_clauses d.st G _ x _ _ _ row e hseat
  refine ⟨rows, ?_, H.laid rows hcl⟩
  unfold Desc.K15.locOne
  rw [h1]
  exact addRowsP_yes d d.loc.g G rows H.group H.s0.idle hcl

/-- **"LINK" says yes.** -/
theorem linkLoc_yes (p : Par15) (d : St) (G : Group) (r : Fmt.RoundView)
    (cols0 cols1 : List (Nat × List UInt64)) (H : LinkSeats p d G)
    (h0 : ∀ x ∈ (r.drawn.poss.map (· % 2 ^ p.S.table.code.logN)).take p.S.columnsFirst,
      ∃ c, cols0.lookup x = some c ∧ 2 ^ p.S.table.v ≤ c.length)
    (h1 : ∀ x ∈ ((r.drawn.poss.map (· % 2 ^ p.S.table.code.logN)).drop p.S.columnsFirst).take
        p.S.columnsFurther, ∃ c, cols1.lookup x = some c ∧ 2 ^ p.S.table.v ≤ c.length) :
    ∃ rows0 rows1, Desc.K15.link p d [r] [cols0, cols1] =
        some { d with st := withRows (withRows d.st d.loc.g rows0) d.loc.g rows1 } ∧
      LinkSeats p { d with st := withRows (withRows d.st d.loc.g rows0) d.loc.g rows1 }
        { G with rows := G.rows ++ rows0.toArray ++ rows1.toArray } := by
  obtain ⟨rows0, e1, H1⟩ := locOne_yes p d G false _ cols0 H h0
  obtain ⟨rows1, e2, H2⟩ := locOne_yes p _ _ true _ cols1 H1 h1
  refine ⟨rows0, rows1, ?_, H2⟩
  simp only [Bool.false_eq_true, if_false] at e1
  simp only [if_true] at e2
  show (do
    let d ← Desc.K15.locOne p d false
      ((r.drawn.poss.map (· % 2 ^ p.S.table.code.logN)).take p.S.columnsFirst) cols0 d.loc.o0
    Desc.K15.locOne p d true
      (((r.drawn.poss.map (· % 2 ^ p.S.table.code.logN)).drop p.S.columnsFirst).take
        p.S.columnsFurther) cols1 d.loc.o1) = _
  rw [e1]
  exact e2

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.foldSeat_of
#print axioms Johnson.Prover.Link.FoldSeat.congr
#print axioms Johnson.Prover.Link.LinkSeats.laid
#print axioms Johnson.Prover.Link.linkPhi_yes
#print axioms Johnson.Prover.Link.mapM_some
#print axioms Johnson.Prover.Link.locOne_yes
#print axioms Johnson.Prover.Link.linkLoc_yes
