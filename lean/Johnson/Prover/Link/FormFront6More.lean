-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormFront6More.lean: THE FORM's HALF: BEHIND THE LINK's SIX FRONT BLOCKS THE
STATEMENT IS IN ORDER (InOrder, Johnson/Desc/Means/Order.lean), AND THE GROUP HAS AS MANY OPEN
CLAIMS AS THE TWO KEYS' SEEDS, THE COLUMNS DRAWN, AND ONE.

Main names.
  fold_keeps      what every block's step keeps, the fold keeps.
  point_keeps, laysOne_keeps, laysRec_keeps, locOne_keeps, link_keeps, phi_keeps, sendK1_keeps
    K15's functions and the sending's block keep «in order», from their yes.
  front6_order    FROM THE YES ALONE, and one test on the plan (the kind K1's own): in order.
  openRows        how many claims lie open on the group that the small record names.
  addRowsP_open, laysOne_open, laysRec_open, locOne_open, link_open, phi_open   from the yes: how
    many more.
  front6_all      front6_whole's premises (FormSendGave.lean); its end, and beside it: in order,
    and the count.

How. Johnson/Desc/Means/Page.lean's keepers; K1.decideSend_keeps
(Johnson/Desc/K1/Law/KeepsOrder.lean); K1.behind15_st (Johnson/Desc/K1/Law/SitsEntry.lean); the
inversions of Johnson/Desc/K15/GroundInv.lean; mapM_length (Johnson/Desc/First/K4/RunsLength.lean).

Limits. The count is of the group's OPEN claims: the members' sample rows, which a test takes in
beside them, are not counted here. front6_all repeats front6_yes' walk (FormFront6.lean) so as to
hold each step's equation.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormSendGave
import Johnson.Desc.Means.Page
import Johnson.Desc.K1.Law.KeepsOrder
import Johnson.Desc.K1.Law.SitsEntry
import Johnson.Desc.K15.GroundInv
import Johnson.Desc.First.K4.RunsLength

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.Ground
open _root_.Desc.Plain (DState)
open Desc.K15 (St Par15 P15)
open Johnson.Prover.Send
open Means (InOrder)

/-! ## In order -/

/-- **What every block's step keeps, the fold keeps.** -/
theorem fold_keeps {S Cl : Type} (Inv : S → Prop) (ft : Nat) : ∀ (l : List (Block S Cl)) (s : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (out : S × List Fmt.RoundView × List OpenedColumn),
    (∀ b ∈ l, ∀ s s' rs cols k, b.step ft s rs cols = .ok (s', k) → Inv s → Inv s') →
    foldBlocks ft l s rs cols = .ok out → Inv s → Inv out.1
  | [], s, rs, cols, out, _, h, hI => by
    rw [foldBlocks_nil ft s rs cols out h]
    exact hI
  | b :: l, s, rs, cols, out, hb, h, hI => by
    obtain ⟨s', k, _, hs, h'⟩ := foldBlocks_cons ft b l s rs cols out h
    exact fold_keeps Inv ft l s' _ _ out (fun c hc => hb c (List.mem_cons_of_mem _ hc)) h'
      (hb b List.mem_cons_self _ _ _ _ _ hs hI)

theorem point_keeps (p : Par15) (d d' : St) (rs : List Fmt.RoundView)
    (h : Desc.K15.point p d rs = some d') (hI : InOrder d.st) : InOrder d'.st := by
  match rs, h with
  | [r], h =>
    rw [Desc.K15.point_inv p d d' r h]
    exact hI.withGroup _ _
  | [], h => simp [Desc.K15.point] at h
  | _ :: _ :: _, h => simp [Desc.K15.point] at h

theorem laysOne_keeps (p : Par15) (d d' : St) (key : TableKey) (o : FoldedRow)
    (h : Desc.K15.laysOne p d key o = some d') (hI : InOrder d.st) : InOrder d'.st := by
  unfold Desc.K15.laysOne at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨d1, hj, l, _, ha⟩ := h
  exact Means.addRowsP_keeps ha (Means.joinP_keeps hj hI)

theorem laysRec_keeps (p : Par15) (d d' : St) (rs : List Fmt.RoundView)
    (h : Desc.K15.laysRec p d rs = some d') (hI : InOrder d.st) : InOrder d'.st := by
  unfold Desc.K15.laysRec at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, d1, h1, h2⟩ := h
  exact laysOne_keeps p d1 d' _ _ h2 (laysOne_keeps p d d1 _ _ h1 hI)

theorem locOne_keeps (p : Par15) (d d' : St) (further : Bool) (draws : List Nat)
    (cols : List (Nat × List UInt64)) (o : FoldedRow)
    (h : Desc.K15.locOne p d further draws cols o = some d') (hI : InOrder d.st) :
    InOrder d'.st := by
  unfold Desc.K15.locOne at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨l, _, ha⟩ := h
  exact Means.addRowsP_keeps ha hI

theorem link_keeps (p : Par15) (d d' : St) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : Desc.K15.link p d rs gs = some d')
    (hI : InOrder d.st) : InOrder d'.st := by
  unfold Desc.K15.link at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨d1, h1, h2⟩ := h
    exact locOne_keeps p d1 d' _ _ _ _ h2 (locOne_keeps p d d1 _ _ _ _ h1 hI)
  · cases h

theorem phi_keeps (p : Par15) (d d' : St) (rs : List Fmt.RoundView) (h : Desc.K15.phi p d rs = some d')
    (hI : InOrder d.st) : InOrder d'.st := by
  unfold Desc.K15.phi at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨row, _, ha⟩ := h
    exact (Means.addRowP_keeps ha hI).1
  · cases h

theorem sendK1_keeps (P : P15) (hp : K1.planOkOwn (Desc.K15.parK1 P) = true) (d d' : St)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hfit : roundsFit (K1.rounds (Desc.K15.parK1 P)) rs = true)
    (h : (Desc.K15.sendK1 P).decide d rs gs = .ok d') (hI : InOrder d.st) : InOrder d'.st := by
  obtain ⟨r1, r2, rfl⟩ := roundsFit_two' _ _ rs hfit
  change ((K1.decideSend (Desc.K15.parK1 P) none (sentIn d) [r1, r2]).map fun x =>
      ({ owed := none, held := { x.2 with loc := x.1 } } : K1.Owing (DState (Array Nat)))).bind
    (fun t => named "the sending's numbers are not those that the kind notes"
      (Desc.K15.behind P.par { d with st := t.held.st, book := t.held.book, roots := t.held.roots,
                                      opened := t.held.opened } t.held.loc)) = .ok d' at h
  cases hd : K1.decideSend (Desc.K15.parK1 P) none (sentIn d) [r1, r2] with
  | error e =>
    rw [hd] at h
    cases h
  | ok y =>
    obtain ⟨ids, dk⟩ := y
    rw [hd] at h
    cases hb : Desc.K15.behind P.par { d with st := dk.st, book := dk.book, roots := dk.roots,
                                              opened := dk.opened } ids with
    | none =>
      have h' : named "the sending's numbers are not those that the kind notes"
          (Desc.K15.behind P.par { d with st := dk.st, book := dk.book, roots := dk.roots,
                                          opened := dk.opened } ids) = .ok d' := h
      rw [hb] at h'
      cases h'
    | some e =>
      have h' : named "the sending's numbers are not those that the kind notes"
          (Desc.K15.behind P.par { d with st := dk.st, book := dk.book, roots := dk.roots,
                                          opened := dk.opened } ids) = .ok d' := h
      rw [hb] at h'
      obtain rfl : e = d' := by injection h'
      rw [K1.behind15_st hb]
      exact K1.decideSend_keeps (Desc.K15.parK1 P) none (sentIn d) dk r1 r2 ids hp hfit hd hI

/-- **FROM THE YES ALONE, and one test on the plan: the statement behind the six is in order.** -/
theorem front6_order (P : P15) (x : TableKey × TableKey) (rs rest : List Fmt.RoundView)
    (cols cols' : List OpenedColumn) (d' : St) (hp : K1.planOkOwn (Desc.K15.parK1 P) = true)
    (h : foldBlocks 0 (Desc.K15.frontBlock P :: Desc.K15.blocksOrV P) (Desc.K15.first P.codes x) rs
      cols = .ok (d', rest, cols')) : InOrder d'.st := by
  refine fold_keeps (fun d : St => InOrder d.st) 0 _ _ rs cols _ ?_ h (InOrder.start P.codes)
  intro b hb s s' rs cols k hs hI
  obtain ⟨hfit, _, _, hd⟩ := step_inv 0 b s s' rs cols k hs
  rcases List.mem_cons.1 hb with rfl | hb
  · obtain rfl : s = s' := by injection hd
    exact hI
  · cases he : Desc.K15.entries P with
    | none =>
      unfold Desc.K15.blocksOrV Desc.K15.linkBlocksBeforeTest at hb
      simp only [he, Option.bind_eq_bind, Option.bind_none, Option.getD_none,
        List.mem_singleton] at hb
      subst hb
      obtain rfl : s = s' := by injection hd
      exact hI
    | some es =>
      rw [Desc.K15.blocksV_eq P es he] at hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl
      · exact point_keeps P.par s s' _ (Desc.K15.why_ok _ _ _ hd) hI
      · exact sendK1_keeps P hp s s' _ _
          ((H2K.Onto.roundsFit_noDigest _ rs).trans hfit) hd hI
      · exact laysRec_keeps P.par s s' _ (Desc.K15.why_ok _ _ _ hd) hI
      · exact link_keeps P.par s s' _ _ (Desc.K15.why_ok _ _ _ hd) hI
      · exact phi_keeps P.par s s' _ (Desc.K15.why_ok _ _ _ hd) hI

/-! ## How many open claims -/

/-- How many claims lie open on the group that the small record names. WHERE THERE IS NO SUCH GROUP:
0. -/
def openRows (d : St) : Nat := ((d.st.groups[d.loc.g]?).map (·.rows.size)).getD 0

theorem openRows_of {d : St} {G : Group} (h : d.st.groups[d.loc.g]? = some G) :
    openRows d = G.rows.size := by
  unfold openRows
  rw [h]
  rfl

/-- Rows laid on a group, from the yes: the group was there; behind, it has them at its end. -/
theorem addRowsP_open {L : Type} (d d' : DState L) (g : Nat) (l : List Row)
    (h : addRowsP d g l = some d') :
    ∃ G G', d.st.groups[g]? = some G ∧ d'.st.groups[g]? = some G' ∧
      G'.rows.size = G.rows.size + l.length ∧ d'.loc = d.loc := by
  obtain ⟨_, rfl⟩ := Desc.K15.addRowsP_inv d d' g l h
  unfold addRowsP at h
  split at h
  · rename_i hk
    simp only [Ground.ok, rowsL, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true] at hk
    obtain ⟨G, hG⟩ := Option.isSome_iff_exists.1 hk.1
    exact ⟨G, _, hG, withRows_group g l d.st G hG, by simp, rfl⟩
  · cases h

theorem laysOne_open (p : Par15) (d d' : St) (key : TableKey) (o : FoldedRow)
    (h : Desc.K15.laysOne p d key o = some d') :
    openRows d' = openRows d + key.seeds.length ∧ d'.loc = d.loc := by
  unfold Desc.K15.laysOne at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨d1, hj, l, hl, ha⟩ := h
  obtain ⟨G, hG, rfl⟩ := Desc.K15.joinP_inv d d1 _ _ _ hj
  obtain ⟨G1, G', h1, h2, hs, h3⟩ := addRowsP_open _ d' _ l ha
  have e1 : G1.rows = G.rows := by
    obtain rfl := Option.some.inj
      (h1.symm.trans (joined_group d.st d.loc.g o.oracle false G hG))
    rfl
  have hlen := OnBytes.Desc.First.K4.mapM_length _ l hl
  have h2' : d'.st.groups[d'.loc.g]? = some G' := by rw [h3]; exact h2
  refine ⟨?_, h3⟩
  rw [openRows_of h2', openRows_of hG, hs, e1, hlen, List.length_zipIdx]

theorem laysRec_open (p : Par15) (d d' : St) (rs : List Fmt.RoundView)
    (h : Desc.K15.laysRec p d rs = some d') :
    openRows d' = openRows d + d.loc.key0.seeds.length + d.loc.key1.seeds.length ∧
      d'.loc = d.loc := by
  unfold Desc.K15.laysRec at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, d1, h1, h2⟩ := h
  obtain ⟨a1, a2⟩ := laysOne_open p d d1 _ _ h1
  obtain ⟨b1, b2⟩ := laysOne_open p d1 d' _ _ h2
  exact ⟨by rw [b1, a1, a2], b2.trans a2⟩

theorem locOne_open (p : Par15) (d d' : St) (further : Bool) (draws : List Nat)
    (cols : List (Nat × List UInt64)) (o : FoldedRow)
    (h : Desc.K15.locOne p d further draws cols o = some d') :
    openRows d' = openRows d + draws.length ∧ d'.loc = d.loc := by
  unfold Desc.K15.locOne at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨l, hl, ha⟩ := h
  obtain ⟨G, G', h1, h2, hs, h3⟩ := addRowsP_open d d' _ l ha
  have hlen := OnBytes.Desc.First.K4.mapM_length _ l hl
  have h2' : d'.st.groups[d'.loc.g]? = some G' := by rw [h3]; exact h2
  refine ⟨?_, h3⟩
  rw [openRows_of h2', openRows_of h1, hs, hlen]

theorem link_open (p : Par15) (d d' : St) (r : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : Desc.K15.link p d [r] gs = some d')
    (hr : r.drawn.poss.length = p.S.columnsFirst + p.S.columnsFurther) :
    openRows d' = openRows d + (p.S.columnsFirst + p.S.columnsFurther) ∧ d'.loc = d.loc := by
  unfold Desc.K15.link at h
  split at h
  · rename_i _ _ r' c0 c1 e1
    obtain rfl : r = r' := by injection e1
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨d1, h1, h2⟩ := h
    obtain ⟨a1, a2⟩ := locOne_open p d d1 _ _ _ _ h1
    obtain ⟨b1, b2⟩ := locOne_open p d1 d' _ _ _ _ h2
    refine ⟨?_, b2.trans a2⟩
    rw [b1, a1]
    simp only [List.length_take, List.length_drop, List.length_map, hr]
    omega
  · cases h

theorem phi_open (p : Par15) (d d' : St) (r : Fmt.RoundView) (h : Desc.K15.phi p d [r] = some d') :
    openRows d' = openRows d + 1 ∧ d'.loc = d.loc := by
  obtain ⟨rE, _, _, rfl⟩ := Desc.K15.phi_inv p d d' r h
  have h' : (do addRowP d d.loc.g (← Desc.K15.eqPhi p.S (Desc.K14.drawn r) d.loc.o0 d.loc.o1)) =
      some { d with st := withRow d.st d.loc.g rE } := h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h'
  obtain ⟨row, _, ha⟩ := h'
  obtain ⟨hk, _⟩ := Desc.K15.addRowP_inv d _ _ _ ha
  obtain ⟨G, hG, _⟩ := Means.rowIn_of_rowL hk
  refine ⟨?_, rfl⟩
  rw [openRows_of (d := { d with st := withRow d.st d.loc.g rE })
    (withRow_group d.st d.loc.g rE G hG), openRows_of hG]
  simp

/-- How many positions a round that fits one declared round draws. -/
theorem poss_of_fit (dcl : Fmt.DeclaredRound) (r : Fmt.RoundView) (h : roundsFit [dcl] [r] = true) :
    r.drawn.poss.length = dcl.entry.poss := by
  unfold roundsFit at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.1.1.2

/-- **front6_all: front6_whole's premises; its end, and beside it: in order, and the count.** -/
theorem front6_all (P : P15) (x : TableKey × TableKey) (r0 r1 r2 r3 r4 : Fmt.RoundView)
    (cols : List OpenedColumn) (he : Desc.K15.entries P = some (Desc.K15.fiveOf P))
    (hl : P.codes.lengthsOk = true) (hok : linkOk P.codes P.S P.set.samples = true)
    (hp : K1.planOkOwn (Desc.K15.parK1 P) = true) (k0 : Own.keyFits x.1 P.S.table = true)
    (k1 : Own.keyFits x.2 P.S.table = true) (z0 : x.1.seeds.all (!isZeroE ·.beta) = true)
    (z1 : x.2.seeds.all (!isZeroE ·.beta) = true)
    (f0 : roundsFit (Desc.K15.bPoint P (Desc.K15.fiveOf P)).rounds [r0] = true)
    (f12 : roundsFit (K1.rounds (Desc.K15.parK1 P)) [r1, r2] = true)
    (f3 : roundsFit (Desc.K15.bLink P (Desc.K15.fiveOf P)).rounds [r3] = true)
    (hc : (cols.take (linkWant P.S r3).length).map (fun c => (c.1, c.2.1, c.2.2.length)) =
      linkWant P.S r3)
    (f4 : roundsFit (Desc.K15.bPhi P (Desc.K15.fiveOf P)).rounds [r4] = true) :
    ∃ d' G', foldBlocks 0 (Desc.K15.frontBlock P :: Desc.K15.blocksOrV P)
        (Desc.K15.first P.codes x) [r0, r1, r2, r3, r4] cols =
        .ok (d', [], cols.drop (linkWant P.S r3).length) ∧ LinkSeats P.par d' G' ∧
      InOrder d'.st ∧
      G'.rows.size = 2 * P.S.table.answers + (P.S.columnsFirst + P.S.columnsFurther) + 1 := by
  obtain ⟨g1, g2, g3⟩ := linkOk_gives P.codes P.S P.set.samples hok
  have hn : 1 ≤ P.set.samples := by
    have h2 := g2
    simp only [foldeqOk, FoldeqShape.ok, Bool.and_eq_true, decide_eq_true_eq] at h2
    exact h2.1.1.1.2
  obtain ⟨d2, hs, hg⟩ := sendK1_gave P (pointT P.par (Desc.K15.first P.codes x) (noDigest r0)) r1 r2
    cols (SendFront.of_lengths _ _ rfl hp rfl hl) f12 hn
  have e0 : r0.drawn.elems.length = P.S.table.v := elems_of_fit _ r0 f0
  have e4 : r4.drawn.elems.length = P.S.entryBits := elems_of_fit _ r4 f4
  have e3 : r3.drawn.poss.length = P.S.columnsFirst + P.S.columnsFurther := poss_of_fit _ r3 f3
  have hSent := linkSent_of P.par (Desc.K15.first P.codes x) d2 (noDigest r0) hg g2 g3 e0 k0 k1 z0
    z1
  obtain ⟨rows0, rows1, eR, HR⟩ := laysRec_yes P.par d2 _ [] hSent
  obtain ⟨d4, G4, eL, HL⟩ := bLink_step P _ _ r3 cols HR f3 hc
  obtain ⟨row, eP, HP⟩ := linkPhi_yes P.par d4 G4 (noDigest r4) HL e4
  obtain ⟨d', G', e, H'⟩ := front6_yes P x r0 r1 r2 r3 r4 cols d2 he hok k0 k1 z0 z1 f0 hs hg f3 hc
    f4
  refine ⟨d', G', e, H', front6_order P x _ _ cols _ d' hp e, ?_⟩
  -- the record behind is one: the fold is a function
  have s0 : (Desc.K15.frontBlock P).step 0 (Desc.K15.first P.codes x) [] cols =
      .ok (Desc.K15.first P.codes x, 0) :=
    step_no_cols _ 0 _ _ [] cols (fun r hr => absurd hr (by simp [Desc.K15.frontBlock, roundlessBlock]))
      rfl rfl
  have s1 : (Desc.K15.bPoint P (Desc.K15.fiveOf P)).step 0 (Desc.K15.first P.codes x) [r0] cols =
      .ok (pointT P.par (Desc.K15.first P.codes x) (noDigest r0), 0) :=
    step_no_cols _ 0 _ _ [r0] cols
      (fun r hr => by
        obtain rfl := List.mem_singleton.1 hr
        exact ⟨rfl, rfl⟩) f0
      (by
        show Desc.K15.why [] (Desc.K15.point P.par (Desc.K15.first P.codes x) [noDigest r0]) = _
        rw [point_yes P.par (Desc.K15.first P.codes x) (noDigest r0) g1]
        rfl)
  have s3 : (Desc.K15.bRec P (Desc.K15.fiveOf P)).step 0 d2 [] cols = .ok (_, 0) :=
    step_no_cols _ 0 _ _ [] cols (fun r hr => absurd hr (by simp [Desc.K15.bRec])) rfl
      (by
        show Desc.K15.why _ (Desc.K15.laysRec P.par d2 []) = _
        rw [eR]
        rfl)
  have s5 : (Desc.K15.bPhi P (Desc.K15.fiveOf P)).step 0 d4 [r4]
      (cols.drop (linkWant P.S r3).length) = .ok (_, 0) :=
    step_no_cols _ 0 _ _ [r4] _
      (fun r hr => by
        obtain rfl := List.mem_singleton.1 hr
        exact ⟨rfl, rfl⟩) f4
      (by
        show Desc.K15.why [] (Desc.K15.phi P.par d4 [noDigest r4]) = _
        rw [eP]
        rfl)
  have e' : foldBlocks 0 (Desc.K15.frontBlock P :: Desc.K15.blocksOrV P)
      (Desc.K15.first P.codes x) [r0, r1, r2, r3, r4] cols =
      .ok ({ d4 with st := withRows d4.st d4.loc.g [row] }, [],
        (cols.drop (linkWant P.S r3).length).drop 0) := by
    rw [Desc.K15.blocksV_eq P _ he]
    refine (foldBlocks_ok 0 _ _ _ [] [r0, r1, r2, r3, r4] cols rfl _ 0 s0).trans ?_
    refine (foldBlocks_ok 0 _ _ _ [r0] [r1, r2, r3, r4] cols rfl _ 0 s1).trans ?_
    refine (foldBlocks_ok 0 _ _ _ [r1, r2] [r3, r4] cols rfl _ 0 hs).trans ?_
    refine (foldBlocks_ok 0 _ _ _ [] [r3, r4] cols rfl _ 0 s3).trans ?_
    refine (foldBlocks_ok 0 _ _ _ [r3] [r4] cols rfl _ _ eL).trans ?_
    exact foldBlocks_ok 0 _ [] _ [r4] [] _ rfl _ 0 s5
  have hd : d' = { d4 with st := withRows d4.st d4.loc.g [row] } := by
    have := e.symm.trans e'
    injection this with this
    exact congrArg Prod.fst this
  -- the count, step by step, from each function's yes
  obtain ⟨_, _, _, hdL⟩ := step_inv 0 _ _ _ _ _ _ eL
  obtain ⟨c3, l3⟩ := laysRec_open P.par d2 _ [] eR
  obtain ⟨c4, _⟩ := link_open P.par _ d4 (noDigest r3) _ (Desc.K15.why_ok _ _ _ hdL) e3
  obtain ⟨c5, _⟩ := phi_open P.par d4 _ (noDigest r4) eP
  have c2 : openRows d2 = 0 := openRows_of hSent.group
  have a0 : d2.loc.key0.seeds.length = P.S.table.answers := by
    rw [hg.key0]
    have := k0
    simp only [Own.keyFits, Bool.and_eq_true, beq_iff_eq] at this
    exact this.1.2
  have a1 : d2.loc.key1.seeds.length = P.S.table.answers := by
    rw [hg.key1]
    have := k1
    simp only [Own.keyFits, Bool.and_eq_true, beq_iff_eq] at this
    exact this.1.2
  rw [← openRows_of H'.group, hd, c5, c4, c3, c2, a0, a1]
  show 0 + _ + _ + (P.S.columnsFirst + P.S.columnsFurther) + 1 = _
  omega

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.fold_keeps
#print axioms Johnson.Prover.Link.point_keeps
#print axioms Johnson.Prover.Link.laysOne_keeps
#print axioms Johnson.Prover.Link.laysRec_keeps
#print axioms Johnson.Prover.Link.locOne_keeps
#print axioms Johnson.Prover.Link.link_keeps
#print axioms Johnson.Prover.Link.phi_keeps
#print axioms Johnson.Prover.Link.sendK1_keeps
#print axioms Johnson.Prover.Link.front6_order
#print axioms Johnson.Prover.Link.openRows_of
#print axioms Johnson.Prover.Link.addRowsP_open
#print axioms Johnson.Prover.Link.laysOne_open
#print axioms Johnson.Prover.Link.laysRec_open
#print axioms Johnson.Prover.Link.locOne_open
#print axioms Johnson.Prover.Link.link_open
#print axioms Johnson.Prover.Link.phi_open
#print axioms Johnson.Prover.Link.poss_of_fit
#print axioms Johnson.Prover.Link.front6_all
