-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/G4/RunLaws.lean: on plain data that fit, the program's lookup verifier, run at the least
caller, goes through, and it hands on as many end claims as the public inputs say.

The first law (`portOn_ok`). Let S be public inputs of a lookup that meet the premises below, and t
plain data (Flat, OnBytes/G4/Flat.lean) with t.fits S = true. Then portOn S t, the run of the
caller's block (Lkp.verify, then the caller's row on the keys) on t's rounds, gives a value, and the
rows that it has added to the group are so many rows, each of which is `Fine`. t.fits asks for
numbers of elements, for words below p (of the three vectors and of what is drawn, not of what a
round sends) and for draws that are not 0 where the plan says so; it asks nothing else of a value.
(By a reading of the proof: meets_of_fits, the one place where a round's fits is opened, takes the
two numbers of elements.) So whether the block goes through does not hang on what the prover sends
or on what is drawn. What the run finds goes into the rows; whether these hold is another question
(judge).
The second law (`endClaims_some`). For the same S and t, endClaims S t is a list of 1 + (planes - 2)
+ v + d + 5 end claims: every row reads nothing but the caller's three vectors (`onCaller_of_fine`).

The premises on S.
 - `Shaped`, with `Sized` in it, and that the lengths of the made-up statement's codes are powers of
   two (Blk.runNamed asks it): facts on public numbers alone, each of which can be evaluated: one
   part, no shift, which messages are read, the sizes of the caller's three tables, the length of
   the last key level's order, the degrees at the leaves, that the plan's entries are the blocks'
   entries in their order (`blockEntries`), and that the mask row is long enough.
 - `PaddingOut`: NOT a fact on public numbers: a statement for all alpha and all claims at a point
   of v coordinates: the claim on the keys, as the program reckons it, has the coefficient 0 on
   every place of padding. It speaks of no transcript. It is what the last clause of onCaller, a
   test on a value, asks. NEITHER IS PROVED OF ANY PUBLIC INPUTS, here or elsewhere in the library,
   not even of a small example: so the laws that ask them (`run_at`, `block_at`, `portOn_ok`,
   `endClaims_some`; `run_val`, `portOn_eq`, `endClaims_eq` in OnBytes/G4/RunValues.lean) are
   applied at no public inputs.

How it is proved. `ctxAt` spells the context in the middle of the run: the entries and rounds that
are left, the number of mask entries taken, the rows added. For each call of the block there is an
equation or an "there is" on such contexts, whatever the values: receiving and closing a round
(recvEs_fresh, close_opened, hearDraw_at, hearOne_at), the rounds of a sumcheck (hear_at), mask
entries (takeSlots_at, fresh_at), rows (addRow_at, leave_at, with `Fine`: a row that the caller's
group takes; `Added`: so many such rows more), what a sumcheck computes (run_some, with the length
of the form of its first polynomial, hidingWalk_length), one sumcheck (psc_at), a line (line_at: the
one test on values in the course compares a point with itself), the levels of a tree
(levelChain_at), the tie (tieSteps_at), the claim on the keys (keysOf_fits, fine_keysRow), the whole
lookup (run_at), the caller's block (block_at).

Main definitions: statementAt, ctxAt, NoRows, Meets, FitsAll, SlotsOK, Fine, Sized, Added, OutOK,
ClaimOK, MapsOK, chainEntries, chainMasks, tieEntries, blockEntries, Shaped, PaddingOut.
Main theorems: portOn_ok, endClaims_some, onCaller_of_fine, block_at, run_at, levelChain_at,
tieSteps_at, psc_at, run_some.
Not claimed. Nothing on soundness. THE LAWS ARE AT THE LEAST CALLER OF Flat.lean, WHICH NO PROGRAM
HAS. The one caller of Lkp.verify in the program (OnBytes/Iop/Wf.lean) differs in two ways that
matter here: its messages have pads, and Blk.addRow's test on these is a test on values; and it
passes keyMasks := some …, so that the last key level's two mask entries come from a second message
with a ledger of its own. Nothing is claimed there. For a lookup of a key's one-time chain cite the
laws of the namespace `Caller.Laws` (OnBytes/G4/AnyCaller.lean, OnBytes/G4/AnyCourse.lean,
OnBytes/G4/AnyRun.lean): the laws of this file that ask `Shaped`, or that two messages are read, say
nothing there. Nothing on what the rows say. Only at work = 0 in the plan's entries (the run does
not read that number). The converse (data that do not fit are refused) is not claimed and is false:
the block tests neither that words are below p nor that a draw is not 0.


-/
import OnBytes.G4.FlatLaws

set_option autoImplicit false

namespace OnBytes.G4

open Blk

/-! ## How a block is applied to a context -/

theorem bind_ok {α β : Type} {x : Blk α} {f : α → Blk β} {c c' : Ctx} {a : α}
    (h : x c = .ok (a, c')) : (x >>= f) c = f a c' := by
  show (x c >>= fun p => f p.1 p.2) = _
  rw [h]
  rfl

theorem pure_ok {α : Type} (a : α) (c : Ctx) : (pure a : Blk α) c = .ok (a, c) := rfl

theorem must_ok {b : Bool} (h : b = true) (c : Ctx) : (Blk.must b) c = .ok ((), c) := by
  subst h
  rfl

theorem get_ok {α : Type} (a : α) (c : Ctx) : (Blk.get (some a)) c = .ok (a, c) := rfl

theorem test_ok {b : Bool} (h : b = true) (c : Ctx) : (Blk.test b) c = .ok ((), c) := by
  subst h
  rfl

/-! ## The contexts of the run -/

/-- The statement in the middle of the run: k mask entries are taken, and the group has these rows.
-/
def statementAt (S : Lkp.Public) (k : Nat) (rows : Array Row) : Statement :=
  let c := min S.firstBits (S.mu + S.d)
  { codes := { base := #[⟨12, 2 ^ c, 4⟩], mask := #[⟨12, 2 ^ ceilLog2 (Lkp.allMasks S), 4⟩] }
    oracles := #[
      { shape := { code := 0, mainRows := 2 ^ (S.firstBits - c), mainDeg := 3 }, sampled := true,
        groups := [theGroup] },
      { shape := { code := 0, mainRows := 2 ^ (S.mu + S.d - c), mainDeg := 3 }, sampled := true,
        groups := [theGroup] },
      { shape := { maskRows := 1 }, sampled := true, groups := [theGroup],
        ledger := some { next := k, left := Lkp.allMasks S - k, rows := 1, logRows := 0 } }]
    groups := #[{ code := 0, members := #[keysMessage, planesMessage, masksMessage],
                  kept := #[false, false, false], rows := rows }] }

theorem statement_eq (S : Lkp.Public) : statement S = statementAt S 0 #[] := rfl

/-- The context in the middle of the run. -/
def ctxAt (S : Lkp.Public) (es : List Fmt.Entry) (cur : Option Fmt.RoundView) (rs : List Fmt.RoundView)
    (last : Option Fmt.Entry) (k : Nat) (rows : Array Row) : Ctx where
  ch := { dry := false, entries := es, left := rs, cur := cur, last := last }
  st := statementAt S k rows

/-- The entry of the round closed last counts no batched rows. -/
def NoRows (last : Option Fmt.Entry) : Prop := ∀ e, last = some e → e.rows = 0

theorem settled_of_noRows {S : Lkp.Public} {es cur rs last k rows} (h : NoRows last) :
    (ctxAt S es cur rs last k rows).ch.settled = true := by
  unfold Chan.settled ctxAt
  cases last with
  | none => rfl
  | some e => simp [h e rfl]

/-! ## Receiving and closing -/

/-- Receiving elements from a message that is open. -/
theorem recvEsInto_open (S : Lkp.Public) (es rs last k rows) (d : Fmt.Drawn) :
    ∀ (xs : List E) (rest : List Fmt.ItemValue) (acc : Array E),
      Blk.recvEsInto xs.length acc
          (ctxAt S es (some ⟨xs.map (fun x => Fmt.ItemValue.e x.triple) ++ rest, d⟩) rs last k rows) =
        .ok (acc ++ xs.toArray, ctxAt S es (some ⟨rest, d⟩) rs last k rows)
  | [], rest, acc => by simp [Blk.recvEsInto, pure_ok]
  | x :: xs, rest, acc => by
    have h1 : Blk.recvE
        (ctxAt S es (some ⟨(x :: xs).map (fun x => Fmt.ItemValue.e x.triple) ++ rest, d⟩) rs last k rows) =
        .ok (x, ctxAt S es (some ⟨xs.map (fun x => Fmt.ItemValue.e x.triple) ++ rest, d⟩) rs last k rows) := rfl
    show (Blk.recvE >>= fun y => Blk.recvEsInto xs.length (acc.push y)) _ = _
    rw [bind_ok h1, recvEsInto_open S es rs last k rows d xs rest (acc.push x)]
    simp

/-- What the channel holds of a round after its elements are received: if there are none, the round
is not yet begun. -/
def openedCur (r : FlatRound) : Option Fmt.RoundView := if r.sent.isEmpty then none else some ⟨[], r.rv.drawn⟩

/-- The rounds that are not yet begun, after a round's elements are received. -/
def openedLeft (r : FlatRound) (rs : List Fmt.RoundView) : List Fmt.RoundView :=
  if r.sent.isEmpty then r.rv :: rs else rs

/-- Receiving all elements of a round that is not yet begun. -/
theorem recvEs_fresh (S : Lkp.Public) (es rs last k rows) (r : FlatRound) :
    (Blk.recvEs r.sent.length) (ctxAt S es none (r.rv :: rs) last k rows) =
      .ok (r.sent, ctxAt S es (openedCur r) (openedLeft r rs) last k rows) := by
  obtain ⟨sent, drawn⟩ := r
  cases sent with
  | nil => rfl
  | cons x xs =>
    have h1 : Blk.recvE (ctxAt S es none ((⟨x :: xs, drawn⟩ : FlatRound).rv :: rs) last k rows) =
        .ok (x, ctxAt S es (some ⟨xs.map (fun x => Fmt.ItemValue.e x.triple) ++ [],
          (⟨x :: xs, drawn⟩ : FlatRound).rv.drawn⟩) rs last k rows) := by
      simp only [List.append_nil]
      rfl
    show ((Blk.recvE >>= fun y => Blk.recvEsInto xs.length ((#[] : Array E).push y)) >>=
      fun a => pure a.toList) _ = _
    have h2 : (Blk.recvE >>= fun y => Blk.recvEsInto xs.length ((#[] : Array E).push y))
        (ctxAt S es none ((⟨x :: xs, drawn⟩ : FlatRound).rv :: rs) last k rows) =
        .ok ((#[] : Array E).push x ++ xs.toArray,
          ctxAt S es (some ⟨[], (⟨x :: xs, drawn⟩ : FlatRound).rv.drawn⟩) rs last k rows) := by
      rw [bind_ok h1]
      exact recvEsInto_open S es rs last k rows _ xs [] _
    rw [bind_ok h2]
    simp [pure_ok, openedCur, openedLeft]

/-- Closing a round whose elements are received. -/
theorem close_opened (S : Lkp.Public) (e : Fmt.Entry) (es rs last k rows) (r : FlatRound)
    (name : String) (kind : Fmt.Kind) (nz : Nat) (hn : e.name = name) (hz : e.drawNZ = nz)
    (hq : NoRows last) (hd : r.drawn.length = e.drawE) (hp : e.poss = 0) (ht : e.trits = 0) :
    (Blk.close name kind nz) (ctxAt S (e :: es) (openedCur r) (openedLeft r rs) last k rows) =
      .ok (r.rv.drawn, ctxAt S es none rs (some e) k rows) := by
  have hs := settled_of_noRows (S := S) (es := e :: es) (cur := openedCur r)
    (rs := openedLeft r rs) (k := k) (rows := rows) hq
  obtain ⟨sent, drawn⟩ := r
  cases sent with
  | nil =>
    unfold Blk.close
    simp [ctxAt, openedCur, openedLeft, FlatRound.rv, hn, hz, hp, ht] at hs hd ⊢
    simp [hs, hd]
  | cons x xs =>
    unfold Blk.close
    simp [ctxAt, openedCur, openedLeft, FlatRound.rv, hn, hz, hp, ht] at hs hd ⊢
    simp [hs, hd]

/-- The elements of a round's record of what was drawn, read back. -/
theorem drawn_elems (r : FlatRound) : r.rv.drawn.elems.map E.ofTriple = r.drawn :=
  map_ofTriple_triple r.drawn

/-- What a round must meet so that a block can read it under an entry. -/
structure Meets (r : FlatRound) (e : Fmt.Entry) (name : String) (n draws nz : Nat) : Prop where
  name : e.name = name
  nz : e.drawNZ = nz
  drawE : e.drawE = draws
  poss : e.poss = 0
  trits : e.trits = 0
  rows : e.rows = 0
  sent : r.sent.length = n
  drawn : r.drawn.length = draws

theorem Meets.noRows {r e name n draws nz} (h : Meets r e name n draws nz) : NoRows (some e) := by
  intro x hx
  cases hx
  exact h.rows

/-- A round in which nothing is sent and n elements are drawn. -/
theorem hearDraw_at (S : Lkp.Public) (e : Fmt.Entry) (es rs last k rows) (r : FlatRound)
    (name : String) (n : Nat) (h : Meets r e name 0 n 0) (hq : NoRows last) :
    (hearDraw name n) (ctxAt S (e :: es) none (r.rv :: rs) last k rows) =
      .ok (r.drawn, ctxAt S es none rs (some e) k rows) := by
  have hs : r.sent = [] := List.length_eq_zero_iff.1 h.sent
  have hc := close_opened S e es rs last k rows r name .elems 0 h.name h.nz hq
    (h.drawn.trans h.drawE.symm) h.poss h.trits
  simp only [openedCur, openedLeft, hs, List.isEmpty_nil, if_true] at hc
  have h1 : (Blk.closeElems name) (ctxAt S (e :: es) none (r.rv :: rs) last k rows) =
      .ok (r.drawn, ctxAt S es none rs (some e) k rows) := by
    show ((Blk.close name .elems 0) >>= fun d => pure (d.elems.map E.ofTriple)) _ = _
    rw [bind_ok hc, pure_ok, drawn_elems]
  show ((Blk.closeElems name) >>= fun l => (Blk.must (l.length == n)) >>= fun _ => pure l) _ = _
  rw [bind_ok h1, bind_ok (must_ok (by simp [h.drawn]) _), pure_ok]

/-- A round in which n elements are sent and one is drawn. -/
theorem hearOne_at (S : Lkp.Public) (e : Fmt.Entry) (es rs last k rows) (r : FlatRound)
    (name : String) (kind : Fmt.Kind) (n nz : Nat) (h : Meets r e name n 1 nz) (hq : NoRows last) :
    ∃ g, r.drawn = [g] ∧ (Psc.hearOne name kind n nz) (ctxAt S (e :: es) none (r.rv :: rs) last k rows) =
      .ok ((r.sent, g), ctxAt S es none rs (some e) k rows) := by
  obtain ⟨g, hg⟩ := List.length_eq_one_iff.1 h.drawn
  refine ⟨g, hg, ?_⟩
  have hc := close_opened S e es rs last k rows r name kind nz h.name h.nz hq
    (h.drawn.trans h.drawE.symm) h.poss h.trits
  have h1 : (Blk.closeOne name kind nz) (ctxAt S (e :: es) (openedCur r) (openedLeft r rs) last k rows) =
      .ok (g, ctxAt S es none rs (some e) k rows) := by
    unfold Blk.closeOne
    rw [bind_ok hc]
    simp [FlatRound.rv, hg, pure_ok, E.ofTriple_triple]
  show ((Blk.recvEs n) >>= fun q => (Blk.closeOne name kind nz) >>= fun g => pure (q, g)) _ = _
  rw [← h.sent, bind_ok (recvEs_fresh S (e :: es) rs last k rows r), bind_ok h1, pure_ok]

/-! ## Rounds that fit their entries -/

/-- The rounds fit the entries, one by one, and there are as many. -/
def FitsAll : List FlatRound → List Fmt.Entry → Prop
  | [], [] => True
  | r :: rs, e :: es => r.fits e = true ∧ FitsAll rs es
  | _, _ => False

/-- A round that fits an entry without positions, matrix entries and batched rows can be read. -/
theorem meets_of_fits {r : FlatRound} {e : Fmt.Entry} {name : String} {n draws nz : Nat}
    (h : r.fits e = true) (h1 : e.name = name) (h2 : e.msg = 24 * n) (h3 : e.drawE = draws)
    (h4 : e.drawNZ = nz) (h5 : e.poss = 0) (h6 : e.trits = 0) (h7 : e.rows = 0) :
    Meets r e name n draws nz := by
  simp only [FlatRound.fits, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h1, h4, h3, h5, h6, h7, by omega, by omega⟩

/-- The views' rounds. -/
abbrev rvs (rs : List FlatRound) : List Fmt.RoundView := rs.map FlatRound.rv

/-- The rounds of the variables of a sumcheck. -/
theorem hearMany_at (S : Lkp.Public) (work k : Nat) (rows : Array Row) (es' : List Fmt.Entry) :
    ∀ (ns : List Nat) (rs : List FlatRound) (last : Option Fmt.Entry), NoRows last →
      FitsAll rs (ns.map (fun n => (Psc.rOne "PSC round" .elems work n 0).entry) ++ es') →
      ∃ l rs' last', FitsAll rs' es' ∧ NoRows last' ∧
        (Psc.hearMany ns) (ctxAt S (ns.map (fun n => (Psc.rOne "PSC round" .elems work n 0).entry) ++ es')
          none (rvs rs) last k rows) = .ok (l, ctxAt S es' none (rvs rs') last' k rows) ∧
        l.map (fun p => p.1.length) = ns
  | [], rs, last, hq, h => ⟨[], rs, last, h, hq, rfl, rfl⟩
  | n :: ns, [], last, hq, h => by simp [FitsAll] at h
  | n :: ns, r :: rs, last, hq, h => by
    obtain ⟨hr, hrest⟩ := h
    have hm : Meets r (Psc.rOne "PSC round" .elems work n 0).entry "PSC round" n 1 0 :=
      meets_of_fits hr rfl rfl rfl rfl rfl rfl rfl
    obtain ⟨g, _, h1⟩ := hearOne_at S _ (ns.map (fun n => (Psc.rOne "PSC round" .elems work n 0).entry) ++ es')
      (rvs rs) last k rows r "PSC round" .elems n 0 hm hq
    obtain ⟨l, rs', last', hf, hq', h2, hl⟩ := hearMany_at S work k rows es' ns rs _ hm.noRows hrest
    refine ⟨(r.sent, g) :: l, rs', last', hf, hq', ?_, by simp [hl, hm.sent]⟩
    show ((Psc.hearOne "PSC round" .elems n 0) >>= fun a => (Psc.hearMany ns) >>= fun l => pure (a :: l)) _ = _
    rw [show (List.map (fun n => (Psc.rOne "PSC round" .elems work n 0).entry) (n :: ns) ++ es') =
      (Psc.rOne "PSC round" .elems work n 0).entry ::
        (ns.map (fun n => (Psc.rOne "PSC round" .elems work n 0).entry) ++ es') from rfl]
    rw [show rvs (r :: rs) = r.rv :: rvs rs from rfl, bind_ok h1, bind_ok h2, pure_ok]

/-- The round of the shown values. -/
theorem hearValues_at {β : Type} (f : List E → Blk β) (S : Lkp.Public) (e : Fmt.Entry)
    (es rs last k rows) (r : FlatRound) (n : Nat)
    (h : Meets r e "PSC values" n 0 0) (hq : NoRows last) :
    ((Blk.recvEs n) >>= fun values => (Blk.closeEmpty "PSC values") >>= fun _ => f values)
      (ctxAt S (e :: es) none (r.rv :: rs) last k rows) =
      f r.sent (ctxAt S es none rs (some e) k rows) := by
  have hc := close_opened S e es rs last k rows r "PSC values" .nothing 0 h.name h.nz hq
    (h.drawn.trans h.drawE.symm) h.poss h.trits
  have h1 : (Blk.closeEmpty "PSC values") (ctxAt S (e :: es) (openedCur r) (openedLeft r rs) last k rows) =
      .ok ((), ctxAt S es none rs (some e) k rows) := by
    show ((Blk.close "PSC values" .nothing) >>= fun _ => pure ()) _ = _
    rw [bind_ok hc, pure_ok]
  rw [← h.sent, bind_ok (recvEs_fresh S (e :: es) rs last k rows r), bind_ok h1]

/-- The entries of a sumcheck's rounds. -/
abbrev pscEntries (work : Nat) (x : Psc.Size) : List Fmt.Entry := (Psc.roundsOf work x).map (·.entry)

theorem pscEntries_eq (work : Nat) (x : Psc.Size) (es' : List Fmt.Entry) :
    pscEntries work x ++ es' =
      (Psc.rOne "PSC epsilon" .join work 1 0).entry ::
        ((x.degree.map (· - 1)).map (fun n => (Psc.rOne "PSC round" .elems work n 0).entry) ++
          ((if x.withY then [(Psc.rOne "PSC Y" .elems work x.degreeY 1).entry, (Psc.rValues x.values).entry]
            else []) ++ es')) := by
  unfold pscEntries Psc.roundsOf
  cases x.withY <;> simp [List.map_map, Function.comp_def]

/-- Reading the rounds of a sumcheck. -/
theorem hear_at (S : Lkp.Public) (work k : Nat) (rows : Array Row) (x : Psc.Size)
    (es' : List Fmt.Entry) (rs : List FlatRound) (last : Option Fmt.Entry) (hq : NoRows last)
    (h : FitsAll rs (pscEntries work x ++ es')) :
    ∃ hd rs' last', FitsAll rs' es' ∧ NoRows last' ∧
      (Psc.hear x) (ctxAt S (pscEntries work x ++ es') none (rvs rs) last k rows) =
        .ok (hd, ctxAt S es' none (rvs rs') last' k rows) ∧
      hd.rounds.map (fun p => p.1.length) =
        x.degree.map (· - 1) ++ (if x.withY then [x.degreeY] else []) ∧
      hd.values.length = (if x.withY then x.values else 0) := by
  rw [pscEntries_eq] at h ⊢
  cases rs with
  | nil => simp [FitsAll] at h
  | cons r rs =>
    obtain ⟨hr, hrest⟩ := h
    have hm : Meets r (Psc.rOne "PSC epsilon" .join work 1 0).entry "PSC epsilon" 1 1 0 :=
      meets_of_fits hr rfl rfl rfl rfl rfl rfl rfl
    obtain ⟨eps, _, h1⟩ := hearOne_at S _ _ (rvs rs) last k rows r "PSC epsilon" .join 1 0 hm hq
    obtain ⟨mu, hmu⟩ := List.length_eq_one_iff.1 hm.sent
    obtain ⟨inX, rs1, last1, hf1, hq1, h2, hl⟩ := hearMany_at S work k rows _ _ rs _ hm.noRows hrest
    unfold Psc.hear
    rw [show rvs (r :: rs) = r.rv :: rvs rs from rfl, bind_ok h1]
    simp only [hmu, List.head?_cons]
    rw [bind_ok (get_ok mu _), bind_ok h2]
    cases hY : x.withY with
    | false =>
      simp only [hY, Bool.false_eq_true, if_false, List.nil_append, List.append_nil] at hf1 ⊢
      exact ⟨_, rs1, last1, hf1, hq1, rfl, hl, rfl⟩
    | true =>
      simp only [hY, if_true, List.cons_append, List.nil_append] at hf1 ⊢
      cases rs1 with
      | nil => simp [FitsAll] at hf1
      | cons rY rs2 =>
        obtain ⟨hrY, hf2⟩ := hf1
        cases rs2 with
        | nil => simp [FitsAll] at hf2
        | cons rV rs3 =>
          obtain ⟨hrV, hf3⟩ := hf2
          have hmY : Meets rY (Psc.rOne "PSC Y" .elems work x.degreeY 1).entry "PSC Y" x.degreeY 1 1 :=
            meets_of_fits hrY rfl rfl rfl rfl rfl rfl rfl
          have hmV : Meets rV (Psc.rValues x.values).entry "PSC values" x.values 0 0 :=
            meets_of_fits hrV rfl rfl rfl rfl rfl rfl rfl
          obtain ⟨beta, _, h3⟩ := hearOne_at S _ ((Psc.rValues x.values).entry :: es') (rvs (rV :: rs3))
            last1 k rows rY "PSC Y" .elems x.degreeY 1 hmY hq1
          refine ⟨⟨mu, eps, inX ++ [(rY.sent, beta)], rV.sent⟩, rs3, _, hf3, hmV.noRows, ?_, ?_, hmV.sent⟩
          · rw [show rvs (rY :: rV :: rs3) = rY.rv :: rvs (rV :: rs3) from rfl, bind_ok h3]
            rw [show rvs (rV :: rs3) = rV.rv :: rvs rs3 from rfl]
            exact hearValues_at _ S _ es' (rvs rs3) _ k rows rV x.values hmV hmY.noRows
          · simp [hl, hmY.sent]

/-! ## Mask entries -/

/-- The oracle message with the mask row, after k entries are taken. -/
def maskOracle (S : Lkp.Public) (k : Nat) : Oracle where
  shape := { maskRows := 1 }
  sampled := true
  groups := [theGroup]
  ledger := some { next := k, left := Lkp.allMasks S - k, rows := 1, logRows := 0 }

/-- Taking one mask entry. -/
theorem takeMask_at (S : Lkp.Public) (es rs last k rows) (h : k < Lkp.allMasks S) :
    (Blk.takeMask masksMessage) (ctxAt S es none rs last k rows) =
      .ok (k, ctxAt S es none rs last (k + 1) rows) := by
  have hl : (!false && decide (0 < Lkp.allMasks S - k)) = true := by simp; omega
  have hn : nextRealRow 1 0 (2 ^ 0) k = k := by simp [nextRealRow, Nat.mod_one]
  have h1 : (Blk.oracle masksMessage) (ctxAt S es none rs last k rows) =
      .ok (maskOracle S k, ctxAt S es none rs last k rows) := rfl
  unfold Blk.takeMask
  rw [bind_ok h1]
  simp only [maskOracle]
  rw [bind_ok (get_ok _ _), bind_ok (must_ok hl _)]
  simp only [hn]
  have h2 : ∀ f : Oracle → Oracle, f (maskOracle S k) = maskOracle S (k + 1) →
      (Blk.onOracle masksMessage f) (ctxAt S es none rs last k rows) =
        .ok ((), ctxAt S es none rs last (k + 1) rows) := by
    intro f hf
    simp only [maskOracle] at hf
    simp [Blk.onOracle, ctxAt, statementAt, masksMessage, hf]
  rw [bind_ok (h2 _ (by simp [maskOracle, Nat.sub_sub]))]
  rfl

/-- Taking n mask entries. -/
theorem takeMasksInto_at (S : Lkp.Public) (es rs last rows) :
    ∀ (n k : Nat) (acc : Array Nat), k + n ≤ Lkp.allMasks S →
      (Blk.takeMasksInto masksMessage n acc) (ctxAt S es none rs last k rows) =
        .ok (acc ++ (List.range' k n).toArray, ctxAt S es none rs last (k + n) rows)
  | 0, k, acc, _ => by simp [Blk.takeMasksInto, pure_ok]
  | n + 1, k, acc, h => by
    show ((Blk.takeMask masksMessage) >>= fun a => Blk.takeMasksInto masksMessage n (acc.push a)) _ = _
    rw [bind_ok (takeMask_at S es rs last k rows (by omega)),
      takeMasksInto_at S es rs last rows n (k + 1) (acc.push k) (by omega)]
    rw [show k + 1 + n = k + (n + 1) from by omega]
    congr 2
    apply Array.toList_inj.mp
    simp [List.range'_succ]

/-- The mask entries number k to k + n - 1 of the caller's mask row. -/
def slotsFrom (k n : Nat) : List Slot := (List.range' k n).map fun i => ⟨masksMessage, i⟩

/-- Taking n mask entries as slots. -/
theorem takeSlots_at (S : Lkp.Public) (es rs last rows) (n k : Nat) (h : k + n ≤ Lkp.allMasks S) :
    (takeSlots masksMessage n) (ctxAt S es none rs last k rows) =
      .ok (slotsFrom k n, ctxAt S es none rs last (k + n) rows) := by
  show (((Blk.takeMasksInto masksMessage n #[]) >>= fun a => pure a.toList) >>=
    fun l => pure (l.map fun i => (⟨masksMessage, i⟩ : Slot))) _ = _
  rw [bind_ok (bind_ok (takeMasksInto_at S es rs last rows n k #[] h))]
  simp [pure_ok, slotsFrom]

theorem slotsFrom_length (k n : Nat) : (slotsFrom k n).length = n := by simp [slotsFrom]

/-! ## Rows -/

/-- Every entry of a mask form is one that the lookup can take from the caller's mask row. -/
def SlotsOK (S : Lkp.Public) (m : MaskForm) : Prop :=
  ∀ p ∈ m, p.1.oracle = masksMessage ∧ p.1.index < Lkp.allMasks S

/-- A row that the caller's group takes. -/
structure Fine (S : Lkp.Public) (row : Row) : Prop where
  kind : row.kind = .plain
  terms : ∀ t ∈ row.terms, t.oracle = planesMessage ∧ t.part = .main ∧ t.v.vars = S.mu + S.d ∧ t.v.ok = true
  units : ∀ u ∈ row.units, u.oracle = masksMessage ∧ u.part = .mask ∧ u.index < Lkp.allMasks S
  runs : row.runs = #[]
  forms : ∀ f ∈ row.forms, f.oracle = keysMessage ∧ f.c.fits S.firstBits = true
  atPadding : ∀ i, i < 2 ^ S.firstBits → isPadding S i = true →
    isZeroE (row.coefficient keysMessage .main i) = true

/-- What is asked of the sizes of the caller's three tables. -/
structure Sized (S : Lkp.Public) : Prop where
  planes : (statementAt S 0 #[]).tableBits planesMessage .main = S.mu + S.d
  keys : (statementAt S 0 #[]).tableBits keysMessage .main = S.firstBits
  masks : Lkp.allMasks S ≤ 2 ^ (statementAt S 0 #[]).tableBits masksMessage .mask
  hasPlanes : (statementAt S 0 #[]).has planesMessage .main = true
  hasKeys : (statementAt S 0 #[]).has keysMessage .main = true
  hasMasks : (statementAt S 0 #[]).has masksMessage .mask = true
  small : S.mu + S.d ≤ 63

/-- The caller's group with these rows. -/
def groupAt (rows : Array Row) : Group where
  code := 0
  members := #[keysMessage, planesMessage, masksMessage]
  kept := #[false, false, false]
  rows := rows

/-- Adding a row to the caller's group. -/
theorem addRow_at (S : Lkp.Public) (hS : Sized S) (es rs last k rows) (row : Row) (h : Fine S row) :
    (Blk.addRow theGroup row) (ctxAt S es none rs last k rows) =
      .ok ((), ctxAt S es none rs last k (rows.push row)) := by
  have h0 : Blk.statement (ctxAt S es none rs last k rows) =
      .ok (statementAt S k rows, ctxAt S es none rs last k rows) := rfl
  have h1 : (Blk.group theGroup) (ctxAt S es none rs last k rows) =
      .ok (groupAt rows, ctxAt S es none rs last k rows) := rfl
  have h2 : Blk.isDry (ctxAt S es none rs last k rows) = .ok (false, ctxAt S es none rs last k rows) := rfl
  have tP : (statementAt S k rows).tableBits planesMessage .main = S.mu + S.d := hS.planes
  have tK : (statementAt S k rows).tableBits keysMessage .main = S.firstBits := hS.keys
  have tM : Lkp.allMasks S ≤ 2 ^ (statementAt S k rows).tableBits masksMessage .mask := hS.masks
  have aP : (statementAt S k rows).has planesMessage .main = true := hS.hasPlanes
  have aK : (statementAt S k rows).has keysMessage .main = true := hS.hasKeys
  have aM : (statementAt S k rows).has masksMessage .mask = true := hS.hasMasks
  have mK : keysMessage ∈ (groupAt rows).members := by simp [groupAt]
  have mP : planesMessage ∈ (groupAt rows).members := by simp [groupAt]
  have mM : masksMessage ∈ (groupAt rows).members := by simp [groupAt]
  have hT : (row.terms.all fun t =>
      t.v.ok && placeOk (statementAt S k rows) (groupAt rows) t.oracle t.part t.v.vars 0) = true := by
    rw [Array.all_eq_true_iff_forall_mem]
    intro t ht
    obtain ⟨a, b, c, d⟩ := h.terms t ht
    simp [placeOk, a, b, c, d, mP, aP, tP, Nat.two_pow_pos]
  have hU : (row.units.all fun u => placeOk (statementAt S k rows) (groupAt rows) u.oracle u.part
      ((statementAt S k rows).tableBits u.oracle u.part) u.index) = true := by
    rw [Array.all_eq_true_iff_forall_mem]
    intro u hu
    obtain ⟨a, b, c⟩ := h.units u hu
    simp [placeOk, a, b, mM, aM]
    exact Nat.lt_of_lt_of_le c tM
  have hF : (row.forms.all fun f =>
      placeOk (statementAt S k rows) (groupAt rows) f.oracle .main
        ((statementAt S k rows).tableBits f.oracle .main) 0 &&
      f.c.fits ((statementAt S k rows).tableBits f.oracle .main)) = true := by
    rw [Array.all_eq_true_iff_forall_mem]
    intro f hf
    obtain ⟨a, b⟩ := h.forms f hf
    simp [placeOk, a, b, mK, aK, tK, Nat.two_pow_pos]
  unfold Blk.addRow
  rw [bind_ok h0, bind_ok h1, bind_ok (must_ok (by simp [groupAt, h.kind]) _), bind_ok h2]
  simp only [Bool.false_eq_true, if_false]
  rw [bind_ok (pure_ok _ _), bind_ok (must_ok hT _), bind_ok (must_ok hU _),
    bind_ok (must_ok (by simp [h.runs]) _), bind_ok (must_ok hF _),
    bind_ok (test_ok (by simp [groupAt, statementAt, keysMessage, planesMessage, masksMessage]) _)]
  rfl

/-- What the steps of the lookup are told, as Lkp.verify tells them for the least caller. -/
def envOf (S : Lkp.Public) : Lkp.Env where
  S := S
  planesAt := fun row v => row.add planesMessage .main v
  masks := masksMessage
  keyMasks := masksMessage
  group := theGroup

/-- A row goes into the group through the lookup's own door. -/
theorem leave_at (S : Lkp.Public) (hS : Sized S) (hR : S.readFrom = [keysMessage, planesMessage])
    (es rs last k rows) (row : Row) (h : Fine S row) :
    (Lkp.leave (envOf S) row) (ctxAt S es none rs last k rows) =
      .ok ((), ctxAt S es none rs last k (rows.push row)) := by
  have hd : ((row.terms.all fun t => t.part != .main || (envOf S).S.readFrom.contains t.oracle) &&
      (row.units.all fun t => t.part != .main || (envOf S).S.readFrom.contains t.oracle) &&
      (row.runs.all fun t => t.part != .main || (envOf S).S.readFrom.contains t.oracle) &&
      row.forms.all fun t => (envOf S).S.readFrom.contains t.oracle) = true := by
    simp only [Bool.and_eq_true, Array.all_eq_true_iff_forall_mem]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · intro t ht
      simp [envOf, hR, (h.terms t ht).1]
    · intro u hu
      simp [(h.units u hu).2.1]
    · intro x hx
      simp [h.runs] at hx
    · intro f hf
      simp [envOf, hR, (h.forms f hf).1]
  show ((Blk.must _) >>= fun _ => Blk.addRow (envOf S).group row) _ = _
  rw [bind_ok (must_ok hd _)]
  exact addRow_at S hS es rs last k rows row h

/-! ## What a sumcheck computes -/

theorem powersLoop_length (x : E) : ∀ (n : Nat) (c : E) (done : List E),
    (Psc.powersLoop x n c done).length = done.length + n
  | 0, _, done => by simp [Psc.powersLoop]
  | n + 1, c, done => by
    rw [Psc.powersLoop, powersLoop_length x n]
    simp
    omega

theorem powers_length (c x : E) (n : Nat) : (Psc.powers c x n).length = n := by
  simp [Psc.powers, powersLoop_length]

/-- The hiding polynomial's linear form has as many coefficients as Psc.hidingEntries says. -/
theorem hidingWalk_length : ∀ (l : List (Psc.Weight × E)), l ≠ [] → (∀ p ∈ l, 1 ≤ p.1.d) →
    (Psc.hidingWalk l).1.length = 1 + (l.map fun p => p.1.d - 1).sum
  | [], h, _ => absurd rfl h
  | [(w, g)], _, hd => by
    have h1 : 1 ≤ w.d := hd (w, g) (by simp)
    simp only [Psc.hidingWalk, powers_length, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  | (w, g) :: q :: rest, _, hd => by
    have ih := hidingWalk_length (q :: rest) (by simp) (fun p hp => hd p (by simp [hp]))
    simp only [Psc.hidingWalk, List.length_append, powers_length, ih, List.map_cons, List.sum_cons]
    omega

/-- The sizes of the rounds fit the weights. -/
theorem sizes_fit : ∀ (vars : List Psc.Weight) (rounds : List (List E × E)),
    rounds.map (fun p => p.1.length) = vars.map (fun w => w.d - 1) → (∀ w ∈ vars, 1 ≤ w.d) →
    ((vars.zip rounds).all fun p => p.2.1.length + 1 == p.1.d) = true
  | [], _, _, _ => by simp
  | _ :: _, [], h, _ => by simp at h
  | w :: ws, r :: rs, h, hd => by
    simp only [List.map_cons, List.cons.injEq] at h
    have h1 := hd w (by simp)
    have ih := sizes_fit ws rs h.2 (fun x hx => hd x (by simp [hx]))
    simp only [List.zip_cons_cons, List.all_cons, ih, Bool.and_true, beq_iff_eq]
    omega

/-- What is known of what a sumcheck hands on, whatever the values. -/
structure OutOK (c : Psc.Claim) (Sm : Psc.Summand) (fr : List Slot) (o : Psc.Out) : Prop where
  point : o.point.length = c.vars.length
  maps : o.rowMaps.length = Sm.kept
  ends : o.ends.length = Sm.shown
  endsAt : ∀ e ∈ o.ends, e.point = o.point ∧ ∀ p ∈ e.masks, p.1 ∈ fr
  masks : ∀ p ∈ o.rowMasks, p.1 ∈ fr ∨ p.1 ∈ c.masks.map (·.1)

/-- A sumcheck's computation gives something wherever the sizes fit, whatever the values. -/
theorem run_some (c : Psc.Claim) (Sm : Psc.Summand) (fr : List Slot) (h : Psc.Heard)
    (hform : Psc.formOK c Sm = true) (hfr : fr.length = Psc.masksOf c Sm)
    (hl : h.rounds.map (fun p => p.1.length) = (Psc.varsOf c Sm).map (fun w => w.d - 1))
    (hv : h.values.length = Sm.shown) (ha : ∀ p y, (Sm.coeffs p y).length = 1 + Sm.kept)
    (hd : ∀ w ∈ Psc.varsOf c Sm, 1 ≤ w.d) (hne : Psc.varsOf c Sm ≠ [])
    (hle : c.vars.length ≤ (Psc.varsOf c Sm).length) :
    ∃ o, Psc.run c Sm fr h = some o ∧ OutOK c Sm fr o := by
  have hlen : h.rounds.length = (Psc.varsOf c Sm).length := by
    simpa using congrArg List.length hl
  have hw : (Psc.hidingWalk ((Psc.varsOf c Sm).zip (h.rounds.map (·.2)))).1.length =
      Psc.hidingEntries (Psc.varsOf c Sm) := by
    rw [hidingWalk_length]
    · unfold Psc.hidingEntries
      congr 2
      have hz : ((Psc.varsOf c Sm).zip (h.rounds.map (·.2))).map Prod.fst = Psc.varsOf c Sm :=
        List.map_fst_zip (by simp [hlen])
      calc List.map (fun p => p.1.d - 1) ((Psc.varsOf c Sm).zip (h.rounds.map (·.2)))
          = List.map (fun w : Psc.Weight => w.d - 1)
              (((Psc.varsOf c Sm).zip (h.rounds.map (·.2))).map Prod.fst) := by
            rw [List.map_map]
            rfl
        _ = _ := by rw [hz]
    · intro hz
      have := congrArg List.length hz
      simp [hlen] at this
      exact hne this
    · intro p hp
      exact hd p.1 (List.of_mem_zip hp).1
  have cond : (Psc.formOK c Sm && fr.length == Psc.masksOf c Sm &&
      h.rounds.length == (Psc.varsOf c Sm).length && h.values.length == Sm.shown &&
      (Sm.coeffs ((h.rounds.map (·.2)).take c.vars.length) h.values).length == 1 + Sm.kept &&
      (((Psc.varsOf c Sm).zip h.rounds).all fun p => p.2.1.length + 1 == p.1.d)) = true := by
    simp [hform, hfr, hlen, hv, ha, sizes_fit _ _ hl hd]
  unfold Psc.run
  simp only []
  rw [if_pos cond]
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hlen]
    omega
  · simp [ha]
  · simp only [List.length_map, List.length_zip, List.length_drop, hw, hfr, hv, Psc.masksOf]
    omega
  · intro e he
    simp only [List.mem_map] at he
    obtain ⟨p, hp, rfl⟩ := he
    refine ⟨rfl, ?_⟩
    intro q hq
    simp only [List.mem_singleton] at hq
    subst hq
    exact List.mem_of_mem_drop (List.of_mem_zip hp).1
  · intro p hp
    simp only [List.mem_append] at hp
    rcases hp with hp | hp
    · exact Or.inl (List.of_mem_zip hp).1
    · right
      simp only [Psc.scaleForm, List.mem_map] at hp ⊢
      obtain ⟨q, hq, rfl⟩ := hp
      exact ⟨q, hq, rfl⟩

/-! ## One sumcheck of the lookup -/

theorem mem_slotsFrom {k n : Nat} {s : Slot} (h : s ∈ slotsFrom k n) :
    s.oracle = masksMessage ∧ s.index < k + n := by
  simp only [slotsFrom, List.mem_map, List.mem_range'_1] at h
  obtain ⟨i, hi, rfl⟩ := h
  exact ⟨rfl, hi.2⟩

/-- The fresh mask entries of a sumcheck. -/
theorem fresh_at (S : Lkp.Public) (es rs last rows) (n k : Nat) (keys : Bool)
    (h : k + n ≤ Lkp.allMasks S) (h2 : keys = true → 2 ≤ n) :
    ∃ fr, (Lkp.fresh (envOf S) n keys) (ctxAt S es none rs last k rows) =
        .ok (fr, ctxAt S es none rs last (k + n) rows) ∧ fr.length = n ∧
      ∀ s ∈ fr, s.oracle = masksMessage ∧ s.index < Lkp.allMasks S := by
  cases keys with
  | false =>
    refine ⟨slotsFrom k n, takeSlots_at S es rs last rows n k h, slotsFrom_length k n, ?_⟩
    intro s hs
    have := mem_slotsFrom hs
    exact ⟨this.1, by omega⟩
  | true =>
    have hn := h2 rfl
    refine ⟨slotsFrom k (n - 2) ++ slotsFrom (k + (n - 2)) 2, ?_, ?_, ?_⟩
    · show ((Blk.must (decide (2 ≤ n))) >>= fun _ => (takeSlots masksMessage (n - 2)) >>= fun a =>
        (takeSlots masksMessage 2) >>= fun b => pure (a ++ b)) _ = _
      rw [bind_ok (must_ok (by simp [hn]) _),
        bind_ok (takeSlots_at S es rs last rows (n - 2) k (by omega)),
        bind_ok (takeSlots_at S es rs last rows 2 (k + (n - 2)) (by omega)), pure_ok,
        show k + (n - 2) + 2 = k + n from by omega]
    · simp [slotsFrom_length]
      omega
    · intro s hs
      rcases List.mem_append.1 hs with hs | hs
      · have := mem_slotsFrom hs
        exact ⟨this.1, by omega⟩
      · have := mem_slotsFrom hs
        exact ⟨this.1, by omega⟩

/-- A single entry of another message does not turn a row's coefficient on a key. -/
theorem coefficient_addUnit (r : Row) (o : Nat) (part : Part) (index : Nat) (x : E) (i : Nat)
    (ho : o ≠ keysMessage) :
    (r.addUnit o part index x).coefficient keysMessage .main i = r.coefficient keysMessage .main i := by
  simp [Row.coefficient, Row.addUnit, ho]

/-- A structured vector on another message does not turn a row's coefficient on a key. -/
theorem coefficient_add (r : Row) (o : Nat) (part : Part) (v : Tensor) (i : Nat)
    (ho : o ≠ keysMessage) :
    (r.add o part v).coefficient keysMessage .main i = r.coefficient keysMessage .main i := by
  simp [Row.coefficient, Row.add, ho]

/-- A row stays fine when mask entries that the lookup can take are added to it. -/
theorem fine_addMasks (S : Lkp.Public) : ∀ (m : MaskForm) (r : Row), Fine S r → SlotsOK S m →
    Fine S (r.addMasks m)
  | [], r, h, _ => h
  | t :: m, r, h, hm => by
    have ht := hm t (by simp)
    have h1 : Fine S (r.addUnit t.1.oracle .mask t.1.index t.2) :=
      { kind := h.kind, terms := h.terms, runs := h.runs, forms := h.forms
        atPadding := by
          intro i hb hi
          rw [coefficient_addUnit _ _ _ _ _ _ (by rw [ht.1]; decide)]
          exact h.atPadding i hb hi
        units := by
          intro u hu
          simp only [Row.addUnit, Array.mem_push] at hu
          rcases hu with hu | rfl
          · exact h.units u hu
          · exact ⟨ht.1, rfl, ht.2⟩ }
    exact fine_addMasks S m _ h1 (fun p hp => hm p (by simp [hp]))

/-- The row that has only a target. -/
theorem fine_target (S : Lkp.Public) (x : E) : Fine S { target := x } :=
  { kind := rfl, terms := by simp, units := by simp, runs := rfl, forms := by simp
    atPadding := fun _ _ _ => rfl }

/-- A row stays fine when an equality vector on the bits is added to it. -/
theorem fine_planes (S : Lkp.Public) (r : Row) (h : Fine S r) (v : Tensor)
    (hv : v.vars = S.mu + S.d) (hok : v.ok = true) : Fine S (r.add planesMessage .main v) :=
  { kind := h.kind, units := h.units, runs := h.runs, forms := h.forms
    atPadding := by
      intro i hb hi
      rw [coefficient_add _ _ _ _ _ (by decide)]
      exact h.atPadding i hb hi
    terms := by
      intro t ht
      simp only [Row.add, Array.mem_push] at ht
      rcases ht with ht | rfl
      · exact h.terms t ht
      · exact ⟨rfl, rfl, hv, hok⟩ }

/-- rows' is rows and then n rows more, each of which the caller's group takes. -/
def Added (S : Lkp.Public) (n : Nat) (rows rows' : Array Row) : Prop :=
  ∃ new : List Row, rows' = rows ++ new.toArray ∧ new.length = n ∧ ∀ r ∈ new, Fine S r

theorem Added.zero (S : Lkp.Public) (rows : Array Row) : Added S 0 rows rows :=
  ⟨[], by simp, rfl, by simp⟩

theorem Added.push {S : Lkp.Public} {row : Row} (rows : Array Row) (h : Fine S row) :
    Added S 1 rows (rows.push row) :=
  ⟨[row], by simp, rfl, by intro r hr; simp at hr; subst hr; exact h⟩

theorem Added.trans {S : Lkp.Public} {a b : Nat} {r0 r1 r2 : Array Row} (h1 : Added S a r0 r1)
    (h2 : Added S b r1 r2) : Added S (a + b) r0 r2 := by
  obtain ⟨n1, e1, l1, f1⟩ := h1
  obtain ⟨n2, e2, l2, f2⟩ := h2
  refine ⟨n1 ++ n2, by rw [e2, e1]; simp [Array.append_assoc], by simp [l1, l2], ?_⟩
  intro r hr
  rcases List.mem_append.1 hr with h | h
  · exact f1 r h
  · exact f2 r h

/-- The kept maps keep a row fine at points of n coordinates. -/
def MapsOK (S : Lkp.Public) (n : Nat) (kept : List MapAt) : Prop :=
  ∀ m ∈ kept, ∀ (row : Row) (point : List E) (coeff : E), Fine S row → point.length = n →
    Fine S (m row point coeff)

theorem fine_foldl (S : Lkp.Public) (n : Nat) (point : List E) (hp : point.length = n) :
    ∀ (l : List (MapAt × E)) (r : Row), (∀ q ∈ l, ∀ (row : Row) (pt : List E) (coeff : E),
      Fine S row → pt.length = n → Fine S (q.1 row pt coeff)) → Fine S r →
    Fine S (l.foldl (fun r p => p.1 r point p.2) r)
  | [], r, _, h => h
  | q :: l, r, hl, h =>
    fine_foldl S n point hp l _ (fun x hx => hl x (by simp [hx])) (hl q (by simp) r point q.2 h hp)

/-- The lengths that Psc.hear finds are those that Psc.run asks. -/
theorem lens_eq (c : Psc.Claim) (Sm : Psc.Summand) :
    (Psc.sizeOf c Sm).degree.map (· - 1) ++
        (if (Psc.sizeOf c Sm).withY then [(Psc.sizeOf c Sm).degreeY] else []) =
      (Psc.varsOf c Sm).map (fun w => w.d - 1) := by
  unfold Psc.sizeOf Psc.varsOf
  by_cases h : Sm.shown = 0
  · simp [h, List.map_map, Function.comp_def]
  · have h' : 0 < Sm.shown := Nat.pos_of_ne_zero h
    simp [h, h', List.map_map, Function.comp_def, Psc.Weight.atZero, Psc.Weight.equality]

/-- One sumcheck of the lookup goes through, whatever the values. -/
theorem psc_at (S : Lkp.Public) (hS : Sized S) (hR : S.readFrom = [keysMessage, planesMessage])
    (work : Nat) (c : Psc.Claim) (Sm : Psc.Summand) (lastOfKeys : Bool) (kept : List MapAt)
    (place : List E → List E) (es' : List Fmt.Entry) (rs : List FlatRound)
    (last : Option Fmt.Entry) (k : Nat) (rows : Array Row) (hq : NoRows last)
    (hfit : FitsAll rs (pscEntries work (Psc.sizeOf c Sm) ++ es'))
    (hform : Psc.formOK c Sm = true) (ha : ∀ p y, (Sm.coeffs p y).length = 1 + Sm.kept)
    (hd : ∀ w ∈ Psc.varsOf c Sm, 1 ≤ w.d) (hne : Psc.varsOf c Sm ≠ [])
    (hle : c.vars.length ≤ (Psc.varsOf c Sm).length)
    (hk : k + Psc.masksOf c Sm ≤ Lkp.allMasks S) (h2 : lastOfKeys = true → 2 ≤ Psc.masksOf c Sm)
    (hm : SlotsOK S c.masks) (hkept : kept.length = Sm.kept) (hmaps : MapsOK S c.vars.length kept)
    (hplace : ∀ p, (place p).length = p.length) :
    ∃ o rs' last' row, FitsAll rs' es' ∧ NoRows last' ∧
      (Lkp.psc (envOf S) c Sm lastOfKeys kept place)
          (ctxAt S (pscEntries work (Psc.sizeOf c Sm) ++ es') none (rvs rs) last k rows) =
        .ok (o, ctxAt S es' none (rvs rs') last' (k + Psc.masksOf c Sm) (rows.push row)) ∧
      o.point.length = c.vars.length ∧ o.ends.length = Sm.shown ∧
      (∀ e ∈ o.ends, e.point = o.point ∧ SlotsOK S e.masks) ∧ Fine S row := by
  obtain ⟨fr, hfr, hfl, hfs⟩ := fresh_at S (pscEntries work (Psc.sizeOf c Sm) ++ es') (rvs rs) last rows
    (Psc.masksOf c Sm) k lastOfKeys hk h2
  obtain ⟨hd', rs', last', hf', hq', hhear, hlens, hvals⟩ :=
    hear_at S work (k + Psc.masksOf c Sm) rows (Psc.sizeOf c Sm) es' rs last hq hfit
  rw [lens_eq] at hlens
  have hv : hd'.values.length = Sm.shown := by
    rw [hvals]
    unfold Psc.sizeOf
    by_cases h : Sm.shown = 0 <;> simp [h, Nat.pos_of_ne_zero]
  obtain ⟨o, ho, hO⟩ := run_some c Sm fr hd' hform hfl hlens hv ha hd hne hle
  have hver : (Psc.verify c Sm fr)
      (ctxAt S (pscEntries work (Psc.sizeOf c Sm) ++ es') none (rvs rs) last (k + Psc.masksOf c Sm) rows) =
      .ok (o, ctxAt S es' none (rvs rs') last' (k + Psc.masksOf c Sm) rows) := by
    show ((Psc.hear (Psc.sizeOf c Sm)) >>= fun h => Blk.get (Psc.run c Sm fr h)) _ = _
    rw [bind_ok hhear, ho]
    rfl
  -- the out with its points put back
  let o' : Psc.Out := { o with
    point := place o.point
    ends := o.ends.map fun x => { x with point := place x.point } }
  have hmasks : SlotsOK S o'.rowMasks := by
    intro p hp
    rcases hO.masks p hp with h | h
    · exact hfs p.1 h
    · obtain ⟨q, hq1, hq2⟩ := List.mem_map.1 h
      rw [← hq2]
      exact hm q hq1
  have hpl : o'.point.length = c.vars.length := by
    show (place o.point).length = _
    rw [hplace, hO.point]
  have hrow : ∃ row, Psc.rowU o' kept = some row ∧ Fine S row := by
    unfold Psc.rowU
    have : (kept.length == o'.rowMaps.length) = true := by
      show (kept.length == o.rowMaps.length) = true
      simp [hkept, hO.maps]
    rw [if_pos this]
    refine ⟨_, rfl, ?_⟩
    apply fine_foldl S c.vars.length o'.point hpl
    · intro q hq1
      exact hmaps q.1 (List.of_mem_zip hq1).1
    · exact fine_addMasks S _ _ (fine_target S _) hmasks
  obtain ⟨row, hrow1, hrow2⟩ := hrow
  refine ⟨o', rs', last', row, hf', hq', ?_, hpl, ?_, ?_, hrow2⟩
  · unfold Lkp.psc
    rw [bind_ok hfr, bind_ok hver]
    show ((Blk.get (Psc.rowU o' kept)) >>= fun r => (Lkp.leave (envOf S) r) >>= fun _ => pure o') _ = _
    rw [hrow1, bind_ok (get_ok _ _), bind_ok (leave_at S hS hR es' (rvs rs') last' _ rows row hrow2),
      pure_ok]
  · show (o.ends.map _).length = _
    rw [List.length_map, hO.ends]
  · intro e he
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
    obtain ⟨h1, h3⟩ := hO.endsAt x hx
    refine ⟨by show place x.point = place o.point; rw [h1], ?_⟩
    intro p hp
    exact hfs p.1 (h3 p hp)

/-! ## Claims, lines, levels -/

/-- A claim at a point of n coordinates whose mask entries the lookup can take. -/
def ClaimOK (S : Lkp.Public) (n : Nat) (c : PointClaim) : Prop :=
  c.point.length = n ∧ SlotsOK S c.masks

theorem slotsOK_scale {S : Lkp.Public} {m : MaskForm} (x : E) (h : SlotsOK S m) :
    SlotsOK S (Psc.scaleForm x m) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
  exact h q hq

theorem slotsOK_append {S : Lkp.Public} {a b : MaskForm} (ha : SlotsOK S a) (hb : SlotsOK S b) :
    SlotsOK S (a ++ b) := by
  intro p hp
  rcases List.mem_append.1 hp with h | h
  · exact ha p h
  · exact hb p h

theorem note_at (S : Lkp.Public) (es cur rs last k rows) (what : String) (x : E) :
    (Blk.note what x) (ctxAt S es cur rs last k rows) = .ok ((), ctxAt S es cur rs last k rows) := rfl

/-- Two claims at one point become one. -/
theorem line_at (S : Lkp.Public) (n work : Nat) (es' : List Fmt.Entry) (rs : List FlatRound)
    (last k rows) (a b : PointClaim) (ha : ClaimOK S n a) (hb : ClaimOK S n b)
    (hp : a.point = b.point) (hq : NoRows last)
    (hfit : FitsAll rs ((rDraw "LINE" work 1).entry :: es')) :
    ∃ c rs' last', FitsAll rs' es' ∧ NoRows last' ∧
      (line a b) (ctxAt S ((rDraw "LINE" work 1).entry :: es') none (rvs rs) last k rows) =
        .ok (c, ctxAt S es' none (rvs rs') last' k rows) ∧ ClaimOK S (n + 1) c := by
  cases rs with
  | nil => simp [FitsAll] at hfit
  | cons r rs =>
    obtain ⟨hr, hrest⟩ := hfit
    have hm : Meets r (rDraw "LINE" work 1).entry "LINE" 0 1 0 :=
      meets_of_fits hr rfl rfl rfl rfl rfl rfl rfl
    obtain ⟨rho, hrho⟩ := List.length_eq_one_iff.1 hm.drawn
    refine ⟨lineAt rho a b, rs, _, hrest, hm.noRows, ?_, ?_, ?_⟩
    · unfold line
      rw [bind_ok (must_ok (by simp [hp]) _), bind_ok (test_ok (by simp [hp]) _),
        show rvs (r :: rs) = r.rv :: rvs rs from rfl,
        bind_ok (hearDraw_at S _ es' (rvs rs) last k rows r "LINE" 1 hm hq), hrho]
      rfl
    · simp [lineAt, ha.1]
    · exact slotsOK_append (slotsOK_scale _ ha.2) (slotsOK_scale _ hb.2)

/-- The entries of the levels l, l + 1, .. of a product tree, n of them. -/
def chainEntries (work more : Nat) : Nat → Nat → List Fmt.Entry
  | _, 0 => []
  | l, n + 1 =>
    pscEntries work { degree := List.replicate (l + more) 3 } ++
      (rDraw "LINE" work 1).entry :: chainEntries work more (l + 1) n

/-- The mask entries that these levels take. -/
def chainMasks (more : Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | l, n + 1 => (2 * (l + more) + 5) + chainMasks more (l + 1) n

theorem byVariable_length (p : List E) (order : List Nat) :
    (Lkp.byVariable p order).length = p.length := by
  simp [Lkp.byVariable]

theorem sum_replicate_two (n : Nat) : (List.replicate n 2).sum = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]; omega

/-- The sum that a level of a product tree is. -/
def levelSum (c : PointClaim) (order : List Nat) : Psc.Claim where
  vars := order.map fun t => Psc.Weight.equality (c.point.getD t zeroE) 3
  masks := c.masks
  target := c.value

theorem levelSum_size (c : PointClaim) (order : List Nat) :
    Psc.sizeOf (levelSum c order) Lkp.summandProduct = { degree := List.replicate order.length 3 } := by
  simp [Psc.sizeOf, levelSum, Lkp.summandProduct, Psc.Weight.equality, List.map_map,
    Function.comp_def, List.map_const']

theorem levelSum_masks (c : PointClaim) (order : List Nat) :
    Psc.masksOf (levelSum c order) Lkp.summandProduct = 2 * order.length + 5 := by
  simp [Psc.masksOf, Psc.varsOf, Psc.hidingEntries, levelSum, Lkp.summandProduct,
    Psc.Weight.equality, Psc.Weight.atZero, List.map_map, Function.comp_def, List.map_const']
  omega

/-- The order in which level l of a tree binds its variables. -/
def orderAt (S : Lkp.Public) (keys : Bool) (levels more l : Nat) : List Nat :=
  if keys && l + 1 == levels then Lkp.orderBeginning S.lastKeyLevelOrder (more + l)
  else Lkp.defaultOrder (more + l)

/-- One level of a product tree goes through, whatever the values. -/
theorem level_at (S : Lkp.Public) (hS : Sized S) (hR : S.readFrom = [keysMessage, planesMessage])
    (work : Nat) (order : List Nat) (lastOfKeys : Bool) (es' : List Fmt.Entry)
    (rs : List FlatRound) (last k rows) (c : PointClaim) (hc : ClaimOK S order.length c)
    (hq : NoRows last)
    (hfit : FitsAll rs (pscEntries work { degree := List.replicate order.length 3 } ++
      (rDraw "LINE" work 1).entry :: es'))
    (hk : k + (2 * order.length + 5) ≤ Lkp.allMasks S) :
    ∃ c' rs' last' rows', FitsAll rs' es' ∧ NoRows last' ∧
      ((Lkp.psc (envOf S) (levelSum c order) Lkp.summandProduct lastOfKeys []
          fun p => Lkp.byVariable p order) >>= fun o =>
        match o.ends with
        | [e0, e1] => line e0 e1
        | _ => Blk.fail)
        (ctxAt S (pscEntries work { degree := List.replicate order.length 3 } ++
          (rDraw "LINE" work 1).entry :: es') none (rvs rs) last k rows) =
        .ok (c', ctxAt S es' none (rvs rs') last' (k + (2 * order.length + 5)) rows') ∧
      ClaimOK S (order.length + 1) c' ∧ Added S 1 rows rows' := by
  have hsz := levelSum_size c order
  have hmk := levelSum_masks c order
  have hvars : (levelSum c order).vars.length = order.length := by simp [levelSum]
  obtain ⟨o, rs1, last1, row, hf1, hq1, hrun, hpt, hends, hall, hfine⟩ :=
    psc_at S hS hR work (levelSum c order) Lkp.summandProduct lastOfKeys []
      (fun p => Lkp.byVariable p order) ((rDraw "LINE" work 1).entry :: es') rs last k rows hq
      (by rw [hsz]; exact hfit)
      (by simp [Psc.formOK, Lkp.summandProduct, levelSum, Psc.Weight.fits, Psc.Weight.equality])
      (by intro p y; rfl)
      (by
        intro x hx
        simp only [Psc.varsOf, Lkp.summandProduct, levelSum] at hx
        simp at hx
        rcases hx with ⟨t, _, rfl⟩ | rfl <;> simp [Psc.Weight.equality, Psc.Weight.atZero])
      (by simp [Psc.varsOf, Lkp.summandProduct])
      (by simp [Psc.varsOf, Lkp.summandProduct])
      (by rw [hmk]; exact hk) (by intro _; rw [hmk]; omega) hc.2 rfl
      (by intro m hm; simp at hm) (fun p => byVariable_length p order)
  rw [hsz] at hrun
  rw [hmk] at hrun
  have h2 : o.ends.length = 2 := hends
  obtain ⟨e0, e1, he⟩ : ∃ e0 e1, o.ends = [e0, e1] := by
    match o.ends, h2 with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  have h0 := hall e0 (by simp [he])
  have h1 := hall e1 (by simp [he])
  obtain ⟨c', rs', last', hf', hq', hline, hc'⟩ :=
    line_at S order.length work es' rs1 last1 (k + (2 * order.length + 5)) (rows.push row) e0 e1
      ⟨by rw [h0.1, hpt, hvars], h0.2⟩ ⟨by rw [h1.1, hpt, hvars], h1.2⟩ (h0.1.trans h1.1.symm) hq1 hf1
  refine ⟨c', rs', last', rows.push row, hf', hq', ?_, hc', Added.push rows hfine⟩
  rw [bind_ok hrun, he]
  exact hline

/-- What follows a level may be bound behind the level as a whole. -/
theorem level_assoc {β : Type} (x : Blk Psc.Out) (f : PointClaim → Blk β) :
    (x >>= fun o =>
      match o.ends with
      | [e0, e1] => line e0 e1 >>= f
      | _ => Blk.fail) =
    ((x >>= fun o =>
      match o.ends with
      | [e0, e1] => line e0 e1
      | _ => Blk.fail) >>= f) := by
  rw [bind_assoc]
  congr 1
  funext o
  split <;> rfl

/-- The levels of a product tree go through, whatever the values. -/
theorem levelChain_at (S : Lkp.Public) (hS : Sized S)
    (hR : S.readFrom = [keysMessage, planesMessage]) (work : Nat) (keys : Bool) (levels more : Nat)
    (hord : ∀ l, l < levels → (orderAt S keys levels more l).length = more + l)
    (es' : List Fmt.Entry) :
    ∀ (n : Nat) (c : PointClaim) (rs : List FlatRound) (last : Option Fmt.Entry) (k : Nat)
      (rows : Array Row), n ≤ levels → ClaimOK S (more + (levels - n)) c → NoRows last →
      FitsAll rs (chainEntries work more (levels - n) n ++ es') →
      k + chainMasks more (levels - n) n ≤ Lkp.allMasks S →
      ∃ c' rs' last' rows', FitsAll rs' es' ∧ NoRows last' ∧
        (Lkp.levelChain (envOf S) keys levels more n c)
          (ctxAt S (chainEntries work more (levels - n) n ++ es') none (rvs rs) last k rows) =
          .ok (c', ctxAt S es' none (rvs rs') last' (k + chainMasks more (levels - n) n) rows') ∧
        ClaimOK S (more + levels) c' ∧ Added S n rows rows'
  | 0, c, rs, last, k, rows, _, hc, hq, hfit, _ =>
    ⟨c, rs, last, rows, hfit, hq, rfl, by simpa using hc, Added.zero S rows⟩
  | n + 1, c, rs, last, k, rows, hn, hc, hq, hfit, hk => by
    have hl : levels - (n + 1) < levels := by omega
    have ho := hord _ hl
    have hnext : levels - (n + 1) + 1 = levels - n := by omega
    have hlen : levels - (n + 1) + more = (orderAt S keys levels more (levels - (n + 1))).length := by
      rw [ho]; omega
    simp only [chainEntries, chainMasks, List.append_assoc, List.cons_append, hnext, hlen] at hfit hk ⊢
    obtain ⟨c1, rs1, last1, rows1, hf1, hq1, hrun1, hc1, had1⟩ :=
      level_at S hS hR work (orderAt S keys levels more (levels - (n + 1)))
        (keys && levels - (n + 1) + 1 == levels) (chainEntries work more (levels - n) n ++ es') rs last
        k rows c (by rw [ho]; exact hc) hq hfit (by omega)
    obtain ⟨c', rs', last', rows', hf', hq', hrun', hc', had'⟩ :=
      levelChain_at S hS hR work keys levels more hord es' n c1 rs1 last1
        (k + (2 * (orderAt S keys levels more (levels - (n + 1))).length + 5)) rows1 (by omega)
        (by rw [ho] at hc1; rw [← hnext, ← Nat.add_assoc]; exact hc1) hq1 hf1 (by omega)
    refine ⟨c', rs', last', rows', hf', hq', ?_, hc', by
      rw [Nat.add_comm n 1]; exact had1.trans had'⟩
    rw [Nat.add_assoc] at hrun'
    rw [← hrun']
    show ((Blk.must ((orderAt S keys levels more (levels - (n + 1))).length == more + (levels - (n + 1)) &&
        c.point.length == more + (levels - (n + 1)))) >>= fun _ =>
      (Lkp.psc (envOf S) (levelSum c (orderAt S keys levels more (levels - (n + 1)))) Lkp.summandProduct
        (keys && levels - (n + 1) + 1 == levels) []
        fun p => Lkp.byVariable p (orderAt S keys levels more (levels - (n + 1)))) >>= fun o =>
      match o.ends with
      | [e0, e1] => line e0 e1 >>= fun next => Lkp.levelChain (envOf S) keys levels more n next
      | _ => Blk.fail) _ = _
    rw [bind_ok (must_ok (by simp [ho, hc.1]) _), level_assoc, bind_ok hrun1]

/-! ## Sumchecks without a variable: the tie -/

/-- A sumcheck without a variable goes through, whatever the values. -/
theorem value_at (S : Lkp.Public) (hS : Sized S) (hR : S.readFrom = [keysMessage, planesMessage])
    (work : Nat) (cl : Psc.Claim) (hcl : cl.vars = []) (Sm : Psc.Summand) (hs : 0 < Sm.shown)
    (hdg : 0 < Sm.degree) (hk0 : Sm.kept = 0) (ha : ∀ p y, (Sm.coeffs p y).length = 1 + Sm.kept)
    (es' : List Fmt.Entry) (rs : List FlatRound) (last k rows) (hq : NoRows last)
    (hfit : FitsAll rs (pscEntries work
      { degree := [], withY := true, degreeY := Sm.degree, values := Sm.shown } ++ es'))
    (hk : k + (1 + Sm.degree + Sm.shown) ≤ Lkp.allMasks S) (hm : SlotsOK S cl.masks) :
    ∃ o rs' last' row, FitsAll rs' es' ∧ NoRows last' ∧
      (Lkp.psc (envOf S) cl Sm)
          (ctxAt S (pscEntries work
            { degree := [], withY := true, degreeY := Sm.degree, values := Sm.shown } ++ es')
            none (rvs rs) last k rows) =
        .ok (o, ctxAt S es' none (rvs rs') last' (k + (1 + Sm.degree + Sm.shown)) (rows.push row)) ∧
      o.ends.length = Sm.shown ∧ (∀ e ∈ o.ends, ClaimOK S 0 e) ∧ Fine S row := by
  have hne0 : Sm.shown ≠ 0 := Nat.pos_iff_ne_zero.1 hs
  have hdne : Sm.degree ≠ 0 := Nat.pos_iff_ne_zero.1 hdg
  have hsz : Psc.sizeOf cl Sm =
      { degree := [], withY := true, degreeY := Sm.degree, values := Sm.shown } := by
    simp [Psc.sizeOf, hcl, hs]
  have hvo : Psc.varsOf cl Sm = [Psc.Weight.atZero (Sm.degree + 1)] := by
    simp [Psc.varsOf, hcl, hne0]
  have hmk : Psc.masksOf cl Sm = 1 + Sm.degree + Sm.shown := by
    simp [Psc.masksOf, hvo, Psc.hidingEntries, Psc.Weight.atZero, Psc.Weight.equality]
  obtain ⟨o, rs', last', row, hf', hq', hrun, hpt, hends, hall, hfine⟩ :=
    psc_at S hS hR work cl Sm false [] id es' rs last k rows hq (by rw [hsz]; exact hfit)
      (by
        have b1 : (Sm.shown == 0) = false := by simp [hne0]
        have b2 : (Sm.degree == 0) = false := by simp [hdne]
        simp [Psc.formOK, hcl, hs, b1, b2]) ha
      (by rw [hvo]; intro x hx; simp at hx; subst hx; simp [Psc.Weight.atZero, Psc.Weight.equality])
      (by rw [hvo]; simp) (by simp [hcl]) (by rw [hmk]; exact hk) (by intro h; cases h) hm
      (by simp [hk0]) (by intro m hm'; simp at hm') (fun _ => rfl)
  rw [hsz, hmk] at hrun
  refine ⟨o, rs', last', row, hf', hq', hrun, hends, ?_, hfine⟩
  intro e he
  obtain ⟨h1, h2⟩ := hall e he
  exact ⟨by rw [h1, hpt, hcl]; rfl, h2⟩

/-- A claim on a value as a sum without variables. -/
theorem onValue_at (S : Lkp.Public) (c : PointClaim) (hc : ClaimOK S 0 c) (x : Ctx) :
    (Lkp.onValue c) x = .ok (({ vars := [], masks := c.masks, target := c.value } : Psc.Claim), x) := by
  have hp : c.point = [] := List.length_eq_zero_iff.1 hc.1
  simp [Lkp.onValue, Psc.Claim.atPoint, hp, get_ok]

/-- The entries of n later steps of the tie. -/
def tieEntries (work : Nat) : Nat → List Fmt.Entry
  | 0 => []
  | n + 1 => pscEntries work { degree := [], degreeY := 3, values := 2 } ++ tieEntries work n

/-- The later steps of the tie go through, whatever the values. -/
theorem tieSteps_at (S : Lkp.Public) (hS : Sized S) (hR : S.readFrom = [keysMessage, planesMessage])
    (work : Nat) (es' : List Fmt.Entry) :
    ∀ (n : Nat) (c : PointClaim) (rs : List FlatRound) (last : Option Fmt.Entry) (k : Nat)
      (rows : Array Row), ClaimOK S 0 c → NoRows last → FitsAll rs (tieEntries work n ++ es') →
      k + 6 * n ≤ Lkp.allMasks S →
      ∃ l rs' last' rows', FitsAll rs' es' ∧ NoRows last' ∧
        (Lkp.tieSteps (envOf S) n c) (ctxAt S (tieEntries work n ++ es') none (rvs rs) last k rows) =
          .ok (l, ctxAt S es' none (rvs rs') last' (k + 6 * n) rows') ∧
        (∀ x ∈ l, ClaimOK S 0 x) ∧ Added S n rows rows'
  | 0, c, rs, last, k, rows, hc, hq, hfit, _ =>
    ⟨[c], rs, last, rows, hfit, hq, rfl, by intro x hx; simp at hx; subst hx; exact hc,
      Added.zero S rows⟩
  | n + 1, c, rs, last, k, rows, hc, hq, hfit, hk => by
    simp only [tieEntries, List.append_assoc] at hfit ⊢
    obtain ⟨o, rs1, last1, row, hf1, hq1, hrun1, hends, hall, hfine⟩ :=
      value_at S hS hR work { vars := [], masks := c.masks, target := c.value } rfl Lkp.summandTie
        (by decide) (by decide) rfl (fun _ _ => rfl) (tieEntries work n ++ es') rs last k rows hq hfit
        (by show k + (1 + 3 + 2) ≤ _; omega) hc.2
    obtain ⟨power, plane, he⟩ : ∃ a b, o.ends = [a, b] := by
      have h2 : o.ends.length = 2 := hends
      match o.ends, h2 with
      | [a, b], _ => exact ⟨a, b, rfl⟩
    obtain ⟨l, rs', last', rows', hf', hq', hrun', hl, had'⟩ :=
      tieSteps_at S hS hR work es' n power rs1 last1 (k + (1 + 3 + 2)) (rows.push row)
        (hall power (by simp [he])) hq1 hf1 (by omega)
    refine ⟨plane :: l, rs', last', rows', hf', hq', ?_, ?_, by
      rw [Nat.add_comm n 1]; exact (Added.push rows hfine).trans had'⟩
    · show ((Lkp.onValue c) >>= fun cl => (Lkp.psc (envOf S) cl Lkp.summandTie) >>= fun o =>
        match o.ends with
        | [power, plane] => (Lkp.tieSteps (envOf S) n power) >>= fun rest => pure (plane :: rest)
        | _ => Blk.fail) _ = _
      rw [bind_ok (onValue_at S c hc _)]
      refine (bind_ok hrun1).trans ?_
      rw [he]
      show ((Lkp.tieSteps (envOf S) n power) >>= fun rest => pure (plane :: rest)) _ = _
      refine (bind_ok hrun').trans ?_
      rw [pure_ok, show k + (1 + 3 + 2) + 6 * n = k + 6 * (n + 1) from by omega]
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hall _ (by simp [he])
      · exact hl x hx

/-! ## The claim on the keys -/

theorem foldl_inv {α β : Type} (P : β → Prop) (f : β → α → β) (hf : ∀ b a, P b → P (f b a)) :
    ∀ (l : List α) (b : β), P b → P (l.foldl f b)
  | [], _, h => h
  | a :: l, b, h => foldl_inv P f hf l (f b a) (hf b a h)

theorem eq_ok (z : List E) (x : E) (h : z.length ≤ 63) : (Tensor.eq z x).ok = true := by
  simp [Tensor.ok, Tensor.eq, Tensor.vars, distinctNats, h]

theorem cubeTensor_ok (c : Lkp.Cube) (z : List E) (x : E) (h : z.length ≤ 63) :
    (Lkp.cubeTensor c z x).vars = z.length ∧ (Lkp.cubeTensor c z x).ok = true := by
  simp [Tensor.ok, Lkp.cubeTensor, Tensor.vars, distinctNats, h]

theorem fits_add (f : Form) (v : Tensor) (n : Nat) (hf : f.fits n = true) (hv : v.vars = n)
    (hok : v.ok = true) : (f.add v).fits n = true := by
  simp only [Form.add, Form.fits, List.all_cons, Bool.and_eq_true, beq_iff_eq] at hf ⊢
  exact ⟨⟨⟨hv, hok⟩, hf.1⟩, hf.2⟩

theorem fits_ofTensor (v : Tensor) (n : Nat) (hv : v.vars = n) (hok : v.ok = true) :
    (Form.ofTensor v).fits n = true := by
  simp [Form.ofTensor, Form.fits, hv, hok]

theorem takeOut_fits (S : Lkp.Public) (theta : E) (point : List E) (h : point.length ≤ 63)
    (a : Lkp.KeyAcc) (cube : Lkp.Cube) (row : Nat) (block : Option Nat)
    (ha : a.weights.fits point.length = true) :
    (Lkp.takeOut S theta point a cube row block).weights.fits point.length = true := by
  generalize hx : negE oneE = x
  obtain ⟨h1, h2⟩ := cubeTensor_ok cube point x h
  have : (Lkp.takeOut S theta point a cube row block).weights =
      a.weights.add (Lkp.cubeTensor cube point x) := by rw [← hx]; rfl
  rw [this]
  exact fits_add _ _ _ ha h1 h2

/-- The weights of the claim on the keys fit the key vector, whatever the values. -/
theorem keysOf_fits (S : Lkp.Public) (theta alpha : E) (part : Nat) (c : PointClaim)
    (h : c.point.length ≤ 63) :
    (Lkp.keysOf S theta alpha part c).weights.fits c.point.length = true := by
  unfold Lkp.keysOf
  simp only []
  apply foldl_inv (fun a : Lkp.KeyAcc => a.weights.fits c.point.length = true)
  · intro a p ha
    apply foldl_inv (fun a : Lkp.KeyAcc => a.weights.fits c.point.length = true)
    · intro a' cube ha'
      exact takeOut_fits S theta c.point h a' cube _ _ ha'
    · exact ha
  · apply foldl_inv (fun a : Lkp.KeyAcc => a.weights.fits c.point.length = true)
    · intro a b ha
      exact takeOut_fits S theta c.point h a _ _ _ ha
    · exact fits_ofTensor _ _ (by simp [Tensor.eq, Tensor.vars]) (eq_ok c.point oneE h)

/-- The caller's row on the keys is one that the group takes. -/
theorem fine_keysRow (S : Lkp.Public) (theta alpha : E) (c : PointClaim)
    (hc : ClaimOK S S.firstBits c) (h63 : S.firstBits ≤ 63)
    (hpad : ∀ i, i < 2 ^ S.firstBits → isPadding S i = true →
      isZeroE (addE zeroE ((Lkp.keysOf S theta alpha 0 c).weights.entry i)) = true) :
    Fine S (keysRow (Lkp.keysOf S theta alpha 0 c)) := by
  unfold keysRow
  apply fine_addMasks
  · exact
      { kind := rfl, terms := by simp [Row.addForm], units := by simp [Row.addForm], runs := rfl
        atPadding := fun i hb hi => hpad i hb hi
        forms := by
          intro f hf
          simp only [Row.addForm, Array.mem_push] at hf
          rcases hf with hf | rfl
          · simp at hf
          · refine ⟨rfl, ?_⟩
            have := keysOf_fits S theta alpha 0 c (by rw [hc.1]; exact h63)
            rw [hc.1] at this
            exact this }
  · exact slotsOK_scale _ hc.2

theorem noteKeys_at (c : Ctx) (hc : c.keepNotes = false) (l : List Lkp.Keys) :
    (Lkp.noteKeys l) c = .ok ((), c) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have h1 : ∀ (s : String), (Blk.note s x.target) c = .ok ((), c) := by
      intro s
      simp [Blk.note, hc]
    unfold Lkp.noteKeys
    rw [bind_ok (h1 _)]
    exact ih

/-- The claims on the planes' roots become one claim whose mask entries the lookup can take. -/
theorem joinPlanes_ok (S : Lkp.Public) (r : List E) (l : List PointClaim)
    (hl : ∀ x ∈ l, ClaimOK S 0 x) : ClaimOK S r.length (Lkp.joinPlanes S r l) := by
  unfold Lkp.joinPlanes
  apply foldl_inv (fun c : PointClaim => ClaimOK S r.length c)
  · intro c j hc
    cases hj : l[j]? with
    | none =>
      simp only []
      exact ⟨hc.1, hc.2⟩
    | some p =>
      simp only []
      exact ⟨hc.1, slotsOK_append hc.2 (slotsOK_scale _ (hl p (List.mem_of_getElem? hj)).2)⟩
  · exact ⟨rfl, by intro p hp; simp at hp⟩

/-! ## The whole lookup -/

/-- The sizes of the sumcheck on the leaves of the table's tree. -/
def leavesSize (S : Lkp.Public) : Psc.Size where
  degree := List.replicate S.d 3 ++ List.replicate S.mu 2
  withY := false
  degreeY := 0
  values := 0

/-- The sizes of the sumcheck on the bits. -/
def bitsSize (S : Lkp.Public) : Psc.Size where
  degree := List.replicate (S.mu + S.d) 3
  withY := true
  degreeY := 2
  values := 1

/-- The entries of a lookup with one part of 2^v keys and without a shift, block by block. -/
def blockEntries (S : Lkp.Public) (work v : Nat) : List Fmt.Entry :=
  (rDraw "LKP" work 1).entry ::
  (pscEntries work { degree := [], withY := true, degreeY := 3, values := 3 } ++
  (tieEntries work (S.planes - 2) ++
  ((rDraw "JOIN" work S.mu).entry ::
  (chainEntries work 0 (v - v) v ++
  (chainEntries work S.mu (S.d - S.d) S.d ++
  (pscEntries work (leavesSize S) ++
  ((rDraw "ZERO" work (S.mu + S.d)).entry ::
  (pscEntries work (bitsSize S) ++ []))))))))

/-- What is asked of the public inputs: facts on public numbers alone, each of which can be
evaluated. -/
structure Shaped (S : Lkp.Public) (work v : Nat) : Prop where
  sized : Sized S
  reads : S.readFrom = [keysMessage, planesMessage]
  parts : S.parts = [v]
  noShift : S.shifted = false
  ok : S.ok = true
  keys63 : v ≤ 63
  lastOrder : (Lkp.orderBeginning S.lastKeyLevelOrder (v - 1)).length = v - 1
  leaves : (Lkp.defaultOrder (S.mu + S.d)).map (fun t => if t < S.mu then 2 else 3) =
    List.replicate S.d 3 ++ List.replicate S.mu 2
  some : 0 < S.mu + S.d
  entries : entries S work = blockEntries S work v
  masks : 7 + 6 * (S.planes - 2) + chainMasks 0 (v - v) v + chainMasks S.mu (S.d - S.d) S.d +
    (1 + S.mu + 2 * S.d) + (1 + 2 * (S.mu + S.d) + 2 + 1) ≤ Lkp.allMasks S

theorem defaultOrder_length (n : Nat) : (Lkp.defaultOrder n).length = n := by
  simp [Lkp.defaultOrder]

theorem drawOne_at (S : Lkp.Public) (work : Nat) (name : String) (es' : List Fmt.Entry)
    (rs : List FlatRound) (last k rows) (hq : NoRows last)
    (hfit : FitsAll rs ((rDraw name work 1).entry :: es')) :
    ∃ x rs', FitsAll rs' es' ∧
      (Lkp.drawOne name) (ctxAt S ((rDraw name work 1).entry :: es') none (rvs rs) last k rows) =
        .ok (x, ctxAt S es' none (rvs rs') (some (rDraw name work 1).entry) k rows) := by
  cases rs with
  | nil => simp [FitsAll] at hfit
  | cons r rs =>
    obtain ⟨hr, hrest⟩ := hfit
    have hm : Meets r (rDraw name work 1).entry name 0 1 0 := meets_of_fits hr rfl rfl rfl rfl rfl rfl rfl
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.1 hm.drawn
    refine ⟨x, rs, hrest, ?_⟩
    unfold Lkp.drawOne
    rw [show rvs (r :: rs) = r.rv :: rvs rs from rfl,
      bind_ok (hearDraw_at S _ es' (rvs rs) last k rows r name 1 hm hq), hx]
    rfl

theorem draws_at (S : Lkp.Public) (work n : Nat) (name : String) (es' : List Fmt.Entry)
    (rs : List FlatRound) (last k rows) (hq : NoRows last)
    (hfit : FitsAll rs ((rDraw name work n).entry :: es')) :
    ∃ x rs', FitsAll rs' es' ∧ x.length = n ∧
      (hearDraw name n) (ctxAt S ((rDraw name work n).entry :: es') none (rvs rs) last k rows) =
        .ok (x, ctxAt S es' none (rvs rs') (some (rDraw name work n).entry) k rows) := by
  cases rs with
  | nil => simp [FitsAll] at hfit
  | cons r rs =>
    obtain ⟨hr, hrest⟩ := hfit
    have hm : Meets r (rDraw name work n).entry name 0 n 0 := meets_of_fits hr rfl rfl rfl rfl rfl rfl rfl
    exact ⟨r.drawn, rs, hrest, hm.drawn, hearDraw_at S _ es' (rvs rs) last k rows r name n hm hq⟩

theorem noRows_rDraw (name : String) (work n : Nat) : NoRows (some (rDraw name work n).entry) := by
  intro e he
  cases he
  rfl

theorem orderAt_keys (S : Lkp.Public) (v : Nat)
    (hl : (Lkp.orderBeginning S.lastKeyLevelOrder (v - 1)).length = v - 1) :
    ∀ l, l < v → (orderAt S true v 0 l).length = 0 + l := by
  intro l hlv
  unfold orderAt
  by_cases h : l + 1 = v
  · have : l = v - 1 := by omega
    subst this
    simp [h, hl]
  · simp [h, defaultOrder_length]

theorem orderAt_table (S : Lkp.Public) (d mu : Nat) :
    ∀ l, l < d → (orderAt S false d mu l).length = mu + l := by
  intro l _
  simp [orderAt, defaultOrder_length]

/-- The map that says where the bits are keeps a row fine. -/
theorem mapsOK_bits (S : Lkp.Public) (hS : Sized S) :
    MapsOK S (S.mu + S.d) [fun row point coeff => (envOf S).planesAt row (Tensor.eq point coeff)] := by
  intro m hm row point coeff hrow hp
  simp only [List.mem_singleton] at hm
  subst hm
  exact fine_planes S row hrow _ (by simp [Tensor.eq, Tensor.vars, hp])
    (eq_ok point coeff (by rw [hp]; exact hS.small))

/-- The sum on the leaves of the table's tree. -/
def leavesSum (S : Lkp.Public) (c : PointClaim) : Psc.Claim where
  vars := (Lkp.defaultOrder (S.mu + S.d)).map fun t =>
    Psc.Weight.equality (c.point.getD t zeroE) (if t < S.mu then 2 else 3)
  masks := c.masks
  target := c.value

theorem leavesSum_d (S : Lkp.Public) (c : PointClaim) :
    (leavesSum S c).vars.map (·.d) =
      (Lkp.defaultOrder (S.mu + S.d)).map fun t => if t < S.mu then 2 else 3 := by
  simp [leavesSum, Psc.Weight.equality, List.map_map, Function.comp_def]

theorem sum_leaves (d mu : Nat) :
    ((List.replicate d 3 ++ List.replicate mu 2).map (· - 1)).sum = 2 * d + mu := by
  simp [List.map_append, List.map_replicate, List.sum_append]
  omega

/-- A whole lookup goes through, whatever the values. -/
theorem run_at (S : Lkp.Public) (work v : Nat) (h : Shaped S work v) (rs : List FlatRound)
    (hfit : FitsAll rs (blockEntries S work v)) :
    ∃ c alpha last k rows, NoRows last ∧ ClaimOK S v c ∧
      (Lkp.run (envOf S)) (ctxAt S (blockEntries S work v) none (rvs rs) none 0 #[]) =
        .ok ({ theta := zeroE, alpha := alpha, keys := [Lkp.keysOf S zeroE alpha 0 c] },
          ctxAt S [] none [] last k rows) ∧
      Added S (1 + (S.planes - 2) + v + S.d + 1 + 1 + 1 + 1) #[] rows := by
  have hS := h.sized
  have hR := h.reads
  have hM := h.masks
  unfold blockEntries at hfit ⊢
  obtain ⟨alpha, rs1, hf1, hrun1⟩ := drawOne_at S work "LKP" _ rs none 0 #[] (by intro e he; cases he) hfit
  -- the tie's first step
  obtain ⟨first, rs2, last2, row2, hf2, hq2, hrun2, hends2, hall2, hfine2⟩ :=
    value_at S hS hR work { vars := [], masks := [], target := zeroE } rfl
      (Lkp.summandTieFirst (Lkp.factorOf S zeroE alpha)) (by show 0 < 3; omega) (by show 0 < 3; omega) rfl
      (fun _ _ => rfl)
      _ rs1 _ 0 #[] (noRows_rDraw "LKP" work 1) hf1 (by show 0 + (1 + 3 + 3) ≤ _; omega)
      (by intro p hp; simp at hp)
  obtain ⟨x, y, z, he⟩ : ∃ a b c, first.ends = [a, b, c] := by
    have h3 : first.ends.length = 3 := hends2
    match first.ends, h3 with
    | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
  -- its later steps
  obtain ⟨later, rs3, last3, rows3, hf3, hq3, hrun3, hl3, had3⟩ :=
    tieSteps_at S hS hR work _ (S.planes - 2) y rs2 last2 (0 + (1 + 3 + 3)) (#[].push row2)
      (hall2 y (by simp [he])) hq2 hf2 (by omega)
  -- JOIN
  obtain ⟨r, rs4, hf4, hr4, hrun4⟩ := draws_at S work S.mu "JOIN" _ rs3 last3
    (0 + (1 + 3 + 3) + 6 * (S.planes - 2)) rows3 hq3 hf3
  have hTop : ClaimOK S (S.mu + (S.d - S.d)) (Lkp.joinPlanes S r (z :: later)) := by
    have := joinPlanes_ok S r (z :: later) (by
      intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact hall2 _ (by simp [he])
      · exact hl3 q hq)
    rw [hr4] at this
    simpa using this
  -- the key tree
  obtain ⟨onLeaves, rs5, last5, rows5, hf5, hq5, hrun5, hc5, had5⟩ :=
    levelChain_at S hS hR work true v 0 (orderAt_keys S v h.lastOrder) _ v x rs4 _
      (0 + (1 + 3 + 3) + 6 * (S.planes - 2)) rows3 (Nat.le_refl v)
      (by have := hall2 x (by simp [he]); simpa using this) (noRows_rDraw "JOIN" work S.mu) hf4
      (by omega)
  -- the table's tree
  obtain ⟨onTable, rs6, last6, rows6, hf6, hq6, hrun6, hc6, had6⟩ :=
    levelChain_at S hS hR work false S.d S.mu (orderAt_table S S.d S.mu) _ S.d
      (Lkp.joinPlanes S r (z :: later)) rs5 last5
      (0 + (1 + 3 + 3) + 6 * (S.planes - 2) + chainMasks 0 (v - v) v) rows5 (Nat.le_refl _) hTop hq5 hf5
      (by omega)
  -- the leaves
  have hLd := (leavesSum_d S onTable).trans h.leaves
  have hLlen : (leavesSum S onTable).vars.length = S.mu + S.d := by
    simp [leavesSum, defaultOrder_length]
  have hLsz : Psc.sizeOf (leavesSum S onTable)
      (Lkp.summandLeaves S zeroE alpha (Lkp.defaultOrder (S.mu + S.d))) = leavesSize S := by
    simp only [Psc.sizeOf, hLd, leavesSize, Lkp.summandLeaves]
    rfl
  have hLvo : Psc.varsOf (leavesSum S onTable)
      (Lkp.summandLeaves S zeroE alpha (Lkp.defaultOrder (S.mu + S.d))) = (leavesSum S onTable).vars := rfl
  have hLmk : Psc.masksOf (leavesSum S onTable)
      (Lkp.summandLeaves S zeroE alpha (Lkp.defaultOrder (S.mu + S.d))) = 1 + S.mu + 2 * S.d := by
    have e1 : (leavesSum S onTable).vars.map (fun w => w.d - 1) =
        (List.replicate S.d 3 ++ List.replicate S.mu 2).map (· - 1) := by
      rw [← hLd, List.map_map]
      rfl
    have e2 : Psc.masksOf (leavesSum S onTable)
        (Lkp.summandLeaves S zeroE alpha (Lkp.defaultOrder (S.mu + S.d))) =
        1 + ((leavesSum S onTable).vars.map (fun w => w.d - 1)).sum + 0 := rfl
    rw [e2, e1, sum_leaves]
    omega
  have hLw : ∀ w ∈ (leavesSum S onTable).vars, w.fits = true ∧ 1 ≤ w.d := by
    intro w hw
    simp only [leavesSum, List.mem_map] at hw
    obtain ⟨t, _, rfl⟩ := hw
    by_cases ht : t < S.mu <;> simp [Psc.Weight.fits, Psc.Weight.equality, ht]
  have hLne : (leavesSum S onTable).vars ≠ [] := by
    intro h0
    have := congrArg List.length h0
    rw [hLlen] at this
    have := h.some
    simp at *
    omega
  obtain ⟨leaves, rs7, last7, row7, hf7, hq7, hrun7, hpt7, _, _, hfine7⟩ :=
    psc_at S hS hR work (leavesSum S onTable)
      (Lkp.summandLeaves S zeroE alpha (Lkp.defaultOrder (S.mu + S.d))) false
      [fun row point coeff => (envOf S).planesAt row (Tensor.eq point coeff)]
      (fun p => Lkp.byVariable p (Lkp.defaultOrder (S.mu + S.d))) _ rs6 last6
      (0 + (1 + 3 + 3) + 6 * (S.planes - 2) + chainMasks 0 (v - v) v + chainMasks S.mu (S.d - S.d) S.d)
      rows6 hq6 (by rw [hLsz]; exact hf6)
      (by
        have ha : (leavesSum S onTable).vars.all Psc.Weight.fits = true :=
          List.all_eq_true.2 fun w hw => (hLw w hw).1
        have hb : (leavesSum S onTable).vars.isEmpty = false := by
          cases hv : (leavesSum S onTable).vars with
          | nil => exact absurd hv hLne
          | cons _ _ => rfl
        simp [Psc.formOK, Lkp.summandLeaves, ha, hb])
      (fun _ _ => rfl) (by rw [hLvo]; exact fun w hw => (hLw w hw).2) (by rw [hLvo]; exact hLne)
      (by rw [hLvo]; exact Nat.le_refl _) (by rw [hLmk]; omega) (by intro hh; cases hh) hc6.2 rfl
      (by rw [hLlen]; exact mapsOK_bits S hS) (fun p => byVariable_length p _)
  rw [hLsz, hLmk] at hrun7
  -- ZERO
  obtain ⟨zeta, rs8, hf8, hz8, hrun8⟩ := draws_at S work (S.mu + S.d) "ZERO" _ rs7 last7
    (0 + (1 + 3 + 3) + 6 * (S.planes - 2) + chainMasks 0 (v - v) v + chainMasks S.mu (S.d - S.d) S.d +
      (1 + S.mu + 2 * S.d)) (rows6.push row7) hq7 hf7
  -- the bits
  have hOl := defaultOrder_length (S.mu + S.d)
  have hBsz : Psc.sizeOf (levelSum ⟨zeta, [], zeroE⟩ (Lkp.defaultOrder (S.mu + S.d))) Lkp.summandBits =
      bitsSize S := by
    simp [Psc.sizeOf, levelSum, Lkp.summandBits, bitsSize, Psc.Weight.equality, List.map_map,
      Function.comp_def, List.map_const', hOl]
  have hBmk : Psc.masksOf (levelSum ⟨zeta, [], zeroE⟩ (Lkp.defaultOrder (S.mu + S.d))) Lkp.summandBits =
      1 + 2 * (S.mu + S.d) + 2 + 1 := by
    simp [Psc.masksOf, Psc.varsOf, Psc.hidingEntries, levelSum, Lkp.summandBits,
      Psc.Weight.equality, Psc.Weight.atZero, List.map_map, Function.comp_def, List.map_const', hOl]
    omega
  have hBlen : (levelSum ⟨zeta, [], zeroE⟩ (Lkp.defaultOrder (S.mu + S.d))).vars.length = S.mu + S.d := by
    simp [levelSum, hOl]
  obtain ⟨bits, rs9, last9, row9, hf9, hq9, hrun9, hpt9, hends9, hall9, hfine9⟩ :=
    psc_at S hS hR work (levelSum ⟨zeta, [], zeroE⟩ (Lkp.defaultOrder (S.mu + S.d))) Lkp.summandBits false []
      (fun p => Lkp.byVariable p (Lkp.defaultOrder (S.mu + S.d))) [] rs8 _
      (0 + (1 + 3 + 3) + 6 * (S.planes - 2) + chainMasks 0 (v - v) v + chainMasks S.mu (S.d - S.d) S.d +
        (1 + S.mu + 2 * S.d)) (rows6.push row7) (noRows_rDraw "ZERO" work (S.mu + S.d))
      (by rw [hBsz]; exact hf8)
      (by simp [Psc.formOK, Lkp.summandBits, levelSum, Psc.Weight.fits, Psc.Weight.equality])
      (fun _ _ => rfl)
      (by
        intro x hx
        simp only [Psc.varsOf, Lkp.summandBits, levelSum] at hx
        simp at hx
        rcases hx with ⟨t, _, rfl⟩ | rfl <;> simp [Psc.Weight.equality, Psc.Weight.atZero])
      (by simp [Psc.varsOf, Lkp.summandBits]) (by simp [Psc.varsOf, Lkp.summandBits])
      (by rw [hBmk]; omega) (by intro hh; cases hh) (by intro p hp; simp [levelSum] at hp) rfl
      (by intro m hm; simp at hm) (fun p => byVariable_length p _)
  rw [hBsz, hBmk] at hrun9
  have hrs9 : rs9 = [] := by
    cases rs9 with
    | nil => rfl
    | cons _ _ => simp [FitsAll] at hf9
  subst hrs9
  obtain ⟨e9, he9⟩ : ∃ a, bits.ends = [a] := by
    have h1 : bits.ends.length = 1 := hends9
    match bits.ends, h1 with
    | [a], _ => exact ⟨a, rfl⟩
  have h9 := hall9 e9 (by simp [he9])
  -- the two last rows
  have hrowA : Fine S (pointRow e9 fun row point coeff => (envOf S).planesAt row (Tensor.eq point coeff)) := by
    unfold pointRow
    apply fine_addMasks S _ _ _ h9.2
    exact mapsOK_bits S hS (fun row point coeff => (envOf S).planesAt row (Tensor.eq point coeff))
      (by simp) { target := e9.value } e9.point oneE (fine_target S _) (by rw [h9.1, hpt9, hBlen])
  have hrowB : Fine S ((envOf S).planesAt { target := Lkp.natE (S.allKeys - Lkp.paddingCount S) }
      { pairs := ((List.range S.mu).map fun t => (oneE, Lkp.natE (2 ^ 2 ^ t))) ++
          List.replicate S.d (oneE, oneE) }) := by
    apply fine_planes S _ (fine_target S _)
    · simp [Tensor.vars]
    · have := hS.small
      simp [Tensor.ok, Tensor.vars, distinctNats, this]
  refine ⟨onLeaves, alpha, last9,
    0 + (1 + 3 + 3) + 6 * (S.planes - 2) + chainMasks 0 (v - v) v + chainMasks S.mu (S.d - S.d) S.d +
      (1 + S.mu + 2 * S.d) + (1 + 2 * (S.mu + S.d) + 2 + 1),
    (((rows6.push row7).push row9).push
      (pointRow e9 fun row point coeff => (envOf S).planesAt row (Tensor.eq point coeff))).push
      ((envOf S).planesAt { target := Lkp.natE (S.allKeys - Lkp.paddingCount S) }
        { pairs := ((List.range S.mu).map fun t => (oneE, Lkp.natE (2 ^ 2 ^ t))) ++
            List.replicate S.d (oneE, oneE) }),
    hq9, by simpa using hc5, ?_,
    (((((((Added.push #[] hfine2).trans had3).trans had5).trans had6).trans
      (Added.push rows6 hfine7)).trans (Added.push _ hfine9)).trans (Added.push _ hrowA)).trans
      (Added.push _ hrowB)⟩
  unfold Lkp.run
  simp only [show (envOf S).S = S from rfl, h.noShift, Bool.false_eq_true, if_false]
  rw [bind_ok (pure_ok _ _), bind_ok hrun1, bind_ok (note_at _ _ _ _ _ _ _ _ _),
    bind_ok (note_at _ _ _ _ _ _ _ _ _)]
  refine (bind_ok hrun2).trans ?_
  rw [he]
  simp only []
  rw [bind_ok (pure_ok _ _)]
  refine (bind_ok hrun3).trans ?_
  rw [h.parts]
  refine (bind_ok (show (Lkp.partSteps (envOf S) ([v].length - 1) x) _ = .ok ([x], _) from rfl)).trans ?_
  refine (bind_ok hrun4).trans ?_
  refine (bind_ok (note_at _ _ _ _ _ _ _ _ _)).trans ?_
  have hkt : (Lkp.keyTrees (envOf S) [v] [x]) (ctxAt S
      (chainEntries work 0 (v - v) v ++ (chainEntries work S.mu (S.d - S.d) S.d ++
        (pscEntries work (leavesSize S) ++ (rDraw "ZERO" work (S.mu + S.d)).entry ::
          (pscEntries work (bitsSize S) ++ [])))) none (rvs rs4) (some (rDraw "JOIN" work S.mu).entry)
      (0 + (1 + 3 + 3) + 6 * (S.planes - 2)) rows3) = .ok ([onLeaves], ctxAt S
      (chainEntries work S.mu (S.d - S.d) S.d ++
        (pscEntries work (leavesSize S) ++ (rDraw "ZERO" work (S.mu + S.d)).entry ::
          (pscEntries work (bitsSize S) ++ []))) none (rvs rs5) last5
      (0 + (1 + 3 + 3) + 6 * (S.planes - 2) + chainMasks 0 (v - v) v) rows5) := by
    show ((Lkp.levelChain (envOf S) true v 0 v x) >>= fun a =>
      (Lkp.keyTrees (envOf S) [] []) >>= fun rest => pure (a :: rest)) _ = _
    rw [bind_ok hrun5]
    rfl
  refine (bind_ok hkt).trans ?_
  refine (bind_ok hrun6).trans ?_
  refine (bind_ok hrun7).trans ?_
  refine (bind_ok (note_at _ _ _ _ _ _ _ _ _)).trans ?_
  refine (bind_ok hrun8).trans ?_
  refine (bind_ok hrun9).trans ?_
  rw [he9]
  refine (bind_ok (get_ok e9 _)).trans ?_
  refine (bind_ok (leave_at S hS hR _ _ _ _ _ _ hrowA)).trans ?_
  refine (bind_ok (leave_at S hS hR _ _ _ _ _ _ hrowB)).trans ?_
  refine (bind_ok (must_ok (by simp) _)).trans ?_
  refine (bind_ok (noteKeys_at _ rfl _)).trans ?_
  rfl

/-! ## The caller's block, and the run on plain data -/

theorem fitsAll_of_fits : ∀ (rs : List FlatRound) (es : List Fmt.Entry), rs.length = es.length →
    ((rs.zip es).all fun p => p.1.fits p.2) = true → FitsAll rs es
  | [], [], _, _ => trivial
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | r :: rs, e :: es, h, ha => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at ha
    exact ⟨ha.1, fitsAll_of_fits rs es (by simpa using h) ha.2⟩

/-- The claim on the keys has the coefficient 0 on every place of padding, whatever the values: as
the program reckons it, the sum of 0 and the weights' entry there has three words 0. A statement for
all alpha and all claims at a point of v coordinates; it speaks of no transcript. -/
def PaddingOut (S : Lkp.Public) (v : Nat) : Prop :=
  ∀ (alpha : E) (c : PointClaim), ClaimOK S v c → ∀ i, i < 2 ^ S.firstBits → isPadding S i = true →
    isZeroE (addE zeroE ((Lkp.keysOf S zeroE alpha 0 c).weights.entry i)) = true

/-- The caller's block goes through, whatever the values. -/
theorem block_at (S : Lkp.Public) (v : Nat) (h : Shaped S 0 v) (hP : PaddingOut S v)
    (rs : List FlatRound) (hfit : FitsAll rs (blockEntries S 0 v)) :
    ∃ out last k rows, NoRows last ∧
      (block S) (ctxAt S (blockEntries S 0 v) none (rvs rs) none 0 #[]) =
        .ok ((out, rows), ctxAt S [] none [] last k rows) ∧
      Added S (1 + (S.planes - 2) + v + S.d + 1 + 1 + 1 + 1 + 1) #[] rows := by
  obtain ⟨c, alpha, last, k, rows, hq, hc, hrun, had⟩ := run_at S 0 v h rs hfit
  have hfb : S.firstBits = v := by simp [Lkp.Public.firstBits, h.parts]
  have hrow : Fine S (keysRow (Lkp.keysOf S zeroE alpha 0 c)) :=
    fine_keysRow S zeroE alpha c (by rw [hfb]; exact hc) (by rw [hfb]; exact h.keys63) (hP alpha c hc)
  have hver : (Lkp.verify S (fun row v => row.add planesMessage .main v) masksMessage theGroup)
      (ctxAt S (blockEntries S 0 v) none (rvs rs) none 0 #[]) =
      .ok ({ theta := zeroE, alpha := alpha, keys := [Lkp.keysOf S zeroE alpha 0 c] },
        ctxAt S [] none [] last k rows) := by
    unfold Lkp.verify
    rw [h.reads]
    refine (bind_ok (show (Lkp.mustBeSampled [masksMessage]) _ = .ok ((), _) from rfl)).trans ?_
    refine (bind_ok (must_ok h.ok _)).trans ?_
    refine (bind_ok (show (Lkp.mustBeSampled [keysMessage, planesMessage]) _ = .ok ((), _) from rfl)).trans ?_
    exact hrun
  refine ⟨({ theta := zeroE, alpha := alpha, keys := [Lkp.keysOf S zeroE alpha 0 c] } : Lkp.Out), last, k,
    rows.push (keysRow (Lkp.keysOf S zeroE alpha 0 c)), hq, ?_, had.trans (Added.push rows hrow)⟩
  unfold block
  rw [bind_ok hver]
  simp only []
  rw [bind_ok (bind_ok (addRow_at S h.sized [] [] last k rows _ hrow))]
  rfl

/-- THE LAW. On plain data that fit, the program's run at the least caller goes through: it fails on
no value that is sent or drawn. The premises are on the public inputs alone. One of them,
`PaddingOut`, is the padding clause of `Fine` at the caller's row on the keys: assumed, not shown
(fine_keysRow). As stated, it is asked for "the run goes through" too. By a reading of the proofs,
`addRow_at` uses the other five fields of `Fine` alone; the padding clause is carried from one
`Fine` to the next (fine_addMasks, fine_planes), and something else than `Fine` is concluded from it
in `onCaller_of_fine` alone. -/
theorem portOn_ok (S : Lkp.Public) (v : Nat) (h : Shaped S 0 v) (hP : PaddingOut S v)
    (hcodes : (statement S).codes.lengthsOk = true) (t : Flat) (ht : t.fits S = true) :
    ∃ out rows, portOn S t = .ok (out, rows) ∧
      Added S (1 + (S.planes - 2) + v + S.d + 1 + 1 + 1 + 1 + 1) #[] rows := by
  simp only [Flat.fits, Bool.and_eq_true, beq_iff_eq] at ht
  have hfit : FitsAll t.rounds (blockEntries S 0 v) := by
    rw [← h.entries]
    exact fitsAll_of_fits _ _ ht.1.1 ht.1.2
  obtain ⟨out, last, k, rows, hq, hb, had⟩ := block_at S v h hP t.rounds hfit
  refine ⟨out, rows, ?_, had⟩
  have hs := settled_of_noRows (S := S) (es := []) (cur := none) (rs := []) (k := k) (rows := rows) hq
  have hn : (block S).runNamed (start S 0) false t.view.rounds t.view.opened =
      .ok ((out, rows), ctxAt S [] none [] last k rows) := by
    unfold Blk.runNamed
    rw [if_pos (show (start S 0).st.codes.lengthsOk = true from hcodes)]
    rw [← hb, ← h.entries]
    rfl
  unfold portOn Blk.runOn
  rw [hn]
  simp [ctxAt, hs] at hs ⊢

/-- A row that the caller's group takes reads nothing but the caller's three vectors. -/
theorem onCaller_of_fine (S : Lkp.Public) (r : Row) (h : Fine S r) : onCaller S r = true := by
  unfold onCaller
  simp only [Bool.and_eq_true, Array.all_eq_true_iff_forall_mem, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨by simp [h.runs], ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro t ht
    obtain ⟨a, b, _, _⟩ := h.terms t ht
    simp [a, b]
  · intro u hu
    obtain ⟨a, b, c⟩ := h.units u hu
    simp [a, b, c]
  · intro f hf
    simp [(h.forms f hf).1]
  · intro i hi
    cases hp : isPadding S i with
    | false => rfl
    | true => simp [h.atPadding i hi hp]

/-- THE SECOND LAW. On plain data that fit, the program hands on end claims, and as many as the
public inputs say: a row for each sumcheck, two rows on the bits, and the caller's row on the keys.
For that last row the padding clause of `onCaller` is the premise `PaddingOut`: assumed, not shown.
-/
theorem endClaims_some (S : Lkp.Public) (v : Nat) (h : Shaped S 0 v) (hP : PaddingOut S v)
    (hcodes : (statement S).codes.lengthsOk = true) (hs : served S = true) (t : Flat)
    (ht : t.fits S = true) :
    ∃ l, endClaims S t = some l ∧ l.length = 1 + (S.planes - 2) + v + S.d + 1 + 1 + 1 + 1 + 1 := by
  obtain ⟨out, rows, hrun, new, hrows, hlen, hfine⟩ := portOn_ok S v h hP hcodes t ht
  have hall : rows.all (onCaller S) = true := by
    rw [Array.all_eq_true_iff_forall_mem]
    intro r hr
    rw [hrows] at hr
    exact onCaller_of_fine S r (hfine r (by simpa using hr))
  refine ⟨rows.toList.map (ofRow S), ?_, by rw [hrows]; simp [hlen]⟩
  unfold endClaims
  rw [if_pos (by simp [hs, ht]), hrun]
  simp [hall]

end OnBytes.G4
