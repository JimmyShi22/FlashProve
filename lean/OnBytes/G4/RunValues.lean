-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/G4/RunValues.lean: what the program's lookup verifier computes on plain data that fit, call
by
call, with every value named; and the whole run and its end claims as a function of the plain data.

OnBytes/G4/RunLaws.lean shows that each call of the run goes through and says sizes of what it
gives. This
file states the same calls again as equations whose right sides are written out.
 - Which mask entries are taken: `slotsFrom k n`, the next n of the caller's mask row (`fresh_val`).
 - Which rounds are read: `heardOf`, `restOf`: plain functions on the next rounds (`hear_val`).
 - What a sumcheck hands on: `pscOut`: what Psc.run gives at these, with its points put back; and
   which
   row goes to the group: `pscRow`: the row that Lkp.psc makes of it (`psc_val`).
 - A `Stand` is where a run stands: the rounds left, the mask entries taken, the rows added.
   `levelVal`,
   `chainVal`, `tieVal` and `courseOf` are functions on stands, without a state monad and without a
   failure
   (`line_val`, `level_val`, `chain_val`, `value_val`, `tie_val`, `drawOne_val`, `draws_val`,
   `run_val`).
 - `portOn_eq`: on plain data t that fit, portOn S t = .ok ((t.course S v).out S, t.rowsOf S v).
 - `endClaims_eq`: endClaims S t = some ((t.rowsOf S v).toList.map (ofRow S)).
 - What a row holds, list by list: `addMasks_eq`, `pscRow_nil`, `pscRow_bits`, `pointRow_bits`,
   `keysRow_eq`. With
   these, the library's law on a row's coefficient (Row.coefficient_val, OnBytes/Iop/RowLaws.lean)
   reads a row
   as a dense vector.
The functions are made of the program's own pure parts: Psc.run, lineAt, Lkp.joinPlanes, Lkp.keysOf,
Lkp.byVariable, the summands, Psc.rowU, pointRow. Nothing of their arithmetic is opened here.

The premises are those of OnBytes/G4/RunLaws.lean: Shaped, PaddingOut, the codes' lengths, served,
and
t.fits S = true.

Main definitions: pairOf, heardOf, restOf, pscOut, pscRow, Stand, levelVal, chainVal, valueSum,
tieVal,
bitsAt, countsRow, Course, zeroSum, courseOf, Course.out, singlesOf, Flat.course, Flat.rowsOf.
Main theorems: portOn_eq, endClaims_eq, run_val, chain_val, tie_val, level_val, value_val, psc_val,
hear_val.
Not claimed: as in OnBytes/G4/RunLaws.lean: all is at the least caller of OnBytes/G4/Flat.lean,
which no
program has. Where the data do not fit, the functions give values without meaning (defaults). The
entry of
the round closed last is named nowhere: it has no part in a value.
-/
import OnBytes.G4.RunLaws

set_option autoImplicit false

namespace OnBytes.G4

open Blk

/-- A round in which one element is drawn, as a sumcheck reads it: what is sent, and that element.
-/
def pairOf (r : FlatRound) : List E × E := (r.sent, r.drawn.headD zeroE)

/-- What a sumcheck of the given sizes reads of the next rounds. -/
def heardOf (x : Psc.Size) : List FlatRound → Psc.Heard
  | [] => default
  | r :: rs =>
    let inX := (rs.take x.degree.length).map pairOf
    if x.withY then
      match rs.drop x.degree.length with
      | rY :: rV :: _ => ⟨r.sent.headD zeroE, r.drawn.headD zeroE, inX ++ [pairOf rY], rV.sent⟩
      | _ => default
    else ⟨r.sent.headD zeroE, r.drawn.headD zeroE, inX, []⟩

/-- The rounds that a sumcheck of the given sizes leaves. -/
def restOf (x : Psc.Size) : List FlatRound → List FlatRound
  | [] => []
  | _ :: rs => if x.withY then (rs.drop x.degree.length).drop 2 else rs.drop x.degree.length

/-- The rounds of the variables of a sumcheck, with what is read named. -/
theorem hearMany_val (S : Lkp.Public) (work k : Nat) (rows : Array Row) (es' : List Fmt.Entry) :
    ∀ (ns : List Nat) (rs : List FlatRound) (last : Option Fmt.Entry), NoRows last →
      FitsAll rs (ns.map (fun n => (Psc.rOne "PSC round" .elems work n 0).entry) ++ es') →
      ∃ last', FitsAll (rs.drop ns.length) es' ∧ NoRows last' ∧
        (Psc.hearMany ns)
            (ctxAt S (ns.map (fun n => (Psc.rOne "PSC round" .elems work n 0).entry) ++ es')
          none (rvs rs) last k rows) =
          .ok ((rs.take ns.length).map pairOf, ctxAt S es' none (rvs (rs.drop ns.length)) last' k
              rows)
  | [], rs, last, hq, h => ⟨last, h, hq, rfl⟩
  | n :: ns, [], last, hq, h => by simp [FitsAll] at h
  | n :: ns, r :: rs, last, hq, h => by
    obtain ⟨hr, hrest⟩ := h
    have hm : Meets r (Psc.rOne "PSC round" .elems work n 0).entry "PSC round" n 1 0 :=
      meets_of_fits hr rfl rfl rfl rfl rfl rfl rfl
    obtain ⟨g, hg, h1⟩ := hearOne_at S _
      (ns.map (fun n => (Psc.rOne "PSC round" .elems work n 0).entry) ++ es')
      (rvs rs) last k rows r "PSC round" .elems n 0 hm hq
    obtain ⟨last', hf, hq', h2⟩ := hearMany_val S work k rows es' ns rs _ hm.noRows hrest
    refine ⟨last', hf, hq', ?_⟩
    show ((Psc.hearOne "PSC round" .elems n 0) >>= fun a =>
      (Psc.hearMany ns) >>= fun l => pure (a :: l)) _ = _
    rw [show (List.map (fun n => (Psc.rOne "PSC round" .elems work n 0).entry) (n :: ns) ++ es') =
      (Psc.rOne "PSC round" .elems work n 0).entry ::
        (ns.map (fun n => (Psc.rOne "PSC round" .elems work n 0).entry) ++ es') from rfl]
    rw [show rvs (r :: rs) = r.rv :: rvs rs from rfl, bind_ok h1, bind_ok h2, pure_ok]
    simp [pairOf, hg]

/-- Reading the rounds of a sumcheck, with what is read named. -/
theorem hear_val (S : Lkp.Public) (work k : Nat) (rows : Array Row) (x : Psc.Size)
    (es' : List Fmt.Entry) (rs : List FlatRound) (last : Option Fmt.Entry) (hq : NoRows last)
    (h : FitsAll rs (pscEntries work x ++ es')) :
    ∃ last', FitsAll (restOf x rs) es' ∧ NoRows last' ∧
      (Psc.hear x) (ctxAt S (pscEntries work x ++ es') none (rvs rs) last k rows) =
        .ok (heardOf x rs, ctxAt S es' none (rvs (restOf x rs)) last' k rows) := by
  rw [pscEntries_eq] at h ⊢
  cases rs with
  | nil => simp [FitsAll] at h
  | cons r rs =>
    obtain ⟨hr, hrest⟩ := h
    have hm : Meets r (Psc.rOne "PSC epsilon" .join work 1 0).entry "PSC epsilon" 1 1 0 :=
      meets_of_fits hr rfl rfl rfl rfl rfl rfl rfl
    obtain ⟨eps, heps, h1⟩ := hearOne_at S _ _ (rvs rs) last k rows r "PSC epsilon" .join 1 0 hm hq
    obtain ⟨mu, hmu⟩ := List.length_eq_one_iff.1 hm.sent
    obtain ⟨last1, hf1, hq1, h2⟩ := hearMany_val S work k rows _ _ rs _ hm.noRows hrest
    simp only [List.length_map] at hf1 h2
    unfold Psc.hear
    rw [show rvs (r :: rs) = r.rv :: rvs rs from rfl, bind_ok h1]
    simp only [hmu, List.head?_cons]
    rw [bind_ok (get_ok mu _), bind_ok h2]
    cases hY : x.withY with
    | false =>
      simp only [hY, Bool.false_eq_true, if_false, List.nil_append] at hf1 ⊢
      refine ⟨last1, by simpa [restOf, hY] using hf1, hq1, ?_⟩
      simp [heardOf, restOf, hY, hmu, heps, pure_ok]
    | true =>
      simp only [hY, if_true, List.cons_append, List.nil_append] at hf1 ⊢
      cases hd : rs.drop x.degree.length with
      | nil => simp [hd, FitsAll] at hf1
      | cons rY rs2 =>
        rw [hd] at hf1
        obtain ⟨hrY, hf2⟩ := hf1
        cases rs2 with
        | nil => simp [FitsAll] at hf2
        | cons rV rs3 =>
          obtain ⟨hrV, hf3⟩ := hf2
          have hmY : Meets rY (Psc.rOne "PSC Y" .elems work x.degreeY 1).entry "PSC Y" x.degreeY 1
              1 :=
            meets_of_fits hrY rfl rfl rfl rfl rfl rfl rfl
          have hmV : Meets rV (Psc.rValues x.values).entry "PSC values" x.values 0 0 :=
            meets_of_fits hrV rfl rfl rfl rfl rfl rfl rfl
          obtain ⟨beta, hbeta, h3⟩ := hearOne_at S _ ((Psc.rValues x.values).entry :: es')
            (rvs (rV :: rs3)) last1 k rows rY "PSC Y" .elems x.degreeY 1 hmY hq1
          refine ⟨_, by simpa [restOf, hY, hd] using hf3, hmV.noRows, ?_⟩
          rw [show rvs (rY :: rV :: rs3) = rY.rv :: rvs (rV :: rs3) from rfl, bind_ok h3]
          rw [show rvs (rV :: rs3) = rV.rv :: rvs rs3 from rfl]
          rw [hearValues_at _ S _ es' (rvs rs3) _ k rows rV x.values hmV hmY.noRows]
          simp [heardOf, restOf, hY, hd, hmu, heps, hbeta, pairOf, pure_ok]

/-- Mask entries taken in two goes are those taken in one. -/
theorem slotsFrom_append (k a b : Nat) : slotsFrom k a ++ slotsFrom (k + a) b = slotsFrom k
    (a + b) := by
  simp [slotsFrom, ← List.map_append, List.range'_append_1]

/-- The fresh mask entries of a sumcheck, named: the next n of the caller's mask row. -/
theorem fresh_val (S : Lkp.Public) (es rs last rows) (n k : Nat) (keys : Bool)
    (h : k + n ≤ Lkp.allMasks S) (h2 : keys = true → 2 ≤ n) :
    (Lkp.fresh (envOf S) n keys) (ctxAt S es none rs last k rows) =
      .ok (slotsFrom k n, ctxAt S es none rs last (k + n) rows) := by
  cases keys with
  | false => exact takeSlots_at S es rs last rows n k h
  | true =>
    have hn := h2 rfl
    show ((Blk.must (decide (2 ≤ n))) >>= fun _ => (takeSlots masksMessage (n - 2)) >>= fun a =>
      (takeSlots masksMessage 2) >>= fun b => pure (a ++ b)) _ = _
    rw [bind_ok (must_ok (by simp [hn]) _),
      bind_ok (takeSlots_at S es rs last rows (n - 2) k (by omega)),
      bind_ok (takeSlots_at S es rs last rows 2 (k + (n - 2)) (by omega)), pure_ok,
      show k + (n - 2) + 2 = k + n from by omega, slotsFrom_append,
      show n - 2 + 2 = n from by omega]

/-- What one sumcheck of the lookup hands on: what Psc.run gives at the next mask entries and the
next
rounds, with the coordinates of its points put back at their variables' places. -/
def pscOut (c : Psc.Claim) (Sm : Psc.Summand) (place : List E → List E) (k : Nat)
    (rs : List FlatRound) : Psc.Out :=
  let o := (Psc.run c Sm (slotsFrom k (Psc.masksOf c Sm)) (heardOf (Psc.sizeOf c Sm) rs)).getD
      default
  { o with
    point := place o.point
    ends := o.ends.map fun x => { x with point := place x.point } }

/-- The row that one sumcheck of the lookup adds to the group. -/
def pscRow (c : Psc.Claim) (Sm : Psc.Summand) (kept : List MapAt) (place : List E → List E)
    (k : Nat)
    (rs : List FlatRound) : Row :=
  (Psc.rowU (pscOut c Sm place k rs) kept).getD {}

/-- One sumcheck of the lookup, with every value named. -/
theorem psc_val (S : Lkp.Public) (hS : Sized S) (hR : S.readFrom = [keysMessage, planesMessage])
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
    ∃ last', FitsAll (restOf (Psc.sizeOf c Sm) rs) es' ∧ NoRows last' ∧
      (Lkp.psc (envOf S) c Sm lastOfKeys kept place)
          (ctxAt S (pscEntries work (Psc.sizeOf c Sm) ++ es') none (rvs rs) last k rows) =
        .ok (pscOut c Sm place k rs,
          ctxAt S es' none (rvs (restOf (Psc.sizeOf c Sm) rs)) last' (k + Psc.masksOf c Sm)
            (rows.push (pscRow c Sm kept place k rs))) ∧
      (pscOut c Sm place k rs).point.length = c.vars.length ∧
      (pscOut c Sm place k rs).ends.length = Sm.shown ∧
      (∀ e ∈ (pscOut c Sm place k rs).ends,
        e.point = (pscOut c Sm place k rs).point ∧ SlotsOK S e.masks) ∧
      Fine S (pscRow c Sm kept place k rs) := by
  have hfr := fresh_val S (pscEntries work (Psc.sizeOf c Sm) ++ es') (rvs rs) last rows
    (Psc.masksOf c Sm) k lastOfKeys hk h2
  obtain ⟨last', hf', hq', hhear⟩ :=
    hear_val S work (k + Psc.masksOf c Sm) rows (Psc.sizeOf c Sm) es' rs last hq hfit
  -- the sizes of what is heard: RunLaws' hear_at speaks of the same call
  obtain ⟨hd', _, _, _, _, hhear', hlens, hvals⟩ :=
    hear_at S work (k + Psc.masksOf c Sm) rows (Psc.sizeOf c Sm) es' rs last hq hfit
  have hsame : hd' = heardOf (Psc.sizeOf c Sm) rs := by
    rw [hhear] at hhear'
    exact (congrArg Prod.fst (Except.ok.inj hhear')).symm
  subst hsame
  rw [lens_eq] at hlens
  have hv : (heardOf (Psc.sizeOf c Sm) rs).values.length = Sm.shown := by
    rw [hvals]
    unfold Psc.sizeOf
    by_cases h : Sm.shown = 0 <;> simp [h, Nat.pos_of_ne_zero]
  have hfs : ∀ s ∈ slotsFrom k (Psc.masksOf c Sm), s.oracle = masksMessage ∧ s.index < Lkp.allMasks
      S := by
    intro s hs
    have := mem_slotsFrom hs
    exact ⟨this.1, by omega⟩
  obtain ⟨o, ho, hO⟩ := run_some c Sm (slotsFrom k (Psc.masksOf c Sm))
      (heardOf (Psc.sizeOf c Sm) rs) hform
    (slotsFrom_length _ _) hlens hv ha hd hne hle
  have hout : pscOut c Sm place k rs = { o with
      point := place o.point
      ends := o.ends.map fun x => { x with point := place x.point } } := by
    simp [pscOut, ho]
  have hmasks : SlotsOK S (pscOut c Sm place k rs).rowMasks := by
    rw [hout]
    intro p hp
    rcases hO.masks p hp with h | h
    · exact hfs p.1 h
    · obtain ⟨q, hq1, hq2⟩ := List.mem_map.1 h
      rw [← hq2]
      exact hm q hq1
  have hpl : (pscOut c Sm place k rs).point.length = c.vars.length := by
    rw [hout]
    show (place o.point).length = _
    rw [hplace, hO.point]
  have hrow : Psc.rowU (pscOut c Sm place k rs) kept = some (pscRow c Sm kept place k rs) ∧
      Fine S (pscRow c Sm kept place k rs) := by
    have hl : (kept.length == (pscOut c Sm place k rs).rowMaps.length) = true := by
      rw [hout]
      show (kept.length == o.rowMaps.length) = true
      simp [hkept, hO.maps]
    have he : Psc.rowU (pscOut c Sm place k rs) kept =
        some ((kept.zip (pscOut c Sm place k rs).rowMaps).foldl
          (fun r p => p.1 r (pscOut c Sm place k rs).point p.2)
          (({ target := (pscOut c Sm place k rs).rowTarget } : Row).addMasks
            (pscOut c Sm place k rs).rowMasks)) := by
      unfold Psc.rowU
      rw [if_pos hl]
    refine ⟨by rw [pscRow, he]; rfl, ?_⟩
    rw [pscRow, he]
    apply fine_foldl S c.vars.length _ hpl
    · intro q hq1
      exact hmaps q.1 (List.of_mem_zip hq1).1
    · exact fine_addMasks S _ _ (fine_target S _) hmasks
  refine ⟨last', hf', hq', ?_, hpl, ?_, ?_, hrow.2⟩
  rotate_left
  · rw [hout]
    show (o.ends.map _).length = _
    rw [List.length_map, hO.ends]
  · rw [hout]
    intro e he
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
    obtain ⟨h1, h3⟩ := hO.endsAt x hx
    refine ⟨by show place x.point = place o.point; rw [h1], ?_⟩
    intro p hp
    exact hfs p.1 (h3 p hp)
  have hver : (Psc.verify c Sm (slotsFrom k (Psc.masksOf c Sm)))
      (ctxAt S (pscEntries work (Psc.sizeOf c Sm) ++ es') none (rvs rs) last (k + Psc.masksOf c Sm)
          rows) =
      .ok (o, ctxAt S es' none (rvs (restOf (Psc.sizeOf c Sm) rs)) last' (k + Psc.masksOf c Sm)
          rows) := by
    show ((Psc.hear (Psc.sizeOf c Sm)) >>= fun h =>
      Blk.get (Psc.run c Sm (slotsFrom k (Psc.masksOf c Sm)) h)) _ = _
    rw [bind_ok hhear, ho]
    rfl
  unfold Lkp.psc
  rw [bind_ok hfr, bind_ok hver]
  show ((Blk.get (Psc.rowU ({ o with
      point := place o.point
      ends := o.ends.map fun x => { x with point := place x.point } } : Psc.Out) kept)) >>= fun r =>
    (Lkp.leave (envOf S) r) >>= fun _ => pure ({ o with
      point := place o.point
      ends := o.ends.map fun x => { x with point := place x.point } } : Psc.Out)) _ = _
  rw [← hout, hrow.1, bind_ok (get_ok _ _), bind_ok (leave_at S hS hR es' _ last' _ rows _ hrow.2),
      pure_ok]

/-! ## The run as a function on what is left, what is taken and what is added -/

/-- Where a run stands: the rounds that are left, the number of mask entries taken, the rows added.
-/
structure Stand where
  /-- the rounds that are left -/
  rounds : List FlatRound
  /-- the number of mask entries taken -/
  taken : Nat
  /-- the rows added to the group -/
  rows : Array Row

/-- The context of a stand. -/
def Stand.ctx (s : Stand) (S : Lkp.Public) (es : List Fmt.Entry) (last : Option Fmt.Entry) : Ctx :=
  ctxAt S es none (rvs s.rounds) last s.taken s.rows

/-- The stand after one sumcheck. -/
def Stand.afterPsc (s : Stand) (c : Psc.Claim) (Sm : Psc.Summand) (kept : List MapAt)
    (place : List E → List E) : Stand where
  rounds := restOf (Psc.sizeOf c Sm) s.rounds
  taken := s.taken + Psc.masksOf c Sm
  rows := s.rows.push (pscRow c Sm kept place s.taken s.rounds)

/-- The first element drawn in the next round. -/
def Stand.draw (s : Stand) : E := (s.rounds.headD default).drawn.headD zeroE

/-- The stand after the next round. -/
def Stand.next (s : Stand) : Stand := { s with rounds := s.rounds.tail }

/-- One level of a product tree: the claim on the next level, and the stand after it. -/
def levelVal (order : List Nat) (c : PointClaim) (s : Stand) : PointClaim × Stand :=
  let place := fun p => Lkp.byVariable p order
  let o := pscOut (levelSum c order) Lkp.summandProduct place s.taken s.rounds
  let s1 := s.afterPsc (levelSum c order) Lkp.summandProduct [] place
  (lineAt s1.draw (o.ends.getD 0 default) (o.ends.getD 1 default), s1.next)

/-- The last n levels of a product tree. -/
def chainVal (S : Lkp.Public) (keys : Bool) (levels more : Nat) :
    Nat → PointClaim → Stand → PointClaim × Stand
  | 0, c, s => (c, s)
  | n + 1, c, s =>
    let x := levelVal (orderAt S keys levels more (levels - (n + 1))) c s
    chainVal S keys levels more n x.1 x.2

/-- Two claims at one point become one, with the value named. -/
theorem line_val (S : Lkp.Public) (work : Nat) (es' : List Fmt.Entry) (s : Stand) (last)
    (a b : PointClaim) (hp : a.point = b.point) (hq : NoRows last)
    (hfit : FitsAll s.rounds ((rDraw "LINE" work 1).entry :: es')) :
    FitsAll s.next.rounds es' ∧
      (line a b) (s.ctx S ((rDraw "LINE" work 1).entry :: es') last) =
        .ok (lineAt s.draw a b, s.next.ctx S es' (some (rDraw "LINE" work 1).entry)) := by
  obtain ⟨rounds, taken, rows⟩ := s
  cases rounds with
  | nil => simp [FitsAll] at hfit
  | cons r rs =>
    obtain ⟨hr, hrest⟩ := hfit
    have hm : Meets r (rDraw "LINE" work 1).entry "LINE" 0 1 0 :=
      meets_of_fits hr rfl rfl rfl rfl rfl rfl rfl
    obtain ⟨rho, hrho⟩ := List.length_eq_one_iff.1 hm.drawn
    refine ⟨hrest, ?_⟩
    unfold line Stand.ctx
    rw [bind_ok (must_ok (by simp [hp]) _), bind_ok (test_ok (by simp [hp]) _),
      show rvs (r :: rs) = r.rv :: rvs rs from rfl,
      bind_ok (hearDraw_at S _ es' (rvs rs) last taken rows r "LINE" 1 hm hq), hrho]
    simp [Stand.draw, Stand.next, hrho]
    rfl

/-- One level of a product tree, with every value named. -/
theorem level_val (S : Lkp.Public) (hS : Sized S) (hR : S.readFrom = [keysMessage, planesMessage])
    (work : Nat) (order : List Nat) (lastOfKeys : Bool) (es' : List Fmt.Entry) (s : Stand) (last)
    (c : PointClaim) (hc : ClaimOK S order.length c) (hq : NoRows last)
    (hfit : FitsAll s.rounds (pscEntries work { degree := List.replicate order.length 3 } ++
      (rDraw "LINE" work 1).entry :: es'))
    (hk : s.taken + (2 * order.length + 5) ≤ Lkp.allMasks S) :
    FitsAll (levelVal order c s).2.rounds es' ∧
      (levelVal order c s).2.taken = s.taken + (2 * order.length + 5) ∧
      ClaimOK S (order.length + 1) (levelVal order c s).1 ∧
      ((Lkp.psc (envOf S) (levelSum c order) Lkp.summandProduct lastOfKeys []
          fun p => Lkp.byVariable p order) >>= fun o =>
        match o.ends with
        | [e0, e1] => line e0 e1
        | _ => Blk.fail)
        (s.ctx S (pscEntries work { degree := List.replicate order.length 3 } ++
          (rDraw "LINE" work 1).entry :: es') last) =
        .ok ((levelVal order c s).1,
          (levelVal order c s).2.ctx S es' (some (rDraw "LINE" work 1).entry)) := by
  have hsz := levelSum_size c order
  have hmk := levelSum_masks c order
  -- the sizes: RunLaws' psc_at; the values: psc_val; both speak of one call
  obtain ⟨o1, _, _, _, _, _, hrun1, hpt, hends, hall, _⟩ :=
    psc_at S hS hR work (levelSum c order) Lkp.summandProduct lastOfKeys []
      (fun p => Lkp.byVariable p order) ((rDraw "LINE" work 1).entry :: es') s.rounds last s.taken
          s.rows hq
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
  obtain ⟨last1, hf1, hq1, hrun, _, _, _, _⟩ :=
    psc_val S hS hR work (levelSum c order) Lkp.summandProduct lastOfKeys []
      (fun p => Lkp.byVariable p order) ((rDraw "LINE" work 1).entry :: es') s.rounds last s.taken
          s.rows hq
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
  have hsame : o1 = pscOut (levelSum c order) Lkp.summandProduct (fun p => Lkp.byVariable p order)
      s.taken s.rounds := by
    rw [hrun] at hrun1
    exact (congrArg Prod.fst (Except.ok.inj hrun1)).symm
  subst hsame
  obtain ⟨e0, e1, he⟩ : ∃ e0 e1, (pscOut (levelSum c order) Lkp.summandProduct
      (fun p => Lkp.byVariable p order) s.taken s.rounds).ends = [e0, e1] := by
    have h2 : (pscOut (levelSum c order) Lkp.summandProduct
      (fun p => Lkp.byVariable p order) s.taken s.rounds).ends.length = 2 := hends
    match (pscOut (levelSum c order) Lkp.summandProduct
      (fun p => Lkp.byVariable p order) s.taken s.rounds).ends, h2 with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  have h0 := hall e0 (by simp [he])
  have h1 := hall e1 (by simp [he])
  obtain ⟨hf2, hline⟩ := line_val S work es'
    (s.afterPsc (levelSum c order) Lkp.summandProduct [] fun p => Lkp.byVariable p order) last1 e0
        e1
    (h0.1.trans h1.1.symm) hq1 hf1
  have hvars : (levelSum c order).vars.length = order.length := by simp [levelSum]
  refine ⟨hf2, by simp [levelVal, Stand.next, Stand.afterPsc, hmk], ?_, ?_⟩
  · simp only [levelVal, he, List.getD_cons_zero, List.getD_cons_succ]
    exact ⟨by simp [lineAt, h0.1, hpt, hvars],
      slotsOK_append (slotsOK_scale _ h0.2) (slotsOK_scale _ h1.2)⟩
  rw [← hsz]
  refine (bind_ok hrun).trans ?_
  rw [he]
  simp only [levelVal, he, List.getD_cons_zero, List.getD_cons_succ]
  exact hline

/-- The levels of a product tree, with every value named. -/
theorem chain_val (S : Lkp.Public) (hS : Sized S) (hR : S.readFrom = [keysMessage, planesMessage])
    (work : Nat) (keys : Bool) (levels more : Nat)
    (hord : ∀ l, l < levels → (orderAt S keys levels more l).length = more + l)
    (es' : List Fmt.Entry) :
    ∀ (n : Nat) (c : PointClaim) (s : Stand) (last : Option Fmt.Entry), n ≤ levels →
      ClaimOK S (more + (levels - n)) c → NoRows last →
      FitsAll s.rounds (chainEntries work more (levels - n) n ++ es') →
      s.taken + chainMasks more (levels - n) n ≤ Lkp.allMasks S →
      ∃ last', NoRows last' ∧ FitsAll (chainVal S keys levels more n c s).2.rounds es' ∧
        (chainVal S keys levels more n c s).2.taken = s.taken + chainMasks more (levels - n) n ∧
        ClaimOK S (more + levels) (chainVal S keys levels more n c s).1 ∧
        (Lkp.levelChain (envOf S) keys levels more n c)
          (s.ctx S (chainEntries work more (levels - n) n ++ es') last) =
          .ok ((chainVal S keys levels more n c s).1,
            (chainVal S keys levels more n c s).2.ctx S es' last')
  | 0, c, s, last, _, hc, hq, hfit, _ =>
    ⟨last, hq, hfit, rfl, by simpa using hc, rfl⟩
  | n + 1, c, s, last, hn, hc, hq, hfit, hk => by
    have hl : levels - (n + 1) < levels := by omega
    have ho := hord _ hl
    have hnext : levels - (n + 1) + 1 = levels - n := by omega
    have hlen : levels - (n + 1) + more =
        (orderAt S keys levels more (levels - (n + 1))).length := by
      rw [ho]; omega
    simp only [chainEntries, chainMasks, List.append_assoc, List.cons_append, hnext,
      hlen] at hfit hk ⊢
    obtain ⟨hf1, ht1, hc1, hrun1⟩ :=
      level_val S hS hR work (orderAt S keys levels more (levels - (n + 1)))
        (keys && levels - (n + 1) + 1 == levels) (chainEntries work more (levels - n) n ++ es') s
            last
        c (by rw [ho]; exact hc) hq hfit (by omega)
    obtain ⟨last', hq', hf', ht', hc', hrun'⟩ :=
      chain_val S hS hR work keys levels more hord es' n
        (levelVal (orderAt S keys levels more (levels - (n + 1))) c s).1
        (levelVal (orderAt S keys levels more (levels - (n + 1))) c s).2 _ (by omega)
        (by rw [ho] at hc1; rw [← hnext, ← Nat.add_assoc]; exact hc1) (noRows_rDraw "LINE" work 1)
            hf1
        (by rw [ht1]; omega)
    refine ⟨last', hq', hf', by rw [show (chainVal S keys levels more (n + 1) c s) =
      chainVal S keys levels more n
        (levelVal (orderAt S keys levels more (levels - (n + 1))) c s).1
        (levelVal (orderAt S keys levels more (levels - (n + 1))) c s).2 from rfl, ht', ht1]; omega,
      hc', ?_⟩
    show ((Blk.must
        ((orderAt S keys levels more (levels - (n + 1))).length == more + (levels - (n + 1)) &&
        c.point.length == more + (levels - (n + 1)))) >>= fun _ =>
      (Lkp.psc (envOf S) (levelSum c (orderAt S keys levels more (levels - (n + 1))))
          Lkp.summandProduct
        (keys && levels - (n + 1) + 1 == levels) []
        fun p => Lkp.byVariable p (orderAt S keys levels more (levels - (n + 1)))) >>= fun o =>
      match o.ends with
      | [e0, e1] => line e0 e1 >>= fun next => Lkp.levelChain (envOf S) keys levels more n next
      | _ => Blk.fail) _ = _
    rw [bind_ok (must_ok (by simp [ho, hc.1]) _)]
    refine (congrFun (level_assoc _ _) _).trans ?_
    refine (bind_ok hrun1).trans ?_
    exact hrun'

/-! ## The tie -/

/-- A sumcheck without a variable, with every value named. -/
theorem value_val (S : Lkp.Public) (hS : Sized S) (hR : S.readFrom = [keysMessage, planesMessage])
    (work : Nat) (cl : Psc.Claim) (hcl : cl.vars = []) (Sm : Psc.Summand) (hs : 0 < Sm.shown)
    (hdg : 0 < Sm.degree) (hk0 : Sm.kept = 0) (ha : ∀ p y, (Sm.coeffs p y).length = 1 + Sm.kept)
    (es' : List Fmt.Entry) (s : Stand) (last) (hq : NoRows last)
    (hfit : FitsAll s.rounds (pscEntries work
      { degree := [], withY := true, degreeY := Sm.degree, values := Sm.shown } ++ es'))
    (hk : s.taken + (1 + Sm.degree + Sm.shown) ≤ Lkp.allMasks S) (hm : SlotsOK S cl.masks) :
    ∃ last', NoRows last' ∧ FitsAll (s.afterPsc cl Sm [] id).rounds es' ∧
      (s.afterPsc cl Sm [] id).taken = s.taken + (1 + Sm.degree + Sm.shown) ∧
      (pscOut cl Sm id s.taken s.rounds).ends.length = Sm.shown ∧
      (∀ e ∈ (pscOut cl Sm id s.taken s.rounds).ends, ClaimOK S 0 e) ∧
      (Lkp.psc (envOf S) cl Sm)
          (s.ctx S (pscEntries work
            { degree := [], withY := true, degreeY := Sm.degree, values := Sm.shown } ++ es') last)
                =
        .ok (pscOut cl Sm id s.taken s.rounds, (s.afterPsc cl Sm [] id).ctx S es' last') := by
  have hne0 : Sm.shown ≠ 0 := Nat.pos_iff_ne_zero.1 hs
  have hdne : Sm.degree ≠ 0 := Nat.pos_iff_ne_zero.1 hdg
  have hsz : Psc.sizeOf cl Sm =
      { degree := [], withY := true, degreeY := Sm.degree, values := Sm.shown } := by
    simp [Psc.sizeOf, hcl, hs]
  have hvo : Psc.varsOf cl Sm = [Psc.Weight.atZero (Sm.degree + 1)] := by
    simp [Psc.varsOf, hcl, hne0]
  have hmk : Psc.masksOf cl Sm = 1 + Sm.degree + Sm.shown := by
    simp [Psc.masksOf, hvo, Psc.hidingEntries, Psc.Weight.atZero, Psc.Weight.equality]
  obtain ⟨o1, _, _, _, _, _, hrun1, hends, hall, _⟩ :=
    value_at S hS hR work cl hcl Sm hs hdg hk0 ha es' s.rounds last s.taken s.rows hq hfit hk hm
  obtain ⟨last', hf', hq', hrun, _, _, _, _⟩ :=
    psc_val S hS hR work cl Sm false [] id es' s.rounds last s.taken s.rows hq
        (by rw [hsz]; exact hfit)
      (by
        have b1 : (Sm.shown == 0) = false := by simp [hne0]
        have b2 : (Sm.degree == 0) = false := by simp [hdne]
        simp [Psc.formOK, hcl, hs, b1, b2]) ha
      (by rw [hvo]; intro x hx; simp at hx; subst hx; simp [Psc.Weight.atZero, Psc.Weight.equality])
      (by rw [hvo]; simp) (by simp [hcl]) (by rw [hmk]; exact hk) (by intro h; cases h) hm
      (by simp [hk0]) (by intro m hm'; simp at hm') (fun _ => rfl)
  have hrun2 : (Lkp.psc (envOf S) cl Sm)
      (s.ctx S (pscEntries work
        { degree := [], withY := true, degreeY := Sm.degree, values := Sm.shown } ++ es') last) =
      .ok (pscOut cl Sm id s.taken s.rounds, (s.afterPsc cl Sm [] id).ctx S es' last') := by
    rw [← hsz]
    exact hrun
  have hsame : o1 = pscOut cl Sm id s.taken s.rounds := by
    have h3 : (Lkp.psc (envOf S) cl Sm)
      (s.ctx S (pscEntries work
        { degree := [], withY := true, degreeY := Sm.degree, values := Sm.shown } ++ es') last) =
            _ := hrun1
    rw [hrun2] at h3
    exact (congrArg Prod.fst (Except.ok.inj h3)).symm
  subst hsame
  exact ⟨last', hq', hf', by simp [Stand.afterPsc, hmk], hends, hall, hrun2⟩

/-- A claim on a value as a sum without variables. -/
def valueSum (c : PointClaim) : Psc.Claim where
  vars := []
  masks := c.masks
  target := c.value

/-- The last n steps of the tie: the claims on the planes' roots and on the last power, and the
stand
after them. -/
def tieVal : Nat → PointClaim → Stand → List PointClaim × Stand
  | 0, c, s => ([c], s)
  | n + 1, c, s =>
    let o := pscOut (valueSum c) Lkp.summandTie id s.taken s.rounds
    let x := tieVal n (o.ends.getD 0 default) (s.afterPsc (valueSum c) Lkp.summandTie [] id)
    (o.ends.getD 1 default :: x.1, x.2)

/-- The later steps of the tie, with every value named. -/
theorem tie_val (S : Lkp.Public) (hS : Sized S) (hR : S.readFrom = [keysMessage, planesMessage])
    (work : Nat) (es' : List Fmt.Entry) :
    ∀ (n : Nat) (c : PointClaim) (s : Stand) (last : Option Fmt.Entry), ClaimOK S 0 c → NoRows last
        →
      FitsAll s.rounds (tieEntries work n ++ es') → s.taken + 6 * n ≤ Lkp.allMasks S →
      ∃ last', NoRows last' ∧ FitsAll (tieVal n c s).2.rounds es' ∧
        (tieVal n c s).2.taken = s.taken + 6 * n ∧ (∀ x ∈ (tieVal n c s).1, ClaimOK S 0 x) ∧
        (Lkp.tieSteps (envOf S) n c) (s.ctx S (tieEntries work n ++ es') last) =
          .ok ((tieVal n c s).1, (tieVal n c s).2.ctx S es' last')
  | 0, c, s, last, hc, hq, hfit, _ =>
    ⟨last, hq, hfit, rfl, by intro x hx; simp [tieVal] at hx; subst hx; exact hc, rfl⟩
  | n + 1, c, s, last, hc, hq, hfit, hk => by
    simp only [tieEntries, List.append_assoc] at hfit ⊢
    obtain ⟨last1, hq1, hf1, ht1, hends, hall, hrun1⟩ :=
      value_val S hS hR work (valueSum c) rfl Lkp.summandTie (by decide) (by decide) rfl
          (fun _ _ => rfl)
        (tieEntries work n ++ es') s last hq hfit (by show s.taken + (1 + 3 + 2) ≤ _; omega) hc.2
    obtain ⟨power, plane, he⟩ : ∃ a b,
        (pscOut (valueSum c) Lkp.summandTie id s.taken s.rounds).ends = [a, b] := by
      have h2 : (pscOut (valueSum c) Lkp.summandTie id s.taken s.rounds).ends.length = 2 := hends
      match (pscOut (valueSum c) Lkp.summandTie id s.taken s.rounds).ends, h2 with
      | [a, b], _ => exact ⟨a, b, rfl⟩
    have ht1' : (s.afterPsc (valueSum c) Lkp.summandTie [] id).taken = s.taken + 6 := ht1
    obtain ⟨last', hq', hf', ht', hl, hrun'⟩ :=
      tie_val S hS hR work es' n power (s.afterPsc (valueSum c) Lkp.summandTie [] id) last1
        (hall power (by simp [he])) hq1 hf1 (by rw [ht1']; omega)
    have hv : tieVal (n + 1) c s =
        (plane :: (tieVal n power (s.afterPsc (valueSum c) Lkp.summandTie [] id)).1,
          (tieVal n power (s.afterPsc (valueSum c) Lkp.summandTie [] id)).2) := by
      simp [tieVal, he]
    rw [hv]
    refine ⟨last', hq', hf', by rw [ht', ht1']; omega, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hall _ (by simp [he])
      · exact hl x hx
    · show ((Lkp.onValue c) >>= fun cl => (Lkp.psc (envOf S) cl Lkp.summandTie) >>= fun o =>
        match o.ends with
        | [power, plane] => (Lkp.tieSteps (envOf S) n power) >>= fun rest => pure (plane :: rest)
        | _ => Blk.fail) _ = _
      rw [bind_ok (onValue_at S c hc _)]
      refine (bind_ok hrun1).trans ?_
      rw [he]
      show ((Lkp.tieSteps (envOf S) n power) >>= fun rest => pure (plane :: rest)) _ = _
      refine (bind_ok hrun').trans ?_
      rfl

/-! ## The whole lookup -/

/-- All that is drawn in the next round. -/
def Stand.draws (s : Stand) : List E := (s.rounds.headD default).drawn

/-- A round in which one element is drawn and nothing is sent, with the value named. -/
theorem drawOne_val (S : Lkp.Public) (work : Nat) (name : String) (es' : List Fmt.Entry) (s : Stand)
    (last) (hq : NoRows last) (hfit : FitsAll s.rounds ((rDraw name work 1).entry :: es')) :
    FitsAll s.next.rounds es' ∧
      (Lkp.drawOne name) (s.ctx S ((rDraw name work 1).entry :: es') last) =
        .ok (s.draw, s.next.ctx S es' (some (rDraw name work 1).entry)) := by
  obtain ⟨rounds, taken, rows⟩ := s
  cases rounds with
  | nil => simp [FitsAll] at hfit
  | cons r rs =>
    obtain ⟨hr, hrest⟩ := hfit
    have hm : Meets r (rDraw name work 1).entry name 0 1 0 := meets_of_fits hr rfl rfl rfl rfl rfl
        rfl rfl
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.1 hm.drawn
    refine ⟨hrest, ?_⟩
    unfold Lkp.drawOne Stand.ctx
    rw [show rvs (r :: rs) = r.rv :: rvs rs from rfl,
      bind_ok (hearDraw_at S _ es' (rvs rs) last taken rows r name 1 hm hq), hx]
    simp [Stand.draw, Stand.next, hx]
    rfl

/-- A round in which n elements are drawn and nothing is sent, with the values named. -/
theorem draws_val (S : Lkp.Public) (work n : Nat) (name : String) (es' : List Fmt.Entry) (s : Stand)
    (last) (hq : NoRows last) (hfit : FitsAll s.rounds ((rDraw name work n).entry :: es')) :
    FitsAll s.next.rounds es' ∧ s.draws.length = n ∧
      (hearDraw name n) (s.ctx S ((rDraw name work n).entry :: es') last) =
        .ok (s.draws, s.next.ctx S es' (some (rDraw name work n).entry)) := by
  obtain ⟨rounds, taken, rows⟩ := s
  cases rounds with
  | nil => simp [FitsAll] at hfit
  | cons r rs =>
    obtain ⟨hr, hrest⟩ := hfit
    have hm : Meets r (rDraw name work n).entry name 0 n 0 := meets_of_fits hr rfl rfl rfl rfl rfl
        rfl rfl
    exact ⟨hrest, hm.drawn, hearDraw_at S _ es' (rvs rs) last taken rows r name n hm hq⟩

/-- Where the bits are read: the map that the least caller gives to the lookup. -/
def bitsAt (S : Lkp.Public) : MapAt := fun row point coeff => (envOf S).planesAt row
    (Tensor.eq point coeff)

/-- The row that says that the counts sum to the number of keys that are not padding. -/
def countsRow (S : Lkp.Public) : Row :=
  (envOf S).planesAt { target := Lkp.natE (S.allKeys - Lkp.paddingCount S) }
    { pairs := ((List.range S.mu).map fun t => (oneE, Lkp.natE (2 ^ 2 ^ t))) ++
        List.replicate S.d (oneE, oneE) }

/-- The stands and values of a whole lookup with one part of 2 ^ v keys and without a shift, each
under
its name, in the order of the run. -/
structure Course where
  /-- the challenge alpha -/
  alpha : E
  /-- what the tie's first step hands on -/
  first : Psc.Out
  /-- the tie's later steps -/
  tie : List PointClaim × Stand
  /-- the point at which the planes are joined -/
  join : List E
  /-- the key tree: the claim on its leaves -/
  keys : PointClaim × Stand
  /-- the table's tree: the claim on its leaves -/
  table : PointClaim × Stand
  /-- the stand after the sumcheck on the leaves -/
  afterLeaves : Stand
  /-- the point of the test that the bits are bits -/
  zeta : List E
  /-- what the sumcheck on the bits hands on -/
  bits : Psc.Out
  /-- the stand at the end -/
  last : Stand

/-- The sum without variables and with target 0 with which the tie begins. -/
def zeroSum : Psc.Claim where
  vars := []
  masks := []
  target := zeroE

/-- The course of a whole lookup from a stand. -/
def courseOf (S : Lkp.Public) (v : Nat) (s : Stand) : Course :=
  let alpha := s.draw
  let tieFirst := Lkp.summandTieFirst (Lkp.factorOf S zeroE alpha)
  let first := pscOut zeroSum tieFirst id s.next.taken s.next.rounds
  let tie := tieVal (S.planes - 2) (first.ends.getD 1 default)
      (s.next.afterPsc zeroSum tieFirst [] id)
  let join := tie.2.draws
  let keys := chainVal S true v 0 v (first.ends.getD 0 default) tie.2.next
  let table := chainVal S false S.d S.mu S.d
    (Lkp.joinPlanes S join (first.ends.getD 2 default :: tie.1)) keys.2
  let order := Lkp.defaultOrder (S.mu + S.d)
  let place := fun p => Lkp.byVariable p order
  let afterLeaves := table.2.afterPsc (leavesSum S table.1) (Lkp.summandLeaves S zeroE alpha order)
    [bitsAt S] place
  let zeta := afterLeaves.draws
  let bitsSum := levelSum ⟨zeta, [], zeroE⟩ order
  let bits := pscOut bitsSum Lkp.summandBits place afterLeaves.next.taken afterLeaves.next.rounds
  let s9 := afterLeaves.next.afterPsc bitsSum Lkp.summandBits [] place
  { alpha := alpha, first := first, tie := tie, join := join, keys := keys, table := table
    afterLeaves := afterLeaves, zeta := zeta, bits := bits
    last := { s9 with
      rows := (s9.rows.push (pointRow (bits.ends.getD 0 default) (bitsAt S))).push (countsRow S) } }

/-- What a whole lookup returns. -/
def Course.out (x : Course) (S : Lkp.Public) : Lkp.Out where
  theta := zeroE
  alpha := x.alpha
  keys := [Lkp.keysOf S zeroE x.alpha 0 x.keys.1]

/-- A whole lookup, with every value named. -/
theorem run_val (S : Lkp.Public) (work v : Nat) (h : Shaped S work v) (s : Stand) (h0 : s.taken = 0)
    (hfit : FitsAll s.rounds (blockEntries S work v)) :
    ∃ last, NoRows last ∧ ClaimOK S v (courseOf S v s).keys.1 ∧ (courseOf S v s).last.rounds = [] ∧
      (Lkp.run (envOf S)) (s.ctx S (blockEntries S work v) none) =
        .ok ((courseOf S v s).out S, (courseOf S v s).last.ctx S [] last) := by
  have hS := h.sized
  have hR := h.reads
  have hM := h.masks
  unfold blockEntries at hfit ⊢
  generalize hx : courseOf S v s = x
  have hx' := hx.symm
  simp only [courseOf] at hx'
  obtain ⟨hf1, hrun1⟩ := drawOne_val S work "LKP" _ s none (by intro e he; cases he) hfit
  obtain ⟨last2, hq2, hf2, ht2, hends2, hall2, hrun2⟩ :=
    value_val S hS hR work zeroSum rfl (Lkp.summandTieFirst (Lkp.factorOf S zeroE s.draw))
      (by show 0 < 3; omega) (by show 0 < 3; omega) rfl (fun _ _ => rfl) _ s.next _
      (noRows_rDraw "LKP" work 1) hf1 (by show s.taken + (1 + 3 + 3) ≤ _; omega)
      (by intro p hp; simp [zeroSum] at hp)
  have ht2' : (s.next.afterPsc zeroSum (Lkp.summandTieFirst (Lkp.factorOf S zeroE s.draw)) []
      id).taken =
      7 := by
    rw [ht2]
    show s.taken + (1 + 3 + 3) = 7
    omega
  obtain ⟨a, b, c, he⟩ : ∃ a b c,
      (pscOut zeroSum (Lkp.summandTieFirst (Lkp.factorOf S zeroE s.draw)) id
      s.next.taken s.next.rounds).ends = [a, b, c] := by
    have h3 : (pscOut zeroSum (Lkp.summandTieFirst (Lkp.factorOf S zeroE s.draw)) id
      s.next.taken s.next.rounds).ends.length = 3 := hends2
    match (pscOut zeroSum (Lkp.summandTieFirst (Lkp.factorOf S zeroE s.draw)) id
      s.next.taken s.next.rounds).ends, h3 with
    | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
  simp only [he, List.getD_cons_zero, List.getD_cons_succ] at hx'
  obtain ⟨last3, hq3, hf3, ht3, hl3, hrun3⟩ :=
    tie_val S hS hR work _ (S.planes - 2) b _ last2 (hall2 b (by simp [he])) hq2 hf2
        (by rw [ht2']; omega)
  generalize htie : tieVal (S.planes - 2) b
    (s.next.afterPsc zeroSum (Lkp.summandTieFirst (Lkp.factorOf S zeroE s.draw)) [] id) = tie
    at hf3 ht3 hl3 hrun3 hx'
  obtain ⟨hf4, hr4, hrun4⟩ := draws_val S work S.mu "JOIN" _ tie.2 last3 hq3 hf3
  have hTop : ClaimOK S (S.mu + (S.d - S.d)) (Lkp.joinPlanes S tie.2.draws (c :: tie.1)) := by
    have := joinPlanes_ok S tie.2.draws (c :: tie.1) (by
      intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact hall2 _ (by simp [he])
      · exact hl3 q hq)
    rw [hr4] at this
    simpa using this
  have ht4 : tie.2.next.taken = 7 + 6 * (S.planes - 2) := by
    show tie.2.taken = _
    rw [ht3, ht2']
  obtain ⟨last5, hq5, hf5, ht5, hc5, hrun5⟩ :=
    chain_val S hS hR work true v 0 (orderAt_keys S v h.lastOrder) _ v a tie.2.next _
        (Nat.le_refl v)
      (by have := hall2 a (by simp [he]); simpa using this) (noRows_rDraw "JOIN" work S.mu) hf4
      (by rw [ht4]; omega)
  generalize hkeys : chainVal S true v 0 v a tie.2.next = keys at hf5 ht5 hc5 hrun5 hx'
  obtain ⟨last6, hq6, hf6, ht6, hc6, hrun6⟩ :=
    chain_val S hS hR work false S.d S.mu (orderAt_table S S.d S.mu) _ S.d
      (Lkp.joinPlanes S tie.2.draws (c :: tie.1)) keys.2 last5 (Nat.le_refl _) hTop hq5 hf5
      (by rw [ht5, ht4]; omega)
  generalize htable : chainVal S false S.d S.mu S.d (Lkp.joinPlanes S tie.2.draws (c :: tie.1))
      keys.2 =
    table at hf6 ht6 hc6 hrun6 hx'
  -- the leaves
  have hLd := (leavesSum_d S table.1).trans h.leaves
  have hLlen : (leavesSum S table.1).vars.length = S.mu + S.d := by
    simp [leavesSum, defaultOrder_length]
  have hLsz : Psc.sizeOf (leavesSum S table.1)
      (Lkp.summandLeaves S zeroE s.draw (Lkp.defaultOrder (S.mu + S.d))) = leavesSize S := by
    simp only [Psc.sizeOf, hLd, leavesSize, Lkp.summandLeaves]
    rfl
  have hLvo : Psc.varsOf (leavesSum S table.1)
      (Lkp.summandLeaves S zeroE s.draw (Lkp.defaultOrder (S.mu + S.d))) =
          (leavesSum S table.1).vars := rfl
  have hLmk : Psc.masksOf (leavesSum S table.1)
      (Lkp.summandLeaves S zeroE s.draw (Lkp.defaultOrder (S.mu + S.d))) = 1 + S.mu + 2 * S.d := by
    have e1 : (leavesSum S table.1).vars.map (fun w => w.d - 1) =
        (List.replicate S.d 3 ++ List.replicate S.mu 2).map (· - 1) := by
      rw [← hLd, List.map_map]
      rfl
    have e2 : Psc.masksOf (leavesSum S table.1)
        (Lkp.summandLeaves S zeroE s.draw (Lkp.defaultOrder (S.mu + S.d))) =
        1 + ((leavesSum S table.1).vars.map (fun w => w.d - 1)).sum + 0 := rfl
    rw [e2, e1, sum_leaves]
    omega
  have hLw : ∀ w ∈ (leavesSum S table.1).vars, w.fits = true ∧ 1 ≤ w.d := by
    intro w hw
    simp only [leavesSum, List.mem_map] at hw
    obtain ⟨t, _, rfl⟩ := hw
    by_cases ht : t < S.mu <;> simp [Psc.Weight.fits, Psc.Weight.equality, ht]
  have hLne : (leavesSum S table.1).vars ≠ [] := by
    intro hz
    have h1 := congrArg List.length hz
    rw [hLlen] at h1
    have h2 := h.some
    simp at h1
    omega
  obtain ⟨last7, hf7, hq7, hrun7, _, _, _, _⟩ :=
    psc_val S hS hR work (leavesSum S table.1)
      (Lkp.summandLeaves S zeroE s.draw (Lkp.defaultOrder (S.mu + S.d))) false [bitsAt S]
      (fun p => Lkp.byVariable p (Lkp.defaultOrder (S.mu + S.d))) _ table.2.rounds last6
          table.2.taken
      table.2.rows hq6 (by rw [hLsz]; exact hf6)
      (by
        have ha : (leavesSum S table.1).vars.all Psc.Weight.fits = true :=
          List.all_eq_true.2 fun w hw => (hLw w hw).1
        have hb : (leavesSum S table.1).vars.isEmpty = false := by
          cases hv : (leavesSum S table.1).vars with
          | nil => exact absurd hv hLne
          | cons _ _ => rfl
        simp [Psc.formOK, Lkp.summandLeaves, ha, hb])
      (fun _ _ => rfl) (by rw [hLvo]; exact fun w hw => (hLw w hw).2) (by rw [hLvo]; exact hLne)
      (by rw [hLvo]; exact Nat.le_refl _) (by rw [hLmk, ht6, ht5, ht4]; omega)
          (by intro hh; cases hh)
      hc6.2 rfl (by rw [hLlen]; exact mapsOK_bits S hS) (fun p => byVariable_length p _)
  have hrun7' : (Lkp.psc (envOf S) (leavesSum S table.1)
      (Lkp.summandLeaves S zeroE s.draw (Lkp.defaultOrder (S.mu + S.d))) false [bitsAt S]
      fun p => Lkp.byVariable p (Lkp.defaultOrder (S.mu + S.d)))
      (table.2.ctx S (pscEntries work (leavesSize S) ++ (rDraw "ZERO" work (S.mu + S.d)).entry ::
        (pscEntries work (bitsSize S) ++ [])) last6) =
      .ok (pscOut (leavesSum S table.1)
          (Lkp.summandLeaves S zeroE s.draw (Lkp.defaultOrder (S.mu + S.d)))
          (fun p => Lkp.byVariable p (Lkp.defaultOrder (S.mu + S.d))) table.2.taken table.2.rounds,
        (table.2.afterPsc (leavesSum S table.1)
          (Lkp.summandLeaves S zeroE s.draw (Lkp.defaultOrder (S.mu + S.d))) [bitsAt S]
          fun p => Lkp.byVariable p (Lkp.defaultOrder (S.mu + S.d))).ctx S
          ((rDraw "ZERO" work (S.mu + S.d)).entry :: (pscEntries work (bitsSize S) ++ []))
              last7) := by
    rw [← hLsz]
    exact hrun7
  have ht7 : (table.2.afterPsc (leavesSum S table.1)
      (Lkp.summandLeaves S zeroE s.draw (Lkp.defaultOrder (S.mu + S.d))) [bitsAt S]
      fun p => Lkp.byVariable p (Lkp.defaultOrder (S.mu + S.d))).taken =
      table.2.taken + (1 + S.mu + 2 * S.d) := by
    show table.2.taken + Psc.masksOf _ _ = _
    rw [hLmk]
  generalize hs7 : table.2.afterPsc (leavesSum S table.1)
      (Lkp.summandLeaves S zeroE s.draw (Lkp.defaultOrder (S.mu + S.d))) [bitsAt S]
      (fun p => Lkp.byVariable p (Lkp.defaultOrder (S.mu + S.d))) = s7 at ht7 hx' hrun7'
  have hf7' : FitsAll s7.rounds ((rDraw "ZERO" work (S.mu + S.d)).entry ::
      (pscEntries work (bitsSize S) ++ [])) := by
    rw [← hs7]
    exact hf7
  -- ZERO
  obtain ⟨hf8, hz8, hrun8⟩ := draws_val S work (S.mu + S.d) "ZERO" _ s7 last7 hq7 hf7'
  -- the bits
  have hOl := defaultOrder_length (S.mu + S.d)
  have hBsz : Psc.sizeOf (levelSum ⟨s7.draws, [], zeroE⟩ (Lkp.defaultOrder (S.mu + S.d)))
      Lkp.summandBits =
      bitsSize S := by
    simp [Psc.sizeOf, levelSum, Lkp.summandBits, bitsSize, Psc.Weight.equality, List.map_map,
      Function.comp_def, List.map_const', hOl]
  have hBmk : Psc.masksOf (levelSum ⟨s7.draws, [], zeroE⟩ (Lkp.defaultOrder (S.mu + S.d)))
      Lkp.summandBits = 1 + 2 * (S.mu + S.d) + 2 + 1 := by
    simp [Psc.masksOf, Psc.varsOf, Psc.hidingEntries, levelSum, Lkp.summandBits,
      Psc.Weight.equality, Psc.Weight.atZero, List.map_map, Function.comp_def, List.map_const', hOl]
    omega
  have hBlen : (levelSum ⟨s7.draws, [], zeroE⟩ (Lkp.defaultOrder (S.mu + S.d))).vars.length =
      S.mu + S.d := by
    simp [levelSum, hOl]
  obtain ⟨last9, hf9, hq9, hrun9, hpt9, hends9, hall9, _⟩ :=
    psc_val S hS hR work (levelSum ⟨s7.draws, [], zeroE⟩ (Lkp.defaultOrder (S.mu + S.d)))
        Lkp.summandBits
      false [] (fun p => Lkp.byVariable p (Lkp.defaultOrder (S.mu + S.d))) [] s7.next.rounds _
      s7.next.taken s7.next.rows (noRows_rDraw "ZERO" work (S.mu + S.d))
      (by rw [hBsz]; exact hf8)
      (by simp [Psc.formOK, Lkp.summandBits, levelSum, Psc.Weight.fits, Psc.Weight.equality])
      (fun _ _ => rfl)
      (by
        intro x hx
        simp only [Psc.varsOf, Lkp.summandBits, levelSum] at hx
        simp at hx
        rcases hx with ⟨t, _, rfl⟩ | rfl <;> simp [Psc.Weight.equality, Psc.Weight.atZero])
      (by simp [Psc.varsOf, Lkp.summandBits]) (by simp [Psc.varsOf, Lkp.summandBits])
      (by
        rw [hBmk]
        show s7.taken + _ ≤ _
        rw [ht7, ht6, ht5, ht4]
        omega)
      (by intro hh; cases hh) (by intro p hp; simp [levelSum] at hp) rfl
      (by intro m hm; simp at hm) (fun p => byVariable_length p _)
  have hrun9' : (Lkp.psc (envOf S) (levelSum ⟨s7.draws, [], zeroE⟩ (Lkp.defaultOrder (S.mu + S.d)))
      Lkp.summandBits false [] fun p => Lkp.byVariable p (Lkp.defaultOrder (S.mu + S.d)))
      (s7.next.ctx S (pscEntries work (bitsSize S) ++ [])
          (some (rDraw "ZERO" work (S.mu + S.d)).entry)) =
      .ok (pscOut (levelSum ⟨s7.draws, [], zeroE⟩ (Lkp.defaultOrder (S.mu + S.d))) Lkp.summandBits
          (fun p => Lkp.byVariable p (Lkp.defaultOrder (S.mu + S.d))) s7.next.taken s7.next.rounds,
        (s7.next.afterPsc (levelSum ⟨s7.draws, [], zeroE⟩ (Lkp.defaultOrder (S.mu + S.d)))
          Lkp.summandBits [] fun p => Lkp.byVariable p (Lkp.defaultOrder (S.mu + S.d))).ctx S []
              last9) := by
    rw [← hBsz]
    exact hrun9
  obtain ⟨e9, he9⟩ : ∃ a, (pscOut (levelSum ⟨s7.draws, [], zeroE⟩ (Lkp.defaultOrder (S.mu + S.d)))
      Lkp.summandBits (fun p => Lkp.byVariable p (Lkp.defaultOrder (S.mu + S.d))) s7.next.taken
      s7.next.rounds).ends = [a] := by
    have h1 : (pscOut (levelSum ⟨s7.draws, [], zeroE⟩ (Lkp.defaultOrder (S.mu + S.d)))
      Lkp.summandBits (fun p => Lkp.byVariable p (Lkp.defaultOrder (S.mu + S.d))) s7.next.taken
      s7.next.rounds).ends.length = 1 := hends9
    match (pscOut (levelSum ⟨s7.draws, [], zeroE⟩ (Lkp.defaultOrder (S.mu + S.d)))
      Lkp.summandBits (fun p => Lkp.byVariable p (Lkp.defaultOrder (S.mu + S.d))) s7.next.taken
      s7.next.rounds).ends, h1 with
    | [a], _ => exact ⟨a, rfl⟩
  have h9 := hall9 e9 (by simp [he9])
  simp only [he9, List.getD_cons_zero] at hx'
  have hrowA : Fine S (pointRow e9 (bitsAt S)) := by
    unfold pointRow
    apply fine_addMasks S _ _ _ h9.2
    exact mapsOK_bits S hS (bitsAt S) (List.mem_singleton.2 rfl) { target := e9.value } e9.point
        oneE
      (fine_target S _) (by rw [h9.1, hpt9, hBlen])
  have hrowB : Fine S (countsRow S) := by
    apply fine_planes S _ (fine_target S _)
    · simp [Tensor.vars]
    · have := hS.small
      simp [Tensor.ok, Tensor.vars, distinctNats, this]
  have hend : restOf (Psc.sizeOf (levelSum ⟨s7.draws, [], zeroE⟩ (Lkp.defaultOrder (S.mu + S.d)))
      Lkp.summandBits) s7.next.rounds = [] := by
    cases hr : restOf (Psc.sizeOf (levelSum ⟨s7.draws, [], zeroE⟩ (Lkp.defaultOrder (S.mu + S.d)))
      Lkp.summandBits) s7.next.rounds with
    | nil => rfl
    | cons _ _ => rw [hr] at hf9; simp [FitsAll] at hf9
  subst hx'
  refine ⟨last9, hq9, by simpa using hc5, hend, ?_⟩
  unfold Lkp.run
  simp only [show (envOf S).S = S from rfl, h.noShift, Bool.false_eq_true, if_false]
  rw [bind_ok (pure_ok _ _)]
  refine (bind_ok hrun1).trans ?_
  refine (bind_ok (note_at _ _ _ _ _ _ _ _ _)).trans ?_
  refine (bind_ok (note_at _ _ _ _ _ _ _ _ _)).trans ?_
  refine (bind_ok hrun2).trans ?_
  rw [he]
  simp only []
  rw [bind_ok (pure_ok _ _)]
  refine (bind_ok hrun3).trans ?_
  rw [h.parts]
  refine (bind_ok
      (show (Lkp.partSteps (envOf S) ([v].length - 1) a) _ = .ok ([a], _) from rfl)).trans ?_
  refine (bind_ok hrun4).trans ?_
  refine (bind_ok (note_at _ _ _ _ _ _ _ _ _)).trans ?_
  have hkt : (Lkp.keyTrees (envOf S) [v] [a]) (tie.2.next.ctx S
      (chainEntries work 0 (v - v) v ++ (chainEntries work S.mu (S.d - S.d) S.d ++
        (pscEntries work (leavesSize S) ++ (rDraw "ZERO" work (S.mu + S.d)).entry ::
          (pscEntries work (bitsSize S) ++ [])))) (some (rDraw "JOIN" work S.mu).entry)) =
      .ok ([keys.1], keys.2.ctx S
      (chainEntries work S.mu (S.d - S.d) S.d ++
        (pscEntries work (leavesSize S) ++ (rDraw "ZERO" work (S.mu + S.d)).entry ::
          (pscEntries work (bitsSize S) ++ []))) last5) := by
    show ((Lkp.levelChain (envOf S) true v 0 v a) >>= fun y =>
      (Lkp.keyTrees (envOf S) [] []) >>= fun rest => pure (y :: rest)) _ = _
    rw [bind_ok hrun5]
    rfl
  refine (bind_ok hkt).trans ?_
  refine (bind_ok hrun6).trans ?_
  refine (bind_ok hrun7').trans ?_
  refine (bind_ok (note_at _ _ _ _ _ _ _ _ _)).trans ?_
  refine (bind_ok hrun8).trans ?_
  refine (bind_ok hrun9').trans ?_
  rw [he9]
  refine (bind_ok (get_ok e9 _)).trans ?_
  refine (bind_ok (leave_at S hS hR _ _ _ _ _ _ hrowA)).trans ?_
  refine (bind_ok (leave_at S hS hR _ _ _ _ _ _ hrowB)).trans ?_
  refine (bind_ok (must_ok (by simp) _)).trans ?_
  refine (bind_ok (noteKeys_at _ rfl _)).trans ?_
  rfl

/-! ## What a row holds, list by list -/

/-- A mask form as single entries. -/
def singlesOf (m : MaskForm) : List Single := m.map fun p => ⟨p.1.oracle, .mask, p.1.index, p.2⟩

/-- Adding a mask form to a row adds its single entries, in their order, and turns nothing else. -/
theorem addMasks_eq : ∀ (m : MaskForm) (r : Row),
    r.addMasks m = { r with units := r.units ++ (singlesOf m).toArray }
  | [], r => by simp [Row.addMasks, singlesOf]
  | p :: m, r => by
    have ih := addMasks_eq m (r.addUnit p.1.oracle .mask p.1.index p.2)
    show (r.addUnit p.1.oracle .mask p.1.index p.2).addMasks m = _
    rw [ih]
    simp [Row.addUnit, singlesOf]

/-- The row of a sumcheck without a kept map: its target, and its mask form as single entries. It
has
no structured vector, no run and no form. -/
theorem pscRow_nil (c : Psc.Claim) (Sm : Psc.Summand) (place : List E → List E) (k : Nat)
    (rs : List FlatRound) (h : (pscOut c Sm place k rs).rowMaps = []) :
    pscRow c Sm [] place k rs =
      { target := (pscOut c Sm place k rs).rowTarget
        units := (singlesOf (pscOut c Sm place k rs).rowMasks).toArray } := by
  simp [pscRow, Psc.rowU, h, addMasks_eq]

/-- The row of a sumcheck whose one kept map is the bits at the point: its target, its mask form as
single entries, and one structured vector on the bits. It has no run and no form. -/
theorem pscRow_bits (S : Lkp.Public) (c : Psc.Claim) (Sm : Psc.Summand) (place : List E → List E)
    (k : Nat) (rs : List FlatRound) (x : E) (h : (pscOut c Sm place k rs).rowMaps = [x]) :
    pscRow c Sm [bitsAt S] place k rs =
      { target := (pscOut c Sm place k rs).rowTarget
        units := (singlesOf (pscOut c Sm place k rs).rowMasks).toArray
        terms := #[⟨planesMessage, .main, Tensor.eq (pscOut c Sm place k rs).point x⟩] } := by
  simp [pscRow, Psc.rowU, h, addMasks_eq, bitsAt, envOf, Row.add]

/-- The row on the bits at the last sumcheck's point, list by list. -/
theorem pointRow_bits (S : Lkp.Public) (c : PointClaim) :
    pointRow c (bitsAt S) =
      { target := c.value
        units := (singlesOf c.masks).toArray
        terms := #[⟨planesMessage, .main, Tensor.eq c.point oneE⟩] } := by
  simp [pointRow, addMasks_eq, bitsAt, envOf, Row.add]

/-- The caller's row on the keys, list by list. -/
theorem keysRow_eq (k : Lkp.Keys) :
    keysRow k =
      { target := k.target
        units := (singlesOf k.masks).toArray
        forms := #[⟨keysMessage, k.weights⟩] } := by
  simp [keysRow, addMasks_eq, Row.addForm]

/-! ## The caller's block, the run on plain data, and the end claims -/

/-- The course of the lookup on plain data. -/
def Flat.course (t : Flat) (S : Lkp.Public) (v : Nat) : Course := courseOf S v ⟨t.rounds, 0, #[]⟩

/-- All rows that the caller's block adds to the group on plain data: the lookup's, in their order,
then
the caller's row on the keys. -/
def Flat.rowsOf (t : Flat) (S : Lkp.Public) (v : Nat) : Array Row :=
  (t.course S v).last.rows.push
      (keysRow (Lkp.keysOf S zeroE (t.course S v).alpha 0 (t.course S v).keys.1))

/-- THE RUN AS A FUNCTION. On plain data that fit, the program's run at the least caller gives what
the
course says: a function of the rounds made of Psc.run, lineAt, Lkp.joinPlanes, Lkp.keysOf and the
rows'
own makers, without a state and without a failure. -/
theorem portOn_eq (S : Lkp.Public) (v : Nat) (h : Shaped S 0 v) (hP : PaddingOut S v)
    (hcodes : (statement S).codes.lengthsOk = true) (t : Flat) (ht : t.fits S = true) :
    portOn S t = .ok ((t.course S v).out S, t.rowsOf S v) := by
  have ht' := ht
  simp only [Flat.fits, Bool.and_eq_true, beq_iff_eq] at ht'
  have hfit : FitsAll t.rounds (blockEntries S 0 v) := by
    rw [← h.entries]
    exact fitsAll_of_fits _ _ ht'.1.1 ht'.1.2
  obtain ⟨last, hq, hc, hend, hrun⟩ := run_val S 0 v h ⟨t.rounds, 0, #[]⟩ rfl hfit
  have hfb : S.firstBits = v := by simp [Lkp.Public.firstBits, h.parts]
  have hrow : Fine S (keysRow (Lkp.keysOf S zeroE (t.course S v).alpha 0 (t.course S v).keys.1)) :=
    fine_keysRow S zeroE _ _ (by rw [hfb]; exact hc) (by rw [hfb]; exact h.keys63) (hP _ _ hc)
  have hver : (Lkp.verify S (fun row v => row.add planesMessage .main v) masksMessage theGroup)
      (ctxAt S (blockEntries S 0 v) none (rvs t.rounds) none 0 #[]) =
      .ok ((t.course S v).out S, (t.course S v).last.ctx S [] last) := by
    unfold Lkp.verify
    rw [h.reads]
    refine (bind_ok (show (Lkp.mustBeSampled [masksMessage]) _ = .ok ((), _) from rfl)).trans ?_
    refine (bind_ok (must_ok h.ok _)).trans ?_
    refine (bind_ok
        (show (Lkp.mustBeSampled [keysMessage, planesMessage]) _ = .ok ((), _) from rfl)).trans ?_
    exact hrun
  have hb : (block S) (ctxAt S (blockEntries S 0 v) none (rvs t.rounds) none 0 #[]) =
      .ok (((t.course S v).out S, t.rowsOf S v),
        ctxAt S [] none [] last (t.course S v).last.taken (t.rowsOf S v)) := by
    unfold block
    rw [bind_ok hver]
    have hctx : (t.course S v).last.ctx S [] last =
        ctxAt S [] none [] last (t.course S v).last.taken (t.course S v).last.rows := by
      unfold Stand.ctx
      rw [show (t.course S v).last.rounds = [] from hend]
      rfl
    rw [hctx]
    show (((Blk.addRow theGroup
      (keysRow (Lkp.keysOf S zeroE (t.course S v).alpha 0 (t.course S v).keys.1))) >>= fun _ =>
        pure PUnit.unit) >>= _) _ = _
    rw [bind_ok (bind_ok (addRow_at S h.sized [] [] last _ _ _ hrow))]
    rfl
  have hs := settled_of_noRows (S := S) (es := []) (cur := none) (rs := [])
    (k := (t.course S v).last.taken) (rows := t.rowsOf S v) hq
  have hn : (block S).runNamed (start S 0) false t.view.rounds t.view.opened =
      .ok (((t.course S v).out S, t.rowsOf S v),
        ctxAt S [] none [] last (t.course S v).last.taken (t.rowsOf S v)) := by
    unfold Blk.runNamed
    rw [if_pos (show (start S 0).st.codes.lengthsOk = true from hcodes)]
    rw [← hb, ← h.entries]
    rfl
  unfold portOn Blk.runOn
  rw [hn]
  simp [ctxAt, hs] at hs ⊢

/-- THE END CLAIMS AS A FUNCTION. On plain data that fit, the end claims are the rows of the course,
each
read coefficient by coefficient. -/
theorem endClaims_eq (S : Lkp.Public) (v : Nat) (h : Shaped S 0 v) (hP : PaddingOut S v)
    (hcodes : (statement S).codes.lengthsOk = true) (hs : served S = true) (t : Flat)
    (ht : t.fits S = true) :
    endClaims S t = some ((t.rowsOf S v).toList.map (ofRow S)) := by
  obtain ⟨out, rows, hrun, new, hrows, _, hfine⟩ := portOn_ok S v h hP hcodes t ht
  have heq := portOn_eq S v h hP hcodes t ht
  have hsame : rows = t.rowsOf S v := by
    rw [heq] at hrun
    exact (congrArg Prod.snd (Except.ok.inj hrun)).symm
  have hall : (t.rowsOf S v).all (onCaller S) = true := by
    rw [Array.all_eq_true_iff_forall_mem]
    intro r hr
    rw [← hsame, hrows] at hr
    exact onCaller_of_fine S r (hfine r (by simpa using hr))
  unfold endClaims
  rw [if_pos (by simp [hs, ht]), heq]
  simp [hall]

end OnBytes.G4

#print axioms OnBytes.G4.portOn_eq
#print axioms OnBytes.G4.endClaims_eq
