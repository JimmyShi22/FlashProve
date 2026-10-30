-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/HeadAtRecord.lean: the letters of the row claim_read_same_index at the output
head's link, filled from the first chain's carried record; and the statement at the head at these
letters, from public premises and from what a record holds.

What is stated.
  `Fill`: what is public in the filling: the head's shape, layout, border and plan; the number of
    the reads' array and the number of its columns; the table of the tables; the bits of work.
  `Fill.reqOf`: the relation's own request, read off the record's words, the heard reply and the
    plan's policy.
  `Fill.seat`: the seat from the public numbers: a read's first entry and length are those of the
    row of the public table under the program's name for the read (`nameH`,
    Johnson/Desc/Kinds/Law/TwelveOurs.lean).
  `Fill.letters`: the letters of Reads/HeadStated.lean. No letter is left free. The states are the
    records. The two requests are read off the record; the lookup's points and what the head heard
    are what the kind's seat (`seatAt`, Johnson/Stored/HeadSeatAt.lean) reads of the record; the
    smallness test's record and its list of tables are the record's.
  `Lies Z s o cov x t g bh pl`, 22 clauses. The record s stands in the head's link, opened; it holds
    what was heard (x); the text makes the tables t of x and of the covered positions; these tables
    are laid in the record; the reads' array in the record's ledger has the public number of
    columns; the record of the smallness test in s has the plan's matrices, their number, and the
    list of these tables; all the kind's letters are there; the table of the tables is the public
    one. Then ten invariants and sizes: eight premises of `runIs_at_twelve` that speak of x, and the
    sizes of the lookup's two points on the planes.
  `Fill.AtClose`: there are such o, cov, x, t, g, bh, pl.

What is shown.
  `tables_fold`: a yes of the text that makes the head's tables (`K8.ReadsQuiet.tables`): they are
    what `addAsk` makes of the fifteen lines `asksH` (Johnson/Road/HeadReads.lean), and la = ls +
    lt.
  `find_of_mem`: a tool: in a list of rows whose names differ, a row is found under its name.
  `foldFits_at`: **`FoldFits` (Reads/HeadFold.lean) at a record that lies so**, its last clause, the
    weights' tie, by `runIs_at_twelve` and `weights_of_runIs`.
  `lens_at`: **the test on lengths says yes, and every table lies in the third vector, at every
    record that lies so**, by Reads/LensAt.lean.
  `seatFits_at`: `SeatFits` at every record that lies so, from public premises.
  `head_at`: **`HeadClaimW Z.letters`** (Reads/HeadWeights.lean) from `Z.letters.Sane` and public
    premises alone.

Why `Lies` asks the sizes of the lookup's two points on the planes, zb0 and zb1. The statement asks
the test on lengths at every record that lies so. Without these two clauses one gets, from any
record that lies so, another at the same filling with an empty zb0: there a table on the planes has
one weight against a run of 2 ^ lmbH, and the test says no. So the statement would be false wherever
a record lies so. With them the test on lengths is a theorem.

Public premises. Of `foldFits_at` and `lens_at`: hJ, hlsJ, hc6, hls of `runIs_at_twelve`; of the
first also: the plan's matrices are the list `matsH`, eight of them; la = 16; `NumH`. Of `head_at`
beside these: a row of the reads' array has an entry; the kind's four sizes are the full size's;
every use's index lies below the length of its read's table in the public table of the tables.

Limits. `Sane`, which says among others that a record lies so, is a premise (one record, laid by
hand, lies so: Johnson/Desc/Reads/ToyRecord.lean). That a run's record
lies so is not shown: of the 22 clauses, ten are invariants and sizes that no theorem here brings,
and "the table of the tables is the public one" is brought by no test. hJ is shown of no real
layout
(Where this and lean/THEOREM.md differ, the page holds.); it and hlsJ are false at a
layout with fewer than six calls. From the record's words to an
instance nothing is shown. That the forms of these letters are the forms that the kind's block
claims at the record: Reads/FormsAtRecord.lean. Four forms of 35. The full size alone. Nothing on
soundness.


-/
import Johnson.Desc.Reads.RunIsLean
import Johnson.Desc.K8.ReadsQuietSame
import Johnson.Desc.Reads.LensAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads.AtSeat

open OnBytes (E zeroE)
open OnBytes.Model (Reading Aff longPoint)
open OnBytes.Model.Head (Shape HL Border HPlanH2 Covered Tables matsH costWeights ztOf callNo)
open OnBytes.Road.Hd (NumH Ask addAsk asksH asksH_names fold_spec wfT_empty Uni uni_one matsH_at)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.K8 (ReadsQuiet.tables ReadsQuiet.tablesOld ReadsQuiet.tables_same
  ReadsQuiet.bind_ok ReadsQuiet.named_ok ReadsQuiet.need_ok)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law
open VerifiableInference.Reads.AtHead
open Inst.Model.Head (Req)

/-! ## 1. A yes of the text that makes the tables -/

/-- **The tables are what addAsk makes of the fifteen lines.** -/
theorem tables_fold {h : Shape} {L : HL} {hp : HPlanH2} {cov : Covered}
    {x : OnBytes.Model.Head.Heard} {t : Tables} (e : ReadsQuiet.tables h L hp cov x = .ok t) :
    ∃ (ZV : Array E) (lowN : Array E × Array E) (qFC qROW : ℕ) (b0 b1 : Array E),
      h.la = h.ls + h.lt ∧
      (asksH h L x ZV (longPoint lowN.2 x.tN.r) (costWeights cov (ztOf h L x.g1 x.qH)).1
        (costWeights cov (ztOf h L x.g1 x.qH)).2.2 qFC qROW b0 b1).foldlM
          (addAsk hp.tl.mats) {} = some t := by
  rw [ReadsQuiet.tables_same] at e
  unfold ReadsQuiet.tablesOld at e
  obtain ⟨_, _, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨ZV, _, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨lowN, _, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨_, p4, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨qFC, _, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨qROW, _, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨b0, _, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨b1, _, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨t', e3, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨_, _, e⟩ := ReadsQuiet.bind_ok e
  simp only [pure, Except.pure, Except.ok.injEq] at e
  subst e
  have j4 := ReadsQuiet.need_ok p4
  simp only [Bool.and_eq_true, beq_iff_eq] at j4
  exact ⟨ZV, lowN, qFC, qROW, b0, b1, j4.2, ReadsQuiet.named_ok e3⟩

/-- In a list of rows whose names differ, a row is found under its name. -/
theorem find_of_mem : ∀ {l : List (String × ℕ × ℕ)}, (l.map (·.1)).Nodup →
    ∀ {e : String × ℕ × ℕ}, e ∈ l → (l.find? fun y => y.1 == e.1) = some e
  | [], _, _, he => absurd he List.not_mem_nil
  | y :: l, hn, e, he => by
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.1 he with rfl | he'
    · rw [List.find?_cons_of_pos (by simp)]
    · have hne : (y.1 == e.1) = false := by
        cases hb : (y.1 == e.1) with
        | false => rfl
        | true => exact absurd (by rw [beq_iff_eq.1 hb]; exact List.mem_map_of_mem he') hn.1
      simp only [List.find?_cons, hne]
      exact find_of_mem hn.2 he'

/-! ## 2. The filling -/

/-- What is public in the filling. -/
structure Fill where
  h : Shape
  L : HL
  b : Border
  hp : HPlanH2
  (iU3 work cols : ℕ)
  /-- the table of the tables: name, first entry, length -/
  tab : List (String × ℕ × ℕ)

/-- The relation's own request, read off the record's words, the heard reply and the plan's policy:
the first covered position and the position behind the last; at position t the next token of the
request, at the last position the heard reply; the policy's three numbers. -/
def Fill.reqOf (Z : Fill) (s : S) : Req :=
  { r := s.rowR, e := s.rowE
    win := fun t => if t + 1 < Z.h.T then s.tokv.getD (t + 1) 0 else s.replyTok?.getD 0
    pol := { C := Z.h.clipC, theta := Z.h.theta, cap := Z.h.cap } }

/-- The seat, from the public numbers. -/
def Fill.seat (Z : Fill) : Seat where
  iU3 := Z.iU3
  cols := Z.cols
  first := fun r => (Z.tab.find? fun e => e.1 == nameH r).map (·.2.1)
  count := fun r => ((Z.tab.find? fun e => e.1 == nameH r).map (·.2.2)).getD 0
  mat := fun
    | .wide => (0, Z.h.NHf)
    | .act => (Z.h.NHf, 1)
    | .row => (Z.h.NHf + 1, 1)

/-- The lookup's points, as the kind's seat reads them of a record; two empty points where it reads
none. -/
def Fill.look (Z : Fill) (s : S) : Point × (ℕ → Point) :=
  ((seatAt Z.h Z.iU3).lookup s).getD (#[], fun _ => #[])

/-- The record lies behind the reads' quiet step, with all the kind's letters. -/
structure Lies (Z : Fill) (s : S) (o : HeadOwn) (cov : Covered) (x : OnBytes.Model.Head.Heard)
    (t : Tables) (g : Given) (bh : Behind) (pl : Places) : Prop where
  here : s.here = .head o
  opened : o.opened = true
  covered : s.covered Z.h.T Z.h.V = .ok cov
  heard : o.x = some x
  made : ReadsQuiet.tables Z.h Z.L Z.hp cov x = .ok t
  /-- these tables are laid in the record -/
  laid : o.t = some t
  /-- the reads' array in the record's ledger has the public number of columns -/
  cols : ∃ tr, o.F.trees[Z.iU3]? = some tr ∧ tr.K = Z.cols
  mats : o.tl.mats = Z.hp.tl.mats
  funs : o.tl.funs = t.funs
  nm : o.tl.NM = Z.hp.tl.NM
  letters : lettersAt (parOf Z.h Z.work) (seatAt Z.h Z.iU3) s = .ok (g, bh, pl)
  /-- the table of the tables is the public one -/
  tab : t.tab = Z.tab
  /-- what the seat laid of the lookup's record still lies in what was heard -/
  hX1 : o.lookHeard = some x.g1
  hX2 : x.Zl = Point.last x.g1.zx (Z.h.ls + Z.h.lt)
  hqH : x.qH < 6
  hqN : x.qN < 6
  hsPV : x.PV.size = Z.h.lt
  hsSq : x.wpl.r.size = (letI := sizesOf Z.h; Norm.lNI + Norm.lPd) + Z.h.lt
  hsTV : x.tV.r.size = Z.h.lt
  hsTH : x.tH.r.size = Z.h.lt
  /-- the lookup's two points on the planes have all their coordinates -/
  hzb0 : x.g1.zb0.size = x.g1.shape.kT + x.g1.shape.cK + 5
  hzb1 : x.g1.zb1.size = x.g1.shape.kT + x.g1.shape.cK + 5

/-- There are such o, cov, x, t, g, bh, pl. -/
def Fill.AtClose (Z : Fill) (s : S) : Prop := ∃ o cov x t g bh pl, Lies Z s o cov x t g bh pl

/-- The letters of Reads/HeadStated.lean, filled from the record. -/
noncomputable def Fill.letters (Z : Fill) : HeadLetters Cb.Gl.E where
  val := Reading.gl.val
  h := Z.h
  L := Z.L
  sizes := sizesOf Z.h
  policy := (parOf Z.h Z.work).policy
  seat := Z.seat
  State := S
  AtClose := Z.AtClose
  req := Z.reqOf
  request := requestOf
  points := fun s =>
    (@fromLookup (sizesOf Z.h) (OnBytes.Model.Head.keyFloor Z.h) (Z.look s).1 (Z.look s).2).norm
  heard := fun s => (((seatAt Z.h Z.iU3).heard s).map (·.2.2)).getD ⟨{}⟩
  tl := fun s => match s.here with
    | .head o => o.tl
    | _ => {}
  funs := fun s => match s.here with
    | .head o => o.tl.funs
    | _ => #[]

/-! ## 3. FoldFits at the record -/

/-- **FoldFits at a record that lies so.** -/
theorem foldFits_at (Z : Fill) (hN : NumH Z.h Z.L)
    (hmats : ∃ gid sid, Z.hp.tl.mats = matsH Z.h Z.L Z.b gid sid) (hNM : Z.hp.tl.NM = 8)
    (hla : Z.h.la = 16)
    (hJ : ∀ q, q < 6 → (Z.L.calls.getD q default).lJ =
      (letI := sizesOf Z.h; lJ (OnBytes.Model.Head.keyFloor Z.h) (callKeys q)))
    (hlsJ : ∀ q, q < 6 → Z.h.ls ≤ (Z.L.calls.getD q default).lJ)
    (hc6 : ∀ seg q, callNo Z.L seg = some q → q < 6)
    (hls : Z.h.ls ≤ (letI := sizesOf Z.h; Norm.lNI + Norm.lPd))
    {s : S} {o : HeadOwn} {cov : Covered} {x : OnBytes.Model.Head.Heard} {t : Tables}
    {g : Given} {bh : Behind} {pl : Places} (Q : Lies Z s o cov x t g bh pl) :
    ∃ A, FoldFits Z.letters s A t := by
  obtain ⟨ZV, lowN, qFC, qROW, b0, b1, hlaE, hfold⟩ := tables_fold Q.made
  have I := runIs_at_twelve (g := g) (bh := bh) Z.h Z.L Z.b Z.hp Z.iU3 Z.work s o cov x t Q.here
    Q.opened Q.covered Q.heard Q.made Q.hX1 Q.hX2 Q.letters hJ hlsJ hc6 Q.hqH Q.hqN Q.hsPV
    Q.hsSq Q.hsTV Q.hsTH hls
  obtain ⟨hg, H, hH, hb⟩ := lettersAt_ok Q.letters
  obtain ⟨z, y, hz1, -, -, hgE⟩ := Came.given_ok _ _ _ _ hg
  subst hb
  subst hgE
  have htl : Z.letters.tl s = o.tl := by
    show (match s.here with
      | .head o => o.tl
      | _ => {}) = o.tl
    rw [Q.here]
  have hfn : Z.letters.funs s = o.tl.funs := by
    show (match s.here with
      | .head o => o.tl.funs
      | _ => #[]) = o.tl.funs
    rw [Q.here]
  have hlk : Z.look s = z := by
    unfold Fill.look
    rw [hz1]
    rfl
  have hhd : Z.letters.heard s = H.2.2 := by
    show (((seatAt Z.h Z.iU3).heard s).map (·.2.2)).getD ⟨{}⟩ = H.2.2
    rw [hH]
    rfl
  have hpt : Z.letters.points s =
      (@fromLookup (sizesOf Z.h) (OnBytes.Model.Head.keyFloor Z.h) z.1 z.2).norm := by
    show (@fromLookup (sizesOf Z.h) (OnBytes.Model.Head.keyFloor Z.h) (Z.look s).1
      (Z.look s).2).norm = _
    rw [hlk]
  obtain ⟨gid, sid, hm⟩ := hmats
  have hU : ∀ a ∈ asksH Z.h Z.L x ZV (longPoint lowN.2 x.tN.r)
      (costWeights cov (ztOf Z.h Z.L x.g1 x.qH)).1 (costWeights cov (ztOf Z.h Z.L x.g1 x.qH)).2.2
      qFC qROW b0 b1, ∃ m k, Uni Z.hp.tl.mats a m k := by
    obtain ⟨-, zf, -, -, -, -, -, -⟩ := matsH_at Z.L Z.b gid sid hN.NHf
    rw [← hm] at zf
    have uF : ∀ (phi : Array E) (nm : String),
        Uni Z.hp.tl.mats (0, Z.h.NHf, 2 ^ Z.h.la, phi, nm) Z.L.m Z.L.k := by
      intro phi nm q hq
      have hq' : q < 4 := by
        have h0 : q < Z.h.NHf := hq
        rw [hN.NHf] at h0
        exact h0
      have e := zf q hq'
      rw [← Nat.zero_add q] at e
      exact e
    intro a ha
    unfold asksH at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    · exact ⟨_, _, uF _ _⟩
    · exact ⟨_, _, uF _ _⟩
    all_goals exact ⟨_, _, uni_one _ _ rfl⟩
  obtain ⟨-, -, -, hnames, -⟩ := fold_spec Z.hp.tl.mats _ {} t hU wfT_empty hfold
  have hnd : (t.tab.map (·.1)).Nodup := by
    rw [hnames]
    exact asksH_names _ _ _ _ _ _ _ _ _ _ _
  refine ⟨asksOfRun ⟨Z.h, Z.L, Z.b, Z.hp, cov, x, t, Z.iU3⟩ ZV (longPoint lowN.2 x.tN.r) qFC qROW
    b0 b1, ?_⟩
  refine
    { fold := by
        rw [htl, Q.mats]
        exact hfold
      funs := hfn.trans Q.funs
      mats := ⟨Z.b, gid, sid, by rw [htl, Q.mats]; exact hm⟩
      NM := by rw [htl, Q.nm]; exact hNM
      la := hla
      wideParts := rfl
      act := rfl
      rowParts := rfl
      seat := ?_
      weights := ?_ }
  · intro r tb len hmem
    have hf := find_of_mem hnd hmem
    rw [Q.tab] at hf
    have hname : (askOf (asksOfRun ⟨Z.h, Z.L, Z.b, Z.hp, cov, x, t, Z.iU3⟩ ZV
        (longPoint lowN.2 x.tN.r) qFC qROW b0 b1) Z.h r).2.2.2.2 = nameH r := by
      cases r <;> rfl
    have hf' : (Z.tab.find? fun e => e.1 == nameH r) = some (nameH r, tb, len) := by
      rw [← hname]
      exact hf
    constructor
    · show ((Z.tab.find? fun e => e.1 == nameH r).map (·.2.1)).getD 0 = tb
      rw [hf']
      rfl
    · show ((Z.tab.find? fun e => e.1 == nameH r).map (·.2.2)).getD 0 = len
      rw [hf']
      rfl
  · intro r j hj
    have hw := @weights_of_runIs (sizesOf Z.h) (requestOf s)
      (@fromLookup (sizesOf Z.h) (OnBytes.Model.Head.keyFloor Z.h) z.1 z.2).norm H.1 H.2.1 H.2.2
      ⟨Z.h, Z.L, Z.b, Z.hp, cov, x, t, Z.iU3⟩ I rfl rfl hlaE Z.seat ZV (longPoint lowN.2 x.tN.r)
      qFC qROW b0 b1 r j hj
    show Reading.gl.val _ = Reading.gl.val ((@declOf (sizesOf Z.h) (requestOf s)
      (Z.letters.points s) (Z.letters.heard s) Z.seat r).w j)
    rw [hpt, hhd]
    exact hw

/-- **The two tests on the public list, at a record that lies so.** -/
theorem lens_at (Z : Fill)
    (hJ : ∀ q, q < 6 → (Z.L.calls.getD q default).lJ =
      (letI := sizesOf Z.h; lJ (OnBytes.Model.Head.keyFloor Z.h) (callKeys q)))
    (hlsJ : ∀ q, q < 6 → Z.h.ls ≤ (Z.L.calls.getD q default).lJ)
    (hc6 : ∀ seg q, callNo Z.L seg = some q → q < 6)
    (hls : Z.h.ls ≤ (letI := sizesOf Z.h; Norm.lNI + Norm.lPd))
    {s : S} {o : HeadOwn} {cov : Covered} {x : OnBytes.Model.Head.Heard} {t : Tables}
    {g : Given} {bh : Behind} {pl : Places} (Q : Lies Z s o cov x t g bh pl) :
    lensB (Z.letters.funs s) = true ∧ allU3B (Z.letters.funs s) = true := by
  have hz := hz_of_letters Z.h Z.L Z.iU3 Z.work s o x Q.here Q.opened Q.hX1 Q.letters Q.hqH
    (hJ _ Q.hqH) (hlsJ _ Q.hqH)
  have I := runIs_at_twelve (g := g) (bh := bh) Z.h Z.L Z.b Z.hp Z.iU3 Z.work s o cov x t Q.here
    Q.opened Q.covered Q.heard Q.made Q.hX1 Q.hX2 Q.letters hJ hlsJ hc6 Q.hqH Q.hqN Q.hsPV
    Q.hsSq Q.hsTV Q.hsTH hls
  have a1 := I.szt
  have a2 := I.ztFC
  have a3 := I.ztROW
  have a4 := I.ztH
  clear I
  obtain ⟨hg, H, hH, hb⟩ := lettersAt_ok Q.letters
  obtain ⟨z, y, hz1, -, -, hgE⟩ := Came.given_ok _ _ _ _ hg
  subst hb
  subst hgE
  have hfn : Z.letters.funs s = t.funs := by
    show (match s.here with
      | .head o => o.tl.funs
      | _ => #[]) = t.funs
    rw [Q.here]
    exact Q.funs
  have szt : (@fromLookup (sizesOf Z.h) (OnBytes.Model.Head.keyFloor Z.h) z.1 z.2).norm.zt.size =
      Z.h.lt := a1
  rw [hfn]
  refine lens_of_tables Q.made ?_ (fun q hq => ?_) (fun q hq => ?_) ?_ Q.hsPV Q.hsTV
    (tN_size Q.made) Q.hsTH Q.hzb0 Q.hzb1
  · rw [Q.hX2]
    exact last_size _ hz
  · exact (congrArg Array.size (a2 q hq)).trans szt
  · exact (congrArg Array.size (a3 q hq)).trans szt
  · exact (congrArg Array.size a4).trans szt

/-- **SeatFits at a record that lies so**, from public premises. -/
theorem seatFits_at (Z : Fill) (hN : NumH Z.h Z.L)
    (hmats : ∃ gid sid, Z.hp.tl.mats = matsH Z.h Z.L Z.b gid sid)
    (hT : (letI := sizesOf Z.h; Norm.T) = Inst.Model.Head.nT)
    (hS2 : (letI := sizesOf Z.h; Norm.S2) = 64) (hd : (letI := sizesOf Z.h; Norm.d) = 5120)
    (hJV : (letI := sizesOf Z.h; Head.JV) = 202048)
    (hcount : ∀ u : Use, u ∈ (letI := sizesOf Z.h; usesH) →
      (letI := sizesOf Z.h; u.index) < Z.seat.count u.read)
    {s : S} {o : HeadOwn} {cov : Covered} {x : OnBytes.Model.Head.Heard} {t : Tables}
    {g : Given} {bh : Behind} {pl : Places} (Q : Lies Z s o cov x t g bh pl) :
    SeatFits Z.letters s := by
  obtain ⟨gid, sid, hm⟩ := hmats
  obtain ⟨-, zf, -, -, zR1, zR2, -, -⟩ := matsH_at Z.L Z.b gid sid hN.NHf
  rw [← hm, ← Q.mats] at zf zR1 zR2
  have htl : Z.letters.tl s = o.tl := by
    show (match s.here with
      | .head o => o.tl
      | _ => {}) = o.tl
    rw [Q.here]
  have hsm : ∀ μ, (Z.letters.letters.size () s).m μ = (o.tl.mats.getD μ {}).m := fun μ => by
    show ((Z.letters.tl s).mats.getD μ {}).m = _
    rw [htl]
  have hsk : ∀ μ, (Z.letters.letters.size () s).k μ = (o.tl.mats.getD μ {}).k := fun μ => by
    show ((Z.letters.tl s).mats.getD μ {}).k = _
    rw [htl]
  have h5 : Z.h.NHf + 1 = 5 := by rw [hN.NHf]
  exact
    { T := hT, S2 := hS2, d := hd, JV := hJV, row := rfl, wide := rfl
      mR := by
        show (Z.letters.letters.size () s).m (Z.h.NHf + 1) = Z.L.mR
        rw [hsm, h5]
        exact zR1
      kR := by
        show (Z.letters.letters.size () s).k (Z.h.NHf + 1) = Z.L.kR
        rw [hsk, h5]
        exact zR2
      m := by
        rw [hsm]
        exact (zf 0 (by decide)).1
      k := by
        rw [hsk]
        exact (zf 0 (by decide)).2
      count := hcount }

/-- **The statement at the head, at the letters filled from the record.** -/
theorem head_at (Z : Fill) (hS : Z.letters.Sane)
    (hmats : ∃ gid sid, Z.hp.tl.mats = matsH Z.h Z.L Z.b gid sid) (hNM : Z.hp.tl.NM = 8)
    (hla : Z.h.la = 16)
    (hJ : ∀ q, q < 6 → (Z.L.calls.getD q default).lJ =
      (letI := sizesOf Z.h; lJ (OnBytes.Model.Head.keyFloor Z.h) (callKeys q)))
    (hlsJ : ∀ q, q < 6 → Z.h.ls ≤ (Z.L.calls.getD q default).lJ)
    (hc6 : ∀ seg q, callNo Z.L seg = some q → q < 6)
    (hls : Z.h.ls ≤ (letI := sizesOf Z.h; Norm.lNI + Norm.lPd)) (hcols : 0 < Z.cols)
    (hT : (letI := sizesOf Z.h; Norm.T) = Inst.Model.Head.nT)
    (hS2 : (letI := sizesOf Z.h; Norm.S2) = 64) (hd : (letI := sizesOf Z.h; Norm.d) = 5120)
    (hJV : (letI := sizesOf Z.h; Head.JV) = 202048)
    (hcount : ∀ u : Use, u ∈ (letI := sizesOf Z.h; usesH) →
      (letI := sizesOf Z.h; u.index) < Z.seat.count u.read) :
    HeadClaimW Z.letters :=
  head_of_fold Z.letters hS fun s hs => by
    obtain ⟨o, cov, x, t, g, bh, pl, Q⟩ := hs
    obtain ⟨A, F⟩ := foldFits_at Z hS.2.1 hmats hNM hla hJ hlsJ hc6 hls Q
    exact ⟨(lens_at Z hJ hlsJ hc6 hls Q).1,
      seatFits_at Z hS.2.1 hmats hT hS2 hd hJV hcount Q, ⟨A, t, F⟩, hcols, rfl, rfl, rfl⟩

end VerifiableInference.Reads.AtSeat

#print axioms VerifiableInference.Reads.AtSeat.tables_fold
#print axioms VerifiableInference.Reads.AtSeat.find_of_mem
#print axioms VerifiableInference.Reads.AtSeat.foldFits_at
#print axioms VerifiableInference.Reads.AtSeat.lens_at
#print axioms VerifiableInference.Reads.AtSeat.seatFits_at
#print axioms VerifiableInference.Reads.AtSeat.head_at
