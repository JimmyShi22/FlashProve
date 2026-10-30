-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/K4AtTable.lean: K4's ROW AT THE TABLE OF JOINTS: from `K04Law`
(Johnson/Desc/Plain/K04Plain.lean), at whatever letters, to THE BLOCK's OWN LAW IN THE TABLE's OWN
TERMS (`Piece.Own` between `onQ k` and `onQ (k + 1)`, at `meansQ`, `insQ k`, `outsQ k`:
Johnson/Desc/Sound/BordersQ.lean), through the table's own door `ownAtTableWide`. Definitions,
statements and proofs. GLUE: no draw, no count.

At A := the first chain's carried record S itself, get s := (Z, s), Z a letter (what was handed to
the chain); at the seat `seatS`.

  `goodIn_of_keepsW`: the plain law at one world (`KeepsW`) is `Piece.GoodIn` where the piece's
    extractor is the identity at every yes (hx). K4's row lays nothing.
  `AtK4 links ps k m pl`: block number k stands at the place pl: piece 3 of segment m, a layers'
    one.
  `rowQ_k4`, `ins_k4`, `outs_k4`: the table's row there, written out: it closes constr m idn · worth
    m 2 "planes" | "keys" | "rider"; opens formsT m 3 "own" · formsT m 2 "planes" | "join" · wo m;
    reads pin m 0 · pinW · constr m small · pinI; and "no mark" stands on both sides.
  `mark_stays`: the door's fifth premise: at a yes of a piece that holds `below bk`, bk hearing as
    K4's own block at seatS: a mark stays (`mark_of_yes`, LeftOnOfYes.lean).
  **`k4_own_at_table`**: `K04Law seatS Sm Lt par bk q`, hb, hh, hback, hx, the door's four
    implications (hon · hon' · hB · hF, each asked at an unmarked statement inside the promise) and
    hDec ("decodes" rides) give the block's own law at the table.
  `K4Rel`: EIGHT LINES ON THE MEANING, item by item: what each opened item must give (forms · wo ·
    ctxIn: EACH WITH THE LAW's OWN PROMISE BEHIND (the letter on'), THE TABLE's PROMISE BEHIND (the
    letter onB; `k4_own_of_lines` takes it as `onQ … (k + 1)`) AND "no mark" IN HAND), what must
    give each closed item (idn · planes · keys · rider: EACH WITH WHAT THE ROW READS IN HAND (the
    letter ctx) · ctxOut).
  **`k4_own_of_lines`**: the same with hB and hF paid from `K4Rel`.

OBJECT · USER · LETTERS. OBJECT: bk is meant as the block that the first chain's description seats
at piece 3 of a layers' segment; of it these theorems read only hh: what its yes gives (`HearsAs`,
which passes to every block whose yes is a yes of `blockAtS par`: `hearsAs_of_yes`). NO THEOREM HERE
NAMES THAT BLOCK. USER: `Piece.Own` at block number k is one clause of `EachOwn`
(Johnson/Desc/Sound/Spine.lean), which `jointsJoin` (BordersQ.lean) spends; NOTHING HANDS K4's
CLAUSE TO `EachOwn` YET. LETTERS, filled by nobody here: N · Mg · Z · links · ps · k · m · pl · q
but for its block and its rounds behind · Sm · Lt · par.

Limits. K04_law IS NOT PROVED BY THIS: `K04Law` IS A PREMISE. hon, hon', hDec, hx AND THE EIGHT
LINES ARE PREMISES: no filling of `Meaning` is shown to meet them. formsT m 2 "planes" and "join"
are spent nowhere (at a layers' segment the table's `runsOf` names no run for them). The riders
(`Piece.Frames`) are not treated. That the real chain's record is S and its get is (Z, ·) is not
said. `FormsT` asks of every entry that a form names the ledger's own test `Fork.hasEnt`, IN FRONT
OF the sending that brings the reads: were that false at honest ledgers, what the row opens would
hold of nothing and K4's clause for nothing. BY A RUN, NO THEOREM: at one honest proof of each of
two sizes `runsThere` (K04Plain.lean; a copy with code) is true at the record right behind K4's yes
at every layers' place, and false at a control. Nothing on
soundness.
-/
import Johnson.Desc.Sound.BordersQ
import Johnson.Road.K4.LeftOnOfYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Flat OnBytes.Maker
open OnBytes.Desc.First.K4 (Par seatS formsBack)
open _root_.Run (ckP)
open _root_.Run.PQ (CK)
open VerifiableInference.Desc (Place Block)
open VerifiableInference.Desc.First (S ModelPart Item Part Meaning Numbers segRow rowOf)
open VerifiableInference.Desc.Sound (Frame Piece below relAt onQ meansQ insQ outsQ rowQ
  ownAtTableWide strsOf)
open VerifiableInference.Desc.Plain.K04 (Sem Letters Front Behind K04Law HearsAs FormsT frontRun)

/-- The plain law at one world is `GoodIn` where the extractor is the identity at every yes. -/
theorem goodIn_of_keepsW {T Cl W : Type} {C : CK} {F : Frame} (p : Piece C F T Cl W)
    {on on' : T × F.E.Str → Prop} {R R' : T × F.E.Str → W → Prop}
    (h : p.ior.red.KeepsW on on' R R' p.err)
    (hx : ∀ a τ b w, p.ior.red.out a τ = some b → p.ext a τ w = w) : p.GoodIn on on' R R' :=
  fun a ha => Doomed.mono _ _ (fun τ hτ b hb =>
    ⟨(hτ b hb).1, fun w hw => by rw [hx a τ b w hb]; exact (hτ b hb).2 w hw⟩) (h a ha)

/-- Block number k stands at piece 3 of the layers' segment m. -/
structure AtK4 (links : List ModelPart) (ps : List Place) (k m : ℕ) (pl : Place) : Prop where
  here : ps[k]? = some pl
  link : pl.link = some m
  sub : links[m]? = some .layers
  piece : pl.piece = 3

variable {links : List ModelPart} {ps : List Place} {k m : ℕ} {pl : Place}

/-- The table's row at K4's place. -/
theorem rowQ_k4 (H : AtK4 links ps k m pl) : rowQ links ps k = segRow .layers m 3 := by
  simp only [rowQ, H.here, Option.map_some, Option.getD_some,
    VerifiableInference.Desc.First.rowOf, H.link, H.sub, H.piece]

/-- What the row closes, with what it reads, and "no mark". -/
theorem ins_k4 (H : AtK4 links ps k m pl) (i : Item) :
    insQ links ps k i ↔ i ∈ [Item.constr m .idn, .worth m 2 "planes", .worth m 2 "keys",
      .worth m 2 "rider", .pin m 0, .pinW, .constr m .small, .pinI, .unmarked] := by
  unfold insQ
  rw [rowQ_k4 H]
  exact Iff.rfl

/-- What it opens, with what it reads, and "no mark". -/
theorem outs_k4 (H : AtK4 links ps k m pl) (i : Item) :
    outsQ links ps k i ↔ i ∈ [Item.formsT m 3 "own", .formsT m 2 "planes", .formsT m 2 "join",
      .wo m, .pin m 0, .pinW, .constr m .small, .pinI, .unmarked] := by
  unfold outsQ
  rw [rowQ_k4 H]
  exact Iff.rfl

variable {P W Cl : Type} {Fr : Frame} (N : Numbers) (Mg : Meaning P W) (Z : P)
  {q : Piece (ckP .two) Fr S Cl W} {Sm : Sem W} {Lt : Letters S W Fr} {par : Par}
  {bk : Block S Cl}

/-- A mark stays at a yes. -/
theorem mark_stays (hb : q.b = below bk) (hh : HearsAs seatS par bk) (hback : q.back = [])
    (a : S × Fr.E.Str) (τ : Tr (uLT (ckP .two) q.ds)) (b : S × Fr.E.Str)
    (h : q.ior.red.out a τ = some b) (hm : a.1.failed ≠ none) : b.1.failed ≠ none := by
  obtain ⟨_, fo, o, G, y, rfl⟩ := yes_of_out seatS hh hb hback a b τ h
  rw [mark_of_yes y]
  exact hm

/-- **FROM `K04Law` (A PREMISE: NOT PROVED) to K4's own law at the table, through the table's
door**: under hb, hh, hback, hx, the door's four implications and hDec. -/
theorem k4_own_at_table (links : List ModelPart) (ps : List Place) (k : ℕ)
    (hlaw : K04Law seatS Sm Lt par bk q) (hb : q.b = below bk) (hh : HearsAs seatS par bk)
    (hback : q.back = []) (hx : ∀ a τ b w, q.ior.red.out a τ = some b → q.ext a τ w = w)
    (hon : ∀ a, onQ N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none → Lt.on a)
    (hon' : ∀ a τ b, onQ N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      q.ior.red.out a τ = some b → Lt.on' b → onQ N Mg links ps (fun s => (Z, s)) (k + 1) b)
    (hB : ∀ a τ b w, onQ N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      q.ior.red.out a τ = some b → Lt.on' b →
      relAt (meansQ N Mg fun s => (Z, s)) (outsQ links ps k) b w → Behind seatS Sm Lt par b w)
    (hF : ∀ a τ b w, onQ N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      q.ior.red.out a τ = some b → Lt.on' b →
      relAt (meansQ N Mg fun s => (Z, s)) (outsQ links ps k) b w → Front Lt a w →
      relAt (meansQ N Mg fun s => (Z, s)) (insQ links ps k) a w)
    (hDec : ∀ a τ b, q.ior.red.out a τ = some b → Mg.decodes (Z, a.1) (strsOf Fr a.2) →
      Mg.decodes (Z, b.1) (strsOf Fr b.2)) :
    q.Own (onQ N Mg links ps (fun s => (Z, s)) k) (onQ N Mg links ps (fun s => (Z, s)) (k + 1))
      (meansQ N Mg fun s => (Z, s)) (insQ links ps k) (outsQ links ps k) :=
  ownAtTableWide S Cl P W (ckP .two) Fr N Mg links ps (fun s => (Z, s)) k q Lt.on Lt.on'
    (Front Lt) (Behind seatS Sm Lt par) (goodIn_of_keepsW q (hlaw hb hh) hx)
    (fun a h1 h2 => hon a h1 (not_not.mp h2))
    (fun a τ b h1 h2 h3 h4 => hon' a τ b h1 (not_not.mp h2) h3 h4)
    (fun a τ b w h1 h2 h3 h4 h5 => hB a τ b w h1 (not_not.mp h2) h3 h4 h5)
    (fun a τ b w h1 h2 h3 h4 h5 h6 => by
      rw [hx a τ b w h3] at h6 ⊢
      exact hF a τ b w h1 (not_not.mp h2) h3 h4 h5 h6)
    (fun a τ b h hm => mark_stays hb hh hback a τ b h hm) hDec

/-- **The lines on the meaning, item by item**, at the letters Lt and the reading Sm of a world. -/
structure K4Rel (m : ℕ) (Sm : Sem W) (Lt : Letters S W Fr) (par : Par)
    (onB : S × Fr.E.Str → Prop) : Prop where
  /-- formsT m 3 "own": every form behind K4's two runs is there and worth 0, the reads as true -/
  forms : ∀ b w, Lt.on' b → onB b → b.1.failed = none →
    meansQ (Fr := Fr) N Mg (fun s => (Z, s)) (.formsT m 3 "own") b w →
    FormsT seatS Sm (frontRun par) formsBack b.1 w
  /-- wo m: WITH THE TABLE's PROMISE BEHIND IN HAND (onB), AT AN UNMARKED b: the item's sentence may
  hold
  of every witness where its reader of the pending row gives none: the public item that the table
  ties to it, which stands in that promise, shuts that out -/
  wo : ∀ b w, Lt.on' b → onB b → b.1.failed = none →
    meansQ (Fr := Fr) N Mg (fun s => (Z, s)) (.wo m) b w → Lt.wo b w
  /-- what the row reads, behind: the four items give the letter -/
  ctxIn : ∀ b w, Lt.on' b → onB b → b.1.failed = none →
    meansQ (Fr := Fr) N Mg (fun s => (Z, s)) (.pin m 0) b w →
    meansQ (Fr := Fr) N Mg (fun s => (Z, s)) .pinW b w →
    meansQ (Fr := Fr) N Mg (fun s => (Z, s)) (.constr m .small) b w →
    meansQ (Fr := Fr) N Mg (fun s => (Z, s)) .pinI b w → Lt.ctx b w
  /-- what the row reads, in front: the letter gives the four items -/
  ctxOut : ∀ a w, Lt.ctx a w → meansQ (Fr := Fr) N Mg (fun s => (Z, s)) (.pin m 0) a w ∧
    meansQ (Fr := Fr) N Mg (fun s => (Z, s)) .pinW a w ∧
    meansQ (Fr := Fr) N Mg (fun s => (Z, s)) (.constr m .small) a w ∧
    meansQ (Fr := Fr) N Mg (fun s => (Z, s)) .pinI a w
  /-- constr m idn: WITH WHAT THE ROW READS IN HAND (ctx): the item speaks of the integers behind
  the
  committed symbols, the letter of the field's cells: the two meet only where the symbols are a
  packing
  of small integers and the pins hold -/
  idn : ∀ a w, Lt.on a → Lt.ctx a w → Lt.idn a w →
    meansQ (Fr := Fr) N Mg (fun s => (Z, s)) (.constr m .idn) a w
  /-- worth m 2 "planes" | "keys" | "rider": likewise with ctx in hand -/
  planes : ∀ a w, Lt.on a → Lt.ctx a w → Lt.worthPlanes a w →
    meansQ (Fr := Fr) N Mg (fun s => (Z, s)) (.worth m 2 "planes") a w
  keys : ∀ a w, Lt.on a → Lt.ctx a w → Lt.worthKeys a w →
    meansQ (Fr := Fr) N Mg (fun s => (Z, s)) (.worth m 2 "keys") a w
  rider : ∀ a w, Lt.on a → Lt.ctx a w → Lt.worthRider a w →
    meansQ (Fr := Fr) N Mg (fun s => (Z, s)) (.worth m 2 "rider") a w

/-- **The same, with the two implications on the relations paid from the lines.** -/
theorem k4_own_of_lines (H : AtK4 links ps k m pl) (hlaw : K04Law seatS Sm Lt par bk q)
    (hb : q.b = below bk) (hh : HearsAs seatS par bk) (hback : q.back = [])
    (hx : ∀ a τ b w, q.ior.red.out a τ = some b → q.ext a τ w = w)
    (hon : ∀ a, onQ N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none → Lt.on a)
    (hon' : ∀ a τ b, onQ N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      q.ior.red.out a τ = some b → Lt.on' b → onQ N Mg links ps (fun s => (Z, s)) (k + 1) b)
    (R : K4Rel N Mg Z m Sm Lt par (onQ N Mg links ps (fun s => (Z, s)) (k + 1)))
    (hDec : ∀ a τ b, q.ior.red.out a τ = some b → Mg.decodes (Z, a.1) (strsOf Fr a.2) →
      Mg.decodes (Z, b.1) (strsOf Fr b.2)) :
    q.Own (onQ N Mg links ps (fun s => (Z, s)) k) (onQ N Mg links ps (fun s => (Z, s)) (k + 1))
      (meansQ N Mg fun s => (Z, s)) (insQ links ps k) (outsQ links ps k) := by
  refine k4_own_at_table N Mg Z links ps k hlaw hb hh hback hx hon hon' ?_ ?_ hDec
  · intro a τ b w h1 h2 h3 hb' hw
    have hB := hon' a τ b h1 h2 h3 hb'
    have g : ∀ i, i ∈ [Item.formsT m 3 "own", .formsT m 2 "planes", .formsT m 2 "join",
        .wo m, .pin m 0, .pinW, .constr m .small, .pinI, .unmarked] →
        meansQ N Mg (fun s => (Z, s)) i b w := fun i hi => hw i ((outs_k4 H i).mpr hi)
    have hu : b.1.failed = none := g .unmarked (by simp)
    exact ⟨R.ctxIn b w hb' hB hu (g _ (by simp)) (g _ (by simp)) (g _ (by simp)) (g _ (by simp)),
      R.forms b w hb' hB hu (g _ (by simp)), R.wo b w hb' hB hu (g _ (by simp))⟩
  · intro a τ b w h1 h2 _ _ _ hf i hi
    obtain ⟨c, f1, f2, f3, f4⟩ := hf
    obtain ⟨c1, c2, c3, c4⟩ := R.ctxOut a w c
    have ha := hon a h1 h2
    have hi' := (ins_k4 H i).mp hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
    rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact R.idn a w ha c f1
    · exact R.planes a w ha c f2
    · exact R.keys a w ha c f3
    · exact R.rider a w ha c f4
    · exact c1
    · exact c2
    · exact c3
    · exact c4
    · exact h2

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.goodIn_of_keepsW
#print axioms OnBytes.Road.K4.k4_own_at_table
#print axioms OnBytes.Road.K4.k4_own_of_lines
