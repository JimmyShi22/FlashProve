-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/OwesAt.lean: THE SMALLNESS TEST AT THE TABLE OF JOINTS: WHAT IS
OWED AT ONE PLACE OF THE KIND (`K8OwesR`) FROM THE LAW OF THE DRAW AND ONE
STRUCTURE OF NAMED PREMISES. A RULE OVER LETTERS. NO SOUNDNESS.

`K8OwesR` asks for the kind's own conditions and relations, as functions of the statement in front,
with the law between them and three ties to the table. Here these letters are WRITTEN, the law is
the law of the draw at tables of cells (`k08_goodInT_cap_whole`,
Johnson/Desc/First/K8/LawGoodCapT.lean), and the three ties are proved. What is left stands in ONE
structure:
  `K8Fill`: THE PREMISES, field by field, each with a payer of its own:
    the piece: its rounds, no round behind, the cap as its errors; 128 combinations;
    the table: what the row at the place closes, opens and reads; `DrawBlind`; `makes`: what the
      draw must make behind itself (the public test that is tied to the run of forms that it opens);
    the filling: `pin` is the table's pin over the plan's members; the reader of OOD samples is
      blind to the draw; `closes`: the tie at `cellsAt` gives the part "small" and the item "tie";
      `opens`: the run's forms and the digits' part give `SmallAt` and `DigitsAt` at `cellsAhead`;
    `here`: at a reached statement inside the promise, without a mark: a link, a ledger and the
      smallness test's part are there; `frontB`; `Named.namedB`; `K8Sits` at the state's own list
      of members; the fence; `CellsIn` AT THE EARLY ARRAYS ALONE
      (what is spent); "no collision" at the two sendings' seats.
  THE LETTERS, off the statement in front a₀ (`Lt`: tl, L: a₀'s own; σ0: the OOD samples that a₀
    holds): the members: `Named.listOf` | `Named.seatFn` at a₀'s statement of oracles, book, tl, L;
    the one table of cells: `cellsAhead` at a₀; the law's public value: tl.
  `k08_owesR`: **`K8Fill → K8OwesR`.**
Where the state's value has not the place's numbers the block says no: nothing is owed
(`goodIn_where_or_refuses`): so `PlaceRec` is no premise.
Limits. `K8Fill` is shown at no filling. Nothing on soundness.

-/
import Johnson.P1K8R.TiedReach
import Johnson.Desc.First.K8.LawGoodCapT
import Johnson.Desc.First.K8.LawSmallAhead
import Johnson.Desc.First.K8.PinsSig
import Johnson.Desc.First.K8.LawFront
import Johnson.Desc.First.K8.LawRefuses
import Johnson.Desc.Sound.GoodInStretch

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace P1K8T

open Iop
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj Johnson.Pack
open OnBytes.Tie.Pv.Tail (early)
open VerifiableInference.Desc (Block FileDescription Place Claim Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers)
open VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.First.K8.Ready (frontB cond_of_front sameLay_own)

section
variable {Pp Cells Tok Xi : Type} {Fr : Frame} (G : FileDescription Xi) (cs : OnBytes.Codes)
  (arr : ℕ → ℕ → ℕ)
  (smpT : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem) (N : Numbers) (Mg : Meaning Pp (Wit Cells Tok MsgT)) (links : List ModelPart)
  (ps : List Place) (Rch : ℕ → (Pp × S) × Fr.E.Str → Prop) (k m pc : ℕ)
  (q : Piece (Run.ckP .two) Fr (Pp × S) Claim (Wit Cells Tok MsgT)) (p : ParW)
  (rad : OracleShape → ℕ) (oS : Pp → S → Strs → Prop)

/-- The members, off a state's statement of oracles and book. -/
def lA (s : S) (tl : HTailF2) (L : LinkCtx) : List (OracleShape × ℕ) :=
  Named.listOf rad s.st s.book tl L

/-- Their seats. -/
def sA (s : S) (tl : HTailF2) (L : LinkCtx) : Fin (lA rad s tl L).length → ℕ × ℕ :=
  Named.seatFn rad s.st s.book tl L

attribute [irreducible] lA sA

/-- **The premises.** -/
structure K8Fill : Prop where
  piece : ∀ B' : Block S Claim,
    (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece (Run.ckP .two) Fr S Claim (Wit Cells Tok MsgT)) =
    ⟨below B', q.base, [rdt p.toPar], [], fun _ _ w => w,
      Err.cap 128 (uLT (Run.ckP .two) [rdt p.toPar])⟩
  tau : p.tau = 128
  ins : (rowQ links ps k).ins = [.constr m .small, .tie m]
  outs : (rowQ links ps k).outs = [.forms m pc "small", .constr m .lookDigits]
  ctx : (rowQ links ps k).ctx = [.pin m 0, .pin m 1]
  blind : DrawBlind N Mg links ps k q.base oS
  makes : ∀ (z : Pp) (a b : S × Fr.E.Str), onQ N Mg links ps (fun s => (z, s)) k a →
    Rch k ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
    (∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS p.toPar).decide a.1 rs gs = .ok b.1) →
    oS z b.1 (strsOf Fr b.2)
  pin : ∀ j t a y w, Mg.pin j t a y w → pinJT cs G arr smpT ms j t a y w
  smpStay : ∀ (z : Pp) (s : S) (tl : HTailF2) (mm : Array Int) (f : Array Nat), s.tl? = some tl →
    smpT (z, s.putTl { tl with cfF := mm, cfFirst := f }) = smpT (z, s)
  closes : ∀ (z : Pp) (a : S × Fr.E.Str) w, onQ N Mg links ps (fun s => (z, s)) k a →
    Rch k ((z, a.1), a.2) → ¬ a.1.failed ≠ none → TieAt (cellsAt cs arr ms N m (z, a.1)) a.1 w →
    Mg.constr m .small (z, a.1) (strsOf Fr a.2) w ∧ Mg.tie m (z, a.1) (strsOf Fr a.2) w
  opens : ∀ (z : Pp) (a b : S × Fr.E.Str) w, onQ N Mg links ps (fun s => (z, s)) k a →
    Rch k ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
    (∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS p.toPar).decide a.1 rs gs = .ok b.1) →
    Mg.forms m pc "small" (z, b.1) (strsOf Fr b.2) w →
    Mg.constr m .lookDigits (z, b.1) (strsOf Fr b.2) w →
    SmallAt (cellsAhead cs arr ms N m (z, b.1)) b.1 w ∧
      DigitsAt (cellsAhead cs arr ms N m (z, b.1)) b.1 w
  here : ∀ (z : Pp) (a : S × Fr.E.Str), onQ N Mg links ps (fun s => (z, s)) k a →
    Rch k ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
    ∃ tl L F, a.1.tl? = some tl ∧ a.1.link? = some L ∧ a.1.fork? = some F ∧
      frontB a.1 = true ∧ Named.namedB p.toPar a.1.st a.1.book tl L = true ∧
      K8Sits G cs (lA rad a.1 tl L) (sA rad a.1 tl L) smpT ms N m ∧
      (∀ i, (sA rad a.1 tl L i).1 < q.base) ∧
      (∀ t r c o, early tl (.cell t r c) = true → Named.msgNow L t = some o →
        CellsIn cs (lA rad a.1 tl L) (sA rad a.1 tl L) ms N m a.1 t o) ∧
      ∀ t ∈ [0, 1], ∀ e ∈ N.sent m t, noCollJT cs G smpT ms e.1 e.2 (z, a.1) (strsOf Fr a.2)

/-- The letters that are read off the statement in front: its own value and link, and the OOD
samples that it holds. -/
def Lt (z : Pp) (a₀ : S × Fr.E.Str) (tl : HTailF2) (L : LinkCtx)
    (σ0 : (sigOf cs (lA rad a₀.1 tl L)).Smp) : Prop :=
  a₀.1.tl? = some tl ∧ a₀.1.link? = some L ∧
    ∀ i, smpAt cs (lA rad a₀.1 tl L) (sA rad a₀.1 tl L) smpT z a₀.1 i = some (σ0 i)

/-- The law's total reader of OOD samples. -/
noncomputable abbrev smpA (z : Pp) (a₀ : S × Fr.E.Str) (tl : HTailF2) (L : LinkCtx)
    (σ0 : (sigOf cs (lA rad a₀.1 tl L)).Smp) : S → (sigOf cs (lA rad a₀.1 tl L)).Smp :=
  totalOf cs (lA rad a₀.1 tl L) (smpAt cs (lA rad a₀.1 tl L) (sA rad a₀.1 tl L) smpT z) σ0

/-- The law's letters as one term. -/
noncomputable abbrev rdA (z : Pp) (a₀ : S × Fr.E.Str) (tl : HTailF2) (L : LinkCtx)
    (σ0 : (sigOf cs (lA rad a₀.1 tl L)).Smp)
    (hs : ∀ (s : S) (t : HTailF2) (mm : Array Int) (f : Array Nat), s.tl? = some t →
      smpA cs smpT rad z a₀ tl L σ0 (s.putTl { t with cfF := mm, cfFirst := f }) =
        smpA cs smpT rad z a₀ tl L σ0 s)
    (hseat : ∀ i, (sA rad a₀.1 tl L i).1 < q.base) :=
  tabReads (Cells := Cells) (Tok := Tok) tl cs (lA rad a₀.1 tl L) (sA rad a₀.1 tl L) arr
    (entOfMsgs Cells Tok cs (lA rad a₀.1 tl L) (sA rad a₀.1 tl L) arr ms N m z a₀.1)
    (cellsAhead cs arr ms N m (z, a₀.1)) G (smpA cs smpT rad z a₀ tl L σ0) hs Claim Fr p.toPar
    q.base (leastAt p.toPar (OnBytes.Tie.Pv.Tail.sizeOf tl).size) hseat

/-- The condition in front. -/
def oA (z : Pp) (a₀ a : S × Fr.E.Str) : Prop :=
  ∃ tl L σ0, Lt cs smpT rad z a₀ tl L σ0 ∧ a = a₀ ∧
    ∃ hs hseat, (rdA G cs arr smpT ms N m q p rad z a₀ tl L σ0 hs hseat).onA a ∧ Extra a.1

/-- The condition behind. -/
def oB (z : Pp) (a₀ b : S × Fr.E.Str) : Prop :=
  ∃ tl L σ0, Lt cs smpT rad z a₀ tl L σ0 ∧
    ∃ hs hseat, (rdA G cs arr smpT ms N m q p rad z a₀ tl L σ0 hs hseat).onB b ∧ Extra b.1

/-- The relation in front. -/
def rA (z : Pp) (a₀ a : S × Fr.E.Str) (w : Wit Cells Tok MsgT) : Prop :=
  ∃ tl L σ0, Lt cs smpT rad z a₀ tl L σ0 ∧
    PinsAt cs (lA rad a₀.1 tl L) (sA rad a₀.1 tl L) arr G (smpA cs smpT rad z a₀ tl L σ0) Fr a w ∧
    TieAt (cellsAhead cs arr ms N m (z, a₀.1)) a.1 w

/-- The relation behind. -/
def rB (z : Pp) (a₀ b : S × Fr.E.Str) (w : Wit Cells Tok MsgT) : Prop :=
  ∃ tl L σ0, Lt cs smpT rad z a₀ tl L σ0 ∧
    PinsAt cs (lA rad a₀.1 tl L) (sA rad a₀.1 tl L) arr G (smpA cs smpT rad z a₀ tl L σ0) Fr b w ∧
    SmallAt (cellsAhead cs arr ms N m (z, a₀.1)) b.1 w ∧
    DigitsAt (cellsAhead cs arr ms N m (z, a₀.1)) b.1 w

/-- The letters are one. -/
theorem Lt.one {z : Pp} {a₀ : S × Fr.E.Str} {tl tl' : HTailF2} {L L' : LinkCtx}
    {σ0 : (sigOf cs (lA rad a₀.1 tl L)).Smp} {σ0' : (sigOf cs (lA rad a₀.1 tl' L')).Smp}
    (h : Lt cs smpT rad z a₀ tl L σ0) (h' : Lt cs smpT rad z a₀ tl' L' σ0') :
    ∃ (e1 : tl' = tl) (e2 : L' = L), (e1 ▸ e2 ▸ σ0') = σ0 := by
  obtain rfl : tl = tl' := Option.some.inj (h.1.symm.trans h'.1)
  obtain rfl : L = L' := Option.some.inj (h.2.1.symm.trans h'.2.1)
  exact ⟨rfl, rfl, funext fun i => Option.some.inj ((h'.2.2 i).symm.trans (h.2.2 i))⟩

variable {G cs arr smpT ms N Mg links ps Rch k m pc q p rad oS}

/-- The partial reader is blind to the draw where the table's is. General in the list. -/
theorem smpAt_put
    (hst : ∀ (z : Pp) (s : S) (tl : HTailF2) (mm : Array Int) (f : Array Nat), s.tl? = some tl →
      smpT (z, s.putTl { tl with cfF := mm, cfFirst := f }) = smpT (z, s))
    (l : List (OracleShape × ℕ)) (seat' : Fin l.length → ℕ × ℕ) (z : Pp) (s : S) (t : HTailF2)
    (mm : Array Int) (f : Array Nat) (e : s.tl? = some t) :
    smpAt cs l seat' smpT z (s.putTl { t with cfF := mm, cfFirst := f }) =
      smpAt cs l seat' smpT z s := by
  funext i
  unfold smpAt
  rw [hst z s t mm f e]

/-- So is the total one. -/
theorem smpA_put (H : K8Fill G cs arr smpT ms N Mg links ps Rch k m pc q p rad oS) (z : Pp)
    (a₀ : S × Fr.E.Str) (tl : HTailF2) (L : LinkCtx) (σ0 : (sigOf cs (lA rad a₀.1 tl L)).Smp)
    (s : S) (t : HTailF2) (mm : Array Int) (f : Array Nat) (e : s.tl? = some t) :
    smpA cs smpT rad z a₀ tl L σ0 (s.putTl { t with cfF := mm, cfFirst := f }) =
      smpA cs smpT rad z a₀ tl L σ0 s :=
  totalOf_put cs (lA rad a₀.1 tl L) (smpAt cs (lA rad a₀.1 tl L) (sA rad a₀.1 tl L) smpT z) σ0
    (smpAt_put H.smpStay (lA rad a₀.1 tl L) (sA rad a₀.1 tl L) z) s t mm f e

/-- What the field `here` gives, with the OOD samples that the statement holds. -/
theorem K8Fill.letters (H : K8Fill G cs arr smpT ms N Mg links ps Rch k m pc q p rad oS) (z : Pp)
    (a : S × Fr.E.Str) (ha : onQ N Mg links ps (fun s => (z, s)) k a)
    (hr : Rch k ((z, a.1), a.2)) (hm : ¬ a.1.failed ≠ none) :
    ∃ tl L F σ0, Lt cs smpT rad z a tl L σ0 ∧ a.1.fork? = some F ∧ frontB a.1 = true ∧
      Named.namedB p.toPar a.1.st a.1.book tl L = true ∧
      K8Sits G cs (lA rad a.1 tl L) (sA rad a.1 tl L) smpT ms N m ∧
      (∀ i, (sA rad a.1 tl L i).1 < q.base) ∧
      (∀ t r c o, early tl (.cell t r c) = true → Named.msgNow L t = some o →
        CellsIn cs (lA rad a.1 tl L) (sA rad a.1 tl L) ms N m a.1 t o) ∧
      ∀ t ∈ [0, 1], ∀ e ∈ N.sent m t,
        noCollJT cs G smpT ms e.1 e.2 (z, a.1) (strsOf Fr a.2) := by
  obtain ⟨tl, L, F, ht, hL, hF, hfr, hN, T, hseat, hC, hnc⟩ := H.here z a ha hr hm
  obtain ⟨σ0, hσ, -⟩ := cfSig_over G cs (lA rad a.1 tl L) (sA rad a.1 tl L)
    (smpAt cs (lA rad a.1 tl L) (sA rad a.1 tl L) smpT z) a.1 (strsOf Fr a.2)
    (k8_cfSig T z a.1 (strsOf Fr a.2) hnc)
  exact ⟨tl, L, F, σ0, ⟨ht, hL, hσ⟩, hF, hfr, hN, T, hseat, hC, hnc⟩

/-- The law's premise on the early cells. -/
theorem early_cells (z : Pp) (s : S) {tl : HTailF2} {L : LinkCtx} {F : Fork}
    (l : List (OracleShape × ℕ)) (seat' : Fin l.length → ℕ × ℕ) (ht : s.tl? = some tl)
    (hL : s.link? = some L) (hF : s.fork? = some F) {p₀ : Par}
    (hN : Named.namedB p₀ s.st s.book tl L = true)
    (hC : ∀ t r c o, early tl (.cell t r c) = true → Named.msgNow L t = some o →
      CellsIn cs l seat' ms N m s t o)
    (w : Wit Cells Tok MsgT) (t r c : ℕ) (he : early tl (.cell t r c) = true) :
    entOfMsgs Cells Tok cs l seat' arr ms N m z s (msgsOf cs l seat' arr w) t r c =
      cellsAhead cs arr ms N m (z, s) w t r c := by
  obtain ⟨o, ho⟩ := msgNow_of_named hN he
  rw [cellsAhead_sent cs arr ms N m z s w hL hF ht ho r c]
  exact entOfMsgs_eq cs l seat' arr ms N m z s hL hF ht
    (fun t r c he => by
      obtain ⟨o, ho⟩ := msgNow_of_named hN he
      exact ⟨o, ho, hC t r c o he ho⟩) w t r c he

/-- **The law, at the letters off the statement in front.** -/
theorem owes_law (H : K8Fill G cs arr smpT ms N Mg links ps Rch k m pc q p rad oS) (z : Pp)
    (a₀ : S × Fr.E.Str) (ha : onQ N Mg links ps (fun s => (z, s)) k a₀)
    (hr : Rch k ((z, a₀.1), a₀.2)) (hm : ¬ a₀.1.failed ≠ none) (B' : Block S Claim)
    (hB : B'.Narrows (whole p)) :
    (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece (Run.ckP .two) Fr S Claim (Wit Cells Tok MsgT)).GoodIn
      (oA G cs arr smpT ms N m q p rad z a₀) (oB G cs arr smpT ms N m q p rad z a₀)
      (rA G cs arr smpT ms N m rad z a₀) (rB G cs arr smpT ms N m rad z a₀) := by
  obtain ⟨tl, L, F, σ0, hLt, hF, hfr, hN, T, hseat, hC, hnc⟩ := H.letters z a₀ ha hr hm
  obtain ⟨tl₁, ht₁, -, -, hgt, hu⟩ := cond_of_front hfr
  obtain rfl : tl = tl₁ := Option.some.inj (hLt.1.symm.trans ht₁)
  refine goodIn_where_or_refuses _ (PlaceRec p.toPar tl) _ _ _ _ (fun hP => ?_)
    (fun hP a τ b hoa hb => ?_)
  · rw [H.piece B']
    refine goodIn_whole_plain p q.base [rdt p.toPar] [] _ _ _ _ _ ?_ B' hB
    refine goodIn_weaken _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_
      (k08_goodInT_cap_whole tl cs (lA rad a₀.1 tl L) (sA rad a₀.1 tl L) arr
        (entOfMsgs Cells Tok cs (lA rad a₀.1 tl L) (sA rad a₀.1 tl L) arr ms N m z a₀.1)
        (cellsAhead cs arr ms N m (z, a₀.1)) G (smpA cs smpT rad z a₀ tl L σ0)
        (smpA_put H z a₀ tl L σ0) Fr p q.base hseat
        (early_cells z a₀.1 _ _ hLt.1 hLt.2.1 hF hN hC) hgt hu hP H.tau)
    · rintro a ⟨tl', L', σ0', hLt', -, hs', hseat', h⟩
      obtain ⟨rfl, rfl, rfl⟩ := hLt.one cs smpT rad hLt'
      exact h
    · intro b h
      exact ⟨tl, L, σ0, hLt, smpA_put H z a₀ tl L σ0, hseat, h⟩
    · rintro b w ⟨tl', L', σ0', hLt', h⟩
      obtain ⟨rfl, rfl, rfl⟩ := hLt.one cs smpT rad hLt'
      exact h
    · intro a w h
      exact ⟨tl, L, σ0, hLt, h⟩
  · obtain ⟨_, _, _, _, rfl, _⟩ := hoa
    obtain ⟨rs, gs, hd⟩ := whole_yes p
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (Run.ckP .two) Fr S Claim (Wit Cells Tok MsgT)) B' hB rfl _ b τ hb
    exact hP (placeRec_of_decide p.toPar tl _ _ rs gs hLt.1 hd)

/-- **The first tie.** -/
theorem owes_t1 (H : K8Fill G cs arr smpT ms N Mg links ps Rch k m pc q p rad oS) (z : Pp)
    (a : S × Fr.E.Str) (ha : onQ N Mg links ps (fun s => (z, s)) k a)
    (hr : Rch k ((z, a.1), a.2)) (hm : ¬ a.1.failed ≠ none) :
    oA G cs arr smpT ms N m q p rad z a a := by
  obtain ⟨tl, L, F, σ0, hLt, hF, hfr, hN, T, hseat, hC, hnc⟩ := H.letters z a ha hr hm
  obtain ⟨tl₁, ht₁, -, hX, -, -⟩ := cond_of_front hfr
  exact ⟨tl, L, σ0, hLt, rfl, smpA_put H z a tl L σ0, hseat,
    (tab_onA tl cs (lA rad a.1 tl L) (sA rad a.1 tl L) arr _ _ G _ (smpA_put H z a tl L σ0) Claim
      Fr p.toPar q.base _ hseat a).2 ⟨k8_cf σ0 T z a hnc, sameLay_own hLt.1⟩, hX⟩

/-- **The third tie.** -/
theorem owes_t3 (H : K8Fill G cs arr smpT ms N Mg links ps Rch k m pc q p rad oS) (z : Pp)
    (a b : S × Fr.E.Str) (w : Wit Cells Tok MsgT)
    (ha : onQ N Mg links ps (fun s => (z, s)) k a) (hr : Rch k ((z, a.1), a.2))
    (hm : ¬ a.1.failed ≠ none)
    (hy : ∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS p.toPar).decide a.1 rs gs = .ok b.1)
    (hO : relAt (meansQ N Mg fun s => (z, s)) (outsQ links ps k) b w) :
    rB G cs arr smpT ms N m rad z a b w := by
  obtain ⟨tl, L, F, σ0, hLt, hF, hfr, hN, T, hseat, hC, hnc⟩ := H.letters z a ha hr hm
  have mem : ∀ i, i ∈ (rowQ links ps k).outs ++ (rowQ links ps k).ctx →
      meansQ N Mg (fun s => (z, s)) i b w :=
    fun i hi => hO i (List.mem_append_left _ hi)
  rw [H.outs, H.ctx] at mem
  have hp : ∀ t ∈ [0, 1], ∀ e ∈ N.sent m t,
      pinJT cs G arr smpT ms e.1 e.2 (z, b.1) (strsOf Fr b.2) w := by
    intro t ht' e he
    have h01 : t = 0 ∨ t = 1 := by simpa using ht'
    rcases h01 with rfl | rfl
    · exact H.pin _ _ _ _ _ (mem (.pin m 0) (by simp) e he)
    · exact H.pin _ _ _ _ _ (mem (.pin m 1) (by simp) e he)
  obtain ⟨hS, hD⟩ := H.opens z a b w ha hr hm hy (mem (.forms m pc "small") (by simp))
    (mem (.constr m .lookDigits) (by simp))
  obtain ⟨rs, gs, hd⟩ := hy
  have e := cellsAhead_hear cs arr ms N m z p.toPar a.1 b.1 rs gs hd w
  refine ⟨tl, L, σ0, hLt, k8_pins arr σ0 T z b w hp, ?_, ?_⟩
  · obtain ⟨t', h1, h2⟩ := hS
    exact ⟨t', h1, by rw [← e]; exact h2⟩
  · obtain ⟨t', h1, h2⟩ := hD
    exact ⟨t', h1, by rw [← e]; exact h2⟩

/-- **The fourth tie.** -/
theorem owes_t4 (H : K8Fill G cs arr smpT ms N Mg links ps Rch k m pc q p rad oS) (z : Pp)
    (a : S × Fr.E.Str) (w : Wit Cells Tok MsgT)
    (ha : onQ N Mg links ps (fun s => (z, s)) k a) (hr : Rch k ((z, a.1), a.2))
    (hm : ¬ a.1.failed ≠ none) (hR : rA G cs arr smpT ms N m rad z a a w) :
    ∀ i ∈ (rowQ links ps k).ins, meansQ N Mg (fun s => (z, s)) i a w := by
  intro i hi
  obtain ⟨tl, L, F, σ0, hLt, hF, hfr, hN, T, hseat, hC, hnc⟩ := H.letters z a ha hr hm
  obtain ⟨tl₁, ht₁, -, -, hgt, hu⟩ := cond_of_front hfr
  obtain rfl : tl = tl₁ := Option.some.inj (hLt.1.symm.trans ht₁)
  obtain ⟨_, _, _, _, _, hT⟩ := hR
  obtain ⟨h1, h2⟩ := H.closes z a w ha hr hm
    ((tieAt_ahead_iff cs arr ms N m z a.1 hLt.2.1 hF hLt.1 hN hgt hu w).1 hT)
  rw [H.ins] at hi
  have h01 : i = .constr m .small ∨ i = .tie m := by simpa using hi
  rcases h01 with rfl | rfl
  · exact h1
  · exact h2

/-- **WHAT IS OWED AT ONE PLACE OF THE KIND.** -/
theorem k08_owesR (H : K8Fill G cs arr smpT ms N Mg links ps Rch k m pc q p rad oS) :
    K8OwesR N Mg links ps Rch k q p :=
  ⟨oA G cs arr smpT ms N m q p rad, oB G cs arr smpT ms N m q p rad,
    rA G cs arr smpT ms N m rad, rB G cs arr smpT ms N m rad, oS,
    fun z a b ha hr hm hy _ => H.makes z a b ha hr hm hy, H.blind,
    fun z a₀ ha hr hm B' hB => owes_law H z a₀ ha hr hm B' hB,
    fun z a ha hr hm => owes_t1 H z a ha hr hm,
    fun z a b w ha hr hm hy _ _ hO => owes_t3 H z a b w ha hr hm hy hO,
    fun z a _ w ha hr hm _ _ _ _ hR => owes_t4 H z a w ha hr hm hR⟩

end

end P1K8T

#print axioms P1K8T.owes_law
#print axioms P1K8T.owes_t1
#print axioms P1K8T.owes_t3
#print axioms P1K8T.owes_t4
#print axioms P1K8T.k08_owesR
