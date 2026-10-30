-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/HeadFold.lean: at the output head's link: where the list of tables is what the
verifier's routine makes of its fifteen lines, each of the head's five declared reads is whole, its
parts fit the record, and its tables are laid part by part; and what is then left of the row at the
head.

What is shown is a step of the row at the head: it speaks of the kind's written declarations, at
letters, against the list of lines `asksH` of Johnson/Road/HeadReads.lean, which is the list in the
routine `Head.tablesOf` (OnBytes/Model/HeadTables.lean).
  `askOf`: the line of that list under which a read of the head's is laid: wideAtKeys "hf@Z",
    wideAtCosts "hf@phiZ", actAtLogits "hd@r_H", rowAtCosts "hr@phiC", rowCount "hr@rhoC".
  `FoldFits P s A t`: the premises, by name. The fold over the fifteen lines returns t; the letter
    funs is t's list; the record has the plan's eight matrices; a block has 2 ^ 16 rows; the seat
    has the parts of wide, and act and row in one part each, where the list has them; the seat's
    first entries and lengths are those of t's table of tables; and the weights' tie: the array of
    each line reads, below the run's length, as the weights that the kind declares.
  `five_of_fold`: under `NumH`, `SeatFits` and `FoldFits`: `Whole`, `PartsFit` and `PartsLaid` of
    each of the five.
  `head_of_fold`: so `HeadClaimW P` (Reads/HeadWeights.lean) follows from `P.Sane` and, at every
    state with closed tables: the test on lengths, `SeatFits`, `FoldFits`, a row of U3 with an
    entry, one C, and one stretch in the two requests.
  Tools. `decl_ext`: two declarations with the same eight fields are one. `one_of_fold`: one read.

Of OnBytes/Model/ this file names the records `Head.Heard`, `Head.Tables`, `Head.Border`, the list
`Head.matsH`, and the makers of arrays `longPhi` and `eqTab`; through Johnson/Road/HeadReads.lean
the routine `Head.addFun`.

Limits. `FoldFits` is shown of no description and met by no letters here. Its last clause, the
weights' tie, is the hard one: it compares what a verifier's routine makes of what was heard with
what the kind declares. The full size alone. Four forms of 35. Nothing on soundness.


-/
import Johnson.Desc.Reads.FoldLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads

open OnBytes (E)

/-- Two declarations with the same eight fields are one. -/
theorem decl_ext {d d' : ReadDecl E} (h1 : d.name = d'.name) (h2 : d.mat = d'.mat)
    (h3 : d.parts = d'.parts) (h4 : d.make = d'.make) (h5 : d.len = d'.len)
    (h6 : d.count = d'.count) (h7 : d.start = d'.start) (h8 : d.w = d'.w) : d = d' := by
  cases d
  cases d'
  simp_all

end VerifiableInference.Reads

namespace VerifiableInference.Reads.AtHead

open Cb.Pv.Tail
open OnBytes (E zeroE)
open OnBytes.Model (longPhi eqTab)
open OnBytes.Model.Head (Heard HL Border Tables matsH)
open OnBytes.Road.Hd (NumH Ask addAsk Uni asksH matsH_at uni_one mem_drop)
open VerifiableInference.Desc.Kinds
open Inst.Model.Head (nT)

variable {K : Type} [CommRing K]

/-- One read, from a fold of lines. -/
theorem one_of_fold (P : HeadLetters K) (s : P.State) {asks : List Ask} {t : Tables}
    (hU : ∀ a ∈ asks, ∃ m k, Uni (P.tl s).mats a m k)
    (hf : asks.foldlM (addAsk (P.tl s).mats) {} = some t) (hfuns : P.funs s = t.funs)
    (r : Head.Read) {a : Ask} (ha : a ∈ asks) {m k : ℕ} (hUa : Uni (P.tl s).mats a m k)
    (hp : 0 < a.2.1) (hNM : a.1 + a.2.1 ≤ (P.tl s).NM)
    (hseat : ∀ tb len, (a.2.2.2.2, tb, len) ∈ t.tab →
      P.seat.start r = tb ∧ P.seat.count r = len)
    (hmat : (P.decl s r).mat = a.1) (hparts : (P.decl s r).parts = a.2.1)
    (hlen : (P.decl s r).len = a.2.2.1) (hpos : 0 < a.2.2.1)
    (hfits : (P.decl s r).make.Fits a.2.2.1 m)
    (hw : ∀ j, j < a.2.2.1 → P.val (a.2.2.2.1.getD j zeroE) = P.val ((P.decl s r).w j)) :
    (P.decl s r).Whole ((P.letters.size () s).m (P.decl s r).mat)
        ((P.letters.size () s).k (P.decl s r).mat) ∧
      PartsFit (P.letters.size () s) (P.decl s r) ∧
      PartsLaid (P.letters.size () s) (P.letters.phi () s) P.val (P.decl s r) := by
  obtain ⟨tb, hmem, hall⟩ := laid_of_fold (P.tl s) P.val hU hf ha hUa hp hNM
  obtain ⟨hst, hct⟩ := hseat tb _ hmem
  obtain ⟨l1, l2, l3⟩ := hall (P.decl s r).make (P.decl s r).w hw
  have hD : P.decl s r =
      { declOfAsk a (P.decl s r).make tb m k (P.decl s r).w with name := (P.decl s r).name } :=
    decl_ext rfl hmat hparts rfl hlen hct hst rfl
  have hsz : P.letters.size () s = sizeU3 (P.tl s) t.funs := by
    show sizeU3 (P.tl s) (P.funs s) = _
    rw [hfuns]
  have hph : P.letters.phi () s = phiU3 P.val t.funs := by
    show phiU3 P.val (P.funs s) = _
    rw [hfuns]
  have hm0 : (sizeU3 (P.tl s) t.funs).m a.1 = m := by
    have h := (hUa 0 hp).1
    rw [Nat.add_zero] at h
    exact h
  have hf' : (P.decl s r).make.Fits a.2.2.1 ((sizeU3 (P.tl s) t.funs).m a.1) := by
    rw [hm0]
    exact hfits
  rw [hsz, hph, hD]
  exact ⟨⟨hpos, l3, hf'⟩, l2, l1⟩

/-- What the routine computes on the way to its list of lines. -/
structure HeadAsks where
  x : Heard
  (ZV YN phiC rhoCv : Array E)
  (qFC qROW : ℕ)
  (b0 b1 : Array E)

/-- The fifteen lines. -/
def HeadAsks.list (A : HeadAsks) (h : OnBytes.Model.Head.Shape) (L : HL) : List Ask :=
  asksH h L A.x A.ZV A.YN A.phiC A.rhoCv A.qFC A.qROW A.b0 A.b1

/-- The line under which a read of the head's is laid. -/
def askOf (A : HeadAsks) (h : OnBytes.Model.Head.Shape) : Head.Read → Ask
  | .wideAtKeys => (0, h.NHf, 2 ^ h.la, longPhi A.x.Zl h.ls h.lt, "hf@Z")
  | .wideAtCosts =>
    (0, h.NHf, 2 ^ h.la, (Array.range (2 ^ h.la)).map fun i => A.phiC.getD (i % h.T) zeroE,
      "hf@phiZ")
  | .actAtLogits => (h.NHf, 1, h.T, eqTab A.x.tH.r, "hd@r_H")
  | .rowAtCosts => (h.NHf + 1, 1, h.T, A.phiC, "hr@phiC")
  | .rowCount => (h.NHf + 1, 1, h.T, A.rhoCv, "hr@rhoC")

/-- The premises on the list of tables, the record and the seat, by name. -/
structure FoldFits (P : HeadLetters K) (s : P.State) (A : HeadAsks) (t : Tables) : Prop where
  /-- the fold over the fifteen lines returns t, and the letter funs is its list -/
  fold : (A.list P.h P.L).foldlM (addAsk (P.tl s).mats) {} = some t
  funs : P.funs s = t.funs
  /-- the record has the plan's eight matrices -/
  mats : ∃ b gid sid, (P.tl s).mats = matsH P.h P.L b gid sid
  NM : (P.tl s).NM = 8
  /-- a block has 2 ^ 16 rows -/
  la : P.h.la = 16
  /-- the seat has the matrices where the list has them -/
  wideParts : (P.seat.mat .wide).2 = P.h.NHf
  act : P.seat.mat .act = (P.h.NHf, 1)
  rowParts : (P.seat.mat .row).2 = 1
  /-- the seat's first entries and lengths are those of the table of tables -/
  seat : ∀ r tb len, ((askOf A P.h r).2.2.2.2, tb, len) ∈ t.tab →
    P.seat.start r = tb ∧ P.seat.count r = len
  /-- the weights' tie -/
  weights : ∀ r j, j < (askOf A P.h r).2.2.1 →
    P.val ((askOf A P.h r).2.2.2.1.getD j zeroE) = P.val ((P.decl s r).w j)

/-- **The five, from the fold over the fifteen lines.** -/
theorem five_of_fold (P : HeadLetters K) (s : P.State) (hN : NumH P.h P.L) (hF : SeatFits P s)
    {A : HeadAsks} {t : Tables} (Z : FoldFits P s A t) :
    ∀ d ∈ P.decls s,
      d.Whole ((P.letters.size () s).m d.mat) ((P.letters.size () s).k d.mat) ∧
      PartsFit (P.letters.size () s) d ∧
      PartsLaid (P.letters.size () s) (P.letters.phi () s) P.val d := by
  obtain ⟨b, gid, sid, hm⟩ := Z.mats
  obtain ⟨-, zf, zD1, zD2, zR1, zR2, -, -⟩ := matsH_at P.L b gid sid hN.NHf
  rw [← hm] at zf zD1 zD2 zR1 zR2
  have h4 := hN.NHf
  have h8 := Z.NM
  have uF : ∀ (phi : Array E) (nm : String),
      Uni (P.tl s).mats (0, P.h.NHf, 2 ^ P.h.la, phi, nm) P.L.m P.L.k := by
    intro phi nm q hq
    have hq' : q < 4 := by
      have h0 : q < P.h.NHf := hq
      rw [h4] at h0
      exact h0
    have e := zf q hq'
    rw [← Nat.zero_add q] at e
    exact e
  have uD : ∀ (phi : Array E) (nm : String),
      Uni (P.tl s).mats (P.h.NHf, 1, P.h.T, phi, nm) P.L.mD P.L.kD := by
    intro phi nm q hq
    have e : q = 0 := by
      have h0 : q < 1 := hq
      omega
    subst e
    show ((P.tl s).mats.getD (P.h.NHf + 0) {}).m = _ ∧ ((P.tl s).mats.getD (P.h.NHf + 0) {}).k = _
    rw [h4]
    exact ⟨zD1, zD2⟩
  have uR : ∀ (phi : Array E) (nm : String),
      Uni (P.tl s).mats (P.h.NHf + 1, 1, P.h.T, phi, nm) P.L.mR P.L.kR := by
    intro phi nm q hq
    have e : q = 0 := by
      have h0 : q < 1 := hq
      omega
    subst e
    show ((P.tl s).mats.getD (P.h.NHf + 1 + 0) {}).m = _ ∧
      ((P.tl s).mats.getD (P.h.NHf + 1 + 0) {}).k = _
    rw [h4]
    exact ⟨zR1, zR2⟩
  have hU : ∀ a ∈ A.list P.h P.L, ∃ m k, Uni (P.tl s).mats a m k := by
    intro a ha
    unfold HeadAsks.list asksH at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    · exact ⟨_, _, uF _ _⟩
    · exact ⟨_, _, uF _ _⟩
    all_goals exact ⟨_, _, uni_one _ _ rfl⟩
  have hlong : (letI := P.sizes; Norm.S2 * Norm.T) = 2 ^ P.h.la :=
    (congrArg₂ (· * ·) hF.S2 hF.T).trans (by rw [Z.la]; decide)
  have hshort : (letI := P.sizes; Norm.T) = P.h.T := hF.T.trans hN.T.symm
  have hposL : 0 < 2 ^ P.h.la := Nat.two_pow_pos _
  have hposT : 0 < P.h.T := by
    rw [hN.T]
    decide
  have hfitL : ∀ r, (P.decl s r).make = .long (letI := P.sizes; Norm.S2) →
      (P.decl s r).make.Fits (2 ^ P.h.la) P.L.m := by
    intro r hr
    rw [hr, hF.S2, Z.la, hN.m]
    exact ⟨by decide, by decide⟩
  intro d hd
  obtain ⟨r, -, rfl⟩ := List.mem_map.1 hd
  cases r
  · exact one_of_fold P s hU Z.fold Z.funs .wideAtKeys (a := askOf A P.h .wideAtKeys)
      (mem_drop 0 _ rfl) (uF _ _) (by show 0 < P.h.NHf; omega)
      (by show 0 + P.h.NHf ≤ (P.tl s).NM; omega) (Z.seat .wideAtKeys) hF.wide Z.wideParts hlong
      hposL (hfitL _ rfl) (Z.weights .wideAtKeys)
  · exact one_of_fold P s hU Z.fold Z.funs .wideAtCosts (a := askOf A P.h .wideAtCosts)
      (mem_drop 1 _ rfl) (uF _ _) (by show 0 < P.h.NHf; omega)
      (by show 0 + P.h.NHf ≤ (P.tl s).NM; omega) (Z.seat .wideAtCosts) hF.wide Z.wideParts hlong
      hposL (hfitL _ rfl) (Z.weights .wideAtCosts)
  · exact one_of_fold P s hU Z.fold Z.funs .actAtLogits (a := askOf A P.h .actAtLogits)
      (mem_drop 5 _ rfl) (uD _ _) Nat.one_pos
      (by show P.h.NHf + 1 ≤ (P.tl s).NM; omega) (Z.seat .actAtLogits)
      (congrArg Prod.fst Z.act) (congrArg Prod.snd Z.act) hshort hposT True.intro
      (Z.weights .actAtLogits)
  · exact one_of_fold P s hU Z.fold Z.funs .rowAtCosts (a := askOf A P.h .rowAtCosts)
      (mem_drop 10 _ rfl) (uR _ _) Nat.one_pos
      (by show P.h.NHf + 1 + 1 ≤ (P.tl s).NM; omega) (Z.seat .rowAtCosts) hF.row Z.rowParts
      hshort hposT True.intro (Z.weights .rowAtCosts)
  · exact one_of_fold P s hU Z.fold Z.funs .rowCount (a := askOf A P.h .rowCount)
      (mem_drop 11 _ rfl) (uR _ _) Nat.one_pos
      (by show P.h.NHf + 1 + 1 ≤ (P.tl s).NM; omega) (Z.seat .rowCount) hF.row Z.rowParts
      hshort hposT True.intro (Z.weights .rowCount)

/-- **What is left of the row at the head, where the list is the routine's.** -/
theorem head_of_fold (P : HeadLetters K) (hS : P.Sane)
    (h : ∀ s, P.AtClose s →
      lensB (P.funs s) = true ∧ SeatFits P s ∧ (∃ A t, FoldFits P s A t) ∧ 0 < P.seat.cols ∧
      ((P.req s).pol.C : K) = (P.policy.C : K) ∧
      (P.req s).r = (P.request s).r ∧ (P.req s).e = (P.request s).e) :
    HeadClaimW P :=
  head_w_of_laid P hS
    (fun s hs => by
      obtain ⟨a, b, ⟨A, t, Z⟩, c, d, -, -⟩ := h s hs
      exact ⟨a, five_of_fold P s hS.2.1 b Z, b, c, d⟩)
    fun s hs => ⟨(h s hs).2.2.2.2.2.1, (h s hs).2.2.2.2.2.2⟩

end VerifiableInference.Reads.AtHead

#print axioms VerifiableInference.Reads.decl_ext
#print axioms VerifiableInference.Reads.AtHead.one_of_fold
#print axioms VerifiableInference.Reads.AtHead.five_of_fold
#print axioms VerifiableInference.Reads.AtHead.head_of_fold
