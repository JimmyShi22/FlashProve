-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyRow21.lean: ROW 2.1 OF THE KEY FILE's TABLE OF JOINTS (the
shared chain's block «LIN point»; borders 1 → 2): THE CHANCE's HALF, at the tables' own
letters (Johnson/RunOne/KeyRows23At.lean: on₂ | R₂ | L₂).

ON EMPTINESS: IT IS NOT SHOWN THAT ANY RECORD, READING AND ORACLES EXIST AT WHICH on₂ … 1 HOLDS, NOR
A WITNESS AT WHICH R₂ … 2 HOLDS; AND TWO PREMISES HERE ARE WHOLE LAWS ON LETTERS (KeyGood ·
PileOfEval): NO MEMBER OF THEM IS SHOWN. UNTIL A MEMBER IS SHOWN AT F_K's OWN LETTERS, EVERY LAW
THAT HAS PIN AS AN ITEM OR NoColl IN ITS PROMISE MAY BE TRUE AND EMPTY AT THE REAL PROTOCOL, AND
COUNTS AS CLOSING NOTHING.
OBJECT: a piece pc at the record P₂ × St₂ whose block decides by K14's own text «linPoint» on the
second component and leaves the first (hl): meant: the maker's piece number 1 of the shared chain.
USER: the tables' files' keeps₂_of_halves' (KeyHalves23.lean; row 2.1 has row 2.4's form:
«Leads (on₂ … 1)
(fun a b => L₂ … 2 b → L₂ … 1 a) pc.err»), then the field r2_1 of The21.
LETTERS: the tables'; S is p.S; THIS FILE's OWN BESIDE: K ρ · BadKey (the
key's bad points: IT READS THE STATEMENT IN FRONT, so the stored table's RECORD too) · ef c · G.
THE MAP ON WITNESSES IS NOT THE IDENTITY (the row has laysCells): layCells: the cells are laid to
what the stored table decodes to, with the record, off the statement in front.
  cellsAt | layCells | tabK | gK | vK   the letters of point_core
    (Johnson/Desc/K14/Law/PointCore.lean), filled off the tables' own readers
  Front₂₁          what stands in front beside «V is the row weights applied to the matrix»: pinT ·
    pin 0 · srow 0 · pin 2 · srow 2 · «Eval»
  KeyGood          A NAMED PREMISE, A LAW ON LETTERS: off BadKey: «NearU» and «RecRow» at a vector
    u give that the stored table decodes with its record and that u reads as the fold at gamma of
    the rows that it decodes to. MEANT PAYER: K14's files: good_of_notBad2
    (Johnson/Desc/K14/Law/PointKey2.lean) with two translations and a tie of decT | KRead.tab to the
    library's decoder
  PileOfEval       A NAMED PREMISE, FOR CERTAIN: «Eval» and «V = gᵀM» give the pile. MEANT PAYER:
    K14's files with the tables': K13's eval_back (Johnson/Desc/K13/Law/Eval.lean) and the bridge
    tensorRowHolds_iff_k13
  point_step       PROVED: at a yes, off BadKey: Front₂₁ at the laid witness, and (Dot)'s equation
    with the matrix itself at the point drawn (dotTrue_of)
  point_back₂      **THE CHANCE's HALF**
PREMISES, AND, OF EACH THAT IS A BARE «∀», WHY AN INSTANCE THAT IS NOT DEGENERATE EXISTS:
hl [bare ∀, under the block's yes]: K14's files: b1.decide is «why (linPoint p
d rs)» (point_of_blocks); seat_decide is rfl; held_decide · hbase: the frame's numbers · hsame [bare
∀]: R.same := «ρ x = ρ y» is the meant filling · hpins [BARE ∀ z z', under three equations and no
yes]: BaseSt.h₂ meets it at every pair (as at row 2.4) · hof [BARE ∀ w c k]: A CONDITION ON
KRead.of: it reads no cells: the meant filling (msgOf G w at message k's seat: ReadsPinned) reads
msg | pad alone · fits [∀ x]: the written round's (vecMaps, as in point_goodIn: NOT YET CALLED HERE)
· hkey | hgood | hpile | hread: EACH UNDER on₂ … 1 IN FRONT.

KeyGood | PileOfEval have the block's own test on the
public shape at hand (linOk: linPoint_ok). WHAT IS SPENT OF THE PROMISE IN FRONT: Free₂.key · reads
at 2 · NoColl at 2.
Nothing on soundness by itself.
-/
import Johnson.RunOne.KeyRow24
import Johnson.Desc.K14.Law.PointCore
import Johnson.Desc.K14.Law.ZetaWords
import Johnson.Desc.K14.Law.Condition

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat
open _root_.Run.PQ (CK)
open _root_.Iop (Reduction Err)
open _root_.Iop.IOR (drawRound)
open _root_.Prob (cnt)
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Plain
    VerifiableInference.Desc.Sound
open _root_.Desc.Plain (Par)
open _root_.Desc.K14.Law (point_core gamOf loOf drop_ofFn take_ofFn dotTrue_of UIsFold eqK
    linPoint_inv linPoint_ok)
open _root_.Prob (cnt_false)
open _root_.Desc.K14.Law.ZetaWords (val_sumE val_evalEq val_readU)

theorem open₂_at1 : open₂ 1 = [.unmarked, .pinT, .pin 0, .srow 0, .pile, .pin 2, .srow 2] :=
    by decide
theorem open₂_at2 : open₂ 2 = [.unmarked, .pin 0, .srow 0, .pin 2, .srow 2, .claim 1 "Eval", .claim
    2 "NearU", .claim 2 "RecRow", .claim 2 "DotU"] := by decide

section
variable {XI Cells M Smp Rec : Type} (F : FileDescription XI) (G₂ : Reading (P₂ × St₂) Cells M Smp Rec)
    (at_ : Where)
  (S : LinShape) (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (rad : Nat)

theorem recRow₁_is (u : P₂ × St₂) (y : Strs) (w : Wit Cells Unit M) :
    (KItem.claim 2 "RecRow").holds F G₂ at_ (meaning₂ S K₁ R enc rad) u y w ↔
      RecRowAt R.same (plan₂ S).lin.fold.index ((readers₂ S).key u) (((readers₂ S).psi u).drop
          (plan₂ S).lin.kLo)
        (uOf (plan₂ S) R ((readers₂ S).st u.2).codes w) := by
  simp [KItem.holds, meaning₂, claim₂]

end

/-- «NearU» reads of the strings the stored cells alone. -/
theorem nearU_cell (same : E → E → Prop) (logN e : Nat) (enc : (Nat → E) → Nat → E) (ga : List E) (y
    y' : Strs) (u : Nat → E)
    (h : y'.cell = y.cell) (hu : NearUAt same logN e enc ga y' u) : NearUAt same logN e enc ga y u
        := by
  unfold NearUAt at hu ⊢
  rw [h] at hu
  exact hu

/-! ## The letters of the core, filled -/

section
variable {Cells M Smp Rec : Type} (G₂ : Reading (P₂ × St₂) Cells M Smp Rec) (R : KRead Cells M)
variable {K : Type} [Field K] (ρ : Model.Reading K)

/-- What the stored table decodes to, with its record: off the statement. -/
def cellsAt (z : P₂ × St₂) (y : Strs) : Option Cells := (G₂.recOf z).bind (G₂.decT y.cell)

/-- **The map on witnesses**: the cells are laid. -/
def layCells (z : P₂ × St₂) (y : Strs) (w : Wit Cells Unit M) : Wit Cells Unit M :=
  match cellsAt G₂ z y with
  | some c => { w with cells := c }
  | none => w

theorem layCells_of (z : P₂ × St₂) (y : Strs) (w : Wit Cells Unit M) (c : Cells) (h : cellsAt G₂ z y
    = some c) :
    layCells G₂ z y w = { w with cells := c } := by
  unfold layCells
  rw [h]

theorem cellsAt_of_pinT (z : P₂ × St₂) (y : Strs) (w : Wit Cells Unit M) (h : PINW G₂ z y w) :
    cellsAt G₂ z y = some w.cells := by
  obtain ⟨r, h1, h2⟩ := h
  unfold cellsAt
  rw [h1]
  exact h2

/-- The table's row r, place k, read in the field; 0 where there is no table. -/
def tabK (o : Option Cells) (r k : Nat) : K :=
  match o with
  | some c => ρ.val (ofF (R.tab c r k))
  | none => 0

/-- The claim's row weights, off what was handed, read in the field. -/
def gK (S : LinShape) (z : P₂) (y : Nat) : K :=
  match (firstAt S z.2).map (·.g) with
  | some gs => ρ.val (weightAt gs y)
  | none => 0

/-- V's entries, off the witness, read in the field. -/
def vK (S : LinShape) (codes : Codes) (w : Wit Cells Unit M) (c : Nat) : K := ρ.val (vOf' (plan₂ S)
    R codes w c)

theorem valOf_lay (hof : ∀ (w : Wit Cells Unit M) c k, R.of { w with cells := c } k = R.of w k) (Kp
    : KPlan) (w : Wit Cells Unit M) (c : Cells) :
    valOf Kp R { w with cells := c } = valOf Kp R w := by
  funext o pt i
  unfold valOf
  cases Kp.num o with
  | none => rfl
  | some k => simp only [hof]

end

section
variable {XI Cells M Smp Rec : Type} (F : FileDescription XI) (G₂ : Reading (P₂ × St₂) Cells M Smp Rec)
    (at_ : Where)
  (p : Par) (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (rad : Nat)
variable {K : Type} [Field K] (ρ : Model.Reading K)

/-- What stands in front beside «V = gᵀM». -/
def Front₂₁ (z : P₂ × St₂) (y : Strs) (w : Wit Cells Unit M) : Prop :=
  PINW G₂ z y w ∧ (KItem.pin 0).holds F G₂ at_ (meaning₂ p.S K₁ R enc rad) z y w ∧ (KItem.srow
      0).holds F G₂ at_ (meaning₂ p.S K₁ R enc rad) z y w ∧
    (KItem.pin 2).holds F G₂ at_ (meaning₂ p.S K₁ R enc rad) z y w ∧ (KItem.srow 2).holds F G₂ at_
        (meaning₂ p.S K₁ R enc rad) z y w ∧
    (KItem.claim 1 "Eval").holds F G₂ at_ (meaning₂ p.S K₁ R enc rad) z y w

theorem srow₂_lay (hof : ∀ (w : Wit Cells Unit M) c k, R.of { w with cells := c } k = R.of w k) (k :
    Nat) (hk : k = 0 ∨ k = 2)
    (z : P₂) (d d' : St₂) (y y' : Strs) (w : Wit Cells Unit M) (c : Cells)
    (h : (meaning₂ p.S K₁ R enc rad).srow k (z, d') y' w) : (meaning₂ p.S K₁ R enc rad).srow k (z,
        d) y { w with cells := c } := by
  simp only [meaning₂, if_pos hk] at h ⊢
  unfold srowAt at h ⊢
  rw [valOf_lay R hof]
  exact h

/-- **At a yes, off the key's bad points.** -/
theorem point_step (hsame : ∀ x y, R.same x y ↔ ρ.val x = ρ.val y)
    (hof : ∀ (w : Wit Cells Unit M) c k, R.of { w with cells := c } k = R.of w k)
    (z : P₂) (d d' : St₂) (y y' : Strs) (w : Wit Cells Unit M) (psi : Fin (p.S.kLo +
        p.S.fold.index.v) → K)
    (hpsi : d'.loc.psiSh.map ρ.val = List.ofFn psi) (hco : d'.st.codes = d.st.codes) (HP : SamePins
        G₂ (z, d) (z, d'))
    (Hy : StrsStay F at_ (open₂ 1) y y') (cl : Cells) (hcl : cellsAt G₂ (z, d) y = some cl)
    (hU : UIsFold p.S.matrixRows p.S.kLo p.S.fold.index.v (tabK R ρ (some cl)) (List.ofFn (gamOf
        p.S.kLo p.S.fold.index.v psi))
      (fun k => ρ.val (uOf (plan₂ p.S) R d'.st.codes w k)))
    (hw : relAt F G₂ at_ (meaning₂ p.S K₁ R enc rad) (open₂ 2) (z, d') y' w) :
    Front₂₁ F G₂ at_ p K₁ R enc rad (z, d) y { w with cells := cl } ∧
      ∑ c ∈ Finset.range (2 ^ (p.S.kLo + p.S.fold.index.v)), eqK (List.ofFn psi) c * vK R ρ p.S
          d.st.codes { w with cells := cl } c =
        ∑ q ∈ Finset.range p.S.matrixRows, gK ρ p.S z q *
          ∑ c ∈ Finset.range (2 ^ (p.S.kLo + p.S.fold.index.v)), eqK (List.ofFn psi) c *
            _root_.Desc.K14.Law.matOf p.S.kLo (tabK R ρ (some cl)) q c := by
  have mem : ∀ j, j ∈ open₂ 2 → j.holds F G₂ at_ (meaning₂ p.S K₁ R enc rad) (z, d') y' w := hw
  have pin : ∀ k, k ∈ pinned (open₂ 1) → (KItem.pin k).holds F G₂ at_ (meaning₂ p.S K₁ R enc rad)
      (z, d') y' w →
      (KItem.pin k).holds F G₂ at_ (meaning₂ p.S K₁ R enc rad) (z, d) y { w with cells := cl } :=
    fun k hk hu => rides_pin2 F G₂ _ _ (z, d) (z, d') y y' w HP (Hy.word k hk) hu
  refine ⟨⟨?_, pin 0 (by decide) (mem _ (by decide)), srow₂_lay p K₁ R enc rad hof 0 (Or.inl rfl) z
      d d' y y' w cl (mem (.srow 0) (by decide)),
    pin 2 (by decide) (mem _ (by decide)), srow₂_lay p K₁ R enc rad hof 2 (Or.inr rfl) z d d' y y' w
        cl (mem (.srow 2) (by decide)), ?_⟩, ?_⟩
  · obtain ⟨r, h1, h2⟩ := Option.bind_eq_some_iff.1 hcl
    exact ⟨r, h1, h2⟩
  · have he := (eval₄_is F G₂ at_ p.S K₁ R enc rad (z, d') y' w).1 (mem _ (by decide))
    refine (eval₄_is F G₂ at_ p.S K₁ R enc rad (z, d) y _).2 ?_
    rw [valOf_lay R hof]
    exact he
  · obtain ⟨gs, hg, hd⟩ := (dotU₄_is F G₂ at_ p.S K₁ R enc rad (z, d') y' w).1 (mem _ (by decide))
    have hg' : (firstAt p.S z.2).map (·.g) = some gs := hg
    have hd' : R.same (sumE p.S.matrixRows fun q => mulE (weightAt gs q) (readU p.S d'.loc.psiSh
        (uOf (plan₂ p.S) R d'.st.codes w) q))
        (evalEq d'.loc.psiSh (2 ^ (p.S.kLo + p.S.fold.index.v)) (vOf' (plan₂ p.S) R d'.st.codes w))
            := hd
    have h1 := (hsame _ _).1 hd'
    rw [val_sumE, val_evalEq, hpsi] at h1
    have et : (d'.loc.psiSh.take p.S.kLo).map ρ.val = List.ofFn (loOf p.S.kLo p.S.fold.index.v psi)
        := by
      rw [List.map_take, hpsi]
      exact take_ofFn p.S.kLo p.S.fold.index.v psi
    have eapp : List.ofFn (loOf p.S.kLo p.S.fold.index.v psi) ++ List.ofFn (gamOf p.S.kLo
        p.S.fold.index.v psi) = List.ofFn psi := by
      rw [← take_ofFn, ← drop_ofFn]
      exact List.take_append_drop _ _
    have h2 : ∑ q ∈ Finset.range p.S.matrixRows, ρ.val (weightAt gs q) * ∑ t ∈ Finset.range (2 ^
        p.S.kLo),
        eqK (List.ofFn (loOf p.S.kLo p.S.fold.index.v psi)) t * ρ.val (uOf (plan₂ p.S) R d'.st.codes
            w (t + 2 ^ p.S.kLo * q)) =
        ∑ c ∈ Finset.range (2 ^ (p.S.kLo + p.S.fold.index.v)),
          eqK (List.ofFn (loOf p.S.kLo p.S.fold.index.v psi) ++ List.ofFn (gamOf p.S.kLo
              p.S.fold.index.v psi)) c * ρ.val (vOf' (plan₂ p.S) R d'.st.codes w c) := by
      rw [eapp, ← h1]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [ρ.mul, val_readU, et]
    have h3 := dotTrue_of p.S.matrixRows p.S.kLo p.S.fold.index.v (tabK R ρ (some cl)) _ _ (fun q =>
        ρ.val (weightAt gs q))
      (fun k => ρ.val (uOf (plan₂ p.S) R d'.st.codes w k)) (fun c => ρ.val (vOf' (plan₂ p.S) R
          d'.st.codes w c)) (by simp) hU h2
    rw [eapp] at h3
    have ev : ∀ c, vK R ρ p.S d.st.codes { w with cells := cl } c = ρ.val (vOf' (plan₂ p.S) R
        d'.st.codes w c) := fun c => by
      unfold vK vOf'
      rw [hof, hco]
    have eg : ∀ q, gK ρ p.S z q = ρ.val (weightAt gs q) := fun q => by
      unfold gK
      rw [hg']
    simp only [ev, eg]
    exact h3

end

/-! ## The chance's half -/

/-- A piece at another type of witnesses and another extractor: the reduction and the errors are the
piece's own. -/
abbrev extPiece {C : CK} {Fr : Frame} {S Cl W : Type} (W' : Type) (pc : Piece C Fr S Cl W)
    (ext : S × Fr.E.Str → _root_.Iop.Tr (uLT C pc.ds) → W' → W') : Piece C Fr S Cl W' :=
  ⟨pc.b, pc.base, pc.ds, pc.back, ext, pc.err⟩

section
variable {XI Cells M Smp Rec Cl W : Type} {C : CK} (F : FileDescription XI) (Fr₂ : Frame)
  (G₂ : Reading (P₂ × St₂) Cells M Smp Rec) (at_ : Where)
  (p : Par) (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (rad a : Nat)
  (coll : Strs → Rec → Prop) (last₁ : FirstState → Bool) (off₂ : Nat → Nat)
variable {K : Type} [Field K] (ρ : Model.Reading K)

/-- **A NAMED PREMISE, A LAW ON LETTERS**: off the key's bad points «NearU» and «RecRow» give that
the stored table decodes, and that the vector reads as the fold of what it decodes to. UNDER THE
PROMISE IN FRONT AND THE BLOCK's OWN TEST ON THE PUBLIC SHAPE (linOk: a yes of «LIN point» holds
it). -/
def KeyGood (BadKey : (P₂ × St₂) × Fr₂.E.Str → (Fin p.S.fold.index.v → K) → Prop) : Prop :=
  ∀ (x : (P₂ × St₂) × Fr₂.E.Str) (gam : Fin p.S.fold.index.v → K) (ga : List E) (u : Nat → E),
    on₂ F Fr₂ G₂ at_ p.S K₁ R enc rad a coll last₁ off₂ 1 x → linOk x.1.2.st.codes p.S = true → ¬
        BadKey x gam → ga.map ρ.val = List.ofFn gam →
    NearUAt R.same p.S.fold.index.code.logN rad enc ga (strsOf Fr₂ x.2) u → RecRowAt R.same
        p.S.fold.index x.1.1.1.key ga u →
    ∃ c, cellsAt G₂ x.1 (strsOf Fr₂ x.2) = some c ∧
      UIsFold p.S.matrixRows p.S.kLo p.S.fold.index.v (tabK R ρ (some c)) (List.ofFn gam) fun k =>
          ρ.val (u k)

/-- **A NAMED PREMISE, FOR CERTAIN**: «Eval» and «V is the row weights applied to the matrix in
the witness's cells» give the pile. UNDER THE PROMISE IN FRONT AND THE BLOCK's OWN TEST ON THE
PUBLIC SHAPE. -/
def PileOfEval : Prop :=
  ∀ (x : (P₂ × St₂) × Fr₂.E.Str) (w : Wit Cells Unit M), on₂ F Fr₂ G₂ at_ p.S K₁ R enc rad a coll
      last₁ off₂ 1 x → linOk x.1.2.st.codes p.S = true →
    (KItem.claim 1 "Eval").holds F G₂ at_ (meaning₂ p.S K₁ R enc rad) x.1 (strsOf Fr₂ x.2) w →
    (∀ c < 2 ^ (p.S.kLo + p.S.fold.index.v), vK R ρ p.S x.1.2.st.codes w c =
      ∑ q ∈ Finset.range p.S.matrixRows, gK ρ p.S x.1.1 q * _root_.Desc.K14.Law.matOf p.S.kLo (tabK
          R ρ (some w.cells)) q c) →
    KItem.pile.holds F G₂ at_ (meaning₂ p.S K₁ R enc rad) x.1 (strsOf Fr₂ x.2) w

/-- **ROW 2.1, THE CHANCE's HALF.** -/
theorem point_back₂ [Fintype K] (pc : Piece C Fr₂ (P₂ × St₂) Cl W)
    (hl : ∀ z rs gs z', pc.b.decide z rs gs = .ok z' → z'.1 = z.1 ∧ _root_.Desc.K14.linPoint p z.2
        rs = some z'.2)
    (hbase : ∀ j ∈ pinned (open₂ 1), (at_ j).1 < pc.base)
    (hsame : ∀ x y, R.same x y ↔ ρ.val x = ρ.val y)
    (hpins : ∀ z z' : P₂ × St₂, z'.1 = z.1 → z'.2.st.oracles = z.2.st.oracles → z'.2.st.codes =
        z.2.st.codes → SamePins G₂ z z')
    (hof : ∀ (w : Wit Cells Unit M) c k, R.of { w with cells := c } k = R.of w k)
    (BadKey : (P₂ × St₂) × Fr₂.E.Str → (Fin p.S.fold.index.v → K) → Prop) (ef c : Nat)
    (hc : ef * Fintype.card K ^ p.S.kLo + (p.S.kLo + p.S.fold.index.v) * Fintype.card K ^ (p.S.kLo +
        p.S.fold.index.v - 1) ≤ c)
    (hkey : ∀ x, on₂ F Fr₂ G₂ at_ p.S K₁ R enc rad a coll last₁ off₂ 1 x → cnt (BadKey x) ≤ ef)
    (hgood : KeyGood F Fr₂ G₂ at_ p K₁ R enc rad a coll last₁ off₂ ρ BadKey)
    (hpile : PileOfEval F Fr₂ G₂ at_ p K₁ R enc rad a coll last₁ off₂ ρ)
    (G : (P₂ × St₂) × Fr₂.E.Str → CarryS (uLT C pc.ds) [drawRound (Fin (p.S.kLo + p.S.fold.index.v)
        → K)])
    (fits : ∀ x, (G x).Fits ((c, ()) : Nat × Unit) pc.err)
    (hread : ∀ x τ x', on₂ F Fr₂ G₂ at_ p.S K₁ R enc rad a coll last₁ off₂ 1 x → pc.ior.red.out x τ
        = some x' →
      ∃ psi, (G x).tr τ = some (((), ()), psi, ()) ∧ x'.1.2.loc.psiSh.map ρ.val = List.ofFn psi) :
    pc.ior.red.Leads (on₂ F Fr₂ G₂ at_ p.S K₁ R enc rad a coll last₁ off₂ 1)
      (fun x x' => L₂ F Fr₂ G₂ at_ p.S K₁ R enc rad 2 x' → L₂ F Fr₂ G₂ at_ p.S K₁ R enc rad 1 x)
          pc.err := by
  have arm : ∀ x, on₂ F Fr₂ G₂ at_ p.S K₁ R enc rad a coll last₁ off₂ 1 x →
      Free₂ F G₂ at_ p.S K₁ R coll last₁ off₂ 1 x.1 (strsOf Fr₂ x.2) ∧
        ∀ k ∈ pinned (open₂ 1), NoColl F G₂ (at_ k).1 (at_ k).2 x.1 (strsOf Fr₂ x.2) := fun x h =>
            by
    rcases h with hn | ⟨_, _, h3, h4⟩
    · exact absurd trivial hn
    · exact ⟨h3, h4⟩
  have core := point_core
    (extPiece (Wit Cells Unit M) pc fun x _ w => layCells G₂ x.1 (strsOf Fr₂ x.2) w)
    p.S.matrixRows p.S.kLo p.S.fold.index.v (fun x w => layCells G₂ x.1 (strsOf Fr₂ x.2) w) (fun _ _
        _ => rfl)
    (on₂ F Fr₂ G₂ at_ p.S K₁ R enc rad a coll last₁ off₂ 1) (fun _ => True)
    (fun x w => Front₂₁ F G₂ at_ p K₁ R enc rad x.1 (strsOf Fr₂ x.2) w) (R₂ F Fr₂ G₂ at_ p.S K₁ R
        enc rad 2)
    BadKey (fun _ _ => False)
    (fun x => gK ρ p.S x.1.1) (fun x => _root_.Desc.K14.Law.matOf p.S.kLo (tabK R ρ (cellsAt G₂ x.1
        (strsOf Fr₂ x.2))))
    (fun x w => vK R ρ p.S x.1.2.st.codes w) ef 0 c (by rw [Nat.zero_add]; exact hc) hkey
    (fun _ _ => Nat.le_of_eq (cnt_false fun _ h => h))
    (fun x w w' hx hp hp' => by
      obtain ⟨hf, hN⟩ := arm x hx
      have e := pin_one F G₂ _ _ x.1 _ w w' (hN 2 (by decide)) hp.2.2.2.1 hp'.2.2.2.1
      funext q
      show ρ.val (R.val (R.of w 2) .main _) = ρ.val (R.val (R.of w' 2) .main _)
      rw [hf.reads w 2 (by decide), hf.reads w' 2 (by decide), e])
    G fits
    (fun x τ x' hx hb => by
      obtain ⟨psi, htr, hpsi⟩ := hread x τ x' hx hb
      obtain ⟨e1, k1⟩ := hl _ _ _ _ (piece_decides_at (extPiece (Wit Cells Unit M) pc fun x _ w =>
          layCells G₂ x.1 (strsOf Fr₂ x.2) w) x τ x' hb)
      obtain ⟨_, _, _, hkeyE, hor, hco⟩ := linPoint_inv p _ _ _ k1
      have Hy := strsStay_of_out F Fr₂ at_ (extPiece (Wit Cells Unit M) pc fun x _ w => layCells G₂
          x.1 (strsOf Fr₂ x.2) w) (open₂ 1) hbase x x' τ hb
      obtain ⟨hf, _⟩ := arm x hx
      refine ⟨psi, htr, fun _ => trivial, fun hnk w hw => ?_⟩
      · have ex' : x'.1 = (x.1.1, x'.1.2) := Prod.ext e1 rfl
        have hw' : relAt F G₂ at_ (meaning₂ p.S K₁ R enc rad) (open₂ 2) (x.1.1, x'.1.2) (strsOf Fr₂
            x'.2) w := ex' ▸ hw
        have hN := nearU_cell _ _ _ _ _ _ _ _ Hy.cell ((nearU₄_is F G₂ at_ p.S K₁ R enc rad (x.1.1,
            x'.1.2) (strsOf Fr₂ x'.2) w).1 (hw' _ (by decide)))
        have hR := (recRow₁_is F G₂ at_ p.S K₁ R enc rad (x.1.1, x'.1.2) (strsOf Fr₂ x'.2) w).1 (hw'
            _ (by decide))
        have hR' : RecRowAt R.same p.S.fold.index x'.1.2.loc.key (x'.1.2.loc.psiSh.drop p.S.kLo)
            (uOf (plan₂ p.S) R x'.1.2.st.codes w) := hR
        rw [hkeyE, hf.key] at hR'
        have eg : (x'.1.2.loc.psiSh.drop p.S.kLo).map ρ.val = List.ofFn (gamOf p.S.kLo
            p.S.fold.index.v psi) := by
          rw [List.map_drop, hpsi]
          exact drop_ofFn p.S.kLo p.S.fold.index.v psi
        obtain ⟨cl, hcl, hU⟩ := hgood x _ _ _ hx (linPoint_ok p _ _ _ k1) hnk eg hN hR'
        have st := point_step F G₂ at_ p K₁ R enc rad ρ hsame hof x.1.1 x.1.2 x'.1.2 (strsOf Fr₂
            x.2) (strsOf Fr₂ x'.2) w psi hpsi hco
          (ex' ▸ hpins x.1 x'.1 e1 hor hco) Hy cl hcl hU hw'
        beta_reduce
        rw [layCells_of G₂ x.1 _ w cl hcl, hcl]
        exact st)
  have L := leads_map2_of_goodIn _ _ _ _ _ (fun x _ w => layCells G₂ x.1 (strsOf Fr₂ x.2) w) core
      (fun _ _ _ _ _ => rfl)
  refine Reduction.Leads.conseq L (fun _ h => h) fun x τ x' hx hb hq => ?_
  rintro ⟨w, hw⟩
  have hlin := linPoint_ok p _ _ _ (hl _ _ _ _ (piece_decides_at (extPiece (Wit Cells Unit M) pc fun
      x _ w => layCells G₂ x.1 (strsOf Fr₂ x.2) w) x τ x' hb)).2
  obtain ⟨⟨hT, h0, hs0, h2, hs2, hE⟩, hV⟩ := hq.2 w hw
  refine ⟨layCells G₂ x.1 (strsOf Fr₂ x.2) w, fun i hi => ?_⟩
  rw [open₂_at1] at hi
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact trivial
  · exact hT
  · exact h0
  · exact hs0
  · beta_reduce at hV
    rw [cellsAt_of_pinT G₂ _ _ _ hT] at hV
    exact hpile x _ hx hlin hE hV
  · exact h2
  · exact hs2

end

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.point_step
#print axioms Johnson.RunOne.KeyRows23.point_back₂
