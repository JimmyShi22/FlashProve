-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyTies21At.lean: ROW 2.1 OF THE KEY FILE's TABLE OF JOINTS:
THE TWO TIES ON LETTERS CollTie | DecTie (Johnson/RunOne/KeyGood21.lean) AT THE LIBRARY's OWN
DECODER WITH THE PROGRAM's RECORD, decRec T v eM lg s (OnBytes/Slice/RecordRead.lean:315), WHERE ITS
FOUR NUMBERS ARE THE LAW's OWN SHAPE's (hT · hv · hlg · hs): Rec := its Rec (= RecP NZ v lg s) ·
Cells := what its dcd returns · decT := dcd ∘ yOf · coll ⇐ coll ∘ yOf · the instance's key := keyOf
of the reading's record. THE TRANSPORT ALONG THE FOUR EQUATIONS IS MADE HERE, ONCE (T v lg s are
letters: subst).
AT THE NAME's OWN CONFIGURATION: OnBytes/Flat/EntryRecord.lean:156: frS.toDecR frZ
402653181 = decRec recT recV Params.recordRadius recLg recS := rfl: so DN
(Johnson/Top/Fire/Code/KeyAtName.lean) IS such a decoder; the four equations are then closed facts
at keyFull's index (32 · 402653184 · 44040191 | 11 | 29 | 1).
BY CALLS: collTie_lib | decTie_lib (KeyTies21Lib.lean: dcd_lib | coll_lib) ·
hrec_of_keyOf (KeyRecBack21.lean) · tab_tie | rank0 (Johnson/Desc/K14/Law/DecTie.lean).
ON EMPTINESS: as KeyRow21.lean's head: NO MEMBER OF on₂ … 1 IS SHOWN BY ANYBODY.
OBJECT: CollTie | DecTie at decRec's types, rank := rank0 p.S.fold · USER: point_back₂_lib | … |
_seat (hcoll | hdec) · LETTERS: T v lg s; the tables' but Rec | Cells; err eM.
  yOf           the stored table's symbols, a missing one read as (0, [])
    [as yOf in Johnson/Top/Fire/Code/KeyAtName.lean and tabBack in Johnson/Desc/Sound/DecTop.lean]
  baseWordAt | baseWordAt_reads   htab's INSTANCE: at R.tab := baseWordAt: the base word of a
    base-valued table's entry reads as that entry
  collTie_at    PROVED FROM: the four equations · hkey · hcl
  decTie_at     PROVED FROM: the four equations · hkey · hdc · htab · four public facts
LEFT: hkey [guarded by «recOf z = some r»]: the filling's keyInstanceOfOutOfDomainSample · hcl | hdc [bare ∀]: DEFINITIONS at
coll := fun y r => D.coll (yOf y.cell) r.1 · decT := fun cell r => D.dcd (yOf cell) r: rfl there ·
htab [guarded by «c is base-valued»]: MET at R.tab := baseWordAt (baseWordAt_reads): the
filling's «tab u r i := the base word of u».
Nothing on soundness.
-/
import Johnson.RunOne.KeyRecBack21

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound
open _root_.Desc.Plain (Par)
open _root_.Desc.K14.Law (ixLib bitsOf rank0 tab_tie tabF colsOf)
open VerifiableInference.Desc.K13.Law (ρg)
open OnBytes.Slice (GE GF NZ DecR decRec codeOf keyOf)

/-- The stored table's symbols, a missing one read as (0, []). -/
def yOf (a : Nat) (cell : Nat → Option (Nat × List UInt64)) : Fin (2 ^ a) → Run.PQ.SgX := fun q =>
    (cell q.val).getD (0, [])

/-- The base word of a decoded table's entry: row r, place k; 0 beyond a row's message. [In
OnBytes/Slice/Field.lean: ofF: «the word below p that is read as x».] -/
def baseWordAt {v l : Nat} (c : (Fin v → Bool) × Fin l → GE) (r k : Nat) : UInt64 :=
  if h : k < l then OnBytes.Slice.ofF (c (bitsOf v r, ⟨k, h⟩)).c0 else 0

/-- **htab's instance**: the base word of a base-valued table's entry reads as that entry. -/
theorem baseWordAt_reads {v l : Nat} (c : (Fin v → Bool) × Fin l → GE) (r k : Nat) (hk : k < l)
    (hb : ∀ n, ∃ b : GF, c n = algebraMap GF GE b) : ρg.val (ofF (baseWordAt c r k)) = c (bitsOf v
        r, ⟨k, hk⟩) := by
  obtain ⟨b, e⟩ := hb (bitsOf v r, ⟨k, hk⟩)
  unfold baseWordAt
  rw [dif_pos hk, e]
  show OnBytes.Model.Reading.gl.val (OnBytes.ofF (OnBytes.Slice.ofF b)) = _
  rw [_root_.Desc.K14.Law.gl_ofF, OnBytes.Slice.toF_ofF]

section
variable {XI M Smp : Type} (F : FileDescription XI) (Fr₂ : Frame) (p : Par) (err eM : Nat)

/-- **CollTie at the library's decoder with the program's record.** -/
theorem collTie_at (T : Fmt.M1.Code) (v lg s : Nat) (hT : codeOf p.S.fold.index.code = T) (hv :
    p.S.fold.index.v = v)
    (hlg : p.S.fold.index.cubeBits = lg) (hs : p.S.fold.index.answers = s)
    (G₂ : Reading (P₂ × St₂) ((decRec T v eM lg s).ix.Row × (decRec T v eM lg s).toDec.En → GE) M
        Smp (decRec T v eM lg s).Rec) (at_ : Where)
    (K₁ : KPlan) (R : KRead ((decRec T v eM lg s).ix.Row × (decRec T v eM lg s).toDec.En → GE) M)
        (enc : (Nat → E) → Nat → E) (rad a : Nat)
    (coll : Strs → (decRec T v eM lg s).Rec → Prop) (last₁ : FirstState → Bool) (off₂ : Nat → Nat)
    (hkey : ∀ z r, G₂.recOf z = some r → z.1.1.key = keyOf (v := v) (lg := lg) (s := s) (fun β : NZ
        => β.val) r)
    (hcl : ∀ y r, (decRec T v eM lg s).coll (yOf T.a y.cell) r.1 → coll y r) :
    CollTie F Fr₂ G₂ at_ p K₁ R enc rad a coll last₁ off₂ err eM (rank0 p.S.fold) := by
  subst hT hv hlg hs
  refine collTie_lib F Fr₂ p err eM (rank0 p.S.fold) G₂ at_ K₁ R enc rad a coll last₁ off₂
    (hrec_of_keyOf p err eM (rank0 p.S.fold) G₂ hkey) fun y r h => hcl y r ?_
  have e := tab_tie p.S.fold err eM y.cell
  show (ixLib p.S.fold eM (rank0 p.S.fold)).Coll _ r.1
  exact e ▸ h

/-- **DecTie at the library's decoder with the program's record.** -/
theorem decTie_at (T : Fmt.M1.Code) (v lg s : Nat) (hT : codeOf p.S.fold.index.code = T) (hv :
    p.S.fold.index.v = v)
    (hlg : p.S.fold.index.cubeBits = lg) (hs : p.S.fold.index.answers = s)
    (G₂ : Reading (P₂ × St₂) ((decRec T v eM lg s).ix.Row × (decRec T v eM lg s).toDec.En → GE) M
        Smp (decRec T v eM lg s).Rec) (at_ : Where)
    (K₁ : KPlan) (R : KRead ((decRec T v eM lg s).ix.Row × (decRec T v eM lg s).toDec.En → GE) M)
        (enc : (Nat → E) → Nat → E) (rad a : Nat)
    (coll : Strs → (decRec T v eM lg s).Rec → Prop) (last₁ : FirstState → Bool) (off₂ : Nat → Nat)
    (hkey : ∀ z r, G₂.recOf z = some r → z.1.1.key = keyOf (v := v) (lg := lg) (s := s) (fun β : NZ
        => β.val) r)
    (hdc : ∀ cell r, G₂.decT cell r = (decRec T v eM lg s).dcd (yOf T.a cell) r)
    (htab : ∀ (c : (decRec T v eM lg s).ix.Row × (decRec T v eM lg s).toDec.En → GE) (r k : Nat) (hk
        : k < T.l),
      (∀ n, ∃ b : GF, c n = algebraMap GF GE b) → r < 2 ^ v → ρg.val (ofF (R.tab c r k)) = c (bitsOf
          v r, ⟨k, hk⟩))
    (ha : p.S.fold.index.code.logN ≤ 32) (hroom : p.S.fold.index.code.r + p.S.fold.index.code.ell ≤
        2 ^ p.S.fold.index.code.logN)
    (he : eM < 2 ^ p.S.fold.index.code.logN - (p.S.fold.index.code.r + p.S.fold.index.code.ell) + 1)
    (hell : p.S.matrixRows * 2 ^ p.S.kLo ≤ p.S.fold.index.code.ell) :
    DecTie F Fr₂ G₂ at_ p K₁ R enc rad a coll last₁ off₂ err eM (rank0 p.S.fold) := by
  subst hT hv hlg hs
  refine decTie_lib F Fr₂ p err eM (rank0 p.S.fold) G₂ at_ K₁ R enc rad a coll last₁ off₂
    (hrec_of_keyOf p err eM (rank0 p.S.fold) G₂ hkey) (fun cell r => ?_) htab ha hroom he hell
  rw [hdc]
  have e := tab_tie p.S.fold err eM cell
  show (ixLib p.S.fold eM (rank0 p.S.fold)).dec _ r = _
  exact congrArg (fun f => (ixLib p.S.fold eM (rank0 p.S.fold)).dec f r) e

end

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.baseWordAt_reads
#print axioms Johnson.RunOne.KeyRows23.collTie_at
#print axioms Johnson.RunOne.KeyRows23.decTie_at
