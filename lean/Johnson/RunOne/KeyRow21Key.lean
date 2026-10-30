-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyRow21Key.lean: ROW 2.1 OF THE KEY FILE's TABLE OF JOINTS,
THE CHANCE's HALF WITH ITS NUMBER (Johnson/RunOne/KeyRows2421Number.lean: point_back₂_rounds), AT
THE KEY FILE's OWN TYPED SHAPE, WRITTEN ROUNDS AND RADIUS: THE STATEMENT ON CODES' COUNT hbad PAID:
by k14_point_key (Johnson/Goal/Numbers/K14BadAt.lean: bad_le_efReal, over foldErr_ix,
Johnson/Bridge/FoldErrIx.lean): at keyFull.once.shape (a = 32 · r + l = 446693375 · v = 11), rad
:= 2852142980 (recordRadius), every eM with rad ≤ eM < 3848273922 (the distance), ef := efReal ≤
cMax |K| ^ 10.
ON EMPTINESS: as KeyRow21.lean's head: NO MEMBER OF on₂ … 1 IS SHOWN BY ANYBODY; NO MEMBER OF
DecTie | CollTie.
OBJECT: vecAt b base d kCol (the law's own count at efReal) ext · USER: keeps₂_of_halves' at k = 1,
then keeps_same_cap · LETTERS: the tables' at S := p.S = keyFull.once.shape, rad := 2852142980; err
eM rank: the library's, eM in the range named.
  point_back₂_key   PROVED FROM: hS · hW · hl · hbase · hsame · hpins · hof · henc · hK · hle | hM ·
    CollTie · DecTie · PileTies
What is not claimed. That the tables' letters S | rad are these at the seat; that the frame's data
hold that round at the maker's piece number 1 (hW). No soundness of a verifier.

-/
import Johnson.RunOne.KeyRows2421Number
import Johnson.Goal.Numbers.K14BadAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat
open _root_.Run (ckP)
open _root_.Iop (Reduction Err)
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Plain
    VerifiableInference.Desc.Sound
open _root_.Desc.Plain (Par)
open _root_.Desc.K14.Law (K14Rounds atW k14_rounds_key cMax vecAt ixOf2 PointPaid k14_point_key
    efReal efReal_le indexB index_key)
open VerifiableInference.Desc.K13.Law (ρg)
open scoped ENNReal

section
variable {XI Cells M Smp Rec Cl W : Type} (F : FileDescription XI) (Fr₂ : Frame)
  (G₂ : Reading (P₂ × St₂) Cells M Smp Rec) (at_ : Where)
  (p : Par) (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (a : Nat)
  (coll : Strs → Rec → Prop) (last₁ : FirstState → Bool) (off₂ : Nat → Nat)
  (err eM : Nat) (rank : ((Fin p.S.fold.index.v → Bool) → Fin (p.S.fold.index.code.r +
      p.S.fold.index.code.ell) → Cb.Gl.E) → Nat)

/-- **ROW 2.1 AT THE KEY FILE's OWN TYPED SHAPE, WRITTEN ROUNDS AND RADIUS: the count of the bad
points paid.** -/
theorem point_back₂_key (hS : p.S = Lk6.AtPlan.keyFull.once.shape)
    (d : RDT) (hW : atW Johnson.G.dryKeyFull.2.1 0 = some (d.entry, d.kind))
    (b : Block (P₂ × St₂) Cl) (base : Nat)
    (ext : (P₂ × St₂) × Fr₂.E.Str → _root_.Iop.Tr (uLT (ckP .two) [d]) → W → W)
    (hl : ∀ z rs gs z', b.decide z rs gs = .ok z' → z'.1 = z.1 ∧ _root_.Desc.K14.linPoint p z.2 rs =
        some z'.2)
    (hbase : ∀ j ∈ pinned (open₂ 1), (at_ j).1 < base)
    (hsame : ∀ x y, R.same x y ↔ ρg.val x = ρg.val y)
    (hpins : ∀ z z' : P₂ × St₂, z'.1 = z.1 → z'.2.st.oracles = z.2.st.oracles → z'.2.st.codes =
        z.2.st.codes → SamePins G₂ z z')
    (hof : ∀ (w : Wit Cells Unit M) c k, R.of { w with cells := c } k = R.of w k)
    (henc : EncIs ρg p.S.fold enc) (hK : K₁.lin = p.S)
    (hle : 2852142980 ≤ eM) (hM : eM < 3848273922)
    (hcoll : CollTie F Fr₂ G₂ at_ p K₁ R enc 2852142980 a coll last₁ off₂ err eM rank)
    (hdec : DecTie F Fr₂ G₂ at_ p K₁ R enc 2852142980 a coll last₁ off₂ err eM rank)
    (hties : PileTies F Fr₂ G₂ at_ p K₁ R enc 2852142980 a coll last₁ off₂) :
    (vecAt (F := Fr₂) b base d (p.S.kLo + p.S.fold.index.v)
          (efReal * Fintype.card Cb.Gl.E ^ p.S.kLo + (p.S.kLo + p.S.fold.index.v) * Fintype.card
              Cb.Gl.E ^ (p.S.kLo + p.S.fold.index.v - 1)) ext).ior.red.Leads
        (on₂ F Fr₂ G₂ at_ p.S K₁ R enc 2852142980 a coll last₁ off₂ 1)
        (fun x x' => L₂ F Fr₂ G₂ at_ p.S K₁ R enc 2852142980 2 x' → L₂ F Fr₂ G₂ at_ p.S K₁ R enc
            2852142980 1 x)
        (vecAt (F := Fr₂) b base d (p.S.kLo + p.S.fold.index.v)
          (efReal * Fintype.card Cb.Gl.E ^ p.S.kLo + (p.S.kLo + p.S.fold.index.v) * Fintype.card
              Cb.Gl.E ^ (p.S.kLo + p.S.fold.index.v - 1)) ext).err ∧
      Err.Below (vecAt (F := Fr₂) b base d (p.S.kLo + p.S.fold.index.v)
          (efReal * Fintype.card Cb.Gl.E ^ p.S.kLo + (p.S.kLo + p.S.fold.index.v) * Fintype.card
              Cb.Gl.E ^ (p.S.kLo + p.S.fold.index.v - 1)) ext).err
        ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  have HR : K14Rounds p.S Johnson.G.dryKeyFull.2.1 OnBytes.Params.recordRadius cMax 32 := hS ▸
      k14_rounds_key
  have PP : PointPaid p.S Johnson.G.dryKeyFull.2.1 := hS ▸ k14_point_key
  have hix : indexB p.S = true := hS ▸ index_key
  have ha : p.S.fold.index.code.logN ≤ 32 := by
    unfold indexB at hix
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hix
    exact Nat.le_of_eq hix.1.1
  have efq : ∀ q : Nat, Fintype.card OnBytes.Slice.GE = q → efReal ≤ cMax * q ^ 10 := fun q hq => by
    subst hq
    exact efReal_le
  exact point_back₂_rounds F Fr₂ G₂ at_ p K₁ R enc 2852142980 a coll last₁ off₂ err eM rank HR d hW
      b base ext hl hbase hsame hpins hof henc hK ha
    efReal (efq (Fintype.card Cb.Gl.E) rfl)
    (fun f rec hc => PP.1 (ixOf2 p.S.fold err eM rank) rfl rfl hle hM f rec hc)
        hcoll hdec hties

end

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.point_back₂_key
