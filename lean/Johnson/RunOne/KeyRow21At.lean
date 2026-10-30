-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyRow21At.lean: ROW 2.1 OF THE KEY FILE's TABLE OF JOINTS,
THE CHANCE's HALF (Johnson/RunOne/KeyGood21.lean: point_back₂_lib), AT A STRETCH OF ONE WRITTEN
ROUND: the carriage (G | fits | hread) PAID: K14's files' vecMaps | vecMaps_ok | drawn_shown
(ZetaRead.lean) and linPoint_inv (PointGood.lean), and vec_reads
(Johnson/Desc/K14/Law/VecReadAt.lean), cut out of point_goodIn's proof.
ON EMPTINESS: as KeyRow21.lean's head: NO MEMBER OF on₂ … 1 IS SHOWN BY ANYBODY; NO MEMBER OF
DecTie | CollTie. PileTies is PAID at the tables' own letters (Johnson/RunOne/KeyPileTies.lean).
OBJECT: vecAt b base d kCol e ext: BY rfl it is pieceOf b base [d] [] ⟨ext, the written errors at e⟩
· USER: keeps₂_of_halves' (KeyHalves23.lean), at the maker's piece number 1 · TWO DEBTS AT THAT
CALL, NOT PAID HERE, as at row 2.4: Err.le (the written errors at e) (rest₂ 1 [d]).err: the number:
Johnson/RunOne/KeyRows2421Number.lean · that the maker's stretch at n = 1 is [d] with hd: the
frame's data · LETTERS: as KeyGood21.lean's; d; e.
  point_back₂_empty   PROVED: at a stretch without a round the block says no
  point_back₂_at      PROVED FROM: hd (the written round draws kCol elements and no position) · he
    (the count) · what point_back₂_lib asks beside the carriage
Nothing on soundness.
-/
import Johnson.RunOne.KeyGood21
import Johnson.Desc.K14.Law.VecReadAt
import Johnson.Desc.Sound.Tiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat
open _root_.Run.PQ (CK)
open _root_.Run (ckP)
open _root_.Iop (Reduction Err)
open _root_.Prob (cnt)
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Plain
    VerifiableInference.Desc.Sound
open _root_.Desc.Plain (Par)
open _root_.Desc.K14.Law (vecAt vec_reads vecMaps vecMaps_ok linPoint_inv ixOf2)
open VerifiableInference.Desc.K13.Law (ρg)

section
variable {XI Cells M Smp Rec Cl W : Type} (F : FileDescription XI) (Fr₂ : Frame)
  (G₂ : Reading (P₂ × St₂) Cells M Smp Rec) (at_ : Where)
  (p : Par) (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (rad a : Nat)
  (coll : Strs → Rec → Prop) (last₁ : FirstState → Bool) (off₂ : Nat → Nat)
  (err eM : Nat) (rank : ((Fin p.S.fold.index.v → Bool) → Fin (p.S.fold.index.code.r +
      p.S.fold.index.code.ell) → Cb.Gl.E) → Nat)

/-- **At a stretch without a round there is no yes.** -/
theorem point_back₂_empty {C : CK} (b : Block (P₂ × St₂) Cl) (base : Nat) (x₀ : Rest C Fr₂ (P₂ ×
    St₂) W [])
    (hl : ∀ z rs gs z', b.decide z rs gs = .ok z' → z'.1 = z.1 ∧ _root_.Desc.K14.linPoint p z.2 rs =
        some z'.2)
    (on : (P₂ × St₂) × Fr₂.E.Str → Prop) (Q : (P₂ × St₂) × Fr₂.E.Str → (P₂ × St₂) × Fr₂.E.Str →
        Prop) :
    (pieceOf b base [] [] x₀).ior.red.Leads on Q x₀.err :=
  Reduction.Leads.of_sure (K := (pieceOf b base [] [] x₀).ior.red) x₀.err fun x τ x' _ hb => by
    obtain ⟨_, k1⟩ := hl _ _ _ _ (piece_decides_at (pieceOf b base [] [] x₀) x τ x' hb)
    obtain ⟨r, hr, _⟩ := linPoint_inv p _ _ _ k1
    cases hr

/-- **ROW 2.1, THE CHANCE's HALF, at a stretch of one written round.** -/
theorem point_back₂_at (b : Block (P₂ × St₂) Cl) (base : Nat) (d : RDT) {ns a0 : Nat}
    (hd : OnBytes.Slice.SendsDraws (toRD d) ns (p.S.kLo + p.S.fold.index.v) 0 a0)
    (ext : (P₂ × St₂) × Fr₂.E.Str → _root_.Iop.Tr (uLT (ckP .two) [d]) → W → W)
    (hl : ∀ z rs gs z', b.decide z rs gs = .ok z' → z'.1 = z.1 ∧ _root_.Desc.K14.linPoint p z.2 rs =
        some z'.2)
    (hbase : ∀ j ∈ pinned (open₂ 1), (at_ j).1 < base)
    (hsame : ∀ x y, R.same x y ↔ ρg.val x = ρg.val y)
    (hpins : ∀ z z' : P₂ × St₂, z'.1 = z.1 → z'.2.st.oracles = z.2.st.oracles → z'.2.st.codes =
        z.2.st.codes → SamePins G₂ z z')
    (hof : ∀ (w : Wit Cells Unit M) c k, R.of { w with cells := c } k = R.of w k)
    (henc : EncIs ρg p.S.fold enc) (hK : K₁.lin = p.S)
    (ha : p.S.fold.index.code.logN ≤ 32)
    (ef e : Nat)
    (he : ef * Fintype.card Cb.Gl.E ^ p.S.kLo + (p.S.kLo + p.S.fold.index.v) * Fintype.card Cb.Gl.E
        ^ (p.S.kLo + p.S.fold.index.v - 1) ≤ e)
    (hbad : ∀ f rec, ¬ (ixOf2 p.S.fold err eM rank).Coll f rec.1 → cnt ((ixOf2 p.S.fold err eM
        rank).Bad f rec rad) ≤ ef)
    (hcoll : CollTie F Fr₂ G₂ at_ p K₁ R enc rad a coll last₁ off₂ err eM rank)
    (hdec : DecTie F Fr₂ G₂ at_ p K₁ R enc rad a coll last₁ off₂ err eM rank)
    (hties : PileTies F Fr₂ G₂ at_ p K₁ R enc rad a coll last₁ off₂) :
    (vecAt (F := Fr₂) b base d (p.S.kLo + p.S.fold.index.v) e ext).ior.red.Leads
      (on₂ F Fr₂ G₂ at_ p.S K₁ R enc rad a coll last₁ off₂ 1)
      (fun x x' => L₂ F Fr₂ G₂ at_ p.S K₁ R enc rad 2 x' → L₂ F Fr₂ G₂ at_ p.S K₁ R enc rad 1 x)
      (vecAt (F := Fr₂) b base d (p.S.kLo + p.S.fold.index.v) e ext).err :=
  point_back₂_lib F Fr₂ G₂ at_ p K₁ R enc rad a coll last₁ off₂ err eM rank
    (vecAt (F := Fr₂) b base d (p.S.kLo + p.S.fold.index.v) e ext) hl hbase hsame hpins hof henc hK
        ha ef e he
    hbad hcoll hdec hties
    (fun _ => (vecMaps d (p.S.kLo + p.S.fold.index.v)).carry)
    (fun _ => (vecMaps d (p.S.kLo + p.S.fold.index.v)).fits (vecMaps_ok hd) _)
    (fun x τ x' _ hb => by
      obtain ⟨_, k1⟩ := hl _ _ _ _ (piece_decides_at (vecAt (F := Fr₂) b base d (p.S.kLo +
          p.S.fold.index.v) e ext) x τ x' hb)
      obtain ⟨r, hr, hpsi, _⟩ := linPoint_inv p _ _ _ k1
      obtain ⟨psi, htr, hdr⟩ := vec_reads b base d hd e ext x τ x' r hb hr
      exact ⟨psi, htr, by rw [hpsi]; exact hdr⟩)

end

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.point_back₂_empty
#print axioms Johnson.RunOne.KeyRows23.point_back₂_at
