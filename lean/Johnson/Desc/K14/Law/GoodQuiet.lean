-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/GoodQuiet.lean: the shared chain's blocks without a round, "(rec_gamma)" and
the joinings, in the form that the rule of composition asks of a block at its stretch (GoodIn);
and two identities between the claims at the shared chain's borders.

  quiet_goodIn    a block whose decision goes onward and leaves the small record: what every border
                  holds (Base) goes back through it, and with it every claim Q on the statement that
                  goes back at such a yes; the promise behind is had from the promise in front and
                  the block's own yes.
  rec_goodIn3, joins_goodIn6   at the shared chain's own third and sixth block.
  OmegaCol.back, FoldAt.back   these two claims are such claims.
  dotU_of         if omega_col is col_psi_lo(u) on the rows of M, then (Dot)'s equation is an
                  equation between the row weights on col_psi_lo(u) and W at the point.
  dotTrueCatches  the count at the shared point without omega_col: if W is not g applied to M's
                  rows, then W at psi is g and the equality vector at psi applied to M at no more
                  than k |K| ^ (k - 1) points.

What is not claimed. PREMISES of the first three: the extractor is the identity; under the promise
in front: at a yes a witness that is pinned behind the block is pinned in front of it. THE FORM:
«the pin goes back» is asked UNDER THE PROMISE IN FRONT OF THE BLOCK ALONE, not of every statement.
A block that refuses all has GoodIn too. What the constraints
(rec_gamma) mean is shown elsewhere (recLaw). No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.GoodFold
import Johnson.Desc.K14.Law.DotCount

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words)
open VerifiableInference.Desc (Grows Block noDigest)
open VerifiableInference.Desc.Sound (Frame Piece goodIn_of_sure)
open _root_.Run.PQ (CK)

variable {K : Type} [Field K] (ρ : OnBytes.Model.Reading K)
variable {W : Type} {C : CK} {F : Frame} (rw : W → Words K) (Pin : St × F.E.Str → W → Prop)

/-- **A block that goes onward and leaves the small record.** hon: the promise behind, from the
promise in front and the block's own yes; Q: a claim that goes back at such a yes. -/
theorem quiet_goodIn (pc : Piece C F St Unit W)
    (hq : ∀ d rs gs d', pc.b.decide d rs gs = .ok d' → Onward d d' ∧ d'.loc = d.loc)
    (hext : ∀ a τ w, pc.ext a τ w = w) (on on' : St × F.E.Str → Prop)
    (hback : ∀ a τ b w, on a → pc.ior.red.out a τ = some b → Pin b w → Pin a w)
    (hon : ∀ (a b : St × F.E.Str) rs gs, on a → pc.b.decide a.1 rs gs = .ok b.1 → on' b)
    (Q : St × F.E.Str → Words K → Prop)
    (hQ : ∀ (a : St × F.E.Str) τ (b : St × F.E.Str) m, b.2 = pc.ior.imp a.2 τ → Onward a.1 b.1 →
      b.1.loc = a.1.loc → Q b m → Q a m) :
    pc.GoodIn on on' (fun a w => Base ρ rw Pin a w ∧ Q a (rw w))
      (fun a w => Base ρ rw Pin a w ∧ Q a (rw w)) := by
  refine goodIn_of_sure pc _ _ _ _ fun a τ b ha hout => ?_
  obtain ⟨hy, gs, hd⟩ := piece_yes pc a τ b hout
  obtain ⟨o, l⟩ := hq _ _ _ _ hd
  refine ⟨hon a b _ gs ha hd, fun w hw => ?_⟩
  obtain ⟨⟨hpin, hU, hO⟩, hq'⟩ := hw
  rw [hext]
  refine ⟨⟨hback a τ b w ha hout hpin, ?_, ?_⟩, hQ a τ b _ hy o l hq'⟩
  · rw [← l]; exact hU.back ρ o
  · rw [← l]; exact hO.back ρ o

/-- The claim on omega_col reads the small record and the codes alone. -/
theorem OmegaCol.back (S : LinShape) (d d' : St) (m : Words K) (o : Onward d d')
    (l : d'.loc = d.loc) (h : OmegaCol ρ S d' m) : OmegaCol ρ S d m := by
  unfold OmegaCol at h ⊢
  rw [l, o.grows.1] at h
  exact h

/-- So does (fold)'s equation. -/
theorem FoldAt.back (S : LinShape) (d d' : St) (m : Words K) (o : Onward d d')
    (l : d'.loc = d.loc) (h : FoldAt ρ S d' m) : FoldAt ρ S d m := by
  unfold FoldAt at h ⊢
  rw [l, o.grows.1] at h
  exact h

/-- The third block decides by "(rec_gamma)", the sixth by the joinings. -/
theorem quiet_of_blocks (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    (∀ d rs gs d', b3.decide d rs gs = .ok d' → laysRec P.par d rs = some d') ∧
      ∀ d rs gs d', b6.decide d rs gs = .ok d' → joins P.par d rs = some d' := by
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hb
  obtain ⟨sentU, hU, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hb
  exact ⟨fun d rs gs d' h => why_some h, fun d rs gs d' h => why_some h⟩

/-- **"(rec_gamma)" in the form of the rule of composition**, at the chain's own third block. -/
theorem rec_goodIn3 (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (pc : Piece C F St Unit W)
    (hpc : pc.b = b3) (hext : ∀ a τ w, pc.ext a τ w = w) (on on' : St × F.E.Str → Prop)
    (hback : ∀ a τ b w, on a → pc.ior.red.out a τ = some b → Pin b w → Pin a w)
    (hon : ∀ (a b : St × F.E.Str) rs, on a → laysRec P.par a.1 rs = some b.1 → on' b)
    (Q : St × F.E.Str → Words K → Prop)
    (hQ : ∀ (a : St × F.E.Str) τ (b : St × F.E.Str) m, b.2 = pc.ior.imp a.2 τ → Onward a.1 b.1 →
      b.1.loc = a.1.loc → Q b m → Q a m) :
    pc.GoodIn on on' (fun a w => Base ρ rw Pin a w ∧ Q a (rw w))
      (fun a w => Base ρ rw Pin a w ∧ Q a (rw w)) :=
  quiet_goodIn ρ rw Pin pc
    (fun d rs gs d' h => onward_laysRec P.par d d' rs
      ((quiet_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hbl).1 d rs gs d' (hpc ▸ h)))
    hext on on' hback
    (fun a b rs gs ha h => hon a b rs ha
      ((quiet_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hbl).1 _ rs gs _ (hpc ▸ h))) Q hQ

/-- **The joinings in the form of the rule of composition**, at the chain's own sixth block. -/
theorem joins_goodIn6 (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (pc : Piece C F St Unit W)
    (hpc : pc.b = b6) (hext : ∀ a τ w, pc.ext a τ w = w) (on on' : St × F.E.Str → Prop)
    (hback : ∀ a τ b w, on a → pc.ior.red.out a τ = some b → Pin b w → Pin a w)
    (hon : ∀ (a b : St × F.E.Str) rs, on a → joins P.par a.1 rs = some b.1 → on' b)
    (Q : St × F.E.Str → Words K → Prop)
    (hQ : ∀ (a : St × F.E.Str) τ (b : St × F.E.Str) m, b.2 = pc.ior.imp a.2 τ → Onward a.1 b.1 →
      b.1.loc = a.1.loc → Q b m → Q a m) :
    pc.GoodIn on on' (fun a w => Base ρ rw Pin a w ∧ Q a (rw w))
      (fun a w => Base ρ rw Pin a w ∧ Q a (rw w)) :=
  quiet_goodIn ρ rw Pin pc
    (fun d rs gs d' h => onward_joins P.par d d' rs
      ((quiet_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hbl).2 d rs gs d' (hpc ▸ h)))
    hext on on' hback
    (fun a b rs gs ha h => hon a b rs ha
      ((quiet_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hbl).2 _ rs gs _ (hpc ▸ h))) Q hQ

/-! ## Two identities between the claims -/

/-- With omega_col = col_psi_lo(u) on the rows of M, (Dot)'s equation speaks of u. -/
theorem dotU_of (R k kLo : Nat) (g omega u : Nat → K) (psiLo psi : List K) (V : Nat → K)
    (hO : ∀ y < R, omega y = ∑ t ∈ Finset.range (2 ^ kLo), eqK psiLo t * u (t + 2 ^ kLo * y))
    (hD : DotEq R k g omega psi V) :
    ∑ y ∈ Finset.range R, g y * ∑ t ∈ Finset.range (2 ^ kLo), eqK psiLo t * u (t + 2 ^ kLo * y) =
      ∑ c ∈ Finset.range (2 ^ k), eqK psi c * V c := by
  unfold DotEq at hD
  rw [← hD]
  exact Finset.sum_congr rfl fun y hy => by rw [hO y (Finset.mem_range.1 hy)]

open Classical in
/-- The count at the shared point, without omega_col. -/
theorem dotTrueCatches [Fintype K] (R k : Nat) (M : Nat → Nat → K) (g V : Nat → K)
    (h : ∃ c < 2 ^ k, V c ≠ ∑ y ∈ Finset.range R, g y * M y c) :
    (Finset.univ.filter fun psi : Fin k → K =>
      ∑ c ∈ Finset.range (2 ^ k), eqK (List.ofFn psi) c * V c =
        ∑ y ∈ Finset.range R, g y *
          ∑ c ∈ Finset.range (2 ^ k), eqK (List.ofFn psi) c * M y c).card ≤
      k * Fintype.card K ^ (k - 1) := by
  refine le_trans (Finset.card_le_card ?_) (dotCatches R k M g V h)
  intro psi hpsi
  rw [Finset.mem_filter] at hpsi ⊢
  exact ⟨hpsi.1, fun y => ∑ c ∈ Finset.range (2 ^ k), eqK (List.ofFn psi) c * M y c,
    fun _ _ => rfl, hpsi.2.symm⟩

end Desc.K14.Law
