-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/DrawnSeed.lean: e₁'s ROW 121: A READER OF SAMPLES
THAT LAYS A SEED WHICH MAKES THE SAMPLE ROW ITSELF, AND A TERM FOR pS AT THAT SEED: THE PROGRAM's
SAMPLE ROW, LAID ALONE, IN CLOSED FORM. Definitions, statements and proofs.

Why. Part 5's smpNamed lays SOME seed whose matrix ON THE MESSAGE's REAL ROWS is the sample row's
form (K1.smpAt). K10's law asks pS at the laid seed to be the row's vector ON THE WHOLE CUBE, the
padding rows of the member's block among them, where the row weighs too (evaluated: at all 12 such
members of the small honest walk). Two drawn seeds with one matrix on the real rows may part there.
So what is laid must be a seed that MAKES THE ROW: then the row's every coefficient inside its
tables is K1's closed weight at that seed (K1's meansLaw).

  smpDrawn         THE READER. WITHOUT CODE: where the statement's sample rows of the message are
                   kind K1's one row at some seed (K1.SeedIs): such a seed, and its answer;
                   elsewhere what smpNamed gives
  smpDrawn_seed    where SeedIs holds at some seed: what is laid is a seed ρ and an answer y with
                   SeedIs at ρ, y
  sameVal_drawn    **the library cannot tell it from smpNamed**: wherever smpNamed gives a sample,
                   smpDrawn gives one with the same sample map (Z.val) and the same answers: under
                   K1.Tie of the shape: SameVal (Close/Law/FaTwoReaders.lean), written
                   out
  coef_seed        K1's sample row's coefficient on an entry inside a table of its own message is
                   K1's closed weight at the seed that it reads as
  pSseed T₀ L₀ noOf THE TERM FOR pS: at an index of the cube: the message's weight there by T₀, L₀
                   times K1's closed weight at the seed on the entry that belongs to the index
  pSseed_eq        **pSseed T L noOf as ρ = rowVec N T L ‹K1's sample row at a seed that reads as
                   ρ›**: under Tie and: wherever the message has a weight, the entry lies inside its
                   table (three clauses)

Limits. smpDrawn HAS NO CODE: a walk cannot evaluate it. pSseed reads T₀ and L₀: that the begun
statement's row bits and the layout at a reached state are the plan's is not treated: pSseed_eq is
stated at the state's own T and L. The three clauses on ranges are premises. SeedIs and Tie at a
reached state are premises. SampleFits is not touched. No soundness statement.

-/
import Johnson.Desc.Sound.SmpNamed
import Johnson.Desc.K1.Law.Port4
import Johnson.Desc.K1.Law.SeedIs
import Johnson.Desc.First.Link.Law.SampleAtK10

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker Johnson.Pack Cb Cb.Pv Johnson.Top.H
open KObj
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (NamesOne rowVec SlotNames rowVec_main rowVec_mask
  rowVec_kept rowVec_offCorner)

section Reader
variable {P : Type} (cs : OnBytes.Codes) (seats : List (ℕ × ℕ))

open Classical in
/-- **THE READER OF A SEED THAT MAKES THE ROW.** Without code. -/
noncomputable def smpDrawn (a : P × S) (s : Sending) (i : Fin s.l.length) :
    Option ((sigOf cs s.l).om i).Smp :=
  if h : ∃ (ρ : (Fin (bitsZ cs (s.l.get i).1) → GE) × GEˣ) (y : GE),
      K1.SeedIs cs (s.l.get i).1 a.2.st (numAt seats ⟨s, i⟩) ρ y then
    some (h.choose, fun _ => h.choose_spec.choose)
  else smpNamed cs seats a s i

/-- Where the rows are the kind's at some seed, what is laid is such a seed with its answer. -/
theorem smpDrawn_seed (a : P × S) (s : Sending) (i : Fin s.l.length)
    (h : ∃ (ρ : (Fin (bitsZ cs (s.l.get i).1) → GE) × GEˣ) (y : GE),
      K1.SeedIs cs (s.l.get i).1 a.2.st (numAt seats ⟨s, i⟩) ρ y) :
    ∃ (ρ : (Fin (bitsZ cs (s.l.get i).1) → GE) × GEˣ) (y : GE),
      smpDrawn cs seats a s i = some (ρ, fun _ => y) ∧
      K1.SeedIs cs (s.l.get i).1 a.2.st (numAt seats ⟨s, i⟩) ρ y :=
  ⟨h.choose, h.choose_spec.choose, dif_pos h, h.choose_spec.choose_spec⟩

/-- **The library cannot tell the two readers apart.** -/
theorem sameVal_drawn (a : P × S) (s : Sending) (i : Fin s.l.length)
    (hT : K1.Tie cs (s.l.get i).1) (zz : ((sigOf cs s.l).om i).Smp)
    (hz : smpNamed cs seats a s i = some zz) :
    ∃ zd, smpDrawn cs seats a s i = some zd ∧
      ((sigOf cs s.l).om i).Z.val zd.1 = ((sigOf cs s.l).om i).Z.val zz.1 ∧ zd.2 = zz.2 := by
  by_cases h : ∃ (ρ : (Fin (bitsZ cs (s.l.get i).1) → GE) × GEˣ) (y : GE),
      K1.SeedIs cs (s.l.get i).1 a.2.st (numAt seats ⟨s, i⟩) ρ y
  · obtain ⟨ρ, y, h1, h2⟩ := smpDrawn_seed cs seats a s i h
    have hq : s.seat i ∈ seats := by
      by_contra hn
      rw [smpNamed_none cs seats a s i hn] at hz
      exact absurd hz (by simp)
    obtain ⟨z, e1, e2, e3⟩ := smpNamed_of cs seats a s i hq ρ y hT h2
    obtain rfl : z = zz := Option.some.inj (e1.symm.trans hz)
    exact ⟨_, h1, e3.symm, e2.symm⟩
  · exact ⟨zz, (dif_neg h).trans hz, rfl, rfl⟩

end Reader

/-- K1's sample row's coefficient inside a table of its own message: the closed weight. -/
theorem coef_seed {cs : OnBytes.Codes} {s : OracleShape} (h : K1.Tie cs s) (o : ℕ) (z : List E)
    (β y : E) (ρ : (Fin (bitsZ cs s) → GE) × GEˣ) (r : K1.ReadsOne cs s z β ρ) (part : Part)
    (j : ℕ) (hj : j < 2 ^ (K1.Msg.of cs s).bits part) :
    readE ((K1.sampleRow (K1.Msg.of cs s) o z β 0 y).coefficient o part j) =
      (K1.Msg.of cs s).weight (K1.pointOf ρ.1) (ρ.2 : GE) 0 part j := by
  obtain ⟨_, _, _, hc⟩ := K1.meansLaw (K1.Msg.of cs s) o z β 0 y h.some
    (by rw [K1.v_bitsZ]; exact r.long)
  have e := hc part j hj
  rw [(K1.Msg.of cs s).weight_congr _ _ r.agree, r.factor] at e
  exact e

theorem mul_congr_of {A X Y : GE} (h : A ≠ 0 → X = Y) : A * X = A * Y := by
  by_cases hA : A = 0
  · rw [hA, zero_mul, zero_mul]
  · rw [h hA]

section Term
variable (cs : OnBytes.Codes) (lo : List (OracleShape × ℕ)) (R : RowsK (sigOf cs lo))
  (N : SlotNames R)

/-- **THE TERM FOR pS: the program's sample row, laid alone, in closed form at the seed.** -/
noncomputable def pSseed (T₀ : Statement) (L₀ : GroupLayout) (noOf : Fin lo.length → ℕ) :
    ∀ as : (Σ a : R.G.A, ((sigOf cs lo).om a.1).Z.S), ((sigOf cs lo).om as.1.1).Z.D →
      R.Sh.Cin.J → GE :=
  fun as D j =>
    let ρ : (Fin (bitsZ cs (lo.get as.1.1).1) → GE) × GEˣ := D
    let W : Part → ℕ → GE :=
      (K1.Msg.of cs (lo.get as.1.1).1).weight (K1.pointOf ρ.1) (ρ.2 : GE) 0
    match j with
    | .inl (b, (none, x)) =>
      mainWeight (K := GE) T₀ L₀ (noOf as.1.1) (Sz.rowNo b + 2 ^ (R.s.h + R.s.g) * x.val) *
        W .main (mainBack T₀ L₀ (noOf as.1.1) (Sz.rowNo b + 2 ^ (R.s.h + R.s.g) * x.val))
    | .inl (b, (some q, x)) =>
      if b = fun _ => false then
        keptWeight (K := GE) L₀ (N.orc q) *
          (if N.orc q = noOf as.1.1 then W .main (N.idx q x) else 0)
      else 0
    | .inr (b, x) =>
      maskWeight (K := GE) T₀ L₀ (noOf as.1.1) (Sz.rowNo b + 2 ^ R.s.h * x.val) *
        W .mask (maskBack T₀ L₀ (noOf as.1.1) (Sz.rowNo b + 2 ^ R.s.h * x.val))

/-- **RowsTied's clause on pS, at the term, at a seed that makes the row.** -/
theorem pSseed_eq (T : Statement) (L : GroupLayout) (noOf : Fin lo.length → ℕ)
    (as : Σ a : R.G.A, ((sigOf cs lo).om a.1).Z.S)
    (hT : K1.Tie cs (lo.get as.1.1).1) (z : List E) (β y : E)
    (ρ : (Fin (bitsZ cs (lo.get as.1.1).1) → GE) × GEˣ)
    (r : K1.ReadsOne cs (lo.get as.1.1).1 z β ρ)
    (hm : ∀ (b : Fin (R.s.h + R.s.g) → Bool) (x : Fin R.s.C.l),
      mainWeight (K := GE) T L (noOf as.1.1) (Sz.rowNo b + 2 ^ (R.s.h + R.s.g) * x.val) ≠ 0 →
      mainBack T L (noOf as.1.1) (Sz.rowNo b + 2 ^ (R.s.h + R.s.g) * x.val) <
        2 ^ (K1.Msg.of cs (lo.get as.1.1).1).bits .main)
    (hk : ∀ (q : R.Kp) (x : Fin R.s.C.l), N.orc q = noOf as.1.1 →
      N.idx q x < 2 ^ (K1.Msg.of cs (lo.get as.1.1).1).bits .main)
    (hz : ∀ (b : Fin R.s.h → Bool) (x : Fin R.s.Z.l),
      maskWeight (K := GE) T L (noOf as.1.1) (Sz.rowNo b + 2 ^ R.s.h * x.val) ≠ 0 →
      maskBack T L (noOf as.1.1) (Sz.rowNo b + 2 ^ R.s.h * x.val) <
        2 ^ (K1.Msg.of cs (lo.get as.1.1).1).bits .mask) :
    pSseed cs lo R N T L noOf as ρ =
      rowVec N T L (K1.sampleRow (K1.Msg.of cs (lo.get as.1.1).1) (noOf as.1.1) z β 0 y) := by
  have h1 := namesOne_sampleRow (K1.Msg.of cs (lo.get as.1.1).1) (noOf as.1.1) z β 0 y
  funext j
  rcases j with ⟨b, k, x⟩ | ⟨b, x⟩
  · cases k with
    | none =>
      rw [rowVec_main N T L _ _ h1 b x]
      exact mul_congr_of fun hw => (coef_seed hT _ z β y ρ r .main _ (hm b x hw)).symm
    | some q =>
      by_cases hb : b = fun _ => false
      · subst hb
        rw [rowVec_kept]
        show (if (fun _ => false : Fin (R.s.h + R.s.g) → Bool) = fun _ => false then _ else 0) = _
        rw [if_pos rfl]
        by_cases hq : N.orc q = noOf as.1.1
        · rw [if_pos hq, hq, coef_seed hT _ z β y ρ r .main _ (hk q x hq)]
        · rw [if_neg hq, h1 _ hq]
      · rw [rowVec_offCorner N T L _ b hb q x]
        show (if b = fun _ => false then _ else 0) = _
        rw [if_neg hb]
  · rw [rowVec_mask N T L _ _ h1 b x]
    exact mul_congr_of fun hw => (coef_seed hT _ z β y ρ r .mask _ (hz b x hw)).symm

end Term

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.smpDrawn_seed
#print axioms VerifiableInference.Desc.LinkJoin.sameVal_drawn
#print axioms VerifiableInference.Desc.LinkJoin.coef_seed
#print axioms VerifiableInference.Desc.LinkJoin.pSseed_eq
