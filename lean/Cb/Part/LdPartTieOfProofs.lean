-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartTieOfProofs.lean: the proof of the statement of Cb/Part/LdPartTieOf.lean. The
statement is on the ties at a closing, for the concrete readings (`nm.out`; `L.ValidU`,
Cb/Part/LdPartLkp.lean). Many statements of this library are written twice: a definition in the
namespace `Spec` states a proposition, and a theorem of the same name outside that namespace proves
it (lean/GLOSSARY.md).

The theorem is `ldPartTieOf : Cb.Spec.ldPartTieOf`. It goes clause by clause: `ldPartTieOf_pkX`,
`ldPartTieOf_shape`, `ldPartTieOf_rdX`, `ldPartTieOf_pkR`, `ldPartTieOf_rdOwn`, `ldPartTieOf_rdKept`
(`ldPartTieOf_shape` is a tool for `ldPartTieOf_rdX`). The proof applies
Cb/Part/LdPartTieNmProofs.lean, Cb/Part/LdPartPkRes.lean, Cb/Part/LdPartCellsOut.lean,
Cb/Part/LdPartLkpBitsProofs.lean.

Notation:
  `T`: an `LdPartTieL` (Cb/Part/LdPartTieOf.lean), the record of parameters;
  `T.OK pp`: a `Prop`, the conditions;
  `T.Ok`, `T.O'`: `T.nm₀.out Sk T.at₀`, `T.nm₁.out S' T.at₁`;
  `T.kept : S'.Msg → Sk.Msg`, `T.ov : S'.Msg → LdPartW E → LdPartW E`: fields of `T`;
  `pkX`, `rdX`, `pkR`, `rdOwn`, `rdKept` in the theorems' names: fields of `LdPartTie`
    (Cb/Part/LdPartNext.lean); in `T.Ok.pkX`, `T.O'.pkR`: fields of `LdPartOut`
    (Cb/Part/LdPartRide.lean).

Terms: lean/GLOSSARY.md.
-/
import Cb.Part.LdPartTieOf
import Cb.Part.LdPartTieNmProofs
import Cb.Part.LdPartLkpBitsProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Finset Cb.Rng Cb.RngPk IOR

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] {Cf : LdCf F E}
  {P : LdPartD Cf} {K : LdPartPk} {k : ℕ} {Sk S' : Sig E} {St' J : Type} [Fintype J]
  (T : LdPartTieL P K k Sk S' St' J) {pp : ℕ}

/-- the next body's matrix of packed entries -/
def LdPartTieL.mpk (m : S'.Msg) : T.p₁.Rp → T.p₁.C → E := fun i κ => S'.ents m (T.at₁ i κ)

theorem ldPartTieOf_kept (h : T.OK pp) (m : S'.Msg) :
    (fun i κ => Sk.ents (T.kept m) (T.at₀ i κ)) = resM T.kR T.kC (T.mpk m) :=
  funext fun i => funext fun c => h.keptE m i c

theorem ldPartTieOf_own (h : T.OK pp) (m : S'.Msg) (w : LdPartW E) :
    P.layW K (T.ov m w) (k + 1) = resM T.oR T.oC (T.mpk m) :=
  funext fun i => funext fun c => h.ovOwn m w i c

theorem ldPartTieOf_pkX (h : T.OK pp) (m : S'.Msg) (w : LdPartW E) (g : LdPartGh)
    (h1 : T.Ok.pkX (T.kept m) g)
    (h2 : PackBy P.B K.rdx (P.layX K g (k + 1)) (P.layW K (T.ov m w) (k + 1))) : T.O'.pkX m g := by
  have h1' : PackBy T.p₀.B T.p₀.rdx (T.nm₀.lay g) (fun i κ => Sk.ents (T.kept m) (T.at₀ i κ)) := h1
  rw [h.B₀, h.rdx₀, ldPartTieOf_kept T h m] at h1'
  rw [ldPartTieOf_own T h m w] at h2
  show PackBy T.p₁.B T.p₁.rdx (T.nm₁.lay g) (T.mpk m)
  rw [h.B₁, h.rdx₁]
  exact ldPartTieNm_packX E T.p₀ T.p₁ T.nm₀ T.nm₁ T.kR T.kC K.P (k + 1) _ _ _ _ T.oR T.oC g P.B
    K.rdx (T.mpk m) h.nP₀ h.nP h.ok₀ h.ok₁ h.part h.own h.cover h1' h2

/-- Under the hypotheses below, the places that segment k + 1 reads lie in the shapes of the next
body's naming. -/
theorem ldPartTieOf_shape {p : ℕ} (hP : P.Props p) (hk : k + 1 < P.n) (h : T.OK pp)
    (q : Place) (hq : q ∈ (P.seg (k + 1)).places) :
    q.2.1 < T.nm₁.R q.1 ∧ q.2.2 < T.nm₁.C q.1 := by
  obtain ⟨hle, _, hr, hc⟩ := hP.reads (k + 1) hk q hq
  by_cases hs : q.1 = k + 1
  · rw [hs, h.own.R, h.own.C]
    rw [hs] at hr hc
    exact ⟨hr, hc⟩
  · have hkp := hP.keeps (k + 1) hk q hq k (by omega) (Nat.lt_succ_self k)
    obtain ⟨n1, n2⟩ := h.named _ hkp
    have n1' : q.2.1 < T.nm₀.R q.1 := n1
    have n2' : T.nm₀.C q.1 = (P.seg q.1).cols := n2
    refine ⟨(h.part.row q.1 q.2.1 n1').1, ?_⟩
    rw [← (h.part.col q.1 (lt_of_le_of_lt (Nat.zero_le _) n1')).1, n2']
    exact hc

theorem ldPartTieOf_uniq (h : T.OK pp) : Uniq (2 * T.p₁.D) T.p₁.rdx T.p₁.P pp := by
  rw [h.D₁, h.rdx₁, ← h.nP]
  exact h.uniq

theorem ldPartTieOf_rdX [CharP E pp] {p : ℕ} (hP : P.Props p) (hk : k + 1 < P.n) (h : T.OK pp)
    (m : S'.Msg) (g : LdPartGh) (hx : T.O'.pkX m g) (q : Place) (hq : q ∈ (P.seg (k + 1)).places) :
    T.O'.A m q.1 q.2.1 q.2.2 = ((g q.1 q.2.1 q.2.2 : ℤ) : E) := by
  obtain ⟨s1, s2⟩ := ldPartTieOf_shape T hP hk h q hq
  refine (ldPartCells_out T.p₁ T.nm₁ E S' T.at₁).2.1
    pp (ldPartTieOf_uniq T h) h.ok₁ ?_ m g hx q.1 q.2.1 q.2.2 s1 s2
  rw [h.B₁, h.D₁]
  have := hP.le_D
  have := hP.one_le
  omega

theorem ldPartTieOf_pkR (h : T.OK pp) (m : S'.Msg) (w : LdPartW E) (hr : T.O'.pkR m) :
    Packed K.P (2 * P.D) K.rdx (P.layW K (T.ov m w) (k + 1)) := by
  have hr' : Packed T.p₁.P (2 * T.p₁.D) T.p₁.rdx (T.mpk m) := hr
  rw [ldPartTieOf_own T h m w, h.nP, ← h.D₁, ← h.rdx₁]
  obtain ⟨Y, hY⟩ := hr'
  exact ⟨_, ldPartRes_by E _ _ _ _ T.p₁.P _ _ T.oR T.oC Y (T.mpk m) hY⟩

theorem ldPartTieOf_rdOwn [CharP E pp] (h : T.OK pp) (m : S'.Msg) (w : LdPartW E) (hr : T.O'.pkR m)
    (r c : ℕ) (h1 : r < 2 ^ (P.seg (k + 1)).rowsLog) (h2 : c < (P.seg (k + 1)).cols) :
    T.O'.A m (k + 1) r c = P.cellsW K (T.ov m w) (k + 1) r c := by
  have hr' : Packed T.p₁.P (2 * T.p₁.D) T.p₁.rdx (T.mpk m) := hr
  obtain ⟨i, ei, _, e2⟩ := h.own.row r h1
  obtain ⟨c', ec, _⟩ := h.own.col c h2
  have hl : r % K.P < K.P := by
    rw [← e2]
    exact lt_of_lt_of_eq (T.nm₁.rowAt (k + 1) r).2.2 h.nP.symm
  have hc : (r / K.P < P.rp K (k + 1) ∧ r % K.P < K.P) ∧ c < K.Cw := ⟨⟨ei ▸ i.2, hl⟩, ec ▸ c'.2⟩
  unfold LdPartD.cellsW
  rw [dif_pos hc, if_pos ⟨h1, h2⟩, ldPartTieOf_own T h m w]
  show ((T.nm₁.mats (cells T.p₁.P (2 * T.p₁.D) T.p₁.rdx (T.mpk m)) (k + 1) r c : ℤ) : E) = _
  have hU := ldPartTieOf_uniq T h
  rw [ldPartTieNm_readOwn E pp T.p₁ T.nm₁ K.P (k + 1) _ _ _ _ T.oR T.oC (2 * T.p₁.D)
        T.p₁.rdx (T.mpk m) h.nP h.own hU hr' r c ⟨r / K.P, hc.1.1⟩ ⟨r % K.P, hc.1.2⟩
        ⟨c, hc.2⟩ h1 h2 rfl rfl rfl,
    h.D₁, h.rdx₁]

theorem ldPartTieOf_rdKept [CharP E pp] (h : T.OK pp) (m : S'.Msg) (hr : T.O'.pkR m) (q : ℕ × ℕ)
    (hq : q ∈ P.kept k) (c : ℕ) :
    T.O'.A m q.1 q.2 c = T.Ok.A (T.kept m) q.1 q.2 c := by
  have hr' : Packed T.p₁.P (2 * T.p₁.D) T.p₁.rdx (T.mpk m) := hr
  show ((T.nm₁.mats (cells T.p₁.P (2 * T.p₁.D) T.p₁.rdx (T.mpk m)) q.1 q.2 c : ℤ) : E) =
    ((T.nm₀.mats (cells T.p₀.P (2 * T.p₀.D) T.p₀.rdx fun i κ => Sk.ents (T.kept m) (T.at₀ i κ))
      q.1 q.2 c : ℤ) : E)
  rw [ldPartTieOf_kept T h m, h.D₀, h.rdx₀, ← h.D₁, ← h.rdx₁,
    ldPartTieNm_readPart E pp T.p₀ T.p₁ T.nm₀ T.nm₁ T.kR T.kC (2 * T.p₁.D) T.p₁.rdx (T.mpk m)
      h.nP₀ h.part (ldPartTieOf_uniq T h) hr' q.1 q.2 c (h.named q hq).1]

end

theorem ldPartTieOf : Spec.ldPartTieOf := by
  intro F E _ _ _ _ _ Cf P K p pp k _ Sk S' St' J _ T hP hk h
  exact
    { ovPk := h.ovPk
      ovBit := h.ovBit
      pkX := ldPartTieOf_pkX T h
      rdX := ldPartTieOf_rdX T hP hk h
      bits := fun st U m w g hx hb =>
        ldPartBits_tie F E Cf P (k + 1) St' J T.R T.x' T.e st (T.msg (U, m)) (P.matU U) g
          ((T.ov m w).bit (k + 1)) (hP.wf (k + 1) hk) (h.rdW U m)
          (fun q hq => by rw [h.rdA U m]; exact ldPartTieOf_rdX T hP hk h m g hx q hq)
          (fun Y i => h.ovB U m w Y i) hb
      pkR := ldPartTieOf_pkR T h
      rdOwn := ldPartTieOf_rdOwn T h
      rdKept := ldPartTieOf_rdKept T h }

end Cb
