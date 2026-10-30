-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdKappaWMono.lean: work only helps: the records without work give the records with any
numbers of bits, at the same κ.

Theorems, by the one remark e ≤ κ · v ⇒ e ≤ κ · (2^w · v). Nothing is evaluated. "Work" is proof of
work; the records bound each round's error e, a count of values of its verifier message (`Err`,
Iop/Rbr.lean), by κ times the number v of all values of that message, and by κ · 2^w · v in a round
with w bits of work. In the flat records with work (`KapCW` twice, `KapCBW`, `LdSw.KapW`, `KapBW`,
`NumsAtW`) the factor 2^w stands in the clause `loc` alone. These errors are numbers that the
records' clauses write out or that a link lists (the data field `Nums.err`, Ior/Chain.lean): that a
link is sound at the numbers that it lists is no statement of this file.

Main names:
  `le_mul_work`: that remark.
  Eight theorems, each: a record or recursive definition of Cb/Ld/LdKappaKit.lean,
    Cb/Ld/LdKappaBat.lean, Cb/Ld/LdKappaTow.lean, Cb/Ld/LdKappa.lean → its analogue with w bits
    (Cb/Ld/LdKappaWorkObj.lean, Cb/Ld/LdKappaW.lean); the types ι, P, P', G.P of positions are taken
    nonempty:
    `ldKappaW_of_linC`: `KapC` (of `LdLinP`) → `KapCW`;
    `ldKappaW_of_linCB`: `KapCB` → `KapCBW`;
    `ldKappaW_of_linkC`: `KapC` (of `LdLkP`) → `KapCW`;
    `ldKappaW_of_sw`: `LdSw.Kap` → `LdSw.KapW`;
    `ldKappaW_of_base`: `KapB` → `KapBW`;
    `ldKappaW_of_towC`: `LdTowC.Kap` → `LdTowC.KapW`;
    `ldKappaW_of_towG`: `LdTowG.Kap` → `LdTowG.KapW`;
    `ldKappaW_of_test`: `KapT` → `KapTW`.
  `ldKappaW_of_seg`, `ldKappaW_of_segs`: `S.NumsAt κ` → `S.NumsAtW w κ`; `L.Nums κ` → `L.NumsW w κ`
    (S a reference segment, L a list of them; `NumsAt`, `Nums`: Cb/Req1/LdReqRefFinal.lean; with
    work: Cb/Ld/LdKappaWorkRef.lean).
  `ldKappaW_of_kap`: `Z.Kap κ` → `Z.KapW ws κ`, for all ws.
  `ldKappaW_of_req`: the five clauses "every round's error, as a probability, is at most κ"
    (bFirst to bLast, Cb/Req1/LdReqRefFinal.lean) of the reference request's record → `LdReqKapW` at
    w, κ, for all w.

Why: a guard: the records of Cb/Ld/LdKappaW.lean can be met, at numbers of bits that are not 0,
wherever those of Cb/Ld/LdKappa.lean and the request's five clauses (bFirst to bLast,
Cb/Req1/LdReqRefFinal.lean) can. By Cb/Ld/LdKappaLeast.lean these can be met wherever the hypothesis
`Z.HypRef` (or `Z.HypRefU`, for E of characteristic p) can, at every κ such that each round's error
of the five lists (`Z.R.toP.toT.obj.nums`), as a probability, is at most κ.

Notation: `ws : LdWk4` (Cb/Ld/LdKappaW.lean): bits of work, by the class of the round that draws
locations.

Limits: the guard is not tight: at that κ the work is not needed. This file says nothing on the
value of any number, and nothing on the way back with work.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdKappaW

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain
open scoped ENNReal

theorem le_mul_work {e κ v : ℝ≥0∞} (w : ℕ) (h : e ≤ κ * v) : e ≤ κ * ((2 : ℝ≥0∞) ^ w * v) :=
  le_trans h (mul_le_mul' le_rfl (by
    calc v = 1 * v := (one_mul v).symm
      _ ≤ (2 : ℝ≥0∞) ^ w * v := mul_le_mul' (one_le_pow₀ one_le_two) le_rfl))

section
variable {E ι κ' J Y : Type}
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ'] [Fintype J] [Fintype Y]

theorem ldKappaW_of_linC (P : LdLinP E ι κ' J Y) (S : P.Snd) (εf w : ℕ)
    (κ : ℝ≥0∞) (h : P.KapC S εf κ) : P.KapCW S εf w κ :=
  ⟨h.sW, h.pt, h.sU, le_mul_work w h.loc, h.sO, h.zeta⟩

omit [Fintype κ'] [Fintype J] [Fintype Y] in
theorem ldKappaW_of_linCB (P : LdLinP E ι κ' J Y) (S : P.Snd) (εf N w : ℕ)
    (κ : ℝ≥0∞) (h : P.KapCB S εf N κ) : P.KapCBW S εf N w κ :=
  ⟨h.sW, h.pt, h.sU, le_mul_work w h.loc, h.sO, h.zeta⟩

end

theorem ldKappaW_of_linkC {E ι κ' J Λ : Type} [Field E] [Fintype E] [Fintype ι] [Nonempty ι]
    [Fintype κ'] [Fintype J] [Fintype Λ] (P : LdLkP E ι κ' J Λ) (S : P.Snd) (ε₀ ε₁ w : ℕ)
    (κ : ℝ≥0∞) (h : P.KapC S ε₀ ε₁ κ) : P.KapCW S ε₀ ε₁ w κ :=
  ⟨h.gam, h.snd, le_mul_work w h.loc, h.phi⟩

section
variable {E : Type} [Field E] [Fintype E]

omit [Fintype E] in
theorem ldKappaW_of_sw {P P' St : Type} [Fintype P] [Nonempty P] [Fintype P'] [Nonempty P']
    (D : LdSw E P P' St) (e L w : ℕ) (κ : ℝ≥0∞) (h : D.Kap e L κ) : D.KapW e L w κ :=
  ⟨h.ood, le_mul_work w h.loc⟩

omit [Field E] in
theorem ldKappaW_of_base (a : LdJoint E) (t bad L2 w : ℕ) (κ : ℝ≥0∞) (h : a.KapB t bad L2 κ) :
    a.KapBW t bad L2 w κ :=
  ⟨h.comb, le_mul_work w h.loc⟩

theorem ldKappaW_of_towC (w : ℕ) (κ : ℝ≥0∞) :
    ∀ {a : LdJoint E} (T : LdTowC a), T.Kap κ → T.KapW w κ := by
  intro a T
  induction T with
  | base a t cov d bad L2 => exact fun h => ldKappaW_of_base a t bad L2 w κ h
  | step Y sl e S d Lst mC mS mW e' L rest ih =>
    exact fun h => ⟨h.1, ldKappaW_of_sw (S.D e) e L w κ h.2.1, ih h.2.2⟩

theorem ldKappaW_of_towG {B : Type} [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P]
    {Sb : B → Type} {sl : ∀ b, Slf E (Sb b) G.C.J} {Z : Evader E (G.Row B)} (w : ℕ) (κ : ℝ≥0∞)
    (T : LdTowG G Sb sl Z) (h : T.Kap κ) : T.KapW w κ := by
  cases T with
  | plain T => exact ldKappaW_of_towC w κ T h
  | shaped Sh Sw d Lst mC mS mW e' L rest =>
    exact ⟨h.1, ldKappaW_of_sw (Sw.D G.e) G.e L w κ h.2.1, ldKappaW_of_towC w κ rest h.2.2⟩

theorem ldKappaW_of_test {S : Sig E} (D : LdRunD S) (T : D.Tow) (w : ℕ)
    (κ : ℝ≥0∞) (h : D.KapT T κ) : D.KapTW T w κ :=
  ⟨h.bridge, ldKappaW_of_towG w κ T h.tow⟩

variable {Kc : Type}

theorem ldKappaW_of_seg {I : LdRefIx E} {a : LdStage E Kc} (S : LdRefS E Kc I a) (w : ℕ)
    (κ : ℝ≥0∞) (h : S.NumsAt κ) : S.NumsAtW w κ :=
  ⟨h.body, h.bat, h.fold, h.snd, le_mul_work w h.loc⟩

theorem ldKappaW_of_segs {I : LdRefIx E} {a b : LdStage E Kc}
    (L : LdRefL E Kc I a b) (w : ℕ) (κ : ℝ≥0∞) : L.Nums κ → L.NumsW w κ := by
  induction L with
  | nil => intro _; rw [LdRefL.NumsW]; trivial
  | snoc L S ih =>
      intro h
      rw [LdRefL.Nums] at h
      rw [LdRefL.NumsW]
      exact ⟨ih h.1, ldKappaW_of_seg S w κ h.2⟩

end

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- The record without work gives the record with any work. -/
theorem ldKappaW_of_kap (Z : LdObjZ F E) (ws : LdWk4) (κ : ℝ≥0∞) (h : Z.Kap κ) : Z.KapW ws κ :=
  { wf := h.wf, lin := ldKappaW_of_linC _ _ _ _ κ h.lin, t₁ := ldKappaW_of_test _ _ _ κ h.t₁,
    t₂ := ldKappaW_of_test _ _ _ κ h.t₂, t₃ := ldKappaW_of_test _ _ _ κ h.t₃
    link := ldKappaW_of_linkC _ _ _ _ _ κ h.link,
      tK := ldKappaW_of_test _ _ _ κ h.tK,
      linB := ldKappaW_of_linCB _ _ _ _ _ κ h.linB
    t₁B := ldKappaW_of_test _ _ _ κ h.t₁B,
      t₂B := ldKappaW_of_test _ _ _ κ h.t₂B,
      t₃B := ldKappaW_of_test _ _ _ κ h.t₃B }

/-- The request's five clauses without work give those with any work. -/
theorem ldKappaW_of_req {Kc : Type} (w : ℕ) (κ : ℝ≥0∞) (R : LdORE F E Kc) {a : LdStage E Kc}
    (first : LdSendD a) {a₁ : LdStage E Kc} (more : LdProg first.tgt a₁) {b : LdStage E Kc}
    (Ls : LdRefL E Kc R.ix a₁ b) (T : LdRefT R b)
    (h1 : (ldSendFamErr first.N first.Sd first.L : ℝ≥0∞) ≤ κ * (Fintype.card first.Sd.D : ℝ≥0∞))
    (h2 : more.Below κ) (h3 : Ls.Nums κ) (h4 : T.A.Nums κ)
    (h5 : Err.Below (R.X.bt.nums R.Cf.conf.E0 Kc).err κ) :
    LdReqKapW w κ R first more Ls T := ⟨h1, h2, ldKappaW_of_segs Ls w κ h3, h4, h5⟩

end
end Cb
