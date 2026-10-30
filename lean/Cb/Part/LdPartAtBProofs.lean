-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartAtBProofs.lean: the proofs of the five statements of Cb/Part/LdPartAtB.lean (a
partition, read over the configuration over which its request is built).

  `ldPartAtB_hold`: the message that holds an index is the same over both configurations (a
    definition by cases: by cases).
  `ldPartAtB_cutIn`, `ldPartAtB_cutCongr`, `ldPartAtB_cutBelow`: the cut matrix: inside the shapes
    the matrix itself; one for matrices that agree inside the shapes; below a bound in absolute
    value if the matrix is.
  `ldPartAtB_force` (under the hypotheses of `Spec.ldPartAtB_props`): the clause `force` of
    `(P.atB K Bt).Props p`, the one clause with work: each layer j < P.n of the packing of the cut
    matrix is a packing below the relaxed bound in absolute value (`Cb.ldPartCf_pack`); under unique
    packing the cells read off it are the matrix at every place in shape (`Cb.ldPartCf_hon`: here
    the width is used); the segments' conditions read places in shape alone (`Props.reads`,
    `Cb.ldPartCf_holds`).

Nothing else is said here.
-/
import Cb.Part.LdPartAtB
import Cb.Part.LdPartCfProofs
import Cb.Part.LdPartIff

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks IOR Finset Cb.RngPk

theorem ldPartAtB_idem : Spec.ldPartAtB_idem := fun _ _ _ _ _ _ _ _ _ _ => rfl

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Algebra F E] {Cf : LdCf F E} (P : LdPartD Cf)
  (K : LdPartPk) (Bt : LdPartBits P)

theorem ldPartAtB_hold (i : Cf.I) (η : Cf.Pad) : (P.cfB K Bt).conf.hold i η = Cf.conf.hold i η := by
  funext n
  obtain ⟨a, j | q⟩ := n <;> rfl

omit [Fintype F] in
theorem ldPartAtB_cutIn (M : ℕ → ℕ → ℕ → ℤ) (q : Place) (hq : P.InShape q) :
    P.cut M q.1 q.2.1 q.2.2 = M q.1 q.2.1 q.2.2 := if_pos hq

omit [Fintype F] in
theorem ldPartAtB_cutCongr (M M' : ℕ → ℕ → ℕ → ℤ)
    (h : ∀ q : Place, P.InShape q → M q.1 q.2.1 q.2.2 = M' q.1 q.2.1 q.2.2) :
    P.cut M = P.cut M' := by
  funext s r c
  unfold LdPartD.cut
  split_ifs with hq
  · exact h (s, r, c) hq
  · rfl

omit [Fintype F] in
theorem ldPartAtB_cutBelow (b : ℤ) (M : ℕ → ℕ → ℕ → ℤ) (h : P.Below b M) :
    P.Below b (P.cut M) := fun q hq => by
  rw [ldPartAtB_cutIn P M q hq]
  exact h q hq

omit [Fintype F] in
theorem ldPartAtB_force (p : ℕ) [CharP E p] (hP : P.Props p) (hW : P.Wide K) (hK : 0 < K.P)
    (hU : Uniq (2 * P.D) K.rdx K.P p) (i : Cf.I) (x : Cf.Xm) (M : ℕ → ℕ → ℕ → ℤ) (hf : P.form x)
    (hb : P.Below (2 * P.D) M) (hc : P.Cond x (P.matI i) (LdPartD.castM (E := E) M)) :
    P.RnoB K i x ((P.atB K Bt).ofMat M) := by
  have hD : 0 < 2 * P.D := by
    have h1 := hP.one_le
    have h2 := hP.le_D
    omega
  have hpk : ∀ j < P.n, PackBy
      (2 * P.D) K.rdx (P.layX K (P.cut M) j) (P.layW K ((P.atB K Bt).ofMat M).1 j) := fun j hj =>
    ldPartCf_pack P K Bt x (P.matI i) (P.cut M) (2 * P.D) hD (ldPartAtB_cutBelow P _ M hb) j hj
  refine ⟨hf, fun j hj => ⟨_, hpk j hj⟩, fun s hs => ?_⟩
  refine ldPartCf_holds (P.seg s) P.fmt x (P.matI i) (LdPartD.castM (E := E) M)
    (fun s => P.cellsW K ((P.atB K Bt).ofMat M).1 s) (hP.wf s hs) (fun q hq => ?_) (hc s hs)
  obtain ⟨_, hin⟩ := hP.reads s hs q hq
  show LdPartD.castM (E := E) M q.1 q.2.1 q.2.2 =
    P.cellsW K ((P.atB K Bt).ofMat M).1 q.1 q.2.1 q.2.2
  rw [ldPartCf_hon P K p hK hU ((P.atB K Bt).ofMat M).1 (P.cut M) (2 * P.D) (le_refl _) q.1
        (hW q.1 hin.1) (hpk q.1 hin.1) q.2.1 q.2.2 hin.2.1 hin.2.2,
    ldPartAtB_cutIn P M q hin]
  rfl

end

theorem ldPartAtB_props : Spec.ldPartAtB_props := fun F E _ _ _ _ Cf P K Bt p _ hP hW hK hU =>
  { pos := hP.pos
    formY := fun _ _ _ h => h.1
    admit := fun _ _ _ h => ⟨h.2.1, h.2.2.2.2⟩
    force := fun i x M hf hb hc => ldPartAtB_force P K Bt p hP hW hK hU i x M hf hb hc
    ofMat_congr := fun M M' h => by
      have e := ldPartAtB_cutCongr P M M' h
      unfold LdPartD.atB
      simp only [e]
    wf := hP.wf
    reads := hP.reads
    keeps := hP.keeps
    keptIn := hP.keptIn
    keptStep := hP.keptStep
    reply := hP.reply
    idx := hP.idx
    char := hP.char
    one_le := hP.one_le
    le_D := hP.le_D
    small := hP.small }

theorem ldPartAtB_side : Spec.ldPartAtB_side := fun _ _ _ _ _ _ _ _ _ _ => ⟨Iff.rfl, Iff.rfl⟩

theorem ldPartAtB_bits : Spec.ldPartAtB_bits := fun _ _ _ _ _ _ _ _ _ _ => ⟨rfl, rfl⟩

theorem ldPartAtB_rel : Spec.ldPartAtB_rel := by
  intro F E _ _ _ _ Cf P K Bt S O St x rc bitX vld k
  have hh : ∀ U : Cf.conf.Msg,
      (∃ i η, U = (P.cfB K Bt).conf.hold i η) ↔ ∃ i η, U = Cf.conf.hold i η := fun U =>
    ⟨fun ⟨i, η, e⟩ => ⟨i, η, e.trans (ldPartAtB_hold P K Bt i η)⟩,
      fun ⟨i, η, e⟩ => ⟨i, η, e.trans (ldPartAtB_hold P K Bt i η).symm⟩⟩
  have hr : ∀ st y t,
      ((P.atB K Bt).ride K k O x rc bitX).rel st y t ↔ (P.ride K k O x rc bitX).rel st y t :=
    fun st y t => and_congr (hh t.1.1) Iff.rfl
  refine ⟨ldPartIff_eq _ _ _ _ _ _ hr (fun _ _ => Iff.rfl) (fun _ => Iff.rfl) (fun _ => rfl),
    ldPartIff_eq _ _ _ _ _ _ hr (fun _ _ => Iff.rfl) (fun _ => Iff.rfl) (fun _ => rfl),
    ldPartIff_eq _ _ _ _ _ _ (fun st y t => and_congr (hr st y t) Iff.rfl) (fun _ _ => Iff.rfl)
      (fun _ => Iff.rfl) (fun _ => rfl)⟩

end Cb
