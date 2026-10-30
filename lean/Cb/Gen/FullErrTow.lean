-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/FullErrTow.lean: a whole test below the Johnson radius (Cb/Obj/LdObjectTowerJohn.lean), its
errors overwritten by the full list (Cb/Gen/FullErr.lean), is a tail of a chain from the hypotheses
of `LdRunD.PreJD` alone: no agreement of a code is asked.

In standard terms: a proximity test made of folds and code switches, at a radius below the Johnson
bound. What the library requires of such a test includes mutual correlated agreement of its codes,
with a count of exceptional challenges; at the count |E| (all field elements) every code has it.

Definitions, statements (in `Cb.Spec`) and proofs. Generic: any finite field. Nothing assumed beyond
the hypotheses of the statements and whatever the arguments hold as proofs.
A tower is `LdTowJ`, `LdTowGJ` (Cb/Obj/LdObjectTowerJohn.lean); `T.John` is what that file asks of
it. Below the Johnson radius is `InJohnson n d e` (Cb/Gen/JohnsonList.lean): n (n - d) < (n - e)^2,
for n positions, distance d, radius e. Agreement of a code is mutual correlated agreement on lines,
`MCAat e bad` (Cb/Ld/LdRel.lean); `MCArows` (Cb/Ld/LdRelRows.lean) is the same for any number of
interleaved rows.

Why: a tower's counts of bad challenges (bC, bZ, bW at a fold; b at the base) are parameters of its
constructors and enter its blocks' error lists alone. `T.full` puts all of them to the number of all
field elements: there "agreement with at most so many bad challenges" holds of every code (a count
of field elements). So the existing theorems fire at T.full from what is left of T.John: among it
laws, distances, radii, packing, hiding of single codes, samples, evaders. And the whole test of
`T.full` is equal to that of T but for the errors: so T's own test, errors overwritten, is a tail of
a chain.

Main names:
  `T.full`: for T : `LdTowJ a`, and for T : `LdTowGJ G Sb sl Z` (G.P non-empty, as in all statements
    on it).
  `Spec.ldTowJ_fullQ`, `Spec.ldTowGJ_fullQ`: the long positions that are needed: the same number.
  `Spec.ldTowJ_fullEnd`, `Spec.ldTowGJ_fullEnd`: T.full.toC.toEnd.full = T.toC.toEnd.full;
    T.full.toG.toEnd.full = T.toG.toEnd.full.
  `D.full`: one test on a group (`LdRunD`, Cb/Ld/LdLinCloseRuns.lean) with `D.T.full` for D.T.
  `D.PreJD Tw d`: `D.PreJ Tw d` with "Tw.full.John" for "Tw.John".
  `Spec.ldRunD_fullOK`: D.PreJD Tw d → D.full.OK.
  `Spec.ldRunD_preJD`: D.PreJ Tw d → D.PreJD Tw d: `D.PreJD` is the weaker one.

Limits: D.full.OK is the honest half of D.OK in the frame's own form (the head of
Cb/Gen/FullErr.lean): nothing on the chance of a cheating prover (it keeps the bound on lists, a
fact on words that is true under `isL`, `laws`, `dist`, `john` of `D.PreJD`: no agreement and no
assumed statement is asked for it). This file does not say that D.PreJD holds anywhere (over
Goldilocks' cubic extension, from `RunGlJAt D Tw d`: Cb/Gl/GlFullErrTow.lean). On protocols the file
has the whole test of a tower, a fold and one test on a group (`LdTowJ`, `LdTowGJ`, `SumPar.John`,
Cb/Obj/LdObjectTowerJohn.lean; `LdRunD`, Cb/Ld/LdLinCloseRuns.lean); beyond these no statement of
the file speaks of an object or a protocol. It says nothing on numerals.
Terms: lean/GLOSSARY.md: agreement, assumed statement, below the Johnson radius, block, chain,
code switch, error, evader, fold, full list, group, laws (of a code), list, long position, radius,
tail, tower, whole test.
-/
import Cb.Gen.FullErr
import Cb.Obj.LdObjectTowerJohn
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Iop.IOR

theorem ldCode_mcaRowsFull {E P : Type} [Field E] [Fintype E] [Fintype P] (C : LdCode E P) (e : ℕ) :
    C.MCArows e (Fintype.card E) :=
  fun _ _ _ _ _ => cnt_le_card _
theorem ldCode_mcaAtFull {E P : Type} [Field E] [Fintype E] [Fintype P] (C : LdCode E P) (e : ℕ) :
    C.MCAat e (Fintype.card E) :=
  fun _ _ => cnt_le_card _

/-- all counts of bad challenges put to the number of all field elements -/
def LdTowJ.full {E : Type} [Field E] [Fintype E] :
    {a : LdJoint E} → LdTowJ a → LdTowJ a
  | _, .base a t cov d _ => .base a t cov d (Fintype.card E)
  | _, @LdTowJ.step _ _ _ _ _ _ _ _ _ _ Y sl e S d _ _ _ e' d' rest =>
    .step Y sl e S d (Fintype.card E) (Fintype.card E) (Fintype.card E) e' d' rest.full

def LdTowGJ.full {E B : Type} [Field E] [Fintype E] [Fintype B]
    {S : Sig E} {G : Grp S} [Nonempty G.P] {Sb : B → Type}
    {sl : ∀ b, Slf E (Sb b) G.C.J} {Z : Evader E (G.Row B)} :
    LdTowGJ G Sb sl Z → LdTowGJ G Sb sl Z
  | .plain T => .plain T.full
  | @LdTowGJ.shaped _ _ _ _ _ _ _ _ _ _ _ _ _ _ Sh Sw d _ _ _ e' d' rest =>
    .shaped Sh Sw d (Fintype.card E) (Fintype.card E) (Fintype.card E) e' d' rest.full

/-- one test on a group, its whole test's errors overwritten by the full list -/
def LdRunD.full {E : Type} [Field E] [Fintype E] {S : Sig E} (D : LdRunD S) : LdRunD S :=
  { D with T := D.T.full }

/-- What is asked of one test with the tower Tw, below the Johnson radius. -/
structure LdRunD.PreJD {E : Type} [Field E] [Fintype E] {S : Sig E}
    (D : LdRunD S) (Tw : D.TowJ) (d : ℕ) : Prop where
  isT  : D.T = Tw.toG.toEnd
  isQ  : D.t = Tw.toG.q
  isL  : D.L = listMax (Fintype.card D.G.P) d D.G.e
  laws : ∀ a : D.G.A, ((S.om a.1).C.atPos (D.G.pos a)).Laws
  dist : ∀ a : D.G.A, ((S.om a.1).C.atPos (D.G.pos a)).Dist d
  john : InJohnson (Fintype.card D.G.P) d D.G.e
  ev   : D.Z.OK
  fits : D.G.Fits
  /-- John at the counts |E|: its clauses on agreement hold of every code there
  (`ldCode_mcaRowsFull`, `ldCode_mcaAtFull`): so what is asked is the rest -/
  tow  : LdTowGJ.John (LdTowGJ.full Tw)

namespace Spec

def ldTowJ_fullQ : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (a : LdJoint E) (T : LdTowJ a), T.full.toC.q = T.toC.q

def ldTowJ_fullEnd : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (a : LdJoint E) (T : LdTowJ a),
    T.full.toC.toEnd.full = T.toC.toEnd.full

def ldTowGJ_fullQ : Prop :=
  ∀ (E B : Type) [Field E] [Fintype E] [Fintype B] (S : Sig E) (G : Grp S)
      [Nonempty G.P] (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J)
      (Z : Evader E (G.Row B)) (T : LdTowGJ G Sb sl Z),
    T.full.toG.q = T.toG.q

def ldTowGJ_fullEnd : Prop :=
  ∀ (E B : Type) [Field E] [Fintype E] [Fintype B] (S : Sig E) (G : Grp S)
      [Nonempty G.P] (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J)
      (Z : Evader E (G.Row B)) (T : LdTowGJ G Sb sl Z),
    T.full.toG.toEnd.full = T.toG.toEnd.full

def ldRunD_fullOK : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (D : LdRunD S) (Tw : D.TowJ) (d : ℕ),
    D.PreJD Tw d → D.full.OK

def ldTowJ_johnFull : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (a : LdJoint E) (T : LdTowJ a), T.John → T.full.John

def ldRunD_preJD : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (D : LdRunD S) (Tw : D.TowJ) (d : ℕ),
    D.PreJ Tw d → D.PreJD Tw d

end Spec

section
variable {E : Type} [Field E] [Fintype E]

theorem LdTowJ.full_q : ∀ {a : LdJoint E} (T : LdTowJ a), T.full.toC.q = T.toC.q
  | _, .base _ _ _ _ _ => rfl
  | _, @LdTowJ.step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl

theorem LdTowJ.full_end : ∀ {a : LdJoint E} (T : LdTowJ a), T.full.toC.toEnd.full = T.toC.toEnd.full
  | _, .base _ _ _ _ _ => rfl
  | _, @LdTowJ.step _ _ _ _ _ _ _ _ _ _ _ _ e S _ _ _ _ e' _ rest =>
      have hq : rest.full.toC.toTower.q = rest.toC.toTower.q := rest.full_q
      ldFull_consOf (ldFull_seqOf rfl (congrArg (fun t => (ldSwBlock (S.D e) _ e' _ t).full) hq))
        rest.full_end

end

theorem ldTowJ_fullQ : Spec.ldTowJ_fullQ := fun _ _ _ _ T => T.full_q

theorem ldTowJ_fullEnd : Spec.ldTowJ_fullEnd := fun _ _ _ _ T => T.full_end

theorem ldTowGJ_fullQ : Spec.ldTowGJ_fullQ := fun _ _ _ _ _ _ _ _ _ _ _ T => by
  cases T with
  | plain T => exact T.full_q
  | shaped Sh Sw d bC bZ bW e' d' rest => rfl

theorem ldTowGJ_fullEnd : Spec.ldTowGJ_fullEnd := fun _ _ _ _ _ _ G _ _ _ _ T => by
  cases T with
  | plain T => exact T.full_end
  | shaped Sh Sw d bC bZ bW e' d' rest =>
    have hq : rest.full.toC.toTower.q = rest.toC.toTower.q := rest.full_q
    exact ldFull_consOf
      (ldFull_seqOf rfl (congrArg (fun t => (ldSwBlock (Sw.D G.e) _ e' _ t).full) hq)) rest.full_end

theorem ldRunD_fullOK : Spec.ldRunD_fullOK := fun E _ _ S D Tw d h =>
  have h1 : (LdRunD.PreJ { D with T := (LdTowGJ.full Tw).toG.toEnd } (LdTowGJ.full Tw) d) :=
    { isT := rfl, isQ := h.isQ.trans (ldTowGJ_fullQ E _ S D.G D.Sb D.sl D.Z Tw).symm, isL := h.isL,
      laws := h.laws, dist := h.dist, john := h.john, ev := h.ev, fits := h.fits, tow := h.tow }
  have h2 := (ldTowGJ_run E S _ _ d h1).2
  { ev := h2.ev, list := h2.list, fits := h2.fits
    tail := by
      show D.T.full.OK D.t
      rw [h.isT, ← ldTowGJ_fullEnd E _ S D.G D.Sb D.sl D.Z Tw]
      exact ldEnd_full E _ _ _ h2.tail }

theorem SumPar.John.full {E P : Type} [Field E] [Fintype E] [Fintype P] {Y : SumPar E P}
    {d e t bC bZ bW : ℕ} (h : Y.John d e t bC bZ bW) :
    Y.John d e t (Fintype.card E) (Fintype.card E) (Fintype.card E) :=
  { h with
    mcaC := ldCode_mcaRowsFull _ _, mcaZ := ldCode_mcaRowsFull _ _, mcaW := ldCode_mcaRowsFull _ _ }

theorem LdTowJ.john_full {E : Type} [Field E] [Fintype E] :
    ∀ {a : LdJoint E} (T : LdTowJ a), T.John → T.full.John
  | _, .base _ _ _ _ _, h => ⟨h.1, h.2.1, h.2.2.1, ldCode_mcaAtFull _ _, h.2.2.2.2⟩
  | _, @LdTowJ.step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rest, h =>
    ⟨h.1.full, rest.full_q.symm ▸ h.2.1, rest.john_full h.2.2⟩

theorem ldTowJ_johnFull : Spec.ldTowJ_johnFull := fun _ _ _ _ T => T.john_full

theorem ldRunD_preJD : Spec.ldRunD_preJD := fun E _ _ _ D Tw d h =>
  { isT := h.isT, isQ := h.isQ, isL := h.isL, laws := h.laws, dist := h.dist, john := h.john,
    ev := h.ev, fits := h.fits
    tow := by
      have ht := h.tow
      cases Tw with
      | plain T => exact T.john_full ht
      | shaped Sh Sw d bC bZ bW e' d' rest =>
        exact ⟨ht.1, ht.2.1.full, rest.full_q.symm ▸ ht.2.2.1, rest.john_full ht.2.2.2⟩ }

end Cb
