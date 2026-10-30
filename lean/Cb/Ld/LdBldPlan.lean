-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBldPlan.lean: for the test for linear constraints (Cb/Ld/LdLin.lean) this file says which
oracle messages its three prover messages contain, and gives the four groups of oracle messages of
its plan, each with long positions, readings and a radius.

A builder for variable data: the three prover messages of the linear test in the shape of a write-up
of ours (lean/CREDITS.md; {W}, {the fold's message}, {Ω, the split's message}) from four
oracle messages; and the write-up's plan with standard groups, each at long positions
(`StdPq`,
Cb/Obj/LdObjectPpStdQ.lean), over the test with these families.

Definitions and statements with their proofs. Generic: any finite field F and any finite field E
that is an algebra over F; codes, readings, numbers are parameters. Nothing assumed.
A reading is a map from a group's long positions to those of an oracle message. W, Ω are the oracle
messages with the test's vectors w (on the columns) and ω (on the rows) (`BldLn`,
Cb/Ld/LdBldLin.lean).

Main names:
  `BldLn.four MW MU MO MS aW aU aO e' t`: what the linear test needs beside the configuration and
    the claims (`BldLn`, Cb/Ld/LdBldLin.lean): W's family and the fold's family have one member; Ω's
    family has two: true = Ω, false = the split's message s°.
  `BldPq O MW MU MO MS`, the choices of a plan: jS is the free entry of s° at which the splitting's
    mask is. On what the preamble left: the form slR, and the rows rowsA with targets tgA. inG and
    kpA say which of the preamble's messages lie in the instance's group and which are kept for the
    fourth test (each in one at least). P4 and r4A a are the fourth group's positions (not empty)
    and readings. Then four radii, and a fixed position of each of the four messages (no group reads
    a message that is no member of it: the plan's record needs a reading all the same).
  `Q.pq : StdPq (O.withBld (four ..))`: the plan's data.
  `Spec.bldPq_pos`: what each group reads of its members: the fold's group: the fold's message as it
    stands, s° along rUS; omega's: Ω as it stands, s° along rOS; the instance's: Ω as it stands, W
    along rCW, a message left along rCA; the fourth: along r4A.
  `Spec.bldPq_same`, `Spec.bldPq_n0`: see their doc comments. These two and `Spec.bldPq_pos` hold by
    definition.

Limits: this file says nothing on codes, radii, whole tests. It does not say that the readings are
even. (even: `Reading.Even`, Cb/Gen/CodeRep.lean)

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Ld.LdBldLin
import Cb.Obj.LdObjectPpStdQ
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- Ω's family -/
@[reducible] def bldOS {E : Type} (MO MS : BldM E) : Bool → BldM E
  | true => MO
  | false => MS

/-- The three prover messages in the write-up's shape. -/
@[reducible] def BldLn.four {E Col κ Y : Type} (MW MU MO MS : BldM E)
    (aW : Col → {i : MW.Ent // ¬ MW.fr i.1}) (aU : κ → {i : MU.Ent // ¬ MU.fr i.1})
    (aO : Y → {i : MO.Ent // ¬ MO.fr i.1}) (e' t : ℕ) : BldLn E Col κ Y where
  FW := { O := Unit, m := fun _ => MW }
  iW := ()
  aW := aW
  FU := { O := Unit, m := fun _ => MU }
  iU := ()
  aU := aU
  FO := { O := Bool, m := bldOS MO MS }
  iO := true
  aO := aO
  e' := e'
  t := t

section
variable {F E : Type} [Field F] [Field E] [Fintype E] [DecidableEq E] [Algebra F E]

/-- The test over the configuration, the families laid in. -/
@[reducible] def LdOL.withBld
    (O : LdOL F E) (L : BldLn E ((Fin O.Cf.X.v ⊕ Fin O.klo) → Bool) (Fin O.Cf.C₀.k) O.Y) :
    LdOL F E :=
  { O with
    e' := L.e', t := L.t
    NW := L.FW.sig, SdW := L.FW.Sd, iW := L.iW, lW := fun c => L.FW.lay.atD L.iW (L.aW c)
    NU := L.FU.sig, SdU := L.FU.Sd, iU := L.iU, lU := fun k => L.FU.lay.atD L.iU (L.aU k)
    NO := L.FO.sig, SdO := L.FO.Sd, iO := L.iO, lO := fun y => L.FO.lay.atD L.iO (L.aO y) }

/-- The choices of a plan. -/
structure BldPq (O : LdOL F E) (MW MU MO MS : BldM E) where
  jS     : {i : MS.Ent // MS.fr i.1}
  slR    : Slf E O.Cl O.S.Ent
  BM     : Type
  [finBM : Fintype BM]
  rowsA  : BM → Slf E O.Cl O.S.Ent
  tgA    : O.Cl → BM → E
  inG    : O.S.O → Prop
  [dInG  : DecidablePred inG]
  kpA    : O.S.O → Prop
  [dKpA  : DecidablePred kpA]
  cov    : ∀ a, inG a ∨ kpA a
  /-- the readings -/
  rUS : MU.P → MS.P
  rOS : MO.P → MS.P
  rCW : MO.P → MW.P
  rCA : ∀ a : O.S.O, MO.P → (O.S.om a).P
  P4  : Type
  [finP4 : Fintype P4]
  [neP4 : Nonempty P4]
  r4A : ∀ a : O.S.O, P4 → (O.S.om a).P
  /-- the radii -/
  eU : ℕ
  eO : ℕ
  eC : ℕ
  e4 : ℕ
  /-- fixed positions -/
  pW : MW.P
  pU : MU.P
  pO : MO.P
  pS : MS.P

attribute [instance] BldPq.finBM BldPq.dInG BldPq.dKpA BldPq.finP4 BldPq.neP4

namespace BldPq
variable {O : LdOL F E} {MW MU MO MS : BldM E} (Q : BldPq O MW MU MO MS)
  (aW : ((Fin O.Cf.X.v ⊕ Fin O.klo) → Bool) → {i : MW.Ent // ¬ MW.fr i.1})
  (aU : Fin O.Cf.C₀.k → {i : MU.Ent // ¬ MU.fr i.1})
  (aO : O.Y → {i : MO.Ent // ¬ MO.fr i.1}) (e' t : ℕ)

/-- the test -/
abbrev Ob (_Q : BldPq O MW MU MO MS)
    (aW : ((Fin O.Cf.X.v ⊕ Fin O.klo) → Bool) → {i : MW.Ent // ¬ MW.fr i.1})
    (aU : Fin O.Cf.C₀.k → {i : MU.Ent // ¬ MU.fr i.1})
    (aO : O.Y → {i : MO.Ent // ¬ MO.fr i.1}) (e' t : ℕ) : LdOL F E :=
  O.withBld (BldLn.four MW MU MO MS aW aU aO e' t)

/-- how each group reads every oracle message -/
def posU : ∀ o : (Q.Ob aW aU aO e' t).toC.S.O, MU.P → ((Q.Ob aW aU aO e' t).toC.S.om o).P
  | .inl (.inl (.inl a)) => fun _ => Q.rCA a Q.pO
  | .inl (.inl (.inr _)) => fun _ => Q.pW
  | .inl (.inr _) => fun x => x
  | .inr true => fun _ => Q.pO
  | .inr false => Q.rUS
def posO : ∀ o : (Q.Ob aW aU aO e' t).toC.S.O, MO.P → ((Q.Ob aW aU aO e' t).toC.S.om o).P
  | .inl (.inl (.inl a)) => Q.rCA a
  | .inl (.inl (.inr _)) => Q.rCW
  | .inl (.inr _) => fun _ => Q.pU
  | .inr true => fun x => x
  | .inr false => Q.rOS
def pos4 : ∀ o : (Q.Ob aW aU aO e' t).toC.S.O, Q.P4 → ((Q.Ob aW aU aO e' t).toC.S.om o).P
  | .inl (.inl (.inl a)) => Q.r4A a
  | .inl (.inl (.inr _)) => fun _ => Q.pW
  | .inl (.inr _) => fun _ => Q.pU
  | .inr true => fun _ => Q.pO
  | .inr false => fun _ => Q.pS

/-- The plan's data. -/
@[reducible] def pq : StdPq (Q.Ob aW aU aO e' t) where
  n₀ := (BldLn.four MW MU MO MS aW aU aO e' t).FO.lay.entF ⟨false, Q.jS⟩
  neO := Bool.false_ne_true
  four := by
    rintro (((a | a) | a) | a)
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inl rfl)
    · cases a
      · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
      · exact Or.inr (Or.inr (Or.inl rfl))
  slR := Q.slR
  BM := Q.BM
  rowsA := Q.rowsA
  tgA := Q.tgA
  inG := Q.inG
  kpA := Q.kpA
  cov := Q.cov
  PU := MU.P
  nePU := ⟨Q.pU⟩
  PO := MO.P
  nePO := ⟨Q.pO⟩
  PC := MO.P
  nePC := ⟨Q.pO⟩
  P4 := Q.P4
  posU := Q.posU aW aU aO e' t
  posO := Q.posO aW aU aO e' t
  posC := Q.posO aW aU aO e' t
  pos4 := Q.pos4 aW aU aO e' t
  eU := Q.eU
  eO := Q.eO
  eC := Q.eC
  e4 := Q.e4

end BldPq
end

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [DecidableEq E] [Algebra F E]

/-- the records that store the families give tests of this form, by definition -/
def bldPq_same : Prop :=
  (∀ (W : LdOWf F E) (L : BldLn E ((Fin W.Cf.X.v ⊕ Fin W.klo) → Bool) (Fin W.Cf.C₀.k) W.P.Rw),
    (W.withBld L).O = W.O.withBld L) ∧
  ∀ (Cf : LdCf F E) (D : LdOLd Cf)
      (L : BldLn E ((Fin Cf.X.v ⊕ Fin D.klo) → Bool) (Fin Cf.C₀.k) D.Y),
    (D.withBld L).ol = D.ol.withBld L

/-- the plan's mask entry is the senders' free entry jS (the premise nIs of `ldObjStQ_pl₁`,
Cb/Obj/LdObjectPpStdQObj.lean): by definition -/
def bldPq_n0 : Prop :=
  ∀ (O : LdOL F E) (MW MU MO MS : BldM E) (Q : BldPq O MW MU MO MS)
      (aW : ((Fin O.Cf.X.v ⊕ Fin O.klo) → Bool) → {i : MW.Ent // ¬ MW.fr i.1})
      (aU : Fin O.Cf.C₀.k → {i : MU.Ent // ¬ MU.fr i.1})
      (aO : O.Y → {i : MO.Ent // ¬ MO.fr i.1}) (e' t : ℕ),
    (Q.pq aW aU aO e' t).n₀ = (BldLn.four MW MU MO MS aW aU aO e' t).FO.lay.entF ⟨false, Q.jS⟩

/-- What each group reads of its members. -/
def bldPq_pos : Prop :=
  ∀ (O : LdOL F E) (MW MU MO MS : BldM E) (Q : BldPq O MW MU MO MS)
      (aW : ((Fin O.Cf.X.v ⊕ Fin O.klo) → Bool) → {i : MW.Ent // ¬ MW.fr i.1})
      (aU : Fin O.Cf.C₀.k → {i : MU.Ent // ¬ MU.fr i.1})
      (aO : O.Y → {i : MO.Ent // ¬ MO.fr i.1}) (e' t : ℕ),
    ((Q.pq aW aU aO e' t).posU (.inl (.inr ())) = fun x => x) ∧
    (Q.pq aW aU aO e' t).posU (.inr false) = Q.rUS ∧
    ((Q.pq aW aU aO e' t).posO (.inr true) = fun x => x) ∧
    (Q.pq aW aU aO e' t).posO (.inr false) = Q.rOS ∧
    ((Q.pq aW aU aO e' t).posC (.inr true) = fun x => x) ∧
    (Q.pq aW aU aO e' t).posC (.inl (.inl (.inr ()))) = Q.rCW ∧
    (∀ a, (Q.pq aW aU aO e' t).posC (.inl (.inl (.inl a))) = Q.rCA a) ∧
    ∀ a, (Q.pq aW aU aO e' t).pos4 (.inl (.inl (.inl a))) = Q.r4A a

end
end Spec

theorem bldPq_n0 (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E]
    [DecidableEq E] [Algebra F E] : Spec.bldPq_n0 F E :=
  fun _ _ _ _ _ _ _ _ _ _ _ => rfl

theorem bldPq_pos (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E]
    [DecidableEq E] [Algebra F E] : Spec.bldPq_pos F E :=
  fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl⟩

theorem bldPq_same (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E]
    [DecidableEq E] [Algebra F E] : Spec.bldPq_same F E :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

end Cb
