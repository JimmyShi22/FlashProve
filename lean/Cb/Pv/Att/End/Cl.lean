-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/End/Cl.lean: the ledger of the claims that the verifier of an attention sub-proof keeps of
the sub-proof's own rounds, and the forms of the late entries, both from the chain's last statement
alone; the ledger's pull-back gives what the chain owes at its end.

Definitions, statements and proofs. The chain is that of Cb/Pv/Att/OwnSteps.lean. Its last statement
is made of a run u: what was sent, drawn and put out, by name (P.Run in Cb/Pv/Att/OwnLast.lean).

Main names:
  EndLay P J₂: the letters of the end: the places cellJ of the cells among the early entries, the
    sizes ls and lmS of the tables' blocks, and the names of the late entries.
  planes_agree: the last lmS coordinates of the inner points of the four families of planes are the
    same, if the first two calls have the same size.
  attTb L u: the weights of the 21 tables. The six tables at the lookup's point take it from the
    first statement in u; a table of a sumcheck takes challenges and point from that sumcheck's
    output statement in u.
  attA L u: the forms of the late entries.
  ownCl L Q u: the ledger, in the order in which the verifier adds the claims: the planes of the
    two plane messages; for each unit of the scores its planes, its row maxima, its row and its end
    values; the scalars of the division, the row and the end values of the denominator times the
    output; the join, on the hidden values of the named scalars; the line on the two sums of the
    value product, with their rows and end values; the pairs' scalars; the row and the first end
    values of the score at the index; the row and the end values of the key at the index; the row
    and the end values of the bits.
  Fits L: what is asked of the letters: how the cells are read, sizes, the names, and that the
    three free linear claims of P are those of Cb/Pv/Att/End/Hid.lean.
  att_last: if the pull-backs of all claims of ownCl hold of the entries of m, and Dn holds of the
    first statement, the chain's Ch.Last holds of the last statement made of u, and m.
  att_hEnd: the same in the form of the premise hEnd of sub_link (Cb/Pv/Att/Link.lean), for a ledger
    whose pull-back gives the pull-backs of ownCl's claims; holds_of_mem: so it is if the ledger
    holds ownCl's claims among others.

Limits: those of the files that this one imports. That the ledger is the programs' is not said here.
The lookup's other claims (its rows, and three on its planes) are not in ownCl: att_hEnd takes any
ledger that gives ownCl's claims, and takes as given that this ledger gives Dn and that B₀ gives
what rides: so of the three parts of its conclusion it proves the third, the chain's bill. An output
statement carries a public state of its own: the tables' weights and the reading forms take the
challenges from there; on the output of a run that state is the claim's. So that ownCl is the
programs' ledger can hold at runs alone (Cb/Pv/Att/End/ClRan.lean has the premise at runs). That the
forms attA are what the smallness test's block ties the late entries to is not shown here. Nothing
on an honest prover or on hiding.


-/
import Cb.Pv.Att.OwnLast
import Cb.Pv.Att.End.Hid
import Cb.Pv.Att.End.LastOut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att.End
open Iop Prob Cb IOR TWhole Cb.Sub Finset Blocks
open Inst.Model.AttSeg

/-- The last lmS coordinates of the inner points of the four families of planes are the same. -/
theorem planes_agree {E : Type} [Field E] (D : Dim) (C : Calls) (lmS : ℕ) (z : ℕ → E)
    (h01 : C.a 0 = C.a 1) (hla : ∀ u : Inst.Model.AttSeg.Fam, IsPlane u → u.l D ≤ C.a u.call)
    (hl : ∀ u : Inst.Model.AttSeg.Fam, IsPlane u → lmS ≤ u.l D) (u : Inst.Model.AttSeg.Fam)
    (hu : IsPlane u) :
    eqN lmS (u.l D - lmS) (inn D C z u) = eqN lmS (D.lM - lmS) (inn D C z .m1) := by
  have hz : C.zC 1 z = C.zC 0 z := by
    funext t
    unfold Calls.zC Calls.e
    rw [h01]
  have key : ∀ v : Inst.Model.AttSeg.Fam, IsPlane v →
      C.zC v.call z = C.zC 0 z ∧ C.a v.call = C.a 0 := by
    intro v hv
    cases v with
    | m1 => exact ⟨rfl, rfl⟩
    | d1 => exact ⟨rfl, rfl⟩
    | m2 => exact ⟨hz, h01.symm⟩
    | d2 => exact ⟨hz, h01.symm⟩
    | w3 => exact hv.elim
    | x3 => exact hv.elim
    | f4 => exact hv.elim
  funext X
  refine eqN_agree (fun k hk => ?_) X
  have a1 := hla u hu
  have a2 := hl u hu
  have b1 := hla .m1 trivial
  have b2 := hl .m1 trivial
  have b1' : D.lM ≤ C.a 0 := b1
  have b2' : lmS ≤ D.lM := b2
  unfold inn sh
  rw [(key u hu).1]
  show C.zC 0 z (C.a u.call - u.l D + (u.l D - lmS + k)) =
    C.zC 0 z (C.a 0 - D.lM + (D.lM - lmS + k))
  rw [(key u hu).2] at a1 ⊢
  congr 1
  omega

section Own
variable {E M X : Type} [Field E] [Fintype E] (P : OwnPar E M X)

/-- The letters of the end. -/
structure EndLay (J₂ : Type) where
  /-- the places of the cells among the early entries -/
  cellJ : Raw → P.J
  /-- a table on blocks of features has 2^ls features in a block -/
  ls : ℕ
  /-- a table on the regions' entries has 2^lmS cells in an entry -/
  lmS : ℕ
  /-- the names of the late entries -/
  Y : LateLay AttTab J₂

variable {P} {J₂ : Type} [Fintype J₂] [DecidableEq J₂] (L : EndLay P J₂) (Q : JoinLay P)

instance dec_uM : DecidableEq P.uM.T.J := P.decJ
instance dec_uD : DecidableEq P.uD.T.J := P.decJ
instance dec_sE : DecidableEq P.sE.T.J := P.decJ
instance dec_sVM : DecidableEq P.sVM.T.J := P.decJ
instance dec_sVD : DecidableEq P.sVD.T.J := P.decJ
instance dec_sF : DecidableEq P.sF.T.J := P.decJ
instance dec_sD : DecidableEq P.sD.T.J := P.decJ
instance dec_sH : DecidableEq P.sH.T.J := P.decJ

/-! ### The tables' weights -/

/-- The lookup's end point. -/
def zT (u : P.Run) : ℕ → E := P.zOf u.x

/-- The weights of the tables. -/
noncomputable def attTb (u : P.Run) : AttTab → TabW E
  | .tA => .col (eqN L.lmS (P.D.lM - L.lmS) (inn P.D P.C (zT u) .m1))
  | .tMm => .row (psiRow P.D (zP P.D P.C (zT u)) (zs P.D P.C (zT u)) (zi' P.D P.C (zT u)))
  | .tMd => .row (eqT P.D (cat (P.D.lP + 1) (zID P.D P.C (zT u)) (zi' P.D P.C (zT u))))
  | .hW => .row (eqT P.D (yi P.D P.C (zT u)))
  | .hX => .row (eqT P.D (xi P.D P.C (zT u)))
  | .tO => .long (eqN L.ls (P.D.ln - L.ls) (yn P.D P.C (zT u))) (eqT P.D (yi P.D P.C (zT u)))
  | .tQm => .long
      (eqN L.ls (P.D.ln - L.ls) (sh (ptN P.uM.T u.oM) (P.D.lg + P.D.lP + (P.D.lP + 1))))
      (psiRow P.D (sh (ptN P.uM.T u.oM) P.D.lg) (sh (ptN P.uM.T u.oM) (P.D.lg + P.D.lP))
        (zi' P.D P.C (Pub.z u.oM.st)))
  | .tKm => .long
      (eqN L.ls (P.D.ln - L.ls) (sh (ptN P.uM.T u.oM) (P.D.lg + P.D.lP + (P.D.lP + 1))))
      (psiCol P.D (sh (ptN P.uM.T u.oM) P.D.lg) (sh (ptN P.uM.T u.oM) (P.D.lg + P.D.lP))
        (zj' P.D P.C (Pub.z u.oM.st)))
  | .tQd => .long (eqN L.ls (P.D.ln - L.ls) (sh (ptN P.uD.T u.oD) (P.D.lg + (P.D.lP + 1))))
      (psiDiag P.D (sh (ptN P.uD.T u.oD) P.D.lg) (zi' P.D P.C (Pub.z u.oD.st)))
  | .tKd => .long (eqN L.ls (P.D.ln - L.ls) (sh (ptN P.uD.T u.oD) (P.D.lg + (P.D.lP + 1))))
      (psiDiag P.D (sh (ptN P.uD.T u.oD) P.D.lg) (zj' P.D P.C (Pub.z u.oD.st)))
  | .hE => .row (eqT P.D (sh (ptN P.sE.T u.oE) P.D.lg))
  | .qO => .long (eqN L.ls (P.D.ln - L.ls) (yn P.D P.C (Pub.z u.oE.st)))
      (eqT P.D (sh (ptN P.sE.T u.oE) P.D.lg))
  | .tVM => .col (eqN L.lmS (P.D.lM - L.lmS) (ptBelow P.D P.C u.oVM.st (ptN P.sVM.T u.oVM)))
  | .qVM => .long (eqN L.ls (P.D.ln - L.ls) (yn P.D P.C (Pub.z u.oVM.st)))
      (psiCol P.D (sh (ptN P.sVM.T u.oVM) P.D.lg) (sh (ptN P.sVM.T u.oVM) (P.D.lg + P.D.lP))
        (sh (ptN P.sVM.T u.oVM) (P.D.lg + P.D.lP + (P.D.lP + 1))))
  | .tVD => .col (eqN L.lmS (P.D.lD - L.lmS) (ptOn P.D P.C u.oVD.st (ptN P.sVD.T u.oVD)))
  | .qVD => .long (eqN L.ls (P.D.ln - L.ls) (yn P.D P.C (Pub.z u.oVD.st)))
      (eqT P.D (sh (ptN P.sVD.T u.oVD) P.D.lg))
  | .hT => .row (eqT P.D (P.pubZ u.z).ti)
  | .qF => .long (eqN L.ls (P.D.ln - L.ls) (sh (ptN P.sF.T u.oF) (P.D.lT + P.D.lg)))
      (eqT P.D (ptN P.sF.T u.oF))
  | .qKx => .long (eqN L.ls (P.D.ln - L.ls) (Pub.fn (Prod.fst u.oK.st)))
      (eqT P.D (ptN P.sD.T u.oK))
  | .hPi => .row (eqT P.D (sh (ptN P.sD.T u.oK) (P.D.lT + P.D.lg)))
  | .hR2 => .row (eqT P.D (ptN P.sH.T u.oH))

/-- The forms of the late entries. -/
noncomputable def attA (u : P.Run) : J₂ → Aff E P.J :=
  lateA L.cellJ P.D L.ls L.lmS L.Y (attTb L u)

/-! ### The ledger, part by part -/

/-- The scalars in front of the first unit's sumcheck. -/
def clM0 (u : P.Run) : TWhole.Ledger E (P.J ⊕ J₂) :=
  linCl P.D P.C L.ls L.lmS L.Y nameM u.rM P.kM (zT u)
/-- The unit below the diagonal. -/
noncomputable def clM (u : P.Run) : TWhole.Ledger E (P.J ⊕ J₂) :=
  plainCl P.uM.T u.oM (pairs P.D.nb)
    (pick (rA6b P.D L.ls L.Y (ptN P.uM.T u.oM)) (rB6b P.D L.ls L.Y (ptN P.uM.T u.oM)))
/-- The scalars of the unit on the diagonal. -/
def clD0 (u : P.Run) : TWhole.Ledger E (P.J ⊕ J₂) :=
  linCl P.D P.C L.ls L.lmS L.Y nameD u.rD P.kD (zT u)
/-- The unit on the diagonal. -/
noncomputable def clD (u : P.Run) : TWhole.Ledger E (P.J ⊕ J₂) :=
  plainCl P.uD.T u.oD (pairs P.D.nb)
    (pick (rA6d P.D L.ls L.Y (ptN P.uD.T u.oD)) (rB6d P.D L.ls L.Y (ptN P.uD.T u.oD)))
/-- The scalars of the division. -/
def clE0 (u : P.Run) : TWhole.Ledger E (P.J ⊕ J₂) :=
  linCl P.D P.C L.ls L.lmS L.Y (nameE P.D) u.rE P.kE (zT u)
/-- The denominator times the output. -/
noncomputable def clE (u : P.Run) : TWhole.Ledger E (P.J ⊕ J₂) :=
  plainCl P.sE.T u.oE (pairs P.D.nb)
    (pick (rA8 P.D L.Y (ptN P.sE.T u.oE)) (rB8 P.D P.C L.ls L.Y u.oE.st (ptN P.sE.T u.oE)))
/-- The join: the lookup's claim on the calls' key vectors, on the hidden values of the named
scalars. -/
def joinF (u : P.Run) : TWhole.Form E (P.J ⊕ J₂) :=
  (joinA (Q.q u.x) (kfA (scl := Q.scl) P.D P.C (P.pub0 u.y0) (hidA P u)) (liftA (Q.ce u.x))).claim
/-- The line on the two sums of the value product: the two hidden sums add up to the hidden ACC plus
the drawn element times the hidden ZC. -/
def lineF (u : P.Run) : TWhole.Form E (P.J ⊕ J₂) :=
  (aSub (aAdd (hidF (u.rV 0) (P.kV 0)) (hidF (u.rV 1) (P.kV 1)))
    (aAdd (hidF (u.rE P.iACC) (P.kE P.iACC))
      (aSmul u.th (hidF (u.rE P.iZC) (P.kE P.iZC))))).claim
/-- The value product below the diagonal. -/
noncomputable def clVM (u : P.Run) : TWhole.Ledger E (P.J ⊕ J₂) :=
  plainCl P.sVM.T u.oVM (pairs P.D.nb)
    (pick (rA11 P.D P.C L.lmS L.Y u.oVM.st (ptN P.sVM.T u.oVM))
      (rB11 P.D P.C L.ls L.Y u.oVM.st (ptN P.sVM.T u.oVM)))
/-- The value product on the diagonal. -/
noncomputable def clVD (u : P.Run) : TWhole.Ledger E (P.J ⊕ J₂) :=
  plainCl P.sVD.T u.oVD (pairs P.D.nb)
    (pick (rA12 P.D P.C L.lmS L.Y u.oVD.st (ptN P.sVD.T u.oVD))
      (rB12 P.D P.C L.ls L.Y u.oVD.st (ptN P.sVD.T u.oVD)))
/-- The pairs' scalars. -/
noncomputable def clM6 (u : P.Run) : TWhole.Ledger E (P.J ⊕ J₂) :=
  (List.finRange P.D.nb).map fun i => linF (u.s i) (P.kF i) (rM6 P.D L.Y (P.pubZ u.z) i.val)
/-- The score at the index: its row and its first end values. -/
noncomputable def clF (u : P.Run) : TWhole.Ledger E (P.J ⊕ J₂) :=
  plainCl P.sF.T u.oF (firsts P.D.nb) fun a => rA16 P.D L.ls L.Y (ptN P.sF.T u.oF) a.1.val
/-- The key at the index. -/
noncomputable def clK (u : P.Run) : TWhole.Ledger E (P.J ⊕ J₂) :=
  plainCl P.sD.T u.oK (ends18 (size18 P.D))
    (keyR P.D L.ls L.Y (Prod.fst u.oK.st) (ptN P.sD.T u.oK))
/-- The bits. -/
noncomputable def clH (u : P.Run) : TWhole.Ledger E (P.J ⊕ J₂) :=
  plainCl P.sH.T u.oH (pairs P.D.nb) (bitsR P.D L.Y P.rd (fun _ _ => 0) P.kap P.cH P.wH u.oH)

/-- The verifier's claims of the sub-proof's own rounds. -/
noncomputable def ownCl (u : P.Run) : TWhole.Ledger E (P.J ⊕ J₂) :=
  clM0 L u ++ (clM L u ++ (clD0 L u ++ (clD L u ++ (clE0 L u ++ (clE L u ++ (joinF Q u :: lineF u ::
    (clVM L u ++ (clVD L u ++ (clM6 L u ++ (clF L u ++ (clK L u ++ clH L u)))))))))))

/-! ### What is asked of the letters -/

/-- What is asked of the letters. -/
structure Fits : Prop where
  /-- the cells are read off the entries at the places cellJ -/
  rd : ∀ m, P.rd m = rdOf L.cellJ m
  ls : L.ls ≤ P.D.ln
  lmS : ∀ u : Inst.Model.AttSeg.Fam, IsPlane u → L.lmS ≤ u.l P.D
  a01 : P.C.a 0 = P.C.a 1
  la : ∀ u : Inst.Model.AttSeg.Fam, IsPlane u → u.l P.D ≤ P.C.a u.call
  kap : P.D.lT ≤ 2 ^ P.kap
  /-- two plane messages: the places of the named scalars (placeK, nameM) are meant for that -/
  npl : P.npl = 2
  /-- the names that the forms read are names of late entries -/
  gLin : LinGood P.D L.ls L.lmS L.Y
  g6b : Good6b P.D L.ls L.Y
  g6d : Good6d P.D L.ls L.Y
  g8 : Good8 P.D L.ls L.Y
  g11 : Good11 P.D L.ls L.lmS L.Y
  g12 : Good12 P.D L.ls L.lmS L.Y
  gM : GoodM P.D L.Y
  g16 : Good16 P.D L.ls L.Y
  g18 : Good18 P.D L.ls L.Y
  gH : GoodH P.D L.Y
  /-- the three free linear claims are those of Cb/Pv/Att/End/Hid.lean -/
  LM : ∀ x r m, P.LM x r m ↔ LMat P x r m
  LD : ∀ x r m, P.LD x r m ↔ LDat P x r m
  LE : ∀ x r m, P.LE x r m ↔ LEat P Q x r m

variable {L Q}

omit [Fintype J₂] [DecidableEq J₂] in
/-- The tables at the lookup's point have the weights that the linear claims' forms ask for. -/
theorem linTabs (F : Fits L Q) (u : P.Run) : LinTabs P.D P.C L.ls L.lmS (attTb L u) (zT u) where
  tA := fun v hv => by
    show TabW.col _ = TabW.col _
    rw [planes_agree P.D P.C L.lmS (zT u) F.a01 F.la F.lmS v hv]
  tMm := rfl
  tMd := rfl
  hW := rfl
  hX := rfl
  tO := rfl

/-- The ledger's pull-back gives what the chain owes at its end. -/
theorem att_last (Mn : Means E P.D P.C P.kap) (F : Fits L Q) (Dn : X → M → Prop) (u : P.Run) (m : M)
    (hDn : Dn u.x m)
    (h : ∀ f ∈ ownCl L Q u, (pullF (attA L u) f).Holds (P.msg m)) :
    (P.own Mn).ch.Last Dn (P.endOf Mn u) m := by
  have hR := fun (a : TWhole.Ledger E (P.J ⊕ J₂)) {b : TWhole.Ledger E (P.J ⊕ J₂)}
      {f : TWhole.Form E (P.J ⊕ J₂)}
    (hf : f ∈ b) => List.mem_append_right a hf
  have ht : ∀ m', P.tOf m' = rdOf L.cellJ (P.msg m') := fun m' => F.rd (P.msg m')
  have k1 : ∀ f ∈ clM0 L u, (pullF (attA L u) f).Holds (P.msg m) := fun f hf =>
    h f (List.mem_append_left _ hf)
  have k2 : ∀ f ∈ clM L u, (pullF (attA L u) f).Holds (P.msg m) := fun f hf =>
    h f (hR _ (List.mem_append_left _ hf))
  have k3 : ∀ f ∈ clD0 L u, (pullF (attA L u) f).Holds (P.msg m) := fun f hf =>
    h f (hR _ (hR _ (List.mem_append_left _ hf)))
  have k4 : ∀ f ∈ clD L u, (pullF (attA L u) f).Holds (P.msg m) := fun f hf =>
    h f (hR _ (hR _ (hR _ (List.mem_append_left _ hf))))
  have k5 : ∀ f ∈ clE0 L u, (pullF (attA L u) f).Holds (P.msg m) := fun f hf =>
    h f (hR _ (hR _ (hR _ (hR _ (List.mem_append_left _ hf)))))
  have k6 : ∀ f ∈ clE L u, (pullF (attA L u) f).Holds (P.msg m) := fun f hf =>
    h f (hR _ (hR _ (hR _ (hR _ (hR _ (List.mem_append_left _ hf))))))
  have kJ : (pullF (attA L u) (joinF Q u)).Holds (P.msg m) :=
    h _ (hR _ (hR _ (hR _ (hR _ (hR _ (hR _ List.mem_cons_self))))))
  have k7 : (pullF (attA L u) (lineF u)).Holds (P.msg m) :=
    h _ (hR _ (hR _ (hR _ (hR _ (hR _ (hR _ (List.mem_cons_of_mem _ List.mem_cons_self)))))))
  have hC := fun {b : TWhole.Ledger E (P.J ⊕ J₂)} {f : TWhole.Form E (P.J ⊕ J₂)} (hf : f ∈ b) =>
    hR (clM0 L u) (hR (clM L u) (hR (clD0 L u) (hR (clD L u) (hR (clE0 L u) (hR (clE L u)
      (List.mem_cons_of_mem (joinF Q u) (List.mem_cons_of_mem (lineF u) hf)))))))
  have k8 : ∀ f ∈ clVM L u, (pullF (attA L u) f).Holds (P.msg m) := fun f hf =>
    h f (hC (List.mem_append_left _ hf))
  have k9 : ∀ f ∈ clVD L u, (pullF (attA L u) f).Holds (P.msg m) := fun f hf =>
    h f (hC (hR _ (List.mem_append_left _ hf)))
  have k10 : ∀ f ∈ clM6 L u, (pullF (attA L u) f).Holds (P.msg m) := fun f hf =>
    h f (hC (hR _ (hR _ (List.mem_append_left _ hf))))
  have k11 : ∀ f ∈ clF L u, (pullF (attA L u) f).Holds (P.msg m) := fun f hf =>
    h f (hC (hR _ (hR _ (hR _ (List.mem_append_left _ hf)))))
  have k12 : ∀ f ∈ clK L u, (pullF (attA L u) f).Holds (P.msg m) := fun f hf =>
    h f (hC (hR _ (hR _ (hR _ (hR _ (List.mem_append_left _ hf))))))
  have k13 : ∀ f ∈ clH L u, (pullF (attA L u) f).Holds (P.msg m) := fun f hf =>
    h f (hC (hR _ (hR _ (hR _ (hR _ (hR _ hf))))))
  have lin : ∀ (name : ℕ → Option KSc) (_ : ∀ j k, name j = some k → LinK P.D k) {n : ℕ}
      (r : Fin n → E) (kk : Fin n → P.J) (x : Seen E X) (_ : x.1 = u.x)
      (_ : ∀ f ∈ linCl (J₁ := P.J) P.D P.C L.ls L.lmS L.Y name r kk (zT u),
        (pullF (attA L u) f).Holds (P.msg m)),
      RuleAt P.D P.C name r kk (P.pub0 x) (P.tOf m) (P.msg m) := by
    intro name hn n r kk x hx hf
    rw [ht m]
    have hz : (P.pub0 x).z = zT u := by
      show P.zOf x.1 = P.zOf u.x
      rw [hx]
    refine linCl_rule L.cellJ P.D P.C L.ls L.lmS L.Y (attTb L u) (P.pub0 x) (P.msg m) F.ls F.lmS
      (by rw [hz]; exact linTabs F u) F.gLin name hn r kk (by rw [hz]; exact hf)
  have oM := out6b P.D P.C L.ls L.lmS L.Y (attTb L u) L.cellJ P.rd F.rd _ (P.cAt .s6b)
    (P.wAt .s6b) u.oM F.ls ⟨rfl, rfl⟩ F.g6b (P.msg m) k2
  have oD := out6d P.D P.C L.ls L.lmS L.Y (attTb L u) L.cellJ P.rd F.rd _ (P.cAt .s6d)
    (P.wAt .s6d) u.oD F.ls ⟨rfl, rfl⟩ F.g6d (P.msg m) k4
  have oE := out8 P.D P.C L.ls L.lmS L.Y (attTb L u) L.cellJ P.rd F.rd _ (P.cAt .s8)
    (P.wAt .s8) u.oE F.ls ⟨rfl, rfl⟩ F.g8 (P.msg m) k6
  have oVM := out11 P.D P.C L.ls L.lmS L.Y (attTb L u) L.cellJ P.rd F.rd _ (P.cAt .s11)
    (P.wAt .s11) u.oVM F.ls (F.lmS .m1 trivial) ⟨rfl, rfl⟩ F.g11 (P.msg m) k8
  have oVD := out12 P.D P.C L.ls L.lmS L.Y (attTb L u) L.cellJ P.rd F.rd _ (P.cAt .s12)
    (P.wAt .s12) u.oVD F.ls (F.lmS .d1 trivial) ⟨rfl, rfl⟩ F.g12 (P.msg m) k9
  have oF := score16 P.D P.C L.ls L.lmS L.Y (attTb L u) L.cellJ P.rd F.rd _ (P.cAt .s16)
    (P.wAt .s16) u.oF F.ls ⟨rfl⟩ F.g16 (P.msg m) k11
  have oK := out18 P.D L.ls L.lmS L.Y (attTb L u) L.cellJ P.rd F.rd (fun _ _ => 0) Prod.fst
    Prod.snd P.w18 P.c18 u.oK F.ls ⟨rfl, rfl⟩ F.g18 (P.msg m) k12
  have oH := outBits P.D L.ls L.lmS L.Y (attTb L u) L.cellJ P.rd F.rd (fun _ _ => 0) P.kap F.kap
    P.cH P.wH u.oH ⟨rfl⟩ F.gH (P.msg m) k13
  have hline : P.sVM.L (u.yE, u.th) u.rV m := by
    have e := (claim_pull (attA L u) _ (P.msg m)).mp k7
    rw [val_aSub, val_aAdd, val_aAdd, val_aSmul, val_hidF, val_hidF, val_hidF, val_hidF,
      sub_eq_zero] at e
    exact e
  have hj : joinVal (Q.q u.x) (KF (scl := Q.scl) P.D P.C (P.pub0 u.y0) (hidV P u.y0 u.rE m))
      ((Q.ce u.x).val (P.msg m)) = 0 := by
    have e := (claim_pull (attA L u) _ (P.msg m)).mp kJ
    rw [val_joinA, val_liftA] at e
    simp only [val_kfA, val_hidA] at e
    exact e
  have hlF : P.lF u.z u.s m := fun i => by
    rw [ht m]
    exact m6 P.D L.ls L.lmS L.Y (attTb L u) L.cellJ (P.pubZ u.z) ⟨rfl⟩ F.gM i.val i.isLt (u.s i)
      (P.kF i) (P.msg m) (k10 _ (List.mem_map_of_mem (List.mem_finRange i)))
  refine (P.own_last_raw Mn Dn u m).mpr
    ⟨⟨⟨⟨⟨⟨⟨⟨⟨hDn, (F.LM _ _ _).mpr (lin nameM (fun _ _ => nameM_lin P.D) u.rM P.kM _ rfl k1), oM⟩,
      (F.LD _ _ _).mpr (lin nameD (fun _ _ => nameD_lin P.D) u.rD P.kD _ rfl k3), oD⟩,
      (F.LE _ _ _).mpr ⟨lin (nameE P.D) (fun _ _ => nameE_lin P.D) u.rE P.kE _ rfl k5, hj⟩, oE⟩,
      hline, oVM⟩, trivial, oVD⟩, hlF⟩, trivial, oF.1, fun a ha => ?_⟩, trivial, oK⟩, trivial, oH⟩
  obtain ⟨i, b⟩ := a
  cases b
  · exact oF.2 i
  · exact absurd rfl (ha i)

/-- A ledger that holds the claims of the own rounds among others gives their pull-backs. -/
theorem holds_of_mem (u : P.Run) (cl : TWhole.Ledger E (P.J ⊕ J₂)) (hm : ∀ f ∈ ownCl L Q u, f ∈ cl)
    (m : M) (h : TWhole.Ledger.Holds (pullL (attA L u) cl) (P.msg m)) :
    ∀ f ∈ ownCl L Q u, (pullF (attA L u) f).Holds (P.msg m) := fun f hf =>
  h _ (List.mem_map_of_mem (hm f hf))

/-- The premise hEnd of the link's statement, for a ledger cl whose pull-back gives the pull-backs
of the claims of the own rounds (hcl; so it is if cl holds these claims among others: holds_of_mem).
hDn: that ledger, with what B₀ says, gives Dn of the first statement. hA0: B₀
gives what rides. -/
theorem att_hEnd (Mn : Means E P.D P.C P.kap) (F : Fits L Q) {Kc X0 Wp : Type} {Ex : ExtSpec}
    (A0 : Rels Kc X0 Ex (M × Wp)) (pr : X → X0) (Dn : X → M → Prop)
    (B₀ : Rels Kc (P.own Mn).ch.End Ex (M × Wp))
    (cl : (P.own Mn).ch.End → TWhole.Ledger E (P.J ⊕ J₂))
    (hcl : ∀ e y w, A0.on (pr ((P.own Mn).ch.back e), y) → B₀.relR (e, y) w →
      TWhole.Ledger.Holds (pullL (attA L (P.runOf Mn e)) (cl e)) (P.msg w.1) →
        ∀ f ∈ ownCl L Q (P.runOf Mn e), (pullF (attA L (P.runOf Mn e)) f).Holds (P.msg w.1))
    (hA0 : ∀ e y w, A0.on (pr ((P.own Mn).ch.back e), y) → B₀.relR (e, y) w →
      A0.relR (pr ((P.own Mn).ch.back e), y) w)
    (hDn : ∀ e y w, A0.on (pr ((P.own Mn).ch.back e), y) → B₀.relR (e, y) w →
      TWhole.Ledger.Holds (pullL (attA L (P.runOf Mn e)) (cl e)) (P.msg w.1) →
        Dn ((P.own Mn).ch.back e) w.1) :
    ∀ e y w, A0.on (pr ((P.own Mn).ch.back e), y) → B₀.relR (e, y) w →
      TWhole.Ledger.Holds (pullL (attA L (P.runOf Mn e)) (cl e)) (P.msg w.1) →
        A0.relR (pr ((P.own Mn).ch.back e), y) w ∧ (P.own Mn).ch.Last Dn e w.1 := by
  intro e y w ho hB hL
  refine ⟨hA0 e y w ho hB, ?_⟩
  rw [P.own_last_at Mn Dn e w.1]
  refine att_last Mn F Dn (P.runOf Mn e) w.1 ?_ (hcl e y w ho hB hL)
  have h1 := hDn e y w ho hB hL
  rw [← P.endOf_runOf Mn e, P.back_endOf Mn] at h1
  exact h1

end Own

end Cb.Pv.Att.End

#print axioms Cb.Pv.Att.End.planes_agree
#print axioms Cb.Pv.Att.End.att_last
#print axioms Cb.Pv.Att.End.att_hEnd
