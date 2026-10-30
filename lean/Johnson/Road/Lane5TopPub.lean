-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5TopPub.lean

The theorems of Lane5Top.lean and Lane5TopL.lean, and their witnesses, with the public hypotheses
tied to one parameter file. Lane5Top.lean is on the plain head, which the programs do not run;
Lane5TopL.lean is on the head with the cost ledger, which they run (Lane5Ledger.lean).

In Lane5Top.lean eleven public hypotheses stand on nine free letters. Here all letters are fields of
ONE value X, the public part that the verifier's own function "publicOf" returns on the parameter
file and the scale file, and the eleven follow from three hypotheses:
* "publicOf pol KL lay = .ok X": the verifier's function has returned;
* "Hd.PublicAt X.P" (HeadL5Pub.lean): 46 numbers and two switches of the parameter file, as scanned,
  are the reference's. It is decidable;
* "Model.fileWords KL = scalesKF.toArray": the words of the scale file are the reference's.
The letters: the layers' shape is "layerShape X.P", their layout "X.y", the scale words
"X.layers.sc", the head's shape "X.hS", its layout "X.HLy", the final norm "Hd.npOf X.hS", the
attention link's shape of group g "Hd.shapeA X g".

Like the files that it joins, this file is a translation, not a step towards a proof file.

Main theorems:
* "npOf_public", "lawful_of_at": the final norm's numbers and "the table is lawful", from the three.
* "reply_of_public": the plain head: Ords at these letters, r = 1,023 and e = 1,024 give the reply.
* "under_of_public": the head with the cost ledger: OrdsL at these letters, a policy within its
  bounds and r < e give "true under its policy".
* "ords_met_public", "ordsL_met_public": under the three hypotheses the two bundles have a value, at
  the attention shapes that the verifier's own function makes.

Not claimed as a theorem: that any parameter file meets the three hypotheses. Runs hold them at the
full-size example's lines and scale words, with no layout file: FormsKeysRunKFull.lean (publicOf
returns), FormsKeysRunK.lean (the words), Lane5PublicRun.lean (PublicAt, of
the X.P that publicOf returns). Not claimed: that a proof file which a verifier accepts has matrices
with Ords or OrdsL; all that the imported files do not claim.
-/
import Johnson.Road.Lane5TopLMet
import Johnson.Road.HeadL5All
import Johnson.Road.FormsKeysLawP

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model

open OnBytes.Model.Verify (publicOf layerShape)

variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}

/-- The final norm's three numbers are the reference's. -/
theorem npOf_public (h : publicOf pol KL lay = .ok X) (A : Hd.PublicAt X.P) :
    Hd.npOf X.hS = nfKF := by
  obtain ⟨P, y, hpl, eP, ey, eS, -, hl, -⟩ := Hd.public_parts h
  have eS' : X.hS = Model.Verify.headShape X.P X.y := by rw [eS, eP, ey]
  have n := Hd.norms_of_at A
  rw [eS']
  show (⟨X.P.h.MF, X.P.h.KF, (X.P.h.epsF : ℤ)⟩ : NormPar) = ⟨44, 30, 53687⟩
  rw [n.2.2.1, n.2.2.2.1, n.2.2.2.2]
  rfl

/-- **The table of scales is lawful.** -/
theorem lawful_of_at (h : publicOf pol KL lay = .ok X) (A : Hd.PublicAt X.P)
    (hW : Model.fileWords KL = scalesKF.toArray) :
    (scalesOf (layerShape X.P) X.layers.sc (Hd.npOf X.hS)).Lawful :=
  lawful_public h hW (Hd.p4_of_at A) (A.num 2) (A.num 41) (A.num 42) (npOf_public h A)

/-- Attention's four public hypotheses, for each of the twelve groups. -/
theorem att_of_at' (h : publicOf pol KL lay = .ok X) (A : Hd.PublicAt X.P) {g : ℕ}
    (hg : g < 12) :
    AttSized (Hd.shapeA X g) ∧
      ((scalesOf (layerShape X.P) X.layers.sc (Hd.npOf X.hS)).kap (4 * g)).sh =
        (Hd.shapeA X g).cf.sh.getD 0 0 ∧
      (∀ ι : ℕ, ι < (Hd.shapeA X g).u0 →
        (((Hd.shapeA X g).Tt.getD ι 0 : ℕ) : ℤ) = tbRef.Exp ι) ∧
      7200 ≤ (Hd.shapeA X g).kAs / (Hd.shapeA X g).cf.NAs * (Hd.shapeA X g).cf.NAs :=
  att_public h (Hd.p4_of_at A) (Hd.fillRef_of_at A (Hd.public_of_publicOf h A))
    (by rw [(Hd.public_of_publicOf h A).groups]; exact hg) hg (layerShape X.P) (Hd.npOf X.hS)

/-- **The plain head, at one parameter file.** -/
theorem reply_of_public (h : publicOf pol KL lay = .ok X) (A : Hd.PublicAt X.P)
    (hW : Model.fileWords KL = scalesKF.toArray) {i : Cm.Idx}
    {x : Instance ppref} {Z : ℕ → ℕ → ℕ → ℕ → ℤ} {ZA : ℕ → Zs} (hr : x.r = 1023)
    (he : x.e = 1024)
    (O : Ords (layerShape X.P) X.layers.sc X.y X.hS X.HLy (Hd.npOf X.hS) (Hd.shapeA X) i.mat x
      Z ZA) (pl : AcceptancePolicy) :
    RinfR ppref (scalesOf (layerShape X.P) X.layers.sc (Hd.npOf X.hS)).kap
      (scalesOf (layerShape X.P) X.layers.sc (Hd.npOf X.hS)).nf (fun _ => tbRef) pl i.index x :=
  have B := Hd.public_of_publicOf h A
  reply_of_ords B.lay B.switches B.sized B.sized2 B.p4 B.groups B.full B.head
    (fun _ hg => (att_of_at' h A hg).1) (fun _ hg => (att_of_at' h A hg).2.1)
    (fun _ hg => (att_of_at' h A hg).2.2.1) (lawful_of_at h A hW) hr he O pl

/-- **The head with the cost ledger, at one parameter file.** -/
theorem under_of_public (h : publicOf pol KL lay = .ok X) (A : Hd.PublicAt X.P)
    (hW : Model.fileWords KL = scalesKF.toArray) {pl : AcceptancePolicy}
    (hpol : Policy.PolCond pl) {i : Cm.Idx} {x : Instance ppref} {Z : ℕ → ℕ → ℕ → ℕ → ℤ}
    {ZA : ℕ → Zs} (hre : x.r < x.e)
    (O : OrdsL (layerShape X.P) X.layers.sc X.y X.hS X.HLy (Hd.npOf X.hS) pl (Hd.shapeA X) i.mat
      x Z ZA) :
    Policy.IsTrueUnder (scalesOf (layerShape X.P) X.layers.sc (Hd.npOf X.hS)) pl i x :=
  have B := Hd.public_of_publicOf h A
  under_of_ords B.lay B.switches B.sized B.sized2 B.p4 B.groups B.full B.head
    (fun _ hg => (att_of_at' h A hg).1) (fun _ hg => (att_of_at' h A hg).2.1)
    (fun _ hg => (att_of_at' h A hg).2.2.1) (lawful_of_at h A hW) hpol hre O

/-- **The plain bundle has a value at the verifier's own shapes.** -/
theorem ords_met_public (h : publicOf pol KL lay = .ok X) (A : Hd.PublicAt X.P)
    (hW : Model.fileWords KL = scalesKF.toArray) :
    ∃ (i : Cm.Idx) (x : Instance ppref) (Z : ℕ → ℕ → ℕ → ℕ → ℤ) (ZA : ℕ → Zs),
      x.r = 1023 ∧ x.e = 1024 ∧
        Ords (layerShape X.P) X.layers.sc X.y X.hS X.HLy (Hd.npOf X.hS) (Hd.shapeA X) i.mat x
          Z ZA :=
  have B := Hd.public_of_publicOf h A
  ords_met B.lay B.switches B.sized B.sized2 B.p4 B.groups B.full B.head
    (fun _ hg => (att_of_at' h A hg).1) (fun _ hg => (att_of_at' h A hg).2.2.2)
    (fun _ hg => (att_of_at' h A hg).2.1) (fun _ hg => (att_of_at' h A hg).2.2.1)
    (lawful_of_at h A hW)

/-- **The ledger's bundle has a value at the verifier's own shapes.** -/
theorem ordsL_met_public (h : publicOf pol KL lay = .ok X) (A : Hd.PublicAt X.P)
    (hW : Model.fileWords KL = scalesKF.toArray) {pl : AcceptancePolicy}
    (hpol : Policy.PolCond pl) :
    ∃ (i : Cm.Idx) (x : Instance ppref) (Z : ℕ → ℕ → ℕ → ℕ → ℤ) (ZA : ℕ → Zs),
      x.r = 1023 ∧ x.e = 1024 ∧
        OrdsL (layerShape X.P) X.layers.sc X.y X.hS X.HLy (Hd.npOf X.hS) pl (Hd.shapeA X) i.mat
          x Z ZA :=
  have B := Hd.public_of_publicOf h A
  ordsL_met B.lay B.switches B.sized B.sized2 B.p4 B.groups B.full B.head
    (fun _ hg => (att_of_at' h A hg).1) (fun _ hg => (att_of_at' h A hg).2.2.2)
    (fun _ hg => (att_of_at' h A hg).2.1) (fun _ hg => (att_of_at' h A hg).2.2.1)
    (lawful_of_at h A hW) hpol

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.lawful_of_at
#print axioms OnBytes.Road.L5.reply_of_public
#print axioms OnBytes.Road.L5.under_of_public
#print axioms OnBytes.Road.L5.ords_met_public
#print axioms OnBytes.Road.L5.ordsL_met_public
