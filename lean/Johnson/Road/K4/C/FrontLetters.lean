-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/FrontLetters.lean.

What is here. THE LISTING front (OnBytes/Desc/First/K4/Claims.lean) RETURNS AT THE LETTERS JUST
WHERE IT RETURNS WITHOUT THEM: the three constants of the normalisations and the counts of padding
keys, which lie inside the layout (setY, TwinLetters.lean), are read by two of the seven listings
that front calls, and for values: the rows' lines read the first two constants (no listing reads the
third), the planes' count starts from the padding keys. (front's list also holds the form
rowBatchForm, which reads two numbers of the layout; it is always there, and the test asks only
whether front returns.) Five listings are the same at the letters by unfolding; of the other two,
whether they return is the same. The scales are free by the library's front_skel
(Johnson/Road/K4/Total/FrontOfParts.lean). The rotary table and the layout of the weights are not
read: of the public parameters front reads the layout and the record of reads alone (front_pub,
Johnson/Road/K4/Total/PubOnly.lean). So the test frontB (Johnson/Road/K4/Total/PlanMemberDefs.lean)
has one value at the public parameters with the letters laid in and without them (frontB_letters).
Four definitions; statements and proofs. On variables; nothing is evaluated.

  `setV`, `setFo`, `setO`, `setPy`   the letters laid into an Env, a Forest.Heard, an Own, the
                    public parameters.
  `norms_set`, `terms_set`, `gated_set`, `oneHot_set`, `emb_set`, `digits_set`   by unfolding.
  `rows_set`, `planesAt_set`, `planes_set`   whether it returns, alone.
  `front_set`       the whole listing.
  **`frontB_letters`**   the test.

Not shown here. That the listing returns anywhere. Nothing on what a form is worth.
No property is claimed.
-/
import Johnson.Road.K4.C.TwinLetters
import Johnson.Road.K4.Total.FrontOfParts
import Johnson.Road.K4.Total.PubOnly
import Johnson.Road.K4.Total.PlanMemberDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Model.Layer
open OnBytes.Desc.First.K4 (normsForms rowsForms termsForms gatedForms oneHotForms planesParts
  planesAt embeddingForm digitsAt front)
open OnBytes.Desc.First.K4.Total (bind_both bind_same mapM_same foldlM_same pure_both planOwn
  planOwnAt frontB front_skel front_pub)

/-- The letters inside the layout, laid into an environment of the forms. -/
def setV (v : Env) (e1 e2 eF : Nat) (pub : Array Nat) : Env :=
  { v with y := setY v.y e1 e2 eF pub }

/-- The counts of padding keys laid into a Forest.Heard. -/
def setFo (fo : Forest.Heard) (pub : Array Nat) : Forest.Heard :=
  { fo with shape := { fo.shape with pub := pub } }

/-- Both laid into an Own. -/
def setO (o : Own) (e1 e2 eF : Nat) (pub : Array Nat) : Own :=
  { o with v := setV o.v e1 e2 eF pub, H := { o.H with fo := setFo o.H.fo pub } }

/-- The public parameters with the letters inside the layout alone. -/
def setPy (P : Pub) (e1 e2 eF : Nat) (pub : Array Nat) : Pub :=
  { P with y := setY P.y e1 e2 eF pub }

variable (e1 e2 eF : Nat) (pub : Array Nat)

/-- Claim group 2 is the same. -/
theorem norms_set (P : Pub) (v : Env) (H : Heard) :
    normsForms (setPy P e1 e2 eF pub) (setV v e1 e2 eF pub) H = normsForms P v H := rfl

/-- Claim group 7 is the same. -/
theorem terms_set (v : Env) (H : Heard) :
    termsForms (setV v e1 e2 eF pub) H = termsForms v H := rfl

/-- Claim groups 8 and 9 are the same. -/
theorem gated_set (P : Pub) (v : Env) (hd : Level) (hd2 : Option Level) :
    gatedForms (setPy P e1 e2 eF pub) (setV v e1 e2 eF pub) hd hd2 = gatedForms P v hd hd2 := rfl

/-- Claim group 10 is the same. -/
theorem oneHot_set (v : Env) : oneHotForms (setV v e1 e2 eF pub) = oneHotForms v := rfl

/-- Claim group 12 is the same. -/
theorem emb_set (v : Env) (H : Heard) (s : Nat) :
    embeddingForm (setV v e1 e2 eF pub) H s = embeddingForm v H s := rfl

/-- A norm's digits are the same. -/
theorem digits_set (v : Env) (Pn : String) (i : Nat) :
    digitsAt (setV v e1 e2 eF pub) Pn i = digitsAt v Pn i := rfl

/-- Claim groups 4 to 6 return at the letters just where they return without them. -/
theorem rows_set (v : Env) (H H' : Heard) :
    (rowsForms (setV v e1 e2 eF pub) H').isSome = (rowsForms v H).isSome := by
  delta rowsForms
  simp only [Option.bind_eq_bind, Option.pure_def]
  refine bind_both (mapM_same _ fun i _ => ?_) fun _ _ =>
    bind_both (mapM_same _ fun i _ => ?_) fun _ _ => pure_both _ _
  · rw [Option.isSome_map, Option.isSome_map, digits_set]
  · rw [digits_set]

/-- A sum over the planes' columns returns at the letters just where it returns without them. -/
theorem planesAt_set (fo : Forest.Heard) (lm e : Nat) (bit : Nat → Nat → Option Aff) :
    (planesAt (setFo fo pub) lm e bit).isSome = (planesAt fo lm e bit).isSome := by
  delta planesAt
  exact foldlM_same _ _ _ (fun _ _ => rfl) _ _

/-- Claim group 11 returns at the letters just where it returns without them. -/
theorem planes_set (v : Env) (fo : Forest.Heard) :
    (planesParts (setV v e1 e2 eF pub) (setFo fo pub)).isSome = (planesParts v fo).isSome := by
  delta planesParts
  exact bind_same _ fun tB0 => bind_same _ fun tB1 => bind_same _ fun tP => bind_same _ fun _ =>
    bind_both (planesAt_set pub fo _ 0 _) fun _ _ =>
      bind_both (planesAt_set pub fo _ 1 _) fun _ _ =>
        bind_both (foldlM_same _ _ _ (fun _ _ => rfl) _ _) fun _ _ => pure_both _ _

/-- **The whole listing returns at the letters just where it returns without them.** -/
theorem front_set (rows : Bool) (P : Pub) (g : Nat) (o : Own) (a b : Aff) :
    (front rows (setPy P e1 e2 eF pub) g (setO o e1 e2 eF pub) a b).isSome =
      (front rows P g o a b).isSome := by
  delta front
  refine bind_both (congrArg Option.isSome (norms_set e1 e2 eF pub P o.v _)) fun _ _ =>
    bind_both (rows_set e1 e2 eF pub o.v _ _) fun _ _ =>
      bind_both (congrArg Option.isSome (terms_set e1 e2 eF pub o.v _)) fun _ _ =>
        bind_both (congrArg Option.isSome (gated_set e1 e2 eF pub P o.v o.hd o.hd2)) fun _ _ =>
          bind_both (congrArg Option.isSome (oneHot_set e1 e2 eF pub o.v)) fun _ _ =>
            bind_both (planes_set e1 e2 eF pub o.v o.H.fo) fun _ _ => ?_
  dsimp only
  by_cases h : (g == 0) = true
  · rw [if_pos h, if_pos h]
    refine bind_both ?_ fun _ _ => pure_both _ _
    rw [Option.isSome_map, Option.isSome_map]
    exact congrArg Option.isSome (emb_set e1 e2 eF pub o.v _ o.sVE)
  · rw [if_neg h, if_neg h]
    exact bind_both rfl fun _ _ => pure_both _ _

/-- **THE TEST frontB HAS ONE VALUE AT THE PUBLIC PARAMETERS WITH THE LETTERS LAID IN AND WITHOUT
THEM.** -/
theorem frontB_letters (rows : Bool) (P : Pub) (hp : HPlan2) (g : Nat) (sc : Scales)
    (rope : Array Nat) (W : WsLay) :
    frontB rows (setP P e1 e2 eF pub sc rope W) hp g (setP P e1 e2 eF pub sc rope W).y.fo =
      frontB rows P hp g P.y.fo := by
  have key : ∀ (iU3 : Nat) (tab : List TableAt),
      (front rows (setP P e1 e2 eF pub sc rope W) g
        (planOwnAt (setP P e1 e2 eF pub sc rope W) hp g (setP P e1 e2 eF pub sc rope W).y.fo iU3
          tab) {} {}).isSome = (front rows P g (planOwnAt P hp g P.y.fo iU3 tab) {} {}).isSome := by
    intro iU3 tab
    rw [front_pub rows (setPy P e1 e2 eF pub) (setP P e1 e2 eF pub sc rope W) g _ {} {} rfl rfl]
    exact (front_skel rows (setPy P e1 e2 eF pub) g
      (planOwnAt (setP P e1 e2 eF pub sc rope W) hp g (setP P e1 e2 eF pub sc rope W).y.fo iU3
        tab)
      (setO (planOwnAt P hp g P.y.fo iU3 tab) e1 e2 eF pub) {} {} {} {}
      ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩).trans
        (front_set e1 e2 eF pub rows P g _ {} {})
  have eL : layTables
      (((setP P e1 e2 eF pub sc rope W).tails.getD g {}).mats.map fun M => (M.m, M.k))
      (tableAsks (setP P e1 e2 eF pub sc rope W).y (setP P e1 e2 eF pub sc rope W).rd g) 0 =
      layTables ((P.tails.getD g {}).mats.map fun M => (M.m, M.k)) (tableAsks P.y P.rd g) 0 := rfl
  delta frontB planOwn
  rw [eL]
  generalize hp.tl.ix.U.getD 2 none = u
  generalize layTables ((P.tails.getD g {}).mats.map fun M => (M.m, M.k))
    (tableAsks P.y P.rd g) 0 = lt
  cases u with
  | none => rfl
  | some iU3 =>
    cases lt with
    | none => rfl
    | some x => exact key iU3 x.1

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.norms_set
#print axioms OnBytes.Road.K4.C.terms_set
#print axioms OnBytes.Road.K4.C.gated_set
#print axioms OnBytes.Road.K4.C.oneHot_set
#print axioms OnBytes.Road.K4.C.emb_set
#print axioms OnBytes.Road.K4.C.digits_set
#print axioms OnBytes.Road.K4.C.rows_set
#print axioms OnBytes.Road.K4.C.planesAt_set
#print axioms OnBytes.Road.K4.C.planes_set
#print axioms OnBytes.Road.K4.C.front_set
#print axioms OnBytes.Road.K4.C.frontB_letters
