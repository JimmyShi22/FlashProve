-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/Road/K4/FrontLater.lean: THE TEST `frontB` (Johnson/Road/K4/Total/PlanMemberDefs.lean:
"the listing
front returns at the plan's value") READS THE GROUP's NUMBER THROUGH "IS IT THE FIRST GROUP" ALONE.
So at the groups behind the first it is ONE test: whoever asks it at group 1 has asked it at all of
them. Nine theorems; nothing is evaluated.

WHY. The families of tables (`tableAsks`, OnBytes/Model/LayerForms.lean) and the listing (`front`,
OnBytes/Desc/First/K4/Claims.lean) read g in "g == 0" alone; every group's matrices have the same
rows and columns (`tails_pairs`, Johnson/Road/FormsKeysTab.lean); the environment's own g lies
outside what the listing's return hangs on (`front_skel`, Johnson/Road/K4/Total/FrontOfParts.lean);
the number of columns of the array of the reads is the plan's nU[2] (`planG_K3`,
Johnson/Goal/Meaning/PlanPort.lean), which behind the first group is the reads' nW.

  `planG_nU`, `planG_nU_later`: what planG lays as nU; behind the first group nU[2] = P.rd.nW. The
    walk is that of `planG_u3` (Johnson/Road/K4/Rec/U3Tree.lean).
  `tableAsks_later`, `front_g_later`: the two texts at two groups behind the first.
  `skel_planOwnAt`: two values off two plans with one number of columns have one skeleton.
  **`frontB_later`**: AN EQUATION OF THE TWO TESTS, at any public parameters of the layers, from:
  both
    groups are not the first; the two plans name their arrays of the reads; these have one number of
    columns; the two groups' matrices have the same rows and columns.
  **`frontB_later_public`**: the same wherever the program's `publicOf` returns X, at X's own plans:
    no scope, no written value.
  `frontB_from_one_public`, **`frontB_from_one`**: so an accept at group 1 is an accept at every
  later
    group; the second in the form of the head `P5J.AtMgA`.

Limits. K04_law IS NOT PROVED BY THIS. `frontB` IS SHOWN TO ACCEPT NOWHERE: an equation of two
tests,
so a reject carries too. (So in this file. By Lean's kernel it accepts at the groups 0 and 1 at what
twins of the makers return: `front_free_at`, Johnson/Road/K4/RowHead/FrontFreeK.lean;
`front_at_head` there carries that to the head; a member of the head is proved at `storedPublicFiles` and `zGap`
alone (at secondHashFunction; side library AtFullSide/Top/).) Nothing on
the first group. Nothing on soundness.
-/
import Johnson.Road.K4.Total.FrontOfParts
import Johnson.Road.K4.Total.PlanMemberDefs
import Johnson.Road.K4.Rec.U3Tree
import Johnson.Road.FormsKeysTab
import OnBytes.Tie.Pv.Lookup.Ends.FoPlaneMatPubG
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Rec
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 Fo Fo.Pub Fo.ZPlan
open Fo.BatRows (bindE_ok)

/-- What planG lays as the lengths of the four vectors. -/
theorem planG_nU (P : Layer.Pub) (g : Nat) (O : Option Layer.HPlan2) (hp : Layer.HPlan2)
    (h : Layer.planG P g O = .ok hp) :
    ∃ e, hp.nU = #[0, 0, P.rd.nW + (if g == 0 then e else 0)] := by
  unfold Layer.planG at h
  obtain ⟨⟨mats, txOf, ft⟩, _, h⟩ := bindE_ok h
  obtain ⟨tl, hS, h⟩ := bindE_ok h
  obtain ⟨⟨tl1, Fp, Tp⟩, hA, h⟩ := bindE_ok h
  obtain ⟨Tp1, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := bindE_ok h
    obtain ⟨y, hy, h⟩ := bindE_ok h
    obtain rfl := pureE_ok hy
    obtain ⟨_, _, h⟩ := bindE_ok h
    cases h
    exact ⟨_, rfl⟩
  · split at h
    · repeat obtain ⟨_, _, h⟩ := bindE_ok h
      cases h
      exact ⟨_, rfl⟩
    · obtain ⟨_, hx, _⟩ := bindE_ok h
      cases hx

/-- Behind the first group the third vector has the reads' own length. -/
theorem planG_nU_later (P : Layer.Pub) (n : Nat) (O : Option Layer.HPlan2) (hp : Layer.HPlan2)
    (h : Layer.planG P (n + 1) O = .ok hp) : hp.nU.getD 2 0 = P.rd.nW := by
  obtain ⟨e, he⟩ := planG_nU P (n + 1) O hp h
  rw [he]
  rfl

end OnBytes.Road.K4.Rec

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Model.Verify (Public publicOf)
open OnBytes.Model.Layer (Pub HPlan2 TableAt layTables tableAsks)
open OnBytes.Desc.First.K4 (front)
open OnBytes.Desc.First.K4.Total (frontB planOwn planOwnAt front_skel Skel)
open OnBytes.Maker (WholeD)

/-- The families of tables at two groups behind the first. -/
theorem tableAsks_later (y : Layer.Lay) (rd : Layer.Reads) (n n' : ℕ) :
    tableAsks y rd (n + 1) = tableAsks y rd (n' + 1) := rfl

/-- The listing at two groups behind the first. -/
theorem front_g_later (rows : Bool) (P : Pub) (n n' : ℕ) (o : Layer.Own) (a b : Aff) :
    front rows P (n + 1) o a b = front rows P (n' + 1) o a b := rfl

/-- Two values off two plans with one number of columns have one skeleton. -/
theorem skel_planOwnAt (P : Pub) (hp hp' : HPlan2) (g g' : ℕ) (sh : Forest.Shape) (i i' : ℕ)
    (tab : List TableAt)
    (hK : ((hp.Fp.trees[i]?).map (·.K)).getD 0 = ((hp'.Fp.trees[i']?).map (·.K)).getD 0) :
    Skel (planOwnAt P hp g sh i tab) (planOwnAt P hp' g' sh i' tab) :=
  ⟨⟨rfl, rfl, hK⟩, rfl, rfl, rfl, rfl, rfl⟩

/-- **Behind the first group the test is one test**: where the two plans name their arrays of the
reads, these have one number of columns, and the two groups' matrices have the same rows and
columns. -/
theorem frontB_later (rows : Bool) (P : Pub) {hp hp' : HPlan2} (n n' : ℕ) {i i' : ℕ}
    (sh : Forest.Shape) (hU : hp.tl.ix.U.getD 2 none = some i)
    (hU' : hp'.tl.ix.U.getD 2 none = some i')
    (hK : ((hp.Fp.trees[i]?).map (·.K)).getD 0 = ((hp'.Fp.trees[i']?).map (·.K)).getD 0)
    (hM : ((P.tails.getD (n + 1) {}).mats.map fun M => (M.m, M.k)) =
      ((P.tails.getD (n' + 1) {}).mats.map fun M => (M.m, M.k))) :
    frontB rows P hp (n + 1) sh = frontB rows P hp' (n' + 1) sh := by
  unfold frontB planOwn
  rw [hU, hU', hM, tableAsks_later P.y P.rd n n']
  cases layTables ((P.tails.getD (n' + 1) {}).mats.map fun M => (M.m, M.k))
      (tableAsks P.y P.rd (n' + 1)) 0 with
  | none => rfl
  | some x =>
    show (front rows P (n + 1) (planOwnAt P hp (n + 1) sh i x.1) {} {}).isSome =
      (front rows P (n' + 1) (planOwnAt P hp' (n' + 1) sh i' x.1) {} {}).isSome
    rw [front_g_later rows P n n']
    exact front_skel rows P (n' + 1) _ _ {} {} {} {}
      (skel_planOwnAt P hp hp' (n + 1) (n' + 1) sh i i' x.1 hK)

variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Public}

/-- **Wherever the program's publicOf returns X: at X's own plans of two groups behind the first the
test is one test.** -/
theorem frontB_later_public (h : publicOf pol KL lay = .ok X) (rows : Bool) (sh : Forest.Shape)
    {g g' : ℕ} {hp hp' : HPlan2} (hg : g ≠ 0) (hg' : g' ≠ 0) (hG : X.G[g]? = some hp)
    (hG' : X.G[g']? = some hp') :
    frontB rows X.layers hp g sh = frontB rows X.layers hp' g' sh := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hg
  obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hg'
  have p := Fo.Pub.public_G h _ hp hG
  have p' := Fo.Pub.public_G h _ hp' hG'
  have u : hp.tl.ix.U.getD 2 none = some 0 := by
    rw [(Rec.planG_u3 _ _ _ _ p).1]
    rfl
  have u' : hp'.tl.ix.U.getD 2 none = some 0 := by
    rw [(Rec.planG_u3 _ _ _ _ p').1]
    rfl
  have k := (_root_.Meaning.Plan.planG_K3 _ _ _ _ p u).trans (Rec.planG_nU_later _ _ _ _ p)
  have k' := (_root_.Meaning.Plan.planG_K3 _ _ _ _ p' u').trans (Rec.planG_nU_later _ _ _ _ p')
  refine frontB_later rows X.layers n n' sh u u' (k.trans k'.symm) ?_
  rw [Fo.PlaneMatG.public_tails h, OnBytes.Road.tails_pairs _ (Fo.PlaneMatG.public_G_lt h hG),
    OnBytes.Road.tails_pairs _ (Fo.PlaneMatG.public_G_lt h hG')]

/-- So an accept at group 1 is an accept at every group behind the first. -/
theorem frontB_from_one_public (h : publicOf pol KL lay = .ok X) (rows : Bool) (sh : Forest.Shape)
    {hp₁ : HPlan2} (h1 : X.G[1]? = some hp₁) (t : frontB rows X.layers hp₁ 1 sh = true) :
    ∀ g, g ≠ 0 → ∀ hp, X.G[g]? = some hp → frontB rows X.layers hp g sh = true :=
  fun _ hg _ hG => (frontB_later_public h rows sh hg (by decide) hG h1).trans t

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **Under the head: an accept at group 1 is an accept at the ten later groups.** -/
theorem frontB_from_one (hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {hp₁ : HPlan2}
    (h1 : (P5J.At.X Zp).G[1]? = some hp₁)
    (t : frontB false (P5J.At.X Zp).layers hp₁ 1 (P5J.At.X Zp).layers.y.fo = true) :
    ∀ g, 2 ≤ g → g < 12 → ∀ hp, (P5J.At.X Zp).G[g]? = some hp →
      frontB false (P5J.At.X Zp).layers hp g (P5J.At.X Zp).layers.y.fo = true := by
  obtain ⟨Bs, base, O⟩ := hA.laid.opened
  have hpub : publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X := O.W ▸ O.public
  intro g h2 _ hp hG
  exact frontB_from_one_public hpub false _ h1 t g (by omega) hp hG

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Rec.planG_nU
#print axioms OnBytes.Road.K4.Rec.planG_nU_later
#print axioms OnBytes.Road.K4.tableAsks_later
#print axioms OnBytes.Road.K4.front_g_later
#print axioms OnBytes.Road.K4.skel_planOwnAt
#print axioms OnBytes.Road.K4.frontB_later
#print axioms OnBytes.Road.K4.frontB_later_public
#print axioms OnBytes.Road.K4.frontB_from_one_public
#print axioms OnBytes.Road.K4.frontB_from_one
