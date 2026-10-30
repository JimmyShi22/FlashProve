-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/ZzRowsAtPlans.lean: THE SMALLNESS TEST: IN THE PLANNED LEDGER OF EVERY SEGMENT EVERY
VIRTUAL ROW OF THE DIGITS' ARRAY (ZZ) BEGINS AT COLUMN 0 (the field L0 of HRow,
OnBytes/Model/Hide.lean). Definitions and lemmas; none of the library's goals. No prover stands in
them; nothing on completeness, soundness or hiding.

  `l0At F t e`   the first column of virtual row e of array t of the ledger F; 0 where there is no
      such row
  `ZzZero tl F`   every virtual row of the array ZZ of F begins at column 0
  **`addTreesF_zzTree`**   behind addTreesF (OnBytes/Model/Tail.lean) the array ZZ is, whole, what
      t2AddN laid: 2 * zzBlocks + 2 empty virtual rows
  `replicate_l0`, `l0At_trimL`   an empty row begins at column 0; freeing the weights (Fork.trimL)
      leaves the first columns
  **`zz_made`**   so `ZzZero` of every record with addTreesF's return's arrays' numbers and every
      ledger with its first columns
  `planG_zz`, `planA_zz`, `planH2_zz`   at what each of the three planners returns
  `public_G_zz`, `public_A_zz`, `public_H_zz`, **`public_zz`**   at every plan in what
      Verify.publicOf returns: the feed-forward segments', the attention segments', the head's; all
      three
  **`built_zz`**   in the goals' scope, under an opening of the description: at each of the 25 built
      segments
By: OnBytes.Road.K4.Rec.t2AddN_tree (Johnson/Road/K4/Rec/U3Tree.lean) · the walk of
Fo.ZPlan.addTreesF_zz and the cuts of planG_zMine, planH2_zMine, public_A_zMine; seamPlan_cut,
addTreesF_sameP and the laws on SameP (OnBytes/Tie/Pv/Lookup/Ends/FoZMade.lean, FoZPublic.lean) ·
Fo.t2AddN_ok, t2AddP_ok, Ext (FoAddTrees.lean) · IM.ground_tails (Johnson/IMR/K8Seat.lean).
Limits. THE PLANNED LEDGER ALONE: nothing on the ledger of any state. The array ZZ alone. The full
size's 25 segments in `built_zz`.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoZPublic
import Johnson.Road.K4.Rec.U3Tree
import Johnson.IMR.K8Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open _root_.Fo (Ext t2AddN_ok t2AddP_ok SameP pureE_ok)
open _root_.Fo.BatRows _root_.Fo.Pub _root_.Fo.ZPlan

/-- The first column of virtual row e of array t. -/
def l0At (F : Fork) (t e : Nat) : Nat := ((F.trees.getD t {}).rows.getD e {}).L0

/-- Every virtual row of the array ZZ begins at column 0. -/
def ZzZero (tl : HTailF2) (F : Fork) : Prop := ∀ e, l0At F tl.ix.ZZ e = 0

/-- **Behind addTreesF the array ZZ is what t2AddN laid.** -/
theorem addTreesF_zzTree {tl tl' : HTailF2} {F G : Fork} {T T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (h : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', G, T')) :
    G.trees.getD tl.ix.ZZ {} =
      { name := "ZZ", kind := .table, R := tl.tau, K := 2 * tl.mz, owner := !false,
        rows := Array.replicate (2 * tl.zzBlocks + 2) ({} : HRow) } := by
  unfold addTreesF at h
  obtain ⟨_, h⟩ := jpX h
  obtain ⟨_, h⟩ := jpX h
  obtain ⟨_, h⟩ := jpX h
  obtain ⟨_, h⟩ := jpX h
  obtain ⟨⟨F1, T1⟩, _, h⟩ := bindX h
  obtain ⟨⟨F2, T2⟩, _, h⟩ := bindX h
  obtain ⟨⟨F3, T3⟩, _, h⟩ := bindX h
  obtain ⟨⟨gotZ, FZ, TZ⟩, hZ, h⟩ := bindX h
  obtain ⟨gZ, h⟩ := jpX h
  obtain ⟨⟨gotB, FB, TB⟩, hB, h⟩ := bindX h
  obtain ⟨gB, h⟩ := jpX h
  obtain ⟨⟨F4, T4⟩, h4, h⟩ := bindX h
  obtain ⟨_, h⟩ := jpX h
  have e := Except.ok.inj h
  obtain ⟨e1, e2⟩ := Prod.mk.inj e
  obtain ⟨e2, _⟩ := Prod.mk.inj e2
  subst e1 e2
  have K4 : Ext FB F4 := forInX _ (fun s : MProd Fork Tail2 => Ext FB s.1)
    (fun a s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := bindX hs
      obtain ⟨_, hs⟩ := jpX hs
      exact ⟨_, (Except.ok.inj hs).symm, hI.trans (t2AddP_ok hP)⟩)
    _ _ _ (Ext.refl FB) h4
  obtain ⟨z1, z2, z3, z4, z5⟩ := t2AddN_ok hZ
  obtain ⟨b1, b2, b3, b4, b5⟩ := t2AddN_ok hB
  have tree := OnBytes.Road.K4.Rec.t2AddN_tree hZ
  have gZ' : gotZ = tl.ix.ZZ := by simpa using gZ
  subst gZ'
  have lZ : tl.ix.ZZ < FZ.trees.size := by omega
  have tZ : F4.trees.getD tl.ix.ZZ {} = FZ.trees.getD tl.ix.ZZ {} :=
    (K4.2 _ (Nat.lt_of_lt_of_le lZ b2.1)).trans (b2.2 _ lZ)
  rw [tZ]
  exact tree

/-- An empty row begins at column 0. -/
theorem replicate_l0 (n e : Nat) : ((Array.replicate n ({} : HRow)).getD e {}).L0 = 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> rfl

/-- Freeing the weights leaves the first columns. -/
theorem l0At_trimL (F : Fork) (t e : Nat) : l0At F.trimL t e = l0At F t e := by
  unfold l0At Fork.trimL
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases F.trees[t]? with
  | none => rfl
  | some X =>
    simp only [Option.map_some, Option.getD_some, Array.getElem?_map]
    cases X.rows[e]? with
    | none => rfl
    | some r => rfl

/-- **From addTreesF's return to a plan's record and ledger.** -/
theorem zz_made {tl tl' : HTailF2} {F G : Fork} {T T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (ha : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', G, T'))
    (tlc : HTailF2) (hr : SameP tl' tlc) (Fc : Fork)
    (hF : ∀ t e, l0At Fc t e = l0At G t e) : ZzZero tlc Fc := by
  intro e
  have hix : tlc.ix = tl.ix := ((addTreesF_sameP ha).trans hr).same.ix
  rw [hF, hix]
  unfold l0At
  rw [addTreesF_zzTree ha]
  exact replicate_l0 _ e

theorem planG_zz (P : Layer.Pub) (g : Nat) (O : Option Layer.HPlan2) (hp : Layer.HPlan2)
    (h : Layer.planG P g O = .ok hp) : ZzZero hp.tl hp.Fp := by
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
    exact zz_made hA _ (ownerIs_sameP tl1 g) _ (l0At_trimL Fp)
  · split at h
    · repeat obtain ⟨_, _, h⟩ := bindE_ok h
      cases h
      have hy := pureE_ok ‹(pure _ : Except String HTailF2) = Except.ok _›
      have hB := ‹HTailF2.borderMeans _ _ _ _ = Except.ok _›
      dsimp only
      rw [hy]
      exact zz_made hA _ ((ownerIs_sameP tl1 g).trans (borderMeans_sameP hB)) _ (l0At_trimL Fp)
    · obtain ⟨_, hx, _⟩ := bindE_ok h
      cases hx

theorem planA_zz (settings : Settings) (i : Attention.In) (cf : Attention.Cfg)
    (P : Attention.Plan) (e : Attention.plan settings i cf = .ok P) (tlc : HTailF2)
    (hr : SameP P.seam.tl tlc) : ZzZero tlc P.seam.Fp := by
  obtain ⟨seam0, -, h1, -⟩ := planA_rows0 settings i cf P e
  obtain ⟨T, hA⟩ := seamPlan_cut h1
  exact zz_made hA tlc hr P.seam.Fp fun _ _ => rfl

theorem planH2_zz (g : Settings) (h : Head.Shape) (L : Head.HL) (b : Head.Border)
    (O : Head.Owner) (NGr lkW : Nat) (hp : Head.HPlanH2)
    (e : Head.planH2 g h L b O NGr lkW = .ok hp) (Fc : Fork)
    (hF : ∀ t e, l0At Fc t e = l0At hp.Fp t e) : ZzZero hp.tl Fc := by
  unfold Head.planH2 at e
  repeat obtain ⟨_, _, e⟩ := bindE_ok e
  dsimp only at e
  split at e
  · obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨tl, hS, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨⟨tl1, Fp, Tp⟩, hA, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨tl2, hO, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    cases e
    exact zz_made hA _ (ownerHeld_sameP hO) Fc hF
  · obtain ⟨_, hx, _⟩ := bindE_ok e
    cases hx

section
variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}

theorem public_G_zz (h : Verify.publicOf pol KL layout = .ok X) (g : Nat) (hp : Layer.HPlan2)
    (hg : X.G[g]? = some hp) : ZzZero hp.tl hp.Fp :=
  planG_zz X.layers g _ hp (public_G h g hp hg)

theorem public_H_zz (h : Verify.publicOf pol KL layout = .ok X) : ZzZero X.H.tl X.H.Fp := by
  obtain ⟨H0, h0, e⟩ := public_H h
  rw [e]
  exact planH2_zz _ _ _ _ _ _ _ H0 h0 _ (l0At_trimL H0.Fp)

theorem public_A_zz (h : Verify.publicOf pol KL layout = .ok X) (g : Nat)
    (a : Attention.Plan) (hg : X.A[g]? = some a) : ZzZero a.seam.tl a.seam.Fp := by
  obtain ⟨_, _, _, _, _, sc, A0, seen, k2, k3, k6, k7⟩ := publicOf_cut pol KL layout X h
  rw [k7] at hg
  have hz : ∃ a0 s, A0[g]? = some a0 ∧ seen[g]? = some s ∧
      a = { a0 with seam := { a0.seam with tl := s.tl } } := by
    rw [← Array.getElem?_toList, Array.toList_zipWith] at hg
    obtain ⟨a0, s, e1, e2, e3⟩ := List.getElem?_zipWith_eq_some.1 hg
    exact ⟨a0, s, by simpa using e1, by simpa using e2, e3.symm⟩
  obtain ⟨a0, s, e1, e2, e3⟩ := hz
  obtain ⟨s0, f1, f2⟩ := owners_sameP k6 g s e2
  have f3 : s0 = ⟨a0.seam.tl, a0.seam.Fp, a0.seam.Tp⟩ := by
    unfold seenA0 at f1
    rw [Array.getElem?_map, e1] at f1
    exact (Option.some.inj f1).symm
  rcases k3 with ⟨_, c, k9, rfl⟩ | ⟨_, rfl⟩
  · obtain ⟨lines, l1, l2⟩ := config_at k9
    obtain ⟨cf, m1, m2⟩ := group_plan (l2 g a0 e1)
    subst e3
    show ZzZero s.tl a0.seam.Fp
    rw [f3] at f2
    exact planA_zz _ _ _ a0 m2 s.tl f2
  · simp at e1

/-- **At every plan in what publicOf returns.** -/
theorem public_zz (h : Verify.publicOf pol KL layout = .ok X) :
    (∀ (g : Nat) (hp : Layer.HPlan2), X.G[g]? = some hp → ZzZero hp.tl hp.Fp) ∧
    (∀ (g : Nat) (a : Attention.Plan), X.A[g]? = some a → ZzZero a.seam.tl a.seam.Fp) ∧
      ZzZero X.H.tl X.H.Fp :=
  ⟨public_G_zz h, public_A_zz h, public_H_zz h⟩

end

/-- **At each of the 25 built segments.** -/
theorem built_zz {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)}
    {c : Chain S Claim} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) : ZzZero Xl.tl Xl.Fp := by
  obtain ⟨hT, X24, e24, h24, f24, -⟩ := IM.ground_tails hS hR O.pub O.blank
  by_cases hh : l = 24
  · subst hh
    obtain rfl : X24 = Xl := Option.some.inj (e24.symm.trans e3)
    rw [h24, f24]
    exact (public_zz O.public).2.2
  · obtain ⟨g, hg, rfl | rfl⟩ : ∃ g, g < 12 ∧ (l = 2 * g ∨ l = 2 * g + 1) :=
      ⟨l / 2, by omega, by omega⟩
    · obtain ⟨hp, -, X', -, ehp, -, e3', htl, hfp, -⟩ := hT g hg
      obtain rfl : X' = Xl := Option.some.inj (e3'.symm.trans e3)
      rw [htl, hfp]
      exact (public_zz O.public).1 g hp ehp
    · obtain ⟨-, q, -, X', -, eq, -, -, -, -, -, -, e3', htl, hfp, -⟩ := hT g hg
      obtain rfl : X' = Xl := Option.some.inj (e3'.symm.trans e3)
      rw [htl, hfp]
      exact (public_zz O.public).2.1 g q eq

end P1K8

#print axioms P1K8.addTreesF_zzTree
#print axioms P1K8.replicate_l0
#print axioms P1K8.l0At_trimL
#print axioms P1K8.zz_made
#print axioms P1K8.planG_zz
#print axioms P1K8.planA_zz
#print axioms P1K8.planH2_zz
#print axioms P1K8.public_G_zz
#print axioms P1K8.public_H_zz
#print axioms P1K8.public_A_zz
#print axioms P1K8.public_zz
#print axioms P1K8.built_zz
