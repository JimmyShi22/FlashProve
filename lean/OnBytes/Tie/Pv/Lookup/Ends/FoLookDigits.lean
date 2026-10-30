-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoLookDigits.lean.
The smallness test: the claims of its lookup on the digits inside the one equation, at the runs of
its two routines.

A sub-proof's check runs the smallness test's messages (`HTailF2.transcriptF`) and, later, adds its
claims (`HTailF2.objectsF`). This file takes these two run equations as premises and states by how
much the total has grown behind the lookup's claims: by one batched form of a ledger with exponents,
read at the committed entries.

Main names:
  `digForms`: the lookup's claims as a list of affine forms on the caller's entries: a function of
    the test's record, the two maps of places, the shape, the lookup's first slot and the rounds. It
    is taken by choice from a statement of existence (`claimsZ_forms_dig`), so it is noncomputable,
    and all that is known of it is `digForms_len` (its length) and `digForms_val` (its members'
    values at every reading of the entries are the list `claimsZ`).
  `z_look_at`: the draw of the matrix, the commitment, `Forest.pad`, `Forest.objects`, `linJoin9`
    and `linBits9` have returned, each from where the one before it in its routine ended; rv are the
    rounds of the view that `Forest.pad` took; and in every later state, at all entries m, in every
    world that meets the law of the rows, the total behind `linBits9` is the total before
    `Forest.objects` plus the gap at m of `batchAt theta (lookLed n0 (digForms ..))`, n0 the number
    of claims before.

Under: the two runs return; the first from a state whose arrays have their sizes and a context on a
view; the state from which the second runs is a later state than the first left, its arrays have
their sizes, and it has one coefficient for each slot; tests on public numbers (t1 to t10); on the
world: `RowsLaw` in the state that `coefAll` makes of Fc at the record that `objectsF` returns.

Limit: identities at the one element theta of the state, between the total before `Forest.objects`
and the total behind `linBits9`: of the total at the end of the check nothing is said. That Fc is
the state from which the check's routine `coefficientsF` runs is not said here. Whether the entries
m or the world's entries of virtual rows hang on theta is not said here.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoLookDigitsSame
import OnBytes.Tie.Pv.Lookup.Ends.FoSiteOwn
import OnBytes.Tie.Pv.Lookup.Forest.FoPadAll
import OnBytes.Tie.Pv.Lookup.Ends.FoTailSizes
import OnBytes.Tie.Pv.Lookup.Ends.FoTailNums
import OnBytes.Tie.Pv.Lookup.Ends.FoLookBatch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun OnBytes.DgP Cb.Fo Cb.LdLkp
open OnBytes.Road.Rows

section
variable {K : Type} [Field K] {J₀ : Type}

/-- The claims of the lookup on the digits, as forms on the caller's entries. -/
noncomputable def digForms (tl : HTailF2) (en : Ent3 → J₀) (mk : ℕ → J₀) (h : FoNums.Sh) (jLK : ℕ)
    (rs : Rounds K) : List (AffK J₀ K) :=
  Classical.choose (claimsZ_forms_dig tl en mk h jLK rs)

theorem digForms_len (tl : HTailF2) (en : Ent3 → J₀) (mk : ℕ → J₀) (h : FoNums.Sh) (jLK : ℕ)
    (rs : Rounds K) :
    (digForms tl en mk h jLK rs).length = (endsOf h 5 jLK rs).rows.length + 4 :=
  (Classical.choose_spec (claimsZ_forms_dig tl en mk h jLK rs)).1

theorem digForms_val (tl : HTailF2) (en : Ent3 → J₀) (mk : ℕ → J₀) (h : FoNums.Sh) (jLK : ℕ)
    (rs : Rounds K) (μ₀ : J₀ → K) :
    claimsZ h 5 jLK rs (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
        (colsK h 5 (endsOf h 5 jLK rs).zb0 fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
        (colsK h 5 (endsOf h 5 jLK rs).zb1 fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
        (Pin.pinColK 5 fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
        (fun c => AffK.val (digKF tl en (fun c => (endsOf h 5 jLK rs).zk.getD c []) c) (zext μ₀)) =
      (digForms tl en mk h jLK rs).map fun f => AffK.val f μ₀ :=
  (Classical.choose_spec (claimsZ_forms_dig tl en mk h jLK rs)).2 μ₀

end

/-! ### The commitment takes no slot

The rules of FoInvLink for a routine of a link, for a property of the state that need not be kept
by every step. -/

section
variable {I : Fork → Prop} {α β : Type}

theorem nxPure (a : α) : InvL I (Pure.pure a : LinkM α) := fun Lc => Inv.pure (a, Lc)

theorem nxBind {x : LinkM α} {f : α → LinkM β} (hx : InvL I x) (hf : ∀ a, InvL I (f a)) :
    InvL I (x >>= f) := fun Lc =>
  Inv.bind (x := x Lc) (f := fun p => f p.1 p.2) (hx Lc) fun p => hf p.1 p.2

theorem nxSub {x : SubM α} (hx : Inv I x) : InvL I (LinkM.sub x) := fun Lc =>
  Inv.bind (f := fun a => Pure.pure (a, Lc)) hx fun _ => Inv.pure _

theorem nxGet : InvL I (MonadState.get : LinkM LinkCtx) := fun Lc => Inv.pure (Lc, Lc)

theorem nxModify (f : LinkCtx → LinkCtx) : InvL I (_root_.modify f : LinkM PUnit) := by
  intro Lc
  exact Inv.pure (α := PUnit × LinkCtx) (PUnit.unit, f Lc)

theorem nxForIn {σ : Type} {f : α → σ → LinkM (ForInStep σ)} (hf : ∀ a s, InvL I (f a s)) :
    ∀ (l : List α) (s : σ), InvL I (ForIn.forIn l s f)
  | [], s => by
    rw [List.forIn_nil]
    exact nxPure s
  | a :: l, s => by
    rw [List.forIn_cons]
    refine nxBind (hf a s) fun r => ?_
    cases r with
    | done b => exact nxPure b
    | yield b => exact nxForIn hf l b

theorem nxCall (f : ChainCheck → Blk ChainCheck) : InvL I (LinkM.call f) := by
  intro Lc
  exact (Inv.lift _).bind fun _ => (Inv.liftM _).bind fun _ => Inv.pure _

end

/-- The commitment takes no slot. -/
theorem rootInH_next (trees : List ℕ) (n : ℕ) :
    InvL (fun X : Fork => X.next = n) (rootInH trees) := by
  unfold rootInH
  refine nxBind nxGet fun L => ?_
  refine nxBind (nxSub (Inv.liftM _)) fun _ => ?_
  refine nxBind (nxCall _) fun _ => ?_
  refine nxBind (nxModify _) fun _ => ?_
  refine nxBind (nxForIn (fun t _ => ?_) _ _) fun _ => nxSub (Inv.liftM _)
  refine nxBind (nxSub (Inv.ask _)) fun _ => ?_
  refine nxBind (nxSub (Inv.liftM _)) fun _ => ?_
  refine nxBind (nxSub (Inv.change fun F G h hS => ?_)) fun _ => nxPure _
  obtain rfl := Option.some.inj h
  exact hS

/-- **The lookup on the digits inside the one equation, at the two routines' runs.** -/
theorem z_look_at {J : Type} [Fintype J] [DecidableEq J] (tl tl2 tl3 : HTailF2) (L Lt : LinkCtx)
    (F Gt Fb G' : Fork) (c cr cb c' : Ctx) (funs : Array HFun)
    (hT : tl.transcriptF L F c = .ok (((tl2, Lt), Gt), cr)) (hF : Sized F)
    (hd : c.ch.dry = false)
    (hO : tl2.objectsF funs Fb cb = .ok ((tl3, G'), c')) (hL : Later Gt Fb) (sb : Sized Fb)
    (zb : Fb.LS.size = Fb.ns)
    (t1 : tailTest tl2 = true) (t2 : ∀ q < 2, pieceTest tl2 q = true)
    (t3 : ∀ q < 2, apartTest tl2 q = true) (t4 : callsTest tl2 = true)
    (t5 : ∀ h0, Forest.shape #[tl2.z1.call, tl2.z2.call] tl2.lidb = .ok h0 →
      { h0 with pub := tl2.f9.pub } = tl2.f9)
    (t6 : 2 ^ tl2.f9.cK = tl2.f9.NC) (t7 : 5 ≤ tl2.f9.kT + tl2.f9.cK)
    (t8 : ∀ q < 2, (tl2.zOf q).call.n ≤ 63) (Fc : Fork) (t9 : coefTest tl3 Fc = true)
    (t10 : ∀ a ∈ allPieces tl2, a.2.r0 + a.2.Rp ≤ (Fc.trees.getD a.2.tree {}).R) :
    ∃ (tl' : HTailF2) (F1 : Fork) (c5 c1 : Ctx) (g : Heard) (rv : List Fmt.RoundView) (Fa : Fork)
      (ca : Ctx) (tlA : HTailF2) (G1 : Fork) (d1 : Ctx) (tlB : HTailF2) (G2 : Fork) (d2 : Ctx),
      tl.drawMatrixF F c = .ok ((tl', F), c5) ∧
      rootInH [tl.ix.ZZ, tl.ix.BZ] L F c5 = .ok ((((), Lt), F1), c1) ∧
      Forest.pad #[tl2.z1.call, tl2.z2.call] tl2.f9.pub tl2.lidb F1 c1 = .ok ((g, Gt), cr) ∧
      tl2.heard = some g ∧ tl2.f9 = g.shape ∧ tl2.slotA = F1.next ∧ Took c1 rv cr ∧
      Forest.objects g Fb cb = .ok (((), Fa), ca) ∧
      tl2.linJoin9 Fa ca = .ok ((tlA, G1), d1) ∧ tlA.linBits9 G1 d1 = .ok ((tlB, G2), d2) ∧
      Passes G2 G' ∧
      ∀ (K : Type) [Field K] (ρ : Reading K) (en : Ent3 → Option J) (mk : ℕ → Option J)
        (m : J → K) (entry : ℕ → ℕ → ℕ → K) (H : Fork), Later G2 H →
        RowsLaw ρ (coefAll tl3 g Fc) (H.worldOf ρ (fun j => zext m (mk j)) entry)
          (fun t r i => zext m (en (t, r, i))) →
        G2.total ρ (H.worldOf ρ (fun j => zext m (mk j)) entry) =
          Fb.total ρ (H.worldOf ρ (fun j => zext m (mk j)) entry) +
            (batchAt (ρ.val Fb.theta) (lookLed Fb.nClaim
              (digForms tl2 en mk g.shape F1.next (rv.map (rdRV ρ))))).gap m := by
  obtain ⟨tl', F5, F1, c5, c1, L6, g, e1, e2, e3, e4, s1, _, k1⟩ := site_Z tl L F c _ hT hF hd
  obtain ⟨rfl, eT⟩ := drawMatrixF_ok tl tl' F F5 c c5 e1
  have eR : tl2 = { tl' with
      foldDrawn := tl'.foldDrawn + 1, slotA := F5.next, slotB := Gt.next, heard := some g } :=
    congrArg Prod.fst e4
  have eL : Lt = L6 := congrArg Prod.snd e4
  subst eL
  have i1 : tl'.ix = tl.ix := by rw [eT]
  rw [i1] at e2
  have f1 : tl2.z1 = tl'.z1 := by rw [eR]
  have f2 : tl2.z2 = tl'.z2 := by rw [eR]
  have f3 : tl2.f9 = tl'.f9 := by rw [eR]
  have f4 : tl2.lidb = tl'.lidb := by rw [eR]
  have f5 : tl2.heard = some g := by rw [eR]
  have f6 : tl2.slotA = F1.next := by
    rw [eR]
    exact (rootInH_next _ F5.next L _ _ _ _ _ e2 rfl).symm
  have hpad : Forest.pad #[tl2.z1.call, tl2.z2.call] tl2.f9.pub tl2.lidb F1 c1 =
      .ok ((g, Gt), cr) := by
    rw [f1, f2, f3, f4]
    exact e3
  obtain ⟨M, hM⟩ := pad_cut _ _ _ _ _ _ _ _ hpad
  have hsM : M.h tl2.f9.pub = tl2.f9 := t5 M.h0 hM.shape
  have hs : tl2.f9 = g.shape := by rw [pad_shape hM, hsM]
  obtain ⟨⟨h0, q1, q2, q3⟩, _, rv, ht, _, _⟩ :=
    hcOut2V Cb.Gl.E Reading.gl _ _ _ 5 _ _ _ _ _ hpad s1 k1
  have hok : FoNums.ok g.shape = true := by
    rw [q3]
    exact shape_ok q1 q2
  have hTO := tailOK_of_test t1
  obtain ⟨g', Fa, ca, tlA, G1, d1, tlB, G2, d2, o1, o2, o3, o4, o5⟩ :=
    z_objects_exact _ _ _ _ _ _ _ hO
  obtain rfl : g = g' := Option.some.inj (f5.symm.trans o1)
  obtain ⟨lO, sO⟩ := Keeps.objects g Fb cb () Fa ca o2 sb
  have aO := objects_added o2 zb
  refine ⟨tl', F1, c5, c1, g, rv, Fa, ca, tlA, G1, d1, tlB, G2, d2, e1, e2, hpad, f5, hs, f6, ht,
    o2, o3, o4, o5, fun K _ ρ en mk m entry H hH hW => ?_⟩
  obtain ⟨_, _, rv', ht', _, hI⟩ := hcOut2V K ρ _ _ _ 5 _ _ _ _ _ hpad s1 k1
  obtain rfl := took_unique ht ht'
  have h4 :=
    tail_four_lawX ρ tl2 tlA tlB tl3 (same_objectsF tl2 funs _ _ _ _ _ hO) Fa G1 G2 ca d1 d2 o3 o4 g
        f5 hs F1.next
    (rv.map (rdRV ρ)) Gt hI (hL.trans lO) hok hTO sO aO.sized (hs ▸ t6) (hs ▸ t7)
    (tail_zk_size hM tl2 hsM hTO.nc t4) t8 (fun q hq => pieceOK_of_test (t2 q hq))
    (fun q hq => apart_of_test (t3 q hq)) Fc (coefOK_of_test t9) t10 en mk (zext m) entry H hH hW
  obtain ⟨lJ, sJ⟩ := keeps_Model_HTailF2_linJoin9 tl2 Fa ca tlA G1 d1 o3 sO
  obtain ⟨lB, _⟩ := keeps_Model_HTailF2_linBits9 tlA G1 d1 tlB G2 d2 o4 sJ
  have e := look_powSum ρ g 5 F1.next (rv.map (rdRV ρ)) Gt Fb Fa G2 H cb ca o2 hI
    ((((hL.trans lO).trans lJ).trans lB).trans hH) zb
    (fun p => zext (zext m) (NumsEq.placeOf mk (plV tl2 en) p)) entry _ _ _ _ h4
  rw [lookLed_gap, ← digForms_val]
  exact e

end Fo
