-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/K8Tests/PlanFitsOfPublic.lean: THE TEST WITH CODE planFitsAllB
(Johnson/Desc/First/K8/PlanFitsAll.lean) SAYS YES AT EVERYTHING THAT THE VERIFIER's OWN publicOf
RETURNS: at all public files, in the goals' scope or not. Statements and proofs; nothing is
evaluated at particular files.

  planFitsAllB_of_public   publicOf pol KL lay = .ok X → planFitsAllB X = true

How. planFitsB tl asks three facts of a plan's value tl of the approximate range proof: (1) the
shapes fit the matrices; (2) every matrix has its tree's number (NM ≤ gtTree.size); (3) the third
vector of reads is in the list of arrays (ix.U[2]? = some (some _)). (1) is proved for the layers'
groups and the output head (planG_fits, planH2_fits) and follows for the attention groups from
addTreesF_fits. (2), as the equation gtTree.size = NM, and (3), together "GtU", are made by
HTailF2.shapeF (OnBytes/Model/Tail.lean): its third loop pushes just one tree's number a matrix, and
all three callers pass the literal list
#[false, false, true, false] for "which vectors of reads". What follows shapeF in the three plans
(addTreesF, ownerIs, borderMeans, ownerHeld, the owners' places) turns none of NM, gtTree, ix.
  piecesF_keeps, shapeF_gtU, addTreesF_gtU, borderMeans_gtU, ownerHeld_gtU: the routines, one by one
  planG_gtU, planH2_gtU, seamPlan_both: the three plans (ownerIs: by rfl inside planG_gtU)
  both_layers, both_attention, both_head: all three facts at what publicOf returns
  planFitsB_of: the test from the three facts

Limits. The premise is that publicOf returns: that it does at any file is not said here. Nothing on
the built links: that a link's value is its plan's is another file's. Nothing on soundness.
GtU's first half is the equation (another test, gtSizesAllB, asks it).


-/
import Johnson.Desc.First.K8.PlanFitsAll
import OnBytes.Model.Fit.ShapeFCaps
import OnBytes.Model.Fit.AttCaps
import OnBytes.Tie.Pv.Tail.EndInvRuns
import OnBytes.Tie.Pv.Tail.EndHeadForms
import OnBytes.Tie.Pv.Lookup.Ends.FoPublic
import OnBytes.Tie.Pv.Lookup.Ends.FoPublicAPlFor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LT28.K8Tests

open OnBytes OnBytes.Model
open OnBytes.Model.Verify (publicOf)
open OnBytes.Tie.Pv.Tail (Port.Fits)
open VerifiableInference.Desc.First.K8.Ready (planFitsB planFitsAllB)

private theorem okB {α β : Type} {x : Except String α} {f : α → Except String β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem okJ {c : Prop} [Decidable c] {e : String} {β : Type}
    {jp : PUnit.{1} → Except String β} {y : β}
    (h : (if c then (throw e >>= jp) else (pure PUnit.unit >>= jp)) = .ok y) :
    ¬ c ∧ jp PUnit.unit = .ok y := by
  by_cases hc : c
  · rw [if_pos hc] at h
    have h' : (Except.error e : Except String β) = .ok y := h
    cases h'
  · rw [if_neg hc] at h
    exact ⟨hc, h⟩

private theorem forInK {α σ : Type} (f : α → σ → Except String (ForInStep σ)) (l0 : List α)
    (I : List α → σ → Prop)
    (step : ∀ pre a rest, l0 = pre ++ a :: rest → ∀ s s', I pre s → f a s = .ok s' →
      ∃ t, s' = .yield t ∧ I (pre ++ [a]) t) :
    ∀ (l pre : List α) (s r : σ), l0 = pre ++ l → I pre s → forIn l s f = .ok r → I l0 r
  | [], pre, s, r, e, hI, h => by
    rw [List.forIn_nil] at h
    have hr : s = r := Except.ok.inj h
    rw [e, List.append_nil, ← hr]
    exact hI
  | a :: l, pre, s, r, e, hI, h => by
    rw [List.forIn_cons] at h
    obtain ⟨s', hs, h⟩ := okB h
    obtain ⟨t, rfl, hI'⟩ := step pre a l e s s' hI hs
    exact forInK f l0 I step l (pre ++ [a]) t r (by rw [e]; simp) hI' h

/-- The second fact that planFitsB asks, as an equation, and the third. -/
def GtU (tl : HTailF2) : Prop := tl.gtTree.size = tl.NM ∧ ∃ t, tl.ix.U[2]? = some (some t)

/-- GtU reads NM, gtTree and ix alone. -/
theorem GtU.of_same {a b : HTailF2} (h : GtU a) (h1 : b.NM = a.NM) (h2 : b.gtTree = a.gtTree)
    (h3 : b.ix = a.ix) : GtU b := by
  unfold GtU
  rw [h1, h2, h3]
  exact h

/-- shapeF's last act keeps the three fields. -/
theorem piecesF_keeps {tl tl' : HTailF2} (h : tl.piecesF = .ok tl') :
    tl'.NM = tl.NM ∧ tl'.gtTree = tl.gtTree ∧ tl'.ix = tl.ix := by
  unfold HTailF2.piecesF at h
  obtain ⟨bz, _, h⟩ := okB h
  obtain ⟨_, h⟩ := okJ h
  obtain ⟨_, h⟩ := okJ h
  obtain ⟨f9, _, h⟩ := okB h
  obtain ⟨pub, _, h⟩ := okB h
  obtain ⟨_, _, h⟩ := okB h
  have e := (Except.ok.inj h).symm
  subst e
  exact ⟨rfl, rfl, rfl⟩

/-- **What shapeF returns, called as the three plans call it, has the two facts.** -/
theorem shapeF_gtU {tl tl' : HTailF2} {m : Array TMat} {txOf : Array (Option Nat)}
    {f : Array T2Foreign} {tau : Nat}
    (h : tl.shapeF m txOf f #[false, false, true, false] tau = .ok tl') : GtU tl' := by
  unfold HTailF2.shapeF at h
  obtain ⟨_, h⟩ := okJ h
  obtain ⟨_, h⟩ := okJ h
  obtain ⟨r1, _, h⟩ := okB h
  obtain ⟨kTX, pkMat, pxMat⟩ := r1
  obtain ⟨_, h⟩ := okJ h
  obtain ⟨r2, h2, h⟩ := okB h
  obtain ⟨U, count⟩ := r2
  obtain ⟨r3, h3, h⟩ := okB h
  obtain ⟨gtTree, mz, nPK, nextF, off, plFor, plOwn⟩ := r3
  obtain ⟨_, h⟩ := okJ h
  obtain ⟨_, h⟩ := okJ h
  obtain ⟨e1, e2, e3⟩ := piecesF_keeps h
  clear h
  have hU : (#[none, none, some 0, none] : Array (Option Nat)) = U :=
    congrArg MProd.fst (Except.ok.inj h2)
  have K3 := forInK _ (List.range m.size)
    (fun pre (s : MProd (Array Nat) (MProd Nat (MProd Nat (MProd Nat (MProd (Array Nat)
        (MProd (Array PlaceF) (Array PlaceF))))))) => s.fst.size = pre.length)
    (fun pre a rest _ s s' hI hs => by
      obtain ⟨gt, mz', nPK', nextF', off', plFor', plOwn'⟩ := s
      dsimp only at hs hI
      obtain ⟨_, hs⟩ := okJ hs
      obtain ⟨_, hs⟩ := okJ hs
      split at hs
      · split at hs
        · exact ⟨_, (Except.ok.inj hs).symm, by simp [hI]⟩
        · exact ⟨_, (Except.ok.inj hs).symm, by simp [hI]⟩
      · split at hs
        · split at hs
          · simp only [pure_bind] at hs
            split at hs
            · split at hs
              · cases hs
              · split at hs
                · cases hs
                · exact ⟨_, (Except.ok.inj hs).symm, by simp [hI]⟩
            · cases hs
          · cases hs
        · cases hs)
    (List.range m.size) [] _ _ rfl rfl h3
  have k : gtTree.size = m.size := by simpa using K3
  refine ⟨?_, 0, ?_⟩
  · rw [e1, e2]
    exact k
  · rw [e3, ← hU]
    rfl

/-- The making of the list of arrays keeps the two facts. -/
theorem addTreesF_gtU {tl tl' : HTailF2} {F F' : Fork} {T T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (h : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', F', T')) (hg : GtU tl) :
    GtU tl' := by
  have e := (OnBytes.Tie.Pv.Tail.Port.addTreesF_fits _ _ _ _ _ _ _ _ _ _ h).2.2
  exact hg.of_same (by rw [e]) (by rw [e]) (by rw [e])

/-- Recording which array of an earlier sub-proof is meant keeps the two facts. -/
theorem borderMeans_gtU {tl tl' : HTailF2} {iF ownerNo index : Nat}
    (h : tl.borderMeans iF ownerNo index = .ok tl') (hg : GtU tl) : GtU tl' := by
  unfold HTailF2.borderMeans at h
  split at h
  · cases h
  · split at h
    · cases h
    · obtain rfl := Except.ok.inj h
      exact hg.of_same rfl rfl rfl

open OnBytes.Tie.Pv.Tail.Port (excBind_ok throw_bind_ne) in
/-- **A layers' group's plan has the two facts.** -/
theorem planG_gtU (P : Layer.Pub) (g : Nat) (O : Option Layer.HPlan2) (hp : Layer.HPlan2)
    (h : Layer.planG P g O = .ok hp) : GtU hp.tl := by
  unfold Layer.planG at h
  obtain ⟨⟨mats, txOf, ft⟩, -, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨tl0, hS, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨⟨tla, Fa, Ta⟩, hadd, h⟩ := (excBind_ok _ _ _).1 h
  have f0 : GtU tla := addTreesF_gtU hadd (shapeF_gtU hS)
  obtain ⟨Tp, -, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
  dsimp only at h
  cases O with
  | none =>
    dsimp only at h
    obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨y, hy, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain rfl := Except.ok.inj hy
    obtain rfl := Except.ok.inj h
    exact f0.of_same rfl rfl rfl
  | some O =>
    dsimp only at h
    split at h
    · obtain ⟨y, -, h⟩ := (excBind_ok _ _ _).1 h
      obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
      obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
      obtain ⟨tlB, hbm, h⟩ := (excBind_ok _ _ _).1 h
      obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
      obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
      obtain ⟨y2, hy, h⟩ := (excBind_ok _ _ _).1 h
      obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
      obtain rfl := Except.ok.inj hy
      obtain rfl := Except.ok.inj h
      exact borderMeans_gtU hbm (f0.of_same rfl rfl rfl)
    · exact absurd h (throw_bind_ne _ _ _)

open OnBytes.Tie.Pv.Tail.Port (excBind_ok throw_bind_ne) in
/-- The comparison with the plan of the last group of layers keeps the two facts. -/
theorem ownerHeld_gtU (O : Head.Owner) (NGr : Nat) (tl tl' : HTailF2) (Fp : Fork) (Tp : Tail2)
    (h : Head.ownerHeld O NGr tl Fp Tp = .ok tl') (hg : GtU tl) : GtU tl' := by
  unfold Head.ownerHeld at h
  dsimp only at h
  split at h
  · obtain ⟨y, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨tlB, hbm, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain rfl := Except.ok.inj h
    exact borderMeans_gtU hbm hg
  · exact absurd h (throw_bind_ne _ _ _)

open OnBytes.Tie.Pv.Tail.Port (excBind_ok throw_bind_ne) in
/-- **The output head's plan has the two facts.** -/
theorem planH2_gtU (g : Settings) (hS : Head.Shape) (Lh : Head.HL) (b : Head.Border)
    (O : Head.Owner) (NGr lkW : Nat) (hp : Head.HPlanH2)
    (h : Head.planH2 g hS Lh b O NGr lkW = .ok hp) : GtU hp.tl := by
  unfold Head.planH2 at h
  obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
  dsimp only at h
  split at h
  · obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨tl0, hsh, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨⟨tla, Fa, Ta⟩, hadd, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨Tp, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨tlF, ho, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain rfl := Except.ok.inj h
    exact ownerHeld_gtU _ _ _ _ _ _ ho (addTreesF_gtU hadd (shapeF_gtU hsh))
  · exact absurd h (throw_bind_ne _ _ _)

/-- **An attention group's seam, as Seam.plan returns it, has all three facts.** -/
theorem seamPlan_both {s s' : Attention.Seam} {nU3 hb hbLine : Nat}
    (e : s.plan nU3 hb hbLine = .ok s') (hg : GtU s.tl) : Port.Fits s'.tl ∧ GtU s'.tl := by
  unfold Attention.Seam.plan at e
  dsimp only at e
  obtain ⟨⟨tl, Fp, T⟩, hr, e⟩ := okB e
  dsimp only at e
  obtain ⟨_, e⟩ := okJ e
  obtain ⟨_, _, e⟩ := okB e
  cases e
  exact ⟨(OnBytes.Tie.Pv.Tail.Port.addTreesF_fits _ _ _ _ _ _ _ _ _ _ hr).1, addTreesF_gtU hr hg⟩

/-- The test, from the three facts. -/
theorem planFitsB_of {tl : HTailF2} (hf : Port.Fits tl) (hg : GtU tl) : planFitsB tl = true := by
  obtain ⟨h1, t, h2⟩ := hg
  unfold planFitsB
  rw [h2]
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq, decide_eq_true_eq,
    and_true]
  exact ⟨fun mu hmu => hf mu hmu, Nat.le_of_eq h1.symm⟩

section
variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Verify.Public}

/-- All three facts at every layers' group. -/
theorem both_layers (h : publicOf pol KL lay = .ok X) {g : Nat} {hp : Layer.HPlan2}
    (hg : X.G[g]? = some hp) : Port.Fits hp.tl ∧ GtU hp.tl :=
  ⟨OnBytes.Tie.Pv.Tail.planG_fits _ _ _ _ (Fo.Pub.public_G h g hp hg),
    planG_gtU _ _ _ _ (Fo.Pub.public_G h g hp hg)⟩

/-- All three facts at every attention group. -/
theorem both_attention (h : publicOf pol KL lay = .ok X) {g : Nat} {a : Attention.Plan}
    (hg : X.A[g]? = some a) : Port.Fits a.seam.tl ∧ GtU a.seam.tl := by
  obtain ⟨a0, hp, ea⟩ := Fo.PubA.public_A_plFor h g a hg
  obtain ⟨seam0, h0, h1, _⟩ := Fo.BatRows.planA_rows0 _ _ _ _ hp
  obtain ⟨f, hF⟩ := OnBytes.Model.Fit.seamShape_F h0
  obtain ⟨k1, k2⟩ := seamPlan_both h1 (shapeF_gtU hF)
  have e : a.seam.tl = { a0.seam.tl with plFor := a.seam.tl.plFor } := by
    conv_lhs => rw [ea]
  exact ⟨k1.of_same (by rw [e]) (by rw [e]) (by rw [e]),
    k2.of_same (by rw [e]) (by rw [e]) (by rw [e])⟩

/-- All three facts at the output head. -/
theorem both_head (h : publicOf pol KL lay = .ok X) : Port.Fits X.H.tl ∧ GtU X.H.tl := by
  obtain ⟨H0, h1, h2⟩ := Fo.Pub.public_H h
  have e : X.H.tl = H0.tl := by rw [h2]
  rw [e]
  exact ⟨OnBytes.Tie.Pv.Tail.planH2_fits _ _ _ _ _ _ _ _ h1, planH2_gtU _ _ _ _ _ _ _ _ h1⟩

/-- At every layers' group. -/
theorem fits_layers (h : publicOf pol KL lay = .ok X) {g : Nat} {hp : Layer.HPlan2}
    (hg : X.G[g]? = some hp) : planFitsB hp.tl = true :=
  planFitsB_of (both_layers h hg).1 (both_layers h hg).2

/-- At every attention group. -/
theorem fits_attention (h : publicOf pol KL lay = .ok X) {g : Nat} {a : Attention.Plan}
    (hg : X.A[g]? = some a) : planFitsB a.seam.tl = true :=
  planFitsB_of (both_attention h hg).1 (both_attention h hg).2

/-- At the output head. -/
theorem fits_head (h : publicOf pol KL lay = .ok X) : planFitsB X.H.tl = true :=
  planFitsB_of (both_head h).1 (both_head h).2

/-- **THE TEST SAYS YES AT EVERYTHING THAT publicOf RETURNS.** -/
theorem planFitsAllB_of_public (h : publicOf pol KL lay = .ok X) : planFitsAllB X = true := by
  unfold planFitsAllB
  simp only [Bool.and_eq_true, Array.all_eq_true]
  refine ⟨⟨fun i hi => ?_, fun i hi => ?_⟩, fits_head h⟩
  · exact fits_layers h (Array.getElem?_eq_getElem hi)
  · exact fits_attention h (Array.getElem?_eq_getElem hi)

end

end LT28.K8Tests

#print axioms LT28.K8Tests.shapeF_gtU
#print axioms LT28.K8Tests.planG_gtU
#print axioms LT28.K8Tests.planH2_gtU
#print axioms LT28.K8Tests.seamPlan_both
#print axioms LT28.K8Tests.both_layers
#print axioms LT28.K8Tests.both_attention
#print axioms LT28.K8Tests.both_head
#print axioms LT28.K8Tests.fits_layers
#print axioms LT28.K8Tests.fits_attention
#print axioms LT28.K8Tests.fits_head
#print axioms LT28.K8Tests.planFitsAllB_of_public
