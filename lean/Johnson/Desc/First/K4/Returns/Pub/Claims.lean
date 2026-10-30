-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/Pub/Claims.lean: THE WEIGHT CLAIMS OF THE SUB-PROTOCOL K4 AT TWO
ENVIRONMENTS (weightClaims, claimE, OnBytes/Model/LayerPanels.lean): general laws, each of which
compares two calls.

Limits. NOTHING HERE SAYS THAT ANY OF THESE FUNCTIONS RETURNS AT ANY PLAN. Each law says: at two
environments in the relation ClaimSkel (Skel.lean: one layout, one group, one layout of the weights,
as many challenges, each call's point as long) both calls are missing, or neither is and what they
return is alike (one unit, factors of the same sizes). Nothing is said of a factor's elements.
Nothing is evaluated. No property is claimed.

  isSome_bind_same, all2_flatten   two small laws on Option and on lists.
  zj_size, lay_skel, isMoe_skel    three readers of the environment.
  facRs_rel, facEw_rel             the two factors that are made of challenges.
  claim_rel                        one claim, at two makers of factors.
  headWeights_rel                  the heads' weights: the first array is as long.
  claimsA_rel, claimsT_rel, weightClaims_rel   the panels' claims.
  claimE_rel                       the embedding's claim, at two points and two lists of tokens: the
                                   lists are as long, and both or neither hold a token from V on.
  claimTests, claimTests_alike, claimTests_true   the count and the merge's tests on the claims
                                   themselves (not its comparison with the number of slots) as one
                                   Bool; it has one value at two lists of claims that are alike.
-/
import Johnson.Desc.First.K4.Returns.Pub.Kit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.RtPub
open OnBytes OnBytes.Model OnBytes.Model.Layer
open OnBytes.Flat (All2 OptRel FacAlike ClaimAlike optRel_bind optRel_bind_same mapM_opt_rel
  all_alike shape_alike size_foldl_modify)

variable {c c₀ : ClaimEnv}

/-- One first step, two continuations that are there together. -/
theorem isSome_bind_same {α β γ : Type} (x : Option α) {f : α → Option β} {g : α → Option γ}
    (h : ∀ a, (f a).isSome = (g a).isSome) : (x >>= f).isSome = (x >>= g).isSome := by
  cases x with
  | none => rfl
  | some a => exact h a

/-- Two lists of lists, member by member, laid end to end. The same law stands in
Johnson/Road/K4/Total/HearRowSkel.lean, over heavier imports. -/
theorem all2_flatten {β : Type} {R : β → β → Prop} {L L' : List (List β)}
    (h : All2 (All2 R) L L') : All2 R L.flatten L'.flatten := by
  induction h with
  | nil => exact .nil
  | cons h0 _ ih =>
    rw [List.flatten_cons, List.flatten_cons]
    exact h0.append ih

/-- The column's coordinates in a call's point are as many. -/
theorem zj_size (S : ClaimSkel c c₀) (q lJ : Nat) : (c.v.zj q lJ).size = (c₀.v.zj q lJ).size := by
  unfold Env.zj
  rw [Array.size_extract, Array.size_extract, S.zk q, S.y]

/-- A layer's number in the model. -/
theorem lay_skel (S : ClaimSkel c c₀) (lam : Nat) : c.v.lay lam = c₀.v.lay lam := by
  unfold Env.lay
  rw [S.y, S.g]

/-- Whether a layer has routed experts. -/
theorem isMoe_skel (S : ClaimSkel c c₀) (lam : Nat) : c.v.isMoe lam = c₀.v.isMoe lam := by
  unfold Env.isMoe
  rw [S.y]

/-- The factor on bits of the batched sumcheck's place. -/
theorem facRs_rel (S : ClaimSkel c c₀) (G : WsGrp) (lo0 wtot : Nat) :
    OptRel FacAlike (c.facRs G lo0 wtot) (c₀.facRs G lo0 wtot) := by
  unfold ClaimEnv.facRs
  dsimp only
  rw [S.rs]
  refine optRel_ite trivial (optRel_bind_same fun _ => ?_)
  refine optRel_bind (S := fun a a' => a.size = G.o ∧ a'.size = G.o)
    (amapM_size_rel G.o fun i _ => getElem?_size (eqLow_size_eq S.rs _ _) i) fun a a' h => ?_
  refine ⟨h.1.trans h.2.symm, ?_, rfl⟩
  show (Array.map _ _).size = (Array.map _ _).size
  rw [Array.size_map, Array.size_map]

/-- The factor on the entries of a segment, at the point of its call. -/
theorem facEw_rel (S : ClaimSkel c c₀) (G : WsGrp) (sn : String) (x0 : Nat) :
    OptRel FacAlike (c.facEw G sn x0) (c₀.facEw G sn x0) := by
  unfold ClaimEnv.facEw
  rw [callOf_skel S.y sn]
  refine optRel_bind_same fun x => ?_
  obtain ⟨q, cd, s⟩ := x
  dsimp only
  refine optRel_ite trivial (optRel_bind_same fun _ => ?_)
  have hz : ((c.v.zj q cd.lJ).extract 0 (cd.lJ - G.z)).size =
      ((c₀.v.zj q cd.lJ).extract 0 (cd.lJ - G.z)).size := by
    rw [Array.size_extract, Array.size_extract, zj_size S]
  refine optRel_bind (S := fun a a' => a.size = G.o ∧ a'.size = G.o)
    (amapM_size_rel G.o fun _ _ => isSome_bind_same _ fun _ =>
      getElem?_size (eqTab_size_eq hz) _) fun a a' h => ?_
  refine ⟨h.1.trans h.2.symm, ?_, rfl⟩
  show (Array.map _ _).size = (Array.map _ _).size
  rw [Array.size_map, Array.size_map]

/-- One claim, at two makers of factors. -/
theorem claim_rel (S : ClaimSkel c c₀) (X lam : Nat) {fac fac₀ : WsGrp → Option WsFac}
    (h : ∀ G, OptRel FacAlike (fac G) (fac₀ G)) :
    OptRel ClaimAlike (c.claim X lam fac) (c₀.claim X lam fac₀) := by
  unfold ClaimEnv.claim
  rw [S.lay, lay_skel S lam]
  refine optRel_bind_same fun _ => ?_
  refine optRel_bind_same fun _ => ?_
  exact optRel_bind (S := All2 FacAlike) (mapM_opt_rel h _) fun _ _ hf => ⟨rfl, hf⟩

/-- The heads' weights: the first array is as long. -/
theorem headWeights_rel (S : ClaimSkel c c₀) :
    OptRel (fun a b => a.1.size = b.1.size) c.headWeights c₀.headWeights := by
  unfold ClaimEnv.headWeights
  dsimp only
  rw [callOf_skel S.y "QK", S.y]
  refine optRel_bind_same fun x => ?_
  obtain ⟨q, cd, s⟩ := x
  dsimp only
  refine optRel_bind (cutLast_rel (zj_size S q cd.lJ) _) fun a b _ => ?_
  obtain ⟨hi, lo⟩ := a
  obtain ⟨hi₀, lo₀⟩ := b
  dsimp only
  refine optRel_bind_same fun _ => ?_
  refine optRel_bind_same fun _ => ?_
  refine optRel_bind (S := fun (a b : Array E) => a.size = b.size) ?_ fun _ _ r => ?_
  · refine foldlM_opt_rel (fun a a' _ r => ?_) _ _ _ rfl
    have e : ∀ (i : Nat) (x x' : E), (a.setIfInBounds i x).size = (a'.setIfInBounds i x').size := by
      intro i x x'
      rw [Array.size_setIfInBounds, Array.size_setIfInBounds]
      exact r
    exact optRel_ite (optRel_bind_same fun _ => e _ _ _) (optRel_bind_same fun _ => e _ _ _)
  · exact r

/-- The claims of one segment of a call of the lookup's join. -/
theorem claimsA_rel (S : ClaimSkel c c₀) (sn : String) :
    OptRel (All2 ClaimAlike) (c.claimsA sn) (c₀.claimsA sn) := by
  unfold ClaimEnv.claimsA
  dsimp only
  rw [S.y]
  refine optRel_ite (OptRel.some All2.nil) (mapM_opt_rel (fun i => ?_) _)
  simp only [isMoe_skel S]
  exact claim_rel S _ _ fun G => optRel_ite (facRs_rel S G _ _) (facEw_rel S G _ _)

/-- The claims of one segment of a call that has terms in the second token sumcheck. -/
theorem claimsT_rel (S : ClaimSkel c c₀) (sn : String) :
    OptRel (All2 ClaimAlike) (c.claimsT sn) (c₀.claimsT sn) := by
  unfold ClaimEnv.claimsT
  dsimp only
  rw [S.y]
  refine optRel_ite ?_ (optRel_ite (mapM_opt_rel (fun lm => ?_) _) (OptRel.some All2.nil))
  · refine optRel_bind (headWeights_rel S) fun a b hab => ?_
    obtain ⟨AH, lfc⟩ := a
    obtain ⟨AH₀, lfc₀⟩ := b
    dsimp only
    refine mapM_opt_rel (fun lam => claim_rel S _ _ fun G =>
      optRel_ite ?_ (optRel_ite ?_ (facRs_rel S G _ _))) _
    · exact ⟨rfl, rfl, hab⟩
    · refine ⟨rfl, rfl, ?_⟩
      show (c.ropeFactor _ _ _).size = (c₀.ropeFactor _ _ _).size
      rw [ropeFactor_size, ropeFactor_size, S.y]
  · exact claim_rel S _ _ fun G => optRel_ite (facRs_rel S G _ _)
      (optRel_ite (facRs_rel S G _ _) (facEw_rel S G _ _))

/-- **The panels' weight claims at two environments**: both lists are missing, or neither is and
they are alike, member by member. -/
theorem weightClaims_rel (S : ClaimSkel c c₀) (TS : List Nat) :
    OptRel (All2 ClaimAlike) (c.weightClaims TS) (c₀.weightClaims TS) := by
  unfold ClaimEnv.weightClaims
  dsimp only
  rw [S.y]
  refine optRel_bind (mapM_opt_rel (claimsA_rel S) _) fun _ _ ha => ?_
  refine optRel_bind (mapM_opt_rel (claimsT_rel S) _) fun _ _ ht => ?_
  exact (all2_flatten ha).append (all2_flatten ht)

/-- **The embedding's claim at two environments, two points and two lists of tokens.** -/
theorem claimE_rel (S : ClaimSkel c c₀) {ZE ZE₀ tkh tkh₀ : Array E} (hZ : ZE.size = ZE₀.size)
    (hk : tkh.size = tkh₀.size) (V : Nat) {t t₀ : Array Nat} (hs : t.size = t₀.size)
    (ha : t.any (· ≥ V) = t₀.any (· ≥ V)) :
    OptRel ClaimAlike (c.claimE ZE tkh V t) (c₀.claimE ZE₀ tkh₀ V t₀) := by
  unfold ClaimEnv.claimE
  rw [ha, hs]
  dsimp only
  rw [S.y, S.lay]
  refine optRel_ite trivial (optRel_bind_same fun _ => ?_)
  refine optRel_bind_same fun _ => ?_
  refine optRel_bind_same fun _ => ?_
  refine optRel_bind (cutLast_rel hZ _) fun a b hab => ?_
  obtain ⟨low, tok⟩ := a
  obtain ⟨low₀, tok₀⟩ := b
  have hl : low.size = low₀.size := hab.1
  dsimp only
  refine optRel_bind (S := All2 FacAlike) (mapM_opt_rel (fun G => ?_) _)
    fun _ _ hf => ⟨rfl, hf⟩
  refine optRel_ite ?_ (optRel_ite trivial ?_)
  · refine ⟨rfl, rfl, ?_⟩
    show Array.size _ = Array.size _
    rw [size_foldl_modify, size_foldl_modify]
  · have he : ((tkh ++ low).extract 0 (c₀.v.y.lPd - G.z)).size =
        ((tkh₀ ++ low₀).extract 0 (c₀.v.y.lPd - G.z)).size := by
      rw [Array.size_extract, Array.size_extract, Array.size_append, Array.size_append, hk, hl]
    refine optRel_bind (S := fun a a' => a.size = G.o ∧ a'.size = G.o)
      (amapM_size_rel G.o fun i _ => getElem?_size (eqTab_size_eq he) i) fun a a' h => ?_
    refine ⟨h.1.trans h.2.symm, ?_, rfl⟩
    show (Array.map _ _).size = (Array.map _ _).size
    rw [Array.size_map, Array.size_map]

/-- The count of the claims and the merge's tests on the claims themselves, as one Bool: not the
third clause of its first test, which compares their number with the number of slots
(OnBytes/Model/Merge.lean). n: the plan's count. -/
def claimTests (lay : WsLay) (n : Nat) (cl : Array WsClaim) : Bool :=
  cl.size == n && (!cl.isEmpty && decide (cl.size ≤ 4096)) &&
    (cl.all fun c => decide (c.ui < lay.U.size)) && (cl.all fun c => (wsClaimShape lay c).isOk)

/-- The four tests have one value at two lists of claims that are alike. -/
theorem claimTests_alike (lay : WsLay) (n : Nat) {l l₀ : List WsClaim}
    (h : All2 ClaimAlike l l₀) : claimTests lay n l.toArray = claimTests lay n l₀.toArray := by
  unfold claimTests
  have e2 : (l.toArray.all fun c => decide (c.ui < lay.U.size)) =
      (l₀.toArray.all fun c => decide (c.ui < lay.U.size)) := by
    simp only [List.all_toArray]
    exact all_alike (fun _ _ hab => by rw [hab.1]) h
  have e3 : (l.toArray.all fun c => (wsClaimShape lay c).isOk) =
      (l₀.toArray.all fun c => (wsClaimShape lay c).isOk) := by
    simp only [List.all_toArray]
    exact all_alike (fun _ _ hab => by rw [shape_alike lay hab]) h
  rw [e2, e3]
  simp only [Array.isEmpty, List.size_toArray, h.length]

/-- The four tests, one by one. -/
theorem claimTests_true {lay : WsLay} {n : Nat} {cl : Array WsClaim}
    (h : claimTests lay n cl = true) :
    (cl.size == n) = true ∧ (!cl.isEmpty && decide (cl.size ≤ 4096)) = true ∧
      (cl.all fun c => decide (c.ui < lay.U.size)) = true ∧
      (cl.all fun c => (wsClaimShape lay c).isOk) = true := by
  unfold claimTests at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

end OnBytes.Desc.First.K4.RtPub

#print axioms OnBytes.Desc.First.K4.RtPub.isSome_bind_same
#print axioms OnBytes.Desc.First.K4.RtPub.all2_flatten
#print axioms OnBytes.Desc.First.K4.RtPub.zj_size
#print axioms OnBytes.Desc.First.K4.RtPub.lay_skel
#print axioms OnBytes.Desc.First.K4.RtPub.isMoe_skel
#print axioms OnBytes.Desc.First.K4.RtPub.facRs_rel
#print axioms OnBytes.Desc.First.K4.RtPub.facEw_rel
#print axioms OnBytes.Desc.First.K4.RtPub.claim_rel
#print axioms OnBytes.Desc.First.K4.RtPub.headWeights_rel
#print axioms OnBytes.Desc.First.K4.RtPub.claimsA_rel
#print axioms OnBytes.Desc.First.K4.RtPub.claimsT_rel
#print axioms OnBytes.Desc.First.K4.RtPub.weightClaims_rel
#print axioms OnBytes.Desc.First.K4.RtPub.claimE_rel
#print axioms OnBytes.Desc.First.K4.RtPub.claimTests_alike
#print axioms OnBytes.Desc.First.K4.RtPub.claimTests_true
