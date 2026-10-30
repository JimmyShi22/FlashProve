-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/FallLayersLists.lean: ONE YES OF A FEED-FORWARD SEGMENT's FUNCTION OF CLAIMS
BEHIND THE DRAW: WHICH LISTS THE CLAIMS ARE. One statement and its proof. No prover. A lemma; none
of the library's goals.

A sibling of `layers_walk` (Johnson/Desc/K8/Honest/FallLayersLaw.lean), under the same premises and
by the same walk over the seven runs. That lemma says of the claims in front of "K8.equations", of
its first four and of the claims behind it their numbers and their coefficients on entries; this one
says which lists they are: lists written off the state IN FRONT of the draw, with no batching
element in them.
  **`layers_lists`**   ∃ gC gD o lf k8: what the lookup on the calls and the lookup on the digits
      left, what the layers' own rounds returned and the forms of "front" are there, as
      `layers_walk` says; the claims are layersFront gC gD lf ++ k8 ++ layersBack o; k8's first four
      are K9L.four8 a₀.tl gD; the slot of the merge's end value (K9.mergeOf) is the same behind the
      runs as in front of the draw; and k8 is the list that "K8.equations" returns at the data a₀.tl
      and the list of tables o.funs, at some number and ledger
Limits: those of `layers_walk`. Of k8's claims behind its first four only that they are that list's.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.FallLayersLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open OnBytes.Tie.Pv.Tail.Port (readsList)
open OnBytes.Desc.First.K4 (frontAtC backAtC frontOf formsFrontWith formsFrontWith_some
  formsBack_some formsFrontWith_core formsBack_core claimOf Wrote)

/-- **Which lists the claims are**, at one yes of a feed-forward segment's function of claims behind
the draw. -/
theorem layers_lists (L : Link S Claim) (p4 : OnBytes.Desc.First.K4.Par) (nU : Array Nat)
    (p : K9.Where) (s : S) (a₀ : LayOwn) (ties : LinkJoin.LayersTies L p4 nU)
    (tC : ∀ run, LinkJoin.At L (1, "objects") run → LinkJoin.Under run K9.objectsCalls)
    (tD : ∀ run, LinkJoin.At L (6, "objects") run → LinkJoin.Under run K9.objectsDigits)
    (hord : L.order = orderOf .layers) (hs : s.here = .lay a₀) (d : Fmt.Drawn) (t e : S)
    (cls : List Claim) (hdr : drawnAt p s d = .ok t)
    (hg : claimsInBy L.each L.hear L.order t = .ok (cls, e)) :
    ∃ (gC gD : Forest.Heard) (o : Layer.Own) (lf : List Aff) (k8 : List Claim),
      a₀.lookHeard = some gC ∧ a₀.tl.heard = some gD ∧ a₀.own = some o ∧
      K4Values.frontForms (!p4.k3Runs) p4.P p4.g o a₀.F = some lf ∧
      cls = layersFront gC gD lf ++ k8 ++ layersBack o ∧ k8.take 4 = K9L.four8 a₀.tl gD ∧
      K9.mergeOf e = K9.mergeOf s ∧
      ∃ (n₀ : Nat) (F₁ F₂ : Fork) (tl' : HTailF2),
        equations n₀ a₀.tl o.funs F₁ = .ok (tl', F₂, k8) := by
  obtain ⟨a0, x0, dr, ha0, hel, hdc, htt⟩ := drawnAt_ok p s t d hdr
  have hFa : a0.F = a₀.F :=
    Option.some.inj ((K9.get_fork s a0 ha0).symm.trans (lay_fork s a₀ hs))
  -- the state behind the draw
  have h0 : t.here = .lay { a₀ with L := dr.L, F := dr.F } := by
    rw [htt]
    exact lay_set s a₀ _ hs
  have sh0 : ∀ j, dr.F.shown j = a₀.F.shown j := fun j => by
    rw [shown_drawn _ _ _ _ _ _ _ hdc j, hFa]
  rw [hord, claimsInBy_eq] at hg
  have ho7 : orderOf .layers = [(1, "objects"), (1, "guests"), (2, "front"), (6, "objects"),
      (6, "guests"), (4, "K8.equations"), (2, "back")] := rfl
  rw [ho7] at hg
  simp only [runAll] at hg
  obtain ⟨z1, g1, hg⟩ := bind_ok hg
  obtain ⟨z2, g2, hg⟩ := bind_ok hg
  obtain ⟨z3, g3, hg⟩ := bind_ok hg
  obtain ⟨z4, g4, hg⟩ := bind_ok hg
  obtain ⟨z5, g5, hg⟩ := bind_ok hg
  obtain ⟨z6, g6, hg⟩ := bind_ok hg
  obtain ⟨z7, g7, hg⟩ := bind_ok hg
  have hz7 : z7 = (cls, e) := Except.ok.inj hg
  -- 1: the lookup on the calls: "objects"
  obtain ⟨r1, c1, e1, at1, y1, rfl⟩ := step_ok g1
  obtain ⟨F1, gC, f1, k1, rfl, rfl⟩ := objectsBy_ok _ _ _ _ _ (tC r1 at1 _ _ _ _ y1)
  obtain rfl : dr.F = F1 := Option.some.inj ((lay_fork t _ h0).symm.trans f1)
  have hC : a₀.lookHeard = some gC := (lay_look t _ h0).symm.trans k1
  have h1 := lay_putFork t _ (dr.F.paid gC.owedObjects) h0
  -- 2: "guests"
  obtain ⟨r2, c2, e2, at2, y2, rfl⟩ := step_ok g2
  have i2 := Except.ok.inj (ties.tGuests 1 (by simp) r2 at2 _ _ _ _ y2)
  obtain rfl : [] = c2 := congrArg Prod.fst i2
  obtain rfl : _ = e2 := congrArg Prod.snd i2
  -- 3: "front"
  obtain ⟨r3, c3, e3, at3, y3, rfl⟩ := step_ok g3
  obtain ⟨q3, l3, u3⟩ := ties.tFront r3 at3
  obtain ⟨A3, o, fs3, G3, ho3, hf3, rfl, w3⟩ := frontAtC l3 (u3 _ _ _ _ y3)
  obtain ⟨w3a, h3⟩ := wrote_here w3
  obtain rfl : _ = A3 := Here.lay.inj (h1.symm.trans w3a)
  have ho : a₀.own = some o := ho3
  rw [frontOf_eq] at hf3
  have hf : K4Values.frontForms (!p4.k3Runs) p4.P p4.g o a₀.F = some fs3.toList := by
    have e3 : K4Values.frontForms (!p4.k3Runs) p4.P p4.g o (dr.F.paid gC.owedObjects) =
        some fs3.toList := frontForms_of hf3
    rw [frontForms_shown _ _ _ _ (dr.F.paid gC.owedObjects) a₀.F (fun j => sh0 j)] at e3
    exact e3
  have s3 : SameSums dr.F G3 :=
    (SameSums.paid dr.F _).trans (SameSums.ofCore (formsFrontWith_core hf3))
  -- 4: the lookup on the digits: "objects"
  obtain ⟨r4, c4, e4, at4, y4, rfl⟩ := step_ok g4
  obtain ⟨F4, gD, f4, k4, rfl, rfl⟩ := objectsBy_ok _ _ _ _ _ (tD r4 at4 _ _ _ _ y4)
  obtain rfl : G3 = F4 := Option.some.inj ((lay_fork _ _ h3).symm.trans f4)
  have hD : a₀.tl.heard = some gD := by
    rw [lay_tl _ _ h3] at k4
    exact k4
  have h4 := lay_putFork _ _ (G3.paid gD.owedObjects) h3
  -- 5: "guests"
  obtain ⟨r5, c5, e5, at5, y5, rfl⟩ := step_ok g5
  have i5 := Except.ok.inj (ties.tGuests 6 (by simp) r5 at5 _ _ _ _ y5)
  obtain rfl : [] = c5 := congrArg Prod.fst i5
  obtain rfl : _ = e5 := congrArg Prod.snd i5
  -- 6: "K8.equations"
  obtain ⟨r6, c6, e6, at6, y6, rfl⟩ := step_ok g6
  obtain ⟨F6, tl6, fu6, tl', F6', f6, t6, n6, q6, rfl⟩ :=
    K9L.k8Run_ok _ _ _ _ (ties.tEq r6 at6 _ _ _ _ y6)
  obtain rfl : _ = F6 := Option.some.inj ((lay_fork _ _ h4).symm.trans f6)
  obtain rfl : a₀.tl = tl6 := Option.some.inj ((lay_tl _ _ h4).symm.trans t6)
  obtain rfl : o.funs = fu6 := by
    rw [lay_funs _ _ h4] at n6
    have e6 : (a₀.own.map (·.funs)) = some fu6 := n6
    rw [ho] at e6
    exact Option.some.inj e6
  have h6 := lay_putFork _ _ F6' (lay_putTl _ _ tl' h4)
  have s6 : SameSums dr.F F6' :=
    (s3.trans (SameSums.paid G3 _)).trans (SameSums.ofSide (eq_side q6))
  obtain ⟨g8, Fa, hg8, h48, -, -⟩ := K9L.take_four q6
  obtain rfl : gD = g8 := Option.some.inj (hD.symm.trans hg8)
  obtain ⟨-, -, -, -, -, hk8, -⟩ := k8_cut q6
  -- 7: "back"
  obtain ⟨r7, c7, e7, at7, y7, rfl⟩ := step_ok g7
  obtain ⟨q7, l7, u7⟩ := ties.tBack r7 at7
  obtain ⟨A7, o7, fs7, G7, ho7', hf7, rfl, w7⟩ := backAtC l7 (u7 _ _ _ _ y7)
  obtain ⟨w7a, h7⟩ := wrote_here w7
  obtain rfl : _ = A7 := Here.lay.inj (h6.symm.trans w7a)
  obtain rfl : o = o7 := Option.some.inj (ho.symm.trans ho7')
  obtain ⟨Fb, hb7, -, -⟩ := formsBack_some hf7
  have s7 : SameSums dr.F G7 := s6.trans (SameSums.ofCore (formsBack_core hf7))
  -- the whole
  have hcls : cls = [] ++ plainOf gC.rows.toList ++ [] ++ fs3.toList.map claimOf ++
      plainOf gD.rows.toList ++ [] ++ c6 ++ fs7.toList.map claimOf := (congrArg Prod.fst hz7).symm
  have he : e7 = e := congrArg Prod.snd hz7
  subst he
  obtain ⟨x, hx, hxF⟩ := lay_part t _ h0
  obtain ⟨y, hy, hyF⟩ := lay_part e7 _ h7
  have hfr : [] ++ plainOf gC.rows.toList ++ [] ++ fs3.toList.map claimOf ++
      plainOf gD.rows.toList ++ [] = layersFront gC gD fs3.toList := by
    simp [layersFront, plainOf, claimOf]
  have hbk : fs7.toList.map claimOf = layersBack o := by
    rw [hb7]
    simp [layersBack, plainOf, claimOf, K4Values.backForms]
  refine ⟨gC, gD, o, fs3.toList, c6, hC, hD, ho, hf, by rw [hcls, hfr, hbk], h48, ?_,
    ⟨_, _, F6', tl', q6⟩⟩
  unfold K9.mergeOf
  rw [h7, hs]

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.layers_lists
