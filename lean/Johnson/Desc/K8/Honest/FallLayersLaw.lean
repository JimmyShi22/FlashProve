-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/FallLayersLaw.lean: THE STATEMENT OF Johnson/Desc/K8/Honest/FallLayers.lean, PROVED:
`gathers_layers : GathersLayers`. Statements and proofs. No prover.

The proof walks the seven runs of a feed-forward segment's order from a yes of the frame's function of
claims. At each run the yes is passed down to the kind's own run (the ties), and the library's equations
on that run say what the list is and what is written:
  "objects"        `objectsBy_ok` (here; the run's text is four lines)
  "front", "back"  frontAtC, backAtC (Johnson/Desc/First/K4/RunsAtC.lean) with formsFrontWith_some,
                   formsBack_some (OnBytes/Desc/First/K4/ClaimsLaws.lean)
  "K8.equations"   k8Run_ok (Johnson/Desc/First/Batch/Law/K8Run.lean), take_four (Law/K8Four.lean)
  `drawn_F`       the ledger that the draw lays, whole
  `shown_drawn`, `frontForms_shown`   what is shown under a slot is not turned by the draw; the forms of
                   "front" read of a ledger what is shown alone
  `plainOf_plain`, `four8_plain`, `coefAt_some`
  `GatherBody`, **`layers_walk`**   one yes, walked: the four things heard are there, and `Gathers`'
                   clause holds at the letters written out off them
  **`gathers_layers`**   the statement
  **`gathers_layers_some`**   with no premise on what was heard: `Gathers` at SOME numbers and
                   coefficients
Limits: those of the statement. The ties are premises.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.FallLayers
import Johnson.Desc.K8.Honest.FallFold
import Johnson.Desc.K8.Honest.FallDraw
import Johnson.Desc.K8.Honest.FallReads
import Johnson.Desc.First.K4.RunsAtC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open OnBytes.Tie.Pv.Tail.Port (readsList)
open OnBytes.Desc.First.K4 (frontAtC backAtC frontOf formsFrontWith formsFrontWith_some
  formsBack_some formsFrontWith_core formsBack_core claimOf Wrote)

/-! ## Small things -/

theorem named_ok {α : Type} {n : String} {x : Option α} {a : α} (h : named n x = .ok a) :
    x = some a := by
  cases x with
  | none => exact absurd h (by simp [named])
  | some b => simpa [named] using h

/-- The lookup's run "objects", where it returns. -/
theorem objectsBy_ok (heard : S → Option Forest.Heard) (n : Nat) (s e : S) (c : List Claim)
    (h : K9.objectsBy heard n s = .ok (c, e)) :
    ∃ F g, s.fork? = some F ∧ heard s = some g ∧ c = plainOf g.rows.toList ∧
      e = s.putFork (F.paid g.owedObjects) := by
  simp only [K9.objectsBy] at h
  obtain ⟨F, hF, h1⟩ := K9L.ok_bind h
  obtain ⟨g, hg, h2⟩ := K9L.ok_bind h1
  have e2 := Except.ok.inj h2
  exact ⟨F, g, named_ok hF, named_ok hg, (congrArg Prod.fst e2).symm, (congrArg Prod.snd e2).symm⟩

/-- The ledger that the draw lays. -/
theorem drawn_F (rows : Nat) (chi : E) (owed : Option Nat) (used : Nat) (L : LinkCtx)
    (F : Fork) (o : K9.Drawn) (h : K9.drawnClean rows chi owed used L F = .ok o) :
    o.F = { t2FillL F L.list with
      theta := chi, thetaDrawnF := true, kapMapF := Array.replicate F.planClaimsF false } := by
  unfold K9.drawnClean at h
  obtain ⟨o', ho, h⟩ := K9L.ok_bind h
  obtain ⟨_, _, h⟩ := K9L.ok_bind h
  obtain ⟨_, _, h⟩ := K9L.ok_bind h
  obtain ⟨_, _, h⟩ := K9L.ok_bind h
  have e : o' = o := Except.ok.inj h
  subst e
  unfold K9.drawn at ho
  obtain ⟨_, _, ho⟩ := K9L.ok_bind ho
  obtain ⟨_, _, ho⟩ := K9L.ok_bind ho
  obtain ⟨_, _, ho⟩ := K9L.ok_bind ho
  obtain ⟨_, _, ho⟩ := K9L.ok_bind ho
  obtain ⟨_, _, ho⟩ := K9L.ok_bind ho
  have e := Except.ok.inj ho
  rw [← e]

/-- What is shown under a slot is not turned by the draw. -/
theorem shown_drawn (rows : Nat) (chi : E) (owed : Option Nat) (used : Nat) (L : LinkCtx)
    (F : Fork) (o : K9.Drawn) (h : K9.drawnClean rows chi owed used L F = .ok o) (j : Nat) :
    o.F.shown j = F.shown j := by
  rw [drawn_F rows chi owed used L F o h]
  rfl

/-- The forms of "front" read of a ledger what is shown under its slots alone. -/
theorem frontForms_shown (rows : Bool) (P : Layer.Pub) (g : Nat) (o : Layer.Own) (U V : Fork)
    (h : ∀ j, U.shown j = V.shown j) :
    K4Values.frontForms rows P g o U = K4Values.frontForms rows P g o V := by
  unfold K4Values.frontForms
  simp only [h]

theorem frontOf_eq (p : OnBytes.Desc.First.K4.Par) :
    frontOf p = formsFrontWith (!p.k3Runs) p.P p.g := by
  unfold frontOf
  cases p.k3Runs <;> rfl

/-- Where the listing of "front" returns, its forms are `frontForms` at the ledger handed in. -/
theorem frontForms_of {rows : Bool} {P : Layer.Pub} {g : Nat} {o : Layer.Own} {F G : Fork}
    {fs : Array Aff} (h : formsFrontWith rows P g o F = some (fs, G)) :
    K4Values.frontForms rows P g o F = some fs.toList := by
  obtain ⟨sh, pp, l, F1, F2, a1, a2, a3, rfl, -, -, -⟩ := formsFrontWith_some h
  unfold K4Values.frontForms
  simp [a1, a2, a3]

theorem plainOf_plain (l : List Aff) : ∀ cl ∈ plainOf l, cl.eqFirst = none := by
  intro cl hcl
  obtain ⟨f, -, rfl⟩ := List.mem_map.1 hcl
  rfl

theorem four8_plain (tl : HTailF2) (g : Forest.Heard) : ∀ cl ∈ K9L.four8 tl g, cl.eqFirst = none := by
  intro cl hcl
  simp only [K9L.four8, List.mem_cons, List.not_mem_nil, or_false] at hcl
  rcases hcl with rfl | rfl | rfl | rfl <;> rfl

theorem coefAt_some (l : List Claim) (c : Nat) (cl : Claim) (h : l[c]? = some cl) (t r i : Nat) :
    coefAt l c t r i = coefOn cl t r i := by
  unfold coefAt
  rw [h]

theorem wrote_here {s s' : S} {a : LayOwn} {G : Fork} (h : Wrote s a G s') :
    s.here = .lay a ∧ s'.here = .lay { a with F := G } := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨h1, by rw [h2]⟩

/-! ## The walk -/

/-- What `Gathers` says at one challenge: t the state behind the draw, (cls, e) what the function of
claims returns there. The text is `Gathers.each`'s own. -/
def GatherBody (tl : HTailF2) (funs : Array HFun) (nf nb : Nat)
    (a : Nat → Nat → Nat → Nat → Cb.Gl.E) (t e : S) (cls : List Claim) : Prop :=
  ∃ (x y : K9.Part) (tl' : HTailF2) (fr k8 bk : List Claim) (n₀ : Nat) (F₁ F₂ : Fork),
    K9.atS.get? t = some x ∧ K9.atS.get? e = some y ∧
    K9L.core y.F = K9L.core x.F ∧ treesFrame y.F.trees = treesFrame x.F.trees ∧
    e.tl? = some tl' ∧
    cls = fr ++ k8 ++ bk ∧ fr.length = nf ∧ bk.length = nb ∧
    equations n₀ tl funs F₁ = .ok (tl', F₂, k8) ∧
    F₁.theta = x.F.theta ∧ F₁.planClaimsF = x.F.planClaimsF ∧
    treesFrame F₁.trees = treesFrame x.F.trees ∧
    (∀ c cl, (fr ++ k8.take 4)[c]? = some cl →
      cl.eqFirst = none ∧ ∀ t r i, coefOn cl t r i = a c t r i) ∧
    (∀ c cl, bk[c]? = some cl →
      cl.eqFirst = none ∧ ∀ t r i, coefOn cl t r i = a (nf + k8.length + c) t r i)

/-- **One yes of the frame's function of claims behind the draw, walked run by run.** The four things
heard are there, and `Gathers`' clause holds at the numbers and coefficients written out off them. -/
theorem layers_walk (L : Link S Claim) (p4 : OnBytes.Desc.First.K4.Par) (nU : Array Nat)
    (p : K9.Where) (s : S) (a₀ : LayOwn) (ties : LinkJoin.LayersTies L p4 nU)
    (tC : ∀ run, LinkJoin.At L (1, "objects") run → LinkJoin.Under run K9.objectsCalls)
    (tD : ∀ run, LinkJoin.At L (6, "objects") run → LinkJoin.Under run K9.objectsDigits)
    (hord : L.order = orderOf .layers) (hs : s.here = .lay a₀) (d : Fmt.Drawn) (t e : S)
    (cls : List Claim) (hdr : drawnAt p s d = .ok t)
    (hg : claimsInBy L.each L.hear L.order t = .ok (cls, e)) :
    ∃ (gC gD : Forest.Heard) (o : Layer.Own) (lf : List Aff),
      a₀.lookHeard = some gC ∧ a₀.tl.heard = some gD ∧ a₀.own = some o ∧
      K4Values.frontForms (!p4.k3Runs) p4.P p4.g o a₀.F = some lf ∧
      GatherBody a₀.tl o.funs (layersFront gC gD lf).length 4
        (layersCoef (layersFront gC gD lf) (K9L.four8 a₀.tl gD) (layersBack o)
          (a₀.tl.NM + (readsList a₀.tl o.funs).length)) t e cls := by
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
  refine ⟨gC, gD, o, fs3.toList, hC, hD, ho, hf, x, y, tl', layersFront gC gD fs3.toList, c6,
    layersBack o, _, _, F6', hx, hy, ?_, ?_, ?_, ?_, rfl, ?_, q6, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hxF, hyF]
    exact s7.core
  · rw [hxF, hyF]
    exact s7.frame
  · exact lay_tl _ _ h7
  · rw [hcls, hfr, hbk]
  · simp [layersBack, plainOf, K4Values.backForms, OnBytes.Desc.First.K4.back]
  · rw [hxF]
    exact (s3.trans (SameSums.paid G3 _)).theta
  · rw [hxF]
    exact (s3.trans (SameSums.paid G3 _)).plan
  · rw [hxF]
    exact (s3.trans (SameSums.paid G3 _)).frame
  · intro c cl hc
    rw [h48] at hc
    have hlen : c < (layersFront gC gD fs3.toList).length + 4 := by
      have h5 := (List.getElem?_eq_some_iff.1 hc).1
      rw [List.length_append] at h5
      exact h5
    refine ⟨?_, fun t' r i => ?_⟩
    · rcases List.mem_append.1 (List.mem_of_getElem? hc) with hm | hm
      · unfold layersFront at hm
        rcases List.mem_append.1 hm with hm | hm
        · rcases List.mem_append.1 hm with hm | hm
          · exact plainOf_plain _ cl hm
          · exact plainOf_plain _ cl hm
        · exact plainOf_plain _ cl hm
      · exact four8_plain _ _ cl hm
    · unfold layersCoef
      rw [if_pos hlen, coefAt_some _ _ _ hc]
  · intro c cl hc
    refine ⟨plainOf_plain _ cl (List.mem_of_getElem? hc), fun t' r i => ?_⟩
    unfold layersCoef
    rw [if_neg (by rw [hk8]; omega), hk8,
      show (layersFront gC gD fs3.toList).length +
          (4 + (a₀.tl.NM + (readsList a₀.tl o.funs).length)) + c -
        ((layersFront gC gD fs3.toList).length +
          (4 + (a₀.tl.NM + (readsList a₀.tl o.funs).length))) = c by omega,
      coefAt_some _ _ _ hc]

/-! ## The statement, and what a spender wants -/

theorem gathers_layers : GathersLayers := by
  intro L p4 nU p s a₀ gC gD o lf ties tC tD hord hs hC hD ho hf
  refine ⟨fun d t e cls hdr hg => ?_⟩
  obtain ⟨gC', gD', o', lf', hC', hD', ho', hf', hb⟩ :=
    layers_walk L p4 nU p s a₀ ties tC tD hord hs d t e cls hdr hg
  obtain rfl : gC = gC' := Option.some.inj (hC.symm.trans hC')
  obtain rfl : gD = gD' := Option.some.inj (hD.symm.trans hD')
  obtain rfl : o = o' := Option.some.inj (ho.symm.trans ho')
  obtain rfl : lf = lf' := Option.some.inj (hf.symm.trans hf')
  exact hb

/-- **With no premise on what was heard.** From the ties, the order and "s stands in a feed-forward
segment": the frame's function of claims meets `Gathers` at s at SOME numbers and coefficients, and
at the list of tables that the layers' own rounds returned, if they have returned. Where one of the
four things heard is missing the function of claims returns at no state behind the draw. -/
theorem gathers_layers_some (L : Link S Claim) (p4 : OnBytes.Desc.First.K4.Par) (nU : Array Nat)
    (p : K9.Where) (s : S) (a₀ : LayOwn) (ties : LinkJoin.LayersTies L p4 nU)
    (tC : ∀ run, LinkJoin.At L (1, "objects") run → LinkJoin.Under run K9.objectsCalls)
    (tD : ∀ run, LinkJoin.At L (6, "objects") run → LinkJoin.Under run K9.objectsDigits)
    (hord : L.order = orderOf .layers) (hs : s.here = .lay a₀) :
    ∃ (funs : Array HFun) (nf nb : Nat) (a : Nat → Nat → Nat → Nat → Cb.Gl.E),
      (∀ o, a₀.own = some o → funs = o.funs) ∧
      Gathers p (claimsInBy L.each L.hear L.order) s a₀.tl funs nf nb a := by
  by_cases hyes : ∃ (d : Fmt.Drawn) (t e : S) (cls : List Claim), drawnAt p s d = .ok t ∧
      claimsInBy L.each L.hear L.order t = .ok (cls, e)
  · obtain ⟨d, t, e, cls, hdr, hg⟩ := hyes
    obtain ⟨gC, gD, o, lf, hC, hD, ho, hf, -⟩ :=
      layers_walk L p4 nU p s a₀ ties tC tD hord hs d t e cls hdr hg
    exact ⟨o.funs, _, _, _, fun o' ho' => by rw [Option.some.inj (ho.symm.trans ho')],
      gathers_layers L p4 nU p s a₀ gC gD o lf ties tC tD hord hs hC hD ho hf⟩
  · exact ⟨(a₀.own.map (·.funs)).getD #[], 0, 0, fun _ _ _ _ => 0,
      fun o ho => by rw [ho]; rfl,
      ⟨fun d t e cls hdr hg => absurd ⟨d, t, e, cls, hdr, hg⟩ hyes⟩⟩

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.layers_walk
#print axioms VerifiableInference.Desc.First.K8.Honest.gathers_layers
#print axioms VerifiableInference.Desc.First.K8.Honest.gathers_layers_some
