-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/ArmHeadPaid.lean: THE OUTPUT HEAD's HALF OF THE BINDER hArm
(Johnson/Desc/K1/Law/ArmHead.lean: hK6 asks HeadRest, hPl asks PlanesLeft, each inside the fence at
link 24): FOUR OF THEIR CLAUSES PAID: what the link states (KS · hSt's first half) FROM THE SCOPE; what
the readers answer (both hRd) FROM ONE FACT ON THE STATE IN FRONT: NO TABLES ARE LAID (NoTables,
Johnson/Desc/K1/Law/TablesWalkHead.lean): a clause for the letter J of ArmOk. Statements with their
proofs: calls.

Main names:
  lookup_withJoin · lookup_join      the list "the first run, join, the other runs"
  k6States_seated     **KS**: K6States at link 24's third hearing sub-protocol, by
                      k6States_of_hear (Johnson/Desc/Kinds/Law/K6StatesOfHear.lean),
                      IM.k6_of, IM.claims_lookup, IM.guardRun_yes.
  forms_silent        where no tables are laid, a link's readers ask the second reader at every run
                      that answers only where tables are laid (Tabled,
                      Johnson/Desc/K1/Law/ReadersHeadReads.lean).
  rd24                the composed meaning's readers at segment 24 are the opened chain's link's.
  hRd_k6 · hRd_planes **both clauses hRd.**
  headRunsB · headRuns [kernel] · headRuns_fails: in the fence a run under one of K6's four names
                      stands in block 3, "planes" in block 2.
  HeadLeft            HeadRest less KS and hRd. headRest_of: **HeadRest from HeadLeft.**
  hK6_of              **the premise hK6 of arm_at_reads_three, from the like with HeadLeft**, at any J
                      that gives NoTables.
What is not claimed. HeadLeft's seven clauses. NoTables at a reached state. Nothing on soundness, on an
honest prover or on hiding.
THE RECURSION LIMIT IS RAISED IN THIS FILE (maxRecDepth 1000000): for the kernel's evaluations'
elaboration alone.

-/
import Johnson.Desc.K1.Law.ArmHead
import Johnson.Desc.K1.Law.ReadersHeadReads
import Johnson.Desc.K1.Law.TablesWalkHead
import Johnson.Desc.Kinds.Law.K6StatesOfHear

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open Cb Johnson.Pack
open VerifiableInference.Desc (Block Chain Link FileDescription Place)
open VerifiableInference.Desc.First (S Here HeadOwn ModelPart Item Pub Meaning Numbers flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull runsAt MsgT MgData CellsQ mgAll d13 mgBase rowQ Mem
  seatTab dataQ)
open VerifiableInference.OnPublicFiles (headLink)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.K9 (Read Readers RunOf readerOf LinkHoles statesOfLink readersOfLink
  holesAt phAt)
open VerifiableInference.Desc.Kinds.Head (seatAt planesAt callerReaders callerKeys kind kindWithJoin
  asClaim seatedClaims blockClaims parOf lettersAt)
open VerifiableInference.Desc.Kinds.Head.Law (withTables k6Silent K6States K6Name k6States_of_hear
  readsOf workOf p8K6 K6HeardAt ColFour)
open OnBytes.Model.Verify (borderOf)
open OnBytes.Model.Stages (LinkH)
open OnBytes.Params (Rounds)
open ProofFile (Cl)

/-! ## 1 What link 24 states at its third hearing sub-protocol -/

theorem lookup_withJoin {β : Type} (cl : List (String × β)) (J : β) (n : String)
    (hn : n ≠ "join") : (cl.take 1 ++ [("join", J)] ++ cl.drop 1).lookup n = cl.lookup n := by
  have e : (n == "join") = false := by simpa using hn
  cases cl with
  | nil => simp [List.lookup, e]
  | cons a tl =>
    obtain ⟨a1, a2⟩ := a
    simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
      List.cons_append, List.nil_append, List.lookup_cons, e]

theorem lookup_join {β : Type} (a : String × β) (tl : List (String × β)) (J : β)
    (ha : a.1 ≠ "join") :
    ((a :: tl).take 1 ++ [("join", J)] ++ (a :: tl).drop 1).lookup "join" = some J := by
  obtain ⟨a1, a2⟩ := a
  have e : ("join" == a1) = false := by simpa using fun q : "join" = a1 => ha q.symm
  simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
    List.cons_append, List.nil_append, List.lookup_cons, e, beq_self_eq_true]

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **KS, from the scope.** -/
theorem k6States_seated (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (lk : Link S Cl)
    (eL : c.links[24]? = some lk) :
    K6States Bs.G₀.W.hS (readsOf Bs.G₀.W) (parOf Bs.G₀.W.hS (workOf Bs.G₀.W)) 24 4
      (statesOfLink lk) 3 := by
  obtain ⟨Lk, b, b', ms, e1, e2, -, k6, la, -⟩ := IM.k6_of hS hR O
  obtain rfl : lk = Lk := Option.some.inj (eL.symm.trans e1)
  unfold seatedClaims at k6
  obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.1 k6
  unfold blockClaims at h0
  obtain ⟨iU3, hu, rfl⟩ := Option.map_eq_some_iff.1 h0
  have hr : readsOf Bs.G₀.W = iU3 := by
    unfold Kinds.Head.Law.readsOf
    rw [hu]
    rfl
  rw [hr]
  have hcl : ∀ n, b.claims.lookup n =
      (((kind asClaim (seatAt Bs.G₀.W.hS iU3) 24 4 (parOf Bs.G₀.W.hS (workOf Bs.G₀.W))).claims.take 1
        ++ [("join", K3.joinRun (K3.seatCalls asClaim)
          (callerKeys (parOf Bs.G₀.W.hS (workOf Bs.G₀.W)) (seatAt Bs.G₀.W.hS iU3)))] ++
        (kind asClaim (seatAt Bs.G₀.W.hS iU3) 24 4
          (parOf Bs.G₀.W.hS (workOf Bs.G₀.W))).claims.drop 1).lookup n).map
        (IM.guardRun ProofFile.sameReply) := fun n => IM.claims_lookup la n
  have hj : ((kind asClaim (seatAt Bs.G₀.W.hS iU3) 24 4
        (parOf Bs.G₀.W.hS (workOf Bs.G₀.W))).claims.take 1
        ++ [("join", K3.joinRun (K3.seatCalls asClaim)
          (callerKeys (parOf Bs.G₀.W.hS (workOf Bs.G₀.W)) (seatAt Bs.G₀.W.hS iU3)))] ++
        (kind asClaim (seatAt Bs.G₀.W.hS iU3) 24 4
          (parOf Bs.G₀.W.hS (workOf Bs.G₀.W))).claims.drop 1).lookup "join" =
      some (K3.joinRun (K3.seatCalls asClaim)
        (callerKeys (parOf Bs.G₀.W.hS (workOf Bs.G₀.W)) (seatAt Bs.G₀.W.hS iU3))) :=
    lookup_join _ _ _ (by
      show "norm" ≠ "join"
      decide)
  have h3 : ∀ name, name = "norm" ∨ name = "policy" ∨ name = "logits" → ∃ run',
      (kind asClaim (seatAt Bs.G₀.W.hS iU3) 24 4
        (parOf Bs.G₀.W.hS (workOf Bs.G₀.W))).claims.lookup name = some run' := by
    rintro name (rfl | rfl | rfl) <;> exact ⟨_, rfl⟩
  have hne : ∀ name, name = "norm" ∨ name = "policy" ∨ name = "logits" → name ≠ "join" := by
    rintro name (rfl | rfl | rfl) <;> decide
  refine k6States_of_hear _ iU3 _ 24 4 lk 3 b e2 ?_ ?_ ?_
  · rintro name (h | h | h | rfl)
    · obtain ⟨r, hr'⟩ := h3 name (Or.inl h)
      exact ⟨_, by rw [hcl, lookup_withJoin _ _ _ (hne name (Or.inl h)), hr']; rfl⟩
    · obtain ⟨r, hr'⟩ := h3 name (Or.inr (Or.inl h))
      exact ⟨_, by rw [hcl, lookup_withJoin _ _ _ (hne name (Or.inr (Or.inl h))), hr']; rfl⟩
    · obtain ⟨r, hr'⟩ := h3 name (Or.inr (Or.inr h))
      exact ⟨_, by rw [hcl, lookup_withJoin _ _ _ (hne name (Or.inr (Or.inr h))), hr']; rfl⟩
    · exact ⟨_, by rw [hcl, hj]; rfl⟩
  · intro name run hn hrun
    rw [hcl, lookup_withJoin _ _ _ (hne name hn)] at hrun
    obtain ⟨run', h', rfl⟩ := Option.map_eq_some_iff.1 hrun
    exact ⟨run', h', fun k t y hy => ((IM.guardRun_yes run' k t y).1 hy).1⟩
  · intro run hrun k t y hy
    rw [hcl, hj] at hrun
    obtain rfl := Option.some.inj hrun
    exact ((IM.guardRun_yes _ k t y).1 hy).1

end

/-! ## 2 What the readers answer where no tables are laid -/

/-- Where no tables are laid, a run that answers only where tables are laid is silent: the link's
readers ask the second reader. -/
theorem forms_silent (H : LinkHoles) (lk : Link S Claim) (b : ℕ) (name : String)
    (hn : (name == "K8.equations") = false)
    (ht : ∀ r, (statesOfLink lk b).find? (fun r => r.1 == name) = some r → Tabled r.2) (s : S)
    (k : NoTables s) : (readersOfLink H lk).forms b name s = H.silent b name s := by
  have h0 : readerOf (statesOfLink lk) b name s = none := by
    cases h : readerOf (statesOfLink lk) b name s with
    | none => rfl
    | some R =>
      exfalso
      obtain ⟨r, z, f1, f2⟩ := reader_runs (statesOfLink lk) b name h
      obtain ⟨a, t, ha, hta⟩ := ht r f1 s z f2
      rw [k a ha] at hta
      cases hta
  show (if (name == "K8.equations") = true then H.small s
    else
      match readerOf (statesOfLink lk) b name s with
      | some R => some R
      | Option.none => H.silent b name s) = H.silent b name s
  rw [hn, h0]
  rfl

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}

/-- The composed meaning's readers at segment 24. -/
theorem rd24 (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (hX : headLink XV = 24)
    (lk : Link S Claim) (e : Dm.lk 24 = some lk) :
    Dm.Rd 24 = readersOfLink (holesAt XV 24 24 lk) lk := by
  show K9.readersAt Dm.lk XV (headLink XV) 24 = _
  rw [K9.readersAt_some _ _ _ _ lk e, hX]

theorem silent24 (lk : Link S Claim) :
    (holesAt XV 24 24 lk).silent = k6Silent (p8K6 XV 24) (statesOfLink lk) := by
  unfold holesAt
  simp
  rfl

end

/-! ## 3 Where the runs stand -/

/-- In the row of the output head's reads' place: a run under one of K6's four names stands in block
3, "planes" in block 2. -/
def headRunsB (b3 b2 : ℕ) : Bool :=
  (rowQ linksFull (flatPlacesOf linksFull true) (noL 24 false)).ins.all fun it =>
    match it with
    | .formsT l j n => (runsAt linksFull l j n).all fun p =>
        (!(p.2 == "norm" || p.2 == "policy" || p.2 == "logits" || p.2 == "join") || p.1 == b3) &&
          (!(p.2 == "planes") || p.1 == b2)
    | _ => true

theorem headRuns : headRunsB 3 2 = true := by decide +kernel

/-- The test can fail. -/
theorem headRuns_fails : headRunsB 2 2 = false ∧ headRunsB 3 3 = false := by decide +kernel

theorem block_of_run {p : ℕ × String}
    (h : ∃ j n, Item.formsT 24 j n ∈
      (rowQ linksFull (flatPlacesOf linksFull true) (noL 24 false)).ins ∧
        p ∈ runsAt linksFull 24 j n) :
    (K6Name p.2 → p.1 = 3) ∧ (p.2 = "planes" → p.1 = 2) := by
  obtain ⟨j, n, hi, hp⟩ := h
  have t := List.all_eq_true.1 (List.all_eq_true.1 headRuns _ hi) p hp
  obtain ⟨t1, t2⟩ := Eq.mp (Bool.and_eq_true _ _) t
  constructor
  · rintro (e | e | e | e) <;> rw [e] at t1 <;> simpa using t1
  · intro e
    rw [e] at t2
    simpa using t2

/-! ## 4 HeadRest, less what is paid -/

section
open VerifiableInference.Desc.Kinds.Head.Law VerifiableInference.Desc.Kinds.Head
  VerifiableInference.Desc.Kinds
open OnBytes (E zeroE)
open OnBytes.Model (World Reading HFun HTailF2 Fork)
open OnBytes.Model.Verify (borderOf publicOf layerShape)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.K9 (Readers RunOf)
open VerifiableInference.Desc.Sound (dataQ Mem MsgT cellsAt seatTab worldOwn ArmCellIn)

/-- **HeadRest (Johnson/Desc/K1/Law/ArmHead.lean) less KS and hRd.** -/
structure HeadLeft {Cells Tok : Type} (X : OnBytes.Model.Verify.Public)
    (own : List (Nat × Nat)) (s : S) (a b : K9.Part) (cs : OnBytes.Codes)
    (arr : Nat → Nat → Nat) (ms : List Mem) (N : Numbers) (m : Nat) (w : Wit Cells Tok MsgT)
    (cU : Nat × String) : Prop where
  hT : K6HeardAt X.hS (readsOf X) (parOf X.hS (workOf X)) s
  hbare : ∀ gk, s.lookHeard? = some gk → gk.cEnd.ents = #[]
  hwide : ∀ e F tr, withTables (p8K6 X 24) s = some e → e.fork? = some F →
      F.trees[readsOf X]? = some tr → X.H.nU.getD 2 0 ≤ tr.K
  hRun : ∀ e v, withTables (p8K6 X 24) s = some e →
      lettersAt (parOf X.hS (workOf X)) (seatAt X.hS (readsOf X)) e = .ok v →
      ∃ o cov x t, e.here = .head o ∧ e.covered X.hS.T X.hS.V = .ok cov ∧ o.x = some x ∧
        o.t = some t ∧ K8.ReadsQuiet.tables X.hS X.HLy X.H cov x = .ok t ∧
        (letI := v.1
         letI := v.2.1
         RunIs ⟨X.hS, X.HLy, borderOf X.y, X.H, cov, x, t, readsOf X⟩)
  hArr : a.L.arrayOf[readsOf X]? = some cU
  hlab : ∀ μ c i', μ < X.H.tl.NM → c < (Meaning.sizesOf X 24).k μ →
      i' < Alg.symRows ((Meaning.sizesOf X 24).m μ) → ColFour X.hS X.HLy (borderOf X.y) μ c →
      a.L.arrayOf[X.H.tl.gtTree.getD μ 0]? = some (Meaning.ownerK (Meaning.labAt X 24 μ),
        Meaning.nameOf (Meaning.ownerA (Meaning.labAt X 24 μ)))
  hride : ∀ μ c i', μ < X.H.tl.NM → c < (Meaning.sizesOf X 24).k μ →
      i' < Alg.symRows ((Meaning.sizesOf X 24).m μ) → ColFour X.hS X.HLy (borderOf X.y) μ c →
      (dataQ (N.group m) b (seatTab cs arr ms w)).cell (Meaning.ownerK (Meaning.labAt X 24 μ))
          (Meaning.nameOf (Meaning.ownerA (Meaning.labAt X 24 μ))) i' c =
        (dataQ own a (seatTab cs arr ms w)).cell (Meaning.ownerK (Meaning.labAt X 24 μ))
          (Meaning.nameOf (Meaning.ownerA (Meaning.labAt X 24 μ))) i' c

theorem headRest_of {Cells Tok : Type} {X : OnBytes.Model.Verify.Public} {Rd : Readers}
    {own : List (Nat × Nat)} {blk : Nat} {s : S} {a b : K9.Part} {cs : OnBytes.Codes}
    {arr : Nat → Nat → Nat} {ms : List Mem} {N : Numbers} {m : Nat} {w : Wit Cells Tok MsgT}
    {l piece : Nat} {states : Nat → List (RunOf S)} {cU : Nat × String}
    (L : HeadLeft X own s a b cs arr ms N m w cU)
    (KS : K6States X.hS (readsOf X) (parOf X.hS (workOf X)) l piece states blk)
    (hRd : ∀ name, K6Name name → Rd.forms blk name s = k6Silent (p8K6 X 24) states blk name s) :
    HeadRest X Rd own blk s a b cs arr ms N m w l piece states cU :=
  ⟨KS, hRd, L.hT, L.hbare, L.hwide, L.hRun, L.hArr, L.hlab, L.hride⟩

end

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A₀ : ProofFile.SharedSeat} {B₀ : ProofFile.SecondSeat}

/-- **Both clauses hRd**: at a run of link 24 that answers only where tables are laid. -/
theorem hRd_at24 (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (hX : headLink XV = 24)
    (lk : Link S Claim) (e : Dm.lk 24 = some lk) (b : ℕ) (name : String)
    (hn : (name == "K8.equations") = false)
    (ht : ∀ r, (statesOfLink lk b).find? (fun r => r.1 == name) = some r → Tabled r.2) (s : S)
    (k : NoTables s) :
    (Dm.Rd 24).forms b name s = k6Silent (p8K6 XV 24) (statesOfLink lk) b name s := by
  rw [rd24 Dm hX lk e, forms_silent _ lk b name hn ht s k, silent24]

/-- **THE PREMISE hK6 OF arm_at_reads_three, FROM THE LIKE WITH HeadLeft**, at any J that gives
NoTables. -/
theorem hK6_of (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data) (J : S → Prop)
    (hJ : ∀ s, J s → NoTables s) (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₀ B₀) (hDlk : Dm.links = linksFull)
    (hlk : ∀ l, l < 25 → Dm.lk l = c.links[l]?) (hWX : Bs.G₀.W = XV) (aN : ℕ) (R₁ R₂ R₃ : Rounds)
    (hK6' : ∀ X arrs x x' y y' w p A B,
      ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → K6Name p.2 →
      ∃ cU, HeadLeft XV (Dm.N.sent 24 0) x.2 A B Dm.cs Dm.arr Dm.ms Dm.N 24 w cU) :
    ∀ X arrs x x' y y' w p A B,
      ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → K6Name p.2 →
      ∃ l₀ piece states cU, HeadRest XV (Dm.Rd 24) (Dm.N.sent 24 0) p.1 x.2 A B Dm.cs Dm.arr Dm.ms
        Dm.N 24 w l₀ piece states cU := by
  intro X arrs x x' y y' w p A B Fc hn
  obtain ⟨cU, L⟩ := hK6' X arrs x x' y y' w p A B Fc hn
  obtain ⟨lk, _, _, _, eL, -⟩ := IM.k6_of hS hR O
  have hX : headLink XV = 24 := hWX ▸ headLink_open hS hR O
  have hp : p.1 = 3 := by
    refine (block_of_run ?_).1 hn
    obtain ⟨j, n, h1, h2⟩ := Fc.run
    refine ⟨j, n, h1, ?_⟩
    have h2' : p ∈ runsAt Dm.links 24 j n := h2
    rw [hDlk] at h2'
    exact h2'
  have KS := k6States_seated hS hR O lk eL
  rw [hWX] at KS
  refine ⟨24, 4, statesOfLink lk, cU, headRest_of L (hp ▸ KS) fun name hname => ?_⟩
  rw [hp]
  refine hRd_at24 Dm hX lk ((hlk 24 (by decide)).trans eL) 3 name ?_
    (tabled_head3 hS hR O lk eL name) x.2 (hJ _ Fc.inv)
  rcases hname with rfl | rfl | rfl | rfl <;> decide

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.lookup_withJoin
#print axioms VerifiableInference.Desc.K1.lookup_join
#print axioms VerifiableInference.Desc.K1.k6States_seated
#print axioms VerifiableInference.Desc.K1.forms_silent
#print axioms VerifiableInference.Desc.K1.rd24
#print axioms VerifiableInference.Desc.K1.silent24
#print axioms VerifiableInference.Desc.K1.headRuns
#print axioms VerifiableInference.Desc.K1.headRuns_fails
#print axioms VerifiableInference.Desc.K1.block_of_run
#print axioms VerifiableInference.Desc.K1.headRest_of
#print axioms VerifiableInference.Desc.K1.hRd_at24
#print axioms VerifiableInference.Desc.K1.hK6_of
