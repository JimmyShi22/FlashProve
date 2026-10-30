-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/ArmHead.lean: **head_at_reads**: the premise hHead of arm_at_reads
(Johnson/Desc/K1/Law/ArmAtReads.lean), to the letter: the output head's link's arm of the exchange across
its second commitment, from what the output head's files' half still asks. No law of theirs is typed.
With the letter J of arm_at_reads. (The output head's files' lemma in the goals' scope is
called.)
OBJECT: `Sound.ArmCellIn` at link 24's reads, at Dm.uH.
USER: whoever calls arm_at_reads.
LETTERS: arm_at_reads's; the output head's files' letters as they name them.
  `HeadRest`         the premises of `Kinds.Head.Law.armCellIn_K6_in_scope`
                   (Johnson/Desc/Kinds/Law/FourRunsScope.lean; the runs "norm", "policy", "logits",
                   "join"), a field each, to the letter, LESS hZ hR hX · harr · hb · htie · hCome, which
                   are paid here: KS hRd hT hbare hwide hRun hArr hlab hride (nine)
  `PlanesLeft`       the premises of `armCellIn_planes` (Johnson/Desc/Kinds/Law/PlanesCell.lean; the run
                   "planes") at the output head's files' own letters of `uHeadK6`, LESS hArrB,
                   paid here: hSt hRd hArr hwide hlen hbare hHostC
  `tablesCome_at_reads`   THE QUESTION «TablesCome at the dressed step: whose?»: THIS FILE's: behind an
                   accept of the sub-protocol at link 24's reads (the commitment, then the step without a
                   round) `TablesCome G.W s s'` holds, s THE STATE IN FRONT OF THE COMMITMENT:
                   `tablesCome_of_head` is called at the state between
  `headIs24`         [kernel] among the 25 links the output head's sort stands at 24 alone.
                   `headIs24_fails`: the test can fail
  `head_at_reads_of` | `head_at_reads`   **the premise hHead**, at a letter Mg₀ | at mgBase
  `arm_at_reads_three`   **the binder hArm with all three sorts' halves called** (arm_at_reads at
                   head_at_reads: Lean's own check that the two fit)
PREMISES LEFT: hS hR O (the top's own) · hUH : Dm.uH = `uHeadK6 XV` · hWX : Bs.G₀.W = XV (two equations on
letters) · AND THREE, POINTWISE, BEHIND
THE FENCE AT LINK 24: hK6 (at a run under K6Name: letters l₀ piece states cU with HeadRest) ·
hPl (at "planes": letters states cU with PlanesLeft) · hElse (at every other run, the lookup argument's
"objects" and "guests": ArmCellIn at Dm.uH 24, AS IT WAS: no kind's half is known for them).
PAID HERE: htie (the fence's tie) · hb (the fence) · harr, hArrB (`rides_at_reads`) · hCome · hZ hR hX
(the top's hS hR and `IM.Open.public` at hWX).
The recursion limit is raised in this file (maxRecDepth 1000000), as in
Johnson/Desc/K1/Law/ArmAtReads.lean: for the elaboration of the kernel's evaluations alone.
IS IT EMPTY HERE? NO MEMBER IS SHOWN.
What is not claimed. The premises. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.ArmAtReads
import Johnson.Desc.Kinds.Law.FourRunsScope

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

/-! ## 1 What the output head's files' two lemmas still ask -/

section
open VerifiableInference.Desc.Kinds.Head.Law VerifiableInference.Desc.Kinds.Head
  VerifiableInference.Desc.Kinds
open OnBytes (E zeroE)
open OnBytes.Model (World Reading HFun HTailF2 Fork)
open OnBytes.Model.Verify (borderOf publicOf layerShape)
open OnBytes.Road.Hd (FullH)
open OnBytes.Road (Switches Sized Sized2)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.K9 (Readers RunOf)
open VerifiableInference.Desc.Sound (dataQ Mem MsgT cellsAt seatTab worldOwn ArmCellIn)
open VerifiableInference.Desc.Kinds.Head.Law.Planes

/-- **What `armCellIn_K6_in_scope` still asks**, a field a premise, less harr hb htie hCome and the
three on the public files. -/
structure HeadRest {Cells Tok : Type} (X : OnBytes.Model.Verify.Public) (Rd : Readers)
    (own : List (Nat × Nat)) (blk : Nat) (s : S) (a b : K9.Part) (cs : OnBytes.Codes)
    (arr : Nat → Nat → Nat) (ms : List Mem) (N : Numbers) (m : Nat) (w : Wit Cells Tok MsgT)
    (l piece : Nat) (states : Nat → List (RunOf S)) (cU : Nat × String) : Prop where
  KS : K6States X.hS (readsOf X) (parOf X.hS (workOf X)) l piece states blk
  hRd : ∀ name, K6Name name → Rd.forms blk name s = k6Silent (p8K6 X 24) states blk name s
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

/-- **The output head's files' half at its four runs, in the goals' scope, called.** -/
theorem armCellIn_head {P Cells Tok : Type} {X : OnBytes.Model.Verify.Public} {Rd : Readers}
    {own : List (Nat × Nat)} {blk : Nat} {s : S} {a b : K9.Part} {cs : OnBytes.Codes}
    {arr : Nat → Nat → Nat} {ms : List Mem} {N : Numbers} {m : Nat} {w : Wit Cells Tok MsgT}
    {l piece : Nat} {states : Nat → List (RunOf S)} {cU : Nat × String}
    (h : HeadRest X Rd own blk s a b cs arr ms N m w l piece states cU) {Zl : VerifierAndGoals.PublicFiles}
    {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} (hZ : VerifierAndGoals.InScope Zl = true)
    (hR : VerifierAndGoals.readFiles Zl = .ok pp) (hX : publicOf Zl.pol Zl.KL lay = .ok X) (s' : S) (z : P)
    (harr : b.L.arrayOf = a.L.arrayOf) (hCome : TablesCome X s s') (hb : K9.segAt? s' = some b)
    (htie : First.K8.TieAt (cellsAt cs arr ms N m (z, s')) s' w) (name : String)
    (hn : K6Name name) :
    ArmCellIn Rd own (N.group m) blk name s a b (seatTab cs arr ms w) (uHeadK6 X 24) :=
  armCellIn_K6_in_scope hZ hR hX l piece blk states h.KS Rd own s s' a b cs arr ms N m z w h.hRd h.hT
    h.hbare harr h.hwide h.hRun hCome hb htie cU h.hArr h.hlab h.hride name hn

/-- **What `armCellIn_planes` still asks** at the letters of `uHeadK6 X 24`, a field a premise. -/
structure PlanesLeft (X : OnBytes.Model.Verify.Public) (Rd : Readers) (own own' : List (Nat × Nat))
    (blk : Nat) (s : S) (a b : K9.Part) (rdW : Nat × Nat → Sound.MsgQ)
    (states : Nat → List (RunOf S)) (cU : Nat × String) : Prop where
  hSt : PlanesStates (readsOf X) (p8K6 X 24).h.lmbH states blk
  hRd : Rd.forms blk "planes" s = k6Silent (p8K6 X 24) states blk "planes" s
  hArr : a.L.arrayOf[readsOf X]? = some cU
  hwide : ∀ e F tr, withTables (p8K6 X 24) s = some e → e.fork? = some F →
      F.trees[readsOf X]? = some tr → (p8K6 X 24).hp.nU.getD 2 0 ≤ tr.K
  hlen : ∀ gk, s.lookHeard? = some gk →
      gk.shape.NC * 2 ^ (gk.shape.kT + 5 - (p8K6 X 24).h.lmbH) ≤
        ((p8K6 X 24).hp.tl.mats.getD ((p8K6 X 24).h.NHf + 1 + 1) {}).k *
          (((p8K6 X 24).hp.tl.mats.getD ((p8K6 X 24).h.NHf + 1 + 1) {}).m / 2 ^ (p8K6 X 24).h.lmbH)
  hbare : ∀ gk, s.lookHeard? = some gk → gk.leaves.start.ents = #[]
  hHostC : ∀ e r gk, withTables (p8K6 X 24) s = some e →
      callerReaders (planesAt (readsOf X)) e = some r → e.lookHeard? = some gk →
      Meaning.Planes.K3HostPlanes gk.shape (p8K6 X 24).h.lmbH (_root_.Fo.rdL Reading.gl gk.zb0)
        (_root_.Fo.rdL Reading.gl gk.zb1) (nuK6 X s (Sound.dataQ own a rdW))
        (fun f => f.value Reading.gl (worldOwn b [] (Sound.dataQ own' b rdW)))
        (fun e col => (r.1 e col).getD {}) (fun col => (r.2 col).getD {})

/-- **The output head's files' half at the run "planes", called.** -/
theorem armCellIn_headPlanes {X : OnBytes.Model.Verify.Public} {Rd : Readers}
    {own own' : List (Nat × Nat)} {blk : Nat} {s : S} {a b : K9.Part}
    {rdW : Nat × Nat → Sound.MsgQ} {states : Nat → List (RunOf S)} {cU : Nat × String}
    (h : PlanesLeft X Rd own own' blk s a b rdW states cU)
    (hArrB : b.L.arrayOf[readsOf X]? = some cU) :
    ArmCellIn Rd own own' blk "planes" s a b rdW (uHeadK6 X 24) :=
  armCellIn_planes X (p8K6 X 24) blk states h.hSt Rd own own' s a b rdW h.hRd _ (nuK6 X) cU h.hArr
    hArrB h.hwide h.hlen h.hbare h.hHostC

/-- The commitment's three writes at a state in the output head's opened link. -/
theorem commit_head {Lt : Type} {s : S} {a0 : First.HeadOwn} (hs : s.here = .head a0)
    (ho : a0.opened = true) (d : _root_.Desc.Plain.DState Lt) (L : OnBytes.Model.LinkCtx)
    (F : Fork) :
    ((laid s d).putLink L).putFork F =
      { laid s d with here := .head { a0 with L := L, F := F } } := by
  simp [S.putFork, S.putLink, laid, hs, ho]

/-- **TablesCome at the dressed step.** -/
theorem tablesCome_at_reads (Z : ProofFile.Pub) (G : ProofFile.Ground) (X : OnBytes.Model.Stages.LinkH)
    (hX : G.built[24]? = some X) (pr : ℕ) (reads : Option (List ℕ)) (s s' : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (h2 : rs.length = 2)
    (h : (IM.k1Reads Z G 24 X pr reads).decide s rs gs = .ok s') : TablesCome G.W s s' := by
  intro e o t tl he ho ht htl
  obtain ⟨a0, cov, x0, t0, hs0, hop, hcov, hx0, ht0, rfl⟩ := (withTables_iff _ _ _).1 he
  obtain ⟨r₁, r₂, rfl⟩ := List.length_eq_two.1 h2
  obtain ⟨s₁, gs₁, rs₂, gs₂, h1, h3⟩ := joined_yes _ _ _ _ _ (IM.k1Quiet G 24 X) s s' r₁ r₂ gs h
  obtain ⟨_, F, _, y, _, _, _, e1, _⟩ := commitAtS_slots h1
  have hs₁ : s₁ = { laid s y.w with here := .head { a0 with L := y.L, F := y.F } } := by
    rw [e1]
    exact commit_head hs0 hop _ _ _
  have hh₁ : s₁.here = .head { a0 with L := y.L, F := y.F } := by rw [hs₁]
  have hq : (K8.ReadsQuiet.head (p8K6 G.W 24)).decide s₁ rs₂ gs₂ = .ok s' := by
    revert h3
    unfold IM.k1Quiet
    dsimp only
    cases hq : ProofFile.readsQuietAt G 24 X (if X.kind == 0 || X.kind == 1 then 4 else 5) with
    | none => exact fun h => nomatch h
    | some q =>
      intro h3
      have h3' : q.decide s₁ rs₂ gs₂ = .ok s' := h3
      rcases readsQuietAt_cases hq with hz | hz
      · exfalso
        unfold First.Att.readsAtO at hz
        obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 hz
        have h3'' : First.Att.readsAtSO A s₁ = .ok s' := h3'
        obtain ⟨a', t', tl', ha', _⟩ := _root_.Meaning.K2.readsAtSO_eq h3''
        rw [hh₁] at ha'
        cases ha'
      · rcases blockAt_cases hX hz with ⟨hp, hg, rfl⟩ | rfl
        · exfalso
          obtain ⟨a', own, tl', ha', _⟩ := K8.ReadsQuiet.layers_ok h3'
          rw [hh₁] at ha'
          cases ha'
        · exact h3'
  have hc₁ : s₁.covered (p8K6 G.W 24).h.T (p8K6 G.W 24).h.V = .ok cov := by
    rw [hs₁]
    exact hcov
  have he₁ := (withTables_iff (p8K6 G.W 24) s₁ _).2 ⟨_, cov, x0, t0, hh₁, hop, hc₁, hx0, ht0, rfl⟩
  have ho' : ({ a0 with t := some t0 } : First.HeadOwn) = o := by
    simpa using ho
  subst ho'
  obtain rfl : t0 = t := Option.some.inj ht
  exact tablesCome_of_head G.W hq _ _ t0 tl he₁ rfl rfl htl

end

/-! ## 2 The premise hHead -/

open OnBytes OnBytes.Params OnBytes.Model
open Iop Run OnBytes.Maker OnBytes.Flat
open Cb Johnson.Pack
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull MsgT MsgQ MgData CellsQ mgAll mgBase d13 rowQ seatTab
  UFn ArmCellIn)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.Kinds.Head.Law (uHeadK6 K6Name TablesCome)
open VerifiableInference.Desc.First.Att.P (uArm)
open OnBytes.Road.K4 (uLay)
open OnBytes.Model.Stages (LinkH)
open OnBytes.Params (Rounds)
open ProofFile (Cl)

theorem headIs24 : ((List.range 25).all fun l =>
    !((linksFull[l]?).getD .layers == .head) || l == 24) = true := by
  decide +kernel

/-- **The test can fail**: at another number. -/
theorem headIs24_fails : ((List.range 25).all fun l =>
    !((linksFull[l]?).getD .layers == .head) || l == 23) = false := by
  decide +kernel

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)
  (Mg₀ : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))

/-- **The premise hHead of arm_at_reads_of.** -/
theorem head_at_reads_of (J : S → Prop) {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)} {c : Chain S Cl}
    {A₀ : ProofFile.SharedSeat} {B₀ : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A₀ B₀)
    (hUH : Dm.uH = uHeadK6 XV) (hWX : Bs.G₀.W = XV) (aN : ℕ) (R₁ R₂ R₃ : Rounds)
    (hK6 : ∀ X arrs x x' y y' w p A B, ReadsFence Dm dk Mg₀ J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → K6Name p.2 →
      ∃ l₀ piece states cU, HeadRest XV (Dm.Rd 24) (Dm.N.sent 24 0) p.1 x.2 A B Dm.cs Dm.arr Dm.ms Dm.N
        24 w l₀ piece states cU)
    (hPl : ∀ X arrs x x' y y' w p A B, ReadsFence Dm dk Mg₀ J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → p.2 = "planes" →
      ∃ states cU, PlanesLeft XV (Dm.Rd 24) (Dm.N.sent 24 0) (Dm.N.group 24) p.1 x.2 A B
        (seatTab Dm.cs Dm.arr Dm.ms w) states cU)
    (hElse : ∀ X arrs x x' y y' w p A B, ReadsFence Dm dk Mg₀ J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → ¬ K6Name p.2 → p.2 ≠ "planes" →
      ArmCellIn (Dm.Rd 24) (Dm.N.sent 24 0) (Dm.N.group 24) p.1 p.2 x.2 A B
        (seatTab Dm.cs Dm.arr Dm.ms w) (Dm.uH 24)) :
    ∀ l X arrs x x' y y' w p A B, ReadsFence Dm dk Mg₀ J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .head →
      ArmCellIn (Dm.Rd l) (Dm.N.sent l 0) (Dm.N.group l) p.1 p.2 x.2 A B
        (seatTab Dm.cs Dm.arr Dm.ms w) (Dm.uH l) := by
  intro l X arrs x x' y y' w p A B F hsub
  obtain rfl : l = 24 := by
    have t := List.all_eq_true.1 headIs24 l (List.mem_range.2 F.lt)
    rw [hsub] at t
    exact eq_of_beq t
  have hr := rides_at_reads F
  by_cases hn : K6Name p.2
  · have hTC : TablesCome XV x.2 x'.2 := by
      obtain ⟨_, rs, gs, hfit, hd⟩ := F.yes
      have hlen : (rs.map noDigest).length = 2 := by
        rw [List.length_map, Keeps.fit_length _ _ hfit, rounds_blkL]
      rw [← hWX]
      exact tablesCome_at_reads Z Bs.G₀ X F.built _ arrs x.2 x'.2 _ gs hlen hd
    obtain ⟨l₀, piece, states, cU, L⟩ := hK6 X arrs x x' y y' w p A B F hn
    rw [hUH]
    exact armCellIn_head L hS hR (hWX ▸ O.public) x'.2 x'.1 hr.arrays hTC F.behind F.tie p.2 hn
  · by_cases hp : p.2 = "planes"
    · obtain ⟨states, cU, L⟩ := hPl X arrs x x' y y' w p A B F hp
      rw [hUH, hp]
      exact armCellIn_headPlanes L (by rw [hr.arrays]; exact L.hArr)
    · exact hElse X arrs x x' y y' w p A B F hn hp

/-- **THE PREMISE hHead OF arm_at_reads, TO THE LETTER.** -/
theorem head_at_reads (J : S → Prop) {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)} {c : Chain S Cl}
    {A₀ : ProofFile.SharedSeat} {B₀ : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A₀ B₀)
    (hUH : Dm.uH = uHeadK6 XV) (hWX : Bs.G₀.W = XV) (aN : ℕ) (R₁ R₂ R₃ : Rounds)
    (hK6 : ∀ X arrs x x' y y' w p A B, ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → K6Name p.2 →
      ∃ l₀ piece states cU, HeadRest XV (Dm.Rd 24) (Dm.N.sent 24 0) p.1 x.2 A B Dm.cs Dm.arr Dm.ms Dm.N
        24 w l₀ piece states cU)
    (hPl : ∀ X arrs x x' y y' w p A B, ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → p.2 = "planes" →
      ∃ states cU, PlanesLeft XV (Dm.Rd 24) (Dm.N.sent 24 0) (Dm.N.group 24) p.1 x.2 A B
        (seatTab Dm.cs Dm.arr Dm.ms w) states cU)
    (hElse : ∀ X arrs x x' y y' w p A B, ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → ¬ K6Name p.2 → p.2 ≠ "planes" →
      ArmCellIn (Dm.Rd 24) (Dm.N.sent 24 0) (Dm.N.group 24) p.1 p.2 x.2 A B
        (seatTab Dm.cs Dm.arr Dm.ms w) (Dm.uH 24)) :
    ∀ l X arrs x x' y y' w p A B, ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .head →
      ArmCellIn (Dm.Rd l) (Dm.N.sent l 0) (Dm.N.group l) p.1 p.2 x.2 A B
        (seatTab Dm.cs Dm.arr Dm.ms w) (Dm.uH l) :=
  head_at_reads_of Dm dk mgBase J hS hR O hUH hWX aN R₁ R₂ R₃ hK6 hPl hElse

/-- **THE BINDER hArm, BEHIND THE TIE AND ArmOk J, WITH ALL THREE SORTS' HALVES CALLED**:
arm_at_reads with its premise hHead paid by head_at_reads: Lean's own check that the two fit. -/
theorem arm_at_reads_three (J : S → Prop) {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)} {c : Chain S Cl}
    {A₀ : ProofFile.SharedSeat} {B₀ : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A₀ B₀)
    (hDlk : Dm.links = linksFull) (aN : ℕ) (R₁ R₂ R₃ : Rounds)
    (hLay : ∀ l X arrs x x' y y' w p A B, ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .layers →
      ∀ b₀ o hp tl', x.2.here = .lay b₀ → b₀.own = some o → Bs.G₀.W.G[X.g]? = some hp →
      x'.2.tl? = some tl' →
      ∀ e cc, NamedEntry (Dm.Rd l) (Dm.N.sent l 0) p.1 p.2 x.2 A e cc →
      ∃ M n, Dm.uL l x.2 = uLay hp.tl M x.2 ∧
        LayRest (oneEntry e) (Dm.N.sent l 0) p.1 p.2 x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) hp.tl tl' M o n
          (Dm.A1 l x' w))
    (hUA : Dm.uA = uArm XV)
    (hAtt : ∀ l X arrs x x' y y' w p A B, ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .attention →
      ∀ a₀ Ap tlF tl', x.2.here = .att a₀ → Bs.G₀.W.A[X.g]? = some Ap → x.2.tl? = some tlF →
      x'.2.tl? = some tl' →
      ∀ e cc, NamedEntry (Dm.Rd l) (Dm.N.sent l 0) p.1 p.2 x.2 A e cc →
      ∃ i, AttRest XV (oneEntry e) (Dm.N.sent l 0) p.1 p.2 x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) l Ap i
        tlF tl' (Dm.A1 l x' w))
    (hUH : Dm.uH = uHeadK6 XV) (hWX : Bs.G₀.W = XV)
    (hK6 : ∀ X arrs x x' y y' w p A B, ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → K6Name p.2 →
      ∃ l₀ piece states cU, HeadRest XV (Dm.Rd 24) (Dm.N.sent 24 0) p.1 x.2 A B Dm.cs Dm.arr Dm.ms Dm.N
        24 w l₀ piece states cU)
    (hPl : ∀ X arrs x x' y y' w p A B, ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → p.2 = "planes" →
      ∃ states cU, PlanesLeft XV (Dm.Rd 24) (Dm.N.sent 24 0) (Dm.N.group 24) p.1 x.2 A B
        (seatTab Dm.cs Dm.arr Dm.ms w) states cU)
    (hElse : ∀ X arrs x x' y y' w p A B, ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → ¬ K6Name p.2 → p.2 ≠ "planes" →
      ArmCellIn (Dm.Rd 24) (Dm.N.sent 24 0) (Dm.N.group 24) p.1 p.2 x.2 A B
        (seatTab Dm.cs Dm.arr Dm.ms w) (Dm.uH 24)) :
    ∀ l, l < 25 → ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ (x x' : ProofFile.InstPub × S) y y'
      (w : Wit (CellsQ rows cols) Tok MsgT),
      YesOf (blkL Z Bs.G₀ l false X arrs) x x' → InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)) linksFull (flatPlacesOf linksFull true) (noL l false) x y →
      ArmOk J x.2 →
      KeptBelow (baseL aN R₁ R₂ R₃ c l false) y y' → (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)).tie l x' y' w →
      ∀ j n, Item.formsT l j n ∈ (rowQ linksFull (flatPlacesOf linksFull true) (noL l false)).ins →
      ∀ p ∈ Dm.runs l j n, ∀ A B, K9.segAt? x.2 = some A → K9.segAt? x'.2 = some B →
      ArmCellIn (Dm.Rd l) (Dm.N.sent l 0) (Dm.N.group l) p.1 p.2 x.2 A B
        (seatTab Dm.cs Dm.arr Dm.ms w) (armOf Dm.uL Dm.uA Dm.uH ((linksFull[l]?).getD .layers) l) :=
  arm_at_reads Dm dk J hDlk Z Bs aN R₁ R₂ R₃ c hLay hUA hAtt
    (head_at_reads Dm dk J hS hR O hUH hWX aN R₁ R₂ R₃ hK6 hPl hElse)

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.armCellIn_head
#print axioms VerifiableInference.Desc.K1.armCellIn_headPlanes
#print axioms VerifiableInference.Desc.K1.tablesCome_at_reads
#print axioms VerifiableInference.Desc.K1.headIs24
#print axioms VerifiableInference.Desc.K1.headIs24_fails
#print axioms VerifiableInference.Desc.K1.head_at_reads_of
#print axioms VerifiableInference.Desc.K1.head_at_reads
#print axioms VerifiableInference.Desc.K1.arm_at_reads_three
