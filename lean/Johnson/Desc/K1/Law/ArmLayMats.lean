-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/ArmLayMats.lean: THE FIELD hM OF THE FEED-FORWARD LINKS' HALF OF THE EXCHANGE (LayRest,
Johnson/Desc/K1/Law/ArmHalves.lean: "inside the ranges the matrices M at the data in front of the second
commitment are the small integers behind the committed symbols") AT M := the matrices made of the data
(`Sound.matsOfData`: the feed-forward links' files' own arm `uLAt` has it so, Johnson/Road/K4/ULayAt.lean) IS
NO PREMISE ON THE WITNESS: it follows from the tie, under one clause on the state in front and sentences
on letters. AND **hLay_ofJ**: the field hLay of k01_fifty_paid
(K01FiftyPaid.lean), IN ITS OWN TYPE (its text taken by program).
  `closed_like`, `layLike_over_reads`   over an accept at a feed-forward link's reads the closed parameters
                   are like THE PLAN's (the step closes the plan's own: `K8.ReadsQuiet.layers_ok`,
                   `K8.Order.close_lays`)
  `layIsEven` [by evaluation], `group_lay`   in scope the built link at a feed-forward link l has the group l / 2
                   (`IM.ground_named`)
  `layM_of`          **the field hM** at M := matsOfData hp.tl names: `Meaning.Reads.tie_named` at the fence's
                   tie; then matsOfData_of_packs · cell_back (Johnson/Desc/K1/Law/ArmAttMats.lean)
  `JLay`             what stays, a clause for the letter J, on the state in front alone: each entry of the
                   second commitment that a form of one of the row's runs names is (the reads' number, row
                   0, a place with an owner among the tables heard) · the plan's number of the reads is the
                   state's · SymsIn
  `hLay_ofJ'` | `hLay_ofJ`   **the field hLay**, at a letter Mg₀ | at mgBase
PREMISES LEFT: hS hR O · hWX · hJy : ∀ s, J s → JLay … s · ON LETTERS: hUL (Dm.uL l is uLay at the plan's parameters and
matsOfData at names l) · hnm (names l is the written list of link l's arrays) · hsub.
IS IT EMPTY HERE? NO MEMBER IS SHOWN.
What is not claimed. JLay at any state. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.ArmAttMats

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open OnBytes.Tie.Pv.Tail.Port (u3Of)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S LayOwn ModelPart Item Pub Meaning Numbers More flatPlacesOf)
open VerifiableInference.Desc.K8.ReadsQuiet (closed layers_ok head_ok)
open VerifiableInference.Desc.First.Att (readsAtSO)
open VerifiableInference.Desc.Sound (GQ MsgQ dataQ matsOfData linksFull MsgT MgData CellsQ mgAll mgBase d13
  rowQ seatTab UFn linkNo ArmCellIn cellsAt cellsAt_name)
open VerifiableInference.Desc.K12.Door (K12Data)
open OnBytes.Model.Stages (LinkH)
open OnBytes.Params (Rounds)
open OnBytes.Road.K4 (uLay InRange)
open Meaning.Reads (cellA cellZ tie_named)
open Meaning.K2 (bindE)
open Iop Run OnBytes.Maker OnBytes.Flat
open Cb Johnson.Pack
open ProofFile (Cl)

/-! ## 1 Over the reads' accept -/

theorem closed_like {tl tl' : HTailF2} {funs : Array HFun} {L : LinkCtx} {st : Statement}
    (h : closed tl funs L st = .ok tl') : TlLike tl tl' := by
  unfold closed at h
  obtain ⟨t, h1, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  cases h
  rw [First.K8.Order.close_lays tl tl' funs h1]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- **Over an accept at a feed-forward link's reads the closed parameters are like the plan's.** -/
theorem layLike_over_reads (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (X : LinkH)
    (hX : G.built[l]? = some X) (pr : ℕ) (reads : Option (List ℕ)) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h2 : rs.length = 2)
    (h : (IM.k1Reads Z G l X pr reads).decide s rs gs = .ok s') (b₀ : LayOwn)
    (hs : s.here = .lay b₀) :
    ∃ hp tl', G.W.G[X.g]? = some hp ∧ s'.tl? = some tl' ∧ TlLike hp.tl tl' := by
  obtain ⟨r₁, r₂, rfl⟩ := List.length_eq_two.1 h2
  obtain ⟨s₁, gs₁, rs₂, gs₂, h1, h3⟩ := joined_yes _ _ _ _ _ (IM.k1Quiet G l X) s s' r₁ r₂ gs h
  obtain ⟨_, F, _, y, _, _, _, e, _⟩ := commitAtS_slots h1
  have hs₁ := here_commit_lay hs y.w y.L y.F
  rw [← e] at hs₁
  revert h3
  unfold IM.k1Quiet
  dsimp only
  cases hq : ProofFile.readsQuietAt G l X (if X.kind == 0 || X.kind == 1 then 4 else 5) with
  | none => exact fun h => nomatch h
  | some q =>
    intro h3
    have hd' : q.decide s₁ rs₂ gs₂ = .ok s' := h3
    rcases readsQuietAt_cases hq with hz | hz
    · unfold First.Att.readsAtO at hz
      obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 hz
      have hd'' : readsAtSO A s₁ = .ok s' := hd'
      obtain ⟨a', t, tl, ha', _⟩ := Meaning.K2.readsAtSO_eq hd''
      rw [hs₁] at ha'
      cases ha'
    · rcases blockAt_cases hX hz with ⟨hp, hg, rfl⟩ | rfl
      · obtain ⟨a', own, tl', ha', ho, hc, rfl⟩ := layers_ok hd'
        exact ⟨hp, tl', hg, rfl, closed_like hc⟩
      · obtain ⟨a', cov, x, t, tl', ha', _⟩ := head_ok hd'
        rw [hs₁] at ha'
        cases ha'

theorem layIsEven : ∀ l < 25, (linksFull[l]?).getD .layers = ModelPart.layers →
    l = 2 * (l / 2) ∧ l / 2 < 12 := by decide

/-- In scope the built link at a feed-forward link l has the group l / 2. -/
theorem group_lay {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)} {c : Chain S Cl}
    {A₀ : ProofFile.SharedSeat} {B₀ : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A₀ B₀)
    (l : ℕ) (hl : l < 25) (hsub : (linksFull[l]?).getD .layers = ModelPart.layers) (X : LinkH)
    (hX : Bs.G₀.built[l]? = some X) : X.g = l / 2 := by
  obtain ⟨e, hg⟩ := layIsEven l hl hsub
  obtain ⟨nam, -⟩ := IM.ground_named hS hR O.pub O.blank
  obtain ⟨l₁, _, h', _, hg', _⟩ := nam (l / 2) hg
  rw [← e, hX] at h'
  obtain rfl := Option.some.inj h'
  exact hg'

/-! ## 2 The field hM -/

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)
  (Mg₀ : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))

/-- **The field hM at the matrices made of the data.** -/
theorem layM_of {J : S → Prop} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {aN : ℕ} {R₁ R₂ R₃ : Rounds}
    {c : Chain S Cl} {l : ℕ} {X : LinkH} {arrs : Option (List ℕ)} {x x' : ProofFile.InstPub × S}
    {y y' : Strs} {w : Wit (CellsQ rows cols) Tok MsgT} {p : ℕ × String} {A B : K9.Part}
    (Fc : ReadsFence Dm dk Mg₀ J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B)
    (hsub : ∀ u ∈ Dm.N.sent l 0, u ∈ Dm.N.group l) {b₀ : LayOwn} {hp : Layer.HPlan2}
    {tl' : HTailF2} (hs : x.2.here = .lay b₀) (hg : Bs.G₀.W.G[X.g]? = some hp)
    (htl : x'.2.tl? = some tl') (hSy : SymsIn (Dm.N.sent l 0) A hp.tl) :
    InRange tl' (matsOfData hp.tl A.L.arrayOf (dataQ (Dm.N.sent l 0) A (seatTab Dm.cs Dm.arr Dm.ms w)))
      (cellA tl' (Dm.A1 l x' w)) := by
  intro μ r cn hμ hr hc
  obtain ⟨_, rs, gs, hfit, hd⟩ := Fc.yes
  have hlen : (rs.map noDigest).length = 2 := by
    rw [List.length_map, Keeps.fit_length _ _ hfit, rounds_blkL]
  obtain ⟨hp₂, tl₂, hg₂, e2, L⟩ :=
    layLike_over_reads Z Bs.G₀ l X Fc.built _ arrs x.2 x'.2 _ gs hlen hd b₀ hs
  obtain rfl : hp₂ = hp := Option.some.inj (hg₂.symm.trans hg)
  obtain rfl : tl₂ = tl' := Option.some.inj (e2.symm.trans htl)
  obtain ⟨tl₃, htl₃, T⟩ : First.K8.TieAt (Dm.A1 l x') x'.2 w := Fc.tie
  obtain rfl : tl₃ = tl₂ := Option.some.inj (htl₃.symm.trans htl)
  obtain ⟨g1, g2, _⟩ := tie_named T
  have hr' := rides_at_reads Fc
  rw [L.NM] at hμ
  rw [L.mats] at hr hc
  show _ = ((cellZ tl₃ (Dm.A1 l x' w) μ r cn : ℤ) : Cb.Gl.E)
  refine matsOfData_of_packs hp₂.tl A.L.arrayOf _ (cellZ tl₃ (Dm.A1 l x' w)) μ r cn hμ hr hc
    (fun i hi => ?_) fun i' hi' => ?_
  · exact g1 μ (by rw [L.NM]; exact hμ) cn (by rw [L.mats]; exact hc) i (by rw [L.mats]; exact hi)
  · obtain ⟨nm, hn, hcell⟩ := cell_back (Dm.N.sent l 0) (Dm.N.group l) hsub A B
      (seatTab Dm.cs Dm.arr Dm.ms w) hr' _ (hSy μ hμ)
    have h0 := g2 μ (by rw [L.NM]; exact hμ) cn (by rw [L.mats]; exact hc) i'
      (by rw [L.mats]; exact hi')
    rw [L.gtTree, L.mats] at h0
    show (match A.L.arrayOf[hp₂.tl.gtTree.getD μ 0]? with
      | some b => (dataQ (Dm.N.sent l 0) A (seatTab Dm.cs Dm.arr Dm.ms w)).cell b.1 b.2 i' cn
      | none => 0) = _
    rw [hn]
    dsimp only
    rw [← hcell, ← h0]
    exact (cellsAt_name Dm.cs Dm.arr Dm.ms Dm.N l x'.1 x'.2 w B Fc.behind _ nm
      (by rw [hr'.arrays]; exact hn) i' cn).symm

/-- **WHAT STAYS OF THE FEED-FORWARD LINKS' HALF, A CLAUSE FOR THE LETTER J**, on the state in front alone. -/
def JLay (s : S) : Prop :=
  ∀ b₀ o hp A, s.here = .lay b₀ → b₀.own = some o → XV.G[linkNo s / 2]? = some hp →
    K9.segAt? s = some A →
    u3Of hp.tl = o.v.iU3 ∧ SymsIn (Dm.N.sent (linkNo s) 0) A hp.tl ∧
      ∀ p e cc, (∃ j n, Item.formsT (linkNo s) j n ∈
          (rowQ linksFull (flatPlacesOf linksFull true) (noL (linkNo s) false)).ins ∧
          p ∈ Dm.runs (linkNo s) j n) →
        NamedEntry (Dm.Rd (linkNo s)) (Dm.N.sent (linkNo s) 0) p.1 p.2 s A e cc →
        e.tree = o.v.iU3 ∧ e.row = 0 ∧
          ∃ z : HFun × ℕ × ℕ, z.1 ∈ o.funs ∧ hp.tl.tabAt z.1 z.2.1 z.2.2 = some e.idx

/-- **THE FIELD hLay OF k01_fifty_paid, IN ITS OWN TYPE**, at a letter Mg₀. -/
theorem hLay_ofJ' (J : S → Prop) (hM : Mg₀.more = {}) {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)} {c : Chain S Cl}
    {A₀ : ProofFile.SharedSeat} {B₀ : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A₀ B₀)
    (hWX : Bs.G₀.W = XV) (hJy : ∀ s, J s → JLay Dm s) (aN : ℕ) (R₁ R₂ R₃ : Rounds)
    (names : ℕ → Array (ℕ × String))
    (hUL : ∀ l X hp, (linksFull[l]?).getD .layers = .layers → Bs.G₀.built[l]? = some X →
      Bs.G₀.W.G[X.g]? = some hp →
      Dm.uL l = uLay hp.tl fun _ D => matsOfData hp.tl (names l) D)
    (hnm : ∀ l, l < 25 → names l = Dm.pubD.d3.arrayOf.getD l #[])
    (hsub : ∀ l, l < 25 → ∀ u ∈ Dm.N.sent l 0, u ∈ Dm.N.group l) :
    ∀ l X arrs x x' y y' w p A B, ReadsFence Dm dk Mg₀ J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .layers →
      ∀ b₀ o hp tl', x.2.here = .lay b₀ → b₀.own = some o → Bs.G₀.W.G[X.g]? = some hp →
      x'.2.tl? = some tl' →
      ∀ e cc, NamedEntry (Dm.Rd l) (Dm.N.sent l 0) p.1 p.2 x.2 A e cc →
      ∃ M n, Dm.uL l x.2 = uLay hp.tl M x.2 ∧
        LayRest (oneEntry e) (Dm.N.sent l 0) p.1 p.2 x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) hp.tl tl' M o n
          (Dm.A1 l x' w) := by
  intro l X arrs x x' y y' w p A B Fc hsb b₀ o hp tl' hs ho hg htl e cc hN
  have hno : linkNo x.2 = l :=
    linkNo_of_promise Dm dk Mg₀ hM l Fc.lt x y (inAt_down _ _ _ _ _ _ _ _ _ Fc.inAt) A Fc.front
  have hg' : XV.G[linkNo x.2 / 2]? = some hp := by
    rw [hno, ← hWX, ← group_lay hS hR O l Fc.lt hsb X Fc.built]
    exact hg
  obtain ⟨h3, hSy, hE⟩ := hJy _ Fc.inv b₀ o hp A hs ho hg' Fc.front
  rw [hno] at hSy hE
  obtain ⟨e1, e2, z, z1, z2⟩ := hE p e cc Fc.run hN
  have harr := arrays_at_reads Dm dk Mg₀ hM l Fc.lt x y Fc.inAt A Fc.front
  refine ⟨fun _ D => matsOfData hp.tl (names l) D, e.idx + 1, by rw [hUL l X hp hsb Fc.built hg],
    oneEntry_all (P := fun u => u.tree = o.v.iU3 ∧ u.row = 0 ∧ u.idx < e.idx + 1 ∧
      ∃ z : HFun × ℕ × ℕ, z.1 ∈ o.funs ∧ hp.tl.tabAt z.1 z.2.1 z.2.2 = some u.idx)
      ⟨e1, e2, Nat.lt_succ_self _, z, z1, z2⟩ p.1 p.2 x.2, h3, ?_⟩
  show InRange tl' (matsOfData hp.tl (names l) _) _
  rw [hnm l Fc.lt, ← harr]
  exact layM_of Dm dk Mg₀ Fc (hsub l Fc.lt) hs hg htl hSy

/-- **THE FIELD hLay OF k01_fifty_paid, IN ITS OWN TYPE.** -/
theorem hLay_ofJ (J : S → Prop) {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)} {c : Chain S Cl}
    {A₀ : ProofFile.SharedSeat} {B₀ : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A₀ B₀)
    (hWX : Bs.G₀.W = XV) (hJy : ∀ s, J s → JLay Dm s) (aN : ℕ) (R₁ R₂ R₃ : Rounds)
    (names : ℕ → Array (ℕ × String))
    (hUL : ∀ l X hp, (linksFull[l]?).getD .layers = .layers → Bs.G₀.built[l]? = some X →
      Bs.G₀.W.G[X.g]? = some hp →
      Dm.uL l = uLay hp.tl fun _ D => matsOfData hp.tl (names l) D)
    (hnm : ∀ l, l < 25 → names l = Dm.pubD.d3.arrayOf.getD l #[])
    (hsub : ∀ l, l < 25 → ∀ u ∈ Dm.N.sent l 0, u ∈ Dm.N.group l) :
    ∀ l X arrs x x' y y' w p A B, ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .layers →
      ∀ b₀ o hp tl', x.2.here = .lay b₀ → b₀.own = some o → Bs.G₀.W.G[X.g]? = some hp →
      x'.2.tl? = some tl' →
      ∀ e cc, NamedEntry (Dm.Rd l) (Dm.N.sent l 0) p.1 p.2 x.2 A e cc →
      ∃ M n, Dm.uL l x.2 = uLay hp.tl M x.2 ∧
        LayRest (oneEntry e) (Dm.N.sent l 0) p.1 p.2 x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) hp.tl tl' M o n
          (Dm.A1 l x' w) :=
  hLay_ofJ' Dm dk mgBase J rfl hS hR O hWX hJy aN R₁ R₂ R₃ names hUL hnm hsub

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.closed_like
#print axioms VerifiableInference.Desc.K1.layLike_over_reads
#print axioms VerifiableInference.Desc.K1.group_lay
#print axioms VerifiableInference.Desc.K1.layM_of
#print axioms VerifiableInference.Desc.K1.hLay_ofJ'
#print axioms VerifiableInference.Desc.K1.hLay_ofJ
