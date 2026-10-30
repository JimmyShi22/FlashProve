-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6WorthAtMgAll.lean (K6In is taken UNDER THE GUARD "the
witness's cells hold an index", which that meaning's items hand over; the agreement of the weights
is a theorem: Law/HeadWeightsMeet.lean): TWO OF THE THREE ITEMS "worth 24 3" THAT THE
SUB-PROTOCOL AT THE OUTPUT HEAD CLOSES, AT THE COMPOSED FILLING OF ALL PARTS
(Johnson/Desc/Sound/MgAll.lean),
FROM WHAT THE HEAD'S LAW CONCLUDES IN FRONT OF ITS SUB-PROTOCOL (K6In at compCut w):
"rider" and
"keys".

A joining of other files' laws. That filling says these two items in the lookup's library's words,
at the caller of the proved lookup sub-protocol at the head's calls
(Johnson/Desc/Sound/MgAllAt.lean:
mgAll_worth_head_rider, mgAll_worth_head_keys). Two other files have the two roads from
K6In's clauses to these words (Law/RiderNoWeights.lean: rider_arm_but, which reads no weight;
Law/KeysRoad.lean: keys_arm), each at
ANY cells that agree with the law's inside the ranges, and any reading of the places that agrees
with the law's mask row. Law/HeadCellsAtCaller.lean has these two agreements at the caller's own
cells and reading.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable).
  CallerFits (Wp := Wp) x: TWO EQUATIONS ON THE PUBLIC PARAMETERS: the head's segment's number is
      24; the
      place of the lookup on the head's calls is x. (The kind's sizes and policy and the map of
      addresses are made off the public parameters in that filling: they are the
      head's own by rfl.)
  rider_mgAll, keys_mgAll: the two items.
  CallerMeets D lay6 num n x: WHAT TIES THE CALLER'S READING OF THE WITNESS TO THE LAW'S: five
      fields, all on public data (the agreement of the weights is a theorem since that filling
      fixes the committed table's message and its reader: Law/HeadWeightsMeet.lean).
  sameCells_mg, mask_mg: under it (and the geometry, which Law/HeadRangesOfNumbers.lean has in the
      goals' scope, and the test laidThere with PlanK6's clause named) the two
      agreements that the two items ask, at the filling's own letters.

Every letter under "there is": none.
What it does not say. THE PREMISES, EACH NAMED IN THE STATEMENTS: the request that the filling hands
the kind off the public part is the one that the seat reads off the verifier's state (hrq) · the two
readers of the heard token are one (hy, hr) · PlanFacts, Request.ok, the token below V (the head's
own condition in front has them) · the two agreements (hL1, hmask) · on what the lookup heard: the
size of its point, its shape · on the plan: lt ≤ dT, FoNums.ok, six calls. FOR "keys" ALONE ("rider"
reads no weight): the law's weights (whOf: 0 where the cells hold no index) and the caller's (the
lift of two bytes of the committed table's message) agree only at a witness whose cells hold an
index (InRange): in that filling the three items stand UNDER THAT GUARD ON THE
WITNESS: so the agreement is asked under it alone. The third item, "planes":
untouched. Nothing on soundness.
-/
import Johnson.Desc.Sound.MgAllAt
import Johnson.Desc.Kinds.Law.K6AtMgAll
import Johnson.Desc.Kinds.Law.RiderNoWeights
import Johnson.Desc.Kinds.Law.KeysRoad
import Johnson.Desc.Kinds.Law.HeadCellsAtCaller
import Johnson.Desc.Kinds.Law.HeadWeightsMeet

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open OnBytes.Model.Verify (borderOf)
open VerifiableInference.OnPublicFiles (headLink layMs layMu headNu k3AdrAt k3SizesAt k3PolicyAt)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (S Meaning)
open VerifiableInference.Desc.Sound (MsgT MgData mgAll)

variable {Xi P Tok : Type} {rows cols nR : ℕ} {Wp : OnBytes.Model.Verify.Public}
  (D : MgData Xi P Tok rows cols nR Wp)
  (Mg : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT))

/-- **The filling's letters for the head's calls are the head's.** -/
structure CallerFits (x : First.Look.Place) : Prop where
  seg : headLink Wp = 24
  place : headAt Wp = some x

variable {D}

/-- **The item "worth 24 3 rider".** -/
theorem rider_mgAll {x : First.Look.Place} (C : CallerFits (Wp := Wp) x) (a : P × S) (y : Strs)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (d : Pinned) 
    (hin : VerifiableInference.OnPublicFiles.Flat.InRange w.cells → K6In Wp a.2 d) (y0 : ℕ)
    (hy : Reply.token (seatAt Wp.hS (readsOf Wp)).toSeat a.2 = some y0)
    (hr : a.2.replyTok? = some y0)
    (hrq : D.rq a.1 = (seatAt Wp.hS (readsOf Wp)).request a.2) :
    letI := (parOf Wp.hS (workOf Wp)).sizes
    letI := (parOf Wp.hS (workOf Wp)).policy
    letI : Request := (seatAt Wp.hS (readsOf Wp)).request a.2
    PlanFacts →
      SameBut d.1 (headCells (k3AdrAt Wp) x Wp.H.tl D.sent D.l3.rad D.l3.oW D.l3.wOf D.l3.nr D.l3.nc
        (layMs x D.sent D.l3.rad D.l3.oW (fun j => D.l3.seat x.link false j.1) D.l3.arr
          D.l3.msgW w)) →
      (∀ g, a.2.lookHeard? = some g → g.zx.size = x.fs.dT) → Norm.lt ≤ x.fs.dT →
      (mgAll D Mg).worth 24 3 "rider" a y w := by
  intro hP hL1 hz hlt
  rw [← C.seg, Sound.mgAll_worth_head_rider D Mg C.place a y w]
  intro hR
  have key : ∀ (Sz : Sizes) (Po : Policy) (Rq : Request),
      Sz = (parOf Wp.hS (workOf Wp)).sizes → Po = (parOf Wp.hS (workOf Wp)).policy →
      Rq = (seatAt Wp.hS (readsOf Wp)).request a.2 →
      ∀ g F', a.2.fork? = some F' → a.2.lookHeard? = some g →
        VerifiableInference.OnPublicFiles.K3OutRider
          (@headRider Sz Po Rq (k3AdrAt Wp) x Wp.H.tl D.sent D.l3.rad D.l3.oW D.l3.wOf D.l3.nr
              D.l3.nc
            Iop.extNone Unit) x.lm x.F.next (a.2.replyTok?.getD 0)
          (layMs x D.sent D.l3.rad D.l3.oW (fun j => D.l3.seat x.link false j.1) D.l3.arr
            D.l3.msgW w) g F' := by
    intro Sz Po Rq e1 e2 e3 g F' _ hg
    subst e1 e2 e3
    exact rider_arm_but (k3AdrAt Wp) x Wp.H.tl D.sent D.l3.rad D.l3.oW D.l3.wOf D.l3.nr D.l3.nc _
        Unit Wp.hS
      (readsOf Wp) (parOf Wp.hS (workOf Wp)) a.2 d.1 (hin hR).2.1 y0 hy hr _ hP hL1 hz hlt g F' hg
  exact key (k3SizesAt Wp) (k3PolicyAt Wp) (D.rq a.1) rfl rfl hrq

/-- **The item "worth 24 3 keys".** -/
theorem keys_mgAll {x : First.Look.Place} (C : CallerFits (Wp := Wp) x) (a : P × S) (y : Strs)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (d : Pinned) 
    (hin : VerifiableInference.OnPublicFiles.Flat.InRange w.cells → K6In Wp a.2 d) (y0 : ℕ)
    (hy : Reply.token (seatAt Wp.hS (readsOf Wp)).toSeat a.2 = some y0)
    (hr : a.2.replyTok? = some y0)
    (hrq : D.rq a.1 = (seatAt Wp.hS (readsOf Wp)).request a.2) :
    letI := (parOf Wp.hS (workOf Wp)).sizes
    letI := (parOf Wp.hS (workOf Wp)).policy
    letI : Request := (seatAt Wp.hS (readsOf Wp)).request a.2
    PlanFacts → Request.ok = true → y0 < V →
      (VerifiableInference.OnPublicFiles.Flat.InRange w.cells →
        SameCells d.1 (headCells (k3AdrAt Wp) x Wp.H.tl D.sent D.l3.rad D.l3.oW D.l3.wOf D.l3.nr
          D.l3.nc (layMs x D.sent D.l3.rad D.l3.oW (fun j => D.l3.seat x.link false j.1) D.l3.arr
            D.l3.msgW w))) →
      (∀ j, rd (d.2 j) = headNu (k3AdrAt Wp) x Wp.H.tl D.sent D.l3.rad D.l3.oW D.l3.wOf D.l3.nr
          D.l3.nc
        (fun j => D.l3.seat x.link false j.1) D.l3.arr D.l3.msgW w (.mask j)) →
      (∀ g, a.2.lookHeard? = some g → g.shape = x.fs) → FoNums.ok x.fs = true → x.fs.NC = 6 →
      (mgAll D Mg).worth 24 3 "keys" a y w := by
  intro hP hok hV hL1 hmask hsh hfo hnc
  rw [← C.seg, Sound.mgAll_worth_head_keys D Mg C.place a y w]
  intro hR
  have key : ∀ (Sz : Sizes) (Po : Policy) (Rq : Request),
      Sz = (parOf Wp.hS (workOf Wp)).sizes → Po = (parOf Wp.hS (workOf Wp)).policy →
      Rq = (seatAt Wp.hS (readsOf Wp)).request a.2 →
      ∀ g F', a.2.fork? = some F' → a.2.lookHeard? = some g →
        VerifiableInference.OnPublicFiles.K3OutKeys x.fs x.lm x.F.next
          (headNu (k3AdrAt Wp) x Wp.H.tl D.sent D.l3.rad D.l3.oW D.l3.wOf D.l3.nr D.l3.nc
            (fun j => D.l3.seat x.link false j.1) D.l3.arr D.l3.msgW w)
          (Cb.Fo.forK Cb.Gl.E
            (@headLay Sz Rq (k3AdrAt Wp) x.fs x.lm x.F.next x.ns Wp.H.tl D.l3.nr D.l3.nc)
            (a.2.replyTok?.getD 0)
            (Cb.Fo.zext (layMu x Wp.H.tl D.sent D.l3.rad D.l3.oW D.l3.wOf D.l3.nr D.l3.nc
              (fun j => D.l3.seat x.link false j.1) D.l3.arr D.l3.msgW w)))
                  OnBytes.Model.Reading.gl g F' := by
    intro Sz Po Rq e1 e2 e3 g F' hF hg
    subst e1 e2 e3
    exact keys_arm Wp.hS (readsOf Wp) (parOf Wp.hS (workOf Wp)) a.2 d.1 d.2 (hin hR).2.2 y0 hy hr
      (headCells (k3AdrAt Wp) x Wp.H.tl D.sent D.l3.rad D.l3.oW D.l3.wOf D.l3.nr D.l3.nc
        (layMs x D.sent D.l3.rad D.l3.oW (fun j => D.l3.seat x.link false j.1) D.l3.arr
          D.l3.msgW w))
      (headNu (k3AdrAt Wp) x Wp.H.tl D.sent D.l3.rad D.l3.oW D.l3.wOf D.l3.nr D.l3.nc
        (fun j => D.l3.seat x.link false j.1) D.l3.arr D.l3.msgW w)
      x.fs x.lm x.F.next hP hok hV (hL1 hR) hmask hsh hfo hnc g F' hF hg
  exact key (k3SizesAt Wp) (k3PolicyAt Wp) (D.rq a.1) rfl rfl hrq

variable (D)

/-- **WHAT TIES THE CALLER'S READING OF THE WITNESS TO THE LAW'S: ALL ON PUBLIC DATA BUT ONE FIELD**
(weights: on the filling's reader of the committed table's message, AT A WITNESS WHOSE CELLS HOLD AN
INDEX: at other cells the law's weights are 0 by the make of whOf, while the caller's are the lift
of
two bytes: there the two part). -/
structure CallerMeets (lay6 : OnBytes.Params.ReqLayout) (num : ℕ → ℕ → ℕ) (n : ℕ)
    (x : First.Look.Place) : Prop where
  fits : CallerFits (Wp := Wp) x
  lay : D.layout = lay6
  calls : CallsSeated (ColFour Wp.hS Wp.HLy (borderOf Wp.y)) D.arr D.ms D.N Wp lay6 num D.sent
      D.l3.rad x.link
    fun j => D.l3.seat x.link false j.1
  ns : x.ns = Wp.H.ns
  mask : ∃ (m0 : ℕ) (hk : (First.Look.keptAt D.sent x.link).length + m0 <
      (First.Look.sigListCalls D.sent D.l3.rad x.link).length) (xt : ℕ × ℕ) (y : Sound.Mem),
    ((First.Look.messagesAt D.sent x.link).findIdx? fun z => z.shape.maskRows != 0) = some m0 ∧
    0 < ((First.Look.sigListCalls D.sent D.l3.rad x.link).get
      ⟨(First.Look.keptAt D.sent x.link).length + m0, hk⟩).1.maskRows ∧
    (∀ j, j < Wp.H.ns → j < (pMask D.sent.codes ((First.Look.sigListCalls D.sent D.l3.rad
      x.link).get ⟨(First.Look.keptAt D.sent x.link).length + m0, hk⟩).1).ell) ∧
    D.l3.seat x.link false ((First.Look.keptAt D.sent x.link).length + m0) = xt ∧
    ((First.Look.sigListCalls D.sent D.l3.rad x.link).get
      ⟨(First.Look.keptAt D.sent x.link).length + m0, hk⟩).1 = (y.1.l.get y.2).1 ∧
    Sound.namedOnce D.arr D.N 24 n = true ∧ xt ∈ D.N.group 24 ∧ D.arr xt.1 xt.2 = n ∧
    (D.ms.find? fun y => Decidable.decide (Sound.seatOf y = xt)) = some y

variable {D}

/-- **The law's cells are the caller's, inside the ranges, at the filling's own letters.** -/
theorem sameCells_mg {lay6 : OnBytes.Params.ReqLayout} {num : ℕ → ℕ → ℕ} {n : ℕ}
    {x : First.Look.Place} (M : CallerMeets D lay6 num n x)
    (hG : @InRanges (parOf Wp.hS (workOf Wp)).sizes Wp.hS Wp.HLy (borderOf Wp.y))
    (hsz : ∀ a r c, InFour Wp.hS Wp.HLy (borderOf Wp.y) a r c →
      a < (Meaning.sizesOf Wp 24).NM ∧ c < (Meaning.sizesOf Wp 24).k a ∧
        r < (Meaning.sizesOf Wp 24).m a)
    (T : Meaning.laidThere Wp (Meaning.sizesOf Wp) lay6 = true)
    (p1 : ∀ (μ : Fin (Meaning.sizesOf Wp 24).NM) (r c : Nat),
      r < Alg.symRows ((Meaning.sizesOf Wp 24).m μ) → c < (Meaning.sizesOf Wp 24).k μ →
      ColFour Wp.hS Wp.HLy (borderOf Wp.y) μ.val c →
      Sound.namedOnce D.arr D.N 24 (seatLay Wp lay6 num 24 μ r c).1 = true)
    (pl : ℕ → ℕ × Bool × ℕ × ℕ) (w : Wit (Fin rows → Fin cols → GE) Tok MsgT)
    (hR : VerifiableInference.OnPublicFiles.Flat.InRange w.cells)
    (hd : Wp.hS.d = 5120) (hV : Wp.hS.V = 202048) :
    @SameCells (parOf Wp.hS (workOf Wp)).sizes
      (compCut D.cs D.arr D.ms D.N (Meaning.sizesOf Wp) (seatLay Wp lay6 num) Wp pl w).1
      (headCells (k3AdrAt Wp) x Wp.H.tl D.sent D.l3.rad D.l3.oW D.l3.wOf D.l3.nr D.l3.nc
        (layMs x D.sent D.l3.rad D.l3.oW (fun j => D.l3.seat x.link false j.1) D.l3.arr
          D.l3.msgW w)) := by
  letI := (parOf Wp.hS (workOf Wp)).sizes
  letI := (parOf Wp.hS (workOf Wp)).policy
  letI : Request := ⟨fun _ => 0, 0, 0⟩
  exact Came.SameCells.symm' (Came.sameCells_caller D.cs D.arr D.ms D.N Wp lay6 num pl x D.sent
    D.l3.rad D.l3.oW D.l3.wOf D.l3.nr D.l3.nc (fun j => D.l3.seat x.link false j.1) D.l3.msgW w
    hG hsz T M.lay rfl p1 M.calls
    (Came.smallH_own D.cs D.arr D.ms D.N _ _ Wp w (by rw [Came.beta_landed]; norm_num)
      (by rw [Came.beta_landed]; norm_num))
    fun k v hk hv => Came.weights_stored x Wp.H.tl D.sent D.l3.rad D.l3.arr
      (fun j => D.l3.seat x.link false j.1) (k3AdrAt Wp) w hR k v (hd ▸ hk) (hV ▸ hv))

/-- **The same without the weights: AT EVERY WITNESS.** -/
theorem sameBut_mg {lay6 : OnBytes.Params.ReqLayout} {num : ℕ → ℕ → ℕ} {n : ℕ}
    {x : First.Look.Place} (M : CallerMeets D lay6 num n x)
    (hG : @InRanges (parOf Wp.hS (workOf Wp)).sizes Wp.hS Wp.HLy (borderOf Wp.y))
    (hsz : ∀ a r c, InFour Wp.hS Wp.HLy (borderOf Wp.y) a r c →
      a < (Meaning.sizesOf Wp 24).NM ∧ c < (Meaning.sizesOf Wp 24).k a ∧
        r < (Meaning.sizesOf Wp 24).m a)
    (T : Meaning.laidThere Wp (Meaning.sizesOf Wp) lay6 = true)
    (p1 : ∀ (μ : Fin (Meaning.sizesOf Wp 24).NM) (r c : Nat),
      r < Alg.symRows ((Meaning.sizesOf Wp 24).m μ) → c < (Meaning.sizesOf Wp 24).k μ →
      ColFour Wp.hS Wp.HLy (borderOf Wp.y) μ.val c →
      Sound.namedOnce D.arr D.N 24 (seatLay Wp lay6 num 24 μ r c).1 = true)
    (pl : ℕ → ℕ × Bool × ℕ × ℕ) (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) :
    @SameBut (parOf Wp.hS (workOf Wp)).sizes
      (compCut D.cs D.arr D.ms D.N (Meaning.sizesOf Wp) (seatLay Wp lay6 num) Wp pl w).1
      (headCells (k3AdrAt Wp) x Wp.H.tl D.sent D.l3.rad D.l3.oW D.l3.wOf D.l3.nr D.l3.nc
        (layMs x D.sent D.l3.rad D.l3.oW (fun j => D.l3.seat x.link false j.1) D.l3.arr
          D.l3.msgW w)) := by
  letI := (parOf Wp.hS (workOf Wp)).sizes
  obtain ⟨h1, h2⟩ := Came.fourMeet_caller D.cs D.arr D.ms D.N Wp lay6 num pl x D.sent D.l3.rad
    D.l3.oW D.l3.wOf D.l3.nr D.l3.nc (fun j => D.l3.seat x.link false j.1) D.l3.msgW w hG
    hsz T M.lay rfl p1 M.calls
  exact ⟨fun f t hf ht => (h1 .wide f t (Or.inl ⟨rfl, hf⟩) ht).symm,
    fun f t hf ht => (h1 .act f t (Or.inr (Or.inl ⟨rfl, hf⟩)) ht).symm,
    fun f t hf ht => (h1 .row f t (Or.inr (Or.inr ⟨rfl, hf⟩)) ht).symm,
    fun f t hf ht => (h2 f t hf ht).symm⟩

/-- **The law's mask row is the caller's reading of the places "mask".** -/
theorem mask_mg {lay6 : OnBytes.Params.ReqLayout} {num : ℕ → ℕ → ℕ} {n : ℕ}
    {x : First.Look.Place} (M : CallerMeets D lay6 num n x)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (j : ℕ) :
    rd ((compCut D.cs D.arr D.ms D.N (Meaning.sizesOf Wp) (seatLay Wp lay6 num) Wp (plAt n 0)
        w).2 j) =
      headNu (k3AdrAt Wp) x Wp.H.tl D.sent D.l3.rad D.l3.oW D.l3.wOf D.l3.nr D.l3.nc
        (fun j => D.l3.seat x.link false j.1) D.l3.arr D.l3.msgW w (.mask j) := by
  obtain ⟨m0, hk, xt, y, h1, h5, h6, hs, hsh, g1, hg, hn, hy⟩ := M.mask
  exact Came.mask_meets D.cs D.arr D.ms D.N _ _ Wp n (k3AdrAt Wp) x Wp.H.tl D.sent D.l3.rad D.l3.oW
    D.l3.wOf D.l3.nr D.l3.nc (fun j => D.l3.seat x.link false j.1) D.l3.msgW w m0 xt y M.ns rfl hk
    h1 h5 h6 hs hsh g1 hg hn hy j

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.rider_mgAll
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.keys_mgAll
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.sameCells_mg
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.mask_mg
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.sameBut_mg
