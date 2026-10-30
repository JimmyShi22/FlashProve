-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/KeysRoadBack.lean: THE KEYS' ROAD, BACK: FROM THE SENTENCE THAT THE TABLE OF
JOINTS' FILLING HOLDS AT worth 24 3 "keys" AT THE HEAD (K3OutKeys: the library's claim on the join
is 0 at every list of rounds for which what the lookup heard stands) TO WHAT THE OUTPUT HEAD's LAW
WANTS IN FRONT OF ITS OWN SUB-PROTOCOL ON THE CALLS' KEY VECTORS (KeysWorth, KeysTrueInFront).
CONDITIONAL. Statements and proofs; the first three are each the converse of a theorem of the
library and go by that theorem's own steps; the others join them to "left 24".

WHAT IT IS NOT. Implications. THE PREMISES, EACH NAMED IN THE STATEMENTS: the item itself (its payer
is the lookup's side) · InRange w.cells, the item's own guard · "left 24" at the state (the library
has it from the table's promise in front of the head's place at the full chain, at a state without a
mark of failure: left_front, Law/K6FrontSays.lean) · THAT given RETURNS AT THE STATE IN FRONT (hg):
KeysWorth begins with it: on the way from KeysWorth to the item it is in hand; no lemma of the
library that makes it of a state's facts was found by a search for its two forms ("there is g with
given ... = .ok g"; isOk or toOption of given) · the two agreements (SameCells; the mask row, read,
is the reading at the masks): TWO READINGS OF ONE WITNESS: the library has them under CallerMeets at
the reference sizes, the second at plAt n 0 (sameCells_mg, mask_mg, Law/K6WorthAtMgAll.lean: not
called here) · hy, hr, hrq, PlanFacts, Request.ok, the token below V, the shape's clauses: as on the
road out. That what the lookup heard has the place's shape is a premise of keys_back_mgAll and is
paid off "left 24" in keys_back_left (the library has it from the public test lookOut 24 3 too:
heard_of_onOut, heard_mgAll, Law/K6HeardOfLookOut.lean). Nothing on soundness or on any other
property. Under "there is": KeysWorth's own two (pinned by their equations); in stands_of_left the
ledger (pinned by the state's reader) and, inside K3Stands, a list of rounds, which nothing pins:
any list for which what was heard stands will do.

  worth_of_outKeys   the converse of outKeys_of_worth
  keys_arm_back     the converse of keys_arm
  keys_back_mgAll   **the converse of keys_mgAll: the item, its guard on the witness, one list of
                    rounds, a ledger, and keys_mgAll's own premises: KeysTrueInFront**
  stands_of_left    what "left 24" says, at the caller's place: a ledger, the caller's shape in what
                    was heard, and the list of rounds at the item's letters
  keys_back_left    **the same with the list, the ledger, the heard shape and the place's letters
                    taken from "left 24"**

Why. Law/KeysRoad.lean and Law/K6WorthAtMgAll.lean lead from KeysWorth to the item. Whoever is
handed the item and wants the form of "join" opened behind the head's sub-protocol
(Law/JoinFromFront.lean) needs the other direction. The item is a sentence on ALL lists of rounds
for which what was heard stands: to spend it one such list is wanted. The public item "left 24",
which is asked at the head's own place, names one, at the very ledger.
Nothing on any property.

-/
import Johnson.Desc.Kinds.Law.K6WorthAtMgAll
import Johnson.Desc.Kinds.Law.JoinFromFront
import Johnson.Desc.First.Look.K3LeftItem
import Johnson.Desc.First.Look.K3HeadStated
import Johnson.Desc.First.Look.K3AsksHeadLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE)
open OnBytes.Model (Fork Reading Aff World)
open VerifiableInference.OnPublicFiles

/-- **THE KEYS' ROAD, BACK**: the converse of outKeys_of_worth (Law/KeysRoad.lean), where what the
lookup heard stands for SOME rounds (hSt) and given and the lookup's points answer at the state (hg,
hz). By that theorem's own steps, each of which is an equation, read at the one list of rounds.
-/
theorem worth_of_outKeys (p : Par) (L : Seat VerifiableInference.Desc.First.S)
    (s : VerifiableInference.Desc.First.S) (c : NCells) (mask : Nat → E)
    (gk : OnBytes.Model.Forest.Heard) (g : Given) (z : Point × (Nat → Point))
    (hg : given p L s = .ok g) (hz : L.lookup s = some z) (lm first : ℕ)
    (nu : _root_.Fo.Pl → K) (Kv : ℕ → ℕ → K) (hok : FoNums.ok gk.shape = true)
    (h6 : gk.shape.NC = 6) (hmask : ∀ j, rd (mask j) = nu (.mask j))
    (hkeys : ∀ (g : Given) (z : Point × (Nat → Point)), given p L s = .ok g →
      L.lookup s = some z → ∀ call, call < 6 → rd (trueKey c z.2 call) =
        _root_.Fo.extL (Kv call) (_root_.Fo.rdA Reading.gl (gk.zk.getD call #[])))
    (hSt : K3Stands gk.shape lm first Reading.gl gk (L.ledger s))
    (hO : K3OutKeys gk.shape lm first nu Kv Reading.gl gk (L.ledger s)) :
    KeysWorth p L s c mask gk := by
  obtain ⟨rs, hI⟩ := hSt
  have hO' : _root_.Fo.claimJoin gk.shape lm first rs nu
      (VerifiableInference.OnPublicFiles.keysAt gk.shape lm first Kv rs) = 0 := hO rs hI
  refine ⟨g, z, hg, hz, ?_⟩
  have hsz : (trueKeys g z.2 c).size = gk.shape.NC := by
    rw [h6]
    simp [trueKeys]
  rw [worldE_is _ mask nu hmask, joinForm_is]
  have hJ := joinForm_worth Reading.gl gk (trueKeys g z.2 c) hok hsz lm first rs (L.ledger s)
    (L.ledger s) hI (_root_.Fo.Later.refl _) nu fun _ _ _ => 0
  have hc : _root_.Fo.claimJoin gk.shape lm first rs nu
      (VerifiableInference.OnPublicFiles.keysAt gk.shape lm first Kv rs) =
      _root_.Fo.claimJoin gk.shape lm first rs nu fun k =>
        ((trueKeys g z.2 c).getD k (Aff.ofConst zeroE)).value Reading.gl
          ((L.ledger s).worldOf Reading.gl (fun j => nu (.mask j)) fun _ _ _ => 0) := by
    refine claimJoin_congr gk.shape lm first rs nu _ _ fun call hc => ?_
    rw [h6] at hc
    rw [Came.trueKeys_getD g z.2 c call hc]
    show _root_.Fo.extL (Kv call) ((_root_.Fo.endsOf gk.shape lm first rs).zk.getD call []) =
      (Aff.ofConst (trueKey c z.2 call)).value Reading.gl _
    rw [Aff.value_ofConst, ← hI.zk]
    have e := hkeys g z hg hz call hc
    have e2 : (gk.zk.toList.map (_root_.Fo.rdA Reading.gl)).getD call [] =
        _root_.Fo.rdA Reading.gl (gk.zk.getD call #[]) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList,
        Array.getD_eq_getD_getElem?]
      cases gk.zk[call]? <;> rfl
    rw [e2]
    exact e.symm
  exact hJ.trans (hc.symm.trans hO')

/-- **THE SAME IN THE SHAPE OF THE FILLING's ARM "keys"**: the converse of keys_arm
(Law/KeysRoad.lean), in its letters. -/
theorem keys_arm_back (h : OnBytes.Model.Head.Shape) (iU3 : ℕ) (p : Par)
    (s : VerifiableInference.Desc.First.S) (c : NCells) (mask : Nat → E) (g0 : Given)
    (hg : given p (seatAt h iU3) s = .ok g0) (y0 : ℕ)
    (hy : Reply.token (seatAt h iU3).toSeat s = some y0) (hr : s.replyTok? = some y0)
    (c' : NCells) (nu : _root_.Fo.Pl → K) (fs : OnBytes.Model.Forest.Shape) (lm first : ℕ) :
    letI := p.sizes
    letI := p.policy
    letI : Request := (seatAt h iU3).request s
    PlanFacts → Request.ok = true → y0 < V → SameCells c c' →
      (∀ j, rd (mask j) = nu (.mask j)) →
      (∀ g, s.lookHeard? = some g → g.shape = fs) → FoNums.ok fs = true → fs.NC = 6 →
      ∀ (g : OnBytes.Model.Forest.Heard) (F' : Fork), s.fork? = some F' → s.lookHeard? = some g →
        K3Stands fs lm first Reading.gl g F' →
        K3OutKeys fs lm first nu
          (fun call i =>
            letI : Token := ⟨s.replyTok?.getD 0⟩
            rd (keyTable c' call (i / Norm.T) (i % Norm.T))) Reading.gl g F' →
        KeysWorth p (seatAt h iU3) s c mask g := by
  letI := p.sizes
  letI := p.policy
  letI : Request := (seatAt h iU3).request s
  intro hP hreq hyV hL1 hmask hsh hok h6 g F' hF hk hSt hO
  obtain rfl := hsh g hk
  have hled : (seatAt h iU3).ledger s = F' := by
    show s.fork?.getD {} = F'
    rw [hF]
    rfl
  have hz2 : (seatAt h iU3).lookup s = some (g.zx, fun c => g.zk.getD c #[]) := by
    show (s.lookHeard?.map fun g => (g.zx, fun c => g.zk.getD c #[])) = _
    rw [hk]
    rfl
  rw [hr] at hO
  rw [← hled] at hSt hO
  refine worth_of_outKeys p (seatAt h iU3) s c mask g g0 _ hg hz2 lm first nu _ hok h6 hmask ?_ hSt
    hO
  intro g' z hg' hz call _
  obtain ⟨z', y, hz', hy', _, rfl⟩ := Came.given_ok p _ s g' hg'
  obtain rfl : y = y0 := Option.some.inj (hy'.symm.trans hy)
  obtain rfl : z = (g.zx, fun c => g.zk.getD c #[]) := Option.some.inj (hz.symm.trans hz2)
  letI : Token := ⟨y⟩
  exact trueKey_ext c c' hL1 hP hreq hyV (fun c => g.zk.getD c #[]) call

#print axioms worth_of_outKeys
#print axioms keys_arm_back

end VerifiableInference.Desc.Kinds.Head.Law

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open OnBytes.Model.Verify (borderOf)
open VerifiableInference.OnPublicFiles (headLink layMs layMu headNu k3AdrAt k3SizesAt k3PolicyAt)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (S Meaning)
open VerifiableInference.Desc.Sound (MsgT MgData mgAll)

variable {Xi P Tok : Type} {rows cols nR : ℕ} {Wp : OnBytes.Model.Verify.Public}
  {D : MgData Xi P Tok rows cols nR Wp}
  (Mg : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT))

/-- **FROM THE ITEM "worth 24 3 keys" TO THE KEYS' SENTENCE IN FRONT OF THE HEAD's OWN
SUB-PROTOCOL**: the converse of keys_mgAll (Law/K6WorthAtMgAll.lean), in its letters. hR: the item's
own guard. hSt: what the lookup heard stands for some rounds, at the item's letters. hF: the state
has a ledger: without one the item and hSt say nothing. -/
theorem keys_back_mgAll {x : First.Look.Place} (C : CallerFits (Wp := Wp) x) (a : P × S) (y : Strs)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (d : Pinned)
    (hitem : (mgAll D Mg).worth 24 3 "keys" a y w)
    (hR : VerifiableInference.OnPublicFiles.Flat.InRange w.cells) (g0 : Given)
    (hg : given (parOf Wp.hS (workOf Wp)) (seatAt Wp.hS (readsOf Wp)) a.2 = .ok g0)
    (hSt : ∀ g F', a.2.fork? = some F' → a.2.lookHeard? = some g →
      VerifiableInference.OnPublicFiles.K3Stands x.fs x.lm x.F.next OnBytes.Model.Reading.gl g F')
    (y0 : ℕ) (hy : Reply.token (seatAt Wp.hS (readsOf Wp)).toSeat a.2 = some y0)
    (hr : a.2.replyTok? = some y0)
    (hrq : D.rq a.1 = (seatAt Wp.hS (readsOf Wp)).request a.2)
    (hF : ∃ F', a.2.fork? = some F') :
    letI := (parOf Wp.hS (workOf Wp)).sizes
    letI := (parOf Wp.hS (workOf Wp)).policy
    letI : Request := (seatAt Wp.hS (readsOf Wp)).request a.2
    PlanFacts → Request.ok = true → y0 < V →
      SameCells d.1 (headCells (k3AdrAt Wp) x Wp.H.tl D.sent D.l3.rad D.l3.oW D.l3.wOf D.l3.nr
          D.l3.nc (layMs x D.sent D.l3.rad D.l3.oW (fun j => D.l3.seat x.link false j.1) D.l3.arr
            D.l3.msgW w)) →
      (∀ j, rd (d.2 j) = headNu (k3AdrAt Wp) x Wp.H.tl D.sent D.l3.rad D.l3.oW D.l3.wOf D.l3.nr
          D.l3.nc
        (fun j => D.l3.seat x.link false j.1) D.l3.arr D.l3.msgW w (.mask j)) →
      (∀ g, a.2.lookHeard? = some g → g.shape = x.fs) → FoNums.ok x.fs = true → x.fs.NC = 6 →
      KeysTrueInFront Wp a.2 d.1 d.2 := by
  intro hP hok hV hL1 hmask hsh hfo hnc
  rw [← C.seg, Sound.mgAll_worth_head_keys D Mg C.place a y w] at hitem
  have hit := hitem hR
  intro gk hk
  obtain ⟨F', hF'⟩ := hF
  have key : ∀ (Sz : Sizes) (Po : Policy) (Rq : Request),
      Sz = (parOf Wp.hS (workOf Wp)).sizes → Po = (parOf Wp.hS (workOf Wp)).policy →
      Rq = (seatAt Wp.hS (readsOf Wp)).request a.2 →
      VerifiableInference.OnPublicFiles.K3OutKeys x.fs x.lm x.F.next
          (headNu (k3AdrAt Wp) x Wp.H.tl D.sent D.l3.rad D.l3.oW D.l3.wOf D.l3.nr D.l3.nc
            (fun j => D.l3.seat x.link false j.1) D.l3.arr D.l3.msgW w)
          (Cb.Fo.forK Cb.Gl.E
            (@headLay Sz Rq (k3AdrAt Wp) x.fs x.lm x.F.next x.ns Wp.H.tl D.l3.nr D.l3.nc)
            (a.2.replyTok?.getD 0)
            (Cb.Fo.zext (layMu x Wp.H.tl D.sent D.l3.rad D.l3.oW D.l3.wOf D.l3.nr D.l3.nc
              (fun j => D.l3.seat x.link false j.1) D.l3.arr D.l3.msgW w)))
                  OnBytes.Model.Reading.gl gk F' →
      KeysWorth (parOf Wp.hS (workOf Wp)) (seatAt Wp.hS (readsOf Wp)) a.2 d.1 d.2 gk := by
    intro Sz Po Rq e1 e2 e3 hO
    subst e1 e2 e3
    exact keys_arm_back Wp.hS (readsOf Wp) (parOf Wp.hS (workOf Wp)) a.2 d.1 d.2 g0 hg y0 hy hr
      (headCells (k3AdrAt Wp) x Wp.H.tl D.sent D.l3.rad D.l3.oW D.l3.wOf D.l3.nr D.l3.nc
        (layMs x D.sent D.l3.rad D.l3.oW (fun j => D.l3.seat x.link false j.1) D.l3.arr
          D.l3.msgW w))
      (headNu (k3AdrAt Wp) x Wp.H.tl D.sent D.l3.rad D.l3.oW D.l3.wOf D.l3.nr D.l3.nc
        (fun j => D.l3.seat x.link false j.1) D.l3.arr D.l3.msgW w)
      x.fs x.lm x.F.next hP hok hV hL1 hmask hsh hfo hnc gk F' hF' hk (hSt gk F' hF' hk) hO
  exact key (k3SizesAt Wp) (k3PolicyAt Wp) (D.rq a.1) rfl rfl hrq (hit gk F' hF' hk)

/-- What the public item "left 24" says, at the caller's place: the state has a ledger; what the
lookup heard has the caller's shape; and it stands for some rounds, at the item's letters. -/
theorem stands_of_left {x : First.Look.Place} (C : CallerFits (Wp := Wp) x) (s : S)
    (hL : VerifiableInference.OnPublicFiles.k3LeftItemAt Wp 24 s) :
    (∃ F', s.fork? = some F') ∧ (∀ g, s.lookHeard? = some g → g.shape = x.fs) ∧
    ∀ g F', s.fork? = some F' → s.lookHeard? = some g →
      VerifiableInference.OnPublicFiles.K3Stands x.fs x.lm x.F.next OnBytes.Model.Reading.gl g F' := by
  have hx : First.Look.placeAt Wp 24 false =
      some (First.Look.P.ofPlace (OnBytes.Params.settingOf Wp.P.frame) false x) := by
    letI := (parOf Wp.hS (workOf Wp)).sizes
    letI := (parOf Wp.hS (workOf Wp)).policy
    letI : Request := (seatAt Wp.hS (readsOf Wp)).request s
    have h0 := VerifiableInference.OnPublicFiles.placeAt_headAt C.place
    rwa [C.seg] at h0
  obtain ⟨p, hp, ⟨h, hsh, F0, F1, g1, rs, _, hn, hK, hh, hf⟩, _⟩ := hL
  obtain rfl := Option.some.inj (hp.symm.trans hx)
  have e : h = x.fs :=
    Option.some.inj (hsh.symm.trans (VerifiableInference.Desc.K3Asks.headAt_shape C.place))
  refine ⟨⟨F1, hf⟩, fun g hk => ?_, fun g F' hF hk => ?_⟩
  · obtain rfl : g1 = g := Option.some.inj (hh.symm.trans hk)
    exact hK.shape.trans e
  · obtain rfl : g1 = g := Option.some.inj (hh.symm.trans hk)
    obtain rfl : F1 = F' := Option.some.inj (hf.symm.trans hF)
    have hI := hK.heardIs
    rw [hn, e] at hI
    exact ⟨rs, hI⟩

/-- **THE SAME FROM WHAT THE LOOKUP LEFT**: the list of rounds, the ledger and the place's letters
all come of the public item "left 24" in front of the head's own sub-protocol. -/
theorem keys_back_left {x : First.Look.Place} (C : CallerFits (Wp := Wp) x) (a : P × S) (y : Strs)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (d : Pinned)
    (hitem : (mgAll D Mg).worth 24 3 "keys" a y w)
    (hR : VerifiableInference.OnPublicFiles.Flat.InRange w.cells)
    (hL : VerifiableInference.OnPublicFiles.k3LeftItemAt Wp 24 a.2) (g0 : Given)
    (hg : given (parOf Wp.hS (workOf Wp)) (seatAt Wp.hS (readsOf Wp)) a.2 = .ok g0)
    (y0 : ℕ) (hy : Reply.token (seatAt Wp.hS (readsOf Wp)).toSeat a.2 = some y0)
    (hr : a.2.replyTok? = some y0)
    (hrq : D.rq a.1 = (seatAt Wp.hS (readsOf Wp)).request a.2) :
    letI := (parOf Wp.hS (workOf Wp)).sizes
    letI := (parOf Wp.hS (workOf Wp)).policy
    letI : Request := (seatAt Wp.hS (readsOf Wp)).request a.2
    PlanFacts → Request.ok = true → y0 < V →
      SameCells d.1 (headCells (k3AdrAt Wp) x Wp.H.tl D.sent D.l3.rad D.l3.oW D.l3.wOf D.l3.nr
          D.l3.nc (layMs x D.sent D.l3.rad D.l3.oW (fun j => D.l3.seat x.link false j.1) D.l3.arr
            D.l3.msgW w)) →
      (∀ j, rd (d.2 j) = headNu (k3AdrAt Wp) x Wp.H.tl D.sent D.l3.rad D.l3.oW D.l3.wOf D.l3.nr
          D.l3.nc
        (fun j => D.l3.seat x.link false j.1) D.l3.arr D.l3.msgW w (.mask j)) →
      FoNums.ok x.fs = true → x.fs.NC = 6 → KeysTrueInFront Wp a.2 d.1 d.2 := by
  intro hP hok hV hL1 hmask hfo hnc
  obtain ⟨hF, hsh, hSt⟩ := stands_of_left C a.2 hL
  exact keys_back_mgAll Mg C a y w d hitem hR g0 hg hSt y0 hy hr hrq hF hP hok hV hL1 hmask hsh hfo
    hnc

#print axioms keys_back_mgAll
#print axioms stands_of_left
#print axioms keys_back_left

end VerifiableInference.Desc.Kinds.Head.Law.AtTable
