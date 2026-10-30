-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/KeysRoad.lean: THE KEYS' ROAD: FROM WHAT THE OUTPUT HEAD's LAW CLOSES IN
FRONT OF ITS OWN BLOCK ON THE CALLS' KEY VECTORS (Law/RowJoin.lean: KeysWorth: the formula of
"join", fed with the extensions of the calls' tables at their key points, is worth 0 in the world of
the ledger and the mask row) TO THE SENTENCE THAT THE TABLE OF JOINTS' FILLING HOLDS AT worth m 3
"keys" AT THE HEAD (Johnson/Top/H/K3RowOut.lean: K3OutKeys: the library's claim on the join is 0 at
every list of rounds for which what the lookup heard stands). Statements and proofs.

  joinForm_worth   the worth of the library's form of "join" at ANY key forms, where what the
                   lookup heard stands: the library's claim on the join at these forms' worths.
  joinForm_is      K6's formula of "join" IS the library's form, by unfolding.
  worldE_is        K6's world of a ledger, a mask row and no entries IS the library's world
                   of that ledger, where the mask row, read, is the reading nu at the masks.
  outKeys_of_worth KeysWorth at a verifier's state, cells c and a mask row; what the lookup has
                   heard there; hmask; hkeys: K3OutKeys at the reading nu and the vectors Kv.
  wt_eqNrev        two writings of one weight: K6's (the highest bit's coordinate first) is
                   the library's (the lowest first) at the list turned round.
  trueKey_ext      hkeys, PAID DOWN TO THE CELLS: a call's table's extension at its key point, read,
                   is the library's extension of the vector "the table of cells c', read", where c
                   and c' agree on what the head's relation names.
  keys_arm         MAIN: in the shape of the filling's arm "keys": from the third clause of what the
                   head's law closes in front (Law/RowPins.lean: K6In).

BY the library's Fo.join_claim (OnBytes/Tie/Pv/Lookup/Forest/FoClaimsPort.lean): it takes any key
forms, one a call, and no run's yes; and the step on cEnd of join_worth
(Johnson/Top/H/K3RunsLaw.lean).
WHAT IT IS NOT. Implications. TWO NAMED PREMISES OF keys_arm THAT NOBODY PAYS: **hL1**: SameCells c
c' (at c := the cells that compCut reads off the witness and c' := the closed caller's: two readings
of one witness's messages: by report compiled, not shown here, under its own named conditions) ·
**hmask**: the mask row, read, is nu at the masks' places. Beside: the shape in what was heard is
the place's, lawful, with six calls; the tests on the plan and the request; the token is below V;
the two readers of the token give one. (The filling's readers forkR and heardC are S.fork? and
S.lookHeard? by abbreviations: First/Look/K3FillWorth.lean: by reading.) Nothing on soundness.
LETTERS. No letter stands under "there is".

-/
import Mathlib
import Johnson.Top.H.K3RowOut
import Johnson.Top.H.K3RunsLaw
import Johnson.Top.H.K3OutProof
import Johnson.Desc.Kinds.Law.RowJoin
import Johnson.Desc.Kinds.Law.CellsAlike
import Johnson.Desc.Kinds.Law.FromGiven
import Johnson.Stored.HeadSeatAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun OnBytes.PscTie _root_.Fo
open Cb Cb.Fo Cb.Fo.PlaneClaims
open OnBytes.K.Kc

/-- **THE WORTH OF THE FORM OF "join", AT ANY KEY FORMS, WHERE WHAT THE LOOKUP HEARD STANDS**: in
the world of a ledger later than the hearing's, at the reading nu of the masks: the library's claim
on the join, at the key forms' worths. (Top/H/K3RunsLaw.lean's join_worth without its run.) -/
theorem joinForm_worth {K : Type} [CommRing K] (ρ : OnBytes.Model.Reading K) (g : Heard)
    (KF : Array Aff) (hok : FoNums.ok g.shape = true) (hsz : KF.size = g.shape.NC) (lm jLK : ℕ)
    (rsK : Rounds K) (F0 H : Fork) (hI : HeardIs ρ g F0 (endsOf g.shape lm jLK rsK))
    (hL : _root_.Fo.Later F0 H) (ν : _root_.Fo.Pl → K) (entry : ℕ → ℕ → ℕ → K) :
    (joinForm g KF).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) =
      claimJoin g.shape lm jLK rsK ν fun k =>
        (KF.getD k (Aff.ofConst zeroE)).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) := by
  have hcE : g.cEnd.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) =
      AffK.val ((endsOf g.shape lm jLK rsK).cEndF, (endsOf g.shape lm jLK rsK).cEndC) ν := by
    rw [(hI.cEnd H hL).2 (fun j => ν (.mask j)) entry,
      evalL_muOf (onMasks_keyTop g.shape lm jLK rsK) ν]
    show _ = evalL ν (scale (-1) (endsOf g.shape lm jLK rsK).cEndInc) + _
    rw [evalL_scale]
    ring
  exact join_claim ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) g KF hok hsz lm jLK rsK ν
    hI.theta hI.alpha (fun k _ => by
      rw [rdL_getD, show rdL ρ g.e = _ from hI.e]) hI.zy hcE

end VerifiableInference.OnPublicFiles

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE)
open OnBytes.Model (Fork Reading Aff World)
open VerifiableInference.OnPublicFiles

/-- This folder's formula of "join" is the library's form. -/
theorem joinForm_is (g : OnBytes.Model.Forest.Heard) (KF : Array Aff) :
    Came.joinForm g KF = _root_.Fo.joinForm g KF := rfl

/-- This folder's world is the library's, where the mask row, read, is nu at the masks. -/
theorem worldE_is (F : Fork) (mask : Nat → E) (nu : _root_.Fo.Pl → K)
    (hmask : ∀ j, rd (mask j) = nu (.mask j)) :
    worldE F mask noEnt = F.worldOf Reading.gl (fun j => nu (.mask j)) fun _ _ _ => 0 := by
  have h1 : (fun j => rd (hidden F mask j)) = fun j =>
      Reading.gl.val (F.vp.getD j zeroE) - Reading.gl.val (F.mf.getD j zeroE) * nu (.mask j) := by
    funext j
    show rd (F.vp.getD j 0 - F.mf.getD j 0 * mask j) = _
    rw [rd_sub, rd_mul, hmask]
    rfl
  have h2 : (fun t r i => rd (noEnt t r i)) = fun _ _ _ => (0 : K) := by
    funext _ _ _
    exact rd_zero
  show (⟨fun j => rd (hidden F mask j), fun t r i => rd (noEnt t r i)⟩ : World K) = ⟨_, _⟩
  rw [h1, h2]

/-- This folder's weight of a corner (the highest bit's coordinate first) at one coordinate more. -/
theorem wt_snoc (x : K) : ∀ (xs : List K) (i : Nat),
    wt (xs ++ [x]) i = wt xs (i / 2) * (if i % 2 = 1 then x else 1 - x)
  | [], i => by
    have e : i.testBit 0 = Decidable.decide (i % 2 = 1) := Nat.testBit_zero i
    simp [wt, e]
  | a :: xs, i => by
    have e : (i / 2).testBit xs.length = i.testBit (xs.length + 1) := by
      rw [Nat.testBit_succ]
    show (if i.testBit (xs ++ [x]).length then a else 1 - a) * wt (xs ++ [x]) i =
      (if (i / 2).testBit xs.length then a else 1 - a) * wt xs (i / 2) * _
    rw [wt_snoc x xs i, e, List.length_append, List.length_singleton, mul_assoc]

/-- **TWO WRITINGS OF ONE WEIGHT**: this folder's (the highest bit's coordinate first) is the
library's (the lowest first) at the list turned round. -/
theorem wt_eqNrev : ∀ (l : List K) (i : Nat), wt l.reverse i = TwV.eqN l i
  | [], _ => rfl
  | x :: xs, i => by
    rw [List.reverse_cons, wt_snoc, wt_eqNrev xs (i / 2), mul_comm]
    rfl

/-- A list's sum over a range, as a sum over the finite set. -/
theorem sum_range_list (f : Nat → K) : ∀ n, ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_range_list f n,
      Finset.sum_range_succ]
    simp

/-- **hkeys, PAID DOWN TO THE CELLS**: a call's table's extension at its key point, read, is the
library's extension of the vector "entry i: the table of cells c' at column i / T, position i % T,
read", where c and c' agree on what the head's relation names. -/
theorem trueKey_ext [Sizes] [Policy] [Request] [Token] (c c' : NCells) (h : SameCells c c')
    (P : PlanFacts) (hreq : Request.ok = true) (hy : y < V) (zk : Nat → Point) (call : Nat) :
    rd (trueKey c zk call) =
      _root_.Fo.extL (fun i => rd (keyTable c' call (i / Norm.T) (i % Norm.T)))
        (_root_.Fo.rdA Reading.gl (zk call)) := by
  have hT : 0 < Norm.T := Nat.pos_of_ne_zero (by unfold Norm.T; positivity)
  rw [Came.rd_trueKey]
  unfold _root_.Fo.extL _root_.Fo.rdA
  rw [sum_range_list, List.length_map, Array.length_toList]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [rd_eq, if_pos (Finset.mem_range.1 hi), ← wt_eqNrev, List.reverse_reverse,
    Came.keyTable_same h P hreq hy call _ (Nat.mod_lt i hT)]
  rfl

/-- **THE KEYS' ROAD.** -/
theorem outKeys_of_worth (p : Par) (L : Seat VerifiableInference.Desc.First.S)
    (s : VerifiableInference.Desc.First.S) (c : NCells) (mask : Nat → E)
    (gk : OnBytes.Model.Forest.Heard) (hK : KeysWorth p L s c mask gk) (lm first : ℕ)
    (nu : _root_.Fo.Pl → K) (Kv : ℕ → ℕ → K) (hok : FoNums.ok gk.shape = true)
    (h6 : gk.shape.NC = 6) (hmask : ∀ j, rd (mask j) = nu (.mask j))
    (hkeys : ∀ (g : Given) (z : Point × (Nat → Point)), given p L s = .ok g →
      L.lookup s = some z → ∀ call, call < 6 → rd (trueKey c z.2 call) =
        _root_.Fo.extL (Kv call) (_root_.Fo.rdA Reading.gl (gk.zk.getD call #[]))) :
    K3OutKeys gk.shape lm first nu Kv Reading.gl gk (L.ledger s) := by
  intro rs hI
  obtain ⟨g, z, hg, hz, hv⟩ := hK
  have hsz : (trueKeys g z.2 c).size = gk.shape.NC := by
    rw [h6]
    simp [trueKeys]
  rw [worldE_is _ mask nu hmask, joinForm_is] at hv
  have hJ := joinForm_worth Reading.gl gk (trueKeys g z.2 c) hok hsz lm first rs (L.ledger s)
    (L.ledger s) hI (_root_.Fo.Later.refl _) nu fun _ _ _ => 0
  have hv' : (_root_.Fo.joinForm gk (trueKeys g z.2 c)).value Reading.gl
      ((L.ledger s).worldOf Reading.gl (fun j => nu (.mask j)) fun _ _ _ => 0) = 0 := hv
  rw [hv'] at hJ
  show _root_.Fo.claimJoin gk.shape lm first rs nu
    (VerifiableInference.OnPublicFiles.keysAt gk.shape lm first Kv rs) = 0
  rw [hJ]
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

/-- **THE SAME IN THE SHAPE OF THE FILLING's ARM "keys"** (First/Look/K3HeadFill.lean: worthHead):
at whatever the state shows as heard and as its ledger; the vectors: "entry i of call number call:
the table of cells c' at column i / T, position i % T, read", at S.replyTok?'s token or 0: what the
closed caller's layout has by its definition (First/Look/K3CallerHead.lean: headLay.K). -/
theorem keys_arm (h : OnBytes.Model.Head.Shape) (iU3 : ℕ) (p : Par)
    (s : VerifiableInference.Desc.First.S) (c : NCells) (mask : Nat → E)
    (hK : ∃ gk, s.lookHeard? = some gk ∧ KeysWorth p (seatAt h iU3) s c mask gk) (y0 : ℕ)
    (hy : Reply.token (seatAt h iU3).toSeat s = some y0) (hr : s.replyTok? = some y0)
    (c' : NCells) (nu : _root_.Fo.Pl → K) (fs : OnBytes.Model.Forest.Shape) (lm first : ℕ) :
    letI := p.sizes
    letI := p.policy
    letI : Request := (seatAt h iU3).request s
    PlanFacts → Request.ok = true → y0 < V → SameCells c c' →
      (∀ j, rd (mask j) = nu (.mask j)) →
      (∀ g, s.lookHeard? = some g → g.shape = fs) → FoNums.ok fs = true → fs.NC = 6 →
      ∀ (g : OnBytes.Model.Forest.Heard) (F' : Fork), s.fork? = some F' → s.lookHeard? = some g →
        K3OutKeys fs lm first nu
          (fun call i =>
            letI : Token := ⟨s.replyTok?.getD 0⟩
            rd (keyTable c' call (i / Norm.T) (i % Norm.T))) Reading.gl g F' := by
  letI := p.sizes
  letI := p.policy
  letI : Request := (seatAt h iU3).request s
  intro hP hreq hyV hL1 hmask hsh hok h6 g F' hF hk
  obtain ⟨gk, hk', hKW⟩ := hK
  obtain rfl : gk = g := Option.some.inj (hk'.symm.trans hk)
  obtain rfl := hsh gk hk
  have hled : (seatAt h iU3).ledger s = F' := by
    show s.fork?.getD {} = F'
    rw [hF]
    rfl
  rw [hr, ← hled]
  refine outKeys_of_worth p (seatAt h iU3) s c mask gk hKW lm first nu _ hok h6 hmask ?_
  intro g z hg hz call _
  obtain ⟨z', y, hz', hy', _, rfl⟩ := Came.given_ok p _ s g hg
  obtain rfl : y = y0 := Option.some.inj (hy'.symm.trans hy)
  have hz2 : (seatAt h iU3).lookup s = some (gk.zx, fun c => gk.zk.getD c #[]) := by
    show (s.lookHeard?.map fun g => (g.zx, fun c => g.zk.getD c #[])) = _
    rw [hk]
    rfl
  obtain rfl : z = (gk.zx, fun c => gk.zk.getD c #[]) := Option.some.inj (hz.symm.trans hz2)
  letI : Token := ⟨y⟩
  exact trueKey_ext c c' hL1 hP hreq hyV (fun c => gk.zk.getD c #[]) call

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.keys_arm
#print axioms VerifiableInference.OnPublicFiles.joinForm_worth
#print axioms VerifiableInference.Desc.Kinds.Head.Law.outKeys_of_worth
#print axioms VerifiableInference.Desc.Kinds.Head.Law.wt_eqNrev
#print axioms VerifiableInference.Desc.Kinds.Head.Law.trueKey_ext
#print axioms VerifiableInference.Desc.Kinds.Head.Law.joinForm_is
#print axioms VerifiableInference.Desc.Kinds.Head.Law.worldE_is
