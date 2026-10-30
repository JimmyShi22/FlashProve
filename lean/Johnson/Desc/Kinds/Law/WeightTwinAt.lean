-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/WeightTwinAt.lean: the output head's own claim on the committed weights and
the claim that the merge takes, held against each other AT THE CARRIED RECORD'S OWN LETTERS.


The head's block lays no claim (Law/MergeClaimAt.lean). The claim that the merge takes at the head's
link is made by the step without a round behind the digits' lookup: First.Look.weightsClaim R lay
(Johnson/Desc/First/Look/LookQuiet.lean), at a record R of a run that is made of the public record
and of three fields of the carried record: the covered positions, what the head heard (x) and the
tables (t). Law/WeightTwin.lean shows, at the level of values and under nine named ties of the
letters (TwinTies), that the two claims speak of one sum. WHAT THAT PLAIN TEXT RETURNS IS A
LAW OF ANOTHER FILE: Johnson/Top/H0/K11Caller/HeadClaim.lean: weightsClaim_head: called here.



Main names (namespace VerifiableInference.Desc.Kinds.Head.Law; the theorems in Came).
  runAt W cov x t: the record of a run at which the step behind the digits' lookup calls
      weightsClaim.
  FormsAt W s' c mask: the rest of what the block's law opens on its own runs.
  LeftTies W g cov x t ew: THE TWO TIES THAT ARE LEFT: ew and wx of the top digit's key.
  weightTrue_of_says: THE WAY BACK: under TwinTies: if the hidden value under the second end value's
      variable reads as the claim's sum over W, then WeightTrue. weightTrue_iff_says: both ways.
  twinTies_heardOf: at a run whose x is heardOf gk H (Johnson/Stored/HeadSeat.lean), the ties hWin,
      hrH and hrs hold.
  x_behind: behind a yes of the head's block the record's x is heardOf gk H.
  runAt_sizes: hT and hV. hOn_of_covered: the covered positions as S.covered makes them.
  reads_as_Hof: at cells whose weights are whOf M (Law/WhOf.lean), where M holds the index i, the
      weights read as the library's Hof of i's digit matrix (cast_H_eq_Hof, HeadReq.lean).
  behind_all: all that lies behind a yes of the head's block, at one set of letters; with THE SLOT
      OF THE CLAIM'S VALUE: the kind's claim's variable is Aff.slot x.sV, the slot that the merge
      takes (Law/SvLaidHeard.lean's sv_heard, called).
  k6Out_iff: THE WAY INTO what the block's law opens: K6Out is WeightAt, FormsAt and the join's
      sentence.
  zt_size_at: where the tests on the plan say yes, the end of the lookup's point has lt coordinates.
  lPd_ref: at the reference number of features the padded features have 13 bits.
  twin_at: THE TWIN'S OWN EQUATION: where the plain text returns a claim at runAt, at the x that the
      head's block laid, and mu := mergeClaimAt W s': the returned claim's sum in a matrix is the
      reading of mu's sum over the cells' weights, and mu's variable is the slot that the merge
      takes.

Every letter under "there is", and the clause that pins it. x_behind, behind_all, twin_at: g by
given at s; H and F1 by the hearing's return; a by s.here; gk by a.lookHeard; Q by the equation of
records; mu by mergeClaimAt; q by callNo; sg by seg?. FormsAt: g, H by the seat's two readers at s'.
OF THE NINE TIES: hT, hV, hWin, hrH, hrs are paid here; hrHs, and that rs has 13 coordinates, fall,
by Law/SumSize.lean and zt_size_at, to the tests on the plan; hOn is a premise of twin_at and is
paid in
Law/WeightJoint.lean.

Premises that nobody pays here. LeftTies. The reference layout at W.layers.wsLay (Z, hl); W.H.lamS =
13; V = nV; d = nD: public numbers. "Wh reads as Hof" in twin_at.
Limits. THE REFERENCE SIZES ALONE: at the small size the tops are empty. Values, not texts. t is
idle by value: no function under the claim reads it. No values are shown at which the premises hold
together. No draw, no error term, nothing on soundness.
-/
import Mathlib
import Johnson.Desc.Kinds.Law.MergeClaimAt
import Johnson.Desc.Kinds.Law.RowPromise
import Johnson.Desc.Kinds.Law.WeightTwin
import Johnson.Desc.Kinds.Law.K06Glue
import Johnson.Desc.Kinds.Law.Cut
import Johnson.Desc.Kinds.Law.OpenedSent
import Johnson.Desc.Kinds.Law.WhOf
import Johnson.Road.HeadReq
import Johnson.Desc.Kinds.Law.SvLaidHeard
import Johnson.Desc.Kinds.Law.SumSize
import Johnson.Desc.Kinds.Law.GivenLetters
import Johnson.Top.H0.K11Caller.HeadClaim

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE okE)
open OnBytes.Model (Reading eqTab Fork)
open OnBytes.Road (eqR claimVal Wm)
open OnBytes.Road.Hd (avOf facKK)
open Norm (lt ls d lPd T S2)
open Inst.Model (ppref)
open Inst.Model.Layout (kRef)
open Inst.Model.Head (Hof nV nD)
open VerifiableInference.Desc.First (S HeadOwn)

/-- **The record of a run at which the step behind the digits' lookup calls weightsClaim.** -/
def runAt (W : OnBytes.Model.Verify.Public) (cov : OnBytes.Model.Head.Covered)
    (x : OnBytes.Model.Head.Heard) (t : OnBytes.Model.Head.Tables) : OnBytes.Model.Head.Run :=
  { h := W.hS, L := W.HLy, b := OnBytes.Model.Verify.borderOf W.y, hp := W.H, cov := cov, x := x,
    t := t, iU3 := (W.H.tl.ix.U.getD 2 none).getD 0 }

/-- The rest of what the block's law opens on its own runs: every form of every run is worth 0, at
the
letters that the seat's readers give at s' and at s' own ledger. -/
def FormsAt (W : OnBytes.Model.Verify.Public) (s' : S) (c : NCells) (mask : Nat → E) : Prop :=
  ∃ (g : Given) (H : HeardAll),
    given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s' = .ok g ∧
    (seatAt W.hS (readsOf W)).heard s' = some H ∧
    (let _ : Norm.Heard := H.1
     let _ : FinalNorm.Heard := H.2.1
     let _ : Heard := H.2.2
     let _ : FinalNorm.Reads := normReadsAtCells c
     let _ : Reads := readsAt c.toCells
     ∀ name fs, claims.lookup name = some fs → ∀ f, f ∈ fs →
       atWorld ((seatAt W.hS (readsOf W)).ledger s') mask noEnt f = 0)

/-- **The two ties that are left**, at letters g and at runAt: the weights ew read as the kind's
weights of the top digit's key; and their sum over the vocabulary likewise. -/
def LeftTies (W : OnBytes.Model.Verify.Public) (g : Given)
    (cov : OnBytes.Model.Head.Covered) (x : OnBytes.Model.Head.Heard)
    (t : OnBytes.Model.Head.Tables) (ew : Array E) : Prop :=
  (∀ v, v < V → rd (ew.getD v zeroE) = rd (In.ew .marginTop v)) ∧
    rd (OnBytes.Model.Head.wxOf (runAt W cov x t) ew) = rd (In.wx .marginTop)

namespace Came

section Letters
variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In]

section
variable [Heard]

/-- **The way back: the merge's sentence gives WeightTrue.** -/
theorem weightTrue_of_says {R : OnBytes.Model.Head.Run} {ew : Array E} (h : TwinTies R ew)
    {s : OnBytes.Model.WsShape} (Z : OnBytes.Road.SizedW s ppref) {lay : OnBytes.Model.WsLay}
    (hl : OnBytes.Model.wsLayOf s true kRef = .ok lay) (W : Wm K) (c : Cells) (hV : V = nV)
    (hd : d = nD) (hrs : (rs : Point).size = 13)
    (hWh : ∀ k v, k < d → v < V → ((c.Wh k v : Int) : K) = Hof W k v)
    (F : Fork) (mask : Nat → E) (ent : Nat → Nat → Nat → E)
    (hc : okE (logits.end_ 1).var.const = true)
    (hs : rd (atWorld F mask ent (logits.end_ 1).var) = claimVal Reading.gl lay W
      { ui := lay.U.size - 1, f := [{ AV := avOf R ew }, facKK R.x.rs 10 5 13] }) :
    WeightTrue c F mask ent := by
  unfold WeightTrue
  refine eq_of_rd (okE_atWorld F mask ent _ hc) (okE_sumTo _ _) ?_
  rw [← twin_sum h Z hl W c hV hd hrs hWh]
  exact hs

/-- Both ways. -/
theorem weightTrue_iff_says {R : OnBytes.Model.Head.Run} {ew : Array E} (h : TwinTies R ew)
    {s : OnBytes.Model.WsShape} (Z : OnBytes.Road.SizedW s ppref) {lay : OnBytes.Model.WsLay}
    (hl : OnBytes.Model.wsLayOf s true kRef = .ok lay) (W : Wm K) (c : Cells) (hV : V = nV)
    (hd : d = nD) (hrs : (rs : Point).size = 13)
    (hWh : ∀ k v, k < d → v < V → ((c.Wh k v : Int) : K) = Hof W k v)
    (F : Fork) (mask : Nat → E) (ent : Nat → Nat → Nat → E)
    (hc : okE (logits.end_ 1).var.const = true) :
    WeightTrue c F mask ent ↔
      rd (atWorld F mask ent (logits.end_ 1).var) = claimVal Reading.gl lay W
        { ui := lay.U.size - 1, f := [{ AV := avOf R ew }, facKK R.x.rs 10 5 13] } :=
  ⟨weightTrue_says h Z hl W c hV hd hrs hWh F mask ent,
    weightTrue_of_says h Z hl W c hV hd hrs hWh F mask ent hc⟩

end

/-- **At a run whose x is what the head's own block lays, three ties hold.** -/
theorem twinTies_heardOf (gk : OnBytes.Model.Forest.Heard) (H : HeardAll)
    (R : OnBytes.Model.Head.Run) (ew : Array E) (hx : R.x = heardOf gk H) (hT : R.h.T = T)
    (hV : R.h.V = V) :
    let _ : Heard := H.2.2
    (∀ i, i < T → R.cov.hOn.getD i false = checked i) → (rH : Point).size = lt →
    (∀ v, v < V → rd (ew.getD v zeroE) = rd (In.ew .marginTop v)) →
    rd (OnBytes.Model.Head.wxOf R ew) = rd (In.wx .marginTop) → TwinTies R ew := by
  intro _ hOn hrHs hew hwx
  refine ⟨hT, hV, hOn, fun i hi hci => ?_, ?_, hrHs, ?_, hew, hwx⟩
  · rw [hx]
    simp [heardOf, Array.getD, hi, hci]
  · rw [hx]
    rfl
  · rw [hx]
    rfl

end Letters

/-- **Behind a yes of the head's block the record's x is heardOf gk H**, at the letters that given
returns in front, at what the hearing returned, and at what the lookup left. -/
theorem x_behind (h : OnBytes.Model.Head.Shape) (iU3 work l : Nat) {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hd : (blockAt h iU3 work l).decide s rs gs = .ok s') :
    ∃ (g : Given) (H : HeardAll) (F1 : Fork) (a : HeadOwn) (gk : OnBytes.Model.Forest.Heard)
      (Q : OnBytes.Model.Psc),
      given (parOf h work) (seatAt h iU3) s = .ok g ∧
      hear ((seatAt h iU3).ledger s) rs = some (H, F1, []) ∧
      s.here = .head a ∧ a.lookHeard = some gk ∧
      s' = { s with here := .head { a with F := F1, x := some (heardOf gk H),
                                           squaresP := some Q } } := by
  have hd' : decideBy (fun _ => rounds) (fun _ => hear) (fun _ _ => forTheMerge) (parOf h work)
      (seatAt h iU3) s rs = .ok s' := hd
  obtain ⟨g, H, F, s1, s2, hg, hh, e1, e2, hs'⟩ := decide_hands hd'
  have hs2 : s' = s2 := hs'
  obtain ⟨a, _, _, _, ha, hop, _, _⟩ := decide_record h iU3 work l hd
  have e1' : s.putFork? F = .ok s1 := e1
  have hs1 : s.putFork F = s1 := by
    unfold S.putFork? at e1'
    split at e1'
    · exact ((S.unmarked_ok _ _).mp e1').1
    · cases e1'
  have hp : s.putFork F = { s with here := .head { a with F := F } } := by
    simp [S.putFork, ha, hop]
  rw [hp] at hs1
  subst hs1
  obtain ⟨o, gk, ho, hgk, hB⟩ := setHeard_form h iU3 e2
  have ho' : (First.Here.head { a with F := F }) = .head o := ho
  cases ho'
  obtain ⟨z, y, _, hy, _, rfl⟩ := given_ok _ _ _ _ hg
  have hy' : s.out.reply.map OnBytes.Desc.Reply.tokOf = some y := hy
  have ht : (⟨(s.out.reply.map OnBytes.Desc.Reply.tokOf).getD 0⟩ : Token) = ⟨y⟩ := by
    rw [hy']
    rfl
  refine ⟨_, H, F, a, gk, pscOf H.1.squares.psc false, hg, hh, ha, hgk, ?_⟩
  rw [hs2, hB]
  show ({ s with here := .head { a with
      F := F
      x := some (@heardOf (sizesOf h) (requestOf s)
        ⟨(s.out.reply.map OnBytes.Desc.Reply.tokOf).getD 0⟩ gk H)
      squaresP := some (pscOf H.1.squares.psc false) } } : S) = _
  rw [ht]
  rfl

/-- At the letters that given returns at the seat, the run's numbers of positions and of entries of
the vocabulary are the text's. -/
theorem runAt_sizes (W : OnBytes.Model.Verify.Public) {s : S} {g : Given}
    (hg : given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s = .ok g)
    (cov : OnBytes.Model.Head.Covered) (x : OnBytes.Model.Head.Heard)
    (t : OnBytes.Model.Head.Tables) : (runAt W cov x t).h.T = T ∧ (runAt W cov x t).h.V = V := by
  obtain ⟨z, y, _, _, _, rfl⟩ := given_ok _ _ _ _ hg
  exact ⟨rfl, rfl⟩

/-- The covered positions, as the carried record makes them of the request's words: position i is
on just where it lies from the first checked position to the last. -/
theorem hOn_of_covered {T' V' : Nat} {s : S} {cov : OnBytes.Model.Head.Covered}
    (h : s.covered T' V' = .ok cov) (i : Nat) (hi : i < T') :
    cov.hOn.getD i false =
      (Decidable.decide (s.rowR ≤ i) && Decidable.decide (i < s.rowE)) := by
  unfold S.covered at h
  split at h
  · unfold S.coveredAt at h
    dsimp only at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i hsz
        split at h
        · cases h
        · split at h
          · cases h
          · have e := Except.ok.inj h
            have hT : s.reqT = T' := by
              unfold S.reqT
              have : s.req.size = T' + 2 := by simpa using hsz
              omega
            rw [← e]
            simp [Array.getD, hi, S.rowR, S.rowE, hT]
  · cases h

/-- **The third link**: at cells whose weights are read off the stored table's cells M
(Law/WhOf.lean), where M holds the index i, the weights read as the library's Hof of i's digit
matrix, carried into the field. -/
theorem reads_as_Hof {rows cols : Nat} (hr : rows ≤ Inst.Model.Layout.hRef) (hc : cols ≤ 2 ^ kRef)
    {M : Fin rows → Fin cols → VerifiableInference.OnPublicFiles.Flat.GE} {i : Cm.Idx}
    (hH : VerifiableInference.OnPublicFiles.Flat.Holds M i) {c : Cells} (hWh : c.Wh = whOf M) {k v : Nat}
    (hk : k < nD) (hv : v < nV) :
    ((c.Wh k v : Int) : K) = Hof (fun r c' => ((i.mat r c' : Int) : K)) k v := by
  rw [hWh, whOf_holds hr hc hH]
  exact OnBytes.Road.HeadReq.cast_H_eq_Hof i.mat hk hv

/-- **All that lies behind a yes of the head's block, at one set of letters**: what the block lays
(x_behind); the seat's readers behind it, and the kind's claim off the record
(Law/MergeClaimAt.lean); the ledger behind; and THE SLOT OF THE CLAIM'S VALUE: the variable of the
kind's claim is the slot x.sV, which is the slot that the merge takes (Law/SvLaidHeard.lean's
sv_heard, called). -/
theorem behind_all (W : OnBytes.Model.Verify.Public) (l : Nat) {s s' : S}
    {rv : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hd : (blockAt W.hS (readsOf W) (workOf W) l).decide s rv gs = .ok s')
    (hWL : WellLaid ((seatAt W.hS (readsOf W)).ledger s)) (hcan : Canonical rv) :
    ∃ (g : Given) (H : HeardAll) (F1 : Fork) (a : HeadOwn) (gk : OnBytes.Model.Forest.Heard)
      (Q : OnBytes.Model.Psc),
      given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s = .ok g ∧
      hear ((seatAt W.hS (readsOf W)).ledger s) rv = some (H, F1, []) ∧
      s.here = .head a ∧ a.lookHeard = some gk ∧
      s' = { s with here := .head { a with F := F1, x := some (heardOf gk H),
                                           squaresP := some Q } } ∧
      given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s' = .ok g ∧
      (seatAt W.hS (readsOf W)).heard s' = some H ∧
      (seatAt W.hS (readsOf W)).ledger s' = F1 ∧
      mergeClaimAt W s' = some (mergeClaimOf g H) ∧
      (mergeClaimOf g H).value.var = OnBytes.Model.Aff.slot (heardOf gk H).sV := by
  obtain ⟨g, H, F1, a, gk, Q, hg, hh, ha, hgk, hs'⟩ :=
    x_behind W.hS (readsOf W) (workOf W) l hd
  obtain ⟨g2, H2, F2, _, hg2, hh2, hg', hH', _, hm⟩ := mergeClaim_behind W l hd hWL hcan
  obtain rfl : g = g2 := Except.ok.inj (hg.symm.trans hg2)
  obtain rfl : H = H2 := congrArg Prod.fst (Option.some.inj (hh.symm.trans hh2))
  obtain ⟨g3, H3, o', x', hg3, hh3, ho', hx', _, hv⟩ :=
    sv_heard W.hS (readsOf W) (workOf W) l s s' rv gs hWL hd
  obtain rfl : g = g3 := Except.ok.inj (hg.symm.trans hg3)
  have e3 := Option.some.inj (hh.symm.trans hh3)
  obtain rfl : H = H3 := congrArg Prod.fst e3
  have eF : (seatAt W.hS (readsOf W)).ledger s' = F1 := (congrArg (fun p => p.2.1) e3).symm
  have ex : x' = heardOf gk H := by
    rw [hs'] at ho'
    have e : First.Here.head { a with F := F1, x := some (heardOf gk H), squaresP := some Q } =
        .head o' := ho'
    cases e
    exact (Option.some.inj hx').symm
  refine ⟨g, H, F1, a, gk, Q, hg, hh, ha, hgk, hs', hg', hH', eF, hm, ?_⟩
  rw [← ex]
  exact hv

/-- **The way into what the block's law opens**: K6Out is the sentence on the kind's claim, and the
rest: the runs' forms are worth 0, and the join's sentence. -/
theorem k6Out_iff (W : OnBytes.Model.Verify.Public) (s' : S) (d : Pinned) :
    K6Out W s' d ↔ WeightAt W s' d.1.toCells d.2 ∧ FormsAt W s' d.1 d.2 ∧
      ∃ gk, s'.lookHeard? = some gk ∧
        JoinOpened (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s' d.1 d.2 gk := by
  constructor
  · rintro ⟨⟨g, H, hg, hH, hO⟩, hj⟩
    exact ⟨⟨g, H, hg, hH, hO.1⟩, ⟨g, H, hg, hH, hO.2⟩, hj⟩
  · rintro ⟨⟨g, H, hg, hH, hw⟩, ⟨g2, H2, hg2, hH2, hf⟩, hj⟩
    obtain rfl : g = g2 := Except.ok.inj (hg.symm.trans hg2)
    obtain rfl : H = H2 := Option.some.inj (hH.symm.trans hH2)
    exact ⟨⟨g, H, hg, hH, hw, hf⟩, hj⟩

/-- Where the tests on the plan say yes, the end of the lookup's point, at the letters that given
returns, has lt coordinates (Law/GivenLetters.lean's given_letters; the law of fromLookup). -/
theorem zt_size_at (W : OnBytes.Model.Verify.Public) {s : S} {g : Given}
    (hg : given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s = .ok g)
    (hplan : (parOf W.hS (workOf W)).ok = true) : (FinalNorm.zt).size = lt := by
  obtain ⟨z, y, _, _, _, rfl⟩ := given_ok _ _ _ _ hg
  obtain ⟨z2, _, _, hn, _, _, hL⟩ := Came.given_letters _ _ _ _ hg (parOf W.hS (workOf W)).sT hplan
  have e := @LettersOk.zt (parOf W.hS (workOf W)).sizes _ _ _ hL
  rw [← hn] at e
  exact e

/-- At the reference number of features the padded features have 13 bits. -/
theorem lPd_ref [Sizes] (hd : d = nD) : lPd = 13 := by
  unfold Norm.lPd
  rw [hd]
  rfl

/-- **The twin's own equation, at the kind's claim off the record.** Where the plain text of the
step behind the digits' lookup returns a claim at runAt, at the x that the head's block laid, and
mu is the kind's claim off the record behind the head's block: the sum that the returned claim
speaks of in a matrix Wm' is the reading of mu's sum over the cells' weights; and mu's variable is
the slot that the merge takes. -/
theorem twin_at (W : OnBytes.Model.Verify.Public) (l : Nat) {s s' : S}
    {rv : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hd : (blockAt W.hS (readsOf W) (workOf W) l).decide s rv gs = .ok s')
    (hWL : WellLaid ((seatAt W.hS (readsOf W)).ledger s)) (hcan : Canonical rv)
    (hplan : (parOf W.hS (workOf W)).ok = true) :
    ∃ (g : Given) (H : HeardAll) (F1 : Fork) (a : HeadOwn) (gk : OnBytes.Model.Forest.Heard)
      (mu : SumOnMatrix),
      given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s = .ok g ∧
      hear ((seatAt W.hS (readsOf W)).ledger s) rv = some (H, F1, []) ∧
      s.here = .head a ∧ a.lookHeard = some gk ∧ mergeClaimAt W s' = some mu ∧
      mu.value.var = OnBytes.Model.Aff.slot (heardOf gk H).sV ∧
      ∀ (cov : OnBytes.Model.Head.Covered) (t : OnBytes.Model.Head.Tables)
        {sh : OnBytes.Model.WsShape} (_ : OnBytes.Road.SizedW sh ppref)
        (_ : OnBytes.Model.wsLayOf sh true kRef = .ok W.layers.wsLay) (_ : W.H.lamS = 13)
        {claim : OnBytes.Model.WsClaim}
        (_ : First.Look.weightsClaim (runAt W cov (heardOf gk H) t) W.layers.wsLay = .ok claim),
        ∃ q sg, OnBytes.Model.Head.callNo W.HLy "HD0" = some q ∧
          (W.HLy.calls.getD q default).seg? "HD0" = some sg ∧
          ((∀ i, i < T → cov.hOn.getD i false = checked i) →
            LeftTies W g cov (heardOf gk H) t
              (First.K11Caller.ewAt (runAt W cov (heardOf gk H) t) q sg) →
            ∀ (Wm' : Wm K) (c : Cells), V = nV → d = nD →
              (∀ k v, k < d → v < V → ((c.Wh k v : Int) : K) = Hof Wm' k v) →
              claimVal Reading.gl W.layers.wsLay Wm' claim =
                rd (∑ v < V, ∑ k < d, mu.onVocabulary v * eq mu.onFeatures k *
                  ofInt (c.Wh k v))) := by
  obtain ⟨g, H, F1, a, gk, Q, hg, hh, ha, hgk, hs', _, _, _, hm, hv⟩ :=
    behind_all W l hd hWL hcan
  refine ⟨g, H, F1, a, gk, mergeClaimOf g H, hg, hh, ha, hgk, hm, hv,
    fun cov t sh Z hl hlam claim hk => ?_⟩
  obtain ⟨q, sg, hq, hsg, hcl, _⟩ := First.K11Caller.weightsClaim_head Z hl hk hlam
  refine ⟨q, sg, hq, hsg, fun hOn hL Wm' c hV hd' hWh => ?_⟩
  obtain ⟨l2, l3⟩ := hL
  have l1 := zt_size_at W hg hplan
  obtain ⟨hT, hV'⟩ := runAt_sizes W hg cov (heardOf gk H) t
  letI : Heard := H.2.2
  have hrH : (rH : Point).size = lt := rH_size hWL hh l1
  have hrs : (rs : Point).size = 13 := (rs_size hWL hh l1).trans (lPd_ref hd')
  rw [hcl]
  exact twin_sum (twinTies_heardOf gk H (runAt W cov (heardOf gk H) t) _ rfl hT hV' hOn hrH l2 l3)
    Z hl Wm' c hV hd' hrs hWh

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.hOn_of_covered
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.reads_as_Hof
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.weightTrue_of_says
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.weightTrue_iff_says
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.twinTies_heardOf
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.x_behind
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.behind_all
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.k6Out_iff
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.zt_size_at
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.twin_at
