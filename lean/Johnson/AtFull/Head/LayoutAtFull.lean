-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Head/LayoutAtFull.lean: the layout of the output head's sub-proof returns at the full
size's written numbers: Head.layout (headShape P y) y.tauFC = .ok HLy, at P := the written value of
the parameter file's scan at the stored free numbers; and headReads HLy = headReadsW, the nineteen
numbers that the head's plan reads (PlanReads.lean | PlanAtFull.lean beside). This is the premise
p13 of the ledger of publicOfO (publicOfO_of_parts), to its letter; with it the premise
hL of planH2_returns is paid. Two closed facts by Lean's kernel, general laws, and the join. No
sub-protocol imports this file.
  tauFEw · clW · csW   the table of exponentials, the lookup's entries, the bits of a column's
                    number inside a tree: at the full size's letters
  withFs f          a test at the head's numbers, its six calls and the numbers of its lookup, made
                    without the tests on the calls' tables (the twin shapeNoAsk) ·
                    withFs_true: what its accept gives
  bigTest           all that is asked of the kernel: numbers and short lists. THE KERNEL NEVER SEES
                    A TABLE OF 65,536 WORDS NOR AN ARRAY OF COLUMNS (up to 262,144 entries a call)
  allW              BY THE KERNEL: withFs bigTest = true · ask_can_fail: a negative test
  LaidW x           what returns, part by part: the numbers, the calls, the lookup's shape, the
                    planes' columns and the counts, each by its own return; the value written out
  layout_at         the join, at the closed letters hFull | tauFCw: LaidW of the layout's return
  LaidW.reads       what returns has the nineteen
  layout_whole      LaidW at y's letters: FOR WHOEVER STANDS BEHIND publicOfO AND READS MORE OF HLy
                    THAN THE NINETEEN (its calls for the digest, its entries, its counts)
  layout_returns    THE ROW, to p13's letter, under two small equations on y
  plan_of_layout    so Head.layout AND Head.planH2 return (p13 and p19), the second under what is
                    read of the owner alone
Premises of layout_returns. h1 : y.lPd = 13 · hT : y.tauFC = tauFCw (tauFC_of_base |
tauFC_of_layout, Johnson/Road/HeadTabs.lean, have it from the layers' layout's return). That the
ledger's letter P is PW is its p1's to say (polLayout at the stored parameter file).
How. admitted · policy · numbers · callsOf · callSizes · the depth · planeCols · the loop on iotaH ·
the absent calls · h9: closed facts. The table FE's size: fe_ok. Forest.shape: shape_eq | ask_eq
with rec_ok. pubOf: pubOf_eq (at the full size no segment has an entry behind the vocabulary).
pubAsk: pubAsk_of under pub_le's bound; which tree of a call holds a taken column is not known, so
the kernel is asked at all choices.
Called, not typed: shapeNoAsk | callAskNoTab (ForestTwins.lean) · shape_eq | ask_eq (ShapeEq.lean) ·
askB | pubAsk_of (PubAsk.lean) · place_used (Used.lean): law files under
Johnson/Unfolds/ · callsOf_kind (Johnson/Road/HeadCallsLaid.lean) · place_segs
(Johnson/Road/FormsKeysLaid.lean) · shape_at_stored (Johnson/Goal/Meaning/HeadAtFullIs.lean) ·
needed_ok (OnBytes/Flat/CoveredJoin.lean).
Limits. The full size, at the stored free numbers alone. The counts of padding keys are bounded, not
given. No soundness is claimed. On hiding nothing.
-/
import Johnson.AtFull.Head.PlanAtFull
import Johnson.AtFull.Head.PubOfLaw
import Johnson.AtFull.Head.TablesOk
import Johnson.Unfolds.ShapeEq
import Johnson.Unfolds.PubAsk
import Johnson.Unfolds.Used
import Johnson.Road.HeadCallsLaid
import OnBytes.Flat.CoveredJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtFull.Head
open OnBytes OnBytes.Model OnBytes.Model.Head
open OnBytes.Model.Verify (headShape borderOf)
open OnBytes.Road.Hd (tauFCw)
open Johnson.Unfolds (shape_eq ask_eq)
open Johnson.Unfolds (askB pubAsk_of)
open Johnson.Unfolds (place_used)
open VerifiableInference.Desc.Kinds.Head.Law (Cond.hFull Cond.bFull)
open VerifiableInference.Desc.Kinds.Head.Law.InScope (shape_at_stored)

/-- The head's table of exponentials at the full size's three numbers. -/
abbrev tauFEw : Array F := tauFEOf Cond.hFull.famF Cond.hFull.digSh Cond.hFull.tabS

/-- The entries of the head's lookup. -/
abbrev clW (calls : List CallD) : Array Call := lookups Cond.hFull tauFCw tauFEw calls

/-- A test at the head's numbers, calls and lookup. -/
def withFs (f : HL → List CallD → Forest.Shape → Bool) : Bool :=
  match numbers Cond.hFull with
  | .ok L => (match callsOf Cond.hFull L with
    | .ok calls => (match Forest.shapeNoAsk (clW calls) Cond.hFull.LIDB with
      | .ok fs => f L calls fs
      | .error _ => false)
    | .error _ => false)
  | .error _ => false

theorem withFs_true {f : HL → List CallD → Forest.Shape → Bool} (h : withFs f = true) :
    ∃ L calls fs, numbers Cond.hFull = .ok L ∧ callsOf Cond.hFull L = .ok calls ∧
      Forest.shapeNoAsk (clW calls) Cond.hFull.LIDB = .ok fs ∧ f L calls fs = true := by
  unfold withFs at h
  split at h
  · rename_i L hL
    split at h
    · rename_i calls hc
      split at h
      · rename_i fs hf
        exact ⟨L, calls, fs, hL, hc, hf, h⟩
      · cases h
    · cases h
  · cases h

/-- The bits of a column's number inside a tree. -/
abbrev csW (fs : Forest.Shape) : Nat := fs.dT - Cond.hFull.lt

/-- All that is asked of the kernel. -/
def bigTest (L : HL) (calls : List CallD) (fs : Forest.Shape) : Bool :=
  admitted Cond.hFull && (policy Cond.hFull).toOption.isSome &&
  (callSizes Cond.hFull calls).toOption.isSome &&
  ((clW calls).toList.all fun c => (Forest.callAskNoTab c).toOption.isSome) &&
  decide (Cond.hFull.la ≤ fs.dT) &&
  ((List.range calls.length).all fun q => Cond.hFull.iotaH.getD q 0 == fs.iota.getD q 0) &&
  ((Cond.hFull.iotaH.drop calls.length).all (· == 0)) &&
  (h9 Cond.hFull L Head.cellBound).toOption.isSome &&
  (calls.zipIdx.all fun x =>
    (x.1.J / 2 ^ csW fs == 2 ^ fs.iota.getD x.2 0) &&
    (x.1.segs.all fun g => !perEntry g.name || g.n - (Cond.hFull.V - firstEntry L g.name) == 0) &&
    decide (x.1.J ≤ 2 ^ csW fs * 2 ^ fs.iota.getD x.2 0) &&
    x.1.segs.any fun s => decide (0 < s.n) && decide (s.n < 2 ^ (topBit + 1))) &&
  ((choices (calls.zipIdx.map fun x => 2 ^ fs.iota.getD x.2 0)).all fun ts =>
    askB fs (vH Cond.hFull.T (csW fs) fs 0 ts)) &&
  (fs.NC == calls.length) &&
  (match Forest.planeCols fs Cond.hFull.lmbH with
    | .ok kb => decide ([calls.length, calls.length, fs.NT, fs.NT, fs.dT, fs.rK, fs.kT, fs.cK,
        fs.NC, kb, L.m, L.k, L.mD, L.kD, L.mR, L.kR, L.filled, L.fillD, L.fillR] = headReadsW)
    | .error _ => false)

/-- **By the kernel.** -/
theorem allW : withFs bigTest = true := by decide +kernel

/-- A negative test: at the bound «a whole tree's keys at every tree» the tests on the counts
reject (a call of padding alone): so the column that is taken is needed. (withFs is false also
where numbers, callsOf or shapeNoAsk refuse: that they return is allW's.) -/
theorem ask_can_fail : withFs (fun _ _ fs =>
    askB fs fun θ => if θ < fs.NT then 2 ^ csW fs * Cond.hFull.T else 0) = false := by
  decide +kernel

theorem ok_unit {x : Except String PUnit} (h : x.toOption.isSome = true) : x = .ok () := by
  cases x with
  | error e => cases h
  | ok a => rfl

theorem bind_ok {α β : Type} {x : Except String α} {a : α} (h : x = .ok a)
    (f : α → Except String β) : (x >>= f) = f a := by
  rw [h]
  rfl

theorem fst_mem {α : Type} : ∀ (l : List α) (k : Nat) (x : α × Nat), x ∈ l.zipIdx k → x.1 ∈ l
  | [], _, _, h => absurd h (by simp)
  | a :: l, k, x, h => by
    rw [List.zipIdx_cons] at h
    rcases List.mem_cons.1 h with e | h'
    · subst e
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (fst_mem l (k + 1) x h')

/-- What returns, part by part: x is the layout's return. -/
def LaidW (x : Except String HL) : Prop :=
  ∃ (L : HL) (calls : List CallD) (fs : Forest.Shape) (kb : Nat) (pub : Array Nat),
    numbers Cond.hFull = .ok L ∧ callsOf Cond.hFull L = .ok calls ∧
    Forest.shape (clW calls) Cond.hFull.LIDB = .ok fs ∧
    Forest.planeCols fs Cond.hFull.lmbH = .ok kb ∧ pubOf Cond.hFull L fs calls = .ok pub ∧
    pub.size = fs.NT ∧
    [calls.length, calls.length, fs.NT, fs.NT, fs.dT, fs.rK, fs.kT, fs.cK, fs.NC, kb, L.m, L.k,
      L.mD, L.kD, L.mR, L.kR, L.filled, L.fillD, L.fillR] = headReadsW ∧
    x = .ok { L with
      kb := kb, calls := calls.toArray,
      cl := (clW calls).mapIdx fun q c => { c with iota := fs.iota.getD q 0 },
      fs := { fs with
        calls := (clW calls).mapIdx fun q c => { c with iota := fs.iota.getD q 0 },
        pub := pub } }

/-- **The head's layout returns at the closed letters**, and what it returns. -/
theorem layout_at : LaidW (layout Cond.hFull tauFCw) := by
  obtain ⟨L, calls, fs, hL, hc, hfs, hT⟩ := withFs_true allW
  unfold bigTest at hT
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at hT
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨t1, t2⟩, t3⟩, t4⟩, t5⟩, t6⟩, t7⟩, t8⟩, t9⟩, t10⟩, t11⟩, t12⟩ := hT
  -- the planes' columns and the nineteen
  obtain ⟨kb, hkb, h19⟩ : ∃ kb, Forest.planeCols fs Cond.hFull.lmbH = .ok kb ∧
      [calls.length, calls.length, fs.NT, fs.NT, fs.dT, fs.rK, fs.kT, fs.cK, fs.NC, kb, L.m, L.k,
        L.mD, L.kD, L.mR, L.kR, L.filled, L.fillD, L.fillR] = headReadsW := by
    cases e : Forest.planeCols fs Cond.hFull.lmbH with
    | error s => rw [e] at t12; cases t12
    | ok kb => rw [e] at t12; exact ⟨kb, rfl, of_decide_eq_true t12⟩
  -- the lookup's shape
  have asks : ∀ c ∈ (clW calls).toList, Forest.callAsk c = .ok () := by
    intro c hcm
    have r := rec_ok Cond.hFull tauFCw tauFEw calls fc_ok fe_ok hcm
    rw [ask_eq c r.1 r.2]
    exact ok_unit (t4 c hcm)
  have f2 : Forest.shape (clW calls) Cond.hFull.LIDB = .ok fs := (shape_eq _ _ asks).trans hfs
  -- the counts
  have H1 : ∀ x ∈ calls.zipIdx,
      (x.1.J / 2 ^ (fs.dT - Cond.hFull.lt) == 2 ^ fs.iota.getD x.2 0) = true := fun x hx =>
    beq_iff_eq.2 (t9 x hx).1.1.1
  have H2 : ∀ x ∈ calls.zipIdx, ∀ g ∈ x.1.segs, perEntry g.name = true →
      g.n - (Cond.hFull.V - firstEntry L g.name) = 0 := by
    intro x hx g hg hp
    have k := (t9 x hx).1.1.2 g hg
    rw [hp] at k
    simpa using k
  have hpub := pubOf_eq Cond.hFull L fs calls H1 H2
  have hall : ∀ x ∈ calls.zipIdx, x.1.J ≤ 2 ^ csW fs * 2 ^ fs.iota.getD x.2 0 ∧
      ∃ p, p < x.1.J ∧ (x.1.used.getD p 0 == 0) = false := by
    intro x hx
    refine ⟨(t9 x hx).1.2, ?_⟩
    obtain ⟨s, hs, k2⟩ := List.any_eq_true.1 (t9 x hx).2
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at k2
    obtain ⟨name, kind, asks', fl, e, -⟩ :=
      OnBytes.Road.Hd.callsOf_kind hc x.1 (fst_mem _ _ _ hx)
    rw [e] at hs ⊢
    obtain ⟨a, ha, _, e2, _⟩ := OnBytes.Road.place_segs _ _ _ _ s hs
    obtain ⟨p, hp, hpad⟩ := place_used name kind asks' fl
      ⟨a, ha, by rw [← e2]; exact k2.1, by rw [← e2]; exact k2.2⟩
    refine ⟨p, hp, ?_⟩
    unfold CallD.padding at hpad
    exact (Bool.or_eq_false_iff.1 hpad).1
  obtain ⟨ps, ts, hts, hb⟩ := pub_le Cond.hFull.T (csW fs) fs calls hall
  generalize hP : calls.zipIdx.foldl
    (fun pub x => addCols Cond.hFull.T (fs.dT - Cond.hFull.lt) (fs.first.getD x.2 0) x.1 pub)
    (Array.replicate fs.NT 0) = pub at hpub ps hb
  have hsz : ((clW calls).mapIdx fun q c => { c with iota := fs.iota.getD q 0 }).size = fs.NC := by
    rw [Array.size_mapIdx, t11]
    simp [lookups]
  have f7 : Forest.pubAsk { fs with
      calls := (clW calls).mapIdx fun q c => { c with iota := fs.iota.getD q 0 },
      pub := pub } pub = .ok () :=
    pubAsk_of _ pub (vH Cond.hFull.T (csW fs) fs 0 ts) ps hsz hb (t10 ts hts)
  -- the loop on iotaH
  have f5 : (forIn (List.range calls.length) PUnit.unit fun (q : Nat) (_ : PUnit) => (do
      needed (Cond.hFull.iotaH.getD q 0 == fs.iota.getD q 0) "shape-call-H"
      pure (ForInStep.yield PUnit.unit) : Except String (ForInStep PUnit))) = .ok PUnit.unit := by
    refine (forIn_ok _ (fun _ _ => PUnit.unit) _ _ fun q hq b => ?_).trans rfl
    rw [OnBytes.Flat.needed_ok (beq_iff_eq.2 (t6 q hq))]
    rfl
  have fe' : ((tauFEOf Cond.hFull.famF Cond.hFull.digSh Cond.hFull.tabS).size == 65536) = true :=
    beq_iff_eq.2 fe_ok.1
  refine ⟨L, calls, fs, kb, pub, hL, hc, f2, hkb, hpub, ps, h19, ?_⟩
  unfold layout
  rw [bind_ok (OnBytes.Flat.needed_ok t1), bind_ok (ok_unit t2), bind_ok hL, bind_ok hc]
  dsimp only
  rw [bind_ok (OnBytes.Flat.needed_ok fe'), bind_ok (ok_unit t3), bind_ok f2,
    bind_ok (OnBytes.Flat.needed_ok (decide_eq_true t5)), bind_ok hkb, bind_ok f5, bind_ok hpub,
    bind_ok f7,
    bind_ok (OnBytes.Flat.needed_ok (List.all_eq_true.2 fun x hx => beq_iff_eq.2 (t7 x hx))),
    bind_ok (ok_unit t8)]
  rfl

/-- What returns has the nineteen. -/
theorem LaidW.reads {x : Except String HL} (h : LaidW x) :
    ∃ HLy, x = .ok HLy ∧ headReads HLy = headReadsW := by
  obtain ⟨L, calls, fs, kb, pub, -, -, -, -, -, ps, h19, h⟩ := h
  refine ⟨_, h, ?_⟩
  rw [← h19]
  unfold headReads
  simp [ps, lookups]

/-- The whole of what returns, at y's letters: for whoever reads the calls, the entries or the
counts of what publicOfO lays as HLy. -/
theorem layout_whole {y : Layer.Lay} (h1 : y.lPd = 13) (hT : y.tauFC = tauFCw) :
    LaidW (Head.layout (headShape PW y) y.tauFC) := by
  rw [shape_at_stored, h1, hT]
  exact layout_at

/-- **THE HEAD's LAYOUT RETURNS**: the premise p13 of the ledger of publicOfO, to its letter. -/
theorem layout_returns {y : Layer.Lay} (h1 : y.lPd = 13) (hT : y.tauFC = tauFCw) :
    ∃ HLy, Head.layout (headShape PW y) y.tauFC = .ok HLy ∧ headReads HLy = headReadsW :=
  (layout_whole h1 hT).reads

/-- **So the layout and the plan return**: p13 and p19. -/
theorem plan_of_layout {y : Layer.Lay} {owner : Owner} (h1 : y.lPd = 13)
    (hT : y.tauFC = tauFCw) (h2 : borderOf y = Cond.bFull) (h3 : y.NGr = 12)
    (hO : ownerReads owner = ownerW.reads) :
    ∃ HLy, Head.layout (headShape PW y) y.tauFC = .ok HLy ∧
      Head.planH2 PW.settings (headShape PW y) HLy (borderOf y) owner y.NGr PW.lkW = .ok HW := by
  obtain ⟨HLy, a, b⟩ := layout_returns h1 hT
  exact ⟨HLy, a, planH2_returns h1 h2 h3 b hO⟩

end AtFull.Head

#print axioms AtFull.Head.allW
#print axioms AtFull.Head.ask_can_fail
#print axioms AtFull.Head.layout_at
#print axioms AtFull.Head.LaidW.reads
#print axioms AtFull.Head.layout_whole
#print axioms AtFull.Head.layout_returns
#print axioms AtFull.Head.plan_of_layout
#print axioms AtFull.Head.withFs_true
#print axioms AtFull.Head.ok_unit
#print axioms AtFull.Head.bind_ok
#print axioms AtFull.Head.fst_mem
