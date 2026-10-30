-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoHeadLook.lean.
The head sub-proof: its lookup's claims inside the one equation, by value.

Head.walk (OnBytes/Model/Head.lean) adds the head's claims in this order: the lookup's rows on mask
entries (Forest.objects); the sum of squares, the row ledger, the stream times the reciprocal; the
lookup's join (Head.claimJoin); the acceptance policy; the lookup's three claims on the planes
(Head.claimPlanes); then the smallness test's and the rest. Between them it records the equation's
constant under a name.

States:
  headMid1 R n1 n2 n3 n4, headMid2 R n5 n6: the head's own routines between Forest.objects and
    Head.claimJoin, and between Head.claimJoin and Head.claimPlanes; the names under which the
    constant is recorded are letters.
  headKFs R: the loop of Head.claimJoin that makes the calls' key forms. claimJoin_cut: a run of
    Head.claimJoin is a run of that loop from the same state and context, which turns neither, and
    then the join at the forms made is added as a claim.
  headTab R n: the first entry of the table with the name n, as a plain value. claimPlanes_cut: a
    run of Head.claimPlanes is a run of Forest.planeLins from the same state and context, at the
    three tables' first entries.
  head_look_total: there are lists A, B of claims and an array KF of key forms, all three functions
    of the arrays' numbers of columns alone and chosen BEFORE every state, context, field, reading,
    round and world, such that for five runs in a row (Forest.objects, headMid1, Head.claimJoin,
    headMid2, Head.claimPlanes, each from the state and context that the one before has left): what
    lies under the filled slots and the numbers of columns are kept (these also at the state from
    which Head.claimJoin runs); KF is what the loop has returned; and, if the lookup's record holds
    the flat function's end values (Fo.HeardIs), then in every later state, for every reading ν of
    the lookup's places and all entries of virtual rows that meet the law of the reads, the total
    has grown by: powSum of the flat function's rows; A; theta^(its place) times Fo.claimJoin at the
    values of KF; B; powSum of Fo.claimLeaves, Fo.claimBits and the counts' sum at the columns' sums
    of the lookup's cells.
Under, beside the five runs: the state Fb before Forest.objects has one coefficient for each slot
(Fb.LS.size = Fb.ns) and its slots' arrays at their sizes (Sized). For the equation also: the record
holds the end values with a state F0 than which Fb is later; the shape is lawful (FoNums.ok) and has
as many calls as NC (a clause of FoNums.ok, asked once more); tB0, tB1 and tP, at which the law of
the reads is asked, are the first entries that headTab finds under the names bH-bits-0, bH-bits-1
and bH-pin.
Limits: that a run of Head.walk holds these five runs in a row is not shown here
(OnBytes/Tie/Pv/Lookup/Ends/FoHeadLookTied.lean). A, B and KF are chosen behind R and the names:
they can hang on the record R;
that it holds nothing drawn with or after theta is the caller's to say. Which the members of A and B
are, and how many, is not said. The statements speak of runs that return (the head of
OnBytes/Tie/Pv/Lookup/Ends/FoFixed.lean).
Whether ν, the world's slots, or the entries of which the law of the reads speaks hang on theta is
not said.
Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed that a run returns, or that a key form reads the extension of the call's key
vector.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoFixedHead
import OnBytes.Tie.Pv.Lookup.Ends.FoAddsAttV
import OnBytes.Tie.Pv.Lookup.Ends.FoKeepsHead
import OnBytes.Tie.Pv.Lookup.Ends.FoStillH

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.PscRun OnBytes.Model.Head Cb.Fo

/-- The head's own routines between Forest.objects and Head.claimJoin. -/
def headMid1 (R : Head.Run) (n1 n2 n3 n4 : String) : SubM Unit := do
  Head.noteConstant n1
  Head.claimSquares R
  Head.noteConstant n2
  Head.claimLedger R
  Head.noteConstant n3
  Head.claimStream R
  Head.noteConstant n4

/-- The head's own routines between Head.claimJoin and Head.claimPlanes. -/
def headMid2 (R : Head.Run) (n5 n6 : String) : SubM Unit := do
  Head.noteConstant n5
  Head.claimPolicy R
  Head.noteConstant n6

macro_rules | `(tactic| fixed_rule) => `(tactic| with_reducible first
  | exact fixed_noteConstant _ | exact fixed_claimSquares _ | exact fixed_claimLedger _
  | exact fixed_claimStream _ | exact fixed_claimPolicy _)

theorem fixed_headMid1 (R : Head.Run) (n1 n2 n3 n4 : String) :
    Fixed (headMid1 R n1 n2 n3 n4) := by
  unfold headMid1
  fixed

theorem fixed_headMid2 (R : Head.Run) (n5 n6 : String) : Fixed (headMid2 R n5 n6) := by
  unfold headMid2
  fixed

theorem keeps_headMid1 (R : Head.Run) (n1 n2 n3 n4 : String) :
    Keeps (headMid1 R n1 n2 n3 n4) := by
  unfold headMid1
  keeps

theorem keeps_headMid2 (R : Head.Run) (n5 n6 : String) : Keeps (headMid2 R n5 n6) := by
  unfold headMid2
  keeps

/-- The loop of Head.claimJoin that makes the calls' key forms. -/
def headKFs (R : Head.Run) : SubM (Array Aff × Array ℕ) := do
  let mut KF : Array Aff := #[]
  let mut laid := Array.replicate R.x.g1.shape.NT 0
  for q in [0:R.L.calls.size] do
    let (v, l) ← Head.keyForm R q laid
    KF := KF.push v
    laid := l
  pure (KF, laid)

theorem fixed_headKFs (R : Head.Run) : Fixed (headKFs R) := by
  unfold headKFs
  fixed

theorem still_headKFs (R : Head.Run) : Still (headKFs R) := by
  unfold headKFs
  refine Still.bind (Still.forInR _ (fun q s => ?_) _ _) fun _ => Still.pure _
  exact Still.bind (still_keyForm R q _) fun _ => Still.bind (Still.pure _) fun _ => Still.pure _

/-- A run of Head.claimJoin, cut behind the loop that makes the key forms. -/
theorem claimJoin_cut (R : Head.Run) (F G : Fork) (c c' : Ctx)
    (h : Head.claimJoin R F c = .ok (((), G), c')) :
    ∃ (KF : Array Aff) (laid : Array ℕ), headKFs R F c = .ok (((KF, laid), F), c) ∧
      KF.size = R.x.g1.shape.calls.size ∧
      (F.paid R.x.g1.owedJoin).lin (joinForm R.x.g1 KF) = some G ∧ c' = c := by
  unfold Head.claimJoin at h
  dsimp only at h
  obtain ⟨⟨KF, laid⟩, F1, c1, h1, h⟩ := (bind_ok _ _ _ _ _).1 h
  have hk : headKFs R F c = .ok (((KF, laid), F1), c1) := by
    unfold headKFs
    dsimp only
    exact (bind_ok _ _ _ _ _).2 ⟨⟨KF, laid⟩, F1, c1, h1, rfl⟩
  obtain ⟨s1, s2⟩ := still_headKFs R F c _ hk
  have s1' : F1 = F := s1
  have s2' : c1 = c := s2
  rw [s1', s2'] at hk h
  dsimp only at h
  obtain ⟨_, F2, c2, h2, h⟩ := (bind_ok _ _ _ _ _).1 h
  unfold Forest.paddingLaid at h2
  obtain ⟨_, e2⟩ := (mustAs_ok _ _ _ _ _).1 h2
  have t1 : F2 = F := congrArg (fun x : (Unit × Fork) × Ctx => x.1.2) e2
  have t2 : c2 = c := congrArg (fun x : (Unit × Fork) × Ctx => x.2) e2
  rw [t1, t2] at h
  obtain ⟨jf, F3, c3, h3, h⟩ := (bind_ok _ _ _ _ _).1 h
  obtain ⟨k1, _, rfl, rfl, rfl⟩ := join_ok _ _ _ _ _ _ _ h3
  obtain ⟨l1, l2⟩ := (SubM.lin_run _ _ _ _ _).1 h
  exact ⟨KF, laid, hk, k1, l1, l2⟩

/-- The first entry of the table with the name n. -/
def headTab (R : Head.Run) (n : String) : Option ℕ :=
  (R.t.tab.find? fun e => e.1 == n).map (·.2.1)

theorem tabAt_run {R : Head.Run} {n : String} {F G : Fork} {c c' : Ctx} {t : ℕ}
    (h : Head.tabAt R n F c = .ok ((t, G), c')) : headTab R n = some t ∧ G = F ∧ c' = c := by
  obtain ⟨s1, s2⟩ := still_tabAt R n F c _ h
  refine ⟨?_, s1, s2⟩
  obtain ⟨v, _, hv⟩ := Fixed.getAs "internal-table" (headTab R n)
  unfold Head.tabAt at h
  obtain ⟨a', c1, h1, e⟩ := (lift_ok _ _ _ _).1 h
  have e1 : t = a' := congrArg (fun x : (ℕ × Fork) × Ctx => x.1.1) e
  rw [e1]
  unfold headTab
  revert h1
  cases (R.t.tab.find? fun e => e.1 == n).map (·.2.1) with
  | none => intro h1; cases h1
  | some b =>
    intro h1
    have e2 : (b, c) = (a', c1) := Except.ok.inj h1
    rw [(Prod.mk.inj e2).1]

/-- A run of Head.claimPlanes is a run of Forest.planeLins at the three tables' first entries. -/
theorem claimPlanes_cut (R : Head.Run) (F G : Fork) (c c' : Ctx)
    (h : Head.claimPlanes R F c = .ok (((), G), c')) :
    ∃ tB0 tB1 tP, headTab R "bH-bits-0" = some tB0 ∧ headTab R "bH-bits-1" = some tB1 ∧
      headTab R "bH-pin" = some tP ∧
      Forest.planeLins R.x.g1 R.h.lmbH (bitHead R tB0 tB1) (colHead R tP) F c =
        .ok (((), G), c') := by
  rw [claimPlanes_eq] at h
  obtain ⟨tB0, F1, c1, h1, k1⟩ := (bind_ok _ _ _ _ _).1 h
  obtain ⟨a1, e1, e1'⟩ := tabAt_run h1
  rw [e1, e1'] at k1
  obtain ⟨tB1, F2, c2, h2, k2⟩ := (bind_ok _ _ _ _ _).1 k1
  obtain ⟨a2, e2, e2'⟩ := tabAt_run h2
  rw [e2, e2'] at k2
  obtain ⟨tP, F3, c3, h3, k3⟩ := (bind_ok _ _ _ _ _).1 k2
  obtain ⟨a3, e3, e3'⟩ := tabAt_run h3
  rw [e3, e3'] at k3
  exact ⟨tB0, tB1, tP, a1, a2, a3, k3⟩

/-- The head sub-proof's lookup inside the one equation. -/
theorem head_look_total (R : Head.Run) (n1 n2 n3 n4 n5 n6 : String) :
    ∃ (A B : (ℕ → ℕ) → List Cl) (KF : (ℕ → ℕ) → Array Aff),
      ∀ (Fb F1 F2 F3 F4 G : Fork) (cb c1 c2 c3 c4 c' : Ctx),
        Forest.objects R.x.g1 Fb cb = .ok (((), F1), c1) →
        headMid1 R n1 n2 n3 n4 F1 c1 = .ok (((), F2), c2) →
        Head.claimJoin R F2 c2 = .ok (((), F3), c3) →
        headMid2 R n5 n6 F3 c3 = .ok (((), F4), c4) →
        Head.claimPlanes R F4 c4 = .ok (((), G), c') →
        Fb.LS.size = Fb.ns → Sized Fb →
        Later Fb G ∧ Sized G ∧ G.LS.size = G.ns ∧ colsOf G = colsOf Fb ∧ colsOf F2 = colsOf Fb ∧
        (∃ laid, headKFs R F2 c2 = .ok (((KF (colsOf Fb), laid), F2), c2)) ∧
        (KF (colsOf Fb)).size = R.x.g1.shape.calls.size ∧
        ∀ (K : Type) [CommRing K] (ρ : Reading K) (F0 : Fork) (jLK : ℕ) (rsK : Rounds K),
          HeardIs ρ R.x.g1 F0 (endsOf R.x.g1.shape R.h.lmbH jLK rsK) → Later F0 Fb →
          FoNums.ok R.x.g1.shape = true → R.x.g1.shape.calls.size = R.x.g1.shape.NC →
          ∀ tB0 tB1 tP, headTab R "bH-bits-0" = some tB0 → headTab R "bH-bits-1" = some tB1 →
            headTab R "bH-pin" = some tP →
          ∀ (H : Fork), Later G H → ∀ (ν : Pl → K) (entry : ℕ → ℕ → ℕ → K),
            ReadsLaw R.x.g1.shape R.h.lmbH (endsOf R.x.g1.shape R.h.lmbH jLK rsK).zb0
              (endsOf R.x.g1.shape R.h.lmbH jLK rsK).zb1 ν entry R.iU3 (colsOf Fb R.iU3) tB0 tB1
              tP →
            G.total ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) =
              Fb.total ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) +
                powSum (ρ.val Fb.theta) Fb.nClaim
                  ((endsOf R.x.g1.shape R.h.lmbH jLK rsK).rows.map (rowRes ν)) +
                clsValue ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) (ρ.val Fb.theta)
                  (Fb.nClaim + R.x.g1.rows.size) (A (colsOf Fb)) +
                ρ.val Fb.theta ^ (Fb.nClaim + R.x.g1.rows.size + (A (colsOf Fb)).length) *
                  claimJoin R.x.g1.shape R.h.lmbH jLK rsK ν
                    (fun q => ((KF (colsOf Fb)).getD q (Aff.ofConst zeroE)).value ρ
                      (H.worldOf ρ (fun j => ν (.mask j)) entry)) +
                clsValue ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) (ρ.val Fb.theta)
                  (Fb.nClaim + R.x.g1.rows.size + (A (colsOf Fb)).length + 1) (B (colsOf Fb)) +
                powSum (ρ.val Fb.theta)
                  (Fb.nClaim + R.x.g1.rows.size + (A (colsOf Fb)).length + 1 +
                    (B (colsOf Fb)).length)
                  [claimLeaves R.x.g1.shape R.h.lmbH jLK rsK ν
                      (colsK R.x.g1.shape R.h.lmbH (endsOf R.x.g1.shape R.h.lmbH jLK rsK).zb0 ν),
                    claimBits R.x.g1.shape R.h.lmbH jLK rsK ν
                      (colsK R.x.g1.shape R.h.lmbH (endsOf R.x.g1.shape R.h.lmbH jLK rsK).zb1 ν),
                    Pin.countK R.x.g1.shape R.h.lmbH (Pin.pinColK R.h.lmbH ν)] := by
  obtain ⟨_, _, Ho⟩ := fixed_objects R.x.g1
  obtain ⟨_, A, HA⟩ := fixed_headMid1 R n1 n2 n3 n4
  obtain ⟨vK, _, HK⟩ := fixed_headKFs R
  obtain ⟨_, _, HJ⟩ := fixed_claimJoin R
  obtain ⟨_, B, HB⟩ := fixed_headMid2 R n5 n6
  obtain ⟨_, _, HP⟩ := fixed_claimPlanes R
  refine ⟨A, B, fun k => ((vK k).map fun x => x.1).getD #[],
    fun Fb F1 F2 F3 F4 G cb c1 c2 c3 c4 c' r0 r1 r2 r3 r4 hs hF => ?_⟩
  -- the five stretches
  have a0 := objects_added r0 hs
  have k0 := (Ho _ _ _ _ _ r0 hs).2.2
  obtain ⟨m0, z0⟩ := Keeps.objects _ _ _ _ _ _ r0 hF
  obtain ⟨_, a1, k1⟩ := HA _ _ _ _ _ r1 a0.sized
  obtain ⟨m1, z1⟩ := keeps_headMid1 R n1 n2 n3 n4 _ _ _ _ _ r1 z0
  obtain ⟨KF, laid, j1, j2, j3, j4⟩ := claimJoin_cut R F2 F3 c2 c3 r2
  have k2 := (HJ _ _ _ _ _ r2 a1.sized).2.2
  obtain ⟨m2, z2⟩ := keeps_Model_Head_claimJoin R _ _ _ _ _ r2 z1
  have a2 : Added F2 F3 [(joinForm R.x.g1 KF, #[])] := by
    have := (added_paid a1.sized R.x.g1.owedJoin).trans
      (added_lin (added_paid a1.sized R.x.g1.owedJoin).sized j3)
    rwa [List.nil_append] at this
  obtain ⟨_, a3, k3⟩ := HB _ _ _ _ _ r3 a2.sized
  obtain ⟨m3, z3⟩ := keeps_headMid2 R n5 n6 _ _ _ _ _ r3 z2
  have k4 := (HP _ _ _ _ _ r4 a3.sized).2.2
  obtain ⟨m4, z4⟩ := keeps_Model_Head_claimPlanes R _ _ _ _ _ r4 z3
  have q1 : colsOf F1 = colsOf Fb := k0
  have q2 : colsOf F2 = colsOf Fb := k1.trans q1
  have q3 : colsOf F3 = colsOf Fb := k2.trans q2
  have q4 : colsOf F4 = colsOf Fb := k3.trans q3
  rw [q1] at a1
  rw [q3] at a3
  have hv : vK (colsOf Fb) = some (KF, laid) := by
    rw [← q2]
    exact (HK _ _ _ _ _ j1 a1.sized).1
  have hKF : ((vK (colsOf Fb)).map fun x => x.1).getD #[] = KF := by rw [hv]; rfl
  simp only [hKF]
  obtain ⟨tB0', tB1', tP', u0, u1, u2, r4'⟩ := claimPlanes_cut R F4 G c4 c' r4
  have pre := ((a0.trans a1).trans a2).trans a3
  have aP := (HP _ _ _ _ _ r4 a3.sized).2.1
  have lp : Later Fb F4 := ((m0.trans m1).trans m2).trans m3
  refine ⟨lp.trans m4, z4, aP.sized, k4.trans q4, q2, ⟨laid, j1⟩, j2,
    fun K _ ρ F0 jLK rsK hI h0 hok hNC tB0 tB1 tP t0 t1 t2 H hH ν entry Lw => ?_⟩
  obtain rfl : tB0' = tB0 := Option.some.inj (u0.symm.trans t0)
  obtain rfl : tB1' = tB1 := Option.some.inj (u1.symm.trans t1)
  obtain rfl : tP' = tP := Option.some.inj (u2.symm.trans t2)
  have Rd := readsAt_head R tB0' tB1' tP' F4 c4
  rw [congrFun q4 R.iU3] at Rd
  obtain ⟨_, _, _, hg⟩ := planeLins_reads ρ R.x.g1 R.h.lmbH jLK rsK (bitHead R tB0' tB1')
    (colHead R tP') F0 F4 G c4 c' Rd r4' hI (h0.trans lp) hok pre.sized z3
  obtain ⟨e4, _, _⟩ := hg H hH ν entry Lw
  have lH : Later F0 H := ((h0.trans lp).trans m4).trans hH
  have eR := PlaneClaims.rows_claim ρ R.x.g1 R.h.lmbH jLK rsK F0 hI H lH ν entry
  have eJ := joinForm_claim ρ R.x.g1 R.h.lmbH jLK rsK F0 hI hok KF (j2.trans hNC) H lH ν entry
  rw [e4, pre.total, pre.theta, pre.nClaim]
  simp only [clsValue_append, clsValue_forms, claimsValue_powSum, List.length_append,
    List.length_map, Array.length_toList, List.length_cons, List.length_nil]
  rw [eR]
  have e1 : clsValue ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) (ρ.val Fb.theta)
      (Fb.nClaim + (R.x.g1.rows.size + (A (colsOf Fb)).length)) [(joinForm R.x.g1 KF, #[])] =
      ρ.val Fb.theta ^ (Fb.nClaim + R.x.g1.rows.size + (A (colsOf Fb)).length) *
        (joinForm R.x.g1 KF).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) := by
    simp [clsValue, sumFrom, value_form, Nat.add_assoc]
  rw [e1, eJ]
  simp only [Nat.add_assoc, Nat.zero_add]
  ring

end Fo
