--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyMarksThr.lean: WHERE A THREAD OVER THE KEY FILE's FIRST CHAIN STANDS AT THE BORDER 15, IN
FRONT OF THE TEST ON THE RANGES, TWO MARKS HOLD OF THE VERIFIER's STATE: no row of the statement
has a written-out factor (`stPlainB`), and the mark on the rows that lie open on the ranges' group
(`claimsAtB`). So of the three clauses of the named test on values at that sub-protocol (`vRng`,
E2E/KeyRangesReturns.lean) two are no debt of an honest side: where the guard on the shape returns,
`vRng` follows from its last clause alone. Steps of the verifier's: NOTHING IS SHOWN OF ANY PROVER.

How. The thread's own clause on how its state was made (`Thread.Made`,
Johnson/Desc/ProofFile/Honest/Thread/Thr.lean) holds the verifier's fold from the chain's first
state up to the border. The chain's flat list is cut at the ranges' test by the library's
`keyFirst_cut` (Johnson/Desc/K12/Law/SitsKeyChains.lean): what stands in front is `keyFirstPre`.
The chain's first state has no row at all. Each of the sub-protocols in front of "rng.0.rows" keeps
`PlainAll` from its own accept (E2E/KeyMarksKeeps.lean); the library's `foldBlocks_keeps`
(Johnson/Desc/FoldKeeps.lean) carries that along the fold; "rng.0.rows" gives the two marks
(`layRows_plain`, E2E/KeyMarksWalk.lean).

  `MarksAt`   the two marks at a state of the first chain.
  `plainAll_start`   `PlainAll` at the chain's first state.
  `pre_front_keeps`   each of the fourteen, as they stand in `keyFirstPre`.
  ★ `marks_of_pre`   a fold over `keyFirstPre` from a state with `PlainAll` ends in the two marks.
  ★★ `marks_of_thr`   at a thread. ONE PREMISE ON THE PLAN: `keyFirstPre` has fifteen members (that
      is: there are two lookups). The premises on the thread are those of `shape15_of_thr`
      (E2E/KeyRangesShape15.lean): its list is the first chain's flat list; its first state is the
      description's.
  `claims_of_gRng`, ★ `vRng_of_marks`   where the guard `gRng` returns at the state's shape, the
      two marks give `claimsB` at the structure that the seat makes (`claims_at_door`,
      Johnson/Desc/K12/Honest/Shape/TestMarksAtRanges.lean); so `vRng` from `valsK12`.
  ★★ `vRng_of_thr`   the two together, at a thread.

Limits. "Where the thread stands": nothing on whether it does. FORM ALONE: that a row holds of
anything is not touched. `valsK12` STAYS, AND IT IS EQUIVALENT TO THE SUB-PROTOCOL's OWN ACCEPT
(`k12_accept_iff_B`, Johnson/Desc/K12/Honest/Shape/TestValsB.lean, under `OneAsks`, which
`asks_of_guard`, TestSeatAsks.lean, gives from the guard, the three marks and the library's test on
the view): the algebra at that sub-protocol stays the honest side's whole debt. That fifteen
sub-protocols stand in front of the ranges' test is asked here, of no scope. That `gRng` returns at
a thread's state is asked here (in scope: `shape15_of_thr` with the run on shapes). The frame's own
word for the test on values at that number is not joined here. Nothing on completeness, on
soundness or on what a view shows.


-/
import E2E.KeyMarksKeeps
import E2E.EndsGive
import E2E.KeyRangesReturns
import Johnson.Desc.FoldKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.AtFiles
open OnBytes OnBytes.Params
open ProofFile.Honest
open VerifiableInference.Desc
open VerifiableInference.Desc.Keeps (Decides foldBlocks_keeps)
open VerifiableInference.Desc.Ground.Sh (stPlainB stTidyB claimsAtB)
open VerifiableInference.Desc.Key (FirstState LookupRecord chainStart firstChain lookupsOf
  lookupLink layRows sendIndexMasks sendOwnMessage pieces rangesParams)
open H2K.JointK (keyFirstPre keyFirst_cut)
open AtPublicFiles.KeyShape (Pub1)
open AtPublicFiles.KeyLookup (PlainAll idx_keeps msg_keeps link_member_keeps layRows_plain)
open ProofFile.Honest.Sh (claimsB valsK12 claims_at_door)

/-- The two marks at a state of the first chain. -/
def MarksAt (s : FirstState) : Prop :=
  stPlainB s.d.st = true ∧ claimsAtB s.d.st s.grp = true

/-- The chain's first state has no row. -/
theorem plainAll_start (codes : Codes) : PlainAll (chainStart codes ({} : LookupRecord)) :=
  ⟨rfl, fun _ hr => by cases hr⟩

/-- Each of the fourteen in front of "rng.0.rows", as they stand in `keyFirstPre`. -/
theorem pre_front_keeps (one : OneTime) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root)
    (set : Setting) (N : H2U.PlaceNums) {b : Block FirstState Key.Claim}
    (hb : b ∈ (firstChain one D told set N).first.asBare ::
      (firstChain one D told set N).front.map Block.asBare ++
      (firstChain one D told set N).links.flatMap Link.blocksInOrder) :
    Decides (fun a c => PlainAll a → PlainAll c) b := by
  intro s rs gs s' e hA
  rcases List.mem_append.1 hb with hb | hb
  · rcases List.mem_cons.1 hb with rfl | hb
    · exact idx_keeps (one := one) (N := pieces) e hA
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
      have hc' : c ∈ [sendOwnMessage (Cl := Key.Claim) one pieces
          (Key.groupsTold told (Key.rootsBefore D 2) (Key.rootsAt D 2))] := hc
      obtain rfl := List.mem_singleton.1 hc'
      exact msg_keeps (one := one) (N := pieces) e hA
  · obtain ⟨L, hL, hcL⟩ := List.mem_flatMap.1 hb
    have hL' : L ∈ (lookupsOf one).zipIdx.map fun x => lookupLink one set x.2 x.1 := hL
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hL'
    exact link_member_keeps one set x.2 x.1 hcL e hA

/-- ★ **A FOLD OVER WHAT STANDS IN FRONT OF THE RANGES' TEST ENDS IN THE TWO MARKS.** -/
theorem marks_of_pre (one : OneTime) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root)
    (set : Setting) (N : H2U.PlaceNums) (ft : ℕ) {s : FirstState} {rs : List Fmt.RoundView}
    {cols : List OpenedColumn} {r : FirstState × List Fmt.RoundView × List OpenedColumn}
    (h : foldBlocks ft (keyFirstPre one D told set N) s rs cols = .ok r) (hA : PlainAll s) :
    MarksAt r.1 := by
  unfold keyFirstPre at h
  obtain ⟨s1, rs1, c1, f1, f2⟩ := (foldBlocks_append_ok _ _ _ _ _ _).1 h
  have p1 : PlainAll s1 := foldBlocks_keeps (fun a c => PlainAll a → PlainAll c) (fun _ x => x)
    (fun _ _ _ x y z => y (x z)) ft _ (fun b hb => pre_front_keeps one D told set N hb) s rs cols
    _ f1 hA
  obtain ⟨-, s2, k2, st2, r2⟩ := foldBlocks_cons_ok.1 f2
  have e2 := (Block.step_ok.1 st2).2.2.1
  obtain rfl := Except.ok.inj r2
  exact layRows_plain (one := one) e2 p1

section Thread
variable {X : Key.Source} {N : H2U.PlaceNums} {P : Key.LaterPlaces}

/-- ★★ **WHERE A THREAD STANDS AT THE BORDER 15 THE TWO MARKS HOLD.** hlen: fifteen sub-protocols
stand in front of the ranges' test. -/
theorem marks_of_thr {V W Xh Pb : Type} {Bk : ProverCoinCounts}
    (hlen : (keyFirstPre X.Y.k.oneTime X.Y.D.1 X.Y.told.1 X.set N).length = 15)
    (T₁ : Thread Bk (keyFileDescription X N P).S₁ (keyFileDescription X N P).Cl V W Xh Pb)
    (hbs : T₁.bs = (keyFileDescription X N P).first.blocksInOrder)
    (hbeg : ∀ k w h s₀, T₁.valid w → T₁.begun k w h s₀ → ∃ x, s₀ = (keyFileDescription X N P).start₁ x)
    {k : Coins Bk} {e : (keyFileDescription X N P).S₁} {m : Mid W Xh} {E : Env} (h : Thr T₁ 15 k e m E) :
    MarksAt e := by
  obtain ⟨-, -, -, -, ⟨-, -, -, -, s₀, cols, hb0, -, hf⟩, -, hval⟩ := h
  obtain ⟨x, rfl⟩ := hbeg _ _ _ _ hval hb0
  have e15 : (keyFileDescription X N P).first.blocksInOrder.take 15 =
      keyFirstPre X.Y.k.oneTime X.Y.D.1 X.Y.told.1 X.set N :=
    (congrArg (List.take 15) (keyFirst_cut _ _ _ _ _)).trans (List.take_left' hlen)
  rw [hbs, e15] at hf
  exact marks_of_pre _ _ _ _ _ T₁.ft hf (plainAll_start _)

end Thread

section Guard
variable (Q : Pub1) (cs : Codes)

/-- Where the guard on the shape returns, the two marks give the front's named test on the open
rows, at the structure that the seat makes. -/
theorem claims_of_gRng (N : H2U.PlaceNums) {s : FirstState} {t : Sh₁B}
    (hg : gRng Q N (sh₁B Q cs s) = .ok t) (hM : MarksAt s) : claimsB (rangesState s) = true := by
  unfold gRng at hg
  split at hg
  · rename_i hm
    rw [Bool.and_eq_true] at hm
    split at hg
    · rename_i hm2
      rw [Bool.and_eq_true] at hm2
      have hT : stTidyB s.d.st = true := hm2.1
      exact claims_at_door (p := rangesParams N) (t := rangesState s) rfl hm.2 hT hM.1 hM.2
    · cases hg
  · cases hg

/-- ★ **THE NAMED TEST ON VALUES AT THE RANGES' TEST, FROM ITS LAST CLAUSE ALONE.** -/
theorem vRng_of_marks (N : H2U.PlaceNums) {s : FirstState} {t : Sh₁B}
    (hg : gRng Q N (sh₁B Q cs s) = .ok t) (hM : MarksAt s) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64)))
    (hv : valsK12 (rangesParams N) (rangesState s) rs gs = true) : vRng N s rs gs = true := by
  show (claimsB (rangesState s) && stPlainB s.d.st &&
    valsK12 (rangesParams N) (rangesState s) rs gs) = true
  rw [claims_of_gRng Q cs N hg hM, hM.1, hv]
  rfl

variable {X : Key.Source} {N : H2U.PlaceNums} {P : Key.LaterPlaces}

/-- ★★ **AT A THREAD AT THE BORDER 15.** -/
theorem vRng_of_thr {V W Xh Pb : Type} {Bk : ProverCoinCounts}
    (hlen : (keyFirstPre X.Y.k.oneTime X.Y.D.1 X.Y.told.1 X.set N).length = 15)
    (T₁ : Thread Bk (keyFileDescription X N P).S₁ (keyFileDescription X N P).Cl V W Xh Pb)
    (hbs : T₁.bs = (keyFileDescription X N P).first.blocksInOrder)
    (hbeg : ∀ k w h s₀, T₁.valid w → T₁.begun k w h s₀ → ∃ x, s₀ = (keyFileDescription X N P).start₁ x)
    {k : Coins Bk} {e : (keyFileDescription X N P).S₁} {m : Mid W Xh} {E : Env} (h : Thr T₁ 15 k e m E)
    (N' : H2U.PlaceNums) {t : Sh₁B} (hg : gRng Q N' (sh₁B Q cs e) = .ok t) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64)))
    (hv : valsK12 (rangesParams N') (rangesState e) rs gs = true) : vRng N' e rs gs = true :=
  vRng_of_marks Q cs N' hg (marks_of_thr hlen T₁ hbs hbeg h) rs gs hv

end Guard

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.plainAll_start
#print axioms AtPublicFiles.AtFiles.pre_front_keeps
#print axioms AtPublicFiles.AtFiles.marks_of_pre
#print axioms AtPublicFiles.AtFiles.marks_of_thr
#print axioms AtPublicFiles.AtFiles.claims_of_gRng
#print axioms AtPublicFiles.AtFiles.vRng_of_marks
#print axioms AtPublicFiles.AtFiles.vRng_of_thr
