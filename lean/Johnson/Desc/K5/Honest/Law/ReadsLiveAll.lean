-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/ReadsLiveAll.lean: CONDITIONAL: AT AN ATTENTION SEGMENT: ON EVERY ONE OF
THE SEGMENT's NAs + 4 MATRICES THE STATE's LIST HOLDS A TABLE IN VECTOR NUMBER 2, OF A LENGTH THAT
IS NOT 0 AND DIVIDES THE NUMBER OF ROWS OF THE PLAN's MATRIX, NO ENTRY OF WHOSE WEIGHTS BELOW THAT
LENGTH READS 0: behind the quiet step that closes the list, and in front of the batching. Under a
test with code on what the segment's own rounds drew, and a condition on the points that the lookup
on the calls left. On the verifier's own functions and state; no prover in it.

Why. Johnson/Desc/K5/Honest/Law/LiveValAt.lean and LiveToBatch.lean show it on the matrices NAs and
NAs + 3, under a test on what the segment's own rounds heard. A count that asks it of every matrix
wants the others too.

The three tables, in the library's written list (`K5Law.laidBy`,
Johnson/Desc/First/Att/Claims/ReadsOfIs.lean):
  on q < NAs: `lastN` of the lookup's point zx: by its definition the table of equality weights of
    the last lmS coordinates;
  on NAs + 1: `blockRows` of `eqTab` of the last ls coordinates of zcW, and of `eqTab` of ziW: two
    cuts of the point that the lookup on the calls left for the call that holds the list of keys
    "the low 16 bits of the division's two remainders" (`Keys.wl`, Johnson/Desc/First/Att/Geo.lean);
  on NAs + 2: the weights 2 ^ (r % 32) under which the counts are summed: public numbers.

Main names:
  `Fine`, `LeftFine`: **what is asked of what the lookup on the calls left**, at values: zx has lmS
    coordinates at least, and no coordinate of the three cuts reads 0 or 1.
  `leftReads`, `leftFine_of_reads`: the same as a test with code on the words (`nz01`,
    Johnson/Desc/K5/Honest/Law/EqTabNz.lean), which gives it.
  `cuts_are`: the two cuts zcW and ziW are cuts of the key point of one call; they hang on the
    geometry and on zk alone.
  `RawFine`, `leftFine_of_raw`: **from the raw points**: zx, and that one call's key point.
  `leftFine_of_zx`: **from zx alone**, where that key point ends in zx.
  `phiP_live`: no weight of the third table reads 0. No premise, no test.
  `left_live`: no entry of the first two reads 0.
  `LiveAllV`: **the end.**
  `funs_liveAll`: **behind a yes of the quiet step.**
  `liveAll_read`: the end hangs on the reading (closed, list) alone.
  `mats_at_head`: **under the head the plan's list has just NAs + 4 matrices**, so that the end
    speaks of every matrix of that list and of no number beyond it.
  `liveAll_behind_reads`, `liveAll_at_batch`: **under the head, to the state in front of the
    batching.**

Not on the road to the end, and offered to a caller: `leftReads` with `leftFine_of_reads`, and
`leftFine_of_zx`.

What it widens. `liveAll_at_batch` has the premises of `live_at_batch` (LiveToBatch.lean) and one
more, hL; its end is that of `Live2V` (LiveValAt.lean), at every matrix for two.

Limits. THE POINTS OF `RawFine` ARE NO CHALLENGES OF THE SEGMENT's OWN ROUNDS: they come of the
rounds of the lookup on the calls; the tests and marks on the segment's own rounds say nothing of
them. How often `RawFine` fails is not shown, nor that it holds at any run. It is sufficient, not
necessary. hL speaks of the field g of the segment that stands open at s4: that this is what the
state's function `lookHeard?` answers there, or at the state in front of the batching, is not shown
here. Else as LiveValAt.lean's and LiveToBatch.lean's: THE MATRIX IS THE PLAN's (a.mats), NOT THE
STATE's (tl.mats): that the two lists are one at that state is not shown; the head is a hypothesis;
at the function `OnBytes.secondHashFunction`; at the library's full size alone. Through its imports the file
stands above the files under ThirdParty/ (lean/LIMITS.md, L15).
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.ReadsLaidAt
import Johnson.Desc.K5.Honest.Law.LiveToBatch
import Johnson.Desc.K5.Honest.Law.Live
import Johnson.Desc.First.Att.Claims.KeysTabs

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Att (readsAtSO)
open VerifiableInference.Desc.First.Att.P (Geo Heard Pts hear behind)
open K5Law (Table laidBy)
open P5J (AtMgA TS)
open H2K5.Door

/-- An element that reads neither 0 nor 1. -/
def Fine (w : E) : Prop := Reading.gl.val w ≠ 0 ∧ Reading.gl.val w ≠ 1

/-- **What is asked of what the lookup on the calls left**, at values: the lookup's point has lmS
coordinates at least; no coordinate of the three cuts reads 0 or 1. -/
def LeftFine (g : Geo) (lk : Att.P.LookIn) (p : Pts) : Prop :=
  g.lmS ≤ lk.zx.size ∧ (∀ w ∈ (Att.P.lastCoords lk.zx g.lmS).toList, Fine w) ∧
    (∀ w ∈ (Att.P.lastCoords p.d.zcW g.ls).toList, Fine w) ∧ ∀ w ∈ p.d.ziW.toList, Fine w

/-- **A test with code, on the words, that gives it** (`leftFine_of_reads`); the other way is not
stated. -/
def leftReads (g : Geo) (lk : Att.P.LookIn) (p : Pts) : Bool :=
  decide (g.lmS ≤ lk.zx.size) && (Att.P.lastCoords lk.zx g.lmS).all nz01 &&
    (Att.P.lastCoords p.d.zcW g.ls).all nz01 && p.d.ziW.all nz01

/-- A point all of whose coordinates are fine reads 0 or 1 at none. -/
theorem pt_of_fine {z : Array E} (h : ∀ w ∈ z.toList, Fine w) :
    ∀ j < z.size, OnBytes.Road.pt Reading.gl z j ≠ 0 ∧ OnBytes.Road.pt Reading.gl z j ≠ 1 := by
  intro j hj
  unfold OnBytes.Road.pt
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj]
  exact h _ (by simp)

/-- What passes the test on the words is fine. -/
theorem fine_of_all {z : Array E} (h : z.all nz01 = true) : ∀ w ∈ z.toList, Fine w := by
  intro w hw
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
  have hj' : j < z.size := by simpa using hj
  have h1 := (Array.all_eq_true.1 h) j hj'
  simpa using nz01_val h1

/-- The test with code gives what is asked. Conditional: h. -/
theorem leftFine_of_reads {g : Geo} {lk : Att.P.LookIn} {p : Pts} (h : leftReads g lk p = true) :
    LeftFine g lk p := by
  unfold leftReads at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨s1, a1⟩, a2⟩, a3⟩ := h
  exact ⟨s1, fine_of_all a1, fine_of_all a2, fine_of_all a3⟩

/-- A member of a cut is a member of the whole. -/
theorem mem_of_extract {z : Array E} {a b : ℕ} {w : E} (h : w ∈ (z.extract a b).toList) :
    w ∈ z.toList := by
  rw [Array.toList_extract, List.extract_eq_take_drop] at h
  exact List.mem_of_mem_drop (List.mem_of_mem_take h)

/-- **The two cuts are cuts of the key point of one call**: that of the unit that holds the list of
keys `Keys.wl`. They hang on the geometry and on zk alone. Conditional: hp: the function of the
points returns. -/
theorem cuts_are {g : Geo} {zk : Array (Array E)} {hh : Heard} {L : Att.P.Left} {p : Pts}
    (hp : Att.P.pointsOf g zk hh L = some p) :
    ∃ u, g.single .wl = some u ∧
      p.d.ziW = (Att.P.inner u (zk.getD u.call #[])).extract (1 + g.lgk) (1 + g.lgk + g.lt) ∧
      p.d.zcW = (Att.P.inner u (zk.getD u.call #[])).extract (1 + g.lgk + g.lt)
        (1 + g.lgk + g.lt + g.ldh) := by
  unfold Att.P.pointsOf at hp
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, K5Law.guard_some, Option.pure_def,
    Option.some.injEq] at hp
  obtain ⟨_, _, _, _, _, _, uW, hW, _, _, _, _, _, _, _, _, e⟩ := hp
  subst e
  exact ⟨uW, hW, rfl, rfl⟩

/-- **FROM THE RAW POINTS**: no coordinate of zx reads 0 or 1, zx has lmS coordinates at least, and
no coordinate of that one call's key point reads 0 or 1. Conditional: hp: the function of the points
returns, at whichever fork and whatever was heard; hx, hs, hk. -/
theorem leftFine_of_raw {g : Geo} {G : Forest.Heard} {hh : Heard} {F : Fork} {p : Pts} {lmb : ℕ}
    (hp : Att.P.ptsFrom g G.zk hh F = some p) (hx : ∀ w ∈ G.zx.toList, Fine w)
    (hs : g.lmS ≤ G.zx.size)
    (hk : ∀ u, g.single .wl = some u → ∀ w ∈ (G.zk.getD u.call #[]).toList, Fine w) :
    LeftFine g (Att.P.lookOfO lmb G) p := by
  unfold Att.P.ptsFrom at hp
  obtain ⟨Lf, _, hp'⟩ := Option.bind_eq_some_iff.1 hp
  obtain ⟨u, hu, e1, e2⟩ := cuts_are hp'
  have hin : ∀ w ∈ (Att.P.inner u (G.zk.getD u.call #[])).toList, Fine w := fun w hw =>
    hk u hu w (mem_of_extract hw)
  refine ⟨hs, fun w hw => hx w (mem_of_extract hw), fun w hw => ?_, fun w hw => ?_⟩
  · rw [e2] at hw
    exact hin w (mem_of_extract (mem_of_extract hw))
  · rw [e1] at hw
    exact hin w (mem_of_extract hw)

/-- **FROM zx ALONE**, where that call's key point ends in zx and the unit has no more bits than zx
has coordinates: the library's `inner_arr` (Johnson/Desc/First/Att/Claims/KeysTabs.lean), called.
Conditional: hp; hx; hs; hE. -/
theorem leftFine_of_zx {g : Geo} {G : Forest.Heard} {hh : Heard} {F : Fork} {p : Pts} {lmb : ℕ}
    (hp : Att.P.ptsFrom g G.zk hh F = some p) (hx : ∀ w ∈ G.zx.toList, Fine w)
    (hs : g.lmS ≤ G.zx.size)
    (hE : ∀ u, g.single .wl = some u →
      K5Law.EndsIn (G.zk.getD u.call #[]) G.zx ∧ u.bits ≤ G.zx.size) :
    LeftFine g (Att.P.lookOfO lmb G) p := by
  unfold Att.P.ptsFrom at hp
  obtain ⟨Lf, _, hp'⟩ := Option.bind_eq_some_iff.1 hp
  obtain ⟨u, hu, e1, e2⟩ := cuts_are hp'
  have hin : ∀ w ∈ (Att.P.inner u (G.zk.getD u.call #[])).toList, Fine w := fun w hw => by
    rw [K5Law.inner_arr (hE u hu).1 u (hE u hu).2] at hw
    exact hx w (mem_of_extract hw)
  refine ⟨hs, fun w hw => hx w (mem_of_extract hw), fun w hw => ?_, fun w hw => ?_⟩
  · rw [e2] at hw
    exact hin w (mem_of_extract (mem_of_extract hw))
  · rw [e1] at hw
    exact hin w (mem_of_extract hw)

/-- The 32 weights pass the test "all words below the prime, not the word 0". -/
theorem two_pow_nz : ∀ k < 32, nzE (ofF (2 ^ k).toUInt64) = true := by decide

/-- **No weight under which the counts are summed reads 0.** -/
theorem phiP_live (lm : ℕ) :
    ∀ c < 2 ^ lm, Reading.gl.val ((Forest.phiP lm).getD c zeroE) ≠ 0 := by
  intro c hc
  have e : (Forest.phiP lm).getD c zeroE = ofF (2 ^ (c % 32)).toUInt64 := by
    unfold Forest.phiP
    simp [Array.getD_eq_getD_getElem?, hc]
  rw [e]
  exact nzE_val (two_pow_nz _ (Nat.mod_lt _ (by decide)))

/-- **No entry of the two written weights reads 0**: of the first below 2 ^ lmS, of the second below
its own number of entries. Conditional: hL. -/
theorem left_live {g : Geo} {lk : Att.P.LookIn} {p : Pts} (hL : LeftFine g lk p) :
    (∀ c < 2 ^ g.lmS, Reading.gl.val ((Att.P.lastN lk.zx g.lmS).getD c zeroE) ≠ 0) ∧
    ∀ x < (Att.P.blockRows (Att.P.eqTab (Att.P.lastCoords p.d.zcW g.ls))
        (Att.P.eqTab p.d.ziW)).size,
      Reading.gl.val ((Att.P.blockRows (Att.P.eqTab (Att.P.lastCoords p.d.zcW g.ls))
        (Att.P.eqTab p.d.ziW)).getD x zeroE) ≠ 0 := by
  obtain ⟨s1, a1, a2, a3⟩ := hL
  have z1 : (Att.P.lastCoords lk.zx g.lmS).size = g.lmS := by
    unfold Att.P.lastCoords
    rw [Array.size_extract]
    omega
  refine ⟨fun c hc => ?_, fun x hx => ?_⟩
  · show Reading.gl.val ((Att.P.eqTab (Att.P.lastCoords lk.zx g.lmS)).getD c zeroE) ≠ 0
    exact eqTab_val_ne Reading.gl (pt_of_fine a1) (by rw [z1]; exact hc)
  · rw [K5Law.blockRows_size, size_eqTab, size_eqTab] at hx
    exact blockRows_eq_val_ne Reading.gl (pt_of_fine a2) (pt_of_fine a3) hx

/-- **What is asked of the raw points that the lookup on the calls left**: no coordinate of zx reads
0 or 1; zx has lmS coordinates at least; no coordinate of the key point of the call that holds the
list of keys `Keys.wl` reads 0 or 1. -/
def RawFine (g : Geo) (G : Forest.Heard) : Prop :=
  (∀ w ∈ G.zx.toList, Reading.gl.val w ≠ 0 ∧ Reading.gl.val w ≠ 1) ∧ g.lmS ≤ G.zx.size ∧
    ∀ u, g.single .wl = some u →
      ∀ w ∈ (G.zk.getD u.call #[]).toList, Reading.gl.val w ≠ 0 ∧ Reading.gl.val w ≠ 1

/-- **The end**: on every matrix below NAs + 4 the state's list holds a table as `LiveV` says, of
some length. mats: the plan's list of matrices. -/
def LiveAllV (g : Geo) (mats : Array TMat) (s : S) : Prop :=
  ∃ tl, s.tl? = some tl ∧ ∀ mu < g.NAs + 4, ∃ n, ∃ Fn ∈ tl.funs.toList, LiveV mats mu n Fn

/-- **BEHIND A YES OF THE QUIET STEP, ON EVERY MATRIX.** Conditional: h: the yes; hR: the test on
what the segment's own rounds heard, in the state in front; hL: what is asked of what the lookup
on the calls left, at the points of the state in front. -/
theorem funs_liveAll (A : Attention.Plan) {m s : S} (h : readsAtSO A m = .ok s)
    (hR : ∀ hh, m.heard5? = some hh → heardReads (Att.P.parCOf A).geo hh = true)
    (hL : ∀ a g hh p, m.here = .att a → a.g = some g → m.heard5? = some hh →
      Att.P.ptsFrom (Att.P.parCOf A).geo g.zk hh a.F = some p →
      LeftFine (Att.P.parCOf A).geo (Att.P.lookOfO (Att.P.parCOf A).geo.lmb g) p) :
    LiveAllV (Att.P.parCOf A).geo A.mats s := by
  obtain ⟨a, hh, g, p, tl, ea, e5, eg, hp, hok, et, hall⟩ := funs_of_laid A h
  obtain ⟨tl2, et2, F0, F3⟩ := funs_liveV A h e5 (hR hh e5)
  obtain rfl : tl2 = tl := Option.some.inj (et2.symm.trans et)
  obtain ⟨l0, l1⟩ := left_live (hL a g hh p ea eg e5 hp)
  have f1 : (Att.P.blockRows (Att.P.eqTab (Att.P.lastCoords p.d.zcW (Att.P.parCOf A).geo.ls))
      (Att.P.eqTab p.d.ziW)).size = 2 ^ (Att.P.parCOf A).geo.la :=
    out_size hok
  have mr : ∀ {x : Table} {X Y : List Table}, x ∈ Y → x ∈ X ++ Y := fun h =>
    List.mem_append_right _ h
  have ml : ∀ {x : Table} {Y : List Table}, x ∈ [x] ++ Y := List.mem_append_left _
    (List.mem_singleton.2 rfl)
  refine ⟨tl2, et, fun mu hmu => ?_⟩
  by_cases c0 : mu < (Att.P.parCOf A).geo.NAs
  · obtain ⟨Fn, hF, e1, e2, e3, e4, e6, e7⟩ := hall ⟨mu, 2 ^ (Att.P.parCOf A).geo.lmS,
      Att.P.lastN (Att.P.lookOfO (Att.P.parCOf A).geo.lmb g).zx (Att.P.parCOf A).geo.lmS,
      (Att.P.parCOf A).geo.kAs / (Att.P.parCOf A).geo.NAs⟩ (by
        unfold laidBy
        exact List.mem_append_left _ (List.mem_map.2 ⟨mu, List.mem_range.2 c0, rfl⟩))
    exact ⟨_, Fn, hF, e1, rfl, e4, e6, e7, fun c hc => by
      rw [e3]
      rw [e2] at hc
      exact l0 c hc⟩
  · have hc : mu = (Att.P.parCOf A).geo.NAs ∨ mu = (Att.P.parCOf A).geo.NAs + 1 ∨
        mu = (Att.P.parCOf A).geo.NAs + 2 ∨ mu = (Att.P.parCOf A).geo.NAs + 3 := by omega
    rcases hc with rfl | rfl | rfl | rfl
    · exact ⟨_, F0⟩
    · obtain ⟨Fn, hF, e1, e2, e3, e4, e6, e7⟩ := hall ⟨(Att.P.parCOf A).geo.NAs + 1,
        2 ^ (Att.P.parCOf A).geo.la,
        Att.P.blockRows (Att.P.eqTab (Att.P.lastCoords p.d.zcW (Att.P.parCOf A).geo.ls))
          (Att.P.eqTab p.d.ziW),
        (Att.P.parCOf A).geo.fillO * (Att.P.parCOf A).geo.T / 2 ^ (Att.P.parCOf A).geo.la⟩ (by
          unfold laidBy
          exact mr (mr (mr (mr (mr (mr (mr (mr (mr (mr ml))))))))))
      exact ⟨_, Fn, hF, e1, rfl, e4, e6, e7, fun x hx => by
        rw [e3]
        rw [e2] at hx
        exact l1 x (by rw [f1]; exact hx)⟩
    · obtain ⟨Fn, hF, e1, e2, e3, e4, e6, e7⟩ := hall ⟨(Att.P.parCOf A).geo.NAs + 2,
        2 ^ (Att.P.parCOf A).geo.lmb, (Att.P.lookOfO (Att.P.parCOf A).geo.lmb g).phiP,
        (Att.P.parCOf A).geo.kbA⟩ (by
          unfold laidBy
          exact mr (mr (mr (mr (mr (mr (mr (mr (mr (mr (mr (mr (mr (mr (mr (mr (mr (mr (mr
            ml)))))))))))))))))))
      exact ⟨_, Fn, hF, e1, rfl, e4, e6, e7, fun c hc => by
        rw [e3]
        rw [e2] at hc
        exact phiP_live _ c hc⟩
    · exact ⟨_, F3⟩

/-- The end hangs on the reading alone. Conditional: e: the reading behind is the reading in front;
hL. -/
theorem liveAll_read {g : Geo} {mats : Array TMat} {s s' : S}
    (e : K8.readTl lstF s' = K8.readTl lstF s) (hL : LiveAllV g mats s) : LiveAllV g mats s' := by
  obtain ⟨tl, ht, h1⟩ := hL
  unfold K8.readTl at e
  rw [ht] at e
  obtain ⟨tl', ht', ef⟩ := Option.map_eq_some_iff.1 e
  have ef2 : tl'.funs = tl.funs := (Prod.mk.inj ef).2
  refine ⟨tl', ht', ?_⟩
  rw [ef2]
  exact h1

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
include h

/-- **Under the head the plan's list has just NAs + 4 matrices**: so the end speaks of every matrix
of the plan's list, and of no number at which there is none. Conditional: the head; ea. -/
theorem mats_at_head {g : ℕ} {a : Attention.Plan} (ea : (P5J.At.X Zp).A[g]? = some a) :
    a.mats.size = (Att.P.parCOf a).geo.NAs + 4 := by
  obtain ⟨A0, pf, hA, e⟩ := planIs_all h g a ea
  exact mats_of_plan ⟨_, _, _, A0, pf, hA, e⟩

/-- **To the state behind the quiet step.** Conditional: the head; hg; ea; f4, f5: which members;
d4, d5: their yes; hc: c holds what the rounds of the first drew; hk: the test on these; hL: what
is asked of the raw points that the lookup on the calls left in the segment that stands open at
s4. -/
theorem liveAll_behind_reads {g : ℕ} (hg : g < 12) {a : Attention.Plan}
    (ea : (P5J.At.X Zp).A[g]? = some a) {b4 b5 : Block S ProofFile.Cl}
    (f4 : cF.blocksInOrder[14 * (2 * g + 1) + 4]? = some b4)
    (f5 : cF.blocksInOrder[14 * (2 * g + 1) + 5]? = some b5) {s4 s5 s6 : S} {rs4 rs5 : List Fmt.RoundView}
    {gs4 gs5 : List (List (ℕ × List UInt64))} (d4 : b4.decide s4 rs4 gs4 = .ok s5)
    (d5 : b5.decide s5 rs5 gs5 = .ok s6) (c : Chal) (hc : Reads c rs4)
    (hk : k5Reads a.own (Att.P.parCOf a).geo c = true)
    (hL : ∀ att G, s4.here = .att att → att.g = some G → RawFine (Att.P.parCOf a).geo G) :
    LiveAllV (Att.P.parCOf a).geo a.mats s6 := by
  obtain ⟨att, hd, G, e4, hh, rfl⟩ := heard_of_k5 h hg ea f4 d4
  have Pu := public_at_head h hg ea
  have hR : heardReads (Att.P.parCOf a).geo hd = true :=
    heardReads_of_plan ⟨a.S, a.own⟩ c hh hc Pu.sized Pu.planned hk
  obtain ⟨G₀, Xl, pd, reads, digits, b, M⟩ := member_at_head h hg
  have hA : G₀.W.A[Xl.g]? = some a := by
    rw [M.group, M.pubW]
    exact ea
  obtain rfl : b = b5 := Option.some.inj (M.flat.symm.trans f5)
  rw [M.is] at d5
  obtain ⟨m, h1, hm⟩ := seated_reads_inv Zp G₀ (2 * g + 1) Xl reads b.name M.kind hA d5
  obtain ⟨L', F', em, _, _, _⟩ := k1_leaves h1 (a₀ := { att with F := G, heard5 := some hd }) rfl
  have h5 : m.heard5? = some hd := by
    unfold S.heard5?
    rw [em]
  refine funs_liveAll a hm (fun hh' e => ?_) (fun a' g' hh' p' ea' eg' _ hp' => ?_)
  · obtain rfl : hd = hh' := Option.some.inj (h5.symm.trans e)
    exact hR
  · rw [em] at ea'
    cases ea'
    obtain ⟨hx, hs, hk⟩ := hL att g' e4 eg'
    exact leftFine_of_raw hp' hx hs hk

/-- **FROM THE TEST AND THE CONDITION TO THE STATE IN FRONT OF THE BATCHING, ON EVERY MATRIX.**
Conditional: the head; hg; ea; f4 … f8: which five members; d4 … d8: their yes, each at its own
rounds; hc, hk, hL: as above. -/
theorem liveAll_at_batch {g : ℕ} (hg : g < 12) {a : Attention.Plan}
    (ea : (P5J.At.X Zp).A[g]? = some a) {b4 b5 b6 b7 b8 : Block S ProofFile.Cl}
    (f4 : cF.blocksInOrder[14 * (2 * g + 1) + 4]? = some b4)
    (f5 : cF.blocksInOrder[14 * (2 * g + 1) + 5]? = some b5)
    (f6 : cF.blocksInOrder[14 * (2 * g + 1) + 6]? = some b6)
    (f7 : cF.blocksInOrder[14 * (2 * g + 1) + 7]? = some b7)
    (f8 : cF.blocksInOrder[14 * (2 * g + 1) + 8]? = some b8) {s4 s5 s6 s7 s8 s9 : S}
    {rs4 rs5 rs6 rs7 rs8 : List Fmt.RoundView} {gs4 gs5 gs6 gs7 gs8 : List (List (ℕ × List UInt64))}
    (d4 : b4.decide s4 rs4 gs4 = .ok s5) (d5 : b5.decide s5 rs5 gs5 = .ok s6)
    (d6 : b6.decide s6 rs6 gs6 = .ok s7) (d7 : b7.decide s7 rs7 gs7 = .ok s8)
    (d8 : b8.decide s8 rs8 gs8 = .ok s9) (c : Chal) (hc : Reads c rs4)
    (hk : k5Reads a.own (Att.P.parCOf a).geo c = true)
    (hL : ∀ att G, s4.here = .att att → att.g = some G → RawFine (Att.P.parCOf a).geo G) :
    LiveAllV (Att.P.parCOf a).geo a.mats s9 := by
  have L6 := liveAll_behind_reads h hg ea f4 f5 d4 d5 c hc hk hL
  have L7 := liveAll_read (lst_leaves h hg (by omega) (by omega) f6 _ _ _ _ d6) L6
  have L8 := liveAll_read (lst_leaves h hg (by omega) (by omega) f7 _ _ _ _ d7) L7
  exact liveAll_read (lst_leaves h hg (by omega) (by omega) f8 _ _ _ _ d8) L8

end

end H2K5.Honest

#print axioms H2K5.Honest.pt_of_fine
#print axioms H2K5.Honest.fine_of_all
#print axioms H2K5.Honest.leftFine_of_reads
#print axioms H2K5.Honest.mem_of_extract
#print axioms H2K5.Honest.cuts_are
#print axioms H2K5.Honest.leftFine_of_raw
#print axioms H2K5.Honest.leftFine_of_zx
#print axioms H2K5.Honest.two_pow_nz
#print axioms H2K5.Honest.phiP_live
#print axioms H2K5.Honest.left_live
#print axioms H2K5.Honest.funs_liveAll
#print axioms H2K5.Honest.liveAll_read
#print axioms H2K5.Honest.mats_at_head
#print axioms H2K5.Honest.liveAll_behind_reads
#print axioms H2K5.Honest.liveAll_at_batch
