-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.Promise354
import Johnson.Loose.H2K12.ChainAtLast
import Johnson.Loose.H2K12.K12LawR
import Johnson.Desc.Sound.SeamDesc
import Johnson.Desc.First.Driver.Chain
import Johnson.P5J.MeansQ
import Johnson.G.PackLit
/-
Johnson/Loose/H2K12/PublicAt354.lean: The
proximity test (the kind K12) on the proof file's first chain, sub-protocol number 354 of the table of joints:
`PublicK12` (Promise354.lean: what the fourth tie's first half asks of the list of rounds and the list of members) FIELD
BY FIELD: what is paid, by whom; what stays, as a smaller Lean structure. Definitions, statements and proofs: calls, and
closed facts by the kernel; beside four of them stands a second fact at a bent value (`…_no`).
  `shL`, `e0L`: the shape and the radius of the one member of the group under test at the full size, as
    evaluations at the stored files print them.
  `PublicLeft354`: WHAT STAYS: six fields: no two members of the list have one seat · no two messages are
    listed at one place · the entry of each member at a tenant of an open pin is (shL, e0L) · `K1.Tie` at
    shL · the log-length of shL's code is 23 · the listed tree's shape is what the IOP as written tells.
  `stage_LFull`, `fit_LFull`, `fit_LFull_no`: the closed place's first stage; the test's radius there
    against a member's listed radius: 2433820 fits, 2433819 does not.
  `publicK12_at`: in the goals' scope, at what `ProofFile.pubPlain` and `H2U.placesOfMade` return, under
    `LastTypedAt`, `PublicAtLast`, "the IOP as written accepts its own list of rounds" and its data, "the
    seats fit", two equations on the fold's public numbers, "a class of rows is open" and
    `PublicLeft354` ⊢ `PublicK12` at the made place, the planner's radii and the frame of that data.
  `O354`, `pinsOpen_of`, `closed_354`, `rowOpen_354`, `rowOpen_353_no`, `pins_354`: at the written list of places: a class of rows of
    segment 25 is open at 354 (at 353 none is); the tenants of open pins are those of moment 0.
  `tie_full`, `tie_no`, `long_full`, `long_full_no`: two of the six at the written codes, by the kernel.
WHO COULD PAY THE SIX. The first five are closed facts off the written sendings and codes: they want the
tie "laid ⇒ the pins accept" of the entry tests' list of thirteen rows. The sixth has no lemma for
the code switch's sendings in this library: it is that kind's files' to show.
What it is not. `PublicLeft354` is a premise; it is shown at no list. By evaluations at the stored
full-size files each of its fields is true there and a negative test of each is false: an evaluation at
one set of files, no theorem. `PublicK12` is itself a structure of premises of another theorem. No
soundness is claimed. Nothing on hiding.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12
open OnBytes OnBytes.Maker Johnson.Pack
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Coin (MemberPub)
open VerifiableInference.Desc.First (ModelPart Item Numbers openSets start rowSegs flatPlacesOf)
open H2K.Member (piLFull rLFull)
open H2K.Pub (sgOf)
open H2K.JointK (pL a12 PublicAtLast)

/-- The shape of the one member of the group under test at the full size. -/
def shL : OracleShape :=
  { code := 0, mainRows := 2, mainDeg := 3, maskRows := 0, maskCode := 0, answers := 1 }

/-- Its listed radius. -/
def e0L : ℕ := 2433820

/-- **What stays of `PublicK12`.** O: the items that are open at the border. No state is read. -/
structure PublicLeft354 (cs : Codes) {Xi : Type} (G : FileDescription Xi) (d : First.FoldData)
    (N : Numbers) (n : ℕ) (O : List Item) (ms : List Mem) : Prop where
  /-- no two members of ms have one seat -/
  seatsOnce : (ms.map seatOf).Nodup
  /-- no two messages are listed at one place -/
  placesOnce : d.L.places.Nodup
  /-- the listed shape and radius of a member at a tenant of an open pin -/
  entry : ∀ x ∈ ms, seatOf x ∈ pinsOpen N O n → x.1.l.get x.2 = (shL, e0L)
  tie : K1.Tie cs shL
  /-- the log-length of that shape's code -/
  long : aOf cs shL = 23
  /-- Its payers: the code switch's files (the kind K2) state, by report, "told is laid" for
  that kind's sendings; that the listed tree's shape is that sending's, and that the IOP as written tells
  that sending's oracle at this tree's number: two ties, K12's files' or the join's: not typed. -/
  told : ∀ x ∈ ms, seatOf x ∈ pinsOpen N O n → MemberTold G d.L.shapes x

/-- The closed place's first stage. -/
theorem stage_LFull (st : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (h : piLFull.nums.stages = st :: rest) :
    rLFull (sgOf st).st = 2433820 ∧ (sgOf st).C.a = 23 ∧ st.Z.a = 17 := by
  have e : piLFull.nums.stages.head? = some st := by rw [h]; rfl
  obtain rfl : _ = st := Option.some.inj e
  decide +kernel

/-- **The test's radius at the first stage against a member's listed radius.** A: the log-length of the
member's code. -/
theorem fit_LFull (A e0 : ℕ) (hA : A = 23) (he : 2433820 ≤ e0) (st : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (h : piLFull.nums.stages = st :: rest) :
    rLFull (sgOf st).st < (e0 + 1) * 2 ^ ((sgOf st).C.a - A) := by
  obtain ⟨h1, h2, _⟩ := stage_LFull st rest h
  rw [h1, h2, hA]
  simp only [Nat.sub_self, pow_zero, Nat.mul_one]
  omega

/-- A closed fact; no control: it cannot fail (with `stage_LFull`: ¬ 2433820 < 2433820). -/
theorem fit_LFull_no (st : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (h : piLFull.nums.stages = st :: rest) :
    ¬ rLFull (sgOf st).st < (2433819 + 1) * 2 ^ ((sgOf st).C.a - 23) := by
  obtain ⟨h1, h2, _⟩ := stage_LFull st rest h
  rw [h1, h2]
  decide

/-- **`PublicK12` at the made place, from what lies and what stays.** -/
theorem publicK12_at {o : ProofFile.SecondHashFunctionArgument} {S : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub} {Np : H2U.Places4}
    {pre : List (Block First.S ProofFile.Cl)} (hS : VerifierAndGoals.InScope S = true)
    (hZ : ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z) (hN : H2U.placesOfMade Z.made = .ok Np)
    (hT : LastTypedAt o S.pol S.lay S.KL) (hPub : PublicAtLast Z Np pre) (cs : Codes) {Xi : Type}
    (G : FileDescription Xi) (file : String) (D : WholeD) (hp : G.planOk = true)
    (hD : G.data file = .ok D) (d : First.FoldData) (N : Numbers) (n : ℕ) (O : List Item)
    (ms : List Mem) (hfit : SeatsFit cs G ms) (hft : d.ft = 0) (hcs : d.sent.codes = cs)
    (hrow : n ∈ rowSegs O) (left : PublicLeft354 cs G d N n O ms) :
    PublicK12 cs G (frameAt D (allOf D) D.key₁ 0) (pL Np) rLFull d N n O ms := by
  obtain ⟨_, C, _, ho, _, _, _⟩ := hPub
  have A := H2K.Sizes.atFull_of_pubPlain hS hZ
  have hL := hT Z hZ
  have hn : (pL Np).nums = Np.L.nums := H2K.Made.nums_of_planOk a12 Np.L C.plan
  have hst : (pL Np).nums.stages = piLFull.nums.stages := by
    rw [hn]
    exact (H2K.Sizes.place_L_of_full A hN hL).1
  have hf0 : (pL Np).nums.firstTree = 0 := by
    rw [hn]
    exact (H2K.Made.places_firstTree Z.made Np hN).1
  refine ⟨C.joh, C.plan, ho, hf0.trans hft.symm, hcs, left.seatsOnce, left.placesOnce, hrow,
    fun x hx hpin => ⟨?_, left.told x hx hpin⟩⟩
  have he := left.entry x hx hpin
  have e1 : (x.1.l.get x.2).1 = shL := congrArg Prod.fst he
  have e2 : (x.1.l.get x.2).2 = e0L := congrArg Prod.snd he
  refine ⟨by rw [e1]; exact left.tie, by rw [e1]; decide, by rw [e1]; decide,
    Or.inl (by rw [e1]; decide), ?_, hfit x hx,
    fun u hu => _root_.Desc.K14.Law.Fence.depth_of_planOk G file D hp hD D.key₁ 0 _ u hu⟩
  intro st rest h
  rw [e1, e2]
  exact fit_LFull _ _ left.long (Nat.le_of_eq rfl) st rest (hst.symm.trans h)

/-! ## The closed facts at the written list of places -/

/-- The items that are open at border 354 of the written list of places. -/
def O354 : List Item :=
  (openSets P5J.fullLinks (flatPlacesOf P5J.fullLinks true) (start P5J.fullLinks))[354]?.getD []

/-- And at 353. -/
def O353 : List Item :=
  (openSets P5J.fullLinks (flatPlacesOf P5J.fullLinks true) (start P5J.fullLinks))[353]?.getD []

/-- Where of a segment's three pins the first alone is open. -/
theorem pinsOpen_of (N : Numbers) (O : List Item) (n : ℕ) (c0 : O.contains (Item.pin n 0) = true)
    (c1 : O.contains (Item.pin n 1) = false) (c2 : O.contains (Item.pin n 2) = false) :
    pinsOpen N O n = N.sent n 0 := by
  have e : List.range 3 = [0, 1, 2] := rfl
  have m0 : Item.pin n 0 ∈ O := List.contains_iff_mem.1 c0
  have m1 : Item.pin n 1 ∉ O := fun h => by
    rw [List.contains_iff_mem.2 h] at c1
    cases c1
  have m2 : Item.pin n 2 ∉ O := fun h => by
    rw [List.contains_iff_mem.2 h] at c2
    cases c2
  simp [pinsOpen, e, m0, m1, m2]

/-- Four closed facts in one evaluation by the kernel. -/
theorem closed_354 : (decide (25 ∈ rowSegs O354) && O354.contains (Item.pin 25 0) &&
    !O354.contains (Item.pin 25 1) && !O354.contains (Item.pin 25 2)) = true := by decide +kernel

theorem rowOpen_354 : 25 ∈ rowSegs O354 := by
  have h := closed_354
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1

/-- The negative test: one border in front no class of rows of segment 25 is open. -/
theorem rowOpen_353_no : 25 ∉ rowSegs O353 := by decide +kernel

/-- The tenants of open pins at 354 are those that segment 25 sends at its moment 0. -/
theorem pins_354 (N : Numbers) : pinsOpen N O354 25 = N.sent 25 0 := by
  have h := closed_354
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  exact pinsOpen_of N O354 25 h.1.1.2 h.1.2 h.2

/-! ## Two of the six at the written codes -/

theorem tie_full : K1.Tie Johnson.G.codesFull2 shL :=
  ⟨rfl, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The negative test: a code's number beyond the list. -/
theorem tie_no : ¬ K1.Tie Johnson.G.codesFull2 { shL with code := 17 } :=
  fun h => absurd h.shape (by decide +kernel)

theorem long_full : aOf Johnson.G.codesFull2 shL = 23 := by decide +kernel

/-- The negative test: at the next code of the list. -/
theorem long_full_no : aOf Johnson.G.codesFull2 { shL with code := 1 } ≠ 23 := by decide +kernel

end H2K12

#print axioms H2K12.stage_LFull
#print axioms H2K12.fit_LFull
#print axioms H2K12.fit_LFull_no
#print axioms H2K12.publicK12_at
#print axioms H2K12.pinsOpen_of
#print axioms H2K12.closed_354
#print axioms H2K12.rowOpen_354
#print axioms H2K12.rowOpen_353_no
#print axioms H2K12.pins_354
#print axioms H2K12.tie_full
#print axioms H2K12.tie_no
#print axioms H2K12.long_full
#print axioms H2K12.long_full_no
