-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/MemberAtYes.lean: the seam's bundle behind our game's relations, PAID MEMBER
BY MEMBER, WITH THE TEST's OWN «accept» AND THE FIRST PASS's «accept» IN THE PAYER's HAND. General
in the IOP as written in Lean, the frame, the place, the doors, the numbering. A definition,
statements and proofs; each proof is a few calls.
Why. `CoreLeft` (CoreBehindQ.lean) speaks «at whatever the verifier's state fixes»: its payer holds
neither the decision's «accept» nor the «accept» of the plain data's tests (gpL), which our laws on
a member's site and sample spend (`site_long` | `site_mask`, ShapesAtSeat.lean · `hQ_of_yesA`,
CoreAtYes.lean). Both lie in our relation QW: the first outright, the second inside the game's
conclusion (NTuple's own «there is a row»). Here they are handed to the payer; and of
`MemberFacts` (Johnson/Desc/Sound/SeamMembers.lean: seven clauses a member) the
first two are paid.
  `MemberLeft`: what is left of `MemberFacts` at a member: on its shape: one answer · the case · one
    of two facts for the site (the second's «the tree's depth is at most the mask code's»: its
    payer: `site_maskB` with split_depth, at a message that lies alone in its tree) ·
    clauses (3) (4) (5) (7) as they stand · clause (6) with ONE conjunct more under its «there is»:
    WHERE THE SHAPE HAS ROWS OF BOTH KINDS every coordinate of the out-of-domain (OOD) seed's point
    is canonical. («The message is sampled» falls to the decision's «accept»: `sampled_of_decide`.)
  `memberFacts_of_left`: MemberLeft, the two «accept»s ⊢ MemberFacts.
  `core_behind_QWm`: the first arm at any numbering by labels nl: QW · johOk · planOk · «the
    statement is in order» · at whatever the state behind the door in fixes: the codes' equation and
    an injective list of members, holding all that sit, with MemberLeft at each ⊢ one tuple of typed
    messages of which all rows taken in hold, a candidate at every member that sits.
`MemberLeft₂` · `MemberLeft.parted` · `memberFacts_of_left₂` ·
`core_behind_QWm₂`: the canonical OOD seed's «there is» stands BESIDE clause (6)'s, not under it:
for a shape with rows
of
both kinds (the key file's V at row 3.2).
KIN, NAMED:
Johnson/Desc/Sound/SeamFactsQ.lean | SeamLastQ.lean: `tupleNine_ofQ` | `tupleNine_membersQ`
and their likes at ten: THE SAME THOUGHT («the facts may spend the game's own conclusion») at the
proof file's two seats; here general, behind QW · its `fixes_unique` is `fixes_one`
(ChecksAt.lean), which is called here · SeamMemberOf.lean: `memberFacts_of`: MemberFacts at one
member from the sendings' invariant (K1.SeedIs · Tie · the reading's tie), which gives clauses (4)
and (6), WITH (1)
(2)
(3) (5) (7) AS PREMISES: THE COMPLEMENT OF `memberFacts_of_left`, which pays (1) and (2) and takes
the rest: the two joined would leave (3) (5) (7), the invariant and the shape's facts: not typed.
What it is not. MemberLeft is a premise: no member of it is shown here. FIRST LIMIT, as at
`core_behind_QWn`: the book's price stands in clause (7), at no := nuOf π nl t. The second arm's
like is not typed. It pays no field of a table. No soundness is claimed. Nothing on hiding.

-/
import Johnson.Desc.K12.Coin.CoreBehindQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open H2K.Pin
open Cb Cb.Ood Iop Prob OnBytes OnBytes.Slice OnBytes.Slice.ProxRun Johnson.Pack
open OnBytes.Means H2K.ClaimSays
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open OnBytes.Maker
open _root_.Run
open H2K.First (Seat1 Plain gpL)
open H2K.Pub (sgOf johOk)
open _root_.Desc.K14.Law.Fence (CoreFacts core_at GroupFacts MemberFacts)

/-- **What is left of `MemberFacts` at a member, behind the two «accept»s.** -/
def MemberLeft (cs : Codes) {Xi A : Type} (G : FileDescription Xi) (Fr : Frame) (no : ℕ → ℕ)
    (rad : Sg → ℕ)
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (mem : ℕ → Option Mem) (y : Fr.E.Str) (a0 : A) (Y : Strs) (a : Fmt.M1.Stage) (D : Plain)
    (j : Fin D.mems.length) (x : Mem) (e0 : ℕ) : Prop :=
  (D.mems.get j).sh.answers = 1 ∧
  ((0 < (D.mems.get j).sh.maskRows ∨ (D.mems.get j).sh.mainDeg = 3) ∨
    ((D.mems.get j).sh.maskRows = 0 ∧ (D.mems.get j).sh.mainDeg = 1)) ∧
  ((0 < (D.mems.get j).sh.mainRows ∧
      ((D.mems.get j).sh.maskRows = 0 → cs.mask.size ≤ (D.mems.get j).sh.maskCode)) ∨
    (0 < (D.mems.get j).sh.maskRows ∧ cs.base.size ≤ (D.mems.get j).sh.code ∧
      (D.mems.get j).tsh.logN ≤ a.Z.a)) ∧
  rad (sgOf a) < (e0 + 1) * 2 ^ ((sgOf a).C.a - aOf cs (D.mems.get j).sh) ∧
  x.1.l.get x.2 = ((D.mems.get j).sh, e0) ∧
  mem (D.mems.get j).id = some x ∧
  (∃ (o : OnBytes.Oracle) (seed : SampleSeed) (row0 : OnBytes.Row) (tt : E) (β : GEˣ),
    D.st.oracles[(D.mems.get j).id]? = some o ∧
    (¬ (0 < (D.mems.get j).sh.mainRows ∧ 0 < (D.mems.get j).sh.maskRows) ∨
      ∀ c ∈ seed.z, okE c = true) ∧
    Send.form cs (D.mems.get j).sh (D.mems.get j).id seed 0 = some row0 ∧
    o.sampleRows.toList = [{ row0 with target := tt }] ∧
    bitsZ cs (D.mems.get j).sh ≤ seed.z.length ∧ (β : GE) = readE seed.beta ∧
    ∃ (z σ' : ((sigOf cs x.1.l).om x.2).Smp), smp a0 x.1 x.2 = some z ∧
      HEq (((readP (bitsZ cs (D.mems.get j).sh) seed.z, β), fun _ => readE tt) :
        (portOmZ cs (D.mems.get j).sh e0).Smp) σ' ∧ z.2 = σ'.2 ∧
      ((sigOf cs x.1.l).om x.2).Z.val z.1 = ((sigOf cs x.1.l).om x.2).Z.val σ'.1) ∧
  HEq (strOf cs (D.mems.get j).sh e0 (layOf (D.mems.get j))
      (W0 Fr no D.book y (D.mems.get j).t).1 (W0 Fr no D.book y (D.mems.get j).t).2)
    (VerifiableInference.Desc.Sound.wordsOf G cs x.1.l x.1.seat Y x.2)

/-- **A member's seven clauses, from what is left and the two «accept»s.** -/
theorem memberFacts_of_left (cs : Codes) {Xi A : Type} (G : FileDescription Xi) (Fr : Frame) (π : P12)
    (no : ℕ → ℕ) (rad : Sg → ℕ)
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (mem : ℕ → Option Mem) (y : Fr.E.Str) (a0 : A) (Y : Strs) (he : π.early = true)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (t tE : T12) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).decide t rs gs = .ok tE) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain)
    (hf : Fixes π t a rest G0 Ly D) (row : GroupRow)
    (hok : H2K.First.ok (gpL π a row D) = true) (hcs : D.st.codes = cs)
    (j : Fin D.mems.length) (x : Mem) (e0 : ℕ)
    (hL : MemberLeft cs G Fr no rad smp mem y a0 Y a D j x e0) :
    MemberFacts cs G Fr no rad smp mem y a0 Y a D j x e0 := by
  subst hcs
  obtain ⟨h1, hcase, hsite, h3, h4, h5, ⟨o, seed, row0, tt, β, e1, e3, e4, e5, e6, e7, e8⟩, h7⟩ :=
    hL
  have hsome : 0 < (D.mems.get j).sh.mainRows ∨ 0 < (D.mems.get j).sh.maskRows :=
    hsite.elim (fun s => Or.inl s.1) fun s => Or.inr s.1
  have e2 : o.sampled = true := by
    obtain ⟨o', q1, q2, _⟩ := sampled_of_decide π t tE rs gs h a rest G0 Ly D hf j
    obtain rfl : o' = o := Option.some.inj (q1.symm.trans e1)
    exact q2
  refine ⟨?_, ?_, h3, h4, h5, ⟨o, seed, row0, tt, β, e1, e4, e5, e6, e7, e8⟩, h7⟩
  · rcases hsite with ⟨s1, s2⟩ | ⟨s1, s2, s3⟩
    · exact site_long π a row D hok j s1 s2
    · exact site_mask π a row D hok j s1 s2 s3
  · rcases e3 with hone | hall
    · exact hQ_of_yes π he hp t tE rs gs h a rest G0 Ly D hf row hok j
        ⟨o, seed, row0, tt, β, e1, e2, e4, e5, e6, e7⟩ h1 hone hsome hcase
    · exact hQ_of_yesA π he hp t tE rs gs h a rest G0 Ly D hf row hok j
        ⟨o, seed, row0, tt, β, e1, e2, e4, e5, e6, e7, hall⟩ h1 hsome hcase

/-- **The seam's core behind QW, paid member by member; at any numbering by labels.** -/
theorem core_behind_QWm {P S Xi A : Type} (cs : Codes) (G : FileDescription Xi) (Fr : Frame) (π : P12)
    (nl : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (mem : ℕ → Option Mem) (sits : Mem → Prop)
    (rd : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP cs (x.1.l.get x.2).1 m part i)
    (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (a b : (P × S) × Fr.E.Str) (a0 : A) (Y : Strs) (h : QW Fr π nl r rdN enter leave a b)
    (hj : johOk π r = true) (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (left : ∀ t, enter a.1.2 = .ok t → ∀ (s : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
      (G0 : Group) (Ly : GroupLayout) (D : Plain), Fixes π t s rest G0 Ly D →
      D.st.codes = cs ∧
      ∃ (xs : Fin D.mems.length → Mem) (es : Fin D.mems.length → ℕ), Function.Injective xs ∧
        (∀ z, sits z → ∃ j, xs j = z) ∧
        ∀ j : Fin D.mems.length,
          MemberLeft cs G Fr (nuOf π nl t) (fun q => r q.st) smp mem a.2 a0 Y s D j (xs j) (es j))
    (hI : ∀ t, enter a.1.2 = .ok t → InOrder t.st) :
    ∃ t G0, enter a.1.2 = .ok t ∧ t.st.groups[t.g]? = some G0 ∧
      ∃ m : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg,
        AllSay OnBytes.Model.Reading.gl (begun t.st t.g G0) (runRows t.st G0).toList
          (_root_.Desc.K14.Law.wordsT cs mem rd m) ∧
        ∀ x, sits x → CandAt cs G smp x a0 Y (m x) := by
  have he := H2K.JointK.early_of_planOk π hp
  obtain ⟨t0, tE, h1, _, hq, rs, gs, hy⟩ := id h
  obtain ⟨s0, rest0, G00, Ly0, D0, hf0, row₀, hok, _⟩ := id hq
  refine core_behind_QWn cs G Fr π nl r rdN smp mem sits rd hrd enter leave a b a0 Y h hj he hp
    (fun t ht => ?_) hI
  obtain rfl : t0 = t := Except.ok.inj (h1.symm.trans ht)
  refine coreLeft_of_members cs G Fr π _ _ smp mem sits t0 a.2 a0 Y fun s rest G0 Ly D hf => ?_
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := fixes_one π t0 hf0 hf
  obtain ⟨hcs, xs, es, hinj, hs, hM⟩ := left t0 ht s0 rest0 G00 Ly0 D0 hf
  exact ⟨hcs, xs, es, hinj, hs, fun j => memberFacts_of_left cs G Fr π _ _ smp mem a.2 a0 Y he hp t0
    tE rs gs hy s0 rest0 G00 Ly0 D0 hf row₀ hok hcs j (xs j) (es j) (hM j)⟩

/-! ## The two «there is» parted -/

/-- **`MemberLeft` with the canonical OOD seed's «there is» BESIDE clause (6)'s, not under it.** In
`MemberFacts` clauses (2) and (6) have each a witness of its own, and no seed
crosses from the one to the other; `MemberLeft` had merged the two, so that a payer of «every
coordinate is canonical» had to speak of clause (6)'s very seed. Here clause (6) stands as in
`MemberFacts`; where the shape has rows of both kinds, ONE seed is asked that makes the stored
sample row and is canonical:
the
premise of `hQ_of_yesA` less «the message is sampled». `seedOk_reads`
(Johnson/RunOne/KeySeedOk.lean) concludes that form. -/
def MemberLeft₂ (cs : Codes) {Xi A : Type} (G : FileDescription Xi) (Fr : Frame) (no : ℕ → ℕ)
    (rad : Sg → ℕ)
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (mem : ℕ → Option Mem) (y : Fr.E.Str) (a0 : A) (Y : Strs) (a : Fmt.M1.Stage) (D : Plain)
    (j : Fin D.mems.length) (x : Mem) (e0 : ℕ) : Prop :=
  (D.mems.get j).sh.answers = 1 ∧
  ((0 < (D.mems.get j).sh.maskRows ∨ (D.mems.get j).sh.mainDeg = 3) ∨
    ((D.mems.get j).sh.maskRows = 0 ∧ (D.mems.get j).sh.mainDeg = 1)) ∧
  ((0 < (D.mems.get j).sh.mainRows ∧
      ((D.mems.get j).sh.maskRows = 0 → cs.mask.size ≤ (D.mems.get j).sh.maskCode)) ∨
    (0 < (D.mems.get j).sh.maskRows ∧ cs.base.size ≤ (D.mems.get j).sh.code ∧
      (D.mems.get j).tsh.logN ≤ a.Z.a)) ∧
  rad (sgOf a) < (e0 + 1) * 2 ^ ((sgOf a).C.a - aOf cs (D.mems.get j).sh) ∧
  x.1.l.get x.2 = ((D.mems.get j).sh, e0) ∧
  mem (D.mems.get j).id = some x ∧
  (∃ (o : OnBytes.Oracle) (seed : SampleSeed) (row0 : OnBytes.Row) (tt : E) (β : GEˣ),
    D.st.oracles[(D.mems.get j).id]? = some o ∧
    Send.form cs (D.mems.get j).sh (D.mems.get j).id seed 0 = some row0 ∧
    o.sampleRows.toList = [{ row0 with target := tt }] ∧
    bitsZ cs (D.mems.get j).sh ≤ seed.z.length ∧ (β : GE) = readE seed.beta ∧
    ∃ (z σ' : ((sigOf cs x.1.l).om x.2).Smp), smp a0 x.1 x.2 = some z ∧
      HEq (((readP (bitsZ cs (D.mems.get j).sh) seed.z, β), fun _ => readE tt) :
        (portOmZ cs (D.mems.get j).sh e0).Smp) σ' ∧ z.2 = σ'.2 ∧
      ((sigOf cs x.1.l).om x.2).Z.val z.1 = ((sigOf cs x.1.l).om x.2).Z.val σ'.1) ∧
  (¬ (0 < (D.mems.get j).sh.mainRows ∧ 0 < (D.mems.get j).sh.maskRows) ∨
    ∃ (o : OnBytes.Oracle) (seed : SampleSeed) (row0 : OnBytes.Row) (tt : E) (β : GEˣ),
      D.st.oracles[(D.mems.get j).id]? = some o ∧
      Send.form cs (D.mems.get j).sh (D.mems.get j).id seed 0 = some row0 ∧
      o.sampleRows.toList = [{ row0 with target := tt }] ∧
      bitsZ cs (D.mems.get j).sh ≤ seed.z.length ∧ (β : GE) = readE seed.beta ∧
      ∀ c ∈ seed.z, okE c = true) ∧
  HEq (strOf cs (D.mems.get j).sh e0 (layOf (D.mems.get j))
      (W0 Fr no D.book y (D.mems.get j).t).1 (W0 Fr no D.book y (D.mems.get j).t).2)
    (VerifiableInference.Desc.Sound.wordsOf G cs x.1.l x.1.seat Y x.2)

/-- The merged form gives the parted one: whoever pays `MemberLeft` pays `MemberLeft₂`. -/
theorem MemberLeft.parted {cs : Codes} {Xi A : Type} {G : FileDescription Xi} {Fr : Frame} {no : ℕ → ℕ}
    {rad : Sg → ℕ}
    {smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp}
    {mem : ℕ → Option Mem} {y : Fr.E.Str} {a0 : A} {Y : Strs} {a : Fmt.M1.Stage} {D : Plain}
    {j : Fin D.mems.length} {x : Mem} {e0 : ℕ}
    (h : MemberLeft cs G Fr no rad smp mem y a0 Y a D j x e0) :
    MemberLeft₂ cs G Fr no rad smp mem y a0 Y a D j x e0 := by
  obtain ⟨h1, hcase, hsite, h3, h4, h5, ⟨o, seed, row0, tt, β, e1, e3, e4, e5, e6, e7, e8⟩, h7⟩ := h
  exact ⟨h1, hcase, hsite, h3, h4, h5, ⟨o, seed, row0, tt, β, e1, e4, e5, e6, e7, e8⟩,
    e3.imp id fun hall => ⟨o, seed, row0, tt, β, e1, e4, e5, e6, e7, hall⟩, h7⟩

/-- **A member's seven clauses, from the parted remainder and the two «accept»s.** -/
theorem memberFacts_of_left₂ (cs : Codes) {Xi A : Type} (G : FileDescription Xi) (Fr : Frame) (π : P12)
    (no : ℕ → ℕ) (rad : Sg → ℕ)
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (mem : ℕ → Option Mem) (y : Fr.E.Str) (a0 : A) (Y : Strs) (he : π.early = true)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (t tE : T12) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).decide t rs gs = .ok tE) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain)
    (hf : Fixes π t a rest G0 Ly D) (row : GroupRow)
    (hok : H2K.First.ok (gpL π a row D) = true) (hcs : D.st.codes = cs)
    (j : Fin D.mems.length) (x : Mem) (e0 : ℕ)
    (hL : MemberLeft₂ cs G Fr no rad smp mem y a0 Y a D j x e0) :
    MemberFacts cs G Fr no rad smp mem y a0 Y a D j x e0 := by
  subst hcs
  obtain ⟨h1, hcase, hsite, h3, h4, h5, ⟨o, seed, row0, tt, β, e1, e4, e5, e6, e7, e8⟩, e3, h7⟩ :=
    hL
  have hsome : 0 < (D.mems.get j).sh.mainRows ∨ 0 < (D.mems.get j).sh.maskRows :=
    hsite.elim (fun s => Or.inl s.1) fun s => Or.inr s.1
  have smpd : ∀ o' : OnBytes.Oracle, D.st.oracles[(D.mems.get j).id]? = some o' →
      o'.sampled = true := by
    intro o' q
    obtain ⟨o'', q1, q2, _⟩ := sampled_of_decide π t tE rs gs h a rest G0 Ly D hf j
    obtain rfl : o'' = o' := Option.some.inj (q1.symm.trans q)
    exact q2
  refine ⟨?_, ?_, h3, h4, h5, ⟨o, seed, row0, tt, β, e1, e4, e5, e6, e7, e8⟩, h7⟩
  · rcases hsite with ⟨s1, s2⟩ | ⟨s1, s2, s3⟩
    · exact site_long π a row D hok j s1 s2
    · exact site_mask π a row D hok j s1 s2 s3
  · rcases e3 with hone | ⟨o₂, seed₂, row₂, tt₂, β₂, f1, f4, f5, f6, f7, hall⟩
    · exact hQ_of_yes π he hp t tE rs gs h a rest G0 Ly D hf row hok j
        ⟨o, seed, row0, tt, β, e1, smpd o e1, e4, e5, e6, e7⟩ h1 hone hsome hcase
    · exact hQ_of_yesA π he hp t tE rs gs h a rest G0 Ly D hf row hok j
        ⟨o₂, seed₂, row₂, tt₂, β₂, f1, smpd o₂ f1, f4, f5, f6, f7, hall⟩ h1 hsome hcase

/-- **The seam's core behind QW, member by member, at the parted remainder.** -/
theorem core_behind_QWm₂ {P S Xi A : Type} (cs : Codes) (G : FileDescription Xi) (Fr : Frame) (π : P12)
    (nl : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (mem : ℕ → Option Mem) (sits : Mem → Prop)
    (rd : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP cs (x.1.l.get x.2).1 m part i)
    (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (a b : (P × S) × Fr.E.Str) (a0 : A) (Y : Strs) (h : QW Fr π nl r rdN enter leave a b)
    (hj : johOk π r = true) (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (left : ∀ t, enter a.1.2 = .ok t → ∀ (s : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
      (G0 : Group) (Ly : GroupLayout) (D : Plain), Fixes π t s rest G0 Ly D →
      D.st.codes = cs ∧
      ∃ (xs : Fin D.mems.length → Mem) (es : Fin D.mems.length → ℕ), Function.Injective xs ∧
        (∀ z, sits z → ∃ j, xs j = z) ∧
        ∀ j : Fin D.mems.length,
          MemberLeft₂ cs G Fr (nuOf π nl t) (fun q => r q.st) smp mem a.2 a0 Y s D j (xs j) (es j))
    (hI : ∀ t, enter a.1.2 = .ok t → InOrder t.st) :
    ∃ t G0, enter a.1.2 = .ok t ∧ t.st.groups[t.g]? = some G0 ∧
      ∃ m : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg,
        AllSay OnBytes.Model.Reading.gl (begun t.st t.g G0) (runRows t.st G0).toList
          (_root_.Desc.K14.Law.wordsT cs mem rd m) ∧
        ∀ x, sits x → CandAt cs G smp x a0 Y (m x) := by
  have he := H2K.JointK.early_of_planOk π hp
  obtain ⟨t0, tE, h1, _, hq, rs, gs, hy⟩ := id h
  obtain ⟨s0, rest0, G00, Ly0, D0, hf0, row₀, hok, _⟩ := id hq
  refine core_behind_QWn cs G Fr π nl r rdN smp mem sits rd hrd enter leave a b a0 Y h hj he hp
    (fun t ht => ?_) hI
  obtain rfl : t0 = t := Except.ok.inj (h1.symm.trans ht)
  refine coreLeft_of_members cs G Fr π _ _ smp mem sits t0 a.2 a0 Y fun s rest G0 Ly D hf => ?_
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := fixes_one π t0 hf0 hf
  obtain ⟨hcs, xs, es, hinj, hs, hM⟩ := left t0 ht s0 rest0 G00 Ly0 D0 hf
  exact ⟨hcs, xs, es, hinj, hs, fun j => memberFacts_of_left₂ cs G Fr π _ _ smp mem a.2 a0 Y he hp
    t0 tE rs gs hy s0 rest0 G00 Ly0 D0 hf row₀ hok hcs j (xs j) (es j) (hM j)⟩

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.memberFacts_of_left
#print axioms VerifiableInference.Desc.K12.Coin.core_behind_QWm
#print axioms VerifiableInference.Desc.K12.Coin.MemberLeft.parted
#print axioms VerifiableInference.Desc.K12.Coin.memberFacts_of_left₂
#print axioms VerifiableInference.Desc.K12.Coin.core_behind_QWm₂
