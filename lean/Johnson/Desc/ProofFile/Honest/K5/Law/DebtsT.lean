-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/DebtsT.lean: CONDITIONAL: the debts of the member at an
attention segment's own rounds (kind K5) WITH THE `Thread` T A VARIABLE: every fact on T's letters
that is spent is a named premise: the structure `K5AtT` (Honest/K5/Law/AtT.lean), `K5Seated`
(Honest/K5/Law/Seated.lean), the test `Thread.fits`, and sentences on T.keeps, T.rides and the
honest side's letter ans.

How. The proofs are those of Honest/K5/Law/Ready.lean, Front.lean, Accepted.lean, Keeps.lean,
Behind.lean and Exchange.lean, with the unfolding of the first chain's `Thread` at the library's own
letters replaced by the structure's fields. What these proofs spend of the hypothesis `P5J.AtMgA`
alone is cut out first, as laws without a `Thread` (section 1).

  1  `readyO_of_front`, `onAt_next`, `next_of_front`, `ctx_rides_head`   no `Thread`: from "no mark,
     and the table's promise at the kind's place": the state is ready; the promise at the stepped
     open sets is the promise at the next border's own; the promise behind the lay; the three items
     that are read and owed again say behind what they say in front
  2  `reach_T`, `onAt_T`, `readyO_T`, `keeps_T`   what `Thr` T in front hands over, under the
     structure
  3  `k5_accepted_T`   **`Accepted` T fall b, for every fall**
  4  `k5_behind_T`     **`Behind` T b**
  5  `SayOwedT`, `JoinOwedT`, `k5_exchange_T`   **`Exchange` T b**, under two named premises that
     HOLD THE CLAUSE "each form is worth 0" of the items "own" and "join"
  6  `k5_owes_T`       the three and `Plays` T b in one statement

Limits. Every theorem but the last two, which unfold two definitions, is conditional. The hypothesis
is not shown here; the structure is shown of one `Thread` (`k5AtT_thrAt`). For "own" and "join"
`k5_exchange_T` is a frame, not a result on values. At the library's full size and the format's
second hash function alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.AtT

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Block Place OpenedColumn Strs Chain Claim First.S First.Pub First.rowOf
  noDigest)
open VerifiableInference.Desc.First.Att (P.inOf)
open VerifiableInference.Desc.First (Item onAt openSets pubSets start leavesName stepOpen pubStep
  pubRowM openSets_succ pubSets_succ)
open VerifiableInference.Desc.Sound (mgBase mgAll seatTab)
open VerifiableInference.Desc.First.Att.P
open H2K5.Door (moreOver9)
open H2K5.Honest (own_at_head join_at_head planes_item_at_head behind_at_head worldBehind K5Keeps)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile.Honest.FirstThread (Script WtF honest noStrs)
open P5J (AtMgA mgAtAll TS CellsM)

/-! ## 1 Without a `Thread` -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)

/-- **From "no mark, and the table's promise at the kind's place": the state is ready.**
CONDITIONAL: under the hypothesis h; g is below 12; the plan's facts; hu, hon. -/
theorem readyO_of_front {g : Nat} (hg : g < 12) {a : Attention.Plan} (Pl : PlanAt Zp g a)
    {π : ProofFile.InstPub} {s : TS} (hu : s.failed = none)
    (hon : onAt (P5J.At.N Zp cF) (honest (mgAtAll h) ans test) P5J.At.links
      (some ⟨1, some (2 * g + 1), 3, .K5⟩)
      (((openSets P5J.At.links P5J.At.ps (start P5J.At.links))[borderOf g]?).getD [])
      (((pubSets ((moreOver9 {}).strike leavesName) P5J.At.links P5J.At.ps)[borderOf g]?).getD [])
      (π, s) noStrs) : ReadyO (parAt Zp g a) s := by
  have Ix := place_k5 hg
  have T := H2K5.Door.dataIs_all h (2 * g + 1)
  obtain ⟨x₁, hx⟩ := Pl.look
  exact readyO_of_onAt (Mg := honest (mgAtAll h) ans test) h.𝔇.pubD _ (H2K5.Door.hpub_all h) Ix
    (H2K5.Door.isAtt_of _ (by rw [T.d5links]; exact Ix.sub))
    (H2K5.Door.att_not_lay (by rw [T.links]; exact Ix.sub))
    (H2K5.Door.first_at _ (by rw [T.d5W]; exact Pl.planIs) (by rw [T.d5W]; exact Pl.p4)
      (by rw [T.d5W]; exact Pl.plan) (by rw [T.d5W]; exact hx))
    (H2K5.Door.nsOf_all h hg Pl.plan) (parAt Zp g a) Pl.fits
    (open_k5 hg _ (by simp)) (open_k5 hg _ (by simp)) (open_k5 hg _ (by simp)) hu hon

/-- **The promise at the open sets stepped by the kind's two rows is the promise at the next
border's own open sets.** CONDITIONAL: g is below 12; the promise. -/
theorem onAt_next {g : Nat} (hg : g < 12) {π : ProofFile.InstPub} {s' : TS}
    (hon : onAt (P5J.At.N Zp cF) (honest (mgAtAll h) ans test) P5J.At.links
      (some ⟨1, some (2 * g + 1), 4, .K1⟩)
      (stepOpen (((openSets P5J.At.links P5J.At.ps (start P5J.At.links))[borderOf g]?).getD [])
        (First.rowOf P5J.At.links ⟨1, some (2 * g + 1), 3, .K5⟩))
      (pubStep
        (((pubSets ((moreOver9 {}).strike leavesName) P5J.At.links P5J.At.ps)[borderOf g]?).getD [])
        (pubRowM ((moreOver9 {}).strike leavesName) P5J.At.links ⟨1, some (2 * g + 1), 3, .K5⟩))
      (π, s') noStrs) :
    onAt (P5J.At.N Zp cF) (honest (mgAtAll h) ans test) P5J.At.links
      (P5J.At.ps[borderOf g + 1]?)
      (((openSets P5J.At.links P5J.At.ps (start P5J.At.links))[borderOf g + 1]?).getD [])
      (((pubSets (honest (mgAtAll h) ans test).more P5J.At.links P5J.At.ps)[borderOf g + 1]?).getD
        [])
      (π, s') noStrs := by
  have hpl : P5J.At.ps[borderOf g]? = some ⟨1, some (2 * g + 1), 3, .K5⟩ :=
    H2K5.Door.place_full hg
  have hnx : P5J.At.ps[borderOf g + 1]? = some ⟨1, some (2 * g + 1), 4, .K1⟩ :=
    H2K5.Door.next_full hg
  have hm : (honest (mgAtAll h) ans test).more = (moreOver9 {}).strike leavesName :=
    H2K5.Door.hm_all h
  rw [hnx, hm, openSets_succ _ _ _ _ _ hpl, pubSets_succ _ _ _ _ _ hpl]
  exact hon

/-- **The promise at the next border, behind the lay.** CONDITIONAL: under the hypothesis h; g is
below 12; ha; hr, hu, hon: the state in front is reached, bears no mark and meets the promise; e,
hh: the open segment, and the hearing's return. -/
theorem next_of_front {g : Nat} (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {π : ProofFile.InstPub} {s : TS}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (borderOf g) (π, s)) (hu : s.failed = none)
    (hon : onAt (P5J.At.N Zp cF) (honest (mgAtAll h) ans test) P5J.At.links
      (some ⟨1, some (2 * g + 1), 3, .K5⟩)
      (((openSets P5J.At.links P5J.At.ps (start P5J.At.links))[borderOf g]?).getD [])
      (((pubSets ((moreOver9 {}).strike leavesName) P5J.At.links P5J.At.ps)[borderOf g]?).getD [])
      (π, s) noStrs)
    {att : VerifiableInference.Desc.First.AttOwn} (e : s.here = .att att) {rs : List Fmt.RoundView}
    {hd5 : Heard} {G : Fork} (hh : hear a.own (att.F, rs, 0) = some (hd5, G, [], 0)) :
    onAt (P5J.At.N Zp cF) (honest (mgAtAll h) ans test) P5J.At.links
      (P5J.At.ps[borderOf g + 1]?)
      (((openSets P5J.At.links P5J.At.ps (start P5J.At.links))[borderOf g + 1]?).getD [])
      (((pubSets (honest (mgAtAll h) ans test).more P5J.At.links P5J.At.ps)[borderOf g + 1]?).getD
        [])
      (π, behind s att hd5 G) noStrs := by
  obtain ⟨L, hL⟩ := P5J.At.laid_some Zp h.opts.laid
  have hm : (honest (mgAtAll h) ans test).more = (moreOver9 {}).strike leavesName :=
    H2K5.Door.hm_all h
  have hb := behind_at_head h hL hg ha (honest (mgAtAll h) ans test)
    (honestLike_at h ans test) _ _ (atBorder_at hg)
    (Fr := ⟨0, [], fun _ => 0, 0⟩) (bs := 0) (y := (fun _ => (0, []), fun _ => []))
    (y' := (fun _ => (0, []), fun _ => [])) ⟨rfl, fun _ _ _ => rfl⟩ hr hu hon e hh
  rw [hm] at hb
  exact onAt_next h ans test hg hb

/-- **The three items that the kind's row reads and owes again** say behind the step what they say
in front, of any witness, at the table's own sentence. CONDITIONAL: under the hypothesis h; g is
below 12; `K5Keeps`; for the pin of the first sending, `AnsReadsRest`. c, carryX: letters. -/
theorem ctx_rides_head (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (c : CellsM OnBytes.Flat.numsFull) {g : Nat} (hg : g < 12) {s s' : TS} (hK : K5Keeps s s')
    (hans : AnsReadsRest ans ((P5J.At.N Zp cF).sent (2 * g + 1) 0)) (π : ProofFile.InstPub) (y : Strs)
    (v : WtF) (i : Item)
    (hi : i ∈ [Item.pin (2 * g + 1) 0, Item.pinW, Item.constr (2 * g + 1) .small])
    (hm : Item.holds (P5J.At.N Zp cF)
      (honest (mgAll { h.𝔇 with decT := fun _ _ => some c, cr1 := carryX } mgBase) ans test)
      i (π, s) y v) :
    Item.holds (P5J.At.N Zp cF)
      (honest (mgAll { h.𝔇 with decT := fun _ _ => some c, cr1 := carryX } mgBase) ans test)
      i (π, s') y v := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact fun z hz => hans z hz _ _ _ _ _ hK (hm z hz)
  · exact hm
  · obtain ⟨-, a, -, Pl, -⟩ := k5_member h hg
    have hne : 2 * g + 1 ≠ VerifiableInference.OnPublicFiles.headLink (P5J.At.X Zp) := by
      unfold VerifiableInference.OnPublicFiles.headLink
      rw [Pl.p4]
      simp only [if_true]
      omega
    have hm' : (mgAll { h.𝔇 with decT := fun _ _ => some c, cr1 := carryX } mgBase).constr
        (2 * g + 1) .small (π, s) y v := hm
    show (mgAll { h.𝔇 with decT := fun _ _ => some c, cr1 := carryX } mgBase).constr
      (2 * g + 1) .small (π, s') y v
    have h1 := (H2K5.Door.constrIs_any _ mgBase _ _ _ _ _).1 hm'
    refine (H2K5.Door.constrIs_any _ mgBase _ _ _ _ _).2 ?_
    rw [if_neg (by decide)] at h1 ⊢
    exact ⟨h1.1, fun M i hM hH => H2K5.Door.bodySmall_any _ hne i _ _ _ _ _ (h1.2 M i hM hH)⟩

end

/-! ## 2 What `Thr` T in front hands over, under the structure -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  {T : Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst}
  {g : Nat} {it : Item → T.ι} {pb : T.P → ProofFile.InstPub} {wt : T.Wt → WtF}
  {ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop} {test : Nat → TS → Option String}
  {carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop}
  {cq : (Local W₀ Rc ProofFile.Inst Tr) → CellsM OnBytes.Flat.numsFull}
  (R : K5AtT h T g it pb wt ans test carryX cq)
include R

/-- **The verifier's state at a border is reached**, over the description's own flat list.
CONDITIONAL: the structure (T.bs, T.ft, T.begun); `Thr` T at a border within the list. -/
theorem reach_T {b : Nat} (hb : b ≤ cF.blocksInOrder.length) {k : Coins Bk} {s : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} (hT : Thr T b k s m E) :
    Reach 0 cF.blocksInOrder (ProofFile.startS Zp) b (m.st.input.x.pub, s) := by
  have h1 := reach_of_made T (ProofFile.startS Zp) m.st.input.x.pub (by rw [R.bs]; exact hb)
    (fun s₀ e => R.begun _ _ _ _ e) hT.2.2.2.2.1
  rw [R.ft, R.bs] at h1
  exact h1

/-- **No mark, and the table's promise at the kind's place.** CONDITIONAL: the structure (T.form,
T.formP, T.handed); g is below 12; `Thr` T at the kind's border. -/
theorem onAt_T (hg : g < 12) {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {E : Env} (hT : Thr T (borderOf g) k s m E) :
    s.failed = none ∧
      onAt (P5J.At.N Zp cF) (honest (mgAtAll h) ans test) P5J.At.links
        (some ⟨1, some (2 * g + 1), 3, .K5⟩)
        (((openSets P5J.At.links P5J.At.ps (start P5J.At.links))[borderOf g]?).getD [])
        (((pubSets ((moreOver9 {}).strike leavesName) P5J.At.links P5J.At.ps)[borderOf g]?).getD [])
        (m.st.input.x.pub, s) noStrs := by
  obtain ⟨hf0, hon0⟩ := hT.2.2.1
  rw [R.form _ (Or.inl rfl)] at hf0
  have hon := (R.formP _ (Or.inl rfl) _).1 hon0
  have hp : pb (T.seat k m s).1 = m.st.input.x.pub := R.handed _ _ _
  have hpl : P5J.At.ps[borderOf g]? = some ⟨1, some (2 * g + 1), 3, .K5⟩ :=
    H2K5.Door.place_full hg
  have hm : (honest (mgAtAll h) ans test).more = (moreOver9 {}).strike leavesName :=
    H2K5.Door.hm_all h
  rw [hp, hpl, hm] at hon
  exact ⟨Option.isNone_iff_eq_none.1 hf0, hon⟩

/-- **The state in front of the member is ready.** CONDITIONAL: the structure; g is below 12; the
plan's facts; `Thr` T at the kind's border. -/
theorem readyO_T (hg : g < 12) {a : Attention.Plan} (Pl : PlanAt Zp g a) {k : Coins Bk} {s : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} (hT : Thr T (borderOf g) k s m E) :
    ReadyO (parAt Zp g a) s := by
  obtain ⟨hu, hon⟩ := onAt_T h R hg hT
  exact readyO_of_front h ans test hg Pl hu hon

/-- The member decides as the kind's decision. CONDITIONAL: the structure (T.bs); g is below 12; ha;
blk is T's member at the border. -/
theorem decides_T (hg : g < 12) {a : Attention.Plan} (ha : (P5J.At.X Zp).A[g]? = some a)
    {blk : Block TS ProofFile.Cl} (hb : T.bs[borderOf g]? = some blk) :
    PlanAt Zp g a ∧ DecidesAs (parAt Zp g a) blk :=
  seated_decides h hg ha (by rw [← R.bs]; exact hb)

/-- **What the member's step leaves.** CONDITIONAL: the structure; `K5Seated`; `Thr` T in front; the
step's yes. -/
theorem keeps_T (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl} (Hs : K5Seated T (borderOf g) cells Z5 (parAt Zp g a) blk)
    {k : Coins Bk} {s s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X} {cols : List OpenedColumn}
    (hT : Thr T (borderOf g) k s m E) (hd : drawsFit blk.rounds ds = true)
    (hS : T.Stepped blk k s m E ds y cols s') : K5Keeps s s' := by
  obtain ⟨Pl, Dc⟩ := decides_T h R hg ha Hs.member
  exact keeps_of_ready _ Hs Dc (readyO_T h R hg Pl hT) hd hS

/-! ## 3 Accepted -/

/-- **IT IS ACCEPTED, AT T's MEMBER AT THE KIND's BORDER OF GROUP g, FOR EVERY fall.** T IS A
VARIABLE. CONDITIONAL: under the hypothesis h, the structure `K5AtT` and `K5Seated`. -/
theorem k5_accepted_T (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl} (Hs : K5Seated T (borderOf g) cells Z5 (parAt Zp g a) blk)
    (fall : Nat → TS → List Fmt.Drawn → Option String) : Accepted T fall (borderOf g) := by
  obtain ⟨Pl, Dc⟩ := decides_T h R hg ha Hs.member
  exact accepted_of_ready _ Hs Dc (fun k s m E hT => readyO_T h R hg Pl hT) fall

/-! ## 4 Behind -/

/-- **THE DEBT `Behind` AT T's MEMBER AT THE KIND's BORDER OF GROUP g.** T IS A VARIABLE.
CONDITIONAL: under the hypothesis h, the structure `K5AtT` and `K5Seated`; Kp: T.keeps at the border
holds wherever `K5Keeps` does; Rd: what T.rides says in front of the border it says behind, of every
state that `K5Keeps` ties to the one in front. Of the debt's four clauses, keeps and rides are
carried by Kp and Rd. -/
theorem k5_behind_T (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl} (Hs : K5Seated T (borderOf g) cells Z5 (parAt Zp g a) blk)
    (Kp : ∀ s s', K5Keeps s s' → T.keeps (borderOf g) s s')
    (Rd : ∀ w s s', T.rides (borderOf g) w s → K5Keeps s s' → T.rides (borderOf g + 1) w s') :
    Behind T (borderOf g) := by
  intro blk' hblk' k s m E ds y cols s' hT hd hS
  obtain rfl : blk = blk' := Option.some.inj (Hs.member.symm.trans hblk')
  obtain ⟨-, Dc⟩ := decides_T h R hg ha Hs.member
  have hK := keeps_T h R hg ha Hs hT hd hS
  have hf := form_behind _ Hs Dc hd hS
  obtain ⟨att, hd5, G, e, hh, rfl⟩ := behind_is _ Hs Dc hd hS
  obtain ⟨⟨l, -, hy⟩, -⟩ := hS.1
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  obtain ⟨hu, hon⟩ := onAt_T h R hg hT
  have hlt : borderOf g < cF.blocksInOrder.length := by
    rw [← R.bs]
    exact (List.getElem?_eq_some_iff.1 Hs.member).1
  have hr := reach_T h R (Nat.le_of_lt hlt) hT
  refine ⟨⟨?_, ?_⟩, ?_, Kp _ _ hK⟩
  · rw [R.form _ (Or.inr rfl)]
    show (behind s att hd5 G).failed.isNone = true
    rw [hf]
    rfl
  · refine (R.formP _ (Or.inr rfl) _).2 ?_
    have hp : pb (T.seat k y.2 (behind s att hd5 G)).1 = m.st.input.x.pub := by
      rw [← ei]
      exact R.handed _ _ _
    rw [hp]
    exact next_of_front h ans test hg ha hr hu hon e hh
  · rw [ei]
    exact Rd _ _ _ hT.2.2.2.2.2.1 hK

end

/-! ## 5 Exchange -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  (T : Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst)
  (wt : T.Wt → WtF)

/-- **A premise's form, for "own", with T a variable**: along every step of T's member at the border
from `Thr` T in front, at every continuation: what the claims say holds in the item's own world, at
whatever the claims' reading at the state behind returns. It is a definition. Nothing is claimed of
it. -/
def SayOwedT (g : Nat) (a : Attention.Plan) : Prop :=
  ∀ (blk : Block TS ProofFile.Cl) (k : Coins Bk) (s s' : TS) (m : Mid (Local W₀ Rc ProofFile.Inst Tr) X)
    (E : Env) (ds : List Fmt.Drawn) (y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X)
    (cols : List OpenedColumn),
    T.bs[borderOf g]? = some blk → Thr T (borderOf g) k s m E → drawsFit blk.rounds ds = true →
    T.Stepped blk k s m E ds y cols s' →
    ∀ ds' att hd5 G gL, s.here = .att att → att.g = some gL → s' = behind s att hd5 G →
      ∀ i K, P.inOf (seatCO (parCOf a)) (parCOf a) (behind s att hd5 G) = some (i, K) →
        K5Law.SayAt Reading.gl
          (worldBehind h.𝔇.St (h.𝔇.pubD.N.sent (2 * g + 1) 0) s att hd5 G
            (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms
            (wt (T.wit k y.2.st.input (y.2.st.heard ++ ds'))))) a.S gL i K

/-- **A premise's form, for "join", with T a variable**: along every such step, at every
continuation: whatever form the lookup's text returns on the segment's key forms at the state behind
is worth 0 in the item's own world. It is a definition. Nothing is claimed of it. -/
def JoinOwedT (g : Nat) (a : Attention.Plan) : Prop :=
  ∀ (blk : Block TS ProofFile.Cl) (k : Coins Bk) (s s' : TS) (m : Mid (Local W₀ Rc ProofFile.Inst Tr) X)
    (E : Env) (ds : List Fmt.Drawn) (y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X)
    (cols : List OpenedColumn),
    T.bs[borderOf g]? = some blk → Thr T (borderOf g) k s m E → drawsFit blk.rounds ds = true →
    T.Stepped blk k s m E ds y cols s' →
    ∀ ds' att hd5 G, s.here = .att att → s' = behind s att hd5 G →
      ∀ (gL : Forest.Heard) (kf : Array Aff) (z : Aff × Fork × OnBytes.K.Kc.Tape),
        att.lookHeard = some gL →
        keysOfK (seatCO (parCOf a)) (parCOf a) (behind s att hd5 G) = some kf →
        VerifiableInference.Desc.First.Look.joinF gL kf G [] = some z →
        z.1.value Reading.gl
          (worldBehind h.𝔇.St (h.𝔇.pubD.N.sent (2 * g + 1) 0) s att hd5 G
            (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms
            (wt (T.wit k y.2.st.input (y.2.st.heard ++ ds'))))) = 0

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  {T : Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst}
  {g : Nat} {it : Item → T.ι} {pb : T.P → ProofFile.InstPub} {wt : T.Wt → WtF}
  {ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop} {test : Nat → TS → Option String}
  {carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop}
  {cq : (Local W₀ Rc ProofFile.Inst Tr) → CellsM OnBytes.Flat.numsFull}
  (R : K5AtT h T g it pb wt ans test carryX cq)
include R

/-- **THE DEBT `Exchange` AT T's MEMBER AT THE KIND's BORDER OF GROUP g.** T IS A VARIABLE.
CONDITIONAL: under the hypothesis h, the structure `K5AtT`, `K5Seated`, the test T.fits, the letter
ans at the first sending's tenants, and the two named premises `SayOwedT`, `JoinOwedT`, WHICH HOLD
THE CLAUSE "each form is worth 0" of two of the six items. -/
theorem k5_exchange_T {n : Nat} (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl} (Hs : K5Seated T (borderOf g) cells Z5 (parAt Zp g a) blk)
    (hfit : T.fits n = true) (hb : borderOf g < n)
    (hans : AnsReadsRest ans ((P5J.At.N Zp cF).sent (2 * g + 1) 0))
    (hSay : SayOwedT h T wt g a) (hJ : JoinOwedT h T wt g a) : Exchange T (borderOf g) := by
  intro blk' hblk' k s m E ds y cols s' hT hd hS ds' i hi
  obtain rfl : blk = blk' := Option.some.inj (Hs.member.symm.trans hblk')
  rw [R.owes] at hi
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
  refine (R.means j (Or.inr hj) _ _ _ _).2 ?_
  obtain ⟨Pl, Dc⟩ := decides_T h R hg ha Hs.member
  have hK := keeps_T h R hg ha Hs hT hd hS
  have hSay' := hSay blk k s s' m E ds y cols Hs.member hT hd hS ds'
  have hJ' := hJ blk k s s' m E ds y cols Hs.member hT hd hS ds'
  obtain ⟨att, hd5, G, e, hh, rfl⟩ := behind_is _ Hs Dc hd hS
  obtain ⟨L, hL⟩ := P5J.At.laid_some Zp h.opts.laid
  obtain ⟨x₁, hx⟩ := Pl.look
  obtain ⟨hu, hon⟩ := onAt_T h R hg hT
  have hlt : borderOf g < cF.blocksInOrder.length := by
    rw [← R.bs]
    exact (List.getElem?_eq_some_iff.1 Hs.member).1
  have hr := reach_T h R (Nat.le_of_lt hlt) hT
  obtain ⟨⟨l, -, hy⟩, -⟩ := hS.1
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  have eh := play_heard _ _ _ _ _ hy
  have hp : pb (T.seat k y.2 (behind s att hd5 G)).1 = m.st.input.x.pub := by
    rw [← ei]
    exact R.handed _ _ _
  have hp0 : pb (T.seat k m s).1 = m.st.input.x.pub := R.handed _ _ _
  have hfit' := hfit
  unfold Thread.fits at hfit'
  simp only [Bool.and_eq_true] at hfit'
  have hopen : ∀ q, q ∈ asked7 (2 * g + 1) → it q ∈ T.opened (borderOf g) := fun q hq =>
    mem_of_fwdFit hfit'.1.1.1.1 hb (by rw [R.asks]; exact List.mem_map.2 ⟨q, hq, rfl⟩)
  have front : ∀ q (hq : q ∈ asked7 (2 * g + 1)),
      Item.holds (P5J.At.N Zp cF)
        (honest (mgAll { h.𝔇 with decT := fun _ _ => some (cq m.st.input), cr1 := carryX } mgBase)
          ans test)
        q (m.st.input.x.pub, s) (T.strs E) (wt (T.wit k m.st.input (m.st.heard ++ (ds ++ ds')))) :=
    fun q hq => by
      have h0 := (R.means q (Or.inl hq) _ _ _ _).1 (hT.2.2.2.1 (ds ++ ds') _ (hopen q hq))
      rw [hp0] at h0
      exact h0
  rw [hp]
  rcases List.mem_cons.1 hj with rfl | hj
  · obtain ⟨att', gL, e', hgL, -⟩ := (readyO_T h R hg Pl hT).open_
    rw [e] at e'
    cases e'
    exact ⟨own_at_head h hL hg ha hx (honest (mgAtAll h) ans test) rfl rfl _ _ (open8_at hg) hr hu
      hon e hh h.𝔇.St _ hgL (hSay' att hd5 G gL e hgL rfl), fun hw => nomatch hw⟩
  rcases List.mem_cons.1 hj with rfl | hj
  · have h1 := planes_item_at_head h hL hg ha hx (honest (mgAtAll h) ans test) rfl rfl _ _
      (open8_at hg) (open_k5 hg _ (by simp)) hr hu hon e hh (T.strs E) (T.strs (E.add y.1))
      (front _ (List.mem_cons_of_mem _ List.mem_cons_self))
    rw [ei, eh, List.append_assoc]
    exact h1
  rcases List.mem_cons.1 hj with rfl | hj
  · exact ⟨join_at_head h hL hg ha hx (honest (mgAtAll h) ans test) rfl rfl _ _ (open8_at hg) hr hu
      hon e hh h.𝔇.St _ (hJ' att hd5 G e rfl), fun hw => nomatch hw⟩
  have hE := (k5_env _ Hs hd hT.2.2.2.2.1.2.2.2.1 hS.1).1
  have hq : j ∈ asked7 (2 * g + 1) :=
    List.mem_append_right [Item.constr (2 * g + 1) .idn, .worth (2 * g + 1) 2 "planes",
      .worth (2 * g + 1) 2 "keys", .worth (2 * g + 1) 2 "rider"] hj
  have h1 := ctx_rides_head h ans test carryX (cq m.st.input) hg hK hans _ _ _ j hj (front j hq)
  rw [hE, ei, eh, List.append_assoc]
  exact h1

/-! ## 6 In one statement -/

/-- **THE MEMBER's DEBTS IN ONE STATEMENT, WITH T A VARIABLE**: it plays; behind its yes; the
exchange; it is accepted, for every fall. CONDITIONAL: under all premises of `k5_behind_T` and
`k5_exchange_T`. The riders' debt is not among them. -/
theorem k5_owes_T {n : Nat} (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl} (Hs : K5Seated T (borderOf g) cells Z5 (parAt Zp g a) blk)
    (hfit : T.fits n = true) (hb : borderOf g < n)
    (Kp : ∀ s s', K5Keeps s s' → T.keeps (borderOf g) s s')
    (Rd : ∀ w s s', T.rides (borderOf g) w s → K5Keeps s s' → T.rides (borderOf g + 1) w s')
    (hans : AnsReadsRest ans ((P5J.At.N Zp cF).sent (2 * g + 1) 0))
    (hSay : SayOwedT h T wt g a) (hJ : JoinOwedT h T wt g a) :
    Plays T (borderOf g) ∧ Behind T (borderOf g) ∧ Exchange T (borderOf g) ∧
      ∀ fall, Accepted T fall (borderOf g) :=
  ⟨k5_plays _ Hs, k5_behind_T h R hg ha Hs Kp Rd, k5_exchange_T h R hg ha Hs hfit hb hans hSay hJ,
    k5_accepted_T h R hg ha Hs⟩

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
    VerifiableInference.Desc.Sound.MsgT)
  (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
  (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
  (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
  (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (keeps : Nat → TS → TS → Prop)

/-- At the first chain's `Thread` at the library's own letters the two premises' forms are those of
Honest/K5/Law/Exchange.lean. No premise: by unfolding. -/
theorem sayOwedT_thrAt (g : Nat) (a : Attention.Plan) :
    SayOwedT h (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps)
      (fun v => v) g a ↔ SayOwed h hs Q stored ans test carryX item n₁ n₂ valid rides keeps g a :=
  Iff.rfl

/-- The same for "join". No premise: by unfolding. -/
theorem joinOwedT_thrAt (g : Nat) (a : Attention.Plan) :
    JoinOwedT h (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps)
      (fun v => v) g a ↔ JoinOwed h hs Q stored ans test carryX item n₁ n₂ valid rides keeps g a :=
  Iff.rfl

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.readyO_of_front
#print axioms ProofFile.Honest.K5.onAt_next
#print axioms ProofFile.Honest.K5.next_of_front
#print axioms ProofFile.Honest.K5.ctx_rides_head
#print axioms ProofFile.Honest.K5.reach_T
#print axioms ProofFile.Honest.K5.onAt_T
#print axioms ProofFile.Honest.K5.readyO_T
#print axioms ProofFile.Honest.K5.decides_T
#print axioms ProofFile.Honest.K5.keeps_T
#print axioms ProofFile.Honest.K5.k5_accepted_T
#print axioms ProofFile.Honest.K5.k5_behind_T
#print axioms ProofFile.Honest.K5.k5_exchange_T
#print axioms ProofFile.Honest.K5.k5_owes_T
#print axioms ProofFile.Honest.K5.sayOwedT_thrAt
#print axioms ProofFile.Honest.K5.joinOwedT_thrAt
