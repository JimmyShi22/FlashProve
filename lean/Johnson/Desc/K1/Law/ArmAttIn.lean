-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/ArmAttIn.lean: THE CLAUSE hin OF THE ATTENTION LINKS' HALF OF THE EXCHANGE ("the claims' seat's
reading returns, at the plan's number of columns") READ OFF THE PROMISE IN FRONT OF THE READS' PLACE ITSELF:
no fact along reached states is wanted for it.
HOW. The public item formsInT l 3 "own" is open at that border; it says yes at the run (2, "first"): so that
run's reader ANSWERS; at a link that is not the output head's the reader is the run itself; in the goals'
scope block 2 of an attention link is attention's files' own, alone, behind the guard; its run "first"
begins by the seat's reading: so the reading returns. Its number of columns is the ledger's array's: the
public item "ledger.treesAre" at l is open there too and pins it to the plan's list.
  `ownIn_mw` [kernel] · `ownIn_fails`   the two items are open in front of each attention link's reads, and
                   (2, "first") is among the first's runs; the test can fail
  `inOf_of_reader`   where the reader of (2, "first") answers, the seat's reading returns
  `inOf_cols`        its second value is the number of columns of the ledger's array number iU3
  `hin_at_reads`     **the clause hin inside the fence**
  `JFirst N s`       a clause for the letter J, at both sorts of link: FirstSeated (Johnson/Desc/K1/Law/ArmSyms.lean) at
                   the open link
  `hAtt2_ofB'` | `hAtt2_ofB`   **THE FIELD hAtt'' of k01_fifty_paid, IN ITS OWN TYPE** (its
                   text taken by program): hin off the promise; hM off symsSeatedB: of the state there stay
                   the clauses LiveIs and JFirst alone
Left as hypotheses on letters, seven in all: hDlk : Dm.links = linksFull · hWX : Bs.G₀.W = XV · hB :
symsSeatedB holds at each attention link · hsub : ∀ l < 25, ∀ u ∈ Dm.N.sent l 0, u ∈ Dm.N.group l ·
hlk : ∀ l < 25, Dm.lk l = c.links[l]? · hX24 : headLink XV = 24 ·
hKl : at an attention link the plan's
list's entry at the number of the array of the reads has plannedK Ap columns.
What is not claimed. hKl at any written value. Nothing on soundness.
The recursion limit is raised in this file (maxRecDepth 1000000): for the kernel's evaluations'
elaboration alone.

-/
import Johnson.Desc.K1.Law.ArmSyms
import Johnson.Desc.K1.Law.HbackMw1
import Johnson.Desc.First.Att.K05FormsMadeAt
import Johnson.Desc.First.PubAllAt
import Johnson.IMR.K5Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription Link Claim named)
open VerifiableInference.Desc.First (S AttOwn ModelPart Item Pub Meaning Numbers More flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull MsgT MgData CellsQ mgAll mgBase d13 rowQ linkNo runsAt seatTab)
open VerifiableInference.Desc.K13.Law (openAt plus13)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.K9 (readerOf statesOfLink readersOfLink holesAt formsInT)
open VerifiableInference.Desc.First.Att.P (plannedK inOf seatCO parCOf firstK runsN runN find_first named_some)
open VerifiableInference.OnPublicFiles (headLink)
open OnBytes.Model.Stages (LinkH)
open OnBytes.Params (Rounds)
open Iop Run OnBytes.Maker OnBytes.Flat
open Cb Johnson.Pack
open ProofFile (Cl)

/-- In front of each attention link's reads: the row closes formsT l 3 "own", (2, "first") is among its
runs, and "ledger.treesAre" at l is open. -/
def ownInB (n : ℕ) : Bool :=
  (List.range n).all fun l =>
    !((linksFull[l]?).getD .layers == .attention) ||
      ((rowQ linksFull (flatPlacesOf linksFull true) (noL l false)).ins.contains (.formsT l 3 "own") &&
        (runsAt linksFull l 3 "own").contains (2, "first") &&
        openB mwMore linksFull (flatPlacesOf linksFull true) (noL l false)
          (.more (some l) "ledger.treesAre"))

theorem ownIn_mw : ownInB 25 = true := by decide +kernel

/-- The test can fail: a feed-forward link's run is not among an attention link's. -/
theorem ownIn_fails : (runsAt linksFull 1 3 "own").contains (2, "front") = false := by
  decide +kernel

/-! ## 1 Where the reader of (2, "first") answers -/

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)} {c : Chain S Cl}
    {A₀ : ProofFile.SharedSeat} {B₀ : ProofFile.SecondSeat} 

/-- **Where the reader of (2, "first") answers, the seat's reading returns.** -/
theorem inOf_of_reader (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A₀ B₀) (g : ℕ) (hg : g < 12)
    (lk : Link S Cl) (eL : c.links[2 * g + 1]? = some lk) (s : S) (R : K9.Read)
    (h : readerOf (statesOfLink lk) 2 "first" s = some R) :
    ∃ Ap i K, Bs.G₀.W.A[g]? = some Ap ∧ inOf (seatCO (parCOf Ap)) (parCOf Ap) s = some (i, K) := by
  obtain ⟨Lk, b, b', a, e1, e2, k5, la, hA, _⟩ := IM.k5_of hS hR O g hg
  obtain rfl : lk = Lk := Option.some.inj (eL.symm.trans e1)
  unfold First.Att.P.k5AtN at k5
  obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 k5
  obtain rfl : q = a := Option.some.inj (hq.symm.trans hA)
  unfold readerOf at h
  obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.1 h
  have hst : statesOfLink lk 2 = (runsN q).map fun c => (c.1, IM.guardRun ProofFile.sameReply c.2) := by
    unfold statesOfLink
    rw [e2, Option.map_some, Option.getD_some, IM.claims_alone la]
    rfl
  rw [hst, List.find?_map] at hr
  obtain ⟨c0, hc0, rfl⟩ := Option.map_eq_some_iff.1 hr
  have hc1 : (runsN q).find? (fun x => x.1 == "first") = some c0 := hc0
  rw [find_first] at hc1
  obtain rfl := Option.some.inj hc1
  dsimp only at h
  cases hz : IM.guardRun ProofFile.sameReply
      (runN fun _ s => named "K5.first" (firstK (seatCO (parCOf q)) (parCOf q) s)) 0 s with
  | error e =>
    rw [hz] at h
    cases h
  | ok z =>
    obtain ⟨h1, _⟩ := (IM.guardRun_yes _ 0 s z).1 hz
    unfold runN at h1
    dsimp only at h1
    cases hn : named "K5.first" (firstK (seatCO (parCOf q)) (parCOf q) s) with
    | error e =>
      rw [hn] at h1
      cases h1
    | ok v =>
      have hf := named_some hn
      unfold firstK at hf
      obtain ⟨⟨i, K⟩, hi, _⟩ := Option.bind_eq_some_iff.1 hf
      exact ⟨q, i, K, hA, hi⟩

end

/-- The reading's second value is the number of columns of the ledger's array number iU3. -/
theorem inOf_cols {cp : First.Att.P.ParC} {s : S} {i : First.Att.P.Runs.In} {K : ℕ}
    (h : inOf (seatCO cp) cp s = some (i, K)) {a₀ : AttOwn} (hs : s.here = .att a₀) :
    (a₀.F.trees[cp.iU3]?).map (·.K) = some K := by
  unfold inOf at h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨K', hK, h⟩ := Option.bind_eq_some_iff.1 h
  obtain rfl : K' = K := (Prod.mk.inj (Option.some.inj h)).2
  have hK' : (match s.here with
    | .att a => (a.F.trees[cp.iU3]?).map (·.K)
    | _ => none) = some K' := hK
  rw [hs] at hK'
  exact hK'

/-! ## 2 Inside the fence -/

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)
  (Mg₀ : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))

/-- **The clause hin inside the fence.** -/
theorem hin_at_reads {J : S → Prop} (hM : Mg₀.more = {}) {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy}
    {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
    {base₀ : List (Block S Cl)} {c : Chain S Cl} {A₀ : ProofFile.SharedSeat} {B₀ : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A₀ B₀) (hDlk : Dm.links = linksFull)
    (hlk : ∀ l, l < 25 → Dm.lk l = c.links[l]?) (hX24 : headLink XV = 24) (hWX : Bs.G₀.W = XV)
    (hKl : ∀ l Ap t, (linksFull[l]?).getD .layers = .attention → XV.A[l / 2]? = some Ap →
      (Dm.pubD.dS.trees l)[Ap.iU3]? = some t → t.2.1 = plannedK Ap)
    {aN : ℕ} {R₁ R₂ R₃ : Rounds} {l : ℕ} {X : LinkH} {arrs : Option (List ℕ)}
    {x x' : ProofFile.InstPub × S} {y y' : Strs} {w : Wit (CellsQ rows cols) Tok MsgT} {p : ℕ × String}
    {A B : K9.Part} (Fc : ReadsFence Dm dk Mg₀ J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B)
    (hsub : (linksFull[l]?).getD .layers = .attention) {a₀ : AttOwn} {Ap : Attention.Plan}
    (hs : x.2.here = .att a₀) (hA : XV.A[l / 2]? = some Ap) :
    ∃ i, inOf (seatCO (parCOf Ap)) (parCOf Ap) x.2 = some (i, plannedK Ap) := by
  obtain ⟨el, hg⟩ := attIsOdd l Fc.lt hsub
  have t := List.all_eq_true.1 ownIn_mw l (List.mem_range.2 Fc.lt)
  rw [hsub] at t
  have t' : ((rowQ linksFull (flatPlacesOf linksFull true) (noL l false)).ins.contains
      (.formsT l 3 "own") && (runsAt linksFull l 3 "own").contains (2, "first") &&
      openB mwMore linksFull (flatPlacesOf linksFull true) (noL l false)
        (.more (some l) "ledger.treesAre")) = true := t
  obtain ⟨t12, t3⟩ := Bool.and_eq_true_iff.1 t'
  obtain ⟨t1, t2⟩ := Bool.and_eq_true_iff.1 t12
  have hIn' := inAt_down _ _ _ _ _ _ _ _ _ Fc.inAt
  have h0 := inAt_pub hIn' _ (List.mem_append_right _
    (formsInT_of_ins l Fc.lt 3 "own" (List.contains_iff_mem.1 t1)))
  rw [pub_plus13, First.pubAll_formsInT, List.all_eq_true] at h0
  have hin : formsInT (Dm.Rd l) (Dm.N.sent l 0) 2 "first" x.2 = true := h0 (2, "first") (by
    show (2, "first") ∈ runsAt Dm.links l 3 "own"
    rw [hDlk]
    exact List.contains_iff_mem.1 t2)
  obtain ⟨lk, _, _, _, e1, _⟩ := IM.k5_of hS hR O (l / 2) hg
  rw [← el] at e1
  have hRd : Dm.Rd l = readersOfLink (holesAt XV (headLink XV) l lk) lk :=
    K9.readersAt_some Dm.lk XV (headLink XV) l lk ((hlk l Fc.lt).trans e1)
  unfold formsInT at hin
  rw [Fc.front, hRd] at hin
  have hne : (l == headLink XV) = false := by
    rw [hX24]
    exact beq_false_of_ne (by omega)
  cases hr : readerOf (statesOfLink lk) 2 "first" x.2 with
  | none =>
    exfalso
    have e0 : (readersOfLink (holesAt XV (headLink XV) l lk) lk).forms 2 "first" x.2 = none := by
      simp [readersOfLink, holesAt, hr, hne]
    rw [e0] at hin
    cases hin
  | some R =>
    obtain ⟨Ap', i, K, hA', hi⟩ := inOf_of_reader hS hR O (l / 2) hg lk (by rw [← el]; exact e1) x.2 R hr
    obtain rfl : Ap' = Ap := Option.some.inj (hA'.symm.trans (by rw [hWX]; exact hA))
    refine ⟨i, ?_⟩
    obtain ⟨tr, htr, eK⟩ := Option.map_eq_some_iff.1 (inOf_cols hi hs)
    have hmem : Pub.more (some l) "ledger.treesAre" ∈
        (First.pubSets (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀)).more linksFull
          (flatPlacesOf linksFull true))[noL l false]?.getD [] ++
        First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l false)) := by
      have e : (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀)).more = mwMore :=
        plus13_more_closed Dm dk Mg₀ hM
      rw [e]
      exact open_of t3
    have h1 : (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).pub (.more (some l) "ledger.treesAre") x = true :=
      inAt_pub Fc.inAt _ hmem
    rw [pub_plus13, First.pubAll_more_treesAre] at h1
    unfold First.FillSent.treesAreB at h1
    have hF : x.2.fork? = some a₀.F := by
      unfold S.fork?
      rw [hs]
    rw [hF] at h1
    have h2 : a₀.F.trees.toList.map First.FillSent.treeLook = Dm.pubD.dS.trees l := by
      simpa using h1
    have h3 : (Dm.pubD.dS.trees l)[Ap'.iU3]? = some (First.FillSent.treeLook tr) := by
      rw [← h2, List.getElem?_map, Array.getElem?_toList]
      show Option.map _ (a₀.F.trees[(parCOf Ap').iU3]?) = _
      rw [htr]
      rfl
    have h4 : tr.K = plannedK Ap' := hKl l Ap' _ hsub hA h3
    rw [hi, ← eK, h4]

/-- **A CLAUSE FOR THE LETTER J, at both sorts of link**: at the state in front each message of the open link's
first commitment, and each kept one, is there and sits at a seat of that commitment. -/
def JFirst (N : Numbers) (s : S) : Prop :=
  ∀ A, K9.segAt? s = some A → FirstSeated (N.sent (linkNo s) 0) A (linkNo s)

/-- **THE FIELD hAtt'' OF k01_fifty_paid, IN ITS OWN TYPE**: hin off the promise; hM off the test on
public data; at a letter Mg₀. -/
theorem hAtt2_ofB' (J : S → Prop) (hM : Mg₀.more = {}) {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy}
    {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
    {base₀ : List (Block S Cl)} {c : Chain S Cl} {A₀ : ProofFile.SharedSeat} {B₀ : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A₀ B₀) (hDlk : Dm.links = linksFull)
    (hlk : ∀ l, l < 25 → Dm.lk l = c.links[l]?) (hX24 : headLink XV = 24) (hWX : Bs.G₀.W = XV)
    (shp : ReqShape) (lay₀ : ReqLayout) (hJl : ∀ s, J s → LiveIs shp lay₀ s)
    (hJf : ∀ s, J s → JFirst Dm.N s) (aN : ℕ) (R₁ R₂ R₃ : Rounds)
    (hKl : ∀ l Ap t, (linksFull[l]?).getD .layers = .attention → XV.A[l / 2]? = some Ap →
      (Dm.pubD.dS.trees l)[Ap.iU3]? = some t → t.2.1 = plannedK Ap)
    (hB : ∀ l Ap, l < 25 → (linksFull[l]?).getD .layers = .attention → XV.A[l / 2]? = some Ap →
      symsSeatedB (Dm.pubD.d3.arrayOf.getD l #[]) lay₀ shp l Ap.seam.tl = true)
    (hsub : ∀ l, l < 25 → ∀ u ∈ Dm.N.sent l 0, u ∈ Dm.N.group l) :
    ∀ l X arrs x x' y y' w p A B, ReadsFence Dm dk Mg₀ J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .attention →
      ∀ a₀ Ap tl', x.2.here = .att a₀ → XV.A[l / 2]? = some Ap → TlLike Ap.seam.tl a₀.tl →
      x'.2.tl? = some tl' →
      ∃ i, AttLeft2 (Dm.N.sent l 0) x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) Ap i tl' (Dm.A1 l x' w) := by
  intro l X arrs x x' y y' w p A B Fc hsb a₀ Ap tl' hs hA hL htl
  have hno : linkNo x.2 = l :=
    linkNo_of_promise Dm dk Mg₀ hM l Fc.lt x y (inAt_down _ _ _ _ _ _ _ _ _ Fc.inAt) A Fc.front
  obtain ⟨i, hin⟩ := hin_at_reads Dm dk Mg₀ hM hS hR O hDlk hlk hX24 hWX hKl Fc hsb hs hA
  have hF := hJf _ Fc.inv A Fc.front
  rw [hno] at hF
  exact ⟨i, attLeft2_of Dm dk Mg₀ Fc (hsub l Fc.lt) hs hL htl hin
    (symsIn_at_reads Dm dk Mg₀ hM Fc hJl (hB l Ap Fc.lt hsb hA) hF)⟩

/-- **THE FIELD hAtt'' OF k01_fifty_paid, IN ITS OWN TYPE.** -/
theorem hAtt2_ofB (J : S → Prop) {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy}
    {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
    {base₀ : List (Block S Cl)} {c : Chain S Cl} {A₀ : ProofFile.SharedSeat} {B₀ : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A₀ B₀) (hDlk : Dm.links = linksFull)
    (hlk : ∀ l, l < 25 → Dm.lk l = c.links[l]?) (hX24 : headLink XV = 24) (hWX : Bs.G₀.W = XV)
    (shp : ReqShape) (lay₀ : ReqLayout) (hJl : ∀ s, J s → LiveIs shp lay₀ s)
    (hJf : ∀ s, J s → JFirst Dm.N s) (aN : ℕ) (R₁ R₂ R₃ : Rounds)
    (hKl : ∀ l Ap t, (linksFull[l]?).getD .layers = .attention → XV.A[l / 2]? = some Ap →
      (Dm.pubD.dS.trees l)[Ap.iU3]? = some t → t.2.1 = plannedK Ap)
    (hB : ∀ l Ap, l < 25 → (linksFull[l]?).getD .layers = .attention → XV.A[l / 2]? = some Ap →
      symsSeatedB (Dm.pubD.d3.arrayOf.getD l #[]) lay₀ shp l Ap.seam.tl = true)
    (hsub : ∀ l, l < 25 → ∀ u ∈ Dm.N.sent l 0, u ∈ Dm.N.group l) :
    ∀ l X arrs x x' y y' w p A B, ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .attention →
      ∀ a₀ Ap tl', x.2.here = .att a₀ → XV.A[l / 2]? = some Ap → TlLike Ap.seam.tl a₀.tl →
      x'.2.tl? = some tl' →
      ∃ i, AttLeft2 (Dm.N.sent l 0) x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) Ap i tl' (Dm.A1 l x' w) :=
  hAtt2_ofB' Dm dk mgBase J rfl hS hR O hDlk hlk hX24 hWX shp lay₀ hJl hJf aN R₁ R₂ R₃ hKl hB hsub

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.ownIn_mw
#print axioms VerifiableInference.Desc.K1.ownIn_fails
#print axioms VerifiableInference.Desc.K1.inOf_of_reader
#print axioms VerifiableInference.Desc.K1.inOf_cols
#print axioms VerifiableInference.Desc.K1.hin_at_reads
#print axioms VerifiableInference.Desc.K1.hAtt2_ofB'
#print axioms VerifiableInference.Desc.K1.hAtt2_ofB
