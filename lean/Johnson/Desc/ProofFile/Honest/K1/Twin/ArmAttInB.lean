-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Twin/ArmAttInB.lean: MADE BY PROGRAM OFF
Johnson/Desc/K1/Law/ArmAttIn.lean UNDER A MAP OF NAMES AND ONE TURN OF THE MEANING: 3 OF
ITS DECLARATIONS: hin_at_reads_b · hAtt2_ofB'_b · hAtt2_ofB_b. THE PROOFS ARE COPIES.

This letter is for the honest run's own forms alone: no statement on any other party may take it.
NEVER ON SOUNDNESS's ROAD: at the meaning "honest" the
clauses noColl, shown and decodes are True by definition: a law at that meaning may stand beneath
statements on completeness or zero knowledge only, never beneath a statement on soundness.

The map of names. ReadsFence to ReadsFenceB; each twinned theorem n to n_b; the library's closed
facts at its wider table of names (mwMore) to their likes at mgMore, and its laws on the wider
meaning to their likes on "honest" over mgAll (both in Twin/HonestAt.lean, typed by hand).
The turn of the meaning. Where the elder has the wider meaning (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀),
or plus13 (d13 Dm) dk (mgAll Dm Mg₀)), the twin has honest (mgAll Dm Mg₀) ans test
(Johnson/Desc/ProofFile/Honest/Thread/First.lean): the meaning at which the honest thread's own
promise stands; at the item "tie": mgAll Dm Mg₀. The step down from mw1 to plus13 (inAt_down) falls.
The promise itself is the library's InAt: no new text of a promise.
Laid in, on no line of a statement: the letters ans and test, behind each block of letters: implicit
in the theorems, explicit in the structure ReadsFenceB; "include dk" where the source's block binds
dk (no twin's statement names it; it is kept so that a copied call has the source's number
of arguments). Kept as they stand in the source: its namespace, open, variable, section, set_option
and attribute lines, but for one prefix that makes dk implicit (in ArmAtReadsB.lean): there "omit dk
in" stands.
The namespace is the library's, so that a copied proof finds its callees without a sign turned; the
names with the suffix _b are not the library's.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K1.Law.ArmAttIn
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmAtReadsB
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmAttMatsB
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmBySortB
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmSymsB
import Johnson.Desc.ProofFile.Honest.K1.Twin.HonestAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1
open ProofFile.Honest.FirstThread (honest)
open VerifiableInference.Desc (Strs Wit)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (CellsQ MsgT mgMore)
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

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)} {c : Chain S Cl}
    {A₀ : ProofFile.SharedSeat} {B₀ : ProofFile.SecondSeat} 

end

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)
  (Mg₀ : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))

variable {ans : ℕ → ℕ → ProofFile.InstPub × S → Strs → Wit (CellsQ rows cols) Tok MsgT → Prop} {test : ℕ → S → Option String}
include dk
/-- **The clause hin inside the fence.** -/
theorem hin_at_reads_b {J : S → Prop} (hM : Mg₀.more = {}) {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy}
    {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
    {base₀ : List (Block S Cl)} {c : Chain S Cl} {A₀ : ProofFile.SharedSeat} {B₀ : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A₀ B₀) (hDlk : Dm.links = linksFull)
    (hlk : ∀ l, l < 25 → Dm.lk l = c.links[l]?) (hX24 : headLink XV = 24) (hWX : Bs.G₀.W = XV)
    (hKl : ∀ l Ap t, (linksFull[l]?).getD .layers = .attention → XV.A[l / 2]? = some Ap →
      (Dm.pubD.dS.trees l)[Ap.iU3]? = some t → t.2.1 = plannedK Ap)
    {aN : ℕ} {R₁ R₂ R₃ : Rounds} {l : ℕ} {X : LinkH} {arrs : Option (List ℕ)}
    {x x' : ProofFile.InstPub × S} {y y' : Strs} {w : Wit (CellsQ rows cols) Tok MsgT} {p : ℕ × String}
    {A B : K9.Part} (Fc : ReadsFenceB Dm Mg₀ ans test J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B)
    (hsub : (linksFull[l]?).getD .layers = .attention) {a₀ : AttOwn} {Ap : Attention.Plan}
    (hs : x.2.here = .att a₀) (hA : XV.A[l / 2]? = some Ap) :
    ∃ i, inOf (seatCO (parCOf Ap)) (parCOf Ap) x.2 = some (i, plannedK Ap) := by
  obtain ⟨el, hg⟩ := attIsOdd l Fc.lt hsub
  have t := List.all_eq_true.1 ownIn_mg l (List.mem_range.2 Fc.lt)
  rw [hsub] at t
  have t' : ((rowQ linksFull (flatPlacesOf linksFull true) (noL l false)).ins.contains
      (.formsT l 3 "own") && (runsAt linksFull l 3 "own").contains (2, "first") &&
      openB mgMore linksFull (flatPlacesOf linksFull true) (noL l false)
        (.more (some l) "ledger.treesAre")) = true := t
  obtain ⟨t12, t3⟩ := Bool.and_eq_true_iff.1 t'
  obtain ⟨t1, t2⟩ := Bool.and_eq_true_iff.1 t12
  have hIn' := Fc.inAt
  have h0 := inAt_pub hIn' _ (List.mem_append_right _
    (formsInT_of_ins l Fc.lt 3 "own" (List.contains_iff_mem.1 t1)))
  rw [honest_pub_all, First.pubAll_formsInT, List.all_eq_true] at h0
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
        (First.pubSets (honest (mgAll Dm Mg₀) ans test).more linksFull
          (flatPlacesOf linksFull true))[noL l false]?.getD [] ++
        First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l false)) := by
      have e : (honest (mgAll Dm Mg₀) ans test).more = mgMore :=
        honest_more_closed Dm Mg₀ ans test hM
      rw [e]
      exact open_of t3
    have h1 : (honest (mgAll Dm Mg₀) ans test).pub (.more (some l) "ledger.treesAre") x = true :=
      inAt_pub Fc.inAt _ hmem
    rw [honest_pub_all, First.pubAll_more_treesAre] at h1
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

/-- **THE FIELD hAtt'' OF k01_fifty_paid, IN ITS OWN TYPE: a twin, not joined; no call checks
that the two types agree**: hin off the promise; hM off the test on public data; at a letter Mg₀. -/
theorem hAtt2_ofB'_b (J : S → Prop) (hM : Mg₀.more = {}) {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy}
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
    ∀ l X arrs x x' y y' w p A B, ReadsFenceB Dm Mg₀ ans test J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .attention →
      ∀ a₀ Ap tl', x.2.here = .att a₀ → XV.A[l / 2]? = some Ap → TlLike Ap.seam.tl a₀.tl →
      x'.2.tl? = some tl' →
      ∃ i, AttLeft2 (Dm.N.sent l 0) x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) Ap i tl' (Dm.A1 l x' w) := by
  intro l X arrs x x' y y' w p A B Fc hsb a₀ Ap tl' hs hA hL htl
  have hno : linkNo x.2 = l :=
    linkNo_of_promise_b Dm dk Mg₀ hM l Fc.lt x y Fc.inAt A Fc.front
  obtain ⟨i, hin⟩ := hin_at_reads_b Dm dk Mg₀ hM hS hR O hDlk hlk hX24 hWX hKl Fc hsb hs hA
  have hF := hJf _ Fc.inv A Fc.front
  rw [hno] at hF
  exact ⟨i, attLeft2_of_b Dm dk Mg₀ Fc (hsub l Fc.lt) hs hL htl hin
    (symsIn_at_reads_b Dm dk Mg₀ hM Fc hJl (hB l Ap Fc.lt hsb hA) hF)⟩

/-- **THE FIELD hAtt'' OF k01_fifty_paid, IN ITS OWN TYPE: a twin, not joined; no call checks that the two types agree.** -/
theorem hAtt2_ofB_b (J : S → Prop) {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy}
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
    ∀ l X arrs x x' y y' w p A B, ReadsFenceB Dm mgBase ans test J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .attention →
      ∀ a₀ Ap tl', x.2.here = .att a₀ → XV.A[l / 2]? = some Ap → TlLike Ap.seam.tl a₀.tl →
      x'.2.tl? = some tl' →
      ∃ i, AttLeft2 (Dm.N.sent l 0) x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) Ap i tl' (Dm.A1 l x' w) :=
  hAtt2_ofB'_b Dm dk mgBase J rfl hS hR O hDlk hlk hX24 hWX shp lay₀ hJl hJf aN R₁ R₂ R₃ hKl hB hsub

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.hin_at_reads_b
#print axioms VerifiableInference.Desc.K1.hAtt2_ofB'_b
#print axioms VerifiableInference.Desc.K1.hAtt2_ofB_b
