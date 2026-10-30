-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/ArmAttEntry.lean: **hAtt_of2**: the premise hAtt of arm_at_reads
(Johnson/Desc/K1/Law/ArmAtReads.lean), to the letter, from the like with TWO of AttRest's eight fields
(hin hM): over hAtt_of (Johnson/Desc/K1/Law/ArmAttPaid.lean) the field hE ("the named entry lies in the
tables' part of the array of the reads") falls to sentences on letters, and hW to one on the plans.
OBJECT: `K5Law.EntIn Ap.iU3 (plannedK Ap) Ap.nW e` at an entry e with `NamedEntry`.
USER: whoever calls arm_at_reads | arm_at_reads_three.
LETTERS: arm_at_reads's; shp, lay₀ (the plan's shape of the request and layout of the rows).
HOW. e passes the public test entInT and its array cn is of the second commitment:
  `entInT_ranges`    so e's row and index lie below the layout's array's sizes (both arms of entInT)
  `arrays_at_reads`  the open link's list of arrays is the written one: the public item linkFresh l is open in
                   front of each reads' place (`freshIn_mw`, Johnson/Desc/K1/Law/HeardAtReads.lean). (At
                   link 24 alone the like stands as arrays_at342, Johnson/Desc/K1/Law/ArmHeadPromise.lean.)
  `LiveIs shp lay₀ s`   ONE CLAUSE FOR THE LETTER J: the live request's shape and its rows' layout are the
                   plan's. ALONG THE REACHED STATES IT HAS PAYERS: the fields liveShape and liveLayout of
                   FoldFacts (Johnson/Desc/First/FoldFacts.lean)
  hSec             ON LETTERS: at an attention link, of the written list's arrays the one at moment 1 is
                   the array of the reads alone, and each place inside its layout's sizes is a place
                   z < Ap.nW read at plannedK Ap columns. (The part a under "for all" is read through
                   its frame's link and shape alone, which are pinned.)
  hW               ON THE PLANS: Ap.nW ≤ plannedK Ap
  `AttLeft2`         hin hM
  `hAttE_of`         hAtt_of's premise hAtt' from these
  `hAtt_of2'` | `hAtt_of2`   **the premise hAtt**, at a letter Mg₀ | at mgBase
PREMISES LEFT: hS hR O · hWX · hJt : ∀ s, J s → TlIsPlan XV s · hJl : ∀ s, J s → LiveIs shp lay₀ s · hW · hSec ·
hAtt'' (pointwise, behind the fence; NO ENTRY, NO RUN: a letter i with AttLeft2).
IS IT EMPTY HERE? NO MEMBER IS SHOWN. hSec and hW are shown at no written value.
What is not claimed. The premises. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.ArmAttPaid
import Johnson.Desc.K1.Law.HeardAtReads

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

section
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att.P
open VerifiableInference.Desc.Sound (GQ MsgQ dataQ)

/-- **The live request's shape and its rows' layout are the plan's.** -/
def LiveIs (shp : Params.ReqShape) (lay₀ : Params.ReqLayout) (s : First.S) : Prop :=
  s.live.frame.shape = shp ∧ s.live.rows.layout = lay₀

/-- AttLeft4 less hW hE. -/
structure AttLeft2 (own : List (ℕ × ℕ)) (s : First.S) (a : VerifiableInference.Desc.K9.Part)
    (rd : ℕ × ℕ → MsgQ) (A : Attention.Plan) (i : Runs.In) (tl' : HTailF2)
    (Ac : ℕ → ℕ → ℕ → Cb.Gl.E) : Prop where
  hin : inOf (seatCO (parCOf A)) (parCOf A) s = some (i, plannedK A)
  hM : ∀ aI : ℕ → ℕ → ℕ → ℤ,
      (∀ μ, μ < tl'.NM → ∀ c, c < (tl'.mats.getD μ {}).k → ∀ i, i < (tl'.mats.getD μ {}).m →
        |aI μ i c| < 2 * ((2 ^ lbz : ℕ) : ℤ)) →
      (∀ μ, μ < tl'.NM → ∀ c, c < (tl'.mats.getD μ {}).k →
        ∀ i', i' < Alg.symRows (tl'.mats.getD μ {}).m →
          Ac (tl'.gtTree.getD μ 0) i' c =
            ((Alg.pack ((radb : ℕ) : ℤ) (fun i : Fin (tl'.mats.getD μ {}).m => aI μ i c) i' : ℤ) :
              Cb.Gl.E)) →
      ∀ μ r c, μ < tl'.NM → r < (tl'.mats.getD μ {}).m → c < (tl'.mats.getD μ {}).k →
        matsOfData A.seam.tl ((s.link?.map (·.arrayOf)).getD #[]) (dataQ own a rd) μ r c =
          ((aI μ r c : ℤ) : Cb.Gl.E)

end

open OnBytes OnBytes.Params OnBytes.Model
open Iop Run OnBytes.Maker OnBytes.Flat
open Cb Johnson.Pack
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More flatPlacesOf)
open VerifiableInference.Desc.First.Look (linkFreshC)
open VerifiableInference.Desc.Sound (linksFull MsgT MsgQ MgData CellsQ mgAll mgBase d13 rowQ seatTab
  UFn linkNo ArmCellIn second)
open VerifiableInference.Desc.K13.Law (openAt plus13)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.First.Att.P (plannedK)
open VerifiableInference.Desc.K9 (entInT entIn arrayIn arrayIn_some)
open OnBytes.Model.Stages (LinkH)
open OnBytes.Params (Rounds)
open K5Law (EntIn)
open ProofFile (Cl)

/-- Both arms of the public test bound the entry by the layout's array's sizes. -/
theorem entInT_ranges (own : List (ℕ × ℕ)) (a : K9.Part) (e : Ent) (cn : ℕ × String)
    (Ar : Params.ReqArray) (hc : a.L.arrayOf[e.tree]? = some cn)
    (hAr : reqArray a.L.check.rows.layout cn.1 cn.2 = some Ar) (h : entInT own a e = true) :
    e.row < Ar.sizeI ∧ e.idx < Ar.sizeC := by
  unfold entInT at h
  rcases Bool.or_eq_true_iff.1 h with h1 | h1
  · unfold entIn at h1
    cases hai : arrayIn own a e.tree with
    | none =>
      rw [hai] at h1
      cases h1
    | some A' =>
      rw [hai] at h1
      obtain ⟨b, _, _, hb, hA', _, _⟩ := arrayIn_some own a _ _ hai
      obtain rfl : cn = b := Option.some.inj (hc.symm.trans hb)
      obtain rfl : Ar = A' := Option.some.inj (hAr.symm.trans hA')
      obtain ⟨h3, h4⟩ := Bool.and_eq_true_iff.1 h1
      exact ⟨of_decide_eq_true h3, of_decide_eq_true h4⟩
  · rw [hc] at h1
    dsimp only at h1
    rw [hAr] at h1
    obtain ⟨_, h2⟩ := Bool.and_eq_true_iff.1 h1
    obtain ⟨h3, h4⟩ := Bool.and_eq_true_iff.1 h2
    exact ⟨of_decide_eq_true h3, of_decide_eq_true h4⟩

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)
  (Mg₀ : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))

/-- In front of a link's reads, inside the promise, the open link's list of arrays is the written
one. -/
theorem arrays_at_reads (hM : Mg₀.more = {}) (l : ℕ) (hl : l < 25) (x : ProofFile.InstPub × S) (y : Strs)
    (hIn : InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀)) linksFull (flatPlacesOf linksFull true)
      (noL l false) x y) (A : K9.Part) (hA : K9.segAt? x.2 = some A) :
    A.L.arrayOf = Dm.pubD.d3.arrayOf.getD l #[] := by
  have hin : Pub.linkFresh l ∈
      (First.pubSets (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀)).more linksFull
        (flatPlacesOf linksFull true))[noL l false]?.getD [] ++
      First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l false)) := by
    have e : (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀)).more = mwMore :=
      plus13_more_closed Dm dk Mg₀ hM
    rw [e]
    exact open_of (List.all_eq_true.1 freshIn_mw l (List.mem_range.2 hl))
  have h0 : (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).pub (.linkFresh l) x = true := inAt_pub hIn _ hin
  rw [pub_plus13, First.pubAll_linkFresh] at h0
  unfold linkFreshC at h0
  have h1 := (Bool.and_eq_true_iff.1 h0).2
  obtain ⟨_, hLa, _, _, _⟩ := segAt_some hA
  rw [hLa] at h1
  exact eq_of_beq h1

/-- **hAtt_of's premise hAtt'**, from sentences on letters and AttLeft2. -/
theorem hAttE_of (J : S → Prop) (hM : Mg₀.more = {}) (Z : ProofFile.Pub) (Bs : ProofFile.PureBase)
    (c : Chain S Cl) (shp : Params.ReqShape) (lay₀ : Params.ReqLayout)
    (hJl : ∀ s, J s → LiveIs shp lay₀ s) (aN : ℕ) (R₁ R₂ R₃ : Rounds)
    (hW : ∀ (g : ℕ) Ap, XV.A[g]? = some Ap → Ap.nW ≤ plannedK Ap)
    (hSec : ∀ l, l < 25 → (linksFull[l]?).getD .layers = .attention → ∀ Ap, XV.A[l / 2]? = some Ap →
      ∀ (a : K9.Part) t cn Ar, a.L.check.frame.link = l → a.L.check.frame.shape = shp →
      (Dm.pubD.d3.arrayOf.getD l #[])[t]? = some cn → reqArray lay₀ cn.1 cn.2 = some Ar →
      K9.atMoment1 a cn Ar = true → t = Ap.iU3 ∧ ∀ r i, r < Ar.sizeI → i < Ar.sizeC →
        ∃ z < Ap.nW, r = z / plannedK Ap ∧ i = z % plannedK Ap)
    (hAtt'' : ∀ l X arrs x x' y y' w p A B, ReadsFence Dm dk Mg₀ J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .attention →
      ∀ a₀ Ap tl', x.2.here = .att a₀ → XV.A[l / 2]? = some Ap → TlLike Ap.seam.tl a₀.tl →
      x'.2.tl? = some tl' →
      ∃ i, AttLeft2 (Dm.N.sent l 0) x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) Ap i tl' (Dm.A1 l x' w)) :
    ∀ l X arrs x x' y y' w p A B, ReadsFence Dm dk Mg₀ J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .attention →
      ∀ a₀ Ap tl', x.2.here = .att a₀ → XV.A[l / 2]? = some Ap → TlLike Ap.seam.tl a₀.tl →
      x'.2.tl? = some tl' →
      ∀ e cc, NamedEntry (Dm.Rd l) (Dm.N.sent l 0) p.1 p.2 x.2 A e cc →
      ∃ i, AttLeft4 (oneEntry e) (Dm.N.sent l 0) p.1 p.2 x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) Ap i tl'
        (Dm.A1 l x' w) := by
  intro l X arrs x x' y y' w p A B Fc hsub a₀ Ap tl' hs hA htlp htl e cc hN
  obtain ⟨i, L⟩ := hAtt'' l X arrs x x' y y' w p A B Fc hsub a₀ Ap tl' hs hA htlp htl
  obtain ⟨_, _, _, _, _, hin, hc, h2⟩ := hN
  obtain ⟨_, hLa, _, _, _⟩ := segAt_some Fc.front
  have hlive : x.2.live = A.L.check := by
    unfold S.live
    rw [hLa]
  obtain ⟨eS, eL⟩ := hJl _ Fc.inv
  rw [hlive] at eS eL
  have hno : linkNo x.2 = l :=
    linkNo_of_promise Dm dk Mg₀ hM l Fc.lt x y (inAt_down _ _ _ _ _ _ _ _ _ Fc.inAt) A Fc.front
  have hlk : A.L.check.frame.link = l := by
    unfold linkNo at hno
    rw [hLa] at hno
    exact hno
  unfold second at h2
  rw [Fc.front] at h2
  dsimp only at h2
  cases hAr : reqArray A.L.check.rows.layout cc.1 cc.2 with
  | none =>
    rw [hAr] at h2
    cases h2
  | some Ar =>
    rw [hAr] at h2
    obtain ⟨r1, r2⟩ := entInT_ranges _ A e cc Ar hc hAr hin
    obtain ⟨t1, t2⟩ := hSec l Fc.lt hsub Ap hA A e.tree cc Ar hlk eS
      (by rw [← arrays_at_reads Dm dk Mg₀ hM l Fc.lt x y Fc.inAt A Fc.front]; exact hc)
      (by rw [← eL]; exact hAr) h2
    have hWp := hW _ Ap hA
    have hE : EntIn Ap.iU3 (plannedK Ap) Ap.nW e := by
      obtain ⟨z, hz, z1, z2⟩ := t2 e.row e.idx r1 r2
      exact ⟨z, hz, t1, z1, z2⟩
    exact ⟨i, ⟨L.hin, hWp, fun R hR f hf => oneEntry_all hE p.1 p.2 x.2 R hR f hf, L.hM⟩⟩

/-- **The premise hAtt of arm_at_reads_of, from two of AttRest's eight fields.** -/
theorem hAtt_of2' (J : S → Prop) (hM : Mg₀.more = {}) {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)} {c : Chain S Cl}
    {A₀ : ProofFile.SharedSeat} {B₀ : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A₀ B₀)
    (hWX : Bs.G₀.W = XV) (hJt : ∀ s, J s → TlIsPlan XV s) (shp : Params.ReqShape)
    (lay₀ : Params.ReqLayout) (hJl : ∀ s, J s → LiveIs shp lay₀ s) (aN : ℕ) (R₁ R₂ R₃ : Rounds)
    (hW : ∀ (g : ℕ) Ap, XV.A[g]? = some Ap → Ap.nW ≤ plannedK Ap)
    (hSec : ∀ l, l < 25 → (linksFull[l]?).getD .layers = .attention → ∀ Ap, XV.A[l / 2]? = some Ap →
      ∀ (a : K9.Part) t cn Ar, a.L.check.frame.link = l → a.L.check.frame.shape = shp →
      (Dm.pubD.d3.arrayOf.getD l #[])[t]? = some cn → reqArray lay₀ cn.1 cn.2 = some Ar →
      K9.atMoment1 a cn Ar = true → t = Ap.iU3 ∧ ∀ r i, r < Ar.sizeI → i < Ar.sizeC →
        ∃ z < Ap.nW, r = z / plannedK Ap ∧ i = z % plannedK Ap)
    (hAtt'' : ∀ l X arrs x x' y y' w p A B, ReadsFence Dm dk Mg₀ J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .attention →
      ∀ a₀ Ap tl', x.2.here = .att a₀ → XV.A[l / 2]? = some Ap → TlLike Ap.seam.tl a₀.tl →
      x'.2.tl? = some tl' →
      ∃ i, AttLeft2 (Dm.N.sent l 0) x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) Ap i tl' (Dm.A1 l x' w)) :
    ∀ l X arrs x x' y y' w p A B, ReadsFence Dm dk Mg₀ J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .attention →
      ∀ a₀ Ap tlF tl', x.2.here = .att a₀ → Bs.G₀.W.A[X.g]? = some Ap → x.2.tl? = some tlF →
      x'.2.tl? = some tl' →
      ∀ e cc, NamedEntry (Dm.Rd l) (Dm.N.sent l 0) p.1 p.2 x.2 A e cc →
      ∃ i, AttRest XV (oneEntry e) (Dm.N.sent l 0) p.1 p.2 x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) l Ap i
        tlF tl' (Dm.A1 l x' w) :=
  hAtt_of' Dm dk Mg₀ J hM hS hR O hWX hJt aN R₁ R₂ R₃
    (hAttE_of Dm dk Mg₀ J hM Z Bs c shp lay₀ hJl aN R₁ R₂ R₃ hW hSec hAtt'')

/-- **THE PREMISE hAtt OF arm_at_reads, TO THE LETTER, FROM TWO OF AttRest's EIGHT FIELDS.** -/
theorem hAtt_of2 (J : S → Prop) {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)} {c : Chain S Cl}
    {A₀ : ProofFile.SharedSeat} {B₀ : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A₀ B₀)
    (hWX : Bs.G₀.W = XV) (hJt : ∀ s, J s → TlIsPlan XV s) (shp : Params.ReqShape)
    (lay₀ : Params.ReqLayout) (hJl : ∀ s, J s → LiveIs shp lay₀ s) (aN : ℕ) (R₁ R₂ R₃ : Rounds)
    (hW : ∀ (g : ℕ) Ap, XV.A[g]? = some Ap → Ap.nW ≤ plannedK Ap)
    (hSec : ∀ l, l < 25 → (linksFull[l]?).getD .layers = .attention → ∀ Ap, XV.A[l / 2]? = some Ap →
      ∀ (a : K9.Part) t cn Ar, a.L.check.frame.link = l → a.L.check.frame.shape = shp →
      (Dm.pubD.d3.arrayOf.getD l #[])[t]? = some cn → reqArray lay₀ cn.1 cn.2 = some Ar →
      K9.atMoment1 a cn Ar = true → t = Ap.iU3 ∧ ∀ r i, r < Ar.sizeI → i < Ar.sizeC →
        ∃ z < Ap.nW, r = z / plannedK Ap ∧ i = z % plannedK Ap)
    (hAtt'' : ∀ l X arrs x x' y y' w p A B, ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .attention →
      ∀ a₀ Ap tl', x.2.here = .att a₀ → XV.A[l / 2]? = some Ap → TlLike Ap.seam.tl a₀.tl →
      x'.2.tl? = some tl' →
      ∃ i, AttLeft2 (Dm.N.sent l 0) x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) Ap i tl' (Dm.A1 l x' w)) :
    ∀ l X arrs x x' y y' w p A B, ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .attention →
      ∀ a₀ Ap tlF tl', x.2.here = .att a₀ → Bs.G₀.W.A[X.g]? = some Ap → x.2.tl? = some tlF →
      x'.2.tl? = some tl' →
      ∀ e cc, NamedEntry (Dm.Rd l) (Dm.N.sent l 0) p.1 p.2 x.2 A e cc →
      ∃ i, AttRest XV (oneEntry e) (Dm.N.sent l 0) p.1 p.2 x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) l Ap i
        tlF tl' (Dm.A1 l x' w) :=
  hAtt_of2' Dm dk mgBase J rfl hS hR O hWX hJt shp lay₀ hJl aN R₁ R₂ R₃ hW hSec hAtt''

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.entInT_ranges
#print axioms VerifiableInference.Desc.K1.arrays_at_reads
#print axioms VerifiableInference.Desc.K1.hAttE_of
#print axioms VerifiableInference.Desc.K1.hAtt_of2'
#print axioms VerifiableInference.Desc.K1.hAtt_of2
