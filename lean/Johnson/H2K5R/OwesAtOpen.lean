-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/H2K5R/OwesAtOpen.lean: KIND K5: EIGHT FIELDS OF "WHAT IS LEFT OF THE
KIND's LAW AT THE TABLE" (the Lean structure K5Owes,
Johnson/Desc/First/Att/Door/Law/K5AtMgPaid.lean) AS THEOREMS FROM AN OPENING OF THE PROOF FILE's
DESCRIPTION. A join of theorems that stand already: no new mathematics.

Why. K5Owes is a list of premises, a field a premise. Eight of them speak of nothing but what the
description itself lays at an attention segment. They are proved from an opening (IM.Open) in the
files that this one imports.
Here each stands as the field's own text, at the letters that the opening fixes.

THE LETTERS THAT AN OPENING FIXES (W := Bs.G₀.W): Wv := W · g · a (W.A[g]? = some a) · x (lookAt W
(2 g + 1) false = some x) · Lk (c.links[2 g + 1]? = some Lk) · same := ProofFile.sameReply · before :=
(H2K5.k5Before? Z ("A" ++ toString g)).getD [] · blk (k5AtN W (2 g + 1) g before = some blk) ·
Dn := sentOfBuilt Z.first Z.p.built. All other letters of K5Owes stay their owners'.

Main names:
  `k5Entry_at`: the first chain's entry at the kind's place of segment 2 g + 1.
  `K05_facts_at`: K05_facts_of_open (LawAtLaid.lean), which speaks entry by entry, turned to
    speak at a given g.
  `statesAt_of_open` · `sameOut_of_open` · `seated_of_open` · `seatedOk_guard_of_open` ·
  `objIs_gstIs_of_open` · `tiePub_of_open`: the fields statesAt · sameOut · seated · seatedOk, guard
    · objIs, gstIs · tiePub.
PREMISES, BESIDE THE OPENING: h4 · hg · ha everywhere · seatedOk, guard, tiePub: F.planOk = true and
"every test of lawsAsk says yes" · objIs, gstIs: the goals' scope (hS · hR · the second hash
function · g < 12) and K5Owes' own fields rdIs · lkAt: so these two follow from two other fields and
the opening · tiePub: SymsOK, one of TiePub's four facts, STAYS A NAMED PREMISE: NOT PAID.
NO LETTER IS LOOSE: Lk, blk, x stand under their equations; Rd, lk, Wv, mH are tied by rdIs | lkAt.
IS IT EMPTY HERE? Implications from an opening: that onlineDescription returns at any files is not shown.
No soundness of the protocol is claimed.
Nothing is claimed on completeness or hiding.

-/
import Johnson.H2K5R.PublicAtEntry
import Johnson.H2K5R.SeatedStates
import Johnson.H2K5R.ObjectsAtOpen
import Johnson.Desc.First.Att.K05ReadersGuarded
import Johnson.Desc.First.Att.K05TiePublic
import Johnson.Desc.First.Batch.ReadersAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Model.Stages OnBytes.Params OnBytes.Plan
open VerifiableInference.Desc.First.Look (lookAt)
open VerifiableInference.Desc (Claim Block Chain Link FileDescription)
open VerifiableInference.Desc.K9 (Readers statesOfLink readersAt readersAt_some)

section
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block First.S Claim)} {c : Chain First.S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- The first chain's entry at the kind's place of segment 2 g + 1. -/
theorem k5Entry_at (O : IM.Open o pol lay KL F Z Bs base c A B) (h4 : Bs.G₀.W.p4 = true) {g : ℕ}
    (hg : g < Bs.G₀.W.NGr) :
    ∃ b : Block First.S Claim, c.blocksInOrder[IM.flatIx c (2 * g + 1) 2]? = some b ∧
      b.place = ⟨1, some (2 * g + 1), 3, .K5⟩ := by
  obtain ⟨Lk, b, -, e1, e2, -, -⟩ := k5_alone O h4 hg
  have hfl := IM.hear_at_flat e1 e2
  obtain ⟨sv, hfp, -, hk, -⟩ := K05_place_at O h4 hg
  rw [← hfp, List.getElem?_map, hfl] at hk
  exact ⟨b, hfl, Option.some.inj hk⟩

/-- **THE JOINT, AT A GIVEN g.** -/
theorem K05_facts_at (O : IM.Open o pol lay KL F Z Bs base c A B) (hpl : F.planOk = true)
    {D : OnBytes.Maker.WholeD} (hs : ∀ t ∈ LPFD.lawsAsk o pol lay KL F D, t.2 = true)
    (h4 : Bs.G₀.W.p4 = true) {g : ℕ} (hg : g < Bs.G₀.W.NGr) :
    ∃ (blk : Block First.S Claim) (a : Attention.Plan)
      (x : VerifiableInference.Desc.First.Look.Place),
      k5AtN Bs.G₀.W (2 * g + 1) g ((H2K5.k5Before? Z ("A" ++ toString g)).getD []) = some blk ∧
      blk.planOk = true ∧ k5GuardN Bs.G₀.W (2 * g + 1) g = true ∧ Bs.G₀.W.A[g]? = some a ∧
      lookAt Bs.G₀.W (2 * g + 1) false = some x ∧ x.link = 2 * g + 1 ∧
      masksUpTo (sentOfBuilt Z.first Z.p.built) x x.ns = true := by
  obtain ⟨b, hfl, eP⟩ := k5Entry_at O h4 hg
  have hb : b ∈ c.blocksInOrder := List.mem_of_getElem? hfl
  have hK : b.place.kind = .K5 := by rw [eP]
  obtain ⟨g', blk, a, x, -, hg', hfl', -, hat, -, hok, hG, ea, hx, hlk⟩ :=
    (K05_facts_of_open O hpl hs).2.2 b hb hK
  obtain ⟨g'', a'', x'', eP'', ea'', hx'', hm⟩ := (K05_public_of_open O hpl hs).2.2 b hb hK
  obtain ⟨b', hfl₂, eP'⟩ := k5Entry_at O h4 hg'
  obtain rfl : b' = b := Option.some.inj (hfl₂.symm.trans hfl')
  have e1 : g' = g := by
    have h := eP'.symm.trans eP
    injection h with _ h2 _ _
    injection h2 with h3
    omega
  have e2 : g'' = g := by
    have h := eP''.symm.trans eP
    injection h with _ h2 _ _
    injection h2 with h3
    omega
  subst e1
  subst e2
  have ex : x'' = x := Option.some.inj (hx''.symm.trans hx)
  rw [ex] at hm
  exact ⟨blk, a, x, hat, hok, hG, ea, hx, hlk, hm⟩

/-- **statesAt.** -/
theorem statesAt_of_open (O : IM.Open o pol lay KL F Z Bs base c A B) (h4 : Bs.G₀.W.p4 = true)
    {g : ℕ} (hg : g < Bs.G₀.W.NGr) {a : Attention.Plan} (ha : Bs.G₀.W.A[g]? = some a) :
    ∃ Lk : Link First.S Claim, c.links[2 * g + 1]? = some Lk ∧
      statesOfLink Lk 2 = (runsN a).map (guardC ProofFile.sameReply) := by
  obtain ⟨Lk, -, e1, -, hL⟩ := K05_states_of_open O h4 hg ha
  exact ⟨Lk, e1, hL⟩

/-- **sameOut.** -/
theorem sameOut_of_open : ∀ s t : First.S, t.out = s.out → ProofFile.sameReply s t = true :=
  same_of_out

/-- **seated.** -/
theorem seated_of_open (O : IM.Open o pol lay KL F Z Bs base c A B) (h4 : Bs.G₀.W.p4 = true)
    {g : ℕ} (hg : g < Bs.G₀.W.NGr) :
    ∃ blk : Block First.S Claim,
      k5AtN Bs.G₀.W (2 * g + 1) g ((H2K5.k5Before? Z ("A" ++ toString g)).getD []) = some blk := by
  obtain ⟨-, -, blk, -, -, hat, -⟩ := k5_alone O h4 hg
  exact ⟨blk, hat⟩

/-- **seatedOk AND guard.** -/
theorem seatedOk_guard_of_open (O : IM.Open o pol lay KL F Z Bs base c A B)
    (hpl : F.planOk = true) {D : OnBytes.Maker.WholeD}
    (hs : ∀ t ∈ LPFD.lawsAsk o pol lay KL F D, t.2 = true) (h4 : Bs.G₀.W.p4 = true) {g : ℕ}
    (hg : g < Bs.G₀.W.NGr) {blk : Block First.S Claim}
    (hb : k5AtN Bs.G₀.W (2 * g + 1) g ((H2K5.k5Before? Z ("A" ++ toString g)).getD []) =
      some blk) :
    blk.planOk = true ∧ k5GuardN Bs.G₀.W (2 * g + 1) g = true := by
  obtain ⟨blk', -, -, hat, hok, hG, -⟩ := K05_facts_at O hpl hs h4 hg
  obtain rfl : blk' = blk := Option.some.inj (hat.symm.trans hb)
  exact ⟨hok, hG⟩

/-- **tiePub**, but for SymsOK. -/
theorem tiePub_of_open (O : IM.Open o pol lay KL F Z Bs base c A B) (hpl : F.planOk = true)
    {D : OnBytes.Maker.WholeD} (hs : ∀ t ∈ LPFD.lawsAsk o pol lay KL F D, t.2 = true)
    (h4 : Bs.G₀.W.p4 = true) {g : ℕ} (hg : g < Bs.G₀.W.NGr) {a : Attention.Plan}
    (ha : Bs.G₀.W.A[g]? = some a) {x : VerifiableInference.Desc.First.Look.Place}
    (hx : lookAt Bs.G₀.W (2 * g + 1) false = some x) (rad : OracleShape → Nat)
    (hSy : SymsOK x a.seam.tl (sentOfBuilt Z.first Z.p.built) rad) :
    TiePub (sentOfBuilt Z.first Z.p.built) x a.seam.tl a.ns rad := by
  obtain ⟨hlay, hone, -⟩ := K05_public_of_open O hpl hs
  obtain ⟨-, hP, -⟩ := K05_facts_of_open O hpl hs
  obtain ⟨-, -, x', -, -, -, -, hx', -, hm⟩ := K05_facts_at O hpl hs h4 hg
  obtain rfl : x' = x := Option.some.inj (hx'.symm.trans hx)
  obtain ⟨-, -, ens, -, -⟩ := k5Plan_of_public hP h4 ha hx (Params.settingOf Bs.G₀.W.P.frame)
  rw [ens] at hm
  exact ⟨hSy, hm, hlay, fun k hk hk' => hone_of_B (hone x'.link) rad k hk hk'⟩

end

/-- **objIs AND gstIs**: from K5Owes' own fields rdIs | lkAt and the opening. -/
theorem objIs_gstIs_of_open {Pf : VerifierAndGoals.PublicFiles} {pp₀ : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
    {base : List (Block First.S Claim)} {c : Chain First.S Claim} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {Lk : Link First.S Claim} (hL : c.links[2 * g + 1]? = some Lk) (Rd : ℕ → Readers)
    (lk : ℕ → Option (Link First.S Claim)) (Wv : Verify.Public) (mH : ℕ)
    (rdIs : Rd = readersAt lk Wv mH) (lkAt : lk (2 * g + 1) = some Lk) :
    (∀ (t : First.S) (G : Fork) (g₁ : Forest.Heard), t.fork? = some G → t.lookHeard? = some g₁ →
        (∀ f ∈ g₁.rows.toList, f.ents = #[]) →
        (Rd (2 * g + 1)).forms 1 "objects" t = some { forms := g₁.rows.toList, late := [] }) ∧
      ∀ (t : First.S) (G : Fork), t.fork? = some G →
        (Rd (2 * g + 1)).forms 1 "guests" t = some { forms := [], late := [] } := by
  obtain ⟨Lk', e, h1, h2⟩ := K05_objects_guests_of_open hS hR O hg
  obtain rfl : Lk' = Lk := Option.some.inj (e.symm.trans hL)
  rw [rdIs, readersAt_some lk Wv mH (2 * g + 1) Lk' lkAt]
  exact ⟨h1 _, h2 _⟩

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.k5Entry_at
#print axioms VerifiableInference.Desc.First.Att.P.K05_facts_at
#print axioms VerifiableInference.Desc.First.Att.P.statesAt_of_open
#print axioms VerifiableInference.Desc.First.Att.P.sameOut_of_open
#print axioms VerifiableInference.Desc.First.Att.P.seated_of_open
#print axioms VerifiableInference.Desc.First.Att.P.seatedOk_guard_of_open
#print axioms VerifiableInference.Desc.First.Att.P.tiePub_of_open
#print axioms VerifiableInference.Desc.First.Att.P.objIs_gstIs_of_open
