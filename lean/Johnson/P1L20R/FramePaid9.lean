-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1L20R/FramePaid9.lean:
FrameParams9 (FrameRows9.lean) from what other files show of the parameters' own terms:
the carried word's sentence at Dm.cr1 := carryAtZ Z layF (Johnson/Top/H0/Walk/FrameCarryBack.lean)
and the output head's parts' sentences at Dm.headPart := headPartK6 … (FrameHeadOpen.lean).

  carry_laid_is, carry_clear_is   which "carry m" is open at the border behind "laid" l
                    (m + 1 = l) and behind "cleared" l (m = l): from restB_full
  FrameOwed9        WHAT IS STILL OWED, eight fields: which terms two parameters are (carryIs,
                    headIs); kept; low; d1; the fence (CarryFence from what is known in front); and
                    the carried word's sentence, at the step's own yes, at the segments whose next
                    switch does not stand at a link (carryElseLaid, carryElseClear)
  frameParams9_of   FrameParams9 Dm Z T Kn from FrameOwed9

Limits. FrameOwed9 is shown at nothing here. At the segments m whose next code switch stands at the
output head or at the finish ((ProofFile.pAtK2 Z m).stands is not .link: 23 and 24 at the full size, by
reading) nothing is shown of the carried word's sentence: it stays a field: three places: "cleared"
23, "laid" 24, "cleared" 24. carryAtZ Z layF reads the strings by ProofFile.allAt Z and ProofFile.keyAt Z; Stays
and the pieces' strings go by T's own D, all and D.key₁; layF and the layout file of the opening are
two letters: nothing here ties these. Where Kn k never holds the fence and the two fields on
"carryElse" hold trivially, and the debt moves whole to GivesIn (FrameSitsR.lean). No soundness
statement.

-/
import Johnson.P1L20R.FrameRows9
import Johnson.Top.H0.Walk.FrameHeadOpen
import Johnson.Top.H0.Walk.FrameCarryBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1L20

open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Block Chain FileDescription Place KindName Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Pub Part Meaning Numbers)
open VerifiableInference.Desc.First.K2Caller (carryAtZ rest)
open VerifiableInference.OnPublicFiles (headLink)
open Johnson.Desc.First.Walk (layFront)
open Johnson.Desc.First.Walk.Tied
open ProofFile (Cl)

/-- Behind "laid" l the one item "carry m" that is open has m + 1 = l. -/
theorem carry_laid_is {l m : ℕ} (hl : l < 25) (h : openP9 (14 * l + 1 + 1) (.carry m)) :
    l = m + 1 := by
  have hm : Item.carry m ∈ openL9 (14 * l + 1 + 1) :=
    open_mem (behind51_le (succ_mem (mem_our_laid hl))) h
  have hr : Item.carry m ∈ restAt (14 * l + 1 + 1) := List.mem_filter.2 ⟨hm, rfl⟩
  cases l with
  | zero =>
    rw [show 14 * 0 + 1 + 1 = 2 from rfl, rest_laid0] at hr
    simp at hr
  | succ j =>
    rw [rest_laid (by omega : j < 24)] at hr
    simp at hr
    omega

/-- Behind "cleared" l the one item "carry m" that is open has m = l. -/
theorem carry_clear_is {l m : ℕ} (hl : l < 25) (h : openP9 (clearIx l + 1) (.carry m)) : m = l := by
  have hm : Item.carry m ∈ openL9 (clearIx l + 1) :=
    open_mem (behind51_le (succ_mem (mem_our_clear hl))) h
  have hr : Item.carry m ∈ restAt (clearIx l + 1) := List.mem_filter.2 ⟨hm, rfl⟩
  rw [rest_clear hl] at hr
  simpa using hr

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {C : CK} {D : WholeD} {all : List LeftT}
  {X₁ X₂ Xi Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  {T : ThreeAt C D all
    (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
    X₁ X₂ (Wit (CellsQ rows cols) Tok MsgT)}

/-- **WHAT IS STILL OWED.** layF: the layout file at which the carried word's sentence is closed.
HeadIs: that Dm.headPart is the output head's own term, with the request's reader Dm.H.req: as the
three lemmas of FrameHeadOpen.lean take it. -/
structure FrameOwed9 (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR X) (Z : ProofFile.Pub)
    (T : ThreeAt C D all
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      X₁ X₂ (Wit (CellsQ rows cols) Tok MsgT))
    (Kn : ℕ → ProofFile.InstPub × S → Strs → Prop) (layF : ByteArray) : Prop where
  /-- the parameter is the closed sentence on the carried word -/
  carryIs : Dm.cr1 = carryAtZ Z layF
  /-- the output head's parts' sentences go back over every relation that keeps the request's
  reader, at the parts that are open (FrameHeadOpen.lean: headOpen_of_req, at the parameter's own
  term) -/
  headIs : ∀ (Op : Item → Prop), ¬ Op (.constr (headLink X) .lookCallsHeard) →
    ∀ R : ProofFile.InstPub × S → Strs → ProofFile.InstPub × S → Strs → Prop,
    (∀ a y b y', R a y b y' → Dm.H.req a = Dm.H.req b) → HeadOpen Dm Op R
  /-- three parameters read of the verifier's state nothing but what "cleared" keeps -/
  kept : ∀ l, l < 25 → ∀ q, (T.p₁ :: T.l₁)[clearIx l]? = some q → ReadKept Dm q.base
  /-- the tenants whose pin is open in front of each of the 51 sit in trees below the piece's base
  -/
  low : ∀ k, k ∈ our51 → ∀ q, (T.p₁ :: T.l₁)[k]? = some q → LowAt Dm.N (openL9 k) q.base
  /-- the parameter's layout, shape of a claim and numbers of claims are the plan's -/
  d1 : D1Fits Dm.d1 Z.p.built.links Z.p.X.layers.wsLay Z.first.lin
  /-- **the fence**: what is known in front gives: the trees that the carried rows' messages are
  placed in have numbers below the piece's base -/
  fence : ∀ k, k ∈ our51 → ∀ q, (T.p₁ :: T.l₁)[k]? = some q → ∀ m, openP9 (k + 1) (.carry m) →
    (ProofFile.pAtK2 Z m).stands = .link → ∀ p s y, InAt9 Dm Kn k (p, s) y →
    CarryFence Z m q.base (rest s)
  /-- the carried word's sentence over "laid", at the step's own yes, where the next code switch
  does not stand at a link -/
  carryElseLaid : ∀ l, l < 25 → ∀ q, (T.p₁ :: T.l₁)[14 * l + 1]? = some q → ∀ m,
    openP9 (14 * l + 1 + 1) (.carry m) → (ProofFile.pAtK2 Z m).stands ≠ .link →
    GoesBack (StepRel (Yes (layFront l)) q.base (InAt9 Dm Kn (14 * l + 1))) (Dm.cr1 m)
  /-- the like over "cleared" -/
  carryElseClear : ∀ l, l < 25 → ∀ fs f,
    Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs →
    fs[l]? = some f → ∀ q, (T.p₁ :: T.l₁)[clearIx l]? = some q → ∀ m,
    openP9 (clearIx l + 1) (.carry m) → (ProofFile.pAtK2 Z m).stands ≠ .link →
    GoesBack (StepRel (Yes f.clear) q.base (InAt9 Dm Kn (clearIx l))) (Dm.cr1 m)

variable {Dm : MgData Xi ProofFile.InstPub Tok rows cols nR X} {Kn : ℕ → ProofFile.InstPub × S → Strs → Prop}
  {layF : ByteArray}

/-- The carried word's sentence goes back over a step of the 51 that gives RestLike, where its item
is open behind and the next code switch stands at a link. -/
theorem carry_link9 (H : FrameOwed9 Dm Z T Kn layF) {k : ℕ} (hk : k ∈ our51)
    {q : Piece C (frameAt D all D.key₁ T.ft₁) (ProofFile.InstPub × S) Cl
      (Wit (CellsQ rows cols) Tok MsgT)}
    (hq : (T.p₁ :: T.l₁)[k]? = some q) (rel : S → S → Prop)
    (hrel : ∀ s t, rel s t → RestLike s t) {m : ℕ} (hm : openP9 (k + 1) (.carry m))
    (hs : (ProofFile.pAtK2 Z m).stands = .link) :
    GoesBack (StepRel rel q.base (InAt9 Dm Kn k)) (Dm.cr1 m) := by
  rw [H.carryIs]
  exact carry_goesBack_of Z layF m hs rel hrel q.base _ (H.fence k hk q hq m hm hs)

/-- **FrameParams9 from FrameOwed9.** -/
theorem frameParams9_of (H : FrameOwed9 Dm Z T Kn layF) : FrameParams9 Dm Z T Kn where
  kept := H.kept
  low := H.low
  d1 := H.d1
  carryLaid := fun l hl q hq m hm => by
    by_cases hs : (ProofFile.pAtK2 Z m).stands = .link
    · exact carry_link9 H (mem_our_laid hl) hq _ (fun s t e => by
        rw [(Johnson.Desc.First.Walk.Law.layFront_ok e).1]
        exact RestLike.refl s) hm hs
    · exact H.carryElseLaid l hl q hq m hm hs
  carryClear := fun l hl fs f hfs hf q hq m hm => by
    by_cases hs : (ProofFile.pAtK2 Z m).stands = .link
    · exact carry_link9 H (mem_our_clear hl) hq _ (fun s t e => by
        obtain ⟨_, Xl, counts, left, e', _⟩ :=
          Johnson.Desc.First.Walk.Seat.framesOf_row hfs (List.mem_of_getElem? hf)
        have e2 : f.clear s = .ok t := e
        rw [e'] at e2
        exact restLike_cleared e2) hm hs
    · exact H.carryElseClear l hl fs f hfs hf q hq m hm hs
  headFront := fun q _ =>
    H.headIs _ (not_heard mem_our_front) _ fun a y b y' h => by
      obtain rfl : b = a := Prod.ext h.1 (Except.ok.inj h.2.1).symm
      rfl
  headLaid := fun l hl q _ =>
    H.headIs _ (not_heard (mem_our_laid hl)) _ fun a y b y' h => by
      obtain rfl : b = a := Prod.ext h.1 (Johnson.Desc.First.Walk.Law.layFront_ok h.2.1).1
      rfl
  headClear := fun l hl fs f hfs hf q hq =>
    H.headIs _ (not_heard (mem_our_clear hl)) _ fun a y b y' h => by
      obtain ⟨p, s⟩ := a
      obtain ⟨p', t⟩ := b
      obtain rfl : p' = p := h.1
      exact (H.kept l hl q hq).req p' s t (clear_kept hfs hf h.2.1)

end

end P1L20

#print axioms P1L20.carry_laid_is
#print axioms P1L20.carry_clear_is
#print axioms P1L20.carry_link9
#print axioms P1L20.frameParams9_of
