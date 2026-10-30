-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/ArmHeadJ.lean: THE OUTPUT HEAD's CONJUNCT OF THE LETTER J OF ArmOk
(Johnson/Desc/K1/Law/ArmOk.lean): the four clauses that stay of HeadRest read the state in front of the
reads' place alone (HeadLeft6, Johnson/Desc/K1/Law/ArmHeadRide.lean): so they are laid into J, and THE
PREMISE hK6 OF arm_at_reads_three HAS NO POINTWISE PREMISE OF ITS OWN ANY MORE. What is owed instead: J
along the reached states in front of the reads' places: THE HEAD's CONJUNCT IS IDLE AT THE 24 OTHER
SEGMENTS (there the state stands in no head): it is owed at ONE border: 342. A definition, and statements
with their proofs: calls.

Main names:
  JHead X own arr N num lay6 s   where the state stands in the output head's segment: HeadLeft6 at the
                      open segment's part.
  JH … s              NoTables s ∧ JHead … s: THE OUTPUT HEAD's SHARE OF J.
  here_head_of_stand  the promise's stand at link 24 says that the state stands in the head.
  hK6_ofJ             **the premise hK6, from J alone** (hJ : J gives JH), the scope and sentences on
                      letters.
  jHead_low           at l < 24, in front of the reads, JHead holds (idle).
  jH_at_reads         **JH at the reached states in front of all 25 reads' places, FROM ONE PREMISE:
                      h342: HeadLeft6 at the reached states at border 342.**
What is not claimed. h342: its four clauses: hT · hRun (their payers, heardAt_of_below and
runIs_at_border (Johnson/Desc/Reads/RunIsAtBorder.lean), speak behind K6's accept from a state at
which a fact of the promise at 341 holds) · hlay · hMats (MatsSeated at the four ranges). Nothing on
soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.ArmHeadRide

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open Cb Johnson.Pack
open Johnson.Desc.First.Walk.Tied (RchAt)
open VerifiableInference.Desc (Block Chain Link FileDescription Place Strs)
open VerifiableInference.Desc.First (S Here HeadOwn ModelPart Item Pub Meaning Numbers flatPlacesOf standOf)
open VerifiableInference.Desc.Sound (linksFull MsgT MgData CellsQ mgAll d13 mgBase Mem seatTab dataQ
  onQ Frame)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.Kinds.Head.Law (K6Name ColFour CallsSeated)
open VerifiableInference.Desc.First.Look (sigListCalls)
open OnBytes.Model.Verify (borderOf)
open OnBytes.Params (Rounds)
open IM (k1Ix)
open ProofFile (Cl)

/-- Where the state stands in the output head's segment: what stays of HeadRest, at the open segment's
part. -/
def JHead (X : OnBytes.Model.Verify.Public) (own : List (ℕ × ℕ)) (arr : ℕ → ℕ → ℕ) (N : Numbers)
    (num : ℕ → ℕ → ℕ) (lay6 : OnBytes.Params.ReqLayout) (s : S) : Prop :=
  ∀ o a, s.here = .head o → K9.segAt? s = some a → HeadLeft6 X own s a arr N num lay6

/-- **The output head's share of J.** -/
def JH (X : OnBytes.Model.Verify.Public) (own : List (ℕ × ℕ)) (arr : ℕ → ℕ → ℕ) (N : Numbers)
    (num : ℕ → ℕ → ℕ) (lay6 : OnBytes.Params.ReqLayout) (s : S) : Prop :=
  NoTables s ∧ JHead X own arr N num lay6 s

theorem here_head_of_stand {s : S} (h : standOf s = .link .head) : ∃ o, s.here = .head o := by
  unfold standOf at h
  cases hh : s.here with
  | head a => exact ⟨a, rfl⟩
  | between => rw [hh] at h; cases h
  | lay a => rw [hh] at h; cases h
  | att a => rw [hh] at h; cases h
  | fin a => rw [hh] at h; cases h
  | mem a => rw [hh] at h; cases h

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A₀ : ProofFile.SharedSeat} {B₀ : ProofFile.SecondSeat}

/-- **THE PREMISE hK6 OF arm_at_reads_three, FROM J ALONE.** -/
theorem hK6_ofJ (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data) (J : S → Prop)
    (num : ℕ → ℕ → ℕ) (lay6 : OnBytes.Params.ReqLayout)
    (hJ : ∀ s, J s → JH XV (Dm.N.sent 24 0) Dm.arr Dm.N num lay6 s)
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₀ B₀) (hDlk : Dm.links = linksFull)
    (hlk : ∀ l, l < 25 → Dm.lk l = c.links[l]?) (hWX : Bs.G₀.W = XV) (aN : ℕ) (R₁ R₂ R₃ : Rounds)
    (cU : ℕ × String)
    (hU : (Dm.pubD.d3.arrayOf.getD 24 #[])[Kinds.Head.Law.readsOf XV]? = some cU)
    (hK : ∀ t, (Dm.pubD.dS.trees 24)[Kinds.Head.Law.readsOf XV]? = some t →
      XV.H.nU.getD 2 0 ≤ t.2.1)
    (msR : List Mem) (rad : OnBytes.OracleShape → ℕ)
    (seatT : Fin (sigListCalls Dm.sent rad 24).length → ℕ × ℕ)
    (T : _root_.Meaning.laidThere XV (_root_.Meaning.sizesOf XV) lay6 = true)
    (hC : CallsSeated (ColFour XV.hS XV.HLy (borderOf XV.y)) Dm.arr msR Dm.N XV lay6 num Dm.sent rad
      24 seatT)
    (hsub : ∀ x ∈ Dm.N.sent 24 0, x ∈ Dm.N.group 24) :
    ∀ X arrs x x' y y' w p A B,
      ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → K6Name p.2 →
      ∃ l₀ piece states cU, HeadRest XV (Dm.Rd 24) (Dm.N.sent 24 0) p.1 x.2 A B Dm.cs Dm.arr Dm.ms
        Dm.N 24 w l₀ piece states cU :=
  hK6_of5 Dm dk J (fun s h => (hJ s h).1) hS hR O hDlk hlk hWX aN R₁ R₂ R₃ cU hU hK msR lay6 num rad
    seatT T hC hsub fun X arrs x x' y y' w p A B Fc _ => by
      obtain ⟨o, ho⟩ := here_head_of_stand (stand_of_promise 24 (by decide) x y Fc.inAt)
      exact (hJ _ Fc.inv).2 o A ho Fc.front

end

/-! ## Along the reached states -/

/-- At l < 24, in front of the reads' place, the head's conjunct is idle. -/
theorem jHead_low {Pp W : Type} {N₀ : Numbers} {Mg : Meaning Pp W}
    (X : OnBytes.Model.Verify.Public) (own : List (ℕ × ℕ)) (arr : ℕ → ℕ → ℕ) (N : Numbers)
    (num : ℕ → ℕ → ℕ) (lay6 : OnBytes.Params.ReqLayout) (l : ℕ) (hl : l < 24) (x : Pp × S)
    (y : Strs) (hIn : InAt N₀ Mg linksFull (flatPlacesOf linksFull true) (noL l false) x y) :
    JHead X own arr N num lay6 x.2 := by
  intro o a ho _
  exfalso
  have hs := stand_of_promise l (by omega) x y hIn
  unfold standOf at hs
  rw [ho] at hs
  dsimp only at hs
  split at hs
  · exact absurd (First.Stand.link.inj hs).symm (low_not_head l hl)
  · cases hs

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **JH at the reached states in front of all 25 reads' places, from one premise at border 342.** -/
theorem jH_at_reads (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {W : Type} {Fr : Frame}
    (N₀ : Numbers) (Mg : Meaning ProofFile.InstPub W) (X : OnBytes.Model.Verify.Public)
    (own : List (ℕ × ℕ)) (arr : ℕ → ℕ → ℕ) (N : Numbers) (num : ℕ → ℕ → ℕ)
    (lay6 : OnBytes.Params.ReqLayout)
    (h342 : ∀ a : (ProofFile.InstPub × S) × Fr.E.Str,
      RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
        (14 * 24 + k1Ix 24 false + 2) a →
      onQ N₀ Mg linksFull (flatPlacesOf linksFull true) (fun a => a) (14 * 24 + k1Ix 24 false + 2) a →
      a.1.2.failed = none → JHead X own arr N num lay6 a.1.2) :
    ∀ l, l < 25 → ∀ a : (ProofFile.InstPub × S) × Fr.E.Str,
      RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
        (14 * l + k1Ix l false + 2) a →
      onQ N₀ Mg linksFull (flatPlacesOf linksFull true) (fun a => a) (14 * l + k1Ix l false + 2) a →
      a.1.2.failed = none → JH X own arr N num lay6 a.1.2 := by
  intro l hl a hr hon hm
  refine ⟨noTables_at_reads hS hR O N₀ Mg l hl a hr hon hm, ?_⟩
  by_cases h24 : l = 24
  · subst h24
    exact h342 a hr hon hm
  · exact jHead_low X own arr N num lay6 l (by omega) a.1 _ ⟨hon, hm⟩

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.here_head_of_stand
#print axioms VerifiableInference.Desc.K1.hK6_ofJ
#print axioms VerifiableInference.Desc.K1.jHead_low
#print axioms VerifiableInference.Desc.K1.jH_at_reads
