-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/ReadsHead.lean: the kind K1's member at a segment's reads, IN
THE HEAD's SEGMENT: behind its return the chain stands at the head's own part and the tables are
laid (t is there). Statements and proofs, over the library's laws on the step without a round that
is joined behind the reads' commitment. It imports files of the sealed library alone.

WHY BESIDE k1_reads_lays_t (Johnson/Desc/ProofFile/Honest/K1/Law/KeepsReads.lean): that lemma speaks
from the CLAUSE K1ReadsKeeps, which does not say which step was joined: so it takes "the chain
stands at the head's own part" in front as a premise; whoever has the clause alone calls it. THE
MEMBER SAYS MORE: at a link that is neither of kind 0 nor of kind 1 the joined step is the head's or
returns nothing, and the head's step's return says both by itself: no premise on the state in front.

  numbers_five: where a link's reads stand at piece 5 its kind is neither 0 nor 1.
  k1Quiet_head: a return of the joined step at such a link: the chain stood at the head's own part,
    and of the state only t and tl of that part have turned: t is there. By Reads.AtSeat.quiet_is
    (Johnson/Desc/Reads/RowAtLot.lean) and ReadsQuiet.head_ok (Johnson/Desc/K8/ReadsQuietLaws.lean).
  k1_reads_head_t: A RETURN OF THE WHOLE MEMBER AT SUCH A LINK: the chain stands at the head's own
    part behind, and t is there.
  k1_reads_342: FOR FILES IN SCOPE, wherever the description of the proof file is made: the member
    number 342 of the first chain's flat list is that member: every accepting step of it ends so. So
    the premises of k1_reads_head_t on the link are met there, and the member is seated alone over
    that sub-protocol.

Not shown here. ONE WAY, FROM A RETURN: that the member returns anywhere is not said. Nothing on
what the tables hold. Nothing on soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Reads.RowAtLot
import Johnson.Desc.K8.ReadsQuietLaws
import Johnson.IMR.K1Scope
import Johnson.IMR.MemberPath
import Johnson.Top.H0.Walk.ReachInv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open OnBytes.Model.Stages (LinkH)
open Johnson.Desc.First.Walk.Tied (StepYes stepYes_decide)

/-- Where a link's reads stand at piece 5 its kind is neither 0 nor 1. -/
theorem numbers_five {G : ProofFile.Ground} {X : LinkH} {pd : Nat} {reads digits : Option (List Nat)}
    (h : VerifiableInference.Desc.K1.linkNumbers G X = some (5, pd, reads, digits)) :
    X.kind ≠ 0 ∧ X.kind ≠ 1 := by
  unfold VerifiableInference.Desc.K1.linkNumbers at h
  refine ⟨fun e => ?_, fun e => ?_⟩
  · rw [if_pos (by rw [e]; rfl)] at h
    obtain ⟨_, _, e'⟩ := Option.map_eq_some_iff.1 h
    cases e'
  · rw [if_neg (by rw [e]; decide), if_pos (by rw [e]; rfl)] at h
    obtain ⟨_, _, e'⟩ := Option.map_eq_some_iff.1 h
    cases e'

/-- **A return of the step that is joined behind the reads' commitment, at a link that is neither of
kind 0 nor of kind 1**: the chain stood at the head's own part; t and tl of that part alone have
turned; t is there. -/
theorem k1Quiet_head {G : ProofFile.Ground} {l : Nat} {X : LinkH} (hb : G.built[l]? = some X)
    (h0 : X.kind ≠ 0) (h1 : X.kind ≠ 1) {m s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (d : (IM.k1Quiet G l X).decide m rs gs = .ok s') :
    ∃ a t tl, m.here = .head a ∧
      s' = { m with here := .head { a with t := some t, tl := tl } } := by
  have hp : (if X.kind == 0 || X.kind == 1 then 4 else 5) = 5 := by
    rw [if_neg]
    simp [h0, h1]
  have hl : (G.built.toList.map fun Y => (Y.kind, Y.g))[l]? = some (X.kind, X.g) := by
    rw [List.getElem?_map, Array.getElem?_toList, hb]
    rfl
  unfold IM.k1Quiet at d
  simp only [hp] at d
  by_cases h2 : X.kind = 2
  · rw [VerifiableInference.Reads.AtSeat.quiet_is G l X _ _ _ h2 (g := X.g) (by rw [hl, h2])] at d
    obtain ⟨a, -, -, t, tl, ha, -, -, -, -, -, e⟩ :=
      VerifiableInference.Desc.K8.ReadsQuiet.head_ok d
    exact ⟨a, t, tl, ha, e⟩
  · have hn : ProofFile.readsQuietAt G l X 5 = none := by
      unfold ProofFile.readsQuietAt VerifiableInference.Desc.K8.ReadsQuiet.blockAt
      simp [h0, h1, h2, hl]
    rw [hn] at d
    exact nomatch d

/-- **A RETURN OF THE WHOLE MEMBER AT THE READS OF SUCH A LINK**: the chain stands at the head's own
part behind, and t is there. -/
theorem k1_reads_head_t {Z : ProofFile.Pub} {G : ProofFile.Ground} {l : Nat} {X : LinkH} {pr : Nat}
    {reads : Option (List Nat)} (hb : G.built[l]? = some X) (h0 : X.kind ≠ 0) (h1 : X.kind ≠ 1)
    {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (d : (IM.k1Reads Z G l X pr reads).decide s rs gs = .ok s') :
    ∃ a', s'.here = .head a' ∧ a'.t.isSome = true := by
  obtain ⟨m, -, h2⟩ := VerifiableInference.Desc.Keeps.ebind_ok
    (show (((VerifiableInference.Desc.K1.laterAt G.first (VerifiableInference.Desc.K1.gpOf Z) l pr 1
      reads : Block S Unit).decide s _ _).bind fun s₁ =>
        (IM.k1Quiet G l X).decide s₁ _ _) = .ok s' from d)
  obtain ⟨a, t, tl, -, rfl⟩ := k1Quiet_head hb h0 h1 h2
  exact ⟨_, rfl, rfl⟩

/-- **FOR FILES IN SCOPE: THE MEMBER NUMBER 342 OF THE FIRST CHAIN's FLAT LIST**: every accepting
step of it ends with the chain at the head's own part and t there. -/
theorem k1_reads_342 {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {b0 : Block S ProofFile.Cl}
    (hB : c.blocksInOrder[342]? = some b0) {ft : Nat} {s s' : S} (y : StepYes ft b0 s s') :
    ∃ a', s'.here = .head a' ∧ a'.t.isSome = true := by
  obtain ⟨rs, gs, d⟩ := stepYes_decide y
  obtain ⟨Lk, b, Xl, pd, reads, digits, h1, h2, hX, -, hla⟩ :=
    IM.k1_reads_of hS hR O 24 (by decide)
  have h3 := IM.hear_at_flat h1 h2
  rw [IM.flatIx_scope hS hR O (by decide) _] at h3
  obtain rfl : b = b0 := Option.some.inj (h3.symm.trans hB)
  have d' : (IM.k1Reads Z Bs.G₀ 24 Xl (IM.k1Ix 24 false + 1) reads).decide s rs gs = .ok s' :=
    (IM.alone_noMark hla d).1
  obtain ⟨-, l, hl, hk, -⟩ := IM.ground_named hS hR O.pub O.blank
  obtain rfl : l = Xl := Option.some.inj (hl.symm.trans hX)
  exact k1_reads_head_t hX (by rw [hk]; decide) (by rw [hk]; decide) d'

end ProofFile.Honest.K1
